;;;; Per-call state of the CDCL search in search.lisp: literal codes, the
;;;; %SOLVER structure, the clause store and its watch lists, the decision
;;;; heap, the trail and its levels, loading a CNF, and publishing the
;;;; statistics. A %SOLVER lives for one BACKEND-SOLVE or
;;;; BACKEND-FINAL-CONFLICT call; nothing in it survives the call.
;;;;
;;;; Literal codes: +v is 2v and -v is 2v+1, so negation is (LOGXOR l 1) and
;;;; the variable is (ASH l -1). Variable 0 is never assigned, so code 0 is a
;;;; literal that is never true.
;;;;
;;;; Clause ids: the input clauses are 0..M-1 in input order; learnt clauses
;;;; take the ids after them, so a higher id is a younger clause. Ids are never
;;;; reused. Each clause is a fresh (SIMPLE-ARRAY FIXNUM (*)) of literal codes.
;;;;
;;;; Watches: WATCHES[l] lists the clauses that watch literal l, as pairs
;;;; (entry, blocker) in a fixnum vector with WFILL[l] used entries. It is
;;;; visited when l becomes false. ENTRY is the clause id, or (LOGNOT id) for a
;;;; binary clause, whose blocker is always its other literal; a longer clause
;;;; watches its literals 0 and 1, and its blocker is some other literal of it.

(in-package #:sat-backend-cdcl)

;;; ------------------------------------------------------------------ types

(deftype %fixvec () '(simple-array fixnum (*)))
(deftype %bytevec () '(simple-array (signed-byte 8) (*)))
(deftype %dblvec () '(simple-array double-float (*)))

(defmacro %empty (element-type)
  "A shared empty vector, for the typed initforms of %SOLVER."
  `(load-time-value (make-array 0 :element-type ',element-type) t))

(declaim (inline %fixvec %bytevec %dblvec %lit %int))

(defun %fixvec (size &optional (initial 0))
  (make-array size :element-type 'fixnum :initial-element initial))

(defun %bytevec (size)
  (make-array size :element-type '(signed-byte 8) :initial-element 0))

(defun %dblvec (size)
  (make-array size :element-type 'double-float :initial-element 0d0))

(defun %lit (literal)
  "The code of the integer LITERAL."
  (declare (fixnum literal))
  (if (plusp literal) (* 2 literal) (1+ (* -2 literal))))

(defun %int (code)
  "The integer literal of CODE."
  (declare (fixnum code))
  (if (evenp code) (ash code -1) (- (ash code -1))))

(defun %clamp (integer)
  "INTEGER, at most MOST-POSITIVE-FIXNUM (a bound no counter reaches)."
  (min integer most-positive-fixnum))

(defun %double (real low high)
  "REAL as a double-float within [LOW, HIGH] (both double-floats)."
  (cond ((<= real low) low)
        ((>= real high) high)
        (t (float real 1d0))))

;;; -------------------------------------------------------------- the state

(defstruct (%solver (:constructor %make-solver (backend))
                    (:conc-name s-) (:copier nil) (:predicate nil))
  (backend nil)
  (n 0 :type fixnum)                    ; variables 1..N
  (m 0 :type fixnum)                    ; input clauses: ids 0..M-1
  ;; per literal code (2N+2)
  (lval (%empty (signed-byte 8)) :type %bytevec)    ; 1 true, -1 false, 0 unassigned
  (watches #() :type simple-vector)                 ; %FIXVEC of (entry, blocker) pairs
  (wfill (%empty fixnum) :type %fixvec)             ; used length of WATCHES[l]
  (in-core (%empty (signed-byte 8)) :type %bytevec) ; final conflict: 1 for the literals of S
  ;; per variable (N+1)
  (level (%empty fixnum) :type %fixvec)
  (reason (%empty fixnum) :type %fixvec)            ; clause id, or -1
  (saved (%empty (signed-byte 8)) :type %bytevec)   ; saved phase: 1, -1, 0 none
  (act (%empty double-float) :type %dblvec)         ; EVSIDS activity
  (heap-index (%empty fixnum) :type %fixvec)        ; position in HEAP, or -1
  (in-input (%empty (signed-byte 8)) :type %bytevec) ; 1: occurs in an input clause
  (seen (%empty (signed-byte 8)) :type %bytevec)    ; analysis marks, 0 outside them
  (cand (%empty fixnum) :type %fixvec)              ; ORDER candidates: STAMP marks
  ;; the trail: assigned literals in order; QHEAD: the next one to propagate
  (trail (%empty fixnum) :type %fixvec)
  (trail-size 0 :type fixnum)
  (qhead 0 :type fixnum)
  (dl 0 :type fixnum)                               ; the decision level
  ;; per level (N + assumptions + 2): TRAIL-LIM[L] and SCAN-AT[L] are the trail
  ;; size and the SAT-check scan position when level L+1 was opened
  (trail-lim (%empty fixnum) :type %fixvec)
  (scan-at (%empty fixnum) :type %fixvec)
  (level-stamp (%empty fixnum) :type %fixvec)       ; LBD: STAMP marks
  ;; the decision heap: input variables, greatest activity first, ties to the
  ;; lower index; assigned variables leave it lazily (at the top)
  (heap (%empty fixnum) :type %fixvec)
  (heap-size 0 :type fixnum)
  ;; the clause store, by id
  (clauses #() :type simple-vector)
  (nclauses 0 :type fixnum)
  (clause-lbd (%empty fixnum) :type %fixvec)        ; LBD at learning; 0 for input clauses
  (clause-act (%empty double-float) :type %dblvec)  ; learnt-clause activity
  (clause-lock (%empty fixnum) :type %fixvec)       ; reduction: STAMP marks of reasons
  (clause-deleted (%empty (signed-byte 8)) :type %bytevec)
  (learnts (%empty fixnum) :type %fixvec)           ; the learnt database, oldest first
  (nlearnts 0 :type fixnum)
  ;; the SAT check (4b): every input clause before SCAN is true; SAT-LIT[id]
  ;; is a literal that was true in it when last checked (0: none yet)
  (sat-lit (%empty fixnum) :type %fixvec)
  (scan 0 :type fixnum)
  ;; analysis buffers (N+1)
  (out (%empty fixnum) :type %fixvec)               ; the learnt clause
  (stack (%empty fixnum) :type %fixvec)
  (toclear (%empty fixnum) :type %fixvec)
  (nclear 0 :type fixnum)
  (stamp 0 :type fixnum)                            ; fresh marks for CAND, LEVEL-STAMP, CLAUSE-LOCK
  ;; assumptions, as codes in the given order
  (assumps (%empty fixnum) :type %fixvec)
  (nassumps 0 :type fixnum)
  ;; activity bumps and decays
  (var-inc 1d0 :type double-float)
  (var-decay 0.95d0 :type double-float)
  (cla-inc 1d0 :type double-float)
  (cla-decay 0.999d0 :type double-float)
  ;; the call's arguments and the backend's parameters
  (order nil)
  (phase nil)
  (learnt-hook nil)
  (budget nil :type (or null (integer 0 *)))
  (budget-unit :decisions :type symbol)
  (want-core nil)
  (phase-saving t)
  (default-phase nil)
  (minimization :recursive :type symbol)
  (restart-policy :luby :type symbol)
  ;; :LUBY: run RUN-K ends after RUN-LIMIT = LUBY-UNIT * luby(RUN-K) learnt clauses
  (luby-unit 100 :type fixnum)
  (run-k 1 :type fixnum)
  (run-learnt 0 :type fixnum)
  (run-limit 100 :type fixnum)
  ;; :GLUCOSE: the LBDs of this run's last WINDOW learnt clauses
  (window 50 :type fixnum)
  (margin 0.8d0 :type double-float)
  (ring (%empty fixnum) :type %fixvec)
  (ring-count 0 :type fixnum)
  (ring-pos 0 :type fixnum)
  (ring-sum 0 :type fixnum)
  (lbd-total 0 :type fixnum)                        ; every LBD of the call
  ;; reduction: the next one is due at NEXT-REDUCE learnt clauses
  (reduce-p t)
  (reduce-base 2000 :type fixnum)
  (reduce-inc 300 :type fixnum)
  (reduce-k 0 :type fixnum)
  (next-reduce 2000 :type fixnum)
  ;; the statistics (backend.lisp)
  (decisions 0 :type fixnum)
  (propagations 0 :type fixnum)
  (conflicts 0 :type fixnum)
  (learnt 0 :type fixnum)
  (backjumps 0 :type fixnum)
  (restarts 0 :type fixnum)
  (reductions 0 :type fixnum)
  (deleted 0 :type fixnum))

(defun %publish (s)
  "Store a fresh plist of S's counters as its backend's statistics."
  (declare (type %solver s))
  (setf (cdcl-backend-statistics (s-backend s))
        (list :decisions (s-decisions s) :propagations (s-propagations s)
              :conflicts (s-conflicts s) :learnt-clauses (s-learnt s)
              :backjumps (s-backjumps s) :restarts (s-restarts s)
              :reductions (s-reductions s) :deleted-clauses (s-deleted s))))

(defun %setup (s n m assumptions order phase budget want-core)
  "Size S for N variables, M input clauses and ASSUMPTIONS, and take the
backend's parameters and the call's arguments."
  (declare (type %solver s) (type fixnum n m))
  (let* ((backend (s-backend s))
         (nassumps (length assumptions))
         (nlits (+ 2 (* 2 n)))
         (nvars (1+ n))
         (nlevels (+ n nassumps 2))
         (capacity (+ m 64))
         (empty (%fixvec 0))
         (window (%clamp (cdcl-backend-restart-window backend)))
         (base (cdcl-backend-reduce-base backend)))
    (setf (s-n s) n
          (s-m s) m
          (s-lval s) (%bytevec nlits)
          (s-watches s) (make-array nlits :initial-element empty)
          (s-wfill s) (%fixvec nlits)
          (s-in-core s) (%bytevec nlits)
          (s-level s) (%fixvec nvars)
          (s-reason s) (%fixvec nvars -1)
          (s-saved s) (%bytevec nvars)
          (s-act s) (%dblvec nvars)
          (s-heap-index s) (%fixvec nvars -1)
          (s-in-input s) (%bytevec nvars)
          (s-seen s) (%bytevec nvars)
          (s-cand s) (%fixvec nvars)
          (s-trail s) (%fixvec nvars)
          (s-trail-lim s) (%fixvec nlevels)
          (s-scan-at s) (%fixvec nlevels)
          (s-level-stamp s) (%fixvec nlevels)
          (s-heap s) (%fixvec nvars)
          (s-clauses s) (make-array capacity :initial-element empty)
          (s-clause-lbd s) (%fixvec capacity)
          (s-clause-act s) (%dblvec capacity)
          (s-clause-lock s) (%fixvec capacity)
          (s-clause-deleted s) (%bytevec capacity)
          (s-learnts s) (%fixvec 64)
          (s-sat-lit s) (%fixvec m)
          (s-out s) (%fixvec nvars)
          (s-stack s) (%fixvec nvars)
          (s-toclear s) (%fixvec nvars)
          (s-assumps s) (let ((codes (%fixvec nassumps)))
                          (loop for a in assumptions for i from 0
                                do (setf (aref codes i) (%lit a)))
                          codes)
          (s-nassumps s) nassumps
          (s-order s) order
          (s-phase s) phase
          (s-budget s) budget
          (s-want-core s) want-core
          (s-learnt-hook s) (cdcl-backend-learnt-hook backend)
          (s-budget-unit s) (cdcl-backend-budget-unit backend)
          (s-phase-saving s) (cdcl-backend-phase-saving backend)
          (s-default-phase s) (cdcl-backend-default-phase backend)
          (s-minimization s) (cdcl-backend-clause-minimization backend)
          (s-var-decay s) (%double (cdcl-backend-variable-decay backend) 1d-100 1d0)
          (s-cla-decay s) (%double (cdcl-backend-clause-decay backend) 1d-100 1d0)
          (s-restart-policy s) (cdcl-backend-restart-policy backend)
          (s-luby-unit s) (%clamp (cdcl-backend-luby-unit backend))
          (s-run-limit s) (s-luby-unit s)                       ; luby(1) = 1
          (s-window s) window
          (s-margin s) (%double (cdcl-backend-restart-margin backend) 0d0 1d300)
          (s-ring s) (%fixvec (min window 64))
          (s-reduce-p s) (and base t)
          (s-reduce-base s) (if base (%clamp base) 0)
          (s-reduce-inc s) (%clamp (cdcl-backend-reduce-increment backend))
          (s-next-reduce s) (if base (%clamp base) 0))
    s))

;;; ------------------------------------------------------- clauses, watches

(defun %grow-clause-store (s)
  (declare (type %solver s))
  (let* ((old (length (s-clauses s)))
         (new (* 2 (max old 32))))
    (flet ((grow (vector element-type)
             (let ((grown (make-array new :element-type element-type
                                          :initial-element (coerce 0 element-type))))
               (replace grown vector)
               grown)))
      (setf (s-clauses s) (let ((grown (make-array new :initial-element (%fixvec 0))))
                            (replace grown (s-clauses s))
                            grown)
            (s-clause-lbd s) (grow (s-clause-lbd s) 'fixnum)
            (s-clause-act s) (grow (s-clause-act s) 'double-float)
            (s-clause-lock s) (grow (s-clause-lock s) 'fixnum)
            (s-clause-deleted s) (grow (s-clause-deleted s) '(signed-byte 8))))))

(defun %add-clause (s literals lbd)
  "Store LITERALS (a fresh %FIXVEC) under the next id, with LBD; return the id."
  (declare (type %solver s) (type %fixvec literals) (type fixnum lbd))
  (let ((id (s-nclauses s)))
    (when (= id (length (s-clauses s)))
      (%grow-clause-store s))
    (setf (svref (s-clauses s) id) literals
          (aref (s-clause-lbd s) id) lbd
          (aref (s-clause-act s) id) 0d0
          (s-nclauses s) (1+ id))
    id))

(defun %watch (s literal entry blocker)
  "Append the watch (ENTRY, BLOCKER) to WATCHES[LITERAL], growing it when full."
  (declare (type %solver s) (type fixnum literal entry blocker)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let* ((watches (s-watches s))
         (wfill (s-wfill s))
         (ws (svref watches literal))
         (fill (aref wfill literal)))
    (declare (type %fixvec ws wfill) (type fixnum fill))
    (when (> (+ fill 2) (length ws))
      (let ((grown (%fixvec (max 8 (* 2 (length ws))))))
        (replace grown ws :end2 fill)
        (setf (svref watches literal) grown
              ws grown)))
    (setf (aref ws fill) entry
          (aref ws (1+ fill)) blocker
          (aref wfill literal) (+ fill 2))
    nil))

(defun %attach (s id)
  "Watch literals 0 and 1 of clause ID (two or more literals, no tautology)."
  (declare (type %solver s) (type fixnum id))
  (let* ((c (svref (s-clauses s) id))
         (a (aref c 0))
         (b (aref c 1)))
    (declare (type %fixvec c))
    (if (= 2 (length c))
        (let ((entry (lognot id)))
          (%watch s a entry b)
          (%watch s b entry a))
        (progn
          (%watch s a id b)
          (%watch s b id a)))))

;;; ------------------------------------------------------------------- heap

(declaim (inline %better))
(defun %better (act u v)
  "Variable U goes before V: greater activity, ties to the lower index."
  (declare (type %dblvec act) (type fixnum u v))
  (let ((x (aref act u)) (y (aref act v)))
    (or (> x y) (and (= x y) (< u v)))))

(defun %heap-up (s i)
  (declare (type %solver s) (type fixnum i)
           (optimize (speed 3) (safety 1)))
  (let* ((heap (s-heap s)) (index (s-heap-index s)) (act (s-act s))
         (v (aref heap i)))
    (declare (type fixnum v))
    (loop while (plusp i)
          do (let* ((parent (ash (1- i) -1))
                    (u (aref heap parent)))
               (if (%better act v u)
                   (setf (aref heap i) u (aref index u) i i parent)
                   (return))))
    (setf (aref heap i) v (aref index v) i)))

(defun %heap-down (s i)
  (declare (type %solver s) (type fixnum i)
           (optimize (speed 3) (safety 1)))
  (let* ((heap (s-heap s)) (index (s-heap-index s)) (act (s-act s))
         (size (s-heap-size s))
         (v (aref heap i)))
    (declare (type fixnum size v))
    (loop
      (let ((child (1+ (* 2 i))))
        (declare (type fixnum child))
        (when (>= child size) (return))
        (let ((right (1+ child)))
          (when (and (< right size) (%better act (aref heap right) (aref heap child)))
            (setf child right)))
        (let ((u (aref heap child)))
          (if (%better act u v)
              (setf (aref heap i) u (aref index u) i i child)
              (return)))))
    (setf (aref heap i) v (aref index v) i)))

(defun %heap-insert (s v)
  (declare (type %solver s) (type fixnum v))
  (let ((i (s-heap-size s)))
    (setf (aref (s-heap s) i) v
          (aref (s-heap-index s) v) i
          (s-heap-size s) (1+ i))
    (%heap-up s i)))

(defun %heap-pop (s)
  "Remove and return the first variable of the heap (it is not empty)."
  (declare (type %solver s))
  (let* ((heap (s-heap s))
         (top (aref heap 0))
         (size (1- (s-heap-size s))))
    (setf (aref (s-heap-index s) top) -1
          (s-heap-size s) size)
    (when (plusp size)
      (let ((last (aref heap size)))
        (setf (aref heap 0) last
              (aref (s-heap-index s) last) 0)
        (%heap-down s 0)))
    top))

(defun %heap-rebuild (s)
  "Restore the heap order after activities changed together (a rescale)."
  (declare (type %solver s))
  (loop for i from (1- (floor (s-heap-size s) 2)) downto 0
        do (%heap-down s i)))

;;; ------------------------------------------------------------------ trail

(declaim (inline %assign))
(defun %assign (s literal reason)
  "Make LITERAL true at the current level with REASON (a clause id or -1)."
  (declare (type %solver s) (type fixnum literal reason))
  (let ((lval (s-lval s))
        (v (ash literal -1))
        (size (s-trail-size s)))
    (setf (aref lval literal) 1
          (aref lval (logxor literal 1)) -1
          (aref (s-level s) v) (s-dl s)
          (aref (s-reason s) v) reason
          (aref (s-trail s) size) literal
          (s-trail-size s) (1+ size))
    nil))

(defun %new-level (s)
  "Open level DL+1, remembering where the trail and the SAT-check scan stand."
  (declare (type %solver s))
  (let ((dl (s-dl s)))
    (setf (aref (s-trail-lim s) dl) (s-trail-size s)
          (aref (s-scan-at s) dl) (s-scan s)
          (s-dl s) (1+ dl))))

(defun %cancel-until (s target)
  "Undo every assignment above level TARGET. Each undone variable's value
becomes its saved phase, its reason is cleared and an input variable returns
to the heap; the SAT-check scan goes back to where it stood at TARGET."
  (declare (type %solver s) (type fixnum target)
           (optimize (speed 3) (safety 1)))
  (when (> (s-dl s) target)
    (let ((lval (s-lval s)) (trail (s-trail s)) (saved (s-saved s))
          (reason (s-reason s)) (in-input (s-in-input s)) (index (s-heap-index s))
          (start (aref (s-trail-lim s) target)))
      (declare (type fixnum start))
      (loop for i of-type fixnum from (1- (s-trail-size s)) downto start
            do (let* ((l (aref trail i))
                      (v (ash l -1)))
                 (setf (aref saved v) (if (evenp l) 1 -1)
                       (aref lval l) 0
                       (aref lval (logxor l 1)) 0
                       (aref reason v) -1)
                 (when (and (= 1 (aref in-input v)) (minusp (aref index v)))
                   (%heap-insert s v))))
      (setf (s-trail-size s) start
            (s-qhead s) start
            (s-scan s) (aref (s-scan-at s) target)
            (s-dl s) target))))

;;; ------------------------------------------------------------------- load

(defun %load (s clause-lists)
  "R1: store CLAUSE-LISTS (CNF-CLAUSES of the call's CNF) as ids 0..M-1, each
without repeated literals (first occurrences kept); watch every clause of two
or more literals that is not a tautology; put the variables of the input
clauses in the heap; assign the unit clauses at level 0 in input order, each
with its clause as reason (one :PROPAGATIONS). Returns NIL after a conflict
(an empty clause, or a unit whose literal is already false: one :CONFLICTS),
else T."
  (declare (type %solver s) (type list clause-lists)
           (optimize (speed 1) (safety 1)))
  (let* ((n (s-n s))
         (m (s-m s))
         (nlits (+ 2 (* 2 n)))
         (clauses (s-clauses s))
         (mark (%fixvec nlits))
         (occurrences (%fixvec nlits))
         (tautology (%bytevec m))
         (buffer (%fixvec nlits))
         (in-input (s-in-input s))
         (lval (s-lval s)))
    (loop for clause in clause-lists
          for id of-type fixnum from 0
          do (let ((size 0) (stamp (1+ id)) (taut nil))
               (declare (type fixnum size stamp))
               (dolist (literal clause)
                 (let ((l (%lit literal)))
                   (unless (= stamp (aref mark l))
                     (when (= stamp (aref mark (logxor l 1)))
                       (setf taut t))
                     (setf (aref mark l) stamp
                           (aref buffer size) l)
                     (incf size))))
               (when (zerop size)
                 (incf (s-conflicts s))
                 (return-from %load nil))
               (let ((c (subseq buffer 0 size)))
                 (setf (svref clauses id) c)
                 (loop for l across c do (setf (aref in-input (ash l -1)) 1))
                 (cond (taut (setf (aref tautology id) 1))
                       ((>= size 2) (loop for l across c do (incf (aref occurrences l))))))))
    (setf (s-nclauses s) m)
    (let ((watches (s-watches s)))
      (loop for l from 2 below nlits
            for k = (aref occurrences l)
            when (plusp k) do (setf (svref watches l) (%fixvec (* 2 k)))))
    (loop for id from 0 below m
          when (and (zerop (aref tautology id)) (>= (length (svref clauses id)) 2))
            do (%attach s id))
    ;; Activities are all 0, so the variables in index order form a heap.
    (let ((heap (s-heap s)) (index (s-heap-index s)) (size 0))
      (declare (type fixnum size))
      (loop for v from 1 to n
            when (= 1 (aref in-input v))
              do (setf (aref heap size) v (aref index v) size)
                 (incf size))
      (setf (s-heap-size s) size))
    (loop for id from 0 below m
          for c of-type %fixvec = (svref clauses id)
          when (= 1 (length c))
            do (let ((l (aref c 0)))
                 (case (aref lval l)
                   (1)
                   (-1 (incf (s-conflicts s))
                    (return-from %load nil))
                   (t (%assign s l id)
                    (incf (s-propagations s))))))
    t))
