;;;; The CDCL search behind BACKEND-SOLVE and BACKEND-FINAL-CONFLICT
;;;; (sat-protocol 0.2, header of its src/protocol.lisp), in the style of
;;;; MiniSat 2.2 and Glucose. GIVEN: the class and its parameters
;;;; (backend.lisp), the two method signatures and the rules below, which the
;;;; tests pin. STUBBED (%L2B3-PENDING): both methods. Add files to the .asd
;;;; as needed; the rules do not depend on the file layout.
;;;;
;;;; Pure Lisp, sat-protocol only. Typed simple vectors on the hot paths
;;;; (fixnum literals, indices and counters, double-float activities); no
;;;; lists, hash tables or generic arithmetic in propagation and analysis.
;;;; The performance gates (tests/performance-test.lisp) assume this.
;;;; No preprocessing or inprocessing in 0.1.0.
;;;;
;;;; ---------------------------------------------------------------- a call
;;;; Every call starts from nothing: no clause, activity, phase or counter
;;;; survives from an earlier call on the same backend. (0.2.0: a session call
;;;; runs this search on its session's persistent state instead; session.lisp.)
;;;; A call is deterministic: the same CNF, arguments and parameters give the
;;;; same answer, the same hook calls and the same statistics (no randomness;
;;;; nothing depends on hash order or addresses). The CNF is never modified.
;;;; Variables are 1..(CNF-VARIABLE-COUNT cnf); the variables of ASSUMPTIONS
;;;; are among them (the front ends ensure it). Input clauses are taken as
;;;; given: an empty clause makes the call UNSAT at level 0; repeated literals
;;;; are harmless; a clause with both L and -L is satisfied only once its
;;;; variable has a value (the protocol's "every clause contains one of
;;;; them").
;;;;
;;;; SAT -> (values LITERALS T): the trail, in assignment order: assumptions,
;;;; decisions and propagated literals, each variable once. UNSAT ->
;;;; (values NIL NIL). BACKEND-FINAL-CONFLICT: see FINAL CONFLICT.
;;;;
;;;; --------------------------------------------------------------- the loop
;;;; The trail holds the assigned literals, each with a decision level and a
;;;; reason: the clause that implied it, or none (decisions and assumptions).
;;;; Level 0 holds what the clauses imply on their own. A run is the search
;;;; between two restarts.
;;;;
;;;; 1. PROPAGATE, with two watched literals in every clause of two or more
;;;;    literals: while some clause has every literal false but one, and that
;;;;    one unassigned, assign it with the clause as its reason. One
;;;;    :PROPAGATIONS per literal assigned this way; the input's unit clauses
;;;;    are assigned at level 0 the same way, and count. A clause with every
;;;;    literal false is a conflict (one :CONFLICTS): go to 2. Nothing left
;;;;    to propagate: go to 4.
;;;; 2. ANALYSE. A conflict at level 0 ends the call: UNSAT, nothing learnt.
;;;;    Above level 0: first the budget, when its unit is :CONFLICTS (BUDGET
;;;;    below). Then the first-UIP clause: resolve the conflict clause with
;;;;    the reasons of its literals of the conflict level, newest first,
;;;;    until one literal of that level is left (the asserting literal).
;;;;    Literals of level 0 are left out. Every variable met above level 0 is
;;;;    bumped (EVSIDS) and every learnt clause met is bumped (clause
;;;;    activity). Then minimise the clause:
;;;;      :RECURSIVE  drop a non-asserting literal whose negation is implied
;;;;                  by the clause's other literals through reasons, followed
;;;;                  recursively (MiniSat's ccmin-mode 2);
;;;;      :BASIC      drop it when every other literal of its reason is in the
;;;;                  clause or of level 0 (ccmin-mode 1);
;;;;      NIL         keep every literal.
;;;;    The LBD of the result is its number of distinct decision levels. When
;;;;    LEARNT-HOOK is set, call it with a fresh list of the clause's literals,
;;;;    asserting literal first, and the LBD. One :LEARNT-CLAUSES. Then decay:
;;;;    the variable bump is divided by VARIABLE-DECAY and the clause bump by
;;;;    CLAUSE-DECAY. Both kinds of activity are rescaled (all together,
;;;;    order kept) before they overflow a double-float.
;;;; 3. BACKJUMP to the highest level among the clause's other literals (0 for
;;;;    a unit clause): undo every assignment above that level. An undone
;;;;    variable's value becomes its saved phase. When the target level is
;;;;    below the conflict level minus one, count one :BACKJUMPS (a
;;;;    non-chronological backjump). Keep the clause: a unit clause as a level-0
;;;;    fact, a longer one in the learnt database. Assign the asserting
;;;;    literal with the clause as its reason (one :PROPAGATIONS). Then, in
;;;;    this order, REDUCE when due and RESTART when due (below). Go to 1.
;;;; 4. DECISION POINT (no conflict, nothing to propagate):
;;;;    a. ASSUMPTIONS, one level each, in the given order: while some
;;;;       assumption has no level in this run yet, take the next one. Already
;;;;       true: it gets an empty level; take the next. False: UNSAT (FINAL
;;;;       CONFLICT below). Unassigned: assign it at a new level (neither a
;;;;       decision nor a propagation) and go to 1. Every run takes them again.
;;;;    b. SAT: when every input clause has a true literal, the call answers
;;;;       SAT. It runs at every decision point once the assumptions are in,
;;;;       before the budget. Keep it incremental (e.g. a scan position per
;;;;       level, a satisfying literal cached per clause): a full scan per
;;;;       decision misses the performance gates.
;;;;    c. BUDGET, when its unit is :DECISIONS (below).
;;;;    d. DECIDE (one :DECISIONS) at a new level, then go to 1.
;;;;       Variable: with ORDER, (funcall ORDER candidates), CANDIDATES being
;;;;       the ascending indices of the unassigned variables that occur in an
;;;;       input clause with no true literal (learnt clauses add none). ORDER
;;;;       is called once per decision and its choice is decided; a result
;;;;       that is not one of CANDIDATES signals SAT-ERROR. Without ORDER, the
;;;;       unassigned variable of greatest activity among the variables of the
;;;;       input clauses (a binary heap), ties to the lower index; it need not
;;;;       be a candidate. Activities start at 0, so the first decisions of a
;;;;       call take the variables in index order.
;;;;       Value: with PHASE, (funcall PHASE var), called once per decision
;;;;       right after ORDER; else the saved phase when PHASE-SAVING and the
;;;;       variable has one; else DEFAULT-PHASE.
;;;;
;;;; ------------------------------------------------------------------ budget
;;;; BUDGET NIL: unlimited. A non-negative integer: with BUDGET-UNIT
;;;; :DECISIONS (the protocol's unit), at 4c, while the call's decisions so
;;;; far >= BUDGET, (setf budget (signal-budget-exceeded budget)); with
;;;; :CONFLICTS, at 2 (a conflict above level 0, before its analysis), while
;;;; the call's learnt clauses so far >= BUDGET, the same. The statistics are
;;;; current at the signal. CONTINUE and STORE-VALUE resume the search where
;;;; it stopped: a call whose handler always continues makes exactly the
;;;; decisions, hook calls, answer and statistics of the same call without a
;;;; budget. USE-VALUE throws to the front end. Under MINIMIZE's meter
;;;; (sat-protocol's minimize.lisp: :BUDGET 0, STORE-VALUE budget+1 per
;;;; signal), a :CONFLICTS backend's MINIMIZE :BUDGET counts conflicts; the
;;;; conformance suite runs with :DECISIONS.
;;;;
;;;; ---------------------------------------------------------------- restarts
;;;; Checked at 3 after every learnt clause; a restart backtracks to level 0
;;;; (phases saved as at 3) and keeps learnt clauses, activities and phases.
;;;; One :RESTARTS each. RESTART-POLICY:
;;;;   :LUBY     run k (k = 1, 2, ...) ends once LUBY-UNIT * luby(k) clauses
;;;;             have been learnt in it; luby = 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
;;;;             So with S(r) = LUBY-UNIT * (luby(1) + ... + luby(r)), a call
;;;;             with L learnt clauses has made R restarts, S(R) <= L < S(R+1).
;;;;   :GLUCOSE  keep the LBDs of the last RESTART-WINDOW clauses learnt in this
;;;;             run; restart when the window is full and
;;;;             RESTART-MARGIN * (window mean) > (mean LBD of every clause
;;;;             learnt in this call). The window starts empty in every run, so
;;;;             R <= floor(L / RESTART-WINDOW).
;;;;   NIL       never.
;;;;
;;;; --------------------------------------------------------------- reduction
;;;; REDUCE-BASE NIL: never. Otherwise the k-th reduction (k = 1, 2, ...) is
;;;; due at 3 once the call has learnt R_k clauses,
;;;;   R_k = k * REDUCE-BASE + REDUCE-INCREMENT * k * (k - 1) / 2,
;;;; so a call with L learnt clauses made exactly #{k : R_k <= L} reductions.
;;;; A reduction deletes from the learnt database the worse half (floor n/2)
;;;; of its n deletable clauses: those whose LBD (at learning) is above 2 and
;;;; that are not the reason of an assigned literal. Worse: higher LBD, then
;;;; lower clause activity, then older. One :REDUCTIONS per reduction and one
;;;; :DELETED-CLAUSES per clause deleted. The database stays bounded by the
;;;; schedule: about half of what was learnt since the previous reduction,
;;;; plus glue (LBD <= 2) and locked clauses.
;;;;
;;;; ---------------------------------------------------------- final conflict
;;;; (backend-final-conflict backend cnf assumptions &key budget order phase)
;;;; runs exactly the search of BACKEND-SOLVE (same rules, hooks, budget and
;;;; statistics). SAT -> (values NIL NIL LITERALS), LITERALS as BACKEND-SOLVE's.
;;;; UNSAT -> (values CORE T), CORE as MiniSat's analyzeFinal:
;;;;   - a conflict at level 0 (the CNF alone is refuted): CORE = NIL;
;;;;   - an assumption A false at its turn (4a): S = {A} plus every
;;;;     assumption reached from -A through reasons: mark -A's variable; walk
;;;;     the trail from the newest literal down to level 1; at a marked
;;;;     variable with a reason, mark that reason's other variables above
;;;;     level 0; at a marked variable without one (an assumption), put its
;;;;     literal in S. A false at level 0 gives S = {A}.
;;;;   CORE = the elements of ASSUMPTIONS that are in S, in the given order,
;;;;   each once (the first occurrence). CNF plus CORE is unsatisfiable. An
;;;;   assumption over a variable of no clause is in CORE only when it
;;;;   contradicts another assumption (A and -A: both, in the given order).
;;;; BACKEND-SOLVE under assumptions answers UNSAT the same way, without the
;;;; core. BACKEND-SOLVE-ALL, BACKEND-MINIMIZE (every strategy, :CORE-GUIDED
;;;; through this method) and BACKEND-UNSAT-CORE keep sat-protocol's default
;;;; methods.
;;;;
;;;; -------------------------------------------------------------- statistics
;;;; Per call, from 0 (keys in backend.lisp): :DECISIONS (4d), :PROPAGATIONS
;;;; (1 and 3), :CONFLICTS (1, the final level-0 conflict included),
;;;; :LEARNT-CLAUSES (2; so :CONFLICTS - :LEARNT-CLAUSES is 1 when a level-0
;;;; conflict ended the call, else 0), :BACKJUMPS (3), :RESTARTS, :REDUCTIONS
;;;; and :DELETED-CLAUSES.

(in-package #:sat-backend-cdcl)

;;; The search state, the clause store, the heap and the trail are in
;;; solver.lisp. Steps are cited by the numbers of the header above.

;;; ------------------------------------------------------ 1. propagation

(defun %propagate (s)
  "Step 1: propagate the trail from QHEAD with two watched literals. Returns
the id of a clause whose literals are all false (one :CONFLICTS), or -1 at
the fixpoint. Conses only when a watch list grows (%WATCH)."
  (declare (type %solver s)
           (optimize (speed 3) (safety 1) (debug 0))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((lval (s-lval s)) (trail (s-trail s)) (level (s-level s)) (reason (s-reason s))
        (watches (s-watches s)) (wfill (s-wfill s)) (clauses (s-clauses s))
        (qhead (s-qhead s)) (tsize (s-trail-size s)) (dl (s-dl s))
        (confl -1) (props 0))
    (declare (type %bytevec lval) (type %fixvec trail level reason wfill)
             (type simple-vector watches clauses)
             (type fixnum qhead tsize dl confl props))
    (macrolet ((imply (literal id)
                 `(let ((v (ash ,literal -1)))
                    (setf (aref lval ,literal) 1
                          (aref lval (logxor ,literal 1)) -1
                          (aref level v) dl
                          (aref reason v) ,id
                          (aref trail tsize) ,literal)
                    (incf tsize)
                    (incf props))))
      (loop while (and (< qhead tsize) (minusp confl))
            do (let* ((fl (logxor (aref trail qhead) 1)) ; the literal that became false
                      (ws (svref watches fl))
                      (end (aref wfill fl))
                      (i 0)
                      (j 0))
                 (declare (type fixnum fl end i j) (type %fixvec ws))
                 (incf qhead)
                 (macrolet ((keep (entry blocker)
                              `(progn (setf (aref ws j) ,entry
                                            (aref ws (1+ j)) ,blocker)
                                      (incf j 2))))
                   (loop while (< i end)
                         do (let ((entry (aref ws i))
                                  (blocker (aref ws (1+ i))))
                              (declare (type fixnum entry blocker))
                              (incf i 2)
                              (cond
                                ((= 1 (aref lval blocker))
                                 (keep entry blocker))
                                ((minusp entry)
                                 ;; A binary clause: the blocker is its other literal.
                                 (keep entry blocker)
                                 (if (zerop (aref lval blocker))
                                     (imply blocker (lognot entry))
                                     (progn (setf confl (lognot entry))
                                            (return))))
                                (t
                                 (let* ((c (svref clauses entry))
                                        (len (length c)))
                                   (declare (type %fixvec c) (type fixnum len))
                                   ;; The false watch goes to position 1.
                                   (when (= fl (aref c 0))
                                     (setf (aref c 0) (aref c 1)
                                           (aref c 1) fl))
                                   (let ((first (aref c 0)))
                                     (declare (type fixnum first))
                                     (if (and (/= first blocker) (= 1 (aref lval first)))
                                         (keep entry first)
                                         (let ((k 2))
                                           (declare (type fixnum k))
                                           (loop while (and (< k len)
                                                            (= -1 (aref lval (aref c k))))
                                                 do (incf k))
                                           (if (< k len)
                                               ;; A new watch, never FL: the clause has
                                               ;; no repeated literal.
                                               (let ((new (aref c k)))
                                                 (setf (aref c 1) new
                                                       (aref c k) fl)
                                                 (%watch s new entry first))
                                               (progn
                                                 (keep entry first)
                                                 (if (zerop (aref lval first))
                                                     (imply first entry)
                                                     (progn (setf confl entry)
                                                            (return)))))))))))))
                   ;; After a conflict, keep the watches not visited.
                   (loop while (< i end)
                         do (setf (aref ws j) (aref ws i)
                                  (aref ws (1+ j)) (aref ws (1+ i)))
                            (incf i 2)
                            (incf j 2))
                   (setf (aref wfill fl) j)))))
    (setf (s-qhead s) qhead
          (s-trail-size s) tsize)
    (incf (s-propagations s) props)
    (when (>= confl 0)
      (incf (s-conflicts s)))
    confl))

;;; ------------------------------------------------- activities (EVSIDS)

(defun %rescale-vars (s)
  "Scale every variable activity and the bump down together (order kept),
then restore the heap order (an activity may have reached 0, a new tie)."
  (declare (type %solver s))
  (let ((act (s-act s)))
    (loop for v from 1 to (s-n s)
          do (setf (aref act v) (* (aref act v) 1d-100)))
    (setf (s-var-inc s) (* (s-var-inc s) 1d-100))
    (%heap-rebuild s)))

(defun %rescale-clauses (s)
  (declare (type %solver s))
  (let ((act (s-clause-act s)))
    (loop for id from (s-m s) below (s-nclauses s)
          do (setf (aref act id) (* (aref act id) 1d-20)))
    (setf (s-cla-inc s) (* (s-cla-inc s) 1d-20))))

(defun %bump-var (s v)
  (declare (type %solver s) (type fixnum v)
           (optimize (speed 3) (safety 1)))
  (let ((act (s-act s)))
    (when (> (incf (aref act v) (s-var-inc s)) 1d100)
      (%rescale-vars s))
    (let ((i (aref (s-heap-index s) v)))
      (when (>= i 0)
        (%heap-up s i)))))

(defun %bump-clause (s id)
  (declare (type %solver s) (type fixnum id)
           (optimize (speed 3) (safety 1)))
  (let ((act (s-clause-act s)))
    (when (> (incf (aref act id) (s-cla-inc s)) 1d20)
      (%rescale-clauses s))))

(defun %decay (s)
  "Step 2: the variable bump grows by 1/VARIABLE-DECAY, the clause bump by
1/CLAUSE-DECAY, each rescaled before it can overflow."
  (declare (type %solver s))
  (setf (s-var-inc s) (/ (s-var-inc s) (s-var-decay s)))
  (loop while (> (s-var-inc s) 1d100) do (%rescale-vars s))
  (setf (s-cla-inc s) (/ (s-cla-inc s) (s-cla-decay s)))
  (loop while (> (s-cla-inc s) 1d20) do (%rescale-clauses s)))

;;; ----------------------------------------------------------- 2. analysis

(defun %analyze (s confl)
  "Step 2: the first-UIP clause of conflict clause CONFL into OUT, asserting
literal at OUT[0], bumping every variable met above level 0 and every learnt
clause met; then minimised. Returns its size. Reasons are walked by variable:
the literal a reason explains may sit anywhere in it."
  (declare (type %solver s) (type fixnum confl)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((clauses (s-clauses s)) (seen (s-seen s)) (level (s-level s)) (reason (s-reason s))
        (trail (s-trail s)) (out (s-out s)) (m (s-m s)) (dl (s-dl s))
        (path 0) (size 1) (index (1- (s-trail-size s))) (pvar 0) (p 0))
    (declare (type simple-vector clauses) (type %bytevec seen)
             (type %fixvec level reason trail out)
             (type fixnum m dl path size index pvar p))
    (loop
      (when (>= confl m)
        (%bump-clause s confl))
      (let ((c (svref clauses confl)))
        (declare (type %fixvec c))
        (loop for q of-type fixnum across c
              for v of-type fixnum = (ash q -1)
              do (when (and (/= v pvar) (zerop (aref seen v)) (plusp (aref level v)))
                   (%bump-var s v)
                   (setf (aref seen v) 1)
                   (if (>= (aref level v) dl)
                       (incf path)
                       (progn (setf (aref out size) q)
                              (incf size))))))
      ;; The newest marked literal of the conflict level.
      (loop while (zerop (aref seen (ash (aref trail index) -1)))
            do (decf index))
      (setf p (aref trail index)
            pvar (ash p -1)
            confl (aref reason pvar)
            (aref seen pvar) 0)
      (decf index)
      (when (zerop (decf path))
        (return)))
    (setf (aref out 0) (logxor p 1))
    (%minimize-clause s size)))

(declaim (inline %abstract-level))
(defun %abstract-level (level v)
  (declare (type %fixvec level) (type fixnum v))
  (ash 1 (logand (aref level v) 31)))

(defun %redundant-p (s p abstract)
  "MiniSat's litRedundant with an explicit stack: is the negation of P
implied, through reasons, by the marked literals and level 0? New marks are
pushed on TOCLEAR; a failed attempt removes its own."
  (declare (type %solver s) (type fixnum p abstract)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((stack (s-stack s)) (toclear (s-toclear s)) (seen (s-seen s))
        (level (s-level s)) (reason (s-reason s)) (clauses (s-clauses s))
        (top 1) (base (s-nclear s)) (nclear (s-nclear s)))
    (declare (type %fixvec stack toclear level reason) (type %bytevec seen)
             (type simple-vector clauses) (type fixnum top base nclear))
    (setf (aref stack 0) p)
    (loop while (plusp top)
          do (decf top)
             (let* ((xv (ash (aref stack top) -1))
                    (c (svref clauses (aref reason xv))))
               (declare (type fixnum xv) (type %fixvec c))
               (loop for q of-type fixnum across c
                     for v of-type fixnum = (ash q -1)
                     do (when (and (/= v xv) (zerop (aref seen v)) (plusp (aref level v)))
                          (if (and (>= (aref reason v) 0)
                                   (logtest (%abstract-level level v) abstract))
                              (setf (aref seen v) 1
                                    (aref stack top) q
                                    top (1+ top)
                                    (aref toclear nclear) q
                                    nclear (1+ nclear))
                              (progn
                                (loop for i from base below nclear
                                      do (setf (aref seen (ash (aref toclear i) -1)) 0))
                                (setf (s-nclear s) base)
                                (return-from %redundant-p nil)))))))
    (setf (s-nclear s) nclear)
    t))

(defun %minimize-clause (s size)
  "Step 2: drop literals of OUT[1..SIZE) per CLAUSE-MINIMIZATION (:RECURSIVE,
:BASIC or NIL); clear every SEEN mark. Returns the new size."
  (declare (type %solver s) (type fixnum size)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((out (s-out s)) (seen (s-seen s)) (reason (s-reason s)) (level (s-level s))
        (clauses (s-clauses s)) (toclear (s-toclear s))
        (j 1))
    (declare (type %fixvec out reason level toclear) (type %bytevec seen)
             (type simple-vector clauses) (type fixnum j))
    (replace toclear out :start2 1 :end2 size)
    (setf (s-nclear s) (1- size))
    (ecase (s-minimization s)
      ((nil) (setf j size))
      (:basic
       (loop for i of-type fixnum from 1 below size
             for q of-type fixnum = (aref out i)
             for x of-type fixnum = (ash q -1)
             for r of-type fixnum = (aref reason x)
             do (when (or (minusp r)
                          (loop for y of-type fixnum across (the %fixvec (svref clauses r))
                                for u of-type fixnum = (ash y -1)
                                thereis (and (/= u x) (zerop (aref seen u)) (plusp (aref level u)))))
                  (setf (aref out j) q)
                  (incf j))))
      (:recursive
       (let ((abstract 0))
         (declare (type fixnum abstract))
         (loop for i of-type fixnum from 1 below size
               do (setf abstract (logior abstract (%abstract-level level (ash (aref out i) -1)))))
         (loop for i of-type fixnum from 1 below size
               for q of-type fixnum = (aref out i)
               do (when (or (minusp (aref reason (ash q -1)))
                            (not (%redundant-p s q abstract)))
                    (setf (aref out j) q)
                    (incf j))))))
    (loop for i of-type fixnum from 0 below (s-nclear s)
          do (setf (aref seen (ash (aref toclear i) -1)) 0))
    j))

(defun %second-watch (s size)
  "Move the literal of OUT[1..SIZE) with the highest level to OUT[1]; return
that level, the backjump level (0 for a unit clause)."
  (declare (type %solver s) (type fixnum size))
  (let ((out (s-out s)) (level (s-level s)) (bt 0) (at 1))
    (declare (type fixnum bt at))
    (loop for i from 1 below size
          for lv = (aref level (ash (aref out i) -1))
          when (> lv bt) do (setf bt lv at i))
    (when (> size 1)
      (rotatef (aref out 1) (aref out at)))
    bt))

(defun %lbd (s size)
  "The number of distinct levels of OUT[0..SIZE)."
  (declare (type %solver s) (type fixnum size))
  (let ((out (s-out s)) (level (s-level s)) (marks (s-level-stamp s))
        (stamp (incf (s-stamp s))) (count 0))
    (declare (type fixnum count))
    (loop for i from 0 below size
          for lv = (aref level (ash (aref out i) -1))
          unless (= stamp (aref marks lv))
            do (setf (aref marks lv) stamp)
               (incf count))
    count))

;;; -------------------------------------------------------------- reduction

(defun %sweep-watches (s)
  "Drop the watches of deleted clauses (binary clauses are never deleted)."
  (declare (type %solver s)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((watches (s-watches s)) (wfill (s-wfill s)) (deleted (s-clause-deleted s)))
    (declare (type simple-vector watches) (type %fixvec wfill) (type %bytevec deleted))
    (loop for l of-type fixnum from 2 below (length watches)
          do (let ((ws (svref watches l)) (end (aref wfill l)) (j 0))
               (declare (type %fixvec ws) (type fixnum end j))
               (loop for i of-type fixnum from 0 below end by 2
                     for entry of-type fixnum = (aref ws i)
                     unless (and (>= entry 0) (= 1 (aref deleted entry)))
                       do (setf (aref ws j) entry
                                (aref ws (1+ j)) (aref ws (1+ i)))
                          (incf j 2))
               (setf (aref wfill l) j)))))

(defun %reduce (s)
  "REDUCTION: delete the worse half (floor n/2) of the n deletable learnt
clauses (LBD above 2, not the reason of an assigned literal). Worse: higher
LBD, then lower activity, then older (a lower id): a total order."
  (declare (type %solver s))
  (let* ((stamp (incf (s-stamp s)))
         (lock (s-clause-lock s)) (lbd (s-clause-lbd s)) (act (s-clause-act s))
         (deleted (s-clause-deleted s)) (clauses (s-clauses s))
         (learnts (s-learnts s)) (nlearnts (s-nlearnts s))
         (reason (s-reason s)) (trail (s-trail s))
         (candidates (%fixvec nlearnts))
         (count 0))
    (declare (type fixnum count))
    (loop for i from 0 below (s-trail-size s)
          for r = (aref reason (ash (aref trail i) -1))
          when (>= r 0) do (setf (aref lock r) stamp))
    (loop for i from 0 below nlearnts
          for id = (aref learnts i)
          when (and (> (aref lbd id) 2) (/= stamp (aref lock id)))
            do (setf (aref candidates count) id)
               (incf count))
    (let ((worse (sort (subseq candidates 0 count)
                       (lambda (a b)
                         (declare (type fixnum a b))
                         (let ((x (aref lbd a)) (y (aref lbd b)))
                           (if (/= x y)
                               (> x y)
                               (let ((p (aref act a)) (q (aref act b)))
                                 (if (/= p q) (< p q) (< a b))))))))
          (k (floor count 2))
          (empty (%fixvec 0)))
      (dotimes (i k)
        (let ((id (aref worse i)))
          (setf (aref deleted id) 1
                (svref clauses id) empty)))
      (incf (s-reductions s))
      (incf (s-deleted s) k)
      (when (plusp k)
        (%sweep-watches s)
        (let ((j 0))
          (loop for i from 0 below nlearnts
                for id = (aref learnts i)
                when (zerop (aref deleted id))
                  do (setf (aref learnts j) id)
                     (incf j))
          (setf (s-nlearnts s) j))))
    ;; R_{k+1} = R_k + REDUCE-BASE + REDUCE-INCREMENT * k
    (let ((k (incf (s-reduce-k s))))
      (setf (s-next-reduce s)
            (%clamp (+ (s-next-reduce s) (s-reduce-base s) (* (s-reduce-inc s) k)))))))

;;; --------------------------------------------------------------- restarts

(defun %luby (i)
  "The I-th term (from 1) of the Luby sequence 1 1 2 1 1 2 4 1 1 2 ..."
  (declare (type (integer 1 *) i))
  (loop
    (let ((k (integer-length i)))
      (if (= i (1- (ash 1 k)))
          (return (ash 1 (1- k)))
          (setf i (- i (1- (ash 1 (1- k)))))))))

(defun %glucose-push (s lbd)
  "Put LBD in the ring of this run's last WINDOW LBDs."
  (declare (type %solver s) (type fixnum lbd))
  (let ((count (s-ring-count s))
        (window (s-window s))
        (ring (s-ring s)))
    (if (< count window)
        (progn
          (when (= count (length ring))
            (let ((grown (%fixvec (min window (* 2 (max 1 count))))))
              (replace grown ring)
              (setf (s-ring s) grown ring grown)))
          (setf (aref ring count) lbd
                (s-ring-count s) (1+ count))
          (incf (s-ring-sum s) lbd))
        (let ((pos (s-ring-pos s)))
          (incf (s-ring-sum s) (- lbd (aref ring pos)))
          (setf (aref ring pos) lbd
                (s-ring-pos s) (if (= (1+ pos) window) 0 (1+ pos)))))))

(defun %restart-due-p (s lbd)
  "RESTARTS, checked after every learnt clause (its LBD)."
  (declare (type %solver s) (type fixnum lbd))
  (ecase (s-restart-policy s)
    ((nil) nil)
    (:luby
     (>= (incf (s-run-learnt s)) (s-run-limit s)))
    (:glucose
     (%glucose-push s lbd)
     (and (= (s-ring-count s) (s-window s))
          ;; MARGIN * (ring sum / WINDOW) > (LBD total / learnt clauses)
          (> (* (s-margin s) (float (s-ring-sum s) 1d0) (float (s-learnt s) 1d0))
             (* (float (s-lbd-total s) 1d0) (float (s-window s) 1d0)))))))

(defun %restart (s)
  "Back to level 0 (phases saved); learnt clauses, activities and phases stay.
The next run starts: its Luby limit, an empty Glucose ring."
  (declare (type %solver s))
  (%cancel-until s 0)
  (incf (s-restarts s))
  (let ((k (incf (s-run-k s))))
    (setf (s-run-learnt s) 0
          (s-run-limit s) (%clamp (* (s-luby-unit s) (%luby k)))
          (s-ring-count s) 0
          (s-ring-pos s) 0
          (s-ring-sum s) 0)))

;;; --------------------------------------------- 2-3. learning, backjumping

(defun %push-learnt (s id)
  (declare (type %solver s) (type fixnum id))
  (let ((learnts (s-learnts s))
        (k (s-nlearnts s)))
    (when (= k (length learnts))
      (let ((grown (%fixvec (* 2 (max 1 k)))))
        (replace grown learnts)
        (setf (s-learnts s) grown learnts grown)))
    (setf (aref learnts k) id
          (s-nlearnts s) (1+ k))))

(defun %learn (s confl)
  "Steps 2 and 3 for a conflict above level 0: analyse, call the hook, decay;
backjump, keep the clause, assert its first literal; then REDUCE when due and
RESTART when due."
  (declare (type %solver s) (type fixnum confl))
  (let* ((conflict-level (s-dl s))
         (size (%analyze s confl))
         (out (s-out s))
         (bt (%second-watch s size))
         (lbd (%lbd s size))
         (hook (s-learnt-hook s)))
    (when hook
      (funcall hook (loop for i from 0 below size collect (%int (aref out i))) lbd))
    (incf (s-learnt s))
    (incf (s-lbd-total s) lbd)
    (%decay s)
    (when (< bt (1- conflict-level))
      (incf (s-backjumps s)))
    (%cancel-until s bt)
    ;; A unit clause is a level-0 fact; a longer one joins the learnt
    ;; database, watched on OUT[0] and OUT[1], with one bump (MiniSat's
    ;; activity of a new learnt clause).
    (let ((id (%add-clause s (subseq out 0 size) lbd)))
      (when (> size 1)
        (%attach s id)
        (%push-learnt s id)
        (%bump-clause s id))
      (%assign s (aref out 0) id)
      (incf (s-propagations s)))
    (when (and (s-reduce-p s) (>= (s-learnt s) (s-next-reduce s)))
      (%reduce s))
    (when (%restart-due-p s lbd)
      (%restart s))))

;;; -------------------------------------------------------- final conflict

(defun %analyze-final (s a)
  "FINAL CONFLICT: assumption A is false at its turn. Mark the set S in
IN-CORE: A, and the assumptions reached from (not A) through reasons."
  (declare (type %solver s) (type fixnum a))
  (let ((in-core (s-in-core s)) (seen (s-seen s)) (level (s-level s))
        (reason (s-reason s)) (trail (s-trail s)) (clauses (s-clauses s))
        (av (ash a -1)))
    (setf (aref in-core a) 1)
    (when (plusp (aref level av))
      (setf (aref seen av) 1)
      (loop for i from (1- (s-trail-size s)) downto (aref (s-trail-lim s) 0)
            do (let* ((l (aref trail i))
                      (v (ash l -1)))
                 (when (= 1 (aref seen v))
                   (let ((r (aref reason v)))
                     (if (minusp r)
                         (setf (aref in-core l) 1)
                         (loop for q across (the %fixvec (svref clauses r))
                               for u = (ash q -1)
                               unless (or (= u v) (zerop (aref level u)))
                                 do (setf (aref seen u) 1))))
                   (setf (aref seen v) 0)))))))

(defun %core (s assumptions)
  "The elements of ASSUMPTIONS in S, in the given order, each once."
  (declare (type %solver s))
  (let ((in-core (s-in-core s)))
    (loop for a in assumptions
          for l = (%lit a)
          when (= 1 (aref in-core l))
            collect a
            and do (setf (aref in-core l) 0))))

;;; ------------------------------------------------------ 4. decision point

(defun %all-input-true-p (s)
  "Step 4b: every input clause has a true literal. Moves SCAN past the true
clauses, caching each one's true literal."
  (declare (type %solver s)
           (optimize (speed 3) (safety 1))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((lval (s-lval s)) (clauses (s-clauses s)) (sat-lit (s-sat-lit s))
        (m (s-m s)) (p (s-scan s)))
    (declare (type %bytevec lval) (type simple-vector clauses) (type %fixvec sat-lit)
             (type fixnum m p))
    (loop while (< p m)
          do (unless (= 1 (aref lval (aref sat-lit p)))
               (let ((found 0))
                 (declare (type fixnum found))
                 (loop for q of-type fixnum across (the %fixvec (svref clauses p))
                       when (= 1 (aref lval q))
                         do (setf found q)
                            (return))
                 (when (zerop found)
                   (return))
                 (setf (aref sat-lit p) found)))
             (incf p))
    (setf (s-scan s) p)
    (= p m)))

(defun %order-choice (s)
  "Step 4d with ORDER: call it once on the candidates (a fresh ascending list
of the unassigned variables of the input clauses with no true literal) and
return its choice, or signal SAT-ERROR when it is not one of them."
  (declare (type %solver s))
  (let ((stamp (incf (s-stamp s))) (cand (s-cand s)) (lval (s-lval s))
        (clauses (s-clauses s)) (n (s-n s)))
    ;; The clauses before SCAN are true (4b just ran).
    (loop for p from (s-scan s) below (s-m s)
          for c of-type %fixvec = (svref clauses p)
          unless (loop for q across c thereis (= 1 (aref lval q)))
            do (loop for q across c
                     when (zerop (aref lval q))
                       do (setf (aref cand (ash q -1)) stamp)))
    (let* ((candidates (loop with list = '()
                             for v from n downto 1
                             when (= stamp (aref cand v)) do (push v list)
                             finally (return list)))
           (choice (funcall (s-order s) candidates)))
      (unless (and (typep choice 'fixnum) (<= 1 choice n) (= stamp (aref cand choice)))
        (error 'sat-error
               :message (format nil ":ORDER returned ~S, not one of the candidates ~S"
                                choice candidates)))
      choice)))

(defun %heap-choice (s)
  "Step 4d without ORDER: the unassigned input variable of greatest activity,
ties to the lower index."
  (declare (type %solver s))
  (let ((lval (s-lval s)))
    (loop
      (assert (plusp (s-heap-size s)) () "CDCL: no unassigned variable to decide")
      (let ((v (%heap-pop s)))
        (when (zerop (aref lval (* 2 v)))
          (return v))))))

(defun %budget-wait (s count)
  "BUDGET: while COUNT (the call's decisions or learnt clauses so far) has
reached it, publish the statistics and signal; CONTINUE and STORE-VALUE return
the new budget, USE-VALUE throws to the front end."
  (declare (type %solver s) (type fixnum count))
  (loop while (>= count (s-budget s))
        do (%publish s)
           (setf (s-budget s) (signal-budget-exceeded (s-budget s)))))

(defun %decision-point (s)
  "Step 4, with nothing to propagate: :SAT, :UNSAT (an assumption is false,
S marked when a core is wanted), or NIL once a literal is assigned at a new
level."
  (declare (type %solver s))
  ;; 4a. The decision level is the index of the next assumption.
  (loop while (< (s-dl s) (s-nassumps s))
        do (let* ((a (aref (s-assumps s) (s-dl s)))
                  (value (aref (s-lval s) a)))
             (cond ((= value 1)
                    (%new-level s))
                   ((= value -1)
                    (when (s-want-core s)
                      (%analyze-final s a))
                    (return-from %decision-point :unsat))
                   (t
                    (%new-level s)
                    (%assign s a -1)
                    (return-from %decision-point nil)))))
  ;; 4b
  (when (%all-input-true-p s)
    (return-from %decision-point :sat))
  ;; 4c
  (when (and (s-budget s) (eq (s-budget-unit s) :decisions))
    (%budget-wait s (s-decisions s)))
  ;; 4d
  (let* ((v (if (s-order s) (%order-choice s) (%heap-choice s)))
         (saved (aref (s-saved s) v))
         (value (cond ((s-phase s) (funcall (s-phase s) v))
                      ((and (s-phase-saving s) (/= 0 saved)) (= 1 saved))
                      (t (s-default-phase s)))))
    (incf (s-decisions s))
    (%new-level s)
    (%assign s (if value (* 2 v) (1+ (* 2 v))) -1)
    nil))

;;; ------------------------------------------------------------- the loop

(defun %search (s)
  "The loop of this file's header: T for SAT, NIL for UNSAT."
  (declare (type %solver s))
  (loop
    (let ((confl (%propagate s)))
      (cond ((minusp confl)
             (case (%decision-point s)
               (:sat (return t))
               (:unsat (return nil))))
            ((zerop (s-dl s))
             (return nil))
            (t
             (when (and (s-budget s) (eq (s-budget-unit s) :conflicts))
               (%budget-wait s (s-learnt s)))
             (%learn s confl))))))

(defun %cdcl-search (backend cnf assumptions order phase budget want-core)
  "The search of both methods, from nothing. Returns (values T literals NIL)
for SAT, (values NIL NIL core) for UNSAT, CORE NIL unless WANT-CORE. The
statistics are published however the call ends."
  (let ((s (%make-solver backend)))
    (unwind-protect
         (let ((clause-lists (cnf-clauses cnf)))
           (%setup s (cnf-variable-count cnf) (length clause-lists)
                   assumptions order phase budget want-core)
           (if (and (%load s clause-lists) (%search s))
               (values t
                       (loop for i from 0 below (s-trail-size s)
                             collect (%int (aref (s-trail s) i)))
                       nil)
               (values nil nil (and want-core (%core s assumptions)))))
      (%publish s))))

(defmethod backend-solve ((backend cdcl-backend) cnf &key assumptions order phase budget)
  "CDCL search of CNF under ASSUMPTIONS: the loop in this file's header."
  (multiple-value-bind (sat literals)
      (%cdcl-search backend cnf assumptions order phase budget nil)
    (if sat
        (values literals t)
        (values nil nil))))

(defmethod backend-final-conflict ((backend cdcl-backend) cnf assumptions
                                   &key budget order phase)
  "BACKEND-SOLVE's search; on UNSAT, the assumptions of the final conflict
(header: FINAL CONFLICT)."
  (multiple-value-bind (sat literals core)
      (%cdcl-search backend cnf assumptions order phase budget t)
    (if sat
        (values nil nil literals)
        (values core t))))
