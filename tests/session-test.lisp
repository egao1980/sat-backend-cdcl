(in-package #:sat-backend-cdcl/tests)

;;; 0.2.0 native sessions (src/session.lisp). sat-protocol's conformance suite
;;; already checks every session answer against brute force and the fresh front
;;; ends, in both configurations; these tests pin what is CDCL's own: the state
;;; is native and persistent (no from-scratch call, learnt clauses survive),
;;; per-call statistics and budgets, level-0 additions, cut-short calls,
;;; determinism, and every configuration against sat-backend-dpll.

(defclass recording-cdcl (cdcl-backend)
  ((calls :initform nil :accessor recording-cdcl-calls))
  (:documentation "A CDCL-BACKEND recording the from-scratch GFs it is called with."))

(defmethod backend-solve :before ((b recording-cdcl) cnf &key &allow-other-keys)
  (declare (ignore cnf))
  (push 'backend-solve (recording-cdcl-calls b)))

(defmethod backend-final-conflict :before ((b recording-cdcl) cnf assumptions &key &allow-other-keys)
  (declare (ignore cnf assumptions))
  (push 'backend-final-conflict (recording-cdcl-calls b)))

(defmethod backend-minimize :before ((b recording-cdcl) cnf objective &key &allow-other-keys)
  (declare (ignore cnf objective))
  (push 'backend-minimize (recording-cdcl-calls b)))

(defun guarded-php (pigeons holes selector-offset)
  "PHP(PIGEONS, HOLES) over variables 1..p*h with every clause guarded by -S,
S = p*h + SELECTOR-OFFSET + 1. Returns (values clauses s)."
  (multiple-value-bind (clauses n) (pigeonhole pigeons holes)
    (let ((s (+ n selector-offset 1)))
      (values (mapcar (lambda (c) (cons (- s) c)) clauses) s))))

(defun session-of (backend clauses nvars)
  (session-from-clauses clauses nvars :backend backend))

(deftest session-is-native
  (let ((b (make-instance 'recording-cdcl)))
    (with-sat-session (s :backend b)
      (ok (session-backend-state s) "a stateful session")
      (session-add-variables s 6)
      (session-add-clauses s '((1 2) (-1 3) (-3 -4) (4 5 6) (-5 -6)))
      (session-solve s)
      (session-solve s :assumptions '(1 4))
      (session-unsat-core s :minimal t)
      (dolist (strategy '(:linear-bdd :linear-totalizer :stratified :core-guided))
        (session-minimize s '((2 . 1) (1 . 4) (1 . 5)) :strategy strategy)
        (session-minimize s '(:lex ((1 . 2)) ((1 . 6))) :strategy strategy :budget 100))
      (ok (null (recording-cdcl-calls b))
          "no session operation calls BACKEND-SOLVE, BACKEND-FINAL-CONFLICT or BACKEND-MINIMIZE"))))

(deftest session-learnt-clauses-survive
  ;; PHP(7,6) behind a selector S: refuting it under S costs many conflicts;
  ;; once refuted, (-S) follows from what was learnt, so the same call again
  ;; needs (almost) none, and S stays a free choice for the other clauses.
  (multiple-value-bind (php s) (guarded-php 7 6 0)
    (let ((b (cdcl)))
      (with-sat-session (session :backend b)
        (session-add-variables session s)
        (session-add-clauses session php)
        (session-add-clauses session (list (list s (- s 1))))
        (ok (equal (list (list s) t)
                   (multiple-value-list
                    (progn (session-solve session :assumptions (list s))
                           (session-unsat-core session))))
            "UNSAT under S, which is the core")
        (let ((first (stats b :conflicts)))
          (ok (> first 100) (format nil "the first refutation: ~D conflicts" first))
          (ok (null (nth-value 1 (session-solve session :assumptions (list s)))))
          (let ((second (stats b :conflicts)))
            (ok (<= second (floor first 20))
                (format nil "the second one: ~D conflicts, against ~D" second first))))
        (multiple-value-bind (model sat) (session-solve session)
          (ok (and sat (member (- s) model) (member (- s 1) model)) "without the assumption: -S, so the last clause"))
        (backend-final-conflict b (clauses->cnf (append php (list (list s (- s 1)))) s) (list s))
        (ok (> (stats b :conflicts) 100) "a from-scratch call refutes it all over again")))))

(deftest session-statistics-per-call
  (multiple-value-bind (php s) (guarded-php 6 5 0)
    (let ((b (cdcl)))
      (with-sat-session (session :backend b)
        (session-add-variables session s)
        (session-add-clauses session php)
        (session-solve session :assumptions (list s))
        (let ((plist (cdcl-backend-statistics b)))
          (ok (equal +statistics-keys+ (loop for (k) on plist by #'cddr collect k)))
          (ok (every (lambda (k) (typep (getf plist k) '(integer 0 *))) +statistics-keys+))
          (ok (plusp (getf plist :conflicts))))
        (session-solve session :assumptions (list (- s)))
        (ok (eql 0 (stats b :conflicts)) "the counters start at 0 each call")
        (ok (eql 0 (stats b :learnt-clauses)))
        (session-add-clauses session '((1)))
        (ok (eql 0 (stats b :conflicts)) "adding clauses is not a call")))))

(deftest session-level-0-additions
  (let ((b (cdcl)))
    (with-sat-session (s :backend b)
      (session-add-variables s 4)
      (session-add-clauses s '((1) (-1 2) (3 4)))
      (multiple-value-bind (model sat) (session-solve s :assumptions '(-3))
        (ok (and sat (equal '(1 2 -3 4) model))))
      ;; The last call left the trail above level 0; clauses arrive anyway.
      (session-add-clauses s '((-2 -4 3)))
      (ok (null (nth-value 1 (session-solve s :assumptions '(-3)))) "1, 2, -3 force 4, then -4")
      (ok (equal '((-3) t) (multiple-value-list (session-unsat-core s))))
      (session-add-clauses s '((-4 -3) (3 -1 -2 -2)))
      (ok (equal '((1 2 3 -4) t) (multiple-value-list (session-solve s))) "a unit at level 0 after a call")
      (session-add-clauses s '((-1 -3)))
      (ok (equal '(nil nil) (multiple-value-list (session-solve s))) "every literal false: UNSAT for good")
      (ok (equal '(nil t) (multiple-value-list (session-unsat-core s))))
      (ok (equal '(nil nil) (multiple-value-list (session-solve s :assumptions '(2)))))
      (ok (equal '(nil t) (multiple-value-list (session-unsat-core s))) "the core is NIL: the clauses alone")
      (ok (equal '(nil t) (multiple-value-list
                           (backend-session-final-conflict b s '(4 -4))))
          "a session UNSAT for good: core NIL"))))

;;; Random 3-SAT over 120 variables at ratio 4.2: satisfiable or not, every
;;; call under new assumptions needs decisions and conflicts.
(defparameter *budget-instance* '(:seed 5151 :nvars 120 :nclauses 504))

(defun budget-sessions (unit)
  "Two sessions of *BUDGET-INSTANCE*, each on a fresh backend with BUDGET-UNIT UNIT."
  (destructuring-bind (&key seed nvars nclauses) *budget-instance*
    (let ((clauses (random-3sat (make-rng seed) nvars nclauses)))
      (flet ((one () (session-of (make-instance 'cdcl-backend :budget-unit unit) clauses nvars)))
        (values (one) (one) clauses)))))

(deftest-parametrize session-budget-resumes
    ((unit) :ids ("decisions" "conflicts") (:decisions) (:conflicts))
  ;; Two sessions with the same history: a call without a budget, and the same
  ;; call stepped one unit at a time by STORE-VALUE, give the same answer and
  ;; statistics. Then calls cut short by USE-VALUE and by a throw, and the
  ;; next call is still right.
  (multiple-value-bind (sa sb clauses) (budget-sessions unit)
    (let ((a (session-backend sa)) (b (session-backend sb)))
      (unwind-protect
           (progn
             (session-solve sa :assumptions '(1 -2 3))
             (session-solve sb :assumptions '(1 -2 3) :budget 1000000)
             (ok (equal (cdcl-backend-statistics a) (cdcl-backend-statistics b))
                 "an unspent budget changes nothing")
             (let ((plain (multiple-value-list (session-solve sa :assumptions '(-4 5))))
                   (signals 0))
               (let ((stepped (handler-bind ((sat-budget-exceeded
                                               (lambda (c)
                                                 (incf signals)
                                                 (store-value (1+ (sat-budget-exceeded-budget c)) c))))
                                (multiple-value-list (session-solve sb :assumptions '(-4 5) :budget 0)))))
                 (ok (plusp signals) (format nil "~D signals" signals))
                 (ok (equal plain stepped) "the same answer")
                 (ok (equal (cdcl-backend-statistics a) (cdcl-backend-statistics b))
                     "the same statistics")))
             (ok (equal '(:cut nil)
                        (handler-bind ((sat-budget-exceeded (lambda (c) (use-value :cut c))))
                          (multiple-value-list (session-solve sb :assumptions '(6 -7) :budget 2)))))
             (ok (eq :thrown (block out
                               (handler-bind ((sat-budget-exceeded
                                                (lambda (c) (declare (ignore c)) (return-from out :thrown))))
                                 (session-solve sb :assumptions '(-6 8) :budget 3)))))
             (dolist (assumptions '((-6 8) (6 -7) ()))
               (multiple-value-bind (model sat) (session-solve sb :assumptions assumptions)
                 (ok (eq (nth-value 1 (session-solve sa :assumptions assumptions)) sat)
                     (format nil "after the exits, ~S: the status of the other session" assumptions))
                 (when sat
                   (ok (model-satisfies-p model clauses assumptions))))))
        (close-session sa)
        (close-session sb)))))

(deftest session-determinism
  ;; The same operations on two sessions: the same answers and statistics.
  (flet ((script (backend)
           (let ((rng (make-rng 777)) (trace '()))
             (with-sat-session (s :backend backend)
               (let ((vars (session-add-variables s 30)))
                 (dotimes (step 12)
                   (session-add-clauses s (loop repeat 12 collect (random-clause* rng vars 3)))
                   (push (multiple-value-list
                          (session-solve s :assumptions (random-literals* rng vars 3)))
                         trace)
                   (push (cdcl-backend-statistics backend) trace)
                   (when (zerop (mod step 4))
                     (push (multiple-value-list
                            (session-minimize s (random-objective* rng vars 6) :strategy :core-guided))
                           trace)
                     (push (cdcl-backend-statistics backend) trace)))))
             (nreverse trace))))
    (dolist (config '("default" "glucose" "stress"))
      (ok (equal (script (configured config)) (script (configured config))) config))))

(deftest session-learnt-hook
  ;; Every clause learnt in a session follows from the clauses given so far
  ;; (all the models of those clauses satisfy it).
  (let* ((rng (make-rng 4711)) (step 0) (learnt '())
         (b (make-instance 'cdcl-backend :reduce-base 8 :reduce-increment 2
                                         :learnt-hook (lambda (literals lbd)
                                                        (declare (ignore lbd))
                                                        (push (cons step (copy-list literals)) learnt))))
         (given (make-array 8)))
    (with-sat-session (s :backend b)
      (let ((vars (session-add-variables s 13)) (clauses '()))
        (dotimes (i 8)
          (setf step i)
          (let ((new (loop repeat 8 collect (random-clause* rng vars 3))))
            (session-add-clauses s new)
            (setf clauses (append clauses new)
                  (aref given i) clauses))
          (dotimes (j 3)
            (session-solve s :assumptions (random-literals* rng vars 3))))))
    (ok (plusp (length learnt)) (format nil "~D clauses learnt" (length learnt)))
    (ok (loop for i below 8
              for models = (brute-models (aref given i) 13)
              always (every (lambda (entry) (implied-by-models-p (cdr entry) models))
                            (remove i learnt :key #'car :test-not #'eql)))
        "each one implied by the clauses given before its call")))

(defun session-agrees-with-dpll (config seed)
  "Random 3-SAT over 50 variables at ratio 4.2, added in five batches; after each
batch four calls under random assumptions, each against sat-backend-dpll on the
clauses so far. Returns (values agreements calls unsat)."
  (let* ((rng (make-rng seed))
         (all (random-3sat rng 50 210))
         (vars (loop for i from 1 to 50 collect i))
         (agree 0) (calls 0) (unsat 0))
    (with-sat-session (s :backend (configured config))
      (session-add-variables s 50)
      (loop for batch from 0 below 5
            for clauses = (subseq all 0 (* 42 (1+ batch)))
            do (session-add-clauses s (subseq all (* 42 batch) (* 42 (1+ batch))))
               (dotimes (j 4)
                 (let ((assumptions (random-literals* rng vars (rng-int rng 4))))
                   (multiple-value-bind (model sat) (session-solve s :assumptions assumptions)
                     (incf calls)
                     (unless sat (incf unsat))
                     (when (and (eq sat (nth-value 1 (backend-solve (make-instance 'dpll-backend)
                                                                    (clauses->cnf clauses 50)
                                                                    :assumptions assumptions)))
                                (or (not sat) (model-satisfies-p model clauses assumptions)))
                       (incf agree)))))))
    (values agree calls unsat)))

(deftest-parametrize session-configurations-agree-with-dpll
    ((config)
     :ids ("default" "glucose" "no-restarts" "luby-1" "basic-min" "no-min"
           "no-phase-saving" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("luby-1") ("basic-min") ("no-min")
     ("no-phase-saving") ("small-reduce") ("stress"))
  (let ((total 0) (agreed 0) (unsat 0))
    (dolist (seed '(8101 8102 8103))
      (multiple-value-bind (a c u) (session-agrees-with-dpll config seed)
        (incf agreed a) (incf total c) (incf unsat u)))
    (ok (= agreed total) (format nil "~D of ~D calls agree with DPLL" agreed total))
    (ok (< 0 unsat total) "both outcomes")))

(deftest session-growth
  ;; About 1250 variables arriving a few at a time (the state grows many
  ;; times), each tied to the 8 before by a binary clause of a planted
  ;; assignment, and a call every 25 steps under planted assumptions.
  (let ((rng (make-rng 1200)) (planted (make-hash-table)) (vars '()) (clauses '())
        (bad 0) (calls 0))
    (with-sat-session (s :backend (cdcl))
      (dotimes (step 500)
        (let ((new (session-add-variables s (+ 1 (rng-int rng 4)))))
          (dolist (v new)
            (setf (gethash v planted) (zerop (rng-int rng 2))))
          (when (> (length vars) 8)
            (let ((window (last vars 8)))
              (dolist (v new)
                (let ((c (planted-binary rng planted (nth (rng-int rng 8) window) v)))
                  (session-add-clauses s (list c))
                  (push c clauses)))))
          (setf vars (append vars new)))
        (when (zerop (mod step 25))
          (let ((assumptions (loop for v in (last vars 3)
                                   collect (if (gethash v planted) v (- v)))))
            (multiple-value-bind (model sat) (session-solve s :assumptions assumptions)
              (incf calls)
              (unless (and sat (model-satisfies-p model clauses assumptions))
                (incf bad))))))
      (ok (> (session-variable-count s) 1000))
      (ok (zerop bad) (format nil "~D planted calls answered with models" calls)))))
