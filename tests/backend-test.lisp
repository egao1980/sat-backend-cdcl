(in-package #:sat-backend-cdcl/tests)

;;; The class, the parameters, the decision rules of search.lisp (index order
;;; at the start, default phase, phase saving), the ORDER / PHASE hooks, the
;;; budget and its restarts, determinism and per-call state.

;;; ------------------------------------------------------------ class (GIVEN)

(deftest default-backend-install
  (let ((*sat-backend* nil))
    (sat-backend-cdcl::%install-default-backend)
    (ok (typep *sat-backend* 'cdcl-backend) "installed when none is set"))
  (let* ((other (make-instance 'dpll-backend))
         (*sat-backend* other))
    (sat-backend-cdcl::%install-default-backend)
    (ok (eq other *sat-backend*) "an existing default is kept")))

(deftest backend-defaults
  (let ((b (cdcl)))
    (ok (typep b 'sat-backend))
    (ok (equal '(:luby 100 50 0.8 0.95 0.999 t nil :recursive 2000 300 :decisions nil)
               (list (cdcl-backend-restart-policy b) (cdcl-backend-luby-unit b)
                     (cdcl-backend-restart-window b) (cdcl-backend-restart-margin b)
                     (cdcl-backend-variable-decay b) (cdcl-backend-clause-decay b)
                     (cdcl-backend-phase-saving b) (cdcl-backend-default-phase b)
                     (cdcl-backend-clause-minimization b) (cdcl-backend-reduce-base b)
                     (cdcl-backend-reduce-increment b) (cdcl-backend-budget-unit b)
                     (cdcl-backend-learnt-hook b))))
    (ok (null (cdcl-backend-statistics b)) "no statistics before the first call")))

(deftest-parametrize backend-parameter-errors
    ((initarg value)
     :ids ("restart-policy" "luby-unit" "restart-window" "restart-margin" "variable-decay-1"
           "variable-decay-0" "clause-decay" "clause-minimization" "reduce-base"
           "reduce-increment" "budget-unit" "learnt-hook")
     (:restart-policy :never) (:luby-unit 0) (:restart-window 0) (:restart-margin 0)
     (:variable-decay 1) (:variable-decay 0) (:clause-decay 1.5)
     (:clause-minimization :deep) (:reduce-base 0) (:reduce-increment -1)
     (:budget-unit :seconds) (:learnt-hook 'print))
  (ok (signals (make-instance 'cdcl-backend initarg value) 'type-error)))

(deftest backend-parameter-store-value
  (let ((b (handler-bind ((type-error (lambda (c) (store-value :glucose c))))
             (make-instance 'cdcl-backend :restart-policy :never))))
    (ok (eq :glucose (cdcl-backend-restart-policy b)) "CHECK-TYPE's STORE-VALUE")))

;;; ---------------------------------------------------------- answers, counts

(deftest statistics-shape
  (let ((b (cdcl)))
    (multiple-value-bind (clauses n) (pigeonhole 4 3)
      (solve-clauses b clauses n))
    (let ((s (cdcl-backend-statistics b)))
      (ok (= (length s) (* 2 (length +statistics-keys+))) "exactly the eight keys")
      (ok (every (lambda (k) (typep (getf s k) '(integer 0 *))) +statistics-keys+)
          "each a non-negative integer")
      (ok (plusp (getf s :conflicts)))
      (ok (plusp (getf s :decisions))))))

(deftest propagation-chain
  (let ((b (cdcl)))
    (multiple-value-bind (model sat)
        (solve (f '(:and "a" (:implies "a" "b") (:implies "b" "c") (:implies "c" "d")))
               :backend b :complete nil)
      (ok sat)
      (ok (equal '(("a" . t) ("b" . t) ("c" . t) ("d" . t)) model))
      (ok (equal '(0 4 0 0) (list (stats b :decisions) (stats b :propagations)
                                  (stats b :conflicts) (stats b :learnt-clauses)))
          "no decision: the unit clause and three implications"))))

(deftest first-decisions-in-index-order
  ;; Activities start at 0: the lowest index first, DEFAULT-PHASE first.
  (let ((b (cdcl)))
    (ok (equal '((-1 -2 3) t) (multiple-value-list (solve-clauses b '((1 2 3)) 3)))
        "1 = F, 2 = F, then 3 is propagated")
    (ok (equal '(2 1) (list (stats b :decisions) (stats b :propagations)))))
  (let ((b (cdcl :default-phase t)))
    (ok (equal '((1) t) (multiple-value-list (solve-clauses b '((1 2 3)) 3)))
        "1 = T satisfies the clause: the search stops")
    (ok (eql 1 (stats b :decisions)))))

(deftest stops-when-every-clause-is-true
  ;; 4b runs before every decision. Without ORDER a decision need not be a
  ;; candidate: after 1 = T, 2 (activity 0, lowest index) is decided although
  ;; (1 2) is true; 3 = T then satisfies the last clause, so 4 stays free, and
  ;; 5 and 6 (in no clause) are never decided.
  (let ((b (cdcl :default-phase t)))
    (ok (equal '((1 2 3) t) (multiple-value-list (solve-clauses b '((1 2) (3 4) (1 4)) 6))))
    (ok (eql 3 (stats b :decisions)))))

(defparameter *phase-saving-clauses* '((1 2) (-2 5) (1 -2 -5) (2 3 4))
  "Deciding 1 = F propagates 2 and 5 into a conflict. The learnt unit (1) is
asserted at level 0, having bumped 1, 2 and 5; 2 is then decided first (the
tie with 5 goes to the lower index), true from its saved phase.")

(deftest phase-saving-decides-the-saved-value
  (let* ((learnt '())
         (b (cdcl :learnt-hook (lambda (literals lbd) (push (list literals lbd) learnt)))))
    (ok (equal '((1 2 5) t) (multiple-value-list (solve-clauses b *phase-saving-clauses* 5))))
    (ok (equal '(((1) 1)) learnt) "one learnt clause: the unit (1), LBD 1")
    (ok (equal '(2 4 1 1 0) (list (stats b :decisions) (stats b :propagations)
                                  (stats b :conflicts) (stats b :learnt-clauses)
                                  (stats b :backjumps))))))

(deftest phase-saving-off-decides-the-default
  ;; 2 = F, then 5 (activity 1, though its clauses are true) and 3 (lowest of
  ;; the rest) are decided false, and 4 is propagated.
  (let ((b (cdcl :phase-saving nil)))
    (ok (equal '((1 -2 -5 -3 4) t) (multiple-value-list (solve-clauses b *phase-saving-clauses* 5))))
    (ok (equal '(4 4) (list (stats b :decisions) (stats b :propagations))))))

(deftest-parametrize edge-cases
    ((clauses nvars assumptions expected)
     :ids ("empty-cnf" "empty-clause" "units-clash" "tautology" "duplicates"
           "assumptions-clash" "assumption-free-variable")
     ('() 3 '() '(nil t))
     ('(nil (1 2)) 2 '() '(nil nil))
     ('((1) (-1)) 1 '() '(nil nil))
     ('((1 -1)) 1 '() :sat)
     ('((1 1 2) (-1 -1)) 2 '() '((-1 2) t))
     ('((1 2)) 2 '(1 -1) '(nil nil))
     ('((1 2)) 3 '(3) :sat))
  (let ((b (cdcl)))
    (multiple-value-bind (literals sat) (solve-clauses b clauses nvars :assumptions assumptions)
      (if (eq expected :sat)
          (progn
            (ok sat)
            (ok (answer-ok-p clauses literals))
            (ok (subsetp assumptions literals) "the answer assigns the assumptions"))
          (ok (equal expected (list literals sat)))))))

(deftest cnf-not-modified
  (multiple-value-bind (clauses n) (pigeonhole 4 3)
    (let* ((cnf (clauses->cnf clauses n))
           (before (copy-tree (cnf-clauses cnf))))
      (backend-solve (cdcl) cnf :assumptions '(1 -5))
      (backend-final-conflict (cdcl) cnf '(1 5))
      (ok (equal before (cnf-clauses cnf)))
      (ok (= n (cnf-variable-count cnf))))))

;;; --------------------------------------------------------- determinism, state

(defun run-record (backend clauses nvars &rest keys)
  "Answer, statistics and learnt clauses of one call."
  (let* ((learnt '())
         (hooked (apply #'make-instance 'cdcl-backend
                        :learnt-hook (lambda (literals lbd) (push (cons lbd literals) learnt))
                        (loop for (k v) on (backend-parameters backend) by #'cddr
                              unless (eq k :learnt-hook) nconc (list k v)))))
    (let ((answer (multiple-value-list (apply #'solve-clauses hooked clauses nvars keys))))
      (list answer (cdcl-backend-statistics hooked) (reverse learnt)))))

(defun backend-parameters (backend)
  (list :restart-policy (cdcl-backend-restart-policy backend)
        :luby-unit (cdcl-backend-luby-unit backend)
        :restart-window (cdcl-backend-restart-window backend)
        :restart-margin (cdcl-backend-restart-margin backend)
        :variable-decay (cdcl-backend-variable-decay backend)
        :clause-decay (cdcl-backend-clause-decay backend)
        :phase-saving (cdcl-backend-phase-saving backend)
        :default-phase (cdcl-backend-default-phase backend)
        :clause-minimization (cdcl-backend-clause-minimization backend)
        :reduce-base (cdcl-backend-reduce-base backend)
        :reduce-increment (cdcl-backend-reduce-increment backend)
        :budget-unit (cdcl-backend-budget-unit backend)))

(deftest-parametrize deterministic-calls
    ((config)
     :ids ("default" "glucose" "luby-1" "small-reduce" "stress")
     ("default") ("glucose") ("luby-1") ("small-reduce") ("stress"))
  (let ((instances (random-3sat-batch 61 4 40 170)))
    (dolist (clauses instances)
      (let ((first (run-record (configured config) clauses 40))
            (again (run-record (configured config) clauses 40)))
        (ok (equal first again) "same answer, statistics and learnt clauses")))))

(deftest no-state-between-calls
  (let ((b (cdcl))
        (a (first (random-3sat-batch 62 1 40 170))))
    (multiple-value-bind (php n) (pigeonhole 5 4)
      (let ((first (list (multiple-value-list (solve-clauses b a 40))
                         (copy-list (cdcl-backend-statistics b)))))
        (solve-clauses b php n)
        (ok (equal first (list (multiple-value-list (solve-clauses b a 40))
                               (copy-list (cdcl-backend-statistics b))))
            "a call in between changes nothing")))))

;;; ----------------------------------------------------------- ORDER and PHASE

(defun conflict-free-oracle (clauses nvars assumptions choose value)
  "The protocol loop when no conflict can occur (every decision agrees with a
model of CLAUSES and ASSUMPTIONS): propagate to the fixpoint (unique without
a conflict), stop when every clause has a true literal, else decide
(funcall CHOOSE candidates) with (funcall VALUE var). Returns (values
candidate-lists literals), the literals sorted by variable."
  (let ((a (make-array (1+ nvars) :initial-element 0)) (lists '()))
    (labels ((val (l) (if (plusp l) (aref a l) (- (aref a (- l)))))
             (set-lit (l) (setf (aref a (abs l)) (if (plusp l) 1 -1)))
             (propagate ()
               (loop for changed = nil
                     do (dolist (c clauses)
                          (unless (some (lambda (l) (= 1 (val l))) c)
                            (let ((free (remove-if-not (lambda (l) (zerop (val l))) c)))
                              (assert free () "conflict in a conflict-free run")
                              (unless (rest free) (set-lit (first free)) (setf changed t)))))
                     while changed))
             (candidates ()
               (sort (remove-duplicates
                      (loop for c in clauses
                            unless (some (lambda (l) (= 1 (val l))) c)
                              nconc (loop for l in c when (zerop (val l)) collect (abs l))))
                     #'<)))
      (mapc #'set-lit assumptions)
      (propagate)
      (loop for cands = (candidates)
            while cands
            do (push cands lists)
               (let ((v (funcall choose cands)))
                 (set-lit (if (funcall value v) v (- v)))
                 (propagate)))
      (values (nreverse lists)
              (loop for v from 1 to nvars
                    unless (zerop (aref a v)) collect (* v (aref a v)))))))

(defun spread-choice (candidates)
  "A deterministic ORDER choice that is neither the first nor the last."
  (nth (mod (+ (first candidates) (* 3 (length candidates))) (length candidates)) candidates))

(deftest-parametrize order-and-phase-exact-when-conflict-free
    ((config)
     :ids ("default" "stress")
     ("default") ("stress"))
  ;; PHASE follows a planted model, so no conflict can occur and the
  ;; candidate lists are fixed by the rules: they must equal the oracle's.
  (let ((rng (make-rng 5150)))
    (dotimes (i 10)
      (multiple-value-bind (clauses planted) (planted-3sat rng 30 120)
        (let* ((assumptions (loop for v in '(7 14 21)
                                  collect (if (funcall planted v) v (- v))))
               (seen '()) (phased '()) (chosen '())
               (b (configured config)))
          (multiple-value-bind (expected-lists expected-literals)
              (conflict-free-oracle clauses 30 assumptions #'spread-choice planted)
            (multiple-value-bind (literals sat)
                (solve-clauses b clauses 30
                               :assumptions assumptions
                               :order (lambda (cands)
                                        (push cands seen)
                                        (let ((v (spread-choice cands))) (push v chosen) v))
                               :phase (lambda (v) (push v phased) (funcall planted v)))
              (ok sat (format nil "instance ~D: SAT" i))
              (ok (equal expected-lists (reverse seen))
                  (format nil "instance ~D: the candidate lists" i))
              (ok (equal chosen phased) "PHASE is called once per decision, on ORDER's choice")
              (ok (equal expected-literals (sort (copy-list literals) #'< :key #'abs))
                  (format nil "instance ~D: the assigned literals" i))
              (ok (equal (list (length seen) 0) (list (stats b :decisions) (stats b :conflicts)))
                  "one ORDER call per decision, no conflict"))))))))

(deftest order-hook-with-conflicts
  ;; Near the threshold: conflicts, learning and backjumps under ORDER.
  (let ((sat-count 0) (unsat-count 0))
    (dolist (clauses (random-3sat-batch 71 16 14 60))
      (let* ((lists '()) (phased '()) (chosen '())
             (b (cdcl :luby-unit 2)))
        (multiple-value-bind (literals sat)
            (solve-clauses b clauses 14
                           :order (lambda (cands)
                                    (push cands lists)
                                    (let ((v (car (last cands)))) (push v chosen) v))
                           :phase (lambda (v) (push v phased) (evenp v)))
          (ok (eq (brute-satisfiable-p clauses 14) sat) "status")
          (if sat (incf sat-count) (incf unsat-count))
          (when sat (ok (answer-ok-p clauses literals) "answer"))
          (ok (every (lambda (cands)
                       (and cands (every #'< cands (rest cands)) (<= 1 (first cands))
                            (<= (car (last cands)) 14)))
                     lists)
              "candidates: non-empty, ascending, variables of the CNF")
          (ok (eql (length lists) (stats b :decisions)) "one ORDER call per decision")
          (ok (equal chosen phased) "PHASE right after ORDER, on its choice"))))
    (ok (and (plusp sat-count) (plusp unsat-count)) "both outcomes exercised")))

(deftest order-invalid-choice
  (ok (signals (solve-clauses (cdcl) '((1 2) (3 4)) 5 :order (constantly 99)) 'sat-error)
      "not a variable")
  (ok (signals (solve-clauses (cdcl) '((1 2) (3 4)) 5 :order (constantly 5)) 'sat-error)
      "a variable of no clause is not a candidate"))

;;; ---------------------------------------------------------------- budget

(defun php (pigeons holes)
  (multiple-value-bind (clauses n) (pigeonhole pigeons holes)
    (clauses->cnf clauses n)))

(deftest budget-signals-before-the-decision
  (let* ((b (cdcl)) (at-signal nil)
         (result (handler-case
                     (handler-bind ((sat-budget-exceeded
                                      (lambda (c)
                                        (declare (ignore c))
                                        (setf at-signal (copy-list (cdcl-backend-statistics b))))))
                       (backend-solve b (php 5 4) :budget 3))
                   (sat-budget-exceeded (c) (sat-budget-exceeded-budget c)))))
    (ok (eql 3 result) "the condition carries the budget")
    (ok (eql 3 (getf at-signal :decisions)) "statistics are current at the signal")
    (ok (eql 3 (stats b :decisions)) "and after the call ends")))

(deftest budget-stepping-counts-every-decision
  ;; MINIMIZE's meter: :BUDGET 0, STORE-VALUE budget+1 at every signal.
  (let* ((cnf (php 6 5))
         (plain (cdcl)) (metered (cdcl))
         (signals 0) (mismatches 0)
         (unbudgeted (multiple-value-list (backend-solve plain cnf)))
         (stepped (multiple-value-list
                   (handler-bind ((sat-budget-exceeded
                                    (lambda (c)
                                      (incf signals)
                                      (unless (eql (sat-budget-exceeded-budget c)
                                                   (getf (cdcl-backend-statistics metered) :decisions))
                                        (incf mismatches))
                                      (store-value (1+ (sat-budget-exceeded-budget c)) c))))
                     (backend-solve metered cnf :budget 0)))))
    (ok (equal unbudgeted stepped) "same answer")
    (ok (equal (cdcl-backend-statistics plain) (cdcl-backend-statistics metered))
        "the search resumed in place: same statistics")
    (ok (eql signals (stats metered :decisions)) "one signal per decision")
    (ok (zerop mismatches) "each signal at decisions = budget")))

(deftest budget-continue-resumes
  (let* ((cnf (php 6 5)) (plain (cdcl)) (continued (cdcl)) (signals 0))
    (let ((a (multiple-value-list (backend-solve plain cnf)))
          (b (multiple-value-list
              (handler-bind ((sat-budget-exceeded (lambda (c) (incf signals) (continue c))))
                (backend-solve continued cnf :budget 1)))))
      (ok (equal a b))
      (ok (equal (cdcl-backend-statistics plain) (cdcl-backend-statistics continued)))
      (ok (< 1 signals) "CONTINUE doubled the budget several times"))))

(deftest budget-use-value
  (let ((b (cdcl)))
    (ok (equal '(:stopped nil)
               (handler-bind ((sat-budget-exceeded (lambda (c) (use-value :stopped c))))
                 (multiple-value-list (solve (php 5 4) :backend b :budget 3)))))
    (ok (eql 3 (stats b :decisions)) "statistics published on the throw")))

(defun signal-free-p (thunk)
  "(values results signalled): THUNK's values, and whether it signalled
SAT-BUDGET-EXCEEDED (the handler records it and declines)."
  (let ((signalled nil))
    (values (handler-bind ((sat-budget-exceeded
                             (lambda (c) (declare (ignore c)) (setf signalled t))))
              (multiple-value-list (funcall thunk)))
            signalled)))

(deftest budget-nil-and-large
  (dolist (budget '(nil 1000000))
    (multiple-value-bind (results signalled)
        (signal-free-p (lambda () (backend-solve (cdcl) (php 5 4) :budget budget)))
      (ok (equal '(nil nil) results) (format nil "budget ~S: UNSAT" budget))
      (ok (not signalled) (format nil "budget ~S: no signal" budget)))))

(deftest budget-unit-conflicts
  (let* ((cnf (php 6 5))
         (plain (cdcl :budget-unit :conflicts))
         (metered (cdcl :budget-unit :conflicts))
         (signals 0) (mismatches 0)
         (unbudgeted (multiple-value-list (backend-solve plain cnf)))
         (stepped (multiple-value-list
                   (handler-bind ((sat-budget-exceeded
                                    (lambda (c)
                                      (incf signals)
                                      (unless (eql (sat-budget-exceeded-budget c)
                                                   (getf (cdcl-backend-statistics metered)
                                                         :learnt-clauses))
                                        (incf mismatches))
                                      (store-value (1+ (sat-budget-exceeded-budget c)) c))))
                     (backend-solve metered cnf :budget 0)))))
    (ok (equal unbudgeted stepped))
    (ok (equal (cdcl-backend-statistics plain) (cdcl-backend-statistics metered)))
    (ok (eql signals (stats metered :learnt-clauses)) "one signal per analysed conflict")
    (ok (zerop mismatches) "each signal at learnt clauses = budget"))
  (multiple-value-bind (results signalled)
      (signal-free-p (lambda ()
                       (solve-clauses (cdcl :budget-unit :conflicts) '((1 2 3)) 3 :budget 0)))
    (ok (equal '((-1 -2 3) t) results))
    (ok (not signalled) "decisions are not budgeted, and a conflict-free search never signals"))
  (ok (eql 2 (handler-case (backend-solve (cdcl :budget-unit :conflicts) (php 5 4) :budget 2)
               (sat-budget-exceeded (c) (sat-budget-exceeded-budget c))))))

(deftest budget-final-conflict
  (let* ((cnf (multiple-value-bind (clauses n) (pigeonhole 6 5)
                (clauses->cnf clauses (+ n 2))))   ; 31 and 32 occur in no clause
         (signals 0)
         (assumptions '(31 1 -32)))
    (ok (signals (backend-final-conflict (cdcl) cnf assumptions :budget 2) 'sat-budget-exceeded))
    (ok (equal (multiple-value-list (backend-final-conflict (cdcl) cnf assumptions))
               (handler-bind ((sat-budget-exceeded (lambda (c) (incf signals) (continue c))))
                 (multiple-value-list (backend-final-conflict (cdcl) cnf assumptions :budget 1))))
        "CONTINUE gives the unbudgeted core")
    (ok (plusp signals))))
