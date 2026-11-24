(in-package #:sat-backend-cdcl/tests)

;;; BACKEND-FINAL-CONFLICT specialised (search.lisp, FINAL CONFLICT):
;;; MiniSat's analyzeFinal over the assumptions. Exact cores on small cases,
;;; then properties against brute force and against sat-backend-dpll.

(defun subsequence-p (sub list)
  "SUB is LIST with some elements left out, order kept."
  (loop for x in list
        when (and sub (eql x (first sub))) do (pop sub))
  (null sub))

(defun final-conflict (clauses nvars assumptions &rest keys)
  (multiple-value-list
   (apply #'backend-final-conflict (cdcl) (clauses->cnf clauses nvars) assumptions keys)))

(deftest-parametrize final-conflict-exact
    ((clauses nvars assumptions expected)
     :ids ("implication-chain" "level-0-refutation" "searched-refutation" "false-at-level-0"
           "free-variable-clash" "duplicates" "sat")
     ;; 4 (no clause) at level 1, 1 at level 2 implies 2 and 3; -3 is false:
     ;; the walk from 3 reaches 1 only.
     ('((-1 2) (-2 3)) 4 '(4 1 -3) '((1 -3) t))
     ;; Refuted by propagation at level 0: no assumption is blamed.
     ('((1) (-1 2) (-2)) 4 '(3 4) '(nil t))
     ;; PHP(4,3) needs search, but its learnt clauses never mention the
     ;; free variables 13 and 14: the final conflict is at level 0.
     ((pigeonhole 4 3) 14 '(13 -14) '(nil t))
     ;; 1 is false at level 0: S = {1}.
     ('((-1) (2 3)) 3 '(2 1 3) '((1) t))
     ;; 3 occurs in no clause; 3 and -3 contradict each other.
     ('((1 2)) 5 '(3 1 -3) '((3 -3) t))
     ;; The repeated assumption gets an empty level; the core lists it once.
     ('((-1 2)) 3 '(1 1 -2) '((1 -2) t))
     ;; Satisfiable: no core, the answer as BACKEND-SOLVE's.
     ('((-1 2) (-2 3)) 4 '(4 1) '(nil nil (4 1 2 3))))
  (ok (equal expected (final-conflict clauses nvars assumptions))))

(deftest final-conflict-random-against-brute-force
  ;; 12 variables, 20..34 clauses, up to 6 assumptions: 4 on the CNF's variables,
  ;; 2 on free variables 13..15 (a v / -v pair among those forces UNSAT).
  ;; Parameters chosen so seed 3131 gives both outcomes (21 UNSAT / 19 SAT by
  ;; brute force); contract amendment 2026-11-24.
  (let ((rng (make-rng 3131)) (unsat-count 0) (sat-count 0) (core-size 0) (assumed 0))
    (dotimes (i 40)
      (let* ((clauses (random-3sat rng 12 (+ 20 (rng-int rng 15))))
             (assumptions (remove-duplicates
                           (append (loop repeat 4 collect (let ((v (1+ (rng-int rng 12))))
                                                            (if (zerop (rng-int rng 2)) v (- v))))
                                   (loop repeat 2 collect (let ((v (+ 13 (rng-int rng 3))))
                                                            (if (zerop (rng-int rng 2)) v (- v)))))
                           :from-end t)))
        (destructuring-bind (core status &optional literals)
            (final-conflict clauses 15 assumptions)
          (if (not (brute-satisfiable-p (append clauses (mapcar #'list assumptions)) 15))
              (progn
                (incf unsat-count)
                (incf core-size (length core))
                (incf assumed (length assumptions))
                (ok (eq t status) (format nil "instance ~D: UNSAT" i))
                (ok (subsequence-p core assumptions) "an ordered sublist of the assumptions")
                (ok (= (length core) (length (remove-duplicates core))) "no repeats")
                (ok (not (brute-satisfiable-p (append clauses (mapcar #'list core)) 15))
                    (format nil "instance ~D: CNF plus core ~S is UNSAT" i core))
                (ok (every (lambda (l)
                             (or (<= (abs l) 12) (member (- l) core)))
                           core)
                    "a free-variable assumption only with its negation"))
              (progn
                (incf sat-count)
                (ok (null core) (format nil "instance ~D: SAT" i))
                (ok (null status))
                (ok (subsetp assumptions literals) "the answer assigns the assumptions")
                (ok (answer-ok-p clauses literals)))))))
    (ok (and (plusp unsat-count) (plusp sat-count)) "both outcomes exercised")
    (ok (< core-size assumed) "cores are smaller than the assumption lists")))

(defparameter *dpll* (make-instance 'dpll-backend))

(deftest final-conflict-mid-scale-against-dpll
  ;; 50 variables, 170..199 clauses (ratio 3.4..4.0), 4 assumptions: status and
  ;; the core's unsatisfiability checked with sat-backend-dpll. Seed 3132 gives
  ;; both outcomes (7 UNSAT / 5 SAT by DPLL); contract amendment 2026-11-24.
  (let ((rng (make-rng 3132)) (unsat-count 0) (sat-count 0))
    (dotimes (i 12)
      (let* ((clauses (random-3sat rng 50 (+ 170 (rng-int rng 30))))
             (cnf (clauses->cnf clauses 50))
             (assumptions (remove-duplicates
                           (loop repeat 4 collect (let ((v (1+ (rng-int rng 50))))
                                                     (if (zerop (rng-int rng 2)) v (- v))))
                           :key #'abs :from-end t))
             (expected (nth-value 1 (backend-solve *dpll* cnf :assumptions assumptions))))
        (destructuring-bind (core status &optional literals)
            (multiple-value-list (backend-final-conflict (cdcl) cnf assumptions))
          (ok (eq (not expected) status) (format nil "instance ~D: status" i))
          (cond (status
                 (incf unsat-count)
                 (ok (subsequence-p core assumptions))
                 (ok (null (nth-value 1 (backend-solve *dpll* cnf :assumptions core)))
                     (format nil "instance ~D: CNF plus core is UNSAT (DPLL)" i)))
                (t
                 (incf sat-count)
                 (ok (subsetp assumptions literals))
                 (ok (answer-ok-p clauses literals)))))))
    (ok (and (plusp unsat-count) (plusp sat-count)) "both outcomes exercised")))

(deftest final-conflict-statistics
  (let ((b (cdcl)))
    (multiple-value-bind (clauses n) (pigeonhole 5 4)
      (backend-final-conflict b (clauses->cnf clauses n) '(1 -2)))
    (ok (every (lambda (k) (typep (getf (cdcl-backend-statistics b) k) '(integer 0 *)))
               +statistics-keys+)
        "published like BACKEND-SOLVE's")
    (ok (plusp (stats b :conflicts)))))

(deftest unsat-core-minimal-nil-is-the-final-conflict
  (let* ((a (sat-var "a")) (not-c (sat-not (sat-var "c"))) (d (sat-var "d")))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:and (:implies "a" "b") (:implies "b" "c")))
                    :assumptions (list d a not-c) :minimal nil :backend (cdcl))
      (ok (eq t unsat))
      (ok (and (= 2 (length core)) (eq a (first core)) (eq not-c (second core)))
          "exactly a and (not c), the given objects in order: d is not blamed"))))

(deftest core-guided-minimize-uses-final-conflicts
  ;; :CORE-GUIDED on the default methods, over this method: chains of the
  ;; family in instances.lisp, against the DP oracle.
  (dolist (ci (chain-family 41 6 :positions 5 :min-options 2 :max-options 4))
    (multiple-value-bind (cnf objective) (chain-instance-cnf ci)
      (multiple-value-bind (model cost optimal-p)
          (minimize cnf objective :backend (cdcl) :strategy :core-guided)
        (ok (eql (chain-instance-optimum ci) cost) "the DP optimum")
        (ok (eq t optimal-p))
        (let ((labelling (chain-instance-labelling ci model)))
          (ok (and (listp labelling) (eql cost (chain-instance-cost ci labelling)))
              "a valid labelling of that cost"))))))
