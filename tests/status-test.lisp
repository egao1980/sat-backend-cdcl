(in-package #:sat-backend-cdcl/tests)

;;; Answers in every configuration: random 3-SAT at the threshold against
;;; sat-backend-dpll (50 and 75 variables), pigeonhole, planted instances,
;;; hidden cores, and MINIMIZE with each strategy on mid-sized chains.

(defvar *dpll-status* (make-hash-table :test 'equal)
  "sat-backend-dpll's status per (seed count nvars nclauses index), computed once.")

(defun dpll-status (key clauses nvars)
  (multiple-value-bind (status found) (gethash key *dpll-status*)
    (if found
        status
        (setf (gethash key *dpll-status*)
              (nth-value 1 (backend-solve *dpll* (clauses->cnf clauses nvars)))))))

(defparameter *threshold-batches*
  '((1601 16 50 213) (1602 6 75 320))
  "(seed count nvars nclauses): random 3-SAT at ratio ~4.26.")

(deftest-parametrize status-random-3sat-against-dpll
    ((config)
     :ids ("default" "glucose" "no-restarts" "luby-1" "basic-min" "no-min"
           "no-phase-saving" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("luby-1") ("basic-min") ("no-min")
     ("no-phase-saving") ("small-reduce") ("stress"))
  (let ((sat-count 0) (unsat-count 0))
    (loop for (seed count nvars nclauses) in *threshold-batches*
          do (loop for clauses in (random-3sat-batch seed count nvars nclauses)
                   for i from 0
                   do (let ((expected (dpll-status (list seed count nvars nclauses i) clauses nvars)))
                        (multiple-value-bind (literals sat) (solve-clauses (configured config) clauses nvars)
                          (ok (eq expected sat) (format nil "~D vars, instance ~D: status" nvars i))
                          (if sat
                              (progn (incf sat-count)
                                     (ok (answer-ok-p clauses literals)
                                         (format nil "~D vars, instance ~D: answer" nvars i)))
                              (incf unsat-count))))))
    (ok (and (plusp sat-count) (plusp unsat-count)) "both outcomes exercised")))

(deftest-parametrize status-pigeonhole
    ((config)
     :ids ("default" "glucose" "no-restarts" "luby-1" "basic-min" "no-min"
           "no-phase-saving" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("luby-1") ("basic-min") ("no-min")
     ("no-phase-saving") ("small-reduce") ("stress"))
  (loop for holes from 2 to 6
        do (multiple-value-bind (clauses n) (pigeonhole (1+ holes) holes)
             (ok (null (nth-value 1 (solve-clauses (configured config) clauses n)))
                 (format nil "PHP(~D,~D) UNSAT" (1+ holes) holes)))
           (multiple-value-bind (clauses n) (pigeonhole holes holes)
             (multiple-value-bind (literals sat) (solve-clauses (configured config) clauses n)
               (ok (and sat (answer-ok-p clauses literals)) (format nil "PHP(~D,~D) SAT" holes holes))))))

(deftest-parametrize status-planted-and-hidden-core
    ((config)
     :ids ("default" "glucose" "no-restarts" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("small-reduce") ("stress"))
  (let ((rng (make-rng 1603)))
    (dotimes (i 4)
      (let ((clauses (planted-3sat rng 120 500)))
        (multiple-value-bind (literals sat) (solve-clauses (configured config) clauses 120)
          (ok (and sat (answer-ok-p clauses literals)) (format nil "planted ~D" i)))))
    (dotimes (i 2)
      (multiple-value-bind (clauses n) (hidden-core-instance rng :noise-vars 60 :noise-clauses 252
                                                                 :pigeons 5 :holes 4)
        (ok (null (nth-value 1 (solve-clauses (configured config) clauses n)))
            (format nil "hidden core ~D" i))))))

(deftest-parametrize status-under-assumptions-against-dpll
    ((config)
     :ids ("default" "stress")
     ("default") ("stress"))
  (let ((rng (make-rng 1604)) (sat-count 0) (unsat-count 0))
    (dotimes (i 16)
      (let* ((clauses (random-3sat rng 50 (+ 170 (rng-int rng 40))))
             (cnf (clauses->cnf clauses 50))
             (assumptions (loop repeat 8 collect (let ((v (1+ (rng-int rng 50))))
                                                   (if (zerop (rng-int rng 2)) v (- v)))))
             (expected (nth-value 1 (backend-solve *dpll* cnf :assumptions assumptions))))
        (multiple-value-bind (literals sat)
            (backend-solve (configured config) cnf :assumptions assumptions)
          (ok (eq expected sat) (format nil "instance ~D: status" i))
          (if sat
              (progn (incf sat-count)
                     (ok (subsetp assumptions literals))
                     (ok (answer-ok-p clauses literals)))
              (incf unsat-count)))))
    (ok (and (plusp sat-count) (plusp unsat-count)) "both outcomes exercised")))

(deftest-parametrize minimize-chains-every-strategy
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; Larger than sat-protocol's conformance chains, with the default and the
  ;; stress parameters.
  (dolist (ci (chain-family 1605 4 :positions 6 :min-options 2 :max-options 5 :cost-percent 85))
    (multiple-value-bind (cnf objective) (chain-instance-cnf ci)
      (dolist (backend (list (cdcl) (apply #'cdcl *stress-parameters*)))
        (multiple-value-bind (model cost optimal-p)
            (minimize cnf objective :backend backend :strategy strategy)
          (ok (eql (chain-instance-optimum ci) cost) (format nil "~A: the DP optimum" strategy))
          (ok (eq t optimal-p))
          (let ((labelling (chain-instance-labelling ci model)))
            (ok (and (listp labelling) (eql cost (chain-instance-cost ci labelling)))
                "a valid labelling of that cost")))))))

(deftest chain-oracle-self-check
  ;; The DP oracle against enumeration; the encoding's optimum by brute force
  ;; over the CNF (tiny chains), so the oracle and the encoding agree.
  (let ((feasible 0) (infeasible 0) (rng (make-rng 1606)))
    (dotimes (i 40)
      (let ((ci (make-chain-instance rng :positions (+ 2 (rng-int rng 3)) :min-options 1
                                         :max-options 3 :nogood-percent 40)))
        (let ((dp (chain-instance-optimum ci)))
          (if dp (incf feasible) (incf infeasible))
          (ok (eql (chain-instance-brute ci) dp) (format nil "chain ~D: DP = enumeration" i))
          (when dp
            (ok (eql dp (chain-instance-cost ci (nth-value 1 (chain-instance-optimum ci))))
                "the DP labelling has the DP cost")))))
    (ok (and (plusp feasible) (plusp infeasible)) "both outcomes exercised"))
  (dolist (ci (chain-family 1607 6 :positions 3 :min-options 2 :max-options 2))
    (multiple-value-bind (cnf objective) (chain-instance-cnf ci)
      (let* ((n (cnf-variable-count cnf))
             (models (brute-models (cnf-clauses cnf) n))
             (costs (mapcar (lambda (m)
                              (loop for (w . lit) in objective
                                    when (= 1 (sbit m (cnf-variable-index cnf (literal-name lit))))
                                      sum w))
                            models)))
        (ok (<= n 20) "small enough to enumerate")
        (ok (notany (lambda (i) (cnf-aux-variable-p cnf i)) (loop for i from 1 to n collect i))
            "no auxiliary variables")
        (ok (eql (chain-instance-optimum ci) (reduce #'min costs))
            "the CNF's least cost is the DP optimum")))))
