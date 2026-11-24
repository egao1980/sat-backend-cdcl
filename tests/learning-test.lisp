(in-package #:sat-backend-cdcl/tests)

;;; Clause learning, backjumping, restarts and reduction, seen through
;;; LEARNT-HOOK and the statistics (search.lisp, steps 2-3 and the RESTARTS
;;; and REDUCTION sections). Every configuration of *CONFIGURATIONS*.

(defun implied-by-models-p (clause models)
  "Every model (a bit-vector over 1..n) satisfies CLAUSE."
  (every (lambda (m)
           (some (lambda (l) (if (plusp l) (= 1 (sbit m l)) (= 0 (sbit m (- l))))) clause))
         models))

(defun learnt-clause-sane-p (literals lbd nvars)
  (and (consp literals)
       (every (lambda (l) (and (integerp l) (/= 0 l) (<= (abs l) nvars))) literals)
       (= (length literals) (length (remove-duplicates literals)))
       (notany (lambda (l) (member (- l) literals)) literals)
       (integerp lbd)
       (<= 1 lbd (length literals))
       (or (rest literals) (= lbd 1))))

(deftest-parametrize learnt-clauses-are-implied
    ((config)
     :ids ("default" "glucose" "no-restarts" "luby-1" "basic-min" "no-min"
           "no-phase-saving" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("luby-1") ("basic-min") ("no-min")
     ("no-phase-saving") ("small-reduce") ("stress"))
  ;; Satisfiable 14-variable CNFs near the threshold, each searched with no
  ;; assumption and under five random sets of three, which often make it
  ;; UNSAT. A learnt clause must follow from the CNF alone (assumptions are
  ;; decisions), so every model of the CNF satisfies it.
  (let ((rng (make-rng 9001)) (learnt-total 0))
    (dotimes (i 30)
      (let* ((clauses (random-3sat rng 14 (+ 56 (rng-int rng 8))))
             (models (brute-models clauses 14)))
        (when models
          (dotimes (j 6)
            (let* ((assumptions (and (plusp j)
                                     (remove-duplicates
                                      (loop repeat 3 collect (let ((v (1+ (rng-int rng 14))))
                                                               (if (zerop (rng-int rng 2)) v (- v))))
                                      :key #'abs :from-end t)))
                   (learnt '())
                   (b (configured config :learnt-hook (lambda (literals lbd)
                                                        (push (list literals lbd) learnt)))))
              (solve-clauses b clauses 14 :assumptions assumptions)
              (incf learnt-total (length learnt))
              (ok (eql (length learnt) (stats b :learnt-clauses))
                  "one hook call per learnt clause")
              (dolist (entry learnt)
                (destructuring-bind (literals lbd) entry
                  (ok (learnt-clause-sane-p literals lbd 14)
                      (format nil "instance ~D/~D: ~S (LBD ~S) is a clause" i j literals lbd))
                  (ok (implied-by-models-p literals models)
                      (format nil "instance ~D/~D: ~S is implied by the CNF" i j literals)))))))))
    (ok (< 30 learnt-total) (format nil "enough learnt clauses checked (~D)" learnt-total))))

(deftest learnt-clauses-implied-under-order
  ;; The same check with an ORDER hook choosing the highest candidate.
  (let ((rng (make-rng 9002)) (learnt-total 0))
    (dotimes (i 16)
      (let* ((clauses (random-3sat rng 12 44))
             (models (brute-models clauses 12))
             (learnt '())
             (b (cdcl :learnt-hook (lambda (literals lbd) (push (list literals lbd) learnt)))))
        (multiple-value-bind (literals sat)
            (solve-clauses b clauses 12 :order (lambda (cands) (car (last cands)))
                                        :phase (lambda (v) (oddp v)))
          (ok (eq (and models t) sat))
          (when sat (ok (answer-ok-p clauses literals))))
        (incf learnt-total (length learnt))
        (dolist (entry learnt)
          (ok (implied-by-models-p (first entry) models)
              (format nil "instance ~D: ~S" i (first entry))))))
    (ok (plusp learnt-total))))

(defun check-statistics-invariants (label backend sat)
  "The relations search.lisp states between the counters of one call."
  (let* ((s (cdcl-backend-statistics backend))
         (conflicts (getf s :conflicts)) (learnt (getf s :learnt-clauses))
         (restarts (getf s :restarts)) (reductions (getf s :reductions))
         (base (cdcl-backend-reduce-base backend))
         (unit (cdcl-backend-luby-unit backend)))
    (ok (if sat
            (= learnt conflicts)
            (<= 0 (- conflicts learnt) 1))
        (format nil "~A: learnt clauses vs conflicts ~S" label s))
    (ok (<= (getf s :backjumps) learnt) (format nil "~A: backjumps <= learnt" label))
    (ok (<= (getf s :deleted-clauses) learnt) (format nil "~A: deleted <= learnt" label))
    (ok (eql reductions (if base (reductions-due base (cdcl-backend-reduce-increment backend) learnt) 0))
        (format nil "~A: reductions follow the schedule ~S" label s))
    (when (zerop reductions)
      (ok (zerop (getf s :deleted-clauses)) (format nil "~A: no reduction, no deletion" label)))
    (ok (ecase (cdcl-backend-restart-policy backend)
          ((nil) (zerop restarts))
          (:luby (and (<= (luby-sum unit restarts) learnt)
                      (< learnt (luby-sum unit (1+ restarts)))))
          (:glucose (<= restarts (floor learnt (cdcl-backend-restart-window backend)))))
        (format nil "~A: restarts follow ~S ~S" label (cdcl-backend-restart-policy backend) s))))

(deftest-parametrize statistics-invariants
    ((config)
     :ids ("default" "glucose" "no-restarts" "luby-1" "basic-min" "no-min"
           "no-phase-saving" "small-reduce" "stress")
     ("default") ("glucose") ("no-restarts") ("luby-1") ("basic-min") ("no-min")
     ("no-phase-saving") ("small-reduce") ("stress"))
  (let ((n 0))
    (dolist (clauses (random-3sat-batch 4242 10 40 172))
      (let ((b (configured config)))
        (check-statistics-invariants (format nil "~A 3-SAT ~D" config (incf n)) b
                                     (nth-value 1 (solve-clauses b clauses 40)))))
    (dolist (holes '(4 5 6))
      (let ((b (configured config)))
        (multiple-value-bind (clauses vars) (pigeonhole (1+ holes) holes)
          (ok (null (nth-value 1 (solve-clauses b clauses vars))))
          (check-statistics-invariants (format nil "~A PHP ~D" config holes) b nil))))))

(deftest non-chronological-backjumps
  (let ((backjumps 0) (learnt 0))
    (dolist (clauses (random-3sat-batch 515 8 50 230))
      (let ((b (cdcl :restart-policy nil)))
        (solve-clauses b clauses 50)
        (incf backjumps (stats b :backjumps))
        (incf learnt (stats b :learnt-clauses))))
    (ok (plusp learnt))
    (ok (plusp backjumps) "some conflict jumped over at least one level")))

(deftest luby-restarts
  (multiple-value-bind (clauses n) (pigeonhole 7 6)
    (let ((b (cdcl :luby-unit 1)))
      (solve-clauses b clauses n)
      (ok (< 5 (stats b :restarts)) "unit 1 restarts often")
      (check-statistics-invariants "luby unit 1" b nil))
    (let ((b (cdcl :luby-unit 100000)))
      (solve-clauses b clauses n)
      (ok (zerop (stats b :restarts)) "a unit beyond the learnt clauses never restarts"))))

(deftest glucose-restarts
  (let ((restarts 0))
    (multiple-value-bind (clauses n) (pigeonhole 7 6)
      (let ((b (cdcl :restart-policy :glucose :restart-window 8)))
        (ok (null (nth-value 1 (solve-clauses b clauses n))))
        (incf restarts (stats b :restarts))
        (check-statistics-invariants "glucose PHP 7" b nil)))
    (dolist (clauses (random-3sat-batch 516 6 60 260))
      (let ((b (cdcl :restart-policy :glucose :restart-window 8)))
        (check-statistics-invariants "glucose 3-SAT" b (nth-value 1 (solve-clauses b clauses 60)))
        (incf restarts (stats b :restarts))))
    (ok (plusp restarts) "the LBD test fires")))

(deftest reduction-deletes-clauses
  (multiple-value-bind (clauses n) (pigeonhole 7 6)
    (let ((b (cdcl :reduce-base 20 :reduce-increment 5)))
      (ok (null (nth-value 1 (solve-clauses b clauses n))) "still UNSAT")
      (ok (<= 2 (stats b :reductions)))
      (ok (plusp (stats b :deleted-clauses)))
      (check-statistics-invariants "small reduce" b nil))
    (let ((b (cdcl :reduce-base nil)))
      (ok (null (nth-value 1 (solve-clauses b clauses n))))
      (ok (equal '(0 0) (list (stats b :reductions) (stats b :deleted-clauses)))
          "REDUCE-BASE NIL never reduces"))))

(deftest-parametrize minimization-keeps-answers
    ((mode)
     :ids ("recursive" "basic" "none")
     (:recursive) (:basic) (nil))
  (let ((literals 0))
    (dolist (clauses (random-3sat-batch 517 8 40 172))
      (let ((b (cdcl :clause-minimization mode
                     :learnt-hook (lambda (c lbd) (declare (ignore lbd)) (incf literals (length c))))))
        (multiple-value-bind (answer sat) (solve-clauses b clauses 40)
          (ok (eq (nth-value 1 (solve-clauses (make-instance 'dpll-backend) clauses 40)) sat))
          (when sat (ok (answer-ok-p clauses answer))))))
    (ok (plusp literals))))
