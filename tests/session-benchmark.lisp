(in-package #:sat-backend-cdcl/tests)

;;; Soft benchmark (reported, not gated): a chain of 50 segments, each adding
;;; clauses and then solving under assumptions, on one session against the
;;; fresh front-end SOLVE on all the clauses so far. Every answer is checked
;;; (the same status both ways, models of every clause and assumption); the
;;; time ratio is only reported, in the last assertion's description. Each
;;; path's time is the best of RUNS runs.
;;;
;;; Segment p is position p of a planted chain labelling: options x(p, l)
;;; (one-hot: an at-least-one clause and pairwise at-most-one clauses), pair
;;; no-goods with position p-1 and three-position no-goods with p-2 and p-1,
;;; none of them against the planted labelling, so the clauses stay
;;; satisfiable. After segment p, one query per distance d of DISTANCES with
;;; p >= d: the assumptions x(p, a) and x(p-d, b) for random options a, b, and
;;; -x(q, planted) for the positions q between them (at most BLOCK of them), so
;;; the search must find another path (feasible or not).

(defparameter *session-benchmark*
  '(:seed 5050 :segments 50 :min-options 8 :max-options 12
    :nogood-percent 65 :triple-percent 15 :distances (2 4 8 16 30 45) :block 25)
  "The chain of the session benchmark.")

(defun benchmark-segments (&key seed segments min-options max-options nogood-percent
                                triple-percent distances (block 0))
  "A list of (count clauses queries) per segment: COUNT new variables, then
CLAUSES and QUERIES (assumption lists) over the variables so far, which are
numbered in order from 1."
  (let ((rng (make-rng seed)) (first-index '()) (options '()) (planted '()) (next 1)
        (result '()))
    (dotimes (p segments (nreverse result))
      (let* ((k (+ min-options (rng-int rng (1+ (- max-options min-options)))))
             (base next)
             (label (rng-int rng k))
             (clauses '()))
        (setf next (+ next k))
        (push base first-index) (push k options) (push label planted)
        (flet ((x (q l) (+ (nth (- p q) first-index) l))
               (k-of (q) (nth (- p q) options))
               (label-of (q) (nth (- p q) planted)))
          (push (loop for l below k collect (x p l)) clauses)
          (dotimes (a k)
            (loop for b from (1+ a) below k do (push (list (- (x p a)) (- (x p b))) clauses)))
          (when (>= p 1)
            (dotimes (a (k-of (1- p)))
              (dotimes (b k)
                (when (and (< (rng-int rng 100) nogood-percent)
                           (not (and (= a (label-of (1- p))) (= b label))))
                  (push (list (- (x (1- p) a)) (- (x p b))) clauses)))))
          (when (>= p 2)
            (dotimes (a (k-of (- p 2)))
              (dotimes (b (k-of (1- p)))
                (dotimes (c k)
                  (when (and (< (rng-int rng 100) triple-percent)
                             (not (and (= a (label-of (- p 2))) (= b (label-of (1- p))) (= c label))))
                    (push (list (- (x (- p 2) a)) (- (x (1- p) b)) (- (x p c))) clauses))))))
          (push (list k (nreverse clauses)
                      (loop for d in distances
                            when (>= p d)
                              collect (list* (x p (rng-int rng k))
                                             (x (- p d) (rng-int rng (k-of (- p d))))
                                             (loop for q from (1- p) downto (max (1+ (- p d)) (- p block))
                                                   collect (- (x q (label-of q)))))))
                result))))))

(defun best-time (runs thunk)
  "The least of RUNS timings of THUNK, and the values of its last run."
  (let ((best nil) (values nil))
    (dotimes (i runs (values best values))
      (multiple-value-bind (seconds vals) (timed thunk)
        (setf values vals
              best (if best (min best seconds) seconds))))))

(defun run-session-benchmark (&key (spec *session-benchmark*) (backend-class 'cdcl-backend) (runs 3))
  "Both runs of SPEC. Returns (values session-seconds fresh-seconds statuses-agree
models-ok queries unsat)."
  (let* ((segments (apply #'benchmark-segments spec))
         (session-answers '()) (fresh-answers '())
         (session-seconds
           (nth-value 0 (best-time runs
                         (lambda ()
                           (setf session-answers '())
                           (with-sat-session (s :backend (make-instance backend-class))
                             (loop for (count clauses queries) in segments
                                   do (session-add-variables s count)
                                      (session-add-clauses s clauses)
                                      (dolist (q queries)
                                        (push (multiple-value-list (session-solve s :assumptions q))
                                              session-answers))))))))
         (fresh-seconds
           (nth-value 0 (best-time runs
                         (lambda ()
                           (setf fresh-answers '())
                           (let ((cnf (make-cnf)) (backend (make-instance backend-class)))
                             (loop for (count clauses queries) in segments
                                   do (loop repeat count
                                            do (cnf-ensure-variable cnf (1+ (cnf-variable-count cnf))))
                                      (dolist (c clauses) (cnf-add-clause cnf c))
                                      (dolist (q queries)
                                        (push (multiple-value-list
                                               (solve cnf :backend backend
                                                          :assumptions (mapcar #'lit-formula q)))
                                              fresh-answers))))))))
         (checks (let ((so-far '()))
                   ;; (query . clauses so far) per query, in order
                   (loop for (nil clauses queries) in segments
                         do (setf so-far (append so-far clauses))
                         append (mapcar (lambda (q) (cons q so-far)) queries))))
         (queries (mapcar #'car checks)))
    (setf session-answers (nreverse session-answers)
          fresh-answers (nreverse fresh-answers))
    (values session-seconds fresh-seconds
            (every (lambda (s f) (eq (second s) (second f))) session-answers fresh-answers)
            (every (lambda (check s f)
                     (destructuring-bind (q . clauses) check
                       (or (not (second s))
                           (and (model-satisfies-p (first s) clauses q)
                                (clauses-satisfied-p clauses (model->assignment (first f)))))))
                   checks session-answers fresh-answers)
            (length queries)
            (count nil session-answers :key #'second))))

(deftest session-benchmark-chain
  (multiple-value-bind (session fresh agree models queries unsat) (run-session-benchmark)
    (ok agree (format nil "~D queries: the same status in the session and fresh" queries))
    (ok models "every model satisfies the clauses and its assumptions")
    (ok (< 0 unsat queries) (format nil "~D of ~D queries UNSAT" unsat queries))
    (ok t (format nil "session benchmark (soft): session ~,3F s, fresh ~,3F s, speedup ~,1Fx"
                  session fresh (if (plusp session) (/ fresh session) 0)))))
