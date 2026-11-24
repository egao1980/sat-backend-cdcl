(in-package #:sat-backend-cdcl/tests)

;;; Generated instances (no DIMACS files): every generator draws from
;;; sat-protocol/conformance's 31-bit LCG (MAKE-RNG / RNG-INT), so a seed
;;; gives the same instance on every implementation. Recorded statuses and
;;; how they were obtained: tests/fixtures/PROVENANCE.md.

;;; ------------------------------------------------------------ planted 3-SAT

(defun planted-3sat (rng nvars nclauses)
  "NCLAUSES random 3-clauses over 1..NVARS, each satisfied by a random planted
assignment. Returns (values clauses planted), PLANTED a function var -> boolean."
  (let ((planted (make-array (1+ nvars) :initial-element nil)))
    (loop for v from 1 to nvars do (setf (aref planted v) (zerop (rng-int rng 2))))
    (flet ((value (l) (if (plusp l) (aref planted l) (not (aref planted (- l))))))
      (values (loop with clauses = '()
                    while (< (length clauses) nclauses)
                    do (let ((c (first (random-3sat rng nvars 1))))
                         (when (some #'value c) (push c clauses)))
                    finally (return (nreverse clauses)))
              (lambda (v) (aref planted v))))))

;;; ------------------------------------------------------------- hidden core
;;; A small unsatisfiable core among many satisfiable constraints on other
;;; variables: planted 3-SAT "noise" over 1..NOISE-VARS, then PHP(PIGEONS,
;;; HOLES) over the next variables. The noise literals occur more often and
;;; have the lower indices, so a search decides noise first. Chronological
;;; backtracking refutes the core again under every noise assignment it
;;; tries; a learnt clause mentions core variables only, so CDCL refutes the
;;; core once and backjumps over the noise.

(defun hidden-core-instance (rng &key (noise-vars 120) (noise-clauses 504) (pigeons 6) (holes 5))
  "(values clauses nvars): unsatisfiable."
  (let ((noise (planted-3sat rng noise-vars noise-clauses)))
    (multiple-value-bind (core n) (pigeonhole pigeons holes)
      (values (append noise
                      (mapcar (lambda (c)
                                (mapcar (lambda (l) (if (plusp l) (+ l noise-vars) (- l noise-vars)))
                                        c))
                              core))
              (+ noise-vars n)))))

;;; -------------------------------------------------------------- chain family
;;; Weighted chain labelling, the shape of sequence-labelling / chain
;;; selection problems: POSITIONS positions, each with 1 of OPTIONS(p)
;;; options chosen; between adjacent positions some option pairs are
;;; forbidden (no-goods) and the others carry a transition cost (0 or
;;; 1..MAX-COST); an option may carry a unary cost. Encoding: x(p,l) one-hot
;;; per position (an at-least-one clause and pairwise at-most-one clauses),
;;; a binary clause per no-good, and per costly pair a cost literal
;;; y(p,l,m) with x(p,l) & x(p+1,m) -> y(p,l,m); the objective weighs the
;;; y and the costly x. Every variable is a user variable (no auxiliaries).

(defstruct (chain-instance (:constructor %make-chain-instance) (:conc-name ci-))
  (options #() :type simple-vector)       ; options at each position
  (unary #() :type simple-vector)         ; per position: vector of option costs
  (transition #() :type simple-vector))   ; per p < P-1: array [l m] of cost or :NOGOOD

(defun make-chain-instance (rng &key (positions 8) (min-options 2) (max-options 6)
                                     (nogood-percent 20) (cost-percent 70) (max-cost 4)
                                     (unary-percent 30))
  (let* ((options (coerce (loop repeat positions
                                collect (+ min-options
                                           (rng-int rng (1+ (- max-options min-options)))))
                          'simple-vector))
         (unary (map 'simple-vector
                     (lambda (k)
                       (coerce (loop repeat k
                                     collect (if (< (rng-int rng 100) unary-percent)
                                                 (1+ (rng-int rng max-cost))
                                                 0))
                               'simple-vector))
                     options))
         (transition
           (coerce (loop for p below (1- positions)
                         collect (let ((a (make-array (list (svref options p)
                                                            (svref options (1+ p))))))
                                   (dotimes (l (svref options p) a)
                                     (dotimes (m (svref options (1+ p)))
                                       (setf (aref a l m)
                                             (cond ((< (rng-int rng 100) nogood-percent) :nogood)
                                                   ((< (rng-int rng 100) cost-percent)
                                                    (1+ (rng-int rng max-cost)))
                                                   (t 0)))))))
                   'simple-vector)))
    (%make-chain-instance :options options :unary unary :transition transition)))

(defun ci-positions (ci) (length (ci-options ci)))

(defun ci-x (p l) (list :x p l))
(defun ci-y (p l m) (list :y p l m))

(defun chain-instance-cnf (ci)
  "(values CNF OBJECTIVE): the encoding above; OBJECTIVE a MINIMIZE objective
((weight . literal-formula) ...)."
  (let ((cnf (make-cnf)) (objective '()) (n (ci-positions ci)))
    (flet ((x (p l) (cnf-ensure-variable cnf (ci-x p l))))
      (dotimes (p n)
        (dotimes (l (svref (ci-options ci) p)) (x p l)))
      (dotimes (p n)
        (let ((xs (loop for l below (svref (ci-options ci) p) collect (x p l))))
          (cnf-add-clause cnf xs)
          (loop for (a . more) on xs
                do (dolist (b more) (cnf-add-clause cnf (list (- a) (- b)))))
          (loop for l from 0 for cost across (svref (ci-unary ci) p)
                when (plusp cost) do (push (cons cost (sat-var (ci-x p l))) objective))))
      (loop for p below (1- n)
            for a = (svref (ci-transition ci) p)
            do (dotimes (l (array-dimension a 0))
                 (dotimes (m (array-dimension a 1))
                   (let ((cost (aref a l m)))
                     (cond ((eq cost :nogood)
                            (cnf-add-clause cnf (list (- (x p l)) (- (x (1+ p) m)))))
                           ((plusp cost)
                            (let ((y (cnf-ensure-variable cnf (ci-y p l m))))
                              (cnf-add-clause cnf (list (- (x p l)) (- (x (1+ p) m)) y))
                              (push (cons cost (sat-var (ci-y p l m))) objective)))))))))
    (values cnf (nreverse objective))))

(defun chain-instance-cost (ci labelling)
  "Cost of LABELLING (one option per position), or NIL when it uses a no-good."
  (let ((total 0))
    (loop for (l . more) on labelling for p from 0
          do (incf total (svref (svref (ci-unary ci) p) l))
             (when more
               (let ((c (aref (svref (ci-transition ci) p) l (first more))))
                 (when (eq c :nogood) (return-from chain-instance-cost nil))
                 (incf total c))))
    total))

(defun chain-instance-optimum (ci)
  "The dynamic-programming oracle (Viterbi): (values cost labelling) of a
cheapest feasible labelling (ties: lower options), or NIL when none exists."
  (let* ((n (ci-positions ci))
         (best (copy-seq (svref (ci-unary ci) 0)))   ; cost or NIL per option
         (back (make-array n :initial-element nil)))
    (loop for p from 1 below n
          for k = (svref (ci-options ci) p)
          for a = (svref (ci-transition ci) (1- p))
          do (let ((next (make-array k :initial-element nil))
                   (from (make-array k :initial-element nil)))
               (dotimes (m k)
                 (dotimes (l (length best))
                   (let ((b (svref best l)) (c (aref a l m)))
                     (when (and b (not (eq c :nogood)))
                       (let ((total (+ b c (svref (svref (ci-unary ci) p) m))))
                         (when (or (null (svref next m)) (< total (svref next m)))
                           (setf (svref next m) total (svref from m) l)))))))
               (setf best next (svref back p) from)))
    (let ((end nil))
      (dotimes (m (length best))
        (when (and (svref best m) (or (null end) (< (svref best m) (svref best end))))
          (setf end m)))
      (when end
        (let ((labelling (list end)))
          (loop for p from (1- n) downto 1
                do (push (svref (svref back p) (first labelling)) labelling))
          (values (svref best end) labelling))))))

(defun chain-instance-brute (ci)
  "The least cost of a feasible labelling by enumeration, or NIL."
  (let ((labellings (list nil)))
    (loop for k across (reverse (ci-options ci))
          do (setf labellings (loop for l below k
                                    nconc (mapcar (lambda (rest) (cons l rest)) labellings))))
    (let ((costs (remove nil (mapcar (lambda (lab) (chain-instance-cost ci lab)) labellings))))
      (and costs (reduce #'min costs)))))

(defun chain-instance-labelling (ci model)
  "The labelling MODEL chooses, or :INVALID (not one option per position, or a
no-good)."
  (let ((labelling
          (loop for p below (ci-positions ci)
                collect (let ((chosen (loop for l below (svref (ci-options ci) p)
                                            when (cdr (assoc (ci-x p l) model :test #'equal))
                                              collect l)))
                          (if (= 1 (length chosen))
                              (first chosen)
                              (return-from chain-instance-labelling :invalid))))))
    (if (chain-instance-cost ci labelling) labelling :invalid)))

(defun chain-family (seed count &rest keys)
  "COUNT feasible chain instances from SEED (infeasible draws are skipped)."
  (let ((rng (make-rng seed)))
    (loop with out = '()
          while (< (length out) count)
          do (let ((ci (apply #'make-chain-instance rng keys)))
               (when (chain-instance-optimum ci) (push ci out)))
          finally (return (nreverse out)))))

;;; ------------------------------------------------------- recorded instances

(defun random-3sat-batch (seed count nvars nclauses)
  "COUNT instances of RANDOM-3SAT drawn in sequence from one generator."
  (let ((rng (make-rng seed)))
    (loop repeat count collect (random-3sat rng nvars nclauses))))
