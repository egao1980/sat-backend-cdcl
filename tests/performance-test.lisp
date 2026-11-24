(in-package #:sat-backend-cdcl/tests)

;;; Performance gates: wall-clock bounds a sound CDCL meets with room to
;;; spare. Each gate checks its answers as well (statuses, models, proven
;;; optima), so a fast wrong answer fails.
;;;
;;; Calibration (2026-11-24; Apple M4 laptop, SBCL 2.6.9, sat-protocol 0.2.0,
;;; sat-backend-dpll 0.1.0 with its default :dlis heuristic, a 60 s cap per
;;; instance; MiniSat 2.2, Glucose 4 and RC2 through python-sat on the same
;;; instances, tests/fixtures/record-status.py):
;;;
;;;   gate                        DPLL                       reference                  bound
;;;   random 3-SAT, 20 x 150      3.96 s                     MiniSat 0.10 s, Glucose    4 s
;;;   vars, ratio 4.26                                       0.16 s
;;;   PHP(8,7)                    0.013 s (5039 decisions)   MiniSat 0.022 s (11.5k     5 s
;;;                                                          conflicts)
;;;   hidden core, 4 instances    46 s, 55 s, > 60 s, > 60 s MiniSat < 0.001 s each     4 s
;;;                               (> 220 s)                  (~150 conflicts)
;;;   weighted chains, 6, to a    none proven in 60 s each   RC2 0.002 s each; the      30 s
;;;   proven optimum with         (> 360 s); incumbents      :core-guided call pattern
;;;   :core-guided                6-15 for optima 5-8        on from-scratch MiniSat:
;;;                                                          784 calls, 0.2-0.3 s
;;;
;;; - Random 3-SAT near the threshold and pigeonhole are where DPLL is
;;;   strong: sat-backend-dpll's pure literals refute PHP(n+1,n) in (n-1)!
;;;   decisions, and its DLIS search solves the 3-SAT batch in 4 s. CDCL
;;;   cannot be 10x faster there (10x is 0.4 s, 4x MiniSat), so these two
;;;   gates are absolute: the batch no slower than DPLL (40x MiniSat), and
;;;   PHP(8,7) within 5 s (MiniSat needs 11.5k conflicts; VSIDS needs vary).
;;; - The hidden-core and chain gates are the ones a DPLL cannot meet:
;;;   chronological backtracking re-refutes the core under every noise
;;;   assignment, and a final conflict made of every assumption gives
;;;   core-guided search useless cores. Their bounds are more than 10x below
;;;   DPLL's (capped) time: 55x for the hidden cores, 12x for the chains.
;;; - The chain bound is the least certain: sat-protocol 0.2's :core-guided
;;;   solves from scratch on every call (no session until L2b-2) and shrinks
;;;   each core by deletion, about 130 backend calls per chain. 30 s for six
;;;   is 5 s per chain of 227-379 soft literals, the consumer's target per
;;;   window (cl-stack#370), and about 100x the from-scratch MiniSat figure.
;;; - Bounds are laptop seconds times SPEED-FACTOR: this machine's time for
;;;   a fixed probe (sat-backend-dpll on PHP(10,9), 0.74 s on the laptop)
;;;   over the laptop's, never below 1. So slower CI runners get
;;;   proportionally more time and faster machines never get less.
;;; Re-measure with PERFORMANCE-BASELINE (any backend, a cap per instance)
;;; and update this table when a dependency or the instances change.

(defparameter *gate-3sat* '(:seed 4260 :count 20 :nvars 150 :nclauses 639 :seconds 4)
  "RANDOM-3SAT-BATCH: 20 instances, 150 variables, ratio 4.26.")

(defparameter *gate-3sat-status*
  '(t t t nil t t t nil nil t t nil t nil t t nil nil t nil)
  "MiniSat 2.2's status per instance of the batch (Glucose 4 agrees);
tests/fixtures/PROVENANCE.md.")

(defparameter *gate-php* '(:pigeons 8 :holes 7 :seconds 5))

(defparameter *gate-hidden-core*
  '(:seed 7700 :count 4 :noise-vars 200 :noise-clauses 840 :pigeons 6 :holes 5 :seconds 4)
  "HIDDEN-CORE-INSTANCE: planted 3-SAT noise at ratio 4.2 plus PHP(6,5).")

(defparameter *gate-chains*
  '(:seed 3702 :count 6 :positions 12 :min-options 4 :max-options 8 :cost-percent 85 :seconds 30)
  "CHAIN-FAMILY: 12 positions of 4-8 options, 85% of the allowed transitions
costly (1-4), 30% of the options costly; 274-438 variables, 227-379 soft
literals. Minimised with :STRATEGY :CORE-GUIDED to proven optimality.")

(defparameter +probe-laptop-seconds+ 0.74d0
  "sat-backend-dpll on PHP(10,9) on the calibration laptop.")

(defvar *speed-factor* nil)

(defun speed-factor ()
  "This machine's probe time over the laptop's, at least 1 (best of two runs)."
  (or *speed-factor*
      (setf *speed-factor*
            (let ((best (loop repeat 2
                              minimize (nth-value 0 (timed (lambda ()
                                                              (backend-solve (make-instance 'dpll-backend)
                                                                             (php 10 9))))))))
              (max 1d0 (/ best +probe-laptop-seconds+))))))

(defun timed (thunk)
  "(values seconds (multiple-value-list (funcall THUNK)))."
  (let ((start (get-internal-real-time)))
    (let ((values (multiple-value-list (funcall thunk))))
      (values (seconds-since start) values))))

(defun spec-keys (spec &rest drop)
  (loop for (k v) on spec by #'cddr unless (member k drop) nconc (list k v)))

(defun gate-3sat-instances ()
  (destructuring-bind (&key seed count nvars nclauses &allow-other-keys) *gate-3sat*
    (random-3sat-batch seed count nvars nclauses)))

(defun gate-hidden-core-instances ()
  "List of (clauses . nvars)."
  (destructuring-bind (&key seed count &allow-other-keys) *gate-hidden-core*
    (let ((rng (make-rng seed)))
      (loop repeat count
            collect (multiple-value-bind (clauses n)
                        (apply #'hidden-core-instance rng
                               (spec-keys *gate-hidden-core* :seed :count :seconds))
                      (cons clauses n))))))

(defun gate-chain-instances (&optional (spec *gate-chains*))
  (destructuring-bind (&key seed count &allow-other-keys) spec
    (apply #'chain-family seed count (spec-keys spec :seed :count :seconds))))

(defun gate-seconds (spec)
  (* (getf spec :seconds) (speed-factor)))

(defmacro with-gate ((label spec remaining) &body body)
  "Run BODY with REMAINING bound to a function of no arguments returning the
seconds left (at least 0), then check the elapsed time against the gate."
  (let ((limit (gensym "LIMIT")) (start (gensym "START")))
    `(let* ((,limit (gate-seconds ,spec))
            (,start (get-internal-real-time)))
       (flet ((,remaining () (max 0 (- ,limit (seconds-since ,start)))))
         ,@body)
       (let ((elapsed (seconds-since ,start)))
         (ok (<= elapsed ,limit)
             (format nil "~A: ~,2F s within ~,2F s (speed factor ~,2F)"
                     ,label elapsed ,limit (speed-factor)))))))

(defun solve-before (seconds clauses nvars)
  "SOLVE on a fresh CDCL-BACKEND; (values :TIMEOUT NIL) after SECONDS."
  (call-with-deadline seconds
                      (lambda () (solve (clauses->cnf clauses nvars) :backend (cdcl)
                                                                     :budget 1024 :complete nil))))

(deftest gate-random-3sat
  (with-gate ("random 3-SAT batch" *gate-3sat* remaining)
    (loop for clauses in (gate-3sat-instances)
          for expected in *gate-3sat-status*
          for i from 0
          do (multiple-value-bind (model sat) (solve-before (remaining) clauses 150)
               (when (eq model :timeout)
                 (ok nil (format nil "instance ~D: out of time" i))
                 (return))
               (ok (eq expected sat) (format nil "instance ~D: MiniSat's status" i))
               (when sat
                 (ok (clauses-satisfied-p clauses (model->assignment model))
                     (format nil "instance ~D: the model" i)))))))

(deftest gate-pigeonhole
  (with-gate ("PHP(8,7)" *gate-php* remaining)
    (multiple-value-bind (clauses n) (pigeonhole (getf *gate-php* :pigeons) (getf *gate-php* :holes))
      (multiple-value-bind (model sat) (solve-before (remaining) clauses n)
        (ok (and (null model) (null sat)) "UNSAT in time")))))

(deftest gate-hidden-core
  (with-gate ("hidden cores" *gate-hidden-core* remaining)
    (loop for (clauses . n) in (gate-hidden-core-instances)
          for i from 0
          do (multiple-value-bind (model sat) (solve-before (remaining) clauses n)
               (ok (and (null model) (null sat)) (format nil "instance ~D: UNSAT in time" i))
               (when model (return))))))

(deftest gate-chains-core-guided
  (with-gate ("chains, :core-guided" *gate-chains* remaining)
    (loop for ci in (gate-chain-instances)
          for i from 0
          do (multiple-value-bind (cnf objective) (chain-instance-cnf ci)
               (multiple-value-bind (model cost optimal-p)
                   (minimize cnf objective :backend (cdcl) :strategy :core-guided
                                           :timeout (remaining))
                 (ok (eq t optimal-p) (format nil "chain ~D: proven in time" i))
                 (ok (eql (chain-instance-optimum ci) cost) (format nil "chain ~D: the DP optimum" i))
                 (let ((labelling (chain-instance-labelling ci model)))
                   (ok (and (listp labelling) (eql cost (chain-instance-cost ci labelling)))
                       (format nil "chain ~D: a valid labelling of that cost" i)))
                 (unless optimal-p (return)))))))

;;; ------------------------------------------------------------ calibration

(defun performance-baseline (backend &key (cap 60) (gates '(:3sat :php :hidden-core :chains))
                                          (chains *gate-chains*) (stream *standard-output*))
  "Run the gate instances on BACKEND, at most CAP seconds each, printing each
time and answer. Returns a plist of total seconds per gate. For calibration:
  (performance-baseline (make-instance 'sat-backend-dpll:dpll-backend) :cap 30)"
  (let ((totals '()))
    (flet ((solve-capped (clauses n)
             (timed (lambda ()
                      (call-with-deadline
                       cap (lambda () (solve (clauses->cnf clauses n) :backend backend
                                                                      :budget 1024 :complete nil))))))
           (report (label i secs vals)
             (format stream "~&~A ~2D ~9,3F s ~S~%" label i secs
                     (if (eq (first vals) :timeout) :timeout (second vals)))
             (finish-output stream)))
      (when (member :3sat gates)
        (setf (getf totals :3sat)
              (loop for clauses in (gate-3sat-instances) for i from 0
                    sum (multiple-value-bind (secs vals) (solve-capped clauses 150)
                          (report "3sat" i secs vals)
                          secs))))
      (when (member :php gates)
        (multiple-value-bind (clauses n) (pigeonhole (getf *gate-php* :pigeons) (getf *gate-php* :holes))
          (multiple-value-bind (secs vals) (solve-capped clauses n)
            (report "php" 0 secs vals)
            (setf (getf totals :php) secs))))
      (when (member :hidden-core gates)
        (setf (getf totals :hidden-core)
              (loop for (clauses . n) in (gate-hidden-core-instances) for i from 0
                    sum (multiple-value-bind (secs vals) (solve-capped clauses n)
                          (report "hidden" i secs vals)
                          secs))))
      (when (member :chains gates)
        (setf (getf totals :chains)
              (loop for ci in (gate-chain-instances chains) for i from 0
                    sum (multiple-value-bind (cnf objective) (chain-instance-cnf ci)
                          (multiple-value-bind (secs vals)
                              (timed (lambda () (minimize cnf objective :backend backend
                                                                        :strategy :core-guided
                                                                        :timeout cap)))
                            (format stream "~&chain ~2D: ~D vars, ~D clauses, ~D soft, optimum ~D: ~9,3F s, cost ~S, optimal ~S~%"
                                    i (cnf-variable-count cnf) (cnf-clause-count cnf) (length objective)
                                    (chain-instance-optimum ci) secs (second vals) (third vals))
                            (finish-output stream)
                            secs))))))
    totals))
