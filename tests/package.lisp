;;;; sat-backend-cdcl/tests: sat-protocol's conformance suite on CDCL-BACKEND
;;;; (default parameters, and again with *STRESS-PARAMETERS*), then the
;;;; CDCL-specific tests and the performance gates. RUN-WITH-CDCL is what
;;;; test-op calls. Everything under tests/ is the contract: an
;;;; implementation does not edit it.
;;;;
;;;; Oracles: brute force (sat-protocol/conformance) for small instances,
;;;; sat-backend-dpll for mid-sized ones, statuses recorded with MiniSat for
;;;; the performance instances (tests/fixtures/PROVENANCE.md), and a dynamic
;;;; programme for the chain family (instances.lisp).

(defpackage #:sat-backend-cdcl/tests
  (:use #:cl #:rove #:sat-protocol #:sat-backend-cdcl)
  (:import-from #:sat-protocol/conformance
                #:run-conformance
                #:f
                #:make-rng
                #:rng-int
                #:random-3sat
                #:pigeonhole
                #:clauses->cnf
                #:clauses-satisfied-p
                #:model->assignment
                #:brute-models
                #:brute-satisfiable-p)
  (:import-from #:sat-backend-dpll
                #:dpll-backend)
  (:export #:run-with-cdcl
           #:performance-baseline))

(in-package #:sat-backend-cdcl/tests)

(defparameter *stress-parameters*
  '(:restart-policy :glucose :restart-window 4 :clause-minimization :basic
    :phase-saving nil :default-phase t :reduce-base 8 :reduce-increment 2)
  "The conformance suite's second configuration: frequent restarts and
reductions on its small instances, other minimisation and phases.")

(defun run-with-cdcl (&key (style :spec))
  (let ((default (let ((*sat-backend* (make-instance 'cdcl-backend)))
                   (rove:run '("sat-protocol/conformance" "sat-backend-cdcl/tests") :style style)))
        (stress (run-conformance (apply #'make-instance 'cdcl-backend *stress-parameters*)
                                 :style style)))
    (and default stress)))

;;; ---------------------------------------------------------------- helpers

(defun cdcl (&rest parameters)
  (apply #'make-instance 'cdcl-backend parameters))

(defparameter *configurations*
  `(("default")
    ("glucose" :restart-policy :glucose)
    ("no-restarts" :restart-policy nil)
    ("luby-1" :luby-unit 1)
    ("basic-min" :clause-minimization :basic)
    ("no-min" :clause-minimization nil)
    ("no-phase-saving" :phase-saving nil :default-phase t)
    ("small-reduce" :reduce-base 10 :reduce-increment 2)
    ("stress" ,@*stress-parameters*))
  "Named parameter lists; every one must give correct answers.")

(defun configuration (name)
  (let ((entry (assoc name *configurations* :test #'string=)))
    (unless entry (error "no configuration ~S" name))
    (rest entry)))

(defun configured (name &rest more)
  "A fresh backend of configuration NAME, with MORE parameters first."
  (apply #'make-instance 'cdcl-backend (append more (configuration name))))

(defun stats (backend key)
  (getf (cdcl-backend-statistics backend) key))

(defparameter +statistics-keys+
  '(:decisions :propagations :conflicts :learnt-clauses :backjumps
    :restarts :reductions :deleted-clauses))

(defun answer-ok-p (clauses literals)
  "LITERALS assign each variable at most once and satisfy every clause."
  (let ((vars (mapcar #'abs literals)))
    (and (every #'integerp literals)
         (notany #'zerop literals)
         (= (length vars) (length (remove-duplicates vars)))
         (every (lambda (c) (some (lambda (l) (member l literals)) c)) clauses))))

(defun solve-clauses (backend clauses nvars &rest keys)
  "BACKEND-SOLVE on a fresh CNF of CLAUSES over 1..NVARS."
  (apply #'backend-solve backend (clauses->cnf clauses nvars) keys))

(defun luby (i)
  "The I-th term (from 1) of the Luby sequence 1 1 2 1 1 2 4 1 1 2 ..."
  (loop for k from 1
        when (= i (1- (ash 1 k))) return (ash 1 (1- k))
        when (< i (1- (ash 1 k))) return (luby (- i (1- (ash 1 (1- k)))))))

(defun luby-sum (unit r)
  (* unit (loop for i from 1 to r sum (luby i))))

(defun reductions-due (base increment learnt)
  "#{k >= 1 : k*BASE + INCREMENT*k*(k-1)/2 <= LEARNT}."
  (loop for k from 1
        while (<= (+ (* k base) (/ (* increment k (1- k)) 2)) learnt)
        count t))

(defun seconds-since (start)
  (/ (float (- (get-internal-real-time) start) 1d0) internal-time-units-per-second))

(defun call-with-deadline (seconds thunk &key (step 1024))
  "Call THUNK, which runs one front-end search with :BUDGET STEP, raising the
budget by STEP while less than SECONDS have passed; after that the search
returns :TIMEOUT (USE-VALUE). Returns THUNK's values."
  (let ((start (get-internal-real-time)))
    (handler-bind ((sat-budget-exceeded
                     (lambda (c)
                       (if (> (seconds-since start) seconds)
                           (use-value :timeout c)
                           (store-value (+ (sat-budget-exceeded-budget c) step) c)))))
      (funcall thunk))))
