(defsystem "sat-backend-cdcl"
  :version "0.2.0"
  :description "sat-protocol backend: conflict-driven clause learning (watched literals, 1UIP learning, VSIDS, restarts, final-conflict cores, native incremental sessions)"
  :author "egao1980"
  :license "MIT"
  ;; sat-protocol 0.3.0 resolves once it is published (sessions, L2b-2).
  :depends-on ((:version "sat-protocol" "0.3.0"))
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "backend")
               (:file "solver")
               (:file "search")
               ;; 0.2.0 (L2b-2)
               (:file "session"))
  :in-order-to ((test-op (test-op "sat-backend-cdcl/tests"))))

;;; sat-protocol's conformance suite (twice: default and stress parameters;
;;; it includes the session checks), CDCL-specific tests, the performance
;;; gates and the session benchmark. sat-backend-dpll is the status oracle for
;;; mid-sized instances and the calibration baseline.
(defsystem "sat-backend-cdcl/tests"
  :depends-on ("sat-backend-cdcl" "sat-protocol/conformance" "sat-backend-dpll"
               (:version "rove" "0.11.1"))
  :pathname "tests"
  :serial t
  :components ((:file "package")
               (:file "instances")
               (:file "backend-test")
               (:file "learning-test")
               (:file "final-conflict-test")
               (:file "status-test")
               (:file "performance-test")
               ;; 0.2.0 (L2b-2)
               (:file "session-test")
               (:file "session-benchmark"))
  :perform (test-op (o c)
             (unless (symbol-call :sat-backend-cdcl/tests :run-with-cdcl)
               (error "tests failed for ~A" (component-name c)))))
