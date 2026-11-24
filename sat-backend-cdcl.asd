(defsystem "sat-backend-cdcl"
  :version "0.1.0"
  :description "sat-protocol backend: conflict-driven clause learning (watched literals, 1UIP learning, VSIDS, restarts, final-conflict cores)"
  :author "egao1980"
  :license "MIT"
  :depends-on ((:version "sat-protocol" "0.2.0"))
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "backend")
               (:file "search"))
  :in-order-to ((test-op (test-op "sat-backend-cdcl/tests"))))

;;; sat-protocol's conformance suite (twice: default and stress parameters),
;;; CDCL-specific tests, and the performance gates. sat-backend-dpll is the
;;; status oracle for mid-sized instances and the calibration baseline.
(defsystem "sat-backend-cdcl/tests"
  :depends-on ("sat-backend-cdcl" "sat-protocol/conformance" "sat-backend-dpll" "rove")
  :pathname "tests"
  :serial t
  :components ((:file "package")
               (:file "instances")
               (:file "backend-test")
               (:file "learning-test")
               (:file "final-conflict-test")
               (:file "status-test")
               (:file "performance-test"))
  :perform (test-op (o c)
             (unless (symbol-call :sat-backend-cdcl/tests :run-with-cdcl)
               (error "tests failed for ~A" (component-name c)))))
