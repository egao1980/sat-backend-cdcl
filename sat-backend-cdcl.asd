(defsystem "sat-backend-cdcl"
  :version "0.1.0"
  :description "sat-protocol backend: conflict-driven clause learning (watched literals, 1UIP learning, VSIDS, restarts, final-conflict cores)"
  :author "egao1980"
  :license "MIT"
  :depends-on ((:version "sat-protocol" "0.2.0"))
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "backend")))
