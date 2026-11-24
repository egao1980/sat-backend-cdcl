;;;; sat-backend-cdcl: conflict-driven clause learning for sat-protocol.
;;;; Brief: cl-stack/docs/capabilities/logic.md (Track L, slice L2b-3).
;;;;
;;;; 0.1.0 specialises BACKEND-SOLVE and BACKEND-FINAL-CONFLICT. The other
;;;; backend GFs (BACKEND-SOLVE-ALL, BACKEND-MINIMIZE, BACKEND-UNSAT-CORE) keep
;;;; sat-protocol's default methods, which run on those two. Incremental
;;;; sessions (sat-protocol 0.3, L2b-2) come in a later version.

(defpackage #:sat-backend-cdcl
  (:use #:cl #:sat-protocol)
  (:export
   ;; the backend (src/backend.lisp)
   #:cdcl-backend
   #:cdcl-backend-restart-policy
   #:cdcl-backend-luby-unit
   #:cdcl-backend-restart-window
   #:cdcl-backend-restart-margin
   #:cdcl-backend-variable-decay
   #:cdcl-backend-clause-decay
   #:cdcl-backend-phase-saving
   #:cdcl-backend-default-phase
   #:cdcl-backend-clause-minimization
   #:cdcl-backend-reduce-base
   #:cdcl-backend-reduce-increment
   #:cdcl-backend-budget-unit
   #:cdcl-backend-learnt-hook
   #:cdcl-backend-statistics))

(in-package #:sat-backend-cdcl)
