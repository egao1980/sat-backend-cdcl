;;;; sat-backend-cdcl: conflict-driven clause learning for sat-protocol.
;;;; Brief: cl-stack/docs/capabilities/logic.md (Track L, slice L2b-3).

(defpackage #:sat-backend-cdcl
  (:use #:cl #:sat-protocol)
  (:export
   #:cdcl-backend
   #:cdcl-backend-statistics))

(in-package #:sat-backend-cdcl)
