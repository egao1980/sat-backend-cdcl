;;;; CDCL-BACKEND: skeleton. The contract (search rules, parameters, tests)
;;;; follows on its own branch; the methods are stubs until then.

(in-package #:sat-backend-cdcl)

(defun %l2b3-pending (name)
  (error "sat-backend-cdcl L2b-3 pending: ~A" name))

(defclass cdcl-backend (sat-backend)
  ((statistics :initform nil :accessor cdcl-backend-statistics
               :documentation "Counters of the last search call."))
  (:documentation "Conflict-driven clause learning (MiniSat style)."))

(defmethod backend-solve ((backend cdcl-backend) cnf &key assumptions order phase budget)
  (declare (ignore cnf assumptions order phase budget))
  (%l2b3-pending 'backend-solve))

(defmethod backend-final-conflict ((backend cdcl-backend) cnf assumptions &key budget order phase)
  (declare (ignore cnf assumptions budget order phase))
  (%l2b3-pending 'backend-final-conflict))
