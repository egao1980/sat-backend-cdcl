;;;; CDCL-BACKEND: the class, its parameters and the load-time default.
;;;; GIVEN (no stubs here). The search the parameters steer is specified in
;;;; search.lisp.
;;;;
;;;; Parameters (initargs; readers CDCL-BACKEND-<name>). INITIALIZE-INSTANCE
;;;; checks each with CHECK-TYPE, so a bad value is a TYPE-ERROR with a
;;;; STORE-VALUE restart:
;;;;   :restart-policy      :luby (default), :glucose or NIL (never restart)
;;;;   :luby-unit           (integer 1 *), 100: conflicts per Luby unit
;;;;   :restart-window      (integer 1 *), 50: :glucose, recent LBDs averaged
;;;;   :restart-margin      (real (0) *), 0.8: :glucose, K in the restart test
;;;;   :variable-decay      (real (0) (1)), 0.95: EVSIDS decay
;;;;   :clause-decay        (real (0) (1)), 0.999: learnt-clause activity decay
;;;;   :phase-saving        generalized boolean, T
;;;;   :default-phase       generalized boolean, NIL: value of an unsaved phase
;;;;   :clause-minimization :recursive (default), :basic or NIL
;;;;   :reduce-base         (or null (integer 1 *)), 2000: learnt clauses
;;;;                        before the first reduction; NIL never reduces
;;;;   :reduce-increment    (integer 0 *), 300: growth of the reduction interval
;;;;   :budget-unit         :decisions (default; sat-protocol's unit) or
;;;;                        :conflicts: what :BUDGET counts
;;;;   :learnt-hook         (or null function), NIL: called with each learnt
;;;;                        clause (search.lisp, step 2)
;;;;
;;;; CDCL-BACKEND-STATISTICS: NIL before the first call; afterwards a fresh
;;;; plist of the last BACKEND-SOLVE / BACKEND-FINAL-CONFLICT call on this
;;;; backend, with exactly these keys, each a non-negative integer:
;;;;   :decisions :propagations :conflicts :learnt-clauses :backjumps
;;;;   :restarts :reductions :deleted-clauses
;;;; (definitions: search.lisp). The plist is current whenever the search
;;;; signals SAT-BUDGET-EXCEEDED, and when the call ends by any means (an
;;;; answer, a USE-VALUE throw, a throw out of a budget handler, an error).
;;;;
;;;; Loading the system makes a CDCL-BACKEND the default *SAT-BACKEND* when
;;;; none is set (%INSTALL-DEFAULT-BACKEND, as sat-backend-dpll does).

(in-package #:sat-backend-cdcl)

(defclass cdcl-backend (sat-backend)
  ((restart-policy :initarg :restart-policy :initform :luby
                   :reader cdcl-backend-restart-policy
                   :documentation ":LUBY, :GLUCOSE or NIL.")
   (luby-unit :initarg :luby-unit :initform 100 :reader cdcl-backend-luby-unit
              :documentation "Conflicts per unit of the Luby sequence.")
   (restart-window :initarg :restart-window :initform 50 :reader cdcl-backend-restart-window
                   :documentation ":GLUCOSE: number of recent learnt-clause LBDs averaged.")
   (restart-margin :initarg :restart-margin :initform 0.8 :reader cdcl-backend-restart-margin
                   :documentation ":GLUCOSE: K in K * recent mean LBD > mean LBD.")
   (variable-decay :initarg :variable-decay :initform 0.95 :reader cdcl-backend-variable-decay
                   :documentation "EVSIDS: the variable bump grows by 1/decay per conflict.")
   (clause-decay :initarg :clause-decay :initform 0.999 :reader cdcl-backend-clause-decay
                 :documentation "The learnt-clause bump grows by 1/decay per conflict.")
   (phase-saving :initarg :phase-saving :initform t :reader cdcl-backend-phase-saving
                 :documentation "Decide a variable's last value when PHASE is NIL.")
   (default-phase :initarg :default-phase :initform nil :reader cdcl-backend-default-phase
                  :documentation "The value of a variable with no saved phase.")
   (clause-minimization :initarg :clause-minimization :initform :recursive
                        :reader cdcl-backend-clause-minimization
                        :documentation ":RECURSIVE, :BASIC or NIL.")
   (reduce-base :initarg :reduce-base :initform 2000 :reader cdcl-backend-reduce-base
                :documentation "Learnt clauses before the first reduction; NIL: never reduce.")
   (reduce-increment :initarg :reduce-increment :initform 300
                     :reader cdcl-backend-reduce-increment
                     :documentation "Growth of the interval between reductions.")
   (budget-unit :initarg :budget-unit :initform :decisions :reader cdcl-backend-budget-unit
                :documentation "What :BUDGET counts: :DECISIONS or :CONFLICTS.")
   (learnt-hook :initarg :learnt-hook :initform nil :reader cdcl-backend-learnt-hook
                :documentation "NIL, or a function of (literals lbd) called per learnt clause.")
   (statistics :initform nil :accessor cdcl-backend-statistics
               :documentation "Counters of the last call (see this file's header)."))
  (:documentation "Conflict-driven clause learning, MiniSat / Glucose style:
two watched literals, first-UIP learning with clause minimisation, EVSIDS with
phase saving, Luby or Glucose restarts, LBD-based learnt-clause reduction and
assumption-based final-conflict cores. See src/search.lisp."))

(defmethod initialize-instance :after ((backend cdcl-backend) &key)
  (with-slots (restart-policy luby-unit restart-window restart-margin variable-decay
               clause-decay clause-minimization reduce-base reduce-increment budget-unit
               learnt-hook)
      backend
    (check-type restart-policy (member :luby :glucose nil))
    (check-type luby-unit (integer 1 *))
    (check-type restart-window (integer 1 *))
    (check-type restart-margin (real (0) *))
    (check-type variable-decay (real (0) (1)))
    (check-type clause-decay (real (0) (1)))
    (check-type clause-minimization (member :recursive :basic nil))
    (check-type reduce-base (or null (integer 1 *)))
    (check-type reduce-increment (integer 0 *))
    (check-type budget-unit (member :decisions :conflicts))
    (check-type learnt-hook (or null function))))

(defun %install-default-backend ()
  "Make a CDCL-BACKEND the default *SAT-BACKEND* when none is set."
  (unless *sat-backend*
    (setf *sat-backend* (make-instance 'cdcl-backend))))

;;; Loading the backend makes it the default when none is set.
(%install-default-backend)
