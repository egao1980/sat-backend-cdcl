;;;; Native incremental sessions (0.2.0; sat-protocol 0.3.0, Track L slice
;;;; L2b-2). GIVEN: the method signatures and the rules below, which the tests
;;;; pin. IMPLEMENTED: the five methods, here, on solver.lisp's session pieces
;;;; (%ENSURE-VARIABLES, %ADD-INPUT-CLAUSE, %BEGIN-CALL). Add files to the .asd
;;;; as needed; the rules do not depend on the file layout.
;;;;
;;;; The protocol side is sat-protocol's src/session.lisp: front ends, the GF
;;;; contract, and the session path of SESSION-MINIMIZE (its strategies push
;;;; guarded clauses through BACKEND-SESSION-ADD-CLAUSES and search with
;;;; BACKEND-SESSION-SOLVE / -FINAL-CONFLICT, retiring each selector with a unit
;;;; clause before it returns). This file is the backend side: one persistent
;;;; solver per session, so nothing is re-encoded or reloaded between calls and
;;;; what one call learns serves the next.
;;;;
;;;; --------------------------------------------------------------- the state
;;;; (backend-session-open backend session) -> a fresh solver state, never NIL:
;;;;   every CDCL session is stateful. It holds what search.lisp's %SOLVER holds
;;;;   (clauses and watches, the trail, activities and the heap, saved phases,
;;;;   the learnt database) for the session's whole life, sized for
;;;;   (SESSION-VARIABLE-COUNT session) and grown as it grows.
;;;; Persists from one call to the next: every clause given (the input
;;;;   clauses), the learnt clauses and their LBDs and activities, the level-0
;;;;   trail (unit clauses, learnt units, their consequences), variable
;;;;   activities and the EVSIDS / clause bumps, saved phases, and the
;;;;   reduction schedule (REDUCTION in search.lisp, with L counting the learnt
;;;;   clauses of every call of the session, so the database stays bounded over
;;;;   a long session).
;;;; Per call: the assumptions, ORDER, PHASE, BUDGET (its count starts at 0
;;;;   each call, in the backend's BUDGET-UNIT), the restart run (a call starts
;;;;   run 1: its Luby limit, an empty Glucose window, the LBD mean of this
;;;;   call's clauses) and the statistics (from 0; CDCL-BACKEND-STATISTICS is
;;;;   the plist of the last call on the backend, session call or not).
;;;; Sound across calls because clauses only grow: every learnt clause and
;;;;   level-0 fact is implied by the clauses given so far. Assumptions are
;;;;   decisions (levels 1..), so nothing derived from them outlives the call.
;;;;
;;;; ---------------------------------------------------------------- the GFs
;;;; (backend-session-add-clauses backend session clauses)
;;;;   First back to level 0 (an earlier call may have ended, or been cut
;;;;   short, at any level; phases saved as at step 3), then grow to
;;;;   SESSION-VARIABLE-COUNT, then add each clause after the earlier input
;;;;   clauses, in order, as R1 (search.lisp's %LOAD) adds one: repeated
;;;;   literals dropped (first occurrences kept), a tautology stored but never
;;;;   watched, its variables put in the heap. Against the level-0 assignment:
;;;;   - a literal true at level 0: the clause is satisfied for good (stored);
;;;;   - every literal false (the empty clause included): the session is
;;;;     UNSAT for good;
;;;;   - one literal not false, unassigned: assigned at level 0 with the clause
;;;;     as its reason (its consequences propagate at the next call);
;;;;   - otherwise watched on two literals that are not false.
;;;;   No search, no statistics, no hook call.
;;;; (backend-session-solve backend session &key assumptions order phase budget)
;;;; (backend-session-final-conflict backend session assumptions &key budget order phase)
;;;;   The call of search.lisp, every rule of its header (the loop, the
;;;;   budget, restarts, reduction, LEARNT-HOOK, the final conflict, the
;;;;   values), on the session's state instead of a fresh %SOLVER: it starts at
;;;;   level 0 with what the earlier calls left and propagates what is
;;;;   pending; "the input clauses" (the SAT check 4b, ORDER's candidates, the
;;;;   heap) are every clause given so far, in the order given. SAT ->
;;;;   (values LITERALS T): the trail, level-0 facts of earlier calls included.
;;;;   A session UNSAT for good answers UNSAT at once: BACKEND-SESSION-SOLVE
;;;;   (values NIL NIL), BACKEND-SESSION-FINAL-CONFLICT (values NIL T) (the
;;;;   clauses alone are refuted: core NIL).
;;;;   A call cut short by a non-local exit (a budget USE-VALUE, a throw out of
;;;;   a handler or a hook) leaves a consistent state: the next operation goes
;;;;   back to level 0 first and its answer obeys these rules.
;;;; (backend-session-close backend session): drop the state; it is not used
;;;;   again.
;;;; BACKEND-SESSION-MINIMIZE keeps sat-protocol's default method (the session
;;;; path). BACKEND-SOLVE and BACKEND-FINAL-CONFLICT are unchanged: each still
;;;; starts from nothing, and no session operation calls them.
;;;;
;;;; Deterministic: the answers, hook calls and statistics of a session depend
;;;; only on its sequence of operations (and the backend's parameters), so two
;;;; sessions given the same sequence answer the same. A call whose budget
;;;; handler always continues makes exactly the decisions, hook calls, answer
;;;; and statistics of the same call without a budget (as in search.lisp).

(in-package #:sat-backend-cdcl)

;;; Between two operations the solver is consistent in this sense: every
;;; literal at level 0 is implied by the input clauses given so far (input
;;; and add-time units, learnt units and their consequences); add-time units
;;; may still be pending (at or after QHEAD), which the next call's first
;;; propagation visits; every clause of two or more literals is watched under
;;; the two-watch invariant, or is a tautology, or is true at level 0 for
;;; good; every input ordinal before SCAN is true at level 0; and every
;;; unassigned input variable is in the heap, except after a call cut short
;;; (DIRTY, repaired by the next operation). Levels above 0 hold only what the
;;; last call left there, and every operation first undoes them.

(defstruct (%session-state (:constructor %make-session-state (solver))
                           (:conc-name %state-) (:copier nil) (:predicate nil))
  "BACKEND-SESSION-OPEN's value: the session's persistent solver and its
lifecycle."
  (solver nil :type (or null %solver)) ; NIL once BACKEND-SESSION-CLOSE ran
  (busy nil)                           ; a call on this state is running
  (dirty nil))                         ; the last call ended by a non-local exit

(defun %idle-solver (session)
  "SESSION's solver, ready for an operation, and its state: back to level 0
(phases saved, as at step 3), the heap repaired after a call cut short.
SAT-SESSION-CLOSED when the state was dropped (only a caller going around the
front ends can get here); SAT-ERROR for an operation from a hook or handler
inside a running call of the same session, which would undo that call's
levels under it."
  (let* ((state (session-backend-state session))
         (s (%state-solver state)))
    (unless s
      (error 'sat-session-closed :session session))
    (when (%state-busy state)
      (error 'sat-error
             :message (format nil "~S: a session operation from inside a call of that session"
                              session)))
    (%cancel-until s 0)
    (when (%state-dirty state)
      (setf (%state-dirty state) nil)
      (%repair-heap s))
    (values s state)))

(defun %session-call (session assumptions order phase budget want-core)
  "search.lisp's call on SESSION's solver: (values T literals NIL) for SAT,
(values NIL NIL core) for UNSAT, CORE NIL unless WANT-CORE, and NIL when the
clauses alone are refuted. The statistics are published however the call ends;
an end by a non-local exit marks the state dirty."
  (multiple-value-bind (s state) (%idle-solver session)
    ;; Assumption variables may have arrived with no clause (no backend call).
    (%ensure-variables s (session-variable-count session))
    (%begin-call s assumptions order phase budget want-core)
    (let ((done nil))
      (setf (%state-busy state) t)
      (unwind-protect
           (multiple-value-prog1
               (cond ((s-refuted s)
                      ;; UNSAT for good: at once, all statistics 0.
                      (values nil nil nil))
                     ((%search s)
                      (values t (%trail-literals s) nil))
                     (t
                      ;; search.lisp, statistics: CONFLICTS - LEARNT-CLAUSES is 1
                      ;; exactly when a level-0 conflict ended the call (the
                      ;; clauses alone are refuted), 0 when an assumption was
                      ;; false at its turn.
                      (when (> (s-conflicts s) (s-learnt s))
                        (setf (s-refuted s) t))
                      (values nil nil (and want-core (%core s assumptions)))))
             (setf done t))
        (setf (%state-busy state) nil)
        (unless done
          (setf (%state-dirty state) t))
        ;; S, not the state's slot: a handler may have closed the session.
        (%publish s)))))

(defmethod backend-session-open ((backend cdcl-backend) session)
  "A fresh persistent solver state for SESSION (this file's header): no
variable, no clause, the backend's parameters and the reduction schedule at
its start."
  (declare (ignore session))
  (%make-session-state (%setup (%make-solver backend) 0 0 '() nil nil nil nil)))

(defmethod backend-session-add-clauses ((backend cdcl-backend) session clauses)
  "Add CLAUSES to SESSION's solver at level 0 (this file's header)."
  (let ((s (%idle-solver session)))
    (%ensure-variables s (session-variable-count session))
    ;; Once refuted, every answer is UNSAT: later clauses change nothing.
    (unless (s-refuted s)
      (dolist (clause clauses)
        (%add-input-clause s clause)
        (when (s-refuted s)
          (return))))
    nil))

(defmethod backend-session-solve ((backend cdcl-backend) session
                                  &key assumptions order phase budget)
  "search.lisp's call on SESSION's solver state."
  (multiple-value-bind (sat literals)
      (%session-call session assumptions order phase budget nil)
    (if sat
        (values literals t)
        (values nil nil))))

(defmethod backend-session-final-conflict ((backend cdcl-backend) session assumptions
                                           &key budget order phase)
  "search.lisp's call on SESSION's solver state, with the final conflict."
  (multiple-value-bind (sat literals core)
      (%session-call session assumptions order phase budget t)
    (if sat
        (values nil nil literals)
        (values core t))))

(defmethod backend-session-close ((backend cdcl-backend) session)
  "Drop SESSION's solver state. A call still running (from a handler that
closed the session) keeps its own reference and finishes."
  (setf (%state-solver (session-backend-state session)) nil)
  nil)
