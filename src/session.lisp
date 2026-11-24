;;;; Native incremental sessions (0.2.0; sat-protocol 0.3.0, Track L slice
;;;; L2b-2). GIVEN: the method signatures and the rules below, which the tests
;;;; pin. STUBBED (%SESSION-PENDING): the five methods. Add files to the .asd as
;;;; needed; the rules do not depend on the file layout.
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

(defun %session-pending (name)
  "Contract stub for sat-backend-cdcl 0.2.0 sessions (sat-protocol 0.3, Track
L slice L2b-2). Every call is replaced by the implementation, then this
function is deleted. Signals a SIMPLE-ERROR (deliberately not a SAT-ERROR)."
  (error "sat-backend-cdcl 0.2 sessions pending: ~S" name))

(defmethod backend-session-open ((backend cdcl-backend) session)
  "A fresh persistent solver state for SESSION (this file's header)."
  (declare (ignore session))
  (%session-pending 'backend-session-open))

(defmethod backend-session-add-clauses ((backend cdcl-backend) session clauses)
  "Add CLAUSES to SESSION's solver at level 0 (this file's header)."
  (declare (ignore session clauses))
  (%session-pending 'backend-session-add-clauses))

(defmethod backend-session-solve ((backend cdcl-backend) session
                                  &key assumptions order phase budget)
  "search.lisp's call on SESSION's solver state."
  (declare (ignore session assumptions order phase budget))
  (%session-pending 'backend-session-solve))

(defmethod backend-session-final-conflict ((backend cdcl-backend) session assumptions
                                           &key budget order phase)
  "search.lisp's call on SESSION's solver state, with the final conflict."
  (declare (ignore session assumptions budget order phase))
  (%session-pending 'backend-session-final-conflict))

(defmethod backend-session-close ((backend cdcl-backend) session)
  "Drop SESSION's solver state."
  (declare (ignore session))
  (%session-pending 'backend-session-close))
