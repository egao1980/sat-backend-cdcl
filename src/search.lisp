;;;; The CDCL search behind BACKEND-SOLVE and BACKEND-FINAL-CONFLICT
;;;; (sat-protocol 0.2, header of its src/protocol.lisp), in the style of
;;;; MiniSat 2.2 and Glucose. GIVEN: the class and its parameters
;;;; (backend.lisp), the two method signatures and the rules below, which the
;;;; tests pin. STUBBED (%L2B3-PENDING): both methods. Add files to the .asd
;;;; as needed; the rules do not depend on the file layout.
;;;;
;;;; Pure Lisp, sat-protocol only. Typed simple vectors on the hot paths
;;;; (fixnum literals, indices and counters, double-float activities); no
;;;; lists, hash tables or generic arithmetic in propagation and analysis.
;;;; The performance gates (tests/performance-test.lisp) assume this.
;;;; No preprocessing or inprocessing in 0.1.0.
;;;;
;;;; ---------------------------------------------------------------- a call
;;;; Every call starts from nothing: no clause, activity, phase or counter
;;;; survives from an earlier call on the same backend (sessions are L2b-2).
;;;; A call is deterministic: the same CNF, arguments and parameters give the
;;;; same answer, the same hook calls and the same statistics (no randomness;
;;;; nothing depends on hash order or addresses). The CNF is never modified.
;;;; Variables are 1..(CNF-VARIABLE-COUNT cnf); the variables of ASSUMPTIONS
;;;; are among them (the front ends ensure it). Input clauses are taken as
;;;; given: an empty clause makes the call UNSAT at level 0; repeated literals
;;;; are harmless; a clause with both L and -L is satisfied only once its
;;;; variable has a value (the protocol's "every clause contains one of
;;;; them").
;;;;
;;;; SAT -> (values LITERALS T): the trail, in assignment order: assumptions,
;;;; decisions and propagated literals, each variable once. UNSAT ->
;;;; (values NIL NIL). BACKEND-FINAL-CONFLICT: see FINAL CONFLICT.
;;;;
;;;; --------------------------------------------------------------- the loop
;;;; The trail holds the assigned literals, each with a decision level and a
;;;; reason: the clause that implied it, or none (decisions and assumptions).
;;;; Level 0 holds what the clauses imply on their own. A run is the search
;;;; between two restarts.
;;;;
;;;; 1. PROPAGATE, with two watched literals in every clause of two or more
;;;;    literals: while some clause has every literal false but one, and that
;;;;    one unassigned, assign it with the clause as its reason. One
;;;;    :PROPAGATIONS per literal assigned this way; the input's unit clauses
;;;;    are assigned at level 0 the same way, and count. A clause with every
;;;;    literal false is a conflict (one :CONFLICTS): go to 2. Nothing left
;;;;    to propagate: go to 4.
;;;; 2. ANALYSE. A conflict at level 0 ends the call: UNSAT, nothing learnt.
;;;;    Above level 0: first the budget, when its unit is :CONFLICTS (BUDGET
;;;;    below). Then the first-UIP clause: resolve the conflict clause with
;;;;    the reasons of its literals of the conflict level, newest first,
;;;;    until one literal of that level is left (the asserting literal).
;;;;    Literals of level 0 are left out. Every variable met above level 0 is
;;;;    bumped (EVSIDS) and every learnt clause met is bumped (clause
;;;;    activity). Then minimise the clause:
;;;;      :RECURSIVE  drop a non-asserting literal whose negation is implied
;;;;                  by the clause's other literals through reasons, followed
;;;;                  recursively (MiniSat's ccmin-mode 2);
;;;;      :BASIC      drop it when every other literal of its reason is in the
;;;;                  clause or of level 0 (ccmin-mode 1);
;;;;      NIL         keep every literal.
;;;;    The LBD of the result is its number of distinct decision levels. When
;;;;    LEARNT-HOOK is set, call it with a fresh list of the clause's literals,
;;;;    asserting literal first, and the LBD. One :LEARNT-CLAUSES. Then decay:
;;;;    the variable bump is divided by VARIABLE-DECAY and the clause bump by
;;;;    CLAUSE-DECAY. Both kinds of activity are rescaled (all together,
;;;;    order kept) before they overflow a double-float.
;;;; 3. BACKJUMP to the highest level among the clause's other literals (0 for
;;;;    a unit clause): undo every assignment above that level. An undone
;;;;    variable's value becomes its saved phase. When the target level is
;;;;    below the conflict level minus one, count one :BACKJUMPS (a
;;;;    non-chronological backjump). Keep the clause: a unit clause as a level-0
;;;;    fact, a longer one in the learnt database. Assign the asserting
;;;;    literal with the clause as its reason (one :PROPAGATIONS). Then, in
;;;;    this order, REDUCE when due and RESTART when due (below). Go to 1.
;;;; 4. DECISION POINT (no conflict, nothing to propagate):
;;;;    a. ASSUMPTIONS, one level each, in the given order: while some
;;;;       assumption has no level in this run yet, take the next one. Already
;;;;       true: it gets an empty level; take the next. False: UNSAT (FINAL
;;;;       CONFLICT below). Unassigned: assign it at a new level (neither a
;;;;       decision nor a propagation) and go to 1. Every run takes them again.
;;;;    b. SAT: when every input clause has a true literal, the call answers
;;;;       SAT. It runs at every decision point once the assumptions are in,
;;;;       before the budget. Keep it incremental (e.g. a scan position per
;;;;       level, a satisfying literal cached per clause): a full scan per
;;;;       decision misses the performance gates.
;;;;    c. BUDGET, when its unit is :DECISIONS (below).
;;;;    d. DECIDE (one :DECISIONS) at a new level, then go to 1.
;;;;       Variable: with ORDER, (funcall ORDER candidates), CANDIDATES being
;;;;       the ascending indices of the unassigned variables that occur in an
;;;;       input clause with no true literal (learnt clauses add none). ORDER
;;;;       is called once per decision and its choice is decided; a result
;;;;       that is not one of CANDIDATES signals SAT-ERROR. Without ORDER, the
;;;;       unassigned variable of greatest activity among the variables of the
;;;;       input clauses (a binary heap), ties to the lower index; it need not
;;;;       be a candidate. Activities start at 0, so the first decisions of a
;;;;       call take the variables in index order.
;;;;       Value: with PHASE, (funcall PHASE var), called once per decision
;;;;       right after ORDER; else the saved phase when PHASE-SAVING and the
;;;;       variable has one; else DEFAULT-PHASE.
;;;;
;;;; ------------------------------------------------------------------ budget
;;;; BUDGET NIL: unlimited. A non-negative integer: with BUDGET-UNIT
;;;; :DECISIONS (the protocol's unit), at 4c, while the call's decisions so
;;;; far >= BUDGET, (setf budget (signal-budget-exceeded budget)); with
;;;; :CONFLICTS, at 2 (a conflict above level 0, before its analysis), while
;;;; the call's learnt clauses so far >= BUDGET, the same. The statistics are
;;;; current at the signal. CONTINUE and STORE-VALUE resume the search where
;;;; it stopped: a call whose handler always continues makes exactly the
;;;; decisions, hook calls, answer and statistics of the same call without a
;;;; budget. USE-VALUE throws to the front end. Under MINIMIZE's meter
;;;; (sat-protocol's minimize.lisp: :BUDGET 0, STORE-VALUE budget+1 per
;;;; signal), a :CONFLICTS backend's MINIMIZE :BUDGET counts conflicts; the
;;;; conformance suite runs with :DECISIONS.
;;;;
;;;; ---------------------------------------------------------------- restarts
;;;; Checked at 3 after every learnt clause; a restart backtracks to level 0
;;;; (phases saved as at 3) and keeps learnt clauses, activities and phases.
;;;; One :RESTARTS each. RESTART-POLICY:
;;;;   :LUBY     run k (k = 1, 2, ...) ends once LUBY-UNIT * luby(k) clauses
;;;;             have been learnt in it; luby = 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
;;;;             So with S(r) = LUBY-UNIT * (luby(1) + ... + luby(r)), a call
;;;;             with L learnt clauses has made R restarts, S(R) <= L < S(R+1).
;;;;   :GLUCOSE  keep the LBDs of the last RESTART-WINDOW clauses learnt in this
;;;;             run; restart when the window is full and
;;;;             RESTART-MARGIN * (window mean) > (mean LBD of every clause
;;;;             learnt in this call). The window starts empty in every run, so
;;;;             R <= floor(L / RESTART-WINDOW).
;;;;   NIL       never.
;;;;
;;;; --------------------------------------------------------------- reduction
;;;; REDUCE-BASE NIL: never. Otherwise the k-th reduction (k = 1, 2, ...) is
;;;; due at 3 once the call has learnt R_k clauses,
;;;;   R_k = k * REDUCE-BASE + REDUCE-INCREMENT * k * (k - 1) / 2,
;;;; so a call with L learnt clauses made exactly #{k : R_k <= L} reductions.
;;;; A reduction deletes from the learnt database the worse half (floor n/2)
;;;; of its n deletable clauses: those whose LBD (at learning) is above 2 and
;;;; that are not the reason of an assigned literal. Worse: higher LBD, then
;;;; lower clause activity, then older. One :REDUCTIONS per reduction and one
;;;; :DELETED-CLAUSES per clause deleted. The database stays bounded by the
;;;; schedule: about half of what was learnt since the previous reduction,
;;;; plus glue (LBD <= 2) and locked clauses.
;;;;
;;;; ---------------------------------------------------------- final conflict
;;;; (backend-final-conflict backend cnf assumptions &key budget order phase)
;;;; runs exactly the search of BACKEND-SOLVE (same rules, hooks, budget and
;;;; statistics). SAT -> (values NIL NIL LITERALS), LITERALS as BACKEND-SOLVE's.
;;;; UNSAT -> (values CORE T), CORE as MiniSat's analyzeFinal:
;;;;   - a conflict at level 0 (the CNF alone is refuted): CORE = NIL;
;;;;   - an assumption A false at its turn (4a): S = {A} plus every
;;;;     assumption reached from -A through reasons: mark -A's variable; walk
;;;;     the trail from the newest literal down to level 1; at a marked
;;;;     variable with a reason, mark that reason's other variables above
;;;;     level 0; at a marked variable without one (an assumption), put its
;;;;     literal in S. A false at level 0 gives S = {A}.
;;;;   CORE = the elements of ASSUMPTIONS that are in S, in the given order,
;;;;   each once (the first occurrence). CNF plus CORE is unsatisfiable. An
;;;;   assumption over a variable of no clause is in CORE only when it
;;;;   contradicts another assumption (A and -A: both, in the given order).
;;;; BACKEND-SOLVE under assumptions answers UNSAT the same way, without the
;;;; core. BACKEND-SOLVE-ALL, BACKEND-MINIMIZE (every strategy, :CORE-GUIDED
;;;; through this method) and BACKEND-UNSAT-CORE keep sat-protocol's default
;;;; methods.
;;;;
;;;; -------------------------------------------------------------- statistics
;;;; Per call, from 0 (keys in backend.lisp): :DECISIONS (4d), :PROPAGATIONS
;;;; (1 and 3), :CONFLICTS (1, the final level-0 conflict included),
;;;; :LEARNT-CLAUSES (2; so :CONFLICTS - :LEARNT-CLAUSES is 1 when a level-0
;;;; conflict ended the call, else 0), :BACKJUMPS (3), :RESTARTS, :REDUCTIONS
;;;; and :DELETED-CLAUSES.

(in-package #:sat-backend-cdcl)

(defun %l2b3-pending (name)
  (error "sat-backend-cdcl L2b-3 pending: ~A" name))

(defmethod backend-solve ((backend cdcl-backend) cnf &key assumptions order phase budget)
  "CDCL search of CNF under ASSUMPTIONS: the loop in this file's header."
  (declare (ignore cnf assumptions order phase budget))
  (%l2b3-pending 'backend-solve))

(defmethod backend-final-conflict ((backend cdcl-backend) cnf assumptions
                                   &key budget order phase)
  "BACKEND-SOLVE's search; on UNSAT, the assumptions of the final conflict
(header: FINAL CONFLICT)."
  (declare (ignore cnf assumptions budget order phase))
  (%l2b3-pending 'backend-final-conflict))
