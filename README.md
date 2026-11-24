# sat-backend-cdcl

A [sat-protocol](https://github.com/egao1980/sat-protocol) backend: conflict-driven clause learning in the MiniSat / Glucose style. It has:

- two watched literals;
- first-UIP learning with clause minimisation;
- EVSIDS with phase saving;
- Luby or Glucose restarts;
- LBD-based learnt-clause reduction;
- assumption-based final-conflict cores for `backend-final-conflict`;
- 0.2.0: native incremental sessions (sat-protocol 0.3), one persistent solver per session.

Pure Lisp, no dependencies beyond sat-protocol (0.3.0 from version 0.2.0 on; it resolves once sat-protocol 0.3.0 is published).

**Status:** 0.1.0 (slice L2b-3 of Track L); **0.2.0 implemented** (slice L2b-2: native incremental sessions). Brief: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md#l2b-3--sat-backend-cdcl-010-planned-cl-stack370). Motivation: proving optimality on weighted sequence-labelling / chain selection problems, where chronological DPLL finds good models but cannot prove the optimum ([cl-stack#370](https://github.com/egao1980/cl-stack/issues/370)).

## Use

Loading `sat-backend-cdcl` makes a `cdcl-backend` the default `sat-protocol:*sat-backend*` when none is set. Every sat-protocol front end works on it: `solve`, `solve-all`, `minimize` with each strategy, and `unsat-core`. `:core-guided` and `unsat-core :minimal nil` get small final-conflict cores.

```lisp
(make-instance 'sat-backend-cdcl:cdcl-backend
               :restart-policy :glucose      ; :luby (default) | :glucose | nil
               :clause-minimization :recursive
               :reduce-base 2000 :reduce-increment 300
               :budget-unit :decisions       ; or :conflicts
               :learnt-hook (lambda (literals lbd) ...))
```

`cdcl-backend-statistics` returns a plist of the last call's counters: `:decisions`, `:propagations`, `:conflicts`, `:learnt-clauses`, `:backjumps`, `:restarts`, `:reductions` and `:deleted-clauses`. The search rules, parameters and counters are specified in [src/search.lisp](src/search.lisp) and [src/backend.lisp](src/backend.lisp).

## Sessions

`(make-sat-session :backend (make-instance 'cdcl-backend))` opens a stateful session: the clauses, the learnt clauses, level-0 facts, activities and saved phases persist from one call to the next, and only the assumptions, hooks, budget, restart run and statistics are per call. New clauses join at level 0 without reloading anything. `session-minimize` runs sat-protocol's strategies through the same solver, so what one bound learns serves the next. The rules are in [src/session.lisp](src/session.lisp).

## Tests

`cl-repo test` runs sat-protocol's conformance suite twice, once with the default parameters and once with stress parameters. Then it runs the CDCL tests:

- the parameters;
- decision order, phase saving and the `:order` / `:phase` hooks;
- budgets in decisions and in conflicts, with resumption;
- learnt clauses checked against brute force;
- the restart, reduction and backjump invariants;
- exact and random final-conflict cores;
- statuses against sat-backend-dpll.

Then the session tests: no session operation calls the from-scratch GFs, learnt clauses survive between calls, per-call statistics and budgets, clauses added at level 0, calls cut short, determinism, and every configuration against sat-backend-dpll. A soft benchmark reports a 50-segment chain solved incrementally against fresh solving, without a time gate.

Four performance gates follow, with the calibration in [tests/performance-test.lisp](tests/performance-test.lisp) and [tests/fixtures/PROVENANCE.md](tests/fixtures/PROVENANCE.md). Two of them are random 3-SAT and pigeonhole. The other two are instances DPLL cannot finish: a hidden unsatisfiable core, and weighted chains solved to proven optimality with `minimize :strategy :core-guided`.

## License

MIT, see [LICENSE](LICENSE).
