# sat-backend-cdcl

A [sat-protocol](https://github.com/egao1980/sat-protocol) backend: conflict-driven clause learning in the MiniSat / Glucose style. It has:

- two watched literals;
- first-UIP learning with clause minimisation;
- EVSIDS with phase saving;
- Luby or Glucose restarts;
- LBD-based learnt-clause reduction;
- assumption-based final-conflict cores for `backend-final-conflict`.

Pure Lisp, no dependencies beyond sat-protocol 0.2.

**Status:** contract for slice L2b-3 of Track L, 0.1.0. Brief: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md#l2b-3--sat-backend-cdcl-010-planned-cl-stack370). Motivation: proving optimality on weighted sequence-labelling / chain selection problems, where chronological DPLL finds good models but cannot prove the optimum ([cl-stack#370](https://github.com/egao1980/cl-stack/issues/370)).

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

## Tests

`cl-repo test` runs sat-protocol's conformance suite twice, once with the default parameters and once with stress parameters. Then it runs the CDCL tests:

- the parameters;
- decision order, phase saving and the `:order` / `:phase` hooks;
- budgets in decisions and in conflicts, with resumption;
- learnt clauses checked against brute force;
- the restart, reduction and backjump invariants;
- exact and random final-conflict cores;
- statuses against sat-backend-dpll.

Four performance gates follow, with the calibration in [tests/performance-test.lisp](tests/performance-test.lisp) and [tests/fixtures/PROVENANCE.md](tests/fixtures/PROVENANCE.md). Two of them are random 3-SAT and pigeonhole. The other two are instances DPLL cannot finish: a hidden unsatisfiable core, and weighted chains solved to proven optimality with `minimize :strategy :core-guided`.

## License

MIT, see [LICENSE](LICENSE).
