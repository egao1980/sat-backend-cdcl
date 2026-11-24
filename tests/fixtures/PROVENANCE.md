# Test data provenance

There are no instance files. Every instance is generated from a fixed seed by
sat-protocol/conformance's 31-bit LCG (`make-rng`, `rng-int`), so it is the
same on every Lisp implementation:

| Generator | Defined in | Shape |
|---|---|---|
| `random-3sat`, `random-3sat-batch` | sat-protocol/conformance, `tests/instances.lisp` | uniform random 3-SAT |
| `planted-3sat` | `tests/instances.lisp` | random 3-clauses kept when a planted assignment satisfies them |
| `hidden-core-instance` | `tests/instances.lisp` | planted 3-SAT noise, then PHP(p, h) on fresh variables (UNSAT) |
| `make-chain-instance`, `chain-family` | `tests/instances.lisp` | weighted chain labelling: one-hot options per position, adjacent no-goods, transition and unary costs |
| `pigeonhole` | sat-protocol/conformance | PHP(p, h) |

## Recorded data

One table is recorded rather than computed: `*gate-3sat-status*` in
`tests/performance-test.lisp`. It holds the status of each instance of the
3-SAT gate batch (`random-3sat-batch 4260 20 150 639`). The instances are too
large for brute force and too slow for the test-time DPLL oracle to be
useful, and the gate must reject a backend that answers fast and wrong.

The statuses come from MiniSat 2.2 and Glucose 4, through python-sat
(`uv run --with python-sat python tests/fixtures/record-status.py`). The two
solvers agree on every instance. `record-status.py` ports the generators
draw for draw. Its batch fingerprint (the sum over instances, clauses and
positions k of k × literal) is **-9401**, the same as the Lisp batch's.

Everything else is checked against an oracle at test time:

- brute force over every assignment (sat-protocol/conformance) up to 15 variables;
- sat-backend-dpll for statuses and cores at 50 and 75 variables;
- the dynamic programme `chain-instance-optimum` for chain optima, itself
  checked against enumeration and against brute force over the encoded CNF.

## Reference timings (calibration, 2026-11-24)

These were measured on an Apple M4 laptop with SBCL 2.6.9, sat-protocol 0.2.0
and sat-backend-dpll 0.1.0, for the bounds in `tests/performance-test.lisp`.
The script prints the MiniSat, Glucose and RC2 numbers. The DPLL numbers come
from `(performance-baseline (make-instance 'sat-backend-dpll:dpll-backend) :cap 60)`.
The header of `performance-test.lisp` has the table and the reasoning.
