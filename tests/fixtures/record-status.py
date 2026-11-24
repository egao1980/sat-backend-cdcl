"""Recorded statuses and reference timings for sat-backend-cdcl's tests.

Run from the repo root: uv run --with python-sat python tests/fixtures/record-status.py

Ports of the Lisp generators, draw for draw: sat-protocol/conformance's
MAKE-RNG / RNG-INT (31-bit LCG) and RANDOM-3SAT, and tests/instances.lisp's
PLANTED-3SAT, HIDDEN-CORE-INSTANCE, MAKE-CHAIN-INSTANCE / CHAIN-FAMILY and
the chain encoding. A seed gives the same instances as the Lisp tests; the
3-SAT fingerprint printed first must match PROVENANCE.md. Prints the statuses
recorded in tests/performance-test.lisp and the MiniSat 2.2 / Glucose 4 /
RC2 times quoted there (see PROVENANCE.md).
"""

import sys
import time

from pysat.solvers import Glucose4, Minisat22


class Rng:
    def __init__(self, seed):
        self.state = seed % 2147483648

    def int(self, n):
        self.state = (1103515245 * self.state + 12345) % 2147483648
        return (self.state >> 8) % n


def random_3sat(rng, nvars, nclauses):
    clauses = []
    for _ in range(nclauses):
        variables = []
        while len(variables) < 3:
            v = 1 + rng.int(nvars)
            if v not in variables:
                variables.insert(0, v)  # PUSHNEW prepends
        clauses.append([v if rng.int(2) == 0 else -v for v in variables])
    return clauses


def planted_3sat(rng, nvars, nclauses):
    planted = [None] + [rng.int(2) == 0 for _ in range(nvars)]
    clauses = []
    while len(clauses) < nclauses:
        c = random_3sat(rng, nvars, 1)[0]
        if any(planted[l] if l > 0 else not planted[-l] for l in c):
            clauses.append(c)
    return clauses


def pigeonhole(pigeons, holes):
    v = lambda i, j: (i - 1) * holes + j
    clauses = [[v(i, j) for j in range(1, holes + 1)] for i in range(1, pigeons + 1)]
    for j in range(1, holes + 1):
        for i in range(1, pigeons + 1):
            for k in range(i + 1, pigeons + 1):
                clauses.append([-v(i, j), -v(k, j)])
    return clauses


def hidden_core(rng, noise_vars, noise_clauses, pigeons, holes):
    noise = planted_3sat(rng, noise_vars, noise_clauses)
    core = [
        [l + noise_vars if l > 0 else l - noise_vars for l in c]
        for c in pigeonhole(pigeons, holes)
    ]
    return noise + core


def chain_instance(
    rng,
    positions=8,
    min_options=2,
    max_options=6,
    nogood_percent=20,
    cost_percent=70,
    max_cost=4,
    unary_percent=30,
):
    """Port of MAKE-CHAIN-INSTANCE (tests/instances.lisp): same draws, same order."""
    options = [
        min_options + rng.int(max_options - min_options + 1) for _ in range(positions)
    ]
    unary = []
    for k in options:
        row = []
        for _ in range(k):
            row.append(1 + rng.int(max_cost) if rng.int(100) < unary_percent else 0)
        unary.append(row)
    transition = []
    for p in range(positions - 1):
        a = []
        for _ in range(options[p]):
            row = []
            for _ in range(options[p + 1]):
                if rng.int(100) < nogood_percent:
                    row.append(None)  # no-good
                elif rng.int(100) < cost_percent:
                    row.append(1 + rng.int(max_cost))
                else:
                    row.append(0)
            a.append(row)
        transition.append(a)
    return options, unary, transition


def chain_optimum(inst):
    options, unary, transition = inst
    best = list(unary[0])
    for p in range(1, len(options)):
        nxt = [None] * options[p]
        for m in range(options[p]):
            for l, b in enumerate(best):
                c = transition[p - 1][l][m]
                if b is not None and c is not None:
                    total = b + c + unary[p][m]
                    if nxt[m] is None or total < nxt[m]:
                        nxt[m] = total
        best = nxt
    finals = [b for b in best if b is not None]
    return min(finals) if finals else None


def chain_family(seed, count, **keys):
    rng = Rng(seed)
    out = []
    while len(out) < count:
        inst = chain_instance(rng, **keys)
        if chain_optimum(inst) is not None:
            out.append(inst)
    return out


def chain_wcnf(inst):
    """CHAIN-INSTANCE-CNF's encoding as hard clauses plus (weight, literal) costs."""
    options, unary, transition = inst
    index = {}

    def var(key):
        if key not in index:
            index[key] = len(index) + 1
        return index[key]

    for p, k in enumerate(options):
        for l in range(k):
            var(("x", p, l))
    hard, soft = [], []
    for p, k in enumerate(options):
        xs = [var(("x", p, l)) for l in range(k)]
        hard.append(xs)
        for i, a in enumerate(xs):
            for b in xs[i + 1 :]:
                hard.append([-a, -b])
        for l, c in enumerate(unary[p]):
            if c > 0:
                soft.append((c, var(("x", p, l))))
    for p, a in enumerate(transition):
        for l, row in enumerate(a):
            for m, c in enumerate(row):
                if c is None:
                    hard.append([-var(("x", p, l)), -var(("x", p + 1, m))])
                elif c > 0:
                    y = var(("y", p, l, m))
                    hard.append([-var(("x", p, l)), -var(("x", p + 1, m)), y])
                    soft.append((c, y))
    return hard, soft


def rc2_times(name, seed, count, **keys):
    """RC2 (core-guided MaxSAT on incremental Glucose 4) on a chain family; the
    optima must equal the DP oracle's."""
    from pysat.examples.rc2 import RC2
    from pysat.formula import WCNF

    total = 0.0
    for i, inst in enumerate(chain_family(seed, count, **keys)):
        hard, soft = chain_wcnf(inst)
        w = WCNF()
        for c in hard:
            w.append(c)
        for weight, lit in soft:
            w.append([-lit], weight=weight)
        start = time.perf_counter()
        with RC2(w) as rc2:
            rc2.compute()
            cost = rc2.cost
        elapsed = time.perf_counter() - start
        total += elapsed
        assert cost == chain_optimum(inst), (name, i, cost, chain_optimum(inst))
        print(f"  {name} {i}: optimum {cost}, {len(soft)} soft, RC2 {elapsed:.3f} s")
    print(f"{name}: RC2 (Glucose 4) {total:.3f} s in total")


def batch(seed, count, nvars, nclauses):
    rng = Rng(seed)
    return [random_3sat(rng, nvars, nclauses) for _ in range(count)]


def fingerprint(instances):
    return sum(
        k * lit for inst in instances for c in inst for k, lit in enumerate(c, 1)
    )


def statuses(name, seed, count, nvars, nclauses):
    instances = batch(seed, count, nvars, nclauses)
    result = []
    times = {"minisat22": 0.0, "glucose4": 0.0}
    for inst in instances:
        answers = []
        for label, solver in (("minisat22", Minisat22), ("glucose4", Glucose4)):
            with solver(bootstrap_with=inst) as s:
                start = time.perf_counter()
                answers.append(s.solve())
                times[label] += time.perf_counter() - start
        assert answers[0] == answers[1], (name, answers)
        result.append(answers[0])
    print(
        f"{name}: seed {seed}, {count} x {nvars} vars / {nclauses} clauses, "
        f"fingerprint {fingerprint(instances)}"
    )
    print(
        "  statuses (t = SAT):",
        "(" + " ".join("t" if s else "nil" for s in result) + ")",
    )
    print(
        f"  SAT {sum(result)} / {count}; MiniSat 2.2 {times['minisat22']:.3f} s, "
        f"Glucose 4 {times['glucose4']:.3f} s in total"
    )
    return result


def solver_times(name, instances):
    """Status (must be UNSAT for these) and MiniSat / Glucose times."""
    times = {"minisat22": 0.0, "glucose4": 0.0}
    for inst in instances:
        for label, solver in (("minisat22", Minisat22), ("glucose4", Glucose4)):
            with solver(bootstrap_with=inst) as s:
                start = time.perf_counter()
                assert s.solve() is False, (name, label)
                times[label] += time.perf_counter() - start
    print(
        f"{name}: UNSAT; MiniSat 2.2 {times['minisat22']:.4f} s, "
        f"Glucose 4 {times['glucose4']:.4f} s in total"
    )


class _Work:
    """A CNF that grows, solved from scratch on every call (as sat-protocol
    0.2's strategies call a backend: no incremental session yet)."""

    def __init__(self, hard):
        self.clauses = [list(c) for c in hard]
        self.top = max(abs(lit) for c in hard for lit in c)
        self.calls = 0
        self.seconds = 0.0

    def final_conflict(self, assumptions):
        self.calls += 1
        start = time.perf_counter()
        with Minisat22(bootstrap_with=self.clauses) as s:
            core = None if s.solve(assumptions=assumptions) else (s.get_core() or [])
        self.seconds += time.perf_counter() - start
        return core  # None: satisfiable

    def totalizer(self, lits):
        """Outputs o_1..o_n, o_j forced true when at least j of LITS are."""

        def build(ls):
            if len(ls) == 1:
                return [ls[0]]
            a, b = build(ls[: len(ls) // 2]), build(ls[len(ls) // 2 :])
            out = []
            for _ in range(len(a) + len(b)):
                self.top += 1
                out.append(self.top)
            for i in range(len(a) + 1):
                for j in range(len(b) + 1):
                    if i + j:
                        c = [out[i + j - 1]]
                        if i:
                            c.append(-a[i - 1])
                        if j:
                            c.append(-b[j - 1])
                        self.clauses.append(c)
            return out

        return build(lits)


def core_guided_calls(hard, soft, optimum):
    """sat-protocol 0.2's :CORE-GUIDED call pattern (OLL; each core shrunk by
    deletion through final conflicts; unit totalizers), stopped at OPTIMUM.
    Returns (calls, solver seconds)."""
    w = _Work(hard)
    weight, live, nxt, lower = {}, [], {}, 0

    def expose(lit, x):
        if lit not in weight:
            live.append(lit)
        weight[lit] = weight.get(lit, 0) + x

    for x, lit in soft:
        expose(lit, x)
    while lower < optimum:
        assume = [-lit for lit in live if weight[lit] > 0]
        core = w.final_conflict(assume)
        if core is None:
            break
        kept, rest = [], [a for a in assume if a in set(core)]
        while rest:
            e = rest.pop(0)
            if not kept and not rest:
                kept.append(e)
            else:
                c2 = w.final_conflict(kept + rest)
                if c2 is None:
                    kept.append(e)
                else:
                    rest = [x for x in rest if x in set(c2)]
        softs = [-a for a in kept]
        wmin = min(weight[lit] for lit in softs)
        lower += wmin
        for lit in softs:
            weight[lit] -= wmin
            if lit in nxt:
                outs, wt = nxt.pop(lit)
                if outs:
                    expose(outs[0], wt)
                    nxt[outs[0]] = (outs[1:], wt)
        if len(softs) > 1 and lower < optimum:
            outs = w.totalizer(softs)
            expose(outs[1], wmin)
            nxt[outs[1]] = (outs[2:], wmin)
    return w.calls, w.seconds


def emulated_core_guided(name, seed, count, **keys):
    calls = seconds = 0
    for inst in chain_family(seed, count, **keys):
        hard, soft = chain_wcnf(inst)
        c, s = core_guided_calls(hard, soft, chain_optimum(inst))
        calls += c
        seconds += s
    print(
        f"{name}: :core-guided call pattern on from-scratch MiniSat 2.2: "
        f"{calls} calls, {seconds:.3f} s in total"
    )


# *GATE-CHAINS* in tests/performance-test.lisp, without :SECONDS.
GATE_CHAINS = {
    "seed": 3702,
    "count": 6,
    "positions": 12,
    "min_options": 4,
    "max_options": 8,
    "cost_percent": 85,
}


if __name__ == "__main__":
    # Recorded in tests/performance-test.lisp (*GATE-3SAT-STATUS*).
    statuses("gate-3sat", 4260, 20, 150, 639)
    # Reference timings for the other gates (no recorded data: UNSAT by
    # construction, optima from the DP oracle).
    solver_times("gate-php 8-7", [pigeonhole(8, 7)])
    rng = Rng(7700)
    solver_times(
        "gate-hidden-core", [hidden_core(rng, 200, 840, 6, 5) for _ in range(4)]
    )
    rc2_times("gate-chains", **GATE_CHAINS)
    emulated_core_guided("gate-chains", **GATE_CHAINS)
    sys.exit(0)
