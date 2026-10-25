"""Second worked predicate: differential tests (report §8.5.3, Table 9.2; §6.2.4, §8.2;
CLAUDE.md rule 9; Stage 9b, reviewer decisions 2 and 3).

The predicate is examples/simple_alu_x0_1.cqr: bit 1 of x0 of the RevLib "Simple ALU" (SyReC
file simple_alu_234.src [WOD:2010]; DECISIONS.md 2026-10-25, Stage 9b decision 2). The reference
here is computed from the SyReC semantics by integer arithmetic, `[x1 + x2, x1 - x2, x1 * x2,
x1 ^ x2][op] mod 2^w`, bit 1, never from the DSL transcription or the synthesizer's network.

  (0) the reference: the cone claim (bit 1 reads only bits 0..1 of x1, x2; checked at w = 16 on
      random high bits), M by enumeration over the 64 inputs **as a test oracle only** (decision
      3: the certificate stays conditional on solution_count = M);
  (1) `cqr check` (exit 0), `cqr check --truth-table` (evaluator = network = reference),
      `cqr extract --solutions M` (ĉ∧, AND-depth, M), `cqr match --solutions M` (Grover,
      F₁ ↦ 6, F₂ ↦ M), `cqr synthesize` (grade) and `--layers` (the dump has d layers);
  (2) the oracle: in **every** measurement branch, on a random complex |psi>, the output is
      U_P|psi> (x) |0...0>_anc up to a global phase of the branch;
  (3) one Grover iteration = U_s U_P on a random |psi>, every branch;
  (4) the full Grover circuit at r = r* from |0...0>, **every** branch: the ancillae end in
      |0...0> and the success probability sum_{P(x)=1} |amp|^2 equals sin^2((2r*+1) theta),
      sin^2 theta = M/64, to 1e-9, and equals the exact rational 1 - delta (Chebyshev
      polynomial in s = M/N, Fraction arithmetic; the value the certificate states).

Usage: python -I tests/diff/benchmark_diff.py --cqr <path to cqr executable> [--seed S]
"""

import argparse
import json
import math
import os
import subprocess
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "examples", "simple_alu_x0_1.cqr")
N_IN = 6
TOL = 1e-9
# Measured values of this predicate (regression; any change must be explained in DECISIONS.md).
EXPECT_ORACLE = {"w": 16, "d": 80, "t": 40, "a": 10}
EXPECT_CIRCUIT = {"w": 16, "d": 145, "t": 60, "a": 10}


def alu_bit(op, x1, x2, w, k=1):
    """SyReC semantics of simple_alu_234.src: `x0 ^= e` on x0 = 0 (an `out` signal), modulo 2^w."""
    m = (1 << w) - 1
    val = [(x1 + x2) & m, (x1 - x2) & m, (x1 * x2) & m, (x1 ^ x2) & m][op]
    return (val >> k) & 1 == 1


def reference(bits):
    """bits[k] = input bit k: x[0] = op.0, x[1] = op.1, x[2..3] = x1.0..1, x[4..5] = x2.0..1."""
    op = bits[0] | bits[1] << 1
    x1 = bits[2] | bits[3] << 1
    x2 = bits[4] | bits[5] << 1
    return alu_bit(op, x1, x2, 2)


def input_bits(x, n=N_IN):
    """Truth-table index -> input bits (bit k of x = input bit k)."""
    return [(x >> k) & 1 for k in range(n)]


def data_bits(x, n=N_IN):
    """Data-register index -> input bits (qubit 0 = MSB = input bit 0; statevector.py)."""
    return [(x >> (n - 1 - k)) & 1 for k in range(n)]


def grover_success(r, s):
    """sin^2((2r+1) theta) for s = sin^2 theta, exactly: s * U_{2r}(cos theta)^2, U_k in
    Q[c]/(c^2 - (1 - s)) (as CQRV.Certify.groverSuccess)."""
    def times_2c(p):
        a, b = p
        return (2 * b * (1 - s), 2 * a)
    u, v = (Fraction(1), Fraction(0)), (Fraction(0), Fraction(2))
    for _ in range(2 * r):
        w = times_2c(v)
        u, v = v, (w[0] - u[0], w[1] - u[1])
    assert u[1] == 0
    return s * u[0] * u[0]


def cqr(exe, *args):
    p = subprocess.run([exe, *args], capture_output=True, text=True, encoding="utf-8")
    return p.returncode, p.stdout.replace("\r\n", "\n"), p.stderr


def cqr_json(exe, *args):
    rc, so, se = cqr(exe, *args)
    if rc != 0:
        raise AssertionError(f"cqr {' '.join(args)} exited {rc}: {so or se}")
    return json.loads(so)


def u_s(n):
    N = 2**n
    return np.full((N, N), 2.0 / N, dtype=complex) - np.eye(N)


def every_branch(circ, psi, want_data):
    """Every branch ends in want_data (x) |0..0>_anc up to a phase; probabilities sum to 1."""
    n_anc = circ["n_anc"]
    want = np.zeros(2 ** (circ["n_data"] + n_anc), dtype=complex)
    want[:: 2**n_anc] = want_data
    total, count = 0.0, 0
    for bits, s in sv.iter_ir_branches(circ, psi):
        nrm = s.norm2()
        total += nrm
        overlap = abs(np.vdot(want, s.amp)) / np.sqrt(nrm)
        assert overlap >= 1 - TOL, f"branch {bits}: overlap {overlap:.12f} != 1"
        count += 1
    assert abs(total - 1) <= TOL, f"branch probabilities sum to {total}"
    return count


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261025)
    args = ap.parse_args()
    exe = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    rng = np.random.default_rng(args.seed)
    n = N_IN

    # (0) reference, cone, M
    for _ in range(2000):
        op, x1, x2 = (int(v) for v in (rng.integers(4), rng.integers(1 << 16),
                                       rng.integers(1 << 16)))
        assert alu_bit(op, x1, x2, 16) == alu_bit(op, x1 & 3, x2 & 3, 2), (op, x1, x2)
    table = "".join("1" if reference(input_bits(x)) else "0" for x in range(2**n))
    M = table.count("1")
    assert M == 30, M
    print(f"(0) reference from the SyReC semantics; cone of x0.1 = 6 inputs (checked at w = 16 "
          f"on 2000 random operands); M = {M} by enumeration (test oracle only)")

    # (1) front end, ℰ, matcher, synthesizer
    rc, so, se = cqr(exe, "check", SRC)
    assert rc == 0 and so == "", (rc, so, se)
    tt = cqr_json(exe, "check", SRC, "--truth-table")
    assert tt["n"] == n and tt["evaluator"] == table and tt["network"] == table, tt
    sig = cqr_json(exe, "extract", SRC, "--solutions", str(M))
    assert (sig["and_complexity"], sig["and_depth"], sig["solution_count"], sig["arity"]) == \
        (10, 4, M, n), sig
    mt = cqr_json(exe, "match", SRC, "--solutions", str(M))
    assert mt["pattern"] == "Grover" and mt["subst"]["F₁"] == n and mt["subst"]["F₂"] == M, mt
    syn = cqr_json(exe, "synthesize", SRC)
    assert syn["grade"] == EXPECT_ORACLE and syn["and_complexity"] == 10, syn
    rc, so, se = cqr(exe, "synthesize", SRC, "--layers")
    layers = [ln for ln in so.split("\n") if ln.startswith("L")]
    assert rc == 0 and len(layers) == EXPECT_ORACLE["d"], (rc, len(layers))
    print(f"(1) check, truth table (evaluator = network = reference), extract (ĉ∧ 10, depth 4), "
          f"match (Grover, F₂ ↦ {M}), synthesize {syn['grade']}, {len(layers)} layers")

    ok = True
    # (2) oracle, every branch
    oracle = cqr_json(exe, "synthesize", SRC, "--json")["circuit"]
    signs = np.array([-1.0 if reference(data_bits(x)) else 1.0 for x in range(2**n)])
    try:
        psi = sv._random_state(n, rng)
        b = every_branch(oracle, psi, signs * psi)
        print(f"(2) oracle U_P: pass in every branch ({b} branches)")
    except (AssertionError, sv.RestorationError) as e:
        ok = False
        print(f"FAIL (2) oracle: {e}")

    # (3), (4) Grover iteration and full circuit
    res = cqr_json(exe, "synthesize", SRC, "--grover", "--solutions", str(M), "--json")
    r = res["r_star"]
    assert r == 1 and res["iterations"] == r, res
    assert res["grades"]["circuit"] == EXPECT_CIRCUIT, res["grades"]
    try:
        psi = sv._random_state(n, rng)
        b = every_branch(res["iteration_circuit"], psi, u_s(n) @ (signs * psi))
        print(f"(3) Grover iteration U_s U_P: pass in every branch ({b} branches)")
    except (AssertionError, sv.RestorationError) as e:
        ok = False
        print(f"FAIL (3) Grover iteration: {e}")

    s_exact = Fraction(M, 2**n)
    p_exact = grover_success(r, s_exact)
    delta = 1 - p_exact
    assert delta == Fraction(833, 2048), delta
    theta = math.asin(math.sqrt(M / 2**n))
    p_float = math.sin((2 * r + 1) * theta) ** 2
    assert abs(p_float - float(p_exact)) < 1e-15
    try:
        circ = res["circuit"]
        e0 = np.zeros(2**n, dtype=complex)
        e0[0] = 1
        good = [x for x in range(2**n) if reference(data_bits(x))]
        count, total, worst = 0, 0.0, 0.0
        for bits, s in sv.iter_ir_branches(circ, e0):
            nrm = s.norm2()
            total += nrm
            data = s.amp.reshape(2**n, 2 ** circ["n_anc"])
            anc_rest = float(np.sum(np.abs(data[:, 1:]) ** 2)) / nrm
            assert anc_rest < TOL, f"branch {bits}: ancilla not |0...0> (weight {anc_rest})"
            p = float(sum(abs(data[x, 0]) ** 2 for x in good)) / nrm
            worst = max(worst, abs(p - float(p_exact)))
            assert worst <= TOL, f"branch {bits}: success probability {p!r} != {p_exact}"
            count += 1
        assert abs(total - 1) <= TOL, f"branch probabilities sum to {total}"
        print(f"(4) full Grover r* = {r}: every branch ({count}) restores the ancillae; success "
              f"probability = sin^2(3 theta) = {p_exact} = {float(p_exact):.12f} exactly "
              f"(max |diff| over branches {worst:.2e}); delta = {delta}")
    except (AssertionError, sv.RestorationError) as e:
        ok = False
        print(f"FAIL (4) full Grover: {e}")

    print(f"benchmark_diff: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
