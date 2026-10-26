"""Differential test of the diffusion and the Grover circuit (report §8.2, §3.2.4, §6.2.4;
CLAUDE.md rule 9; Stage 5b; Stage 12a: both diffusion shapes).

  (a) diffusion — `cqr synthesize --diffusion n --json [--shape chain] [--amax k]` for n = 1..10,
      V1 with the balanced-tree MCZ (default, Stage 12a) and with the chain MCZ, and Bennett
      budgets (V2, chain only): for a random complex |psi> on the n data qubits, **every
      measurement branch** must end in (2|s><s| - I)|psi> (x) |0...0> up to a global phase;
  (b) one Grover iteration of grover_pred_037 (`iteration_circuit` of
      `cqr synthesize <file> --grover --json [--shape chain]`) = U_s U_P on a random |psi>,
      every branch, for both shapes;
  (c) the full Grover circuit for grover_pred_037 at r = r* = 2 from |0...0>, both shapes: one
      branch, each measurement outcome sampled (restoration makes every branch identical, which
      (a) and (b) check); the ancillae end in |0...0> and the success probability
      sum_{P(x)=1} |amp|^2 equals the exact rational sin^2(5 theta) = 121/128 (sin^2 theta =
      32/256; Chebyshev polynomial in Fraction arithmetic, as `CQRV.Certify.groverSuccess`)
      to 1e-9;
  (d) the same for the second predicate examples/simple_alu_x0_1.cqr (M = 30 from the SyReC
      reference of benchmark_diff.py, r* = 1): success probability exactly 1215/2048, both
      shapes. Every branch of the ALU circuit is checked by scripts/diff_benchmark.sh.

Branches are enumerated depth first (`statevector.iter_ir_branches`). P is evaluated here,
never taken from the synthesizer.

Usage: python -I tests/diff/grover_diff.py --cqr <path to cqr executable> [--seed S]
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
import benchmark_diff as alu  # noqa: E402

MAX_DATA = 10
OVERLAP_TOL = 1e-9
PROB_TOL = 1e-9
SHAPES = ["tree", "chain"]
# (n, k): V2 budgets that pebble (k below the n - 1 ANDs of the straight-line MCZ); chain only.
BENNETT = [(4, 2), (5, 3), (8, 3), (8, 4)]


def cqr_json(cqr, args):
    cmd = [cqr, "synthesize"] + args + ["--json"]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    line = out.stdout.strip().splitlines()[0] if out.stdout.strip() else ""
    if out.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} exited {out.returncode}: {line or out.stderr}")
    return json.loads(line)


def shape_args(shape):
    return ["--shape", shape]


def bits_of(x, n):
    """Data index -> input bits (qubit 0 = MSB = input bit 0)."""
    return [(x >> (n - 1 - k)) & 1 == 1 for k in range(n)]


def u_s(n):
    """2|s><s| - I on n qubits, |s> = H^n |0>."""
    N = 2**n
    return np.full((N, N), 2.0 / N, dtype=complex) - np.eye(N)


def check_all_branches(circ, psi, want_data):
    """Every branch ends in want_data (x) |0..0>_anc up to a phase; probabilities sum to 1.
    Returns the number of branches."""
    n_anc = circ["n_anc"]
    want = np.zeros(2 ** (circ["n_data"] + n_anc), dtype=complex)
    want[:: 2**n_anc] = want_data
    total, count = 0.0, 0
    for bits, s in sv.iter_ir_branches(circ, psi):
        nrm = s.norm2()
        total += nrm
        overlap = abs(np.vdot(want, s.amp)) / np.sqrt(nrm)
        if overlap < 1 - OVERLAP_TOL:
            raise AssertionError(f"branch {bits}: overlap {overlap:.12f} != 1")
        count += 1
    if abs(total - 1) > OVERLAP_TOL:
        raise AssertionError(f"branch probabilities sum to {total}")
    return count


def check_diffusion(cqr, n, shape, amax, rng):
    res = cqr_json(cqr, ["--diffusion", str(n)] + shape_args(shape)
                   + (["--amax", str(amax)] if amax else []))
    assert res["shape"] == shape, res["shape"]
    circ = res["circuit"]
    assert circ["n_data"] == n, circ["n_data"]
    psi = sv._random_state(n, rng)
    return res, check_all_branches(circ, psi, u_s(n) @ psi)


def success_sampled(circ, n, pred, rng):
    """Run from |0...0>, sample each measurement; ancillae must end in |0...0>; return the
    success probability and the sampled bits."""
    e0 = np.zeros(2**n, dtype=complex)
    e0[0] = 1
    bits, s = sv.run_ir_sampled(circ, e0, rng)
    data = s.amp.reshape(2**n, 2 ** circ["n_anc"])
    anc_rest = float(np.sum(np.abs(data[:, 1:]) ** 2))
    assert anc_rest < OVERLAP_TOL, f"ancilla not |0...0> (weight {anc_rest})"
    p = float(sum(abs(data[x, 0]) ** 2 for x in range(2**n) if pred(bits_of(x, n))))
    return p, bits


def check_full(cqr, label, src, extra, n, pred, r_want, exact, shape, rng):
    """(c)/(d): the full Grover circuit at r*; success probability = exact rational."""
    res = cqr_json(cqr, [src, "--grover"] + extra + shape_args(shape))
    assert res["shape"] == shape, res["shape"]
    r = res["r_star"]
    assert r == r_want and res["iterations"] == r_want, (r, res["iterations"])
    p, bits = success_sampled(res["circuit"], n, pred, rng)
    assert abs(p - float(exact)) <= PROB_TOL, f"success probability {p!r} != {exact} = {float(exact)!r}"
    g = res["grades"]["circuit"]
    print(f"  {label} {shape:5s} r*={r}: success probability {p:.12f} = {exact} "
          f"(|diff| = {abs(p - float(exact)):.2e}; grade ({g['w']}, {g['d']}, {g['t']}, {g['a']}); "
          f"sampled branch {''.join(str(bits[c]) for c in sorted(bits))})")
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261024)
    args = ap.parse_args()
    cqr = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    rng = np.random.default_rng(args.seed)
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ok = True

    # (a) diffusion, V1 (tree and chain) and V2 (chain), every branch.
    cases = ([(n, sh, None) for sh in SHAPES for n in range(1, MAX_DATA + 1)]
             + [(n, "chain", k) for n, k in BENNETT])
    passed, branches = 0, 0
    for n, sh, k in cases:
        try:
            res, b = check_diffusion(cqr, n, sh, k, rng)
            passed += 1
            branches += b
            g = res["grade"]
            print(f"  diffusion n={n:2d} {sh:5s} {res['schedule']:24s} (w, d, t, a) = "
                  f"({g['w']}, {g['d']}, {g['t']}, {g['a']}), {b} branches")
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (a) diffusion n={n} shape={sh} amax={k}: {e}")
    print(f"(a) diffusion: {passed}/{len(cases)} pass, {branches} measurement branches checked")
    # Negative control: the n = 3 diffusion (tree) without its final H on x[0] must be rejected.
    circ = cqr_json(cqr, ["--diffusion", "3"])["circuit"]
    bad = {**circ, "gates": circ["gates"][:-3] + circ["gates"][-2:]}
    assert circ["gates"][-3] == {"op": "h", "q": [0]}, circ["gates"][-3]
    psi = sv._random_state(3, rng)
    try:
        check_all_branches(bad, psi, u_s(3) @ psi)
        ok = False
        print("FAIL (a) negative control: a diffusion missing an H was accepted")
    except AssertionError:
        print("(a) negative control: diffusion missing an H rejected")

    # (b) one Grover iteration of grover_pred_037 = U_s U_P, every branch, both shapes.
    n = 8
    pred = lambda x: x[0] and x[3] and x[7]  # noqa: E731
    grover = os.path.join(root, "examples", "grover_pred_037.cqr")
    signs = np.array([-1.0 if pred(bits_of(x, n)) else 1.0 for x in range(2**n)])
    for sh in SHAPES:
        try:
            res = cqr_json(cqr, [grover, "--grover"] + shape_args(sh))
            psi = sv._random_state(n, rng)
            b = check_all_branches(res["iteration_circuit"], psi, u_s(n) @ (signs * psi))
            g = res["grades"]["iteration"]
            print(f"(b) Grover iteration U_s U_P (grover_pred_037, {sh}): pass, {b} branches "
                  f"checked; grade ({g['w']}, {g['d']}, {g['t']}, {g['a']})")
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (b) Grover iteration ({sh}): {e}")

    # (c) full Grover of grover_pred_037 at r* = 2: exactly 121/128.
    exact_c = alu.grover_success(2, Fraction(32, 256))
    assert exact_c == Fraction(121, 128), exact_c
    theta = math.asin(math.sqrt(32 / 256))
    assert abs(float(exact_c) - math.sin(5 * theta) ** 2) < 1e-15
    for sh in SHAPES:
        try:
            check_full(cqr, "(c) grover_pred_037", grover, [], n, pred, 2, exact_c, sh, rng)
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (c) full Grover ({sh}): {e}")

    # (d) full Grover of simple_alu_x0_1 at r* = 1 (M = 30 from the SyReC reference):
    # exactly 1215/2048.
    m_alu = sum(alu.reference(alu.input_bits(x)) for x in range(2**alu.N_IN))
    assert m_alu == 30, m_alu
    exact_d = alu.grover_success(1, Fraction(m_alu, 2**alu.N_IN))
    assert exact_d == Fraction(1215, 2048), exact_d
    pred_alu = lambda x: alu.reference([int(b) for b in x])  # noqa: E731
    for sh in SHAPES:
        try:
            check_full(cqr, "(d) simple_alu_x0_1", alu.SRC, ["--solutions", str(m_alu)],
                       alu.N_IN, pred_alu, 1, exact_d, sh, rng)
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (d) full Grover ALU ({sh}): {e}")

    print(f"grover_diff: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
