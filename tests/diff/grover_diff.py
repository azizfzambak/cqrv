"""Differential test of the diffusion and the Grover circuit (report §8.2, §3.2.4, §6.2.4;
CLAUDE.md rule 9; Stage 5b).

  (a) diffusion — `cqr synthesize --diffusion n --json [--amax k]` for n = 1..10 (V1) and
      Bennett budgets (V2): for a random complex |psi> on the n data qubits, **every
      measurement branch** must end in (2|s><s| - I)|psi> (x) |0...0> up to a global phase;
  (b) one Grover iteration of grover_pred_037 (`iteration_circuit` of
      `cqr synthesize <file> --grover --json`) = U_s U_P on a random |psi>, every branch;
  (c) the full Grover circuit for grover_pred_037 at r = r* = 2 from |0...0>: one branch,
      each measurement outcome sampled (restoration makes every branch identical, which (a)
      and (b) check); the success probability sum_{P(x)=1} |amp|^2 must equal
      sin^2((2r*+1) theta), sin^2 theta = 32/256, to 1e-9.

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

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402

MAX_DATA = 10
OVERLAP_TOL = 1e-9
PROB_TOL = 1e-9
# (n, k): V2 budgets that pebble (k below the n - 1 ANDs of the straight-line MCZ).
BENNETT = [(4, 2), (5, 3), (8, 3), (8, 4)]


def cqr_json(cqr, args):
    cmd = [cqr, "synthesize"] + args + ["--json"]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    line = out.stdout.strip().splitlines()[0] if out.stdout.strip() else ""
    if out.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} exited {out.returncode}: {line or out.stderr}")
    return json.loads(line)


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


def check_diffusion(cqr, n, amax, rng):
    res = cqr_json(cqr, ["--diffusion", str(n)] + (["--amax", str(amax)] if amax else []))
    circ = res["circuit"]
    assert circ["n_data"] == n, circ["n_data"]
    psi = sv._random_state(n, rng)
    return res, check_all_branches(circ, psi, u_s(n) @ psi)


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

    # (a) diffusion, V1 and V2, every branch.
    cases = [(n, None) for n in range(1, MAX_DATA + 1)] + BENNETT
    passed, branches = 0, 0
    for n, k in cases:
        try:
            res, b = check_diffusion(cqr, n, k, rng)
            passed += 1
            branches += b
            g = res["grade"]
            print(f"  diffusion n={n:2d} {res['schedule']:24s} (w, d, t, a) = "
                  f"({g['w']}, {g['d']}, {g['t']}, {g['a']}), {b} branches")
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (a) diffusion n={n} amax={k}: {e}")
    print(f"(a) diffusion: {passed}/{len(cases)} pass, {branches} measurement branches checked")
    # Negative control: the n = 3 diffusion without its final H on x[0] must be rejected.
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

    # (b) one Grover iteration of grover_pred_037 = U_s U_P, every branch.
    n = 8
    pred = lambda x: x[0] and x[3] and x[7]  # noqa: E731
    grover = os.path.join(root, "examples", "grover_pred_037.cqr")
    res = cqr_json(cqr, [grover, "--grover"])
    signs = np.array([-1.0 if pred(bits_of(x, n)) else 1.0 for x in range(2**n)])
    try:
        psi = sv._random_state(n, rng)
        b = check_all_branches(res["iteration_circuit"], psi, u_s(n) @ (signs * psi))
        print(f"(b) Grover iteration U_s U_P (grover_pred_037): pass, {b} branches checked")
    except (AssertionError, sv.RestorationError) as e:
        ok = False
        print(f"FAIL (b) Grover iteration: {e}")

    # (c) full Grover at r = r*, sampled branch, success probability.
    theta = math.asin(math.sqrt(32 / 256))
    r = res["r_star"]
    want = math.sin((2 * r + 1) * theta) ** 2
    try:
        assert r == 2 and res["iterations"] == 2, (r, res["iterations"])
        circ = res["circuit"]
        e0 = np.zeros(2**n, dtype=complex)
        e0[0] = 1
        bits, s = sv.run_ir_sampled(circ, e0, rng)
        data = s.amp.reshape(2**n, 2 ** circ["n_anc"])
        anc_rest = float(np.sum(np.abs(data[:, 1:]) ** 2))
        assert anc_rest < OVERLAP_TOL, f"ancilla not |0...0> (weight {anc_rest})"
        p = float(sum(abs(data[x, 0]) ** 2 for x in range(2**n) if pred(bits_of(x, n))))
        assert abs(p - want) <= PROB_TOL, f"success probability {p!r} != {want!r}"
        print(f"(c) full Grover r*={r}: success probability {p:.12f} = sin^2(5 theta) "
              f"{want:.12f} (|diff| = {abs(p - want):.2e}; sampled branch "
              f"{''.join(str(bits[c]) for c in sorted(bits))})")
    except (AssertionError, sv.RestorationError) as e:
        ok = False
        print(f"FAIL (c) full Grover: {e}")

    print(f"grover_diff: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
