"""Differential test of the few-ancilla MCZ (report §3.1.4 Table 3.3, §6.1.4, §6.2, §8.2;
CLAUDE.md rule 9; Stage 12b decision 3). Stage 12b: the circuits were unproved and this harness
was the only evidence of their correctness (DECISIONS.md 2026-10-26, Stage 12b); since Stage 12c /
12d the restoration of `few:log` is proved in Lean and certified per instance, and this harness
is the independent check (CLAUDE.md rule 9).

  (0) gadgets — Maslov's relative-phase Toffoli (`MczFew.rtof`, the 9-gate list below) equals
      D . Toffoli with D diagonal and D != I (the relative phase is real, so the compute /
      uncompute cancellation matters); the 7-T Toffoli of the negative control is exact;
  (a) diffusion — `cqr synthesize --diffusion n --shape few:<v> --json` for n = 1..10 and both
      variants: for a random complex |psi> on the n data qubits, **every measurement branch**
      must end in (2|s><s| - I)|psi> (x) |0...0> up to a global phase (so the data register is
      exact and the ancillae are back in |0>; `alloc`/`free` assert |0> in every branch); the
      output must carry the variant's `status` label (STATUS, Stage 12d); a <= 2;
  (n) negative controls — (i) the D_8 diffusion of each variant with the *uncompute* copy of one
      relative-phase Toffoli replaced by an exact Toffoli (the relative phase D is then not
      cancelled: only correct up to a phase on part of the state) must be rejected; (ii) with
      one T of a compute copy turned into T-dagger must be rejected;
  (b) one Grover iteration of grover_pred_037 with each variant = U_s U_P, every branch;
  (c) the full Grover circuit of grover_pred_037 at r* = 2 with each variant: ancillae end in
      |0...0>, success probability exactly 121/128 (sampled branch, as grover_diff.py (c)).

Usage: python -I tests/diff/mcz_diff.py --cqr <path to cqr executable> [--seed S]
"""

import argparse
import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402
import benchmark_diff as alu  # noqa: E402
from grover_diff import (bits_of, check_all_branches, check_full, cqr_json,  # noqa: E402
                         u_s)

MAX_DATA = 10
VARIANTS = ["few:ladder", "few:log"]
# The `status` label of each variant in the CLI output (MczVariant.status, Stage 12d decision 5).
STATUS = {"few:ladder": "classical step checked at n = 8, restoration not certified",
          "few:log": "restoration proved (Stage 12c); certified per instance via `cqr certify --shape few:log` (Stage 12d)"}


def rtof(a, b, t):
    """Relative-phase Toffoli with the counts of Maslov 2016 Fig. 3 (dashed); the Margolus-form
    gate list of `CQRV.Synthesis.MczFew.rtof` (the figure is not legible in the text extraction)."""
    seq = [("h", t), ("t", t), ("cnot", b, t), ("tdg", t), ("cnot", a, t), ("t", t),
           ("cnot", b, t), ("tdg", t), ("h", t)]
    return [{"op": g[0], "q": list(g[1:])} for g in seq]


def toffoli(a, b, t):
    """The standard 7-T Toffoli (Nielsen-Chuang Fig. 4.9)."""
    seq = [("h", t), ("cnot", b, t), ("tdg", t), ("cnot", a, t), ("t", t), ("cnot", b, t),
           ("tdg", t), ("cnot", a, t), ("t", b), ("t", t), ("h", t), ("cnot", a, b), ("t", a),
           ("tdg", b), ("cnot", a, b)]
    return [{"op": g[0], "q": list(g[1:])} for g in seq]


def unitary3(gates):
    """The 8 x 8 unitary of a gate list on qubits 0, 1, 2 (qubit 0 = MSB)."""
    cols = []
    for k in range(8):
        s = sv.StateVector(3)
        s.amp = np.zeros(8, dtype=complex)
        s.amp[k] = 1
        for g in gates:
            sv.apply_unitary(s, g)
        cols.append(s.amp)
    return np.array(cols).T


def check_gadgets():
    tof = np.eye(8, dtype=complex)
    tof[[6, 7]] = tof[[7, 6]]
    u = unitary3(toffoli(0, 1, 2))
    assert np.allclose(u, tof), "the 7-T Toffoli is not a Toffoli"
    r = unitary3(rtof(0, 1, 2))
    d = r @ tof  # r = D . Toffoli  <=>  D = r . Toffoli (Toffoli is an involution)
    assert np.allclose(d, np.diag(np.diag(d))), "rtof is not D . Toffoli with D diagonal"
    assert np.allclose(np.abs(np.diag(d)), 1)
    assert not np.allclose(d, np.eye(8)), "rtof has no relative phase"
    assert np.allclose(r @ r, np.eye(8)), "rtof is not self-inverse"
    phases = [complex(round(z.real, 9), round(z.imag, 9)) for z in np.diag(d)]
    print(f"(0) rtof = D . Toffoli, D = diag{tuple(phases)}, rtof^2 = I; "
          f"7-T Toffoli exact")


def find_blocks(gates, pattern_of):
    """Start indices of 9-gate rtof blocks in `gates` (any qubits)."""
    out = []
    for i in range(len(gates) - 8):
        g = gates[i]
        if g["op"] != "h" or "if" in g:
            continue
        nxt = gates[i + 2]
        if nxt["op"] != "cnot" or "if" in nxt:
            continue
        b, t = nxt["q"]
        a = gates[i + 4]["q"][0] if gates[i + 4]["op"] == "cnot" else None
        if a is not None and gates[i:i + 9] == pattern_of(a, b, t):
            out.append((i, a, b, t))
    return out


def rejected(circ, n, rng):
    psi = sv._random_state(n, rng)
    try:
        check_all_branches(circ, psi, u_s(n) @ psi)
        return False
    except (AssertionError, sv.RestorationError):
        return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261026)
    args = ap.parse_args()
    cqr = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    rng = np.random.default_rng(args.seed)
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ok = True

    check_gadgets()

    # (a) diffusion with each few-ancilla MCZ, n = 1..10, every branch.
    passed, branches, total = 0, 0, 0
    for v in VARIANTS:
        for n in range(1, MAX_DATA + 1):
            total += 1
            try:
                res = cqr_json(cqr, ["--diffusion", str(n), "--shape", v])
                assert res["shape"] == v, res["shape"]
                assert res.get("status") == STATUS[v], res.get("status")
                circ = res["circuit"]
                assert circ["n_data"] == n, circ["n_data"]
                g = res["grade"]
                assert g["a"] <= 2, f"a = {g['a']} > 2"
                psi = sv._random_state(n, rng)
                b = check_all_branches(circ, psi, u_s(n) @ psi)
                passed += 1
                branches += b
                print(f"  diffusion n={n:2d} {v:10s} (w, d, t, a) = "
                      f"({g['w']}, {g['d']}, {g['t']}, {g['a']}), {b} branches")
            except (AssertionError, RuntimeError, sv.RestorationError) as e:
                ok = False
                print(f"FAIL (a) diffusion n={n} {v}: {e}")
    print(f"(a) diffusion: {passed}/{total} pass, {branches} measurement branches checked")

    # (n) negative controls on D_8.
    for v in VARIANTS:
        circ = cqr_json(cqr, ["--diffusion", "8", "--shape", v])["circuit"]
        gates = circ["gates"]
        blocks = find_blocks(gates, rtof)
        assert len(blocks) >= 2 and len(blocks) % 2 == 0, len(blocks)
        i, a, b, t = blocks[-1]  # the uncompute copy of the first rtof
        bad = {**circ, "gates": gates[:i] + toffoli(a, b, t) + gates[i + 9:]}
        if rejected(bad, 8, rng):
            print(f"(n) {v}: uncompute rtof -> exact Toffoli (relative phase not cancelled) "
                  f"rejected ({len(blocks)} rtof blocks)")
        else:
            ok = False
            print(f"FAIL (n) {v}: uncancelled relative phase accepted")
        j = blocks[0][0] + 1
        assert gates[j]["op"] == "t"
        bad = {**circ, "gates": gates[:j] + [{**gates[j], "op": "tdg"}] + gates[j + 1:]}
        if rejected(bad, 8, rng):
            print(f"(n) {v}: one T -> T-dagger in a compute rtof rejected")
        else:
            ok = False
            print(f"FAIL (n) {v}: corrupted rtof accepted")

    # (b) one Grover iteration of grover_pred_037, every branch; (c) full Grover r* = 2.
    n = 8
    pred = lambda x: x[0] and x[3] and x[7]  # noqa: E731
    grover = os.path.join(root, "examples", "grover_pred_037.cqr")
    signs = np.array([-1.0 if pred(bits_of(x, n)) else 1.0 for x in range(2**n)])
    exact_c = alu.grover_success(2, Fraction(32, 256))
    assert exact_c == Fraction(121, 128), exact_c
    for v in VARIANTS:
        try:
            res = cqr_json(cqr, [grover, "--grover", "--shape", v])
            assert res.get("status") == STATUS[v], res.get("status")
            psi = sv._random_state(n, rng)
            b = check_all_branches(res["iteration_circuit"], psi, u_s(n) @ (signs * psi))
            g = res["grades"]["iteration"]
            print(f"(b) Grover iteration U_s U_P (grover_pred_037, {v}): pass, {b} branches "
                  f"checked; grade ({g['w']}, {g['d']}, {g['t']}, {g['a']})")
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (b) Grover iteration ({v}): {e}")
        try:
            res = check_full(cqr, "(c) grover_pred_037", grover, [], n, pred, 2, exact_c, v, rng)
            assert res.get("status") == STATUS[v], res.get("status")
        except (AssertionError, RuntimeError, sv.RestorationError) as e:
            ok = False
            print(f"FAIL (c) full Grover ({v}): {e}")

    print(f"mcz_diff: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
