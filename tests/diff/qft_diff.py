"""Differential test of the QFT / approximate QFT circuits (PHASE2_SPEC.md §A.2; Stage 18b B4;
CLAUDE.md rule 9). `qft_basis` (CQRV/Circuit/QFTCorrect.lean) is proved; this harness is the
independent numerical check of the circuits the Lean side builds, and it checks the AQFT bounds
of Stage 18c numerically (`aqft_opNorm_le`, and the `eta_aqft` line of `aqft_diamond_le`; both
proved in Stage 18c, CQRV/Circuit/QFTCorrect.lean).

Convention — the harness's and `qft_basis`'s: **qubit 0 is the most significant bit** of the
basis index (statevector.py). For m qubits the DFT matrix is
    F[y, x] = 2^{-m/2} · exp(2πi · x · y / 2^m)            (x, y read with qubit 0 as the MSB)
and R is the bit-reversal permutation, R[y, x] = [y = bitrev_m(x)]. The simulated `qftCircuit m`
(the textbook circuit without the final swaps) must equal R · F, i.e. the amplitude of output
basis state s on input |x⟩ is 2^{-m/2} · exp(2πi · x · bitrev(s) / 2^m) — exactly `qft_basis`
(`(bitRev s).toNat = s.toNatLE`).

  (a) for m = 1..M: the simulated matrix U_qft (columns = `statevector.run_ir` on the 2^m basis
      states) equals R·F (max entry error < 1e-9), on random states as well, and is unitary;
  (b) `adjointGates (qftGates m)` (CertifyTool `--adjoint`) is the inverse: U_adj · U_qft = I;
  (c) for kmax = 1..m: the spectral norm ‖U_qft − U_aqft‖₂ (numpy.linalg.norm(·, 2)) is
      ≤ 2π m / 2^kmax (`aqft_opNorm_le`, PHASE2_SPEC §A.2) **and** ≤ Σ_dropped 2π / 2^k, the sum
      of the dropped angles (the telescoping bound of Stage 18c C1); kmax = m drops nothing
      (`aqftGates_eq_self`); kmax < m drops exactly the `cp` gates with k > kmax; and the
      eta_aqft line: 2 ‖U_qft − U_aqft‖₂ ≤ eta_aqft m kmax = 4π m / 2^kmax (`aqft_diamond_le`).
      A diamond distance is at most 2, so a pair (m, kmax) with eta_aqft ≥ 2 is a vacuous budget;
      a pair with eta_aqft < 2 and kmax < m (a gate dropped) is informative, marked and counted,
      and the final note reports the count: with 0 informative pairs the line is a consistency
      check in that range, not a test of the bound (18c notes (ii) of STAGE18_TASK.md);
  (d) negative control: the sign of one rotation flipped (a = 1 → −1 in `cp a k`) is detected
      against R·F (error > 0.1).

The circuits come from `lake env lean --run scripts/CertifyTool.lean qft-sample --all M` (one
Lean start). Usage: python -I tests/diff/qft_diff.py [--m-max 6] [--seed S]
"""

import argparse
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402
from lean_tool import certify_tool  # noqa: E402

EPS = 1e-9


def bitrev(x, m):
    return int(format(x, f"0{m}b")[::-1], 2) if m > 0 else 0


def dft_matrix(m):
    n = 2 ** m
    x = np.arange(n)
    return np.exp(2j * np.pi * np.outer(x, x) / n) / math.sqrt(n)  # F[y, x], symmetric


def bitrev_matrix(m):
    n = 2 ** m
    R = np.zeros((n, n))
    for x in range(n):
        R[bitrev(x, m), x] = 1.0
    return R


def simulate(circ):
    """The unitary of an ancilla-free unitary IR circuit, column x = run on basis state |x⟩."""
    assert circ["n_anc"] == 0
    n = 2 ** circ["n_data"]
    U = np.zeros((n, n), dtype=complex)
    for x in range(n):
        e = np.zeros(n, dtype=complex)
        e[x] = 1.0
        branches = sv.run_ir(circ, e)
        assert len(branches) == 1 and branches[0][0] == {}, "a unitary circuit has one branch"
        U[:, x] = branches[0][1].amp
    return U


def dropped_angle_sum(qft, kmax):
    return sum(2 * math.pi / 2 ** g["k"] for g in qft["gates"] if g["op"] == "cp" and g["k"] > kmax)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser()
    ap.add_argument("--m-max", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20261101)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    data = json.loads(certify_tool(["qft-sample", "--all", str(args.m_max)]))
    informative = []  # (m, kmax) with eta_aqft < 2 and a dropped gate
    assert sorted(int(k) for k in data) == list(range(1, args.m_max + 1)), sorted(data)

    for m in range(1, args.m_max + 1):
        entry = data[str(m)]
        qft, adj, aqft = entry["qft"], entry["adjoint"], entry["aqft"]
        n = 2 ** m
        # gate list shape: m H's and m(m-1)/2 rotations, cp 1 k with 2 <= k <= m
        ops = [g["op"] for g in qft["gates"]]
        assert ops.count("h") == m and ops.count("cp") == m * (m - 1) // 2 and \
            len(ops) == m * (m + 1) // 2, ops
        assert all(g["a"] == 1 and 2 <= g["k"] <= m for g in qft["gates"] if g["op"] == "cp")
        # (a) U_qft = R F
        U = simulate(qft)
        RF = bitrev_matrix(m) @ dft_matrix(m)
        err = np.max(np.abs(U - RF))
        assert err < EPS, f"m = {m}: |U_qft - R F| = {err:.3g}"
        unit = np.max(np.abs(U.conj().T @ U - np.eye(n)))
        assert unit < EPS, f"m = {m}: U_qft not unitary ({unit:.3g})"
        for _ in range(3):
            psi = rng.normal(size=n) + 1j * rng.normal(size=n)
            psi /= np.linalg.norm(psi)
            out = sv.run_ir(qft, psi)[0][1].amp
            e = np.max(np.abs(out - RF @ psi))
            assert e < EPS, f"m = {m}: random state error {e:.3g}"
        # (b) the adjoint circuit is the inverse
        Ua = simulate(adj)
        inv = np.max(np.abs(Ua @ U - np.eye(n)))
        assert inv < EPS, f"m = {m}: adjoint is not the inverse ({inv:.3g})"
        assert len(adj["gates"]) == len(qft["gates"]) and \
            [g["op"] for g in adj["gates"]] == ops[::-1] and \
            all(g["a"] == -1 for g in adj["gates"] if g["op"] == "cp"), "adjointGates shape"
        # (c) the AQFT bounds
        bounds = []
        etas = []
        for kmax in range(1, m + 1):
            a = aqft[str(kmax)]
            kept = [g for g in qft["gates"] if g["op"] != "cp" or g["k"] <= kmax]
            assert a["gates"] == kept, f"m = {m}, kmax = {kmax}: aqft is not the filter"
            if kmax == m:
                assert a["gates"] == qft["gates"], "kmax = m must drop nothing"
            Ua = simulate(a)
            dist = np.linalg.norm(U - Ua, 2)
            b1 = 2 * math.pi * m / 2 ** kmax
            b2 = dropped_angle_sum(qft, kmax)
            assert dist <= b1 + EPS, f"m = {m}, kmax = {kmax}: {dist:.4f} > 2 pi m / 2^kmax = {b1:.4f}"
            assert dist <= b2 + EPS, f"m = {m}, kmax = {kmax}: {dist:.4f} > sum of dropped angles {b2:.4f}"
            if kmax == m:
                assert dist < EPS
            bounds.append(f"k{kmax}: {dist:.3f} <= {b2:.3f} <= {b1:.3f}")
            # the eta_aqft line (Stage 18c, aqft_diamond_le): 2 ||U_qft - U_aqft||_2 <= eta_aqft m kmax
            # = 4 pi m / 2^kmax, the diamond-distance budget. A diamond distance is at most 2, so
            # eta_aqft >= 2 is a vacuous budget; a pair with eta_aqft < 2 and a dropped gate
            # (kmax < m) is informative and counted (STAGE18_TASK.md, 18c notes (ii)).
            eta = 4 * math.pi * m / 2 ** kmax
            assert 2 * dist <= eta + EPS, f"m = {m}, kmax = {kmax}: 2 * {dist:.4f} > eta_aqft = {eta:.4f}"
            if eta >= 2:
                mark = " (vacuous, >= 2)"
            elif kmax < m:
                mark = " (informative)"
                informative.append((m, kmax))
            else:
                mark = ""
            etas.append(f"k{kmax}: {2 * dist:.3f} <= {eta:.3f}" + mark)
        print(f"ok:   m = {m}: qftCircuit = R F (max err {err:.1e}), unitary, adjoint inverse "
              f"(err {inv:.1e}); ||U_qft - U_aqft||_2 <= sum of dropped angles <= 2 pi m / 2^kmax: "
              + "; ".join(bounds))
        print(f"      m = {m}: 2 ||U_qft - U_aqft||_2 <= eta_aqft m kmax = 4 pi m / 2^kmax: "
              + "; ".join(etas))

    # (d) negative control: one rotation's sign flipped
    m = 3
    bad = json.loads(json.dumps(data[str(m)]["qft"]))
    i = next(k for k, g in enumerate(bad["gates"]) if g["op"] == "cp")
    bad["gates"][i]["a"] = -1
    err = np.max(np.abs(simulate(bad) - bitrev_matrix(m) @ dft_matrix(m)))
    assert err > 0.1, f"negative control not detected ({err:.3g})"
    print(f"ok:   negative control: cp 1 2 -> cp (-1) 2 in qftCircuit 3 detected (max err {err:.3f})")
    pairs = ", ".join(f"(m = {m}, kmax = {k})" for m, k in informative)
    print(f"note: informative pairs (eta_aqft m kmax = 4 pi m / 2^kmax < 2 with a dropped gate, kmax < m) "
          f"for m <= {args.m_max}: {len(informative)}" + (f" [{pairs}]" if informative else "")
          + ("; in this range the eta_aqft line is a consistency check of aqft_diamond_le, not a "
             "test of the bound (18c notes (ii))" if not informative else ""))
    print(f"qft_diff: PASS — m = 1..{args.m_max}: qftCircuit m = R F (qubit 0 the MSB, as "
          "qft_basis), adjoint = inverse, aqft = the filter with both bounds, eta_aqft consistent")


if __name__ == "__main__":
    main()
