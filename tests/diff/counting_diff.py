"""Differential test of the counting circuit (PHASE2_SPEC.md §A.3 as amended before Stage 19;
Stage 19b B5; CLAUDE.md rule 9). The restoration of the circuit in its own factors is proved in
Lean (`countingCircuit_ancRestore_raw`, CQRV/Circuit/CountingCorrect.lean); this harness is the
independent numerical check of the circuits the Lean side builds and of the **convention** of
§A.3 (5): the phase register is read with `data n` (phase qubit 0) as the most significant bit,
and the eigenphases of the controlled iterates are ±θ/π (the phase fix `z (data (n+j))` present).

Layout (§A.3 (1)): search register `data 0..n−1`, phase register `data n..n+m−1`; in the flat
index of statevector.py qubit 0 is the MSB, so the data index is `search · 2^m + y`, with `y` the
natural reading of the phase register (`data n` the MSB), and the ancillae are the least
significant bits. Every predicate's P is evaluated here (never taken from the synthesizer) and its
truth table is compared with the network's (`truth_table` of `counting-sample`, bit k of x = input
bit k); M = Σ P. With sin²θ = M/2ⁿ:

  (a) coherent mode, one branch from |0…0⟩: the phase-register distribution P(y) (marginal over
      the search register; the ancillae end in |0⟩) equals ½ (P_m(y; θ/π) + P_m(y; −θ/π)) to 1e−9,
      where P_m(y; φ) = |2^{−m} ∑_{j<2^m} e^{2πi j (φ − y/2^m)}|²;
  (b) MBU mode, sampled branches (`statevector.run_ir_sampled`): each branch's final data state
      equals the coherent one (overlap ≥ 1 − 1e−9), the ancillae end in |0⟩;
  (c) negative controls: every phase fix `z (data (n+j))` removed by the harness (the last gate of
      every copy of every controlled iterate, located from the block table) gives the shifted
      mixture ½ (P_m(y; ½ + θ/π) + P_m(y; ½ − θ/π)) to 1e−9 and differs from (a) for a predicate
      with M/2ⁿ ≠ ½: at m = 1 by exactly |cos 2θ| = |1 − 2M/2ⁿ| (more than 0.1 for every predicate
      here), and at every m by more than 1e−6 (the two mixtures can come closer in sup norm for
      larger m: odd_five at m = 2, 0.053; the control is still far above the 1e−9 tolerance);
      for M/2ⁿ = ½ the fix changes nothing (checked); the bit-reversed reading of the phase register fails the closed
      form (error > 0.1) for some m ≥ 2, for every predicate with M ≠ 0 (for M = 0 the distribution
      is δ_{y,0}, invariant under bit reversal, noted);
  (d) grades: measured ≤ composed componentwise (w, a, t equal, d ≤; `grade_append_le`), `tDepth`
      within `tDepth(init) + Σ tCount` (`tDepth_append_le`), the `GradeExt` sums equal, and the
      block table replays to the circuit's gate list (every block's gates with its classical bits
      shifted by the bits of the blocks before it, `Circuit.append`);
  (e) kmax (m = 4, kmax = 2, 3; one predicate): the AQFT circuit is the exact one without the `cp`
      gates with k > kmax (all in the inverse block); the total-variation distance to the exact
      distribution is printed, no bound asserted (η_aqft ≥ 2 for m ≤ 4, as in Stage 18c).

If (a) fails, the harness reports which of the four conventions (phases ±θ/π or ½ ± θ/π, the
register read naturally or bit-reversed) the data fit, and fails: that is the stop condition of
§A.3 (5) — neither the harness nor the circuit is to be changed.

The circuits come from `lake env lean --run scripts/CertifyTool.lean counting-sample --all M
<files>` (one Lean start). Usage: python -I tests/diff/counting_diff.py [--m-max 4] [--seed S]
[--samples 2]
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
HERE = os.path.dirname(os.path.abspath(__file__))
PRED_DIR = os.path.join(HERE, "counting")

# (file, n, the predicate on the input bits x[0..n), the expected M); P is evaluated here
PREDS = [
    ("all_four.cqr", 4, lambda x: x[0] and x[1] and x[2] and x[3], 1),
    ("odd_five.cqr", 4, lambda x: (x[0] and x[1]) or (x[2] and x[3] and x[0]), 5),
    ("half.cqr", 4, lambda x: x[0], 8),
    ("none.cqr", 4, lambda x: False, 0),
    ("all.cqr", 4, lambda x: True, 16),
    ("n6_odd.cqr", 6, lambda x: (x[0] and x[1] and (x[2] != x[3]))
     or (x[0] and x[1] and x[2] and x[3] and x[4] and x[5]), 9),
]
AQFT_PRED = "odd_five.cqr"


def table_of(f, n):
    return "".join("1" if f([bool((x >> k) & 1) for k in range(n)]) else "0" for x in range(2**n))


def closed_form(m, phi):
    """P_m(y; phi) for y = 0 .. 2^m - 1."""
    y = np.arange(2**m)
    j = np.arange(2**m)
    amp = np.exp(2j * np.pi * np.outer(j, phi - y / 2**m)).sum(axis=0) / 2**m
    return np.abs(amp) ** 2


def mixture(m, phi):
    return 0.5 * (closed_form(m, phi) + closed_form(m, -phi))


def bitrev(y, m):
    return int(format(y, f"0{m}b")[::-1], 2)


def coherent_state(circ):
    """The one branch of a measurement-free circuit from |0...0>."""
    e0 = np.zeros(2 ** circ["n_data"], dtype=complex)
    e0[0] = 1.0
    branches = sv.run_ir(circ, e0)
    assert len(branches) == 1 and branches[0][0] == {}, "a coherent circuit has one branch"
    return branches[0][1]


def data_vector(state, n_anc):
    """The data-register vector of a state whose ancillae are |0...0> (asserted)."""
    amp = state.amp.reshape(-1, 2**n_anc)
    rest = float(np.sum(np.abs(amp[:, 1:]) ** 2))
    assert rest < EPS, f"ancillae not |0...0> (weight {rest:.3g})"
    return amp[:, 0]


def phase_dist(state, n, m, n_anc):
    """P(y): the phase register read with data n as the MSB, marginal over the search register."""
    v = data_vector(state, n_anc).reshape(2**n, 2**m)
    return np.sum(np.abs(v) ** 2, axis=0)


def strip_fix(obj):
    """The circuit without the phase fix of every copy of every controlled iterate."""
    n = obj["n"]
    gates = obj["circuit"]["gates"]
    drop = set()
    for row in obj["blocks"]:
        if not row["name"].startswith("cg_"):
            continue
        j = int(row["name"][3:])
        for t in range(row["multiplicity"]):
            idx = row["first"] + t * row["length"] + row["length"] - 1
            assert gates[idx] == {"op": "z", "q": [n + j]}, (row["name"], t, gates[idx])
            drop.add(idx)
    assert len(drop) == sum(2**j for j in range(obj["m"]))
    return {**obj["circuit"], "gates": [g for i, g in enumerate(gates) if i not in drop]}


def replay(obj):
    """(d) the block table replays to the circuit's gate list, bits shifted by the blocks before."""
    out, offset, pos = [], 0, 0
    for row in obj["blocks"]:
        assert row["first"] == pos, (row["name"], row["first"], pos)
        assert row["length"] == len(row["circuit"]["gates"])
        for _ in range(row["multiplicity"]):
            for g in row["circuit"]["gates"]:
                g2 = dict(g)
                if "c" in g2:
                    g2["c"] += offset
                if "if" in g2:
                    g2["if"] += offset
                out.append(g2)
            offset += row["n_bits"]
            pos += row["length"]
    assert out == obj["circuit"]["gates"], "block table does not replay to the circuit"
    assert offset == obj["measured"]["n_bits"]
    assert pos == obj["measured"]["gates"]


def check_grades(obj):
    """(d) measured vs composed (Stage 19a): w, a, t equal, d <=; GradeExt sums; tDepth bound."""
    g, c = obj["measured"]["grade"], obj["composed"]["grade"]
    assert g["w"] == c["w"] and g["a"] == c["a"] and g["t"] == c["t"], (g, c)
    assert g["d"] <= c["d"], (g, c)
    e, ce = obj["measured"]["grade_ext"], obj["composed"]["grade_ext"]
    for k in ("two_qubit", "rot", "meas", "ff"):
        assert e[k] == ce[k], (k, e, ce)
    assert e["t_depth"] <= ce["t_depth"], (e, ce)
    # the whole's live ancillae and the blocks' at the end: 0
    assert obj["measured"]["live_end"] == 0 and all(r["live_end"] == 0 for r in obj["blocks"])
    return g, c


def fmt(g):
    return f"({g['w']}, {g['d']}, {g['t']}, {g['a']})"


def conventions(P, m, theta):
    """The closed-form error of the four conventions: (phase shift, reading) -> max error."""
    rev = np.array([P[bitrev(y, m)] for y in range(2**m)])
    out = {}
    for shift, name in ((0.0, "phases ±θ/π"), (0.5, "phases ½ ± θ/π")):
        want = mixture(m, shift + theta / math.pi)
        out[(name, "data n the MSB")] = float(np.max(np.abs(P - want)))
        out[(name, "bit-reversed")] = float(np.max(np.abs(rev - want)))
    return out


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser()
    ap.add_argument("--m-max", type=int, default=4)
    ap.add_argument("--seed", type=int, default=20261104)
    ap.add_argument("--samples", type=int, default=2, help="sampled MBU branches per (P, m)")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    files = [os.path.join(PRED_DIR, f) for f, _, _, _ in PREDS]
    data = json.loads(certify_tool(["counting-sample", "--all", str(args.m_max)] + files))
    assert sorted(data) == sorted(f for f, _, _, _ in PREDS), sorted(data)

    max_err = 0.0           # (a) largest closed-form error
    max_err_bad = 0.0       # (c) largest closed-form error of the shifted mixture
    min_sep = None          # (c) smallest separation of the fix-less circuit from (a)
    branches = 0
    rev_results = {}
    seps = {}               # (c) separations of the fix-less circuit from (a), per predicate
    for f, n, pred, M_want in PREDS:
        entry = data[f]
        assert entry["n"] == n, (f, entry["n"])
        table = table_of(pred, n)
        M = table.count("1")
        assert M == M_want, (f, M)
        theta = math.asin(math.sqrt(M / 2**n))
        rev_fail = []
        for m in range(1, args.m_max + 1):
            objs = entry["m"][str(m)]
            coh, mbu = objs["coherent"], objs["mbu"]
            for obj in (coh, mbu):
                assert obj["truth_table"] == table, f"{f}: network truth table differs from P"
                assert obj["n"] == n and obj["m"] == m
                assert obj["circuit"]["n_data"] == n + m
                replay(obj)
                check_grades(obj)
            assert mbu["measured"]["n_bits"] > 0 and coh["measured"]["n_bits"] == 0
            # (a) coherent: the closed form
            st = coherent_state(coh["circuit"])
            n_anc = coh["circuit"]["n_anc"]
            P = phase_dist(st, n, m, n_anc)
            assert abs(float(P.sum()) - 1) < EPS
            want = mixture(m, theta / math.pi)
            err = float(np.max(np.abs(P - want)))
            if err >= EPS:
                conv = conventions(P, m, theta)
                lines = "\n".join(f"      {k[0]}, {k[1]}: max error {v:.3g}" for k, v in conv.items())
                raise AssertionError(
                    f"STOP (PHASE2_SPEC §A.3 (5)): {f}, m = {m}: the phase-register distribution is "
                    f"not ½(P_m(θ/π) + P_m(−θ/π)) read with data n the MSB (error {err:.3g}); the "
                    f"four conventions:\n{lines}")
            max_err = max(max_err, err)
            # (b) MBU: sampled branches equal the coherent state
            v_c = data_vector(st, n_anc)
            e0 = np.zeros(2 ** (n + m), dtype=complex)
            e0[0] = 1.0
            for _ in range(args.samples):
                bits, sm = sv.run_ir_sampled(mbu["circuit"], e0, rng)
                v_m = data_vector(sm, mbu["circuit"]["n_anc"])
                ov = abs(np.vdot(v_c, v_m))
                assert ov >= 1 - EPS, f"{f}, m = {m}: MBU branch {bits} overlap {ov:.12f}"
                assert len(bits) == mbu["measured"]["n_bits"]
                branches += 1
            # (c) negative controls
            bad = strip_fix(coh)
            P_bad = phase_dist(coherent_state(bad), n, m, n_anc)
            want_bad = mixture(m, 0.5 + theta / math.pi)
            err_bad = float(np.max(np.abs(P_bad - want_bad)))
            assert err_bad < EPS, f"{f}, m = {m}: without the phase fix: error {err_bad:.3g}"
            max_err_bad = max(max_err_bad, err_bad)
            sep = float(np.max(np.abs(P_bad - P)))
            if 2 * M != 2**n:
                # detected at the harness's tolerance for every m; at m = 1 the separation is
                # exactly |cos 2θ| = |1 − 2M/2ⁿ| (> 0.1 for these predicates); for larger m the
                # two mixtures can come closer in sup norm (odd_five, m = 2: 0.053)
                assert sep > 1e-6, f"{f}, m = {m}: fix-less circuit within {sep:.3g} of the fixed one"
                if m == 1:
                    cos2 = abs(1 - 2 * M / 2**n)
                    assert abs(sep - cos2) < EPS and sep > 0.1, (f, sep, cos2)
                min_sep = sep if min_sep is None else min(min_sep, sep)
                seps.setdefault(f, []).append(sep)
            else:
                assert sep < EPS, f"{f}: M/2^n = 1/2, the fix changes nothing, but {sep:.3g}"
            if m >= 2:
                rev = np.array([P[bitrev(y, m)] for y in range(2**m)])
                rev_fail.append(float(np.max(np.abs(rev - want))) > 0.1)
            g, c = check_grades(coh)
            print(f"  {f:13s} n = {n} M = {M:2d} m = {m}: closed form err {err:.1e} (fix-less: "
                  f"{err_bad:.1e}, sep {sep:.3f}); MBU {args.samples} branches; grade {fmt(g)} "
                  f"<= composed {fmt(c)}, tDepth {coh['measured']['grade_ext']['t_depth']} <= "
                  f"{coh['composed']['grade_ext']['t_depth']}; {coh['measured']['gates']} gates "
                  f"({mbu['measured']['gates']} MBU)")
        if M == 0:
            rev_results[f] = "n/a (M = 0: P = δ_{y,0}, invariant under bit reversal)"
        else:
            assert any(rev_fail), f"{f}: the bit-reversed reading never fails for m >= 2"
            rev_results[f] = "fails for m = " + ", ".join(
                str(m) for m, bad in zip(range(2, args.m_max + 1), rev_fail) if bad)
    print(f"ok:   (a) closed form (phases ±θ/π, data n the MSB), largest error {max_err:.2e} over "
          f"{len(PREDS)} predicates, m = 1..{args.m_max}")
    print(f"ok:   (b) {branches} sampled MBU branches equal the coherent state, ancillae |0⟩")
    for f, ss in seps.items():
        assert max(ss) > 0.1, (f, ss)
    print(f"ok:   (c) negative control 1: every phase fix removed gives the shifted mixture "
          f"(largest error {max_err_bad:.2e}); separation from (a) for M/2^n ≠ ½: at m = 1 exactly "
          f"|cos 2θ| (> 0.1 for every predicate), at least {min_sep:.3f} over all m ("
          + "; ".join(f"{f}: " + ", ".join(f"{x:.3f}" for x in ss) for f, ss in seps.items())
          + "); half.cqr (M/2^n = ½): no change, as expected")
    print("ok:   (c) negative control 2: bit-reversed reading: "
          + "; ".join(f"{f}: {r}" for f, r in rev_results.items()))
    print("ok:   (d) grades measured ≤ composed (w, a, t equal, d ≤), tDepth within its bound, "
          "GradeExt sums equal, block table replays to the circuit, both modes")

    # (e) kmax at m = 4
    m = args.m_max
    entry = data[AQFT_PRED]
    exact = entry["m"][str(m)]["coherent"]
    P_exact = phase_dist(coherent_state(exact["circuit"]), entry["n"], m, exact["circuit"]["n_anc"])
    tvs = []
    for kmax in (2, 3):
        a = entry["m"][str(m)]["aqft"][str(kmax)]
        assert a["kmax"] == kmax and a["uncompute"] == "coherent"
        kept = [g for g in exact["circuit"]["gates"] if not (g["op"] == "cp" and g["k"] > kmax)]
        assert a["circuit"]["gates"] == kept, f"aqft kmax = {kmax} is not the exact circuit minus the dropped cp"
        dropped = len(exact["circuit"]["gates"]) - len(kept)
        assert dropped == sum(1 for g in exact["blocks"][-1]["circuit"]["gates"]
                              if g["op"] == "cp" and g["k"] > kmax) and dropped > 0
        replay(a)
        check_grades(a)
        P_a = phase_dist(coherent_state(a["circuit"]), entry["n"], m, a["circuit"]["n_anc"])
        tv = 0.5 * float(np.sum(np.abs(P_a - P_exact)))
        eta = 4 * math.pi * m / 2**kmax
        tvs.append(f"kmax = {kmax}: {dropped} cp dropped, TV distance {tv:.4f} (eta_aqft = {eta:.2f} >= 2, vacuous)")
    print(f"ok:   (e) {AQFT_PRED}, m = {m}: " + "; ".join(tvs))
    print(f"counting_diff: PASS — {len(PREDS)} predicates (n = 4 and 6; M = 0, 1, 5, 8, 9, 16), "
          f"m = 1..{args.m_max}: the convention of §A.3 (5) (y read with data n the MSB, phases "
          f"±θ/π with the fix present), MBU = coherent, both negative controls, grades vs the "
          "composed bound, block replay, AQFT")


if __name__ == "__main__":
    main()
