"""Probe 21b1, Q3 — the numbers of measured composition (PHASE2_SPEC §A.7, §A.9 (1); STAGE21_TASK.md
21b1). For (n, M) = (8, 32) (grover_pred_037) and (6, 30) (simple_alu_x0_1) and m = 4, 5, 6, 7:

  * ε_f = ae_eps a m = 2π√(a(1−a))/2^m + π²/4^m, a = M/2^n;
  * the domain D of S_g: the outcomes y ∈ 0 … 2^m − 1 with |countEst y − a| ≤ ε_f, where
    countEst y = sin²(π y/2^m) (the ideal point `inr ()` has estimate a and lies in D);
  * r(y) = rStar n (M̃ y), M̃ y the nearest integer to 2^n · countEst y clamped to [1, 2^n], with
    rStar exactly as CQRV.Synthesis.rStar computes it (floor(π/(4θ)), θ = asin √(M/2^n), in
    IEEE doubles — Lean's Float);
  * δ_g = max over y ∈ D ∪ {ideal} of groverDelta (r y) n M, the exact rational
    1 − sin²((2r+1)θ) computed as CQRV.Certify.groverSuccess does (Chebyshev U_{2r} in
    ℚ[c]/(c² − (1 − s))); the "good" r is rStar n M;
  * the composite δ = ae_delta + δ_g and whether it is below 1;
  * the margins: min over y ∉ D of |est − a| − ε_f and min over y ∈ D of ε_f − |est − a|;
  * the stage-1 composed grade at m (read from the counting-sample JSON files given with --samples,
    one per m, or "not measured") and the stage-2 grade (the maximum over y ∈ D of the grade of the
    Grover circuit at r(y), by `cqr synthesize <file> --grover --iterations r --json`).

Usage: python -I scripts/probes/probe_21b1.py --cqr <cqr.exe> [--samples <dir with
<name>_m<m>.json>] [--md <out.md>] [--table]  (--table, 21b2: the full table y ↦ r(y) at
(8, 32, 5), the largest r with its Grover grade — the honest g₂ — and the composite grade)
"""

import argparse
import json
import math
import os
import subprocess
import sys
from fractions import Fraction

INSTANCES = [("grover_pred_037", 8, 32), ("simple_alu_x0_1", 6, 30)]
MS = [4, 5, 6, 7]


def r_star(n, M):
    """CQRV.Synthesis.rStar in IEEE doubles: floor(pi / (4 θ)), θ = asin(sqrt(M / 2^n)), pi = 2 asin 1."""
    if M == 0 or M > 2 ** n:
        return None
    theta = math.asin(math.sqrt(M / float(2 ** n)))
    pi = 2 * math.asin(1.0)
    return int(math.floor(pi / (4 * theta)))


def two_c_times(s, p):
    return (2 * p[1] * (1 - s), 2 * p[0])


def chebyshev_u(s, k):
    """(U_k) as (a, b) meaning a + b c in Q[c]/(c^2 - (1 - s)), as CQRV.Certify.chebyshevU."""
    u, v = (Fraction(1), Fraction(0)), (Fraction(0), Fraction(2))
    for _ in range(k):
        w = two_c_times(s, v)
        u, v = v, (w[0] - u[0], w[1] - u[1])
    return u


def grover_delta(r, n, M):
    s = Fraction(M, 2 ** n)
    u = chebyshev_u(s, 2 * r)[0]
    return 1 - s * u * u


def ae_eps(a, m):
    return 2 * math.pi * math.sqrt(a * (1 - a)) / 2 ** m + math.pi ** 2 / 4 ** m


AE_DELTA = 1 - 8 / math.pi ** 2


def est(y, m):
    return math.sin(math.pi * y / 2 ** m) ** 2


def m_tilde(y, m, n):
    return min(max(round(2 ** n * est(y, m)), 1), 2 ** n)


def grade_of(cqr, src, r):
    p = subprocess.run([cqr, "synthesize", src, "--grover", "--iterations", str(r), "--json"],
                       capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        return None
    g = json.loads(p.stdout)["grades"]["circuit"]
    return (g["w"], g["d"], g["t"], g["a"])


def analyse(name, n, M, m, cqr, samples):
    a = M / 2 ** n
    eps = ae_eps(a, m)
    good_r = r_star(n, M)
    rows, D, margins_in, margins_out = [], [], [], []
    for y in range(2 ** m):
        e = est(y, m)
        dev = abs(e - a)
        r = r_star(n, m_tilde(y, m, n))
        inside = dev <= eps
        if inside:
            D.append(y); margins_in.append(eps - dev)
        else:
            margins_out.append(dev - eps)
        rows.append((y, e, dev, r, inside, grover_delta(r, n, M) if r is not None else None))
    deltas = [grover_delta(r, n, M) for y, e, dev, r, ins, _ in rows if ins]
    deltas.append(grover_delta(good_r, n, M))  # the ideal point: estimate a, r = rStar n M
    delta_g = max(deltas)
    composite = AE_DELTA + float(delta_g)
    bad_in_D = sorted({r for y, e, dev, r, ins, _ in rows if ins and r != good_r})
    bad_r_outside = [y for y, e, dev, r, ins, _ in rows if not ins and r != good_r]
    # the exclusion inequalities: y outside D with r(y) ≠ good r, modulo y ↔ 2^m − y
    excl = sorted({min(y, 2 ** m - y) for y in bad_r_outside})
    tight = min(((dev - eps), y) for y, e, dev, r, ins, _ in rows if not ins and r != good_r) if bad_r_outside else None
    src = os.path.join("examples", f"{name}.cqr")
    stage2 = {r: grade_of(cqr, src, r) for r in sorted({r for y, e, dev, r, ins, _ in rows if ins} | {good_r})}
    g2 = None
    if all(v is not None for v in stage2.values()):
        g2 = tuple(max(v[i] for v in stage2.values()) for i in range(4))
    comp = None
    if samples:
        p = os.path.join(samples, f"{name}_m{m}.json")
        if os.path.exists(p):
            j = json.load(open(p, encoding="utf-8"))
            cg = j["composed"]["grade"]
            comp = (cg["w"], cg["d"], cg["t"], cg["a"])
    return {"name": name, "n": n, "M": M, "m": m, "a": a, "eps": eps, "good_r": good_r, "D": D,
            "rows": rows, "delta_g": delta_g, "composite": composite, "below_one": composite < 1,
            "margin_in": min(margins_in) if margins_in else None,
            "margin_out": min(margins_out) if margins_out else None, "bad_r_in_D": bad_in_D,
            "exclusions": excl, "tightest": tight, "stage2": stage2, "g2": g2, "composed1": comp}


def fmt_g(g):
    return "not measured" if g is None else "(%d, %d, %d, %d)" % g


def seq_comp(g1, g2):
    """Grade ⊕ (report Table 3.1): max w, sum d, sum t, max a."""
    return (max(g1[0], g2[0]), g1[1] + g2[1], g1[2] + g2[2], max(g1[3], g2[3]))


def full_table(name, n, M, m, cqr, samples):
    """21b2 (PHASE2_SPEC §A.9 (9)): the full table y ↦ (estimate, M̃, r(y), in D) at (n, M, m), the
    largest r with the Grover grade there (the honest g₂: stage 2 runs on every outcome), and the
    composite grade stage-1 ⊕ g₂."""
    x = analyse(name, n, M, m, cqr, samples)
    lines = [f"### 21b2 — the full table at {name}, (n, M, m) = ({n}, {M}, {m}); a = {x['a']:.6f}, "
             f"ε_f = {x['eps']:.6f}, rStar = {x['good_r']}\n",
             "| y | sin²(πy/2^m) | M̃ | r(y) | in D |", "|---|---|---|---|---|"]
    for y, e, dev, r, ins, _ in x["rows"]:
        lines.append(f"| {y} | {e:.6f} | {m_tilde(y, m, n)} | {r} | {'yes' if ins else ''} |")
    lines.append(f"| ideal | {x['a']:.6f} | {M} | {x['good_r']} | yes |")
    rmax = max(r for y, e, dev, r, ins, _ in x["rows"])
    ys = [y for y, e, dev, r, ins, _ in x["rows"] if r == rmax]
    g2 = grade_of(cqr, os.path.join("examples", f"{name}.cqr"), rmax)
    lines.append("")
    lines.append(f"Largest r in the table: r = {rmax} (at y = {ys}); the Grover grade at r = {rmax}: {fmt_g(g2)} "
                 f"— the honest g₂ (refinement (9)).")
    if x["composed1"] is not None and g2 is not None:
        lines.append(f"Composite grade: {fmt_g(x['composed1'])} ⊕ {fmt_g(g2)} = {fmt_g(seq_comp(x['composed1'], g2))}.")
    lines.append(f"Over the domain only (the 21b1 figure): {fmt_g(x['g2'])}.")
    return "\n".join(lines)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--samples", default=None)
    ap.add_argument("--md", default=None)
    ap.add_argument("--table", action="store_true",
                    help="21b2: print only the full table at (8, 32, 5) with the honest g₂")
    args = ap.parse_args()
    if args.table:
        text = full_table("grover_pred_037", 8, 32, 5, args.cqr, args.samples)
        print(text)
        if args.md:
            with open(args.md, "w", encoding="utf-8", newline="\n") as f:
                f.write(text + "\n")
        return
    lines = []
    for name, n, M in INSTANCES:
        lines.append(f"### {name}: n = {n}, M = {M}, a = {M}/{2 ** n} = {M / 2 ** n:.6f}, rStar = {r_star(n, M)}, "
                     f"groverDelta(rStar) = {grover_delta(r_star(n, M), n, M)} ≈ {float(grover_delta(r_star(n, M), n, M)):.6f}\n")
        lines.append("| m | ε_f | D (outcomes y) | r(y) on D | δ_g (max over D ∪ ideal) | δ = ae_delta + δ_g | < 1 | margin in | margin out | r(y) ≠ rStar inside D | exclusions (y ↔ 2^m−y) | tightest exclusion | stage-1 composed grade | stage-2 grade (max over D) |")
        lines.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
        for m in MS:
            x = analyse(name, n, M, m, args.cqr, args.samples)
            rs = {y: r for y, e, dev, r, ins, _ in x["rows"] if ins}
            lines.append(
                f"| {m} | {x['eps']:.6f} | {x['D']} | {sorted(set(rs.values()))} (per y: {[rs[y] for y in x['D']]}) | "
                f"{x['delta_g']} ≈ {float(x['delta_g']):.6f} | {x['composite']:.6f} | {'yes' if x['below_one'] else 'no'} | "
                f"{x['margin_in']:.6f} | {x['margin_out']:.6f} | {x['bad_r_in_D'] if x['bad_r_in_D'] else 'none'} | "
                f"{len(x['exclusions'])}: {x['exclusions']} | "
                f"{('y = %d, |est−a| − ε_f = %.6f' % (x['tightest'][1], x['tightest'][0])) if x['tightest'] else 'none'} | "
                f"{fmt_g(x['composed1'])} | {fmt_g(x['g2'])} {x['stage2']} |")
        lines.append("")
    text = "\n".join(lines)
    print(text)
    if args.md:
        with open(args.md, "w", encoding="utf-8", newline="\n") as f:
            f.write(text + "\n")


if __name__ == "__main__":
    main()
