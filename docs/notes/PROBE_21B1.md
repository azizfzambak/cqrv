# Probe 21b1 — feasibility of measured composition (route (a) of PHASE2_SPEC §A.7)

Task 21b1 (STAGE21_TASK.md; PHASE2_SPEC §A.9 (1) and the refinement at the 21m review), 2026-11-15.
The probe writes no certificate and changes nothing under `CQRV/`. Its three files:
`docs/notes/PROBE_21B1.md` (this note), `scripts/probes/probe_21b1.py` (the numbers, run with
`.venv/Scripts/python.exe -I scripts/probes/probe_21b1.py --cqr .lake/build/bin/cqr.exe [--samples
<dir>]`), `scripts/probes/Probe21b1.lean` (the statements and proofs of Q1, Q2 and Q4; checked with
`lake env lean scripts/probes/Probe21b1.lean`, 217 lines, 12.0 s wall including the `import CQRV`
load, every theorem with axioms exactly `propext`, `Classical.choice`, `Quot.sound`).

**Summary.** Route (a) is feasible at `grover_pred_037` (n = 8, M = 32) with precision m = 5: the
composite realizes "search with the estimated count" with ε = ε_f ≈ 0.0746, δ = ae_delta + 7/128 ≈
0.2441 and grade (21, 2996, 1436, 8). The reviewer's arithmetic is confirmed; one detail is
corrected (at m = 4 two outcomes, y = 0 and y = 1, lie in the domain with a wrong r, not one). The
recommendation for 21b2 is route (a) at that instance, about 350–450 lines, with a committed
composition certificate left to the review.

## Q1 — Theorem 3.3a on a pseudo-metric: yes, the proof goes through unchanged

`Probe21b1.measured_composition_pseudo` states `measured_composition` with `[PseudoMetricSpace Y]
[PseudoMetricSpace Z]` and proves it with the proof of `CQRV.measured_composition` verbatim
(`Composition.lean`, Stage 7–8). No lemma it uses needs a metric: `relax_comp` is already stated on
`PseudoMetricSpace`; `mixture_union_bound`, `prob_mixture`, `measure_chan_ofClassical`,
`prob_mono` and `Spec.relax` need none. The `MetricSpace` assumption of the committed theorem is
only stronger than its proof uses (`realizes_zero_iff` and `Spec.relax_zero`, which do need a
metric, are not involved). Axioms: the standard three.

## Q2 — stage 2 as a `GradedChannel`: built from the Choi matrix, 60 lines

Physlib has no measure-and-prepare constructor: `POVM.measureDiscard` measures and re-encodes the
outcome, `CPTPMap.replacement` prepares one fixed state, `CPTPMap.of_kraus_CPTPMap` needs Kraus
operators (which would need the square roots of the prepared states). It has
`CPTPMap.CPTP_of_choi_PSD_Tr`: a channel from a PSD Choi matrix with partial trace 1. The probe
builds (`section Q2`):

- `mpChoi σ := ∑ y, (σ y).m ⊗ₖ (encode y).m`, the block-diagonal Choi matrix of `y ↦ σ y`;
  `mpChoi_psd` (a sum of Kronecker products of PSD matrices: `MState.psd`,
  `Matrix.PosSemidef.PosSemidef_kronecker`, `Finset.sum_induction` with `PosSemidef.add`, under
  `open scoped ComplexOrder`), `mpChoi_traceLeft` (the partial trace is `∑ y, tr(σ y) |y⟩⟨y| = 1`,
  `MState.tr'`);
- `measurePrepare σ : CPTPMap Y dZ := CPTP_of_choi_PSD_Tr (mpChoi_psd σ) (mpChoi_traceLeft σ)`;
- `measurePrepare_encode : measurePrepare σ (encode y₀) = σ y₀` (through
  `CPTPMap.mat_coe_eq_apply_mat`, `MatrixMap.of_choi_matrix` and `encode_m : (encode y).m a a' =
  if a = y ∧ a' = y then 1 else 0`);
- `stage2 C gmax : GradedChannel (CountOut m a) (Reg n) := ⟨measurePrepare fun y => (groverChannel
  n (C y)).chan (encode ()), gmax⟩` and the identity the task asks for,
  `stage2_encode : (stage2 C gmax).chan (encode y) = (groverChannel n (C y)).chan (encode ())`.

Here `C y` is the Grover circuit at `r y` iterations (`groverCircuit N n (r y) = .ok (C y)` for the
instance); the declared grade `gmax` is the maximum of `Synthesis.grade (C y)` over the outcomes
(`groverChannel` keeps the measured grade of its circuit). The construction is 60 lines, with
`Finset.sum_ite_eq` / `Finset.sum_ite_eq'` doing the collapsing sums. Axioms: the standard three.

## Q3 — the numbers (`probe_21b1.py`)

Definitions as in the task: a = M/2ⁿ; ε_f = `ae_eps a m`; D = {y ∈ 0 … 2^m − 1 : |sin²(π y/2^m) − a| ≤
ε_f} (the ideal point `inr ()`, estimate a, is always in the domain); r(y) = `rStar n (M̃ y)` with
M̃ y the nearest integer to 2ⁿ·sin²(π y/2^m) clamped to [1, 2ⁿ], `rStar` in IEEE doubles as
`CQRV.Synthesis.rStar` (floor(π/(4θ)), θ = asin √(M/2ⁿ), π = 2 asin 1); δ_g = max over D ∪ {ideal}
of `groverDelta (r y) n M` (exact rationals through the Chebyshev recurrence of
`CQRV.Certify.groverSuccess`); δ = ae_delta + δ_g with ae_delta = 1 − 8/π² ≈ 0.189431. The stage-1
composed grades are the `composed.grade` of `CertifyTool counting-sample <file> <m>` (shape tree,
mode mbu, exact inverse QFT); the stage-2 grade is the grade of `cqr synthesize <file> --grover
--iterations r --json` at the r(y) of D (one Lean start per sample, 8 to 42 s).

### grover_pred_037: n = 8, M = 32, a = 1/8, rStar = 2, groverDelta(2) = 7/128

| m | ε_f | D | r(y) on D | δ_g | δ = ae_delta + δ_g | < 1 | margin in | margin out | exclusions (y ↔ 2^m − y) | tightest exclusion | stage-1 grade (composed) | stage-2 grade |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 4 | 0.168426 | {0, 1, 2, 14, 15} | 12, 3, 2, 2, 3 | 114760807/134217728 ≈ 0.855035 | 1.044465 | **no** | 0.043426 | 0.015232 | 6 | y = 3: 0.015232 | (20, 1388, 660, 8) | (15, 794, 432, 7) (r = 12) |
| 5 | 0.074575 | {3, 4, 28, 29} | all 2 | 7/128 ≈ 0.054688 | 0.244118 | yes | 0.033840 | 0.012365 | 15 | y = 2 (↔ 30): 0.012365 | (21, 2862, 1364, 8) | (15, 134, 72, 7) |
| 6 | 0.034878 | {7, 8, 56, 57} | all 2 | 7/128 | 0.244118 | yes | 0.013431 | 0.005857 | 30 | y = 9 (↔ 55): 0.022926 | (22, 5808, 2772, 8) | (15, 134, 72, 7) |
| 7 | 0.016837 | {14, 15, 113, 114} | all 2 | 7/128 | 0.244118 | yes | 0.005331 | 0.004610 | 59 | y = 17: 0.022384 | (23, 11698, 5588, 8) | (15, 134, 72, 7) |

"margin in" is the least ε_f − |est − a| over D (the slack a Lean proof of membership has);
"margin out" the least |est − a| − ε_f over the excluded outcomes; "exclusions" the number of
excluded outcomes with r(y) ≠ 2 modulo the symmetry y ↔ 2^m − y, each needing an inequality in a
Lean proof of the δ_g bound; "tightest exclusion" the excluded outcome with r(y) ≠ 2 closest to D.

**The reviewer's arithmetic, checked.** At m = 4 the composite is vacuous (δ ≈ 1.044): the
outcome y = 0 (estimate 0, M̃ = 1, r = 12) lies in D with a bad r — and so does y = 1 (estimate
sin²(π/16) ≈ 0.038, M̃ = 10, r = 3), which the refinement did not mention; δ_g is the r = 12 failure
0.855. At m = 5, 6 and 7 the domain contains only outcomes with r(y) = 2, and δ = 1 − 8/π² + 7/128 =
0.244118: the refinement's "≈ 0.244" is right. The composite grade at m = 5 is (21, 2862, 1364, 8) ⊕
(15, 134, 72, 7) = (21, 2996, 1436, 8) (⊕: max w, sum d, sum t, max a).

### simple_alu_x0_1: n = 6, M = 30, a = 30/64, rStar = 1, groverDelta(1) = 833/2048

| m | ε_f | D | r(y) on D | δ_g | δ | < 1 | margin in | margin out | exclusions | stage-1 grade | stage-2 grade |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 4 | 0.234519 | {3, 4, 5, 11, 12, 13} | 1, 0, 0, 0, 0, 1 | 17/32 ≈ 0.531250 | 0.720681 | yes | 0.011927 | 0.087785 | 6 | (21, 2213, 1020, 11) | (16, 121, 60, 10) |
| 5 | 0.107621 | {7, 8, 24, 25} | 1, 0, 0, 1 | 17/32 | 0.720681 | yes | 0.041326 | 0.021174 | 13 | (22, 4567, 2108, 11) | (16, 121, 60, 10) |
| 6 | 0.051401 | {15, 16, 48, 49} | 1, 0, 0, 1 | 17/32 | 0.720681 | yes | 0.020151 | 0.014894 | 25 | (23, 9273, 4284, 11) | (16, 121, 60, 10) |
| 7 | 0.025098 | {30, 31, 97, 98} | all 1 | 833/2048 ≈ 0.406738 | 0.596169 | yes | 0.007340 | 0.006152 | 50 | (24, 18683, 8636, 11) | (16, 121, 60, 10) |

With a ≈ 0.47 an estimate above 1/2 gives θ > π/4 and `rStar` = 0 (Grover with zero iterations:
success = a, δ = 17/32); up to m = 6 such outcomes lie in D. The composite is non-vacuous at every m
but weak (δ ≈ 0.72 for m ≤ 6, 0.596 at m = 7). The instance is not a candidate.

## Q4 — the Lean cost of the domain, at the candidate instance (m = 5)

For the δ_g bound, every excluded outcome y with r(y) ≠ 2 needs `ae_eps a m < |sin²(π y/2^m) − a|`:
15 inequalities modulo the symmetry (y ∈ {0, 1, 2, 5, 6, …, 16}). The tightest is y = 2 (↔ 30):
sin²(2π/32) ≈ 0.038060, a − ε_f ≈ 0.050425, margin 0.012365. `Probe21b1.exclusion_m5_y2` proves
`ae_eps (1/8) 5 < |sin²(π·2/2^5) − 1/8|` in 16 lines from `Real.pi_lt_d4` (π < 3.1416),
`Real.sin_le` (sin x ≤ x; `Real.sin_bound` and `Real.sin_gt_sub_cube` are available for the
outcomes above a, where a lower bound on sin is needed), `Real.sqrt_lt'` for √(7/64) < 0.330725, and
two `nlinarith` calls (195 ms and 122 ms by `set_option profiler true`; the whole file 12 s wall
with the import). The names confirmed with `#check` are listed in the probe file (the Mathlib
decimal bounds are `Real.pi_gt_d2/d4/d6`, `Real.pi_lt_d2/d4/d6`; `Real.pi_gt_3141592` does not
exist). With monotonicity of sin² on [0, π/2] the 15 inequalities reduce to two (est(2) < a − ε_f
and est(5) > a + ε_f) plus the ordering of the outcomes, so the estimated cost is 80–120 lines.

## Q5 — stage 1 at m = 5

`cqr certify examples/grover_pred_037.cqr --problem count --precision 5 --out <tmp>` (one run, not
committed): certified, status `certified (ε ≈ 0.074575, δ = 1 − 8/π² ≈ 0.189431; universal in M ≥ 1;
M = 32 decided by the kernel)`; kernel 22.4 s, wall 33.0 s (the certificate's `kernel_check`; 35.8 s
for the whole `cqr` process); peak working set of `lean.exe` 2587 MB (tasklist, polled every
0.5 s); composed grade (21, 2862, 1364, 8), `grade_ext` (2397, ≤ 1364, 10, 341, 682), G = 6923, seven
blocks (h_layer, cg_0 … cg_4, inverse); axioms the standard three.

## Recommendation for 21b2: route (a) at (n, M, m) = (8, 32, 5)

The instance is `grover_pred_037` at m = 5: the smallest precision whose domain holds only outcomes
with the good r, composite δ ≈ 0.244, grade (21, 2996, 1436, 8), ε ≈ 0.0746 (about ±19 in units of M).
New library pieces, Physlib-side unless noted, about 350–450 lines in all:

1. `measured_composition_pseudo` in `CQRV/Realizability/Composition.lean` (25 lines; the existing
   theorem keeps its statement).
2. The measure-and-prepare channel: `encode_m`, `mpChoi`, `mpChoi_psd`, `mpChoi_traceLeft`,
   `measurePrepare`, `measurePrepare_encode` (60 lines; a new `CQRV/Realizability/MeasurePrepare.lean`
   or in `Composition.lean`).
3. Stage 2 for the instance: `stage2` with `r y := rStar 8 (M̃ y)` as a Lean function on `CountOut 5
   a` and the circuit family `groverCircuit net 8 (r y)`; its realization of `S_g y z := |countEst 5 a
   y − a| ≤ ae_eps a 5 ∧ P z` on `DiscreteOut (Reg 8)` with δ_g = 7/128: for y ∈ D the Grover
   lemma at r = 2 (`grover_parametric_lemma`, the committed `delta_eq`), for y ∉ D nothing to show
   (60 lines plus the domain lemmas of Q4, 80–120 lines).
4. The two free hypotheses: non-expansiveness with z = z' (10 lines); domain compatibility by
   `countSpec_relax` (10 lines).
5. The composite theorem at the instance, from the counting certificate's `cert` at M = 32 (the
   `Realizes` of `CountSpec 5 (32/256)` under `countPOVM 8 5`, composed grade (21, 2862, 1364, 8))
   and `measured_composition_pseudo`: `Realizes (S_g.comp (CountSpec 5 a)) (basisPOVM 8)
   (measuredComp Φ₁ (countPOVM 8 5 a) Ψ) (ae_eps a 5) (ae_delta + 7/128) ((21, 2862, 1364, 8) +
   (15, 134, 72, 7))` (40 lines), stated with the two circuits as hypotheses (`countingCircuit net 8 5
   … = .ok C₁`, `groverCircuit net 8 2 = .ok C₂`) so that no kernel evaluation enters the library.
6. Tests in `tests/CQRVTests/` (40 lines).

A committed composition certificate (a `Cert.lean` that instantiates 5 with the two literals: the
counting certificate at m = 5, 22.4 s kernel and 2.6 GB, plus the Grover certificate at r = 2) is
possible but is a new certificate kind for the renderer and the schema; the review decides whether
21b2 writes it or stops at the library theorem and its test. Route (b) is not needed: the obstacle
of §A.7 (classically controlled iteration) is absent at the channel level, where stage 2 is the
measure-and-prepare channel of Q2.

What this note does not claim: the composite is for one instance and one precision; the stage-2
grade is a declared maximum over branches, not a measured grade of one circuit; the IR still has no
classically controlled iteration, so no single emitted circuit realizes the composite.
