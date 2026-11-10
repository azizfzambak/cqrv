module

public import CQRV.Grover.Counting
public import CQRV.Realizability.Composition

/-!
# CQRV.Grover.AmplitudeEstimation

PHASE2_SPEC.md §A.4 ("Amendments before Stage 20b" (1)–(2); docs/tasks/STAGE20B_TASK.md 20b1
A1–A4), report §2.1.2 (Definition 2.2), §8.2 — **the amplitude-estimation realization lemma
with the exact inverse QFT**: the output type `CountOut m a = Reg m ⊕ Unit` with the
pseudo-metric induced by the real-valued estimate `countEst`, the specification `CountSpec`
("the answer is the ideal value"), the decoding POVM on the whole data register
(`inl y ↦` the projector onto "phase = y", `inr () ↦ 0`), its measurement on the state the
counting circuit produces (`phaseDist`, Stage 20a2), and `ae_realizes` /
`ae_parametric_lemma`: the channel `groverChannel (n + m) C` of a synthesized counting circuit
`(ae_eps a m, 1 − 8/π²)`-realizes `CountSpec m a` within any grade bounding its measured grade,
from `countingCircuit_ancRestore` (Stage 19c) and `qpe_success` (Stage 20a2).

Imports `CQRV.Grover.Counting` (hence Physlib) and `CQRV.Realizability.Composition` (for
`measure_eq_re_trace`); not in the `cqr` closure (PHASE2_SPEC §A.8 item 6).
-/

@[expose] public section

noncomputable section

namespace CQRV.Grover

open CQRV CQRV.Synthesis CQRV.Counting Matrix Real
open scoped MState

/-! ## A1 — the output type, the metric, the specification -/

/-- PHASE2_SPEC §A.4 (amendments before Stage 20b, (1)) — the estimate decoded from an outcome:
`sin²(π y.toNat / 2^m)` on `inl y` (the decoding of `qpe_success`, with no `bitRev`), and the
ideal value `a` on the distinguished point `inr ()`. Real-valued: `sin²(π/8) = (2 − √2)/4` is
irrational. -/
def countEst (m : ℕ) (a : ℝ) : Reg m ⊕ Unit → ℝ
  | .inl y => Real.sin (π * y.toNat / 2 ^ m) ^ 2
  | .inr () => a

set_option linter.unusedVariables false in
/-- PHASE2_SPEC §A.4 (amendments before Stage 20b, (1)), §A.8 item 1 — the output type of
amplitude estimation: an outcome of the phase register or the ideal point. The metric depends
on `a`, so `a` is a parameter of the type (phantom in the carrier, hence the linter option). -/
def CountOut (m : ℕ) (a : ℝ) : Type := Reg m ⊕ Unit

set_option linter.unusedVariables false in
instance (m : ℕ) (a : ℝ) : Fintype (CountOut m a) := inferInstanceAs (Fintype (Reg m ⊕ Unit))

set_option linter.unusedVariables false in
instance (m : ℕ) (a : ℝ) : DecidableEq (CountOut m a) :=
  inferInstanceAs (DecidableEq (Reg m ⊕ Unit))

/-- PHASE2_SPEC §A.8 item 1 — the pseudo-metric induced by the estimate: `dist y y' =
|countEst y − countEst y'|`. A pseudo-metric, not a metric: `y` and its reflection `2^m − y`
have the same estimate. -/
instance (m : ℕ) (a : ℝ) : PseudoMetricSpace (CountOut m a) :=
  PseudoMetricSpace.induced (countEst m a) inferInstance

/-- Report §2.1.2, PHASE2_SPEC §A.4 (amendments before Stage 20b, (1)) — the counting
specification: the unique input `()` accepts exactly the ideal point `inr ()`; the tolerance
enters through `relax` (`countSpec_relax`). -/
def CountSpec (m : ℕ) (a : ℝ) : Spec Unit (CountOut m a) :=
  fun _ y => y = (Sum.inr () : CountOut m a)

/-- The induced distance, as the absolute difference of the estimates. -/
theorem dist_countOut (m : ℕ) (a : ℝ) (y y' : CountOut m a) :
    dist y y' = |countEst m a y - countEst m a y'| :=
  Real.dist_eq _ _

/-- Report §2.1.2 — the ε-relaxation of `CountSpec` accepts `y` iff its estimate is within `ε`
of the ideal value. -/
theorem countSpec_relax (m : ℕ) (a ε : ℝ) (y : CountOut m a) :
    (CountSpec m a).relax ε () y ↔ |countEst m a y - a| ≤ ε := by
  constructor
  · rintro ⟨y', hy', hd⟩
    have hy : y' = (Sum.inr () : CountOut m a) := hy'
    subst hy
    exact (dist_countOut m a y (Sum.inr ())).symm.trans_le hd
  · intro h
    exact ⟨(Sum.inr () : CountOut m a), rfl, (dist_countOut m a y (Sum.inr ())).trans_le h⟩

/-- Report §2.1.2 — the domain of `CountSpec` is all of `Unit`. -/
theorem countSpec_dom (m : ℕ) (a : ℝ) : (CountSpec m a).dom = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨(Sum.inr () : CountOut m a), rfl⟩

/-! ## A2 — the decoding POVM -/

/-- PHASE2_SPEC §A.4 (amendments before Stage 20b, (2)) — the projector onto "phase = y" on
the whole data register: the sum over the search register `s` of `|(s, y)⟩⟨(s, y)|`, the
basis state indexed through `splitEquiv`. -/
def phaseProj (n m : ℕ) (y : Reg m) : HermitianMat (Reg (n + m)) ℂ :=
  ∑ s : Reg n, (MState.pure (Ket.basis ((splitEquiv n m).symm (s, y)))).M

theorem phaseProj_nonneg (n m : ℕ) (y : Reg m) : 0 ≤ phaseProj n m y :=
  Finset.sum_nonneg fun _ _ => (MState.pure _).nonneg

/-- The projectors onto the phases resolve the identity: `∑_y ∑_s |(s,y)⟩⟨(s,y)| = ∑_x |x⟩⟨x|`
(reindexed through `splitEquiv`), which is `basisPOVM`'s `normalized`. -/
theorem sum_phaseProj (n m : ℕ) : ∑ y : Reg m, phaseProj n m y = 1 := by
  have h := (basisPOVM (n + m)).normalized
  change ∑ x : Reg (n + m), (MState.pure (Ket.basis x)).M = 1 at h
  rw [← h, ← (splitEquiv n m).symm.sum_comp (fun x => (MState.pure (Ket.basis x)).M),
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The POVM elements on `Reg m ⊕ Unit`: `inl y ↦ phaseProj n m y`, `inr () ↦ 0`. -/
def countMats (n m : ℕ) : Reg m ⊕ Unit → HermitianMat (Reg (n + m)) ℂ
  | .inl y => phaseProj n m y
  | .inr () => 0

theorem countMats_nonneg (n m : ℕ) : ∀ z : Reg m ⊕ Unit, 0 ≤ countMats n m z
  | .inl y => phaseProj_nonneg n m y
  | .inr () => le_rfl

/-- Report §2.1.2 (Definition 2.2), PHASE2_SPEC §A.4 (amendments before Stage 20b, (2)) — the
decoding POVM of amplitude estimation on the whole data register `Reg (n + m)`: `inl y` has the
projector onto "phase = y" (summed over the search register, which is never traced), `inr ()`
has `0`. `normalized` is `sum_phaseProj`. -/
def countPOVM (n m : ℕ) (a : ℝ) : POVM (CountOut m a) (Reg (n + m)) where
  mats := countMats n m
  nonneg := countMats_nonneg n m
  normalized := by
    change ∑ z : Reg m ⊕ Unit, countMats n m z = 1
    rw [Fintype.sum_sum_type, Finset.sum_eq_zero (fun (u : Unit) _ => by cases u; rfl), add_zero]
    exact sum_phaseProj n m

/-- `tr(|x⟩⟨x| ρ) = ρ_{xx}` (the computation inside `basisPOVM_measure`). -/
theorem trace_pure_basis_mul {d : Type} [Fintype d] [DecidableEq d] (x : d) (ρ : Matrix d d ℂ) :
    ((MState.pure (Ket.basis x)).m * ρ).trace = ρ x x := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pure_basis_m_apply, ite_and,
    ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- PHASE2_SPEC §A.4 (amendments before Stage 20b, (2)), §A.4 (3) — on the state the counting
circuit produces, the decoding POVM yields `inl y` with probability `phaseDist gp m y`: the
trace against `∑_s |(s,y)⟩⟨(s,y)|` is `∑_s ‖v (s,y)‖²` for `v = U_count |0…0⟩`
(`measure_eq_re_trace`, `uConj_ancZero_m`, `trace_pure_basis_mul`). -/
theorem countPOVM_measure (gp : GroverData) (m : ℕ) (y : Reg m) :
    ((countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ)).measure
      ((U_count gp.P m none) ◃ ancZero (gp.n + m)) (Sum.inl y) : ℝ) = phaseDist gp m y := by
  refine (measure_eq_re_trace _ _ _).trans ?_
  change RCLike.re ((phaseProj gp.n m y).mat * _).trace = _
  rw [phaseProj, HermitianMat.mat_finset_sum, Finset.sum_mul, Matrix.trace_sum, map_sum]
  unfold phaseDist
  refine Finset.sum_congr rfl fun s _ => ?_
  change RCLike.re ((MState.pure (Ket.basis ((splitEquiv gp.n m).symm (s, y)))).m *
    ((U_count gp.P m none) ◃ ancZero (gp.n + m)).m).trace = _
  rw [trace_pure_basis_mul, uConj_ancZero_m, vecMulVec_apply, Pi.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, RCLike.re_to_complex, Complex.ofReal_re]

/-- The distinguished outcome `inr ()` has probability `0` on every state. -/
theorem countPOVM_measure_inr (n m : ℕ) (a : ℝ) (ρ : MState (Reg (n + m))) :
    ((countPOVM n m a).measure ρ (Sum.inr ()) : ℝ) = 0 := by
  refine (measure_eq_re_trace _ _ _).trans ?_
  change RCLike.re ((0 : HermitianMat (Reg (n + m)) ℂ).mat * _).trace = 0
  rw [HermitianMat.mat_zero, Matrix.zero_mul, Matrix.trace_zero, map_zero]

/-! ## A3 — the realization -/

/-- PHASE2_SPEC §A.4 — the failure probability of amplitude estimation, `1 − 8/π²`
(`qpe_success`). -/
def ae_delta : ℝ := 1 - 8 / π ^ 2

open Classical in
/-- The event probability of the relaxed specification under the decoding POVM, as the sum
of `phaseDist` over the decoding set of `qpe_success`: the `inr ()` term is `0`
(`countPOVM_measure_inr`), the `inl y` terms are `phaseDist gp m y` on the event
`|sin²(π y.toNat / 2^m) − a| ≤ ε` (`countSpec_relax`, `countPOVM_measure`). -/
theorem prob_countPOVM_relax (gp : GroverData) (m : ℕ) (ε : ℝ) :
    prob ((countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ)).measure
        ((U_count gp.P m none) ◃ ancZero (gp.n + m)))
      ((CountSpec m (gp.M / 2 ^ gp.n : ℝ)).relax ε ()) =
    ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
      |Real.sin (π * y.toNat / 2 ^ m) ^ 2 - (gp.M / 2 ^ gp.n : ℝ)| ≤ ε), phaseDist gp m y := by
  unfold prob
  rw [Finset.sum_filter]
  change ∑ z : Reg m ⊕ Unit, _ = _
  rw [Fintype.sum_sum_type, Finset.sum_eq_zero (fun (u : Unit) _ => by
    cases u; rw [countPOVM_measure_inr, ite_self]), add_zero]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [countPOVM_measure]
  exact if_congr (countSpec_relax m _ ε (Sum.inl y)) rfl rfl

/-- Report §2.1.2 (Definition 2.2), §8.2; PHASE2_SPEC §A.4 — **the realization conjunct of
amplitude estimation**: any circuit `C` that restores its ancillae with `U_count gp.P m none`
on `Reg (n + m) × Reg C.nAnc` realizes `CountSpec m a` under the decoding POVM with
`ε = ae_eps a m`, `δ = ae_delta = 1 − 8/π²`, within any grade `g` bounding its measured grade.
The channel output on `encode ()` is `U_count ◃ ancZero (n + m)` (`AncRestore.traced`, as in
`grover_realizes_of_ancRestore`); the event is the decoding set of `qpe_success`
(`prob_countPOVM_relax`). -/
theorem ae_realizes (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {C : Circuit}
    (hR : AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (gp.M / 2 ^ gp.n : ℝ)) (countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ))
      (groverChannel (gp.n + m) C) (ae_eps (gp.M / 2 ^ gp.n : ℝ) m) ae_delta g := by
  refine ⟨hg, fun u _ => ?_⟩
  have hchan : (groverChannel (gp.n + m) C).chan (encode u) =
      (U_count gp.P m none) ◃ ancZero (gp.n + m) := by
    simp only [groverChannel, GradedChannel.traceAnc, CPTPMap.compose_eq,
      CPTPMap.replacement_apply, CPTPMap.traceRight_eq_MState_traceRight]
    exact hR.traced (ancZero (gp.n + m))
  rw [hchan, prob_countPOVM_relax, ae_delta, sub_sub_cancel]
  exact qpe_success gp hm

/-! ## A4 — the parametric lemma -/

/-- Report §5.2.4, §8.2; PHASE2_SPEC §A.4 — **the amplitude-estimation parametric lemma**
(exact inverse QFT): for Grover data `gp`, a well-formed single-output network `N` on `gp.n`
inputs computing `gp.P`, and the synthesized counting circuit `C`, the channel
`groverChannel (gp.n + m) C` `(ae_eps a m, 1 − 8/π²)`-realizes `CountSpec m a` within any grade
`g ≥ Synthesis.grade C` (with `g := Synthesis.grade C` the measured statement; Stage 20b3 uses
the composed bound of 19a), and `C` restores its ancillae while applying `U_count gp.P m none`.
From `countingCircuit_ancRestore` (rewritten by `hP`) and `ae_realizes`. -/
theorem ae_parametric_lemma (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network} (hN : N.WF)
    (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N gp.n m none shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (gp.M / 2 ^ gp.n : ℝ)) (countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ))
        (groverChannel (gp.n + m) C) (ae_eps (gp.M / 2 ^ gp.n : ℝ) m) ae_delta g ∧
      AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none) := by
  have hR := (countingCircuit_ancRestore hC hN hn h1).2
  rw [hP] at hR
  exact ⟨ae_realizes gp hm hR g hg, hR⟩

end CQRV.Grover

end

end
