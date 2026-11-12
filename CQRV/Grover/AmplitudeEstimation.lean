module

public import CQRV.Grover.Counting
public import CQRV.Realizability.Composition
public import CQRV.Realizability.Coherent

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

Stage 20b2 (PHASE2_SPEC §A.4 "Amendments before Stage 20b" (3)–(4); STAGE20B_TASK.md 20b2
B2–B4) adds **the AQFT variant through Theorem 3.3b**: the operator norm of `liftP` and of
`A ⊗ₖ 1_{Reg 0}` (B2), the diamond distance of the exact and the approximate inverse blocks
`inverse_diamond_le ≤ eta_aqft m kmax` (B3), and `ae_parametric_lemma_aqft` (B4): the counting
circuit with the approximate inverse QFT realizes `CountSpec` with
`δ = ae_delta + eta_aqft m kmax / 2`, by `coherent_composition_diamond_pseudo` with the exact
circuit as the ideal composite (`η_f = 0` on the shared body, `η_g = eta_aqft` on the inverse).
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

/-- Stage 20b3 (PHASE2_SPEC §A.4 "Amendments before Stage 20b3" (3)) — `ae_parametric_lemma` over
the fields of the Grover data instead of the record: the form a certificate instantiates. With
the record form, every unification of `gp.P` against the predicate literal makes the elaborator
unfold `Network.pred` (a large definition) before it reduces the projection of the constructed
record, which costs seconds per occurrence and exceeds the heartbeat limit of a generated
`Cert.lean`; here every argument is syntactic (`hP` is `rfl` on identical terms, the
conclusion names `P`, `n`, `M` directly). -/
theorem ae_parametric_lemma_mk (n M : ℕ) (hpos : 1 ≤ M) (P : Reg n → Bool)
    (hcard : (Finset.univ.filter fun x => P x = true).card = M) {m : ℕ} (hm : 1 ≤ m)
    {N : Network} (hN : N.WF) (hn : N.nInputs = n) (h1 : N.outputs.length = 1)
    (hP : N.pred n = P) {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N n m none shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (M / 2 ^ n : ℝ)) (countPOVM n m (M / 2 ^ n : ℝ))
        (groverChannel (n + m) C) (ae_eps (M / 2 ^ n : ℝ) m) ae_delta g ∧
      AncRestore (n + m) C.nAnc C (U_count P m none) :=
  ae_parametric_lemma ⟨n, M, hpos, P, hcard⟩ hm hN hn h1 hP hC g hg

/-! ## Stage 20b2 — the AQFT variant through Theorem 3.3b (PHASE2_SPEC §A.4 (3)–(4)) -/

section AQFT

open scoped Matrix.Norms.L2Operator Kronecker

/-! ### B2 — the operator norm under reindexing -/

/-- `1 ⊗ₖ B` is `B ⊗ₖ 1` with the Kronecker factors swapped (`Equiv.prodComm`). -/
theorem one_kronecker_eq_submatrix {d e : Type} [DecidableEq d] [DecidableEq e]
    (B : Matrix e e ℂ) :
    ((1 : Matrix d d ℂ) ⊗ₖ B) =
      (B ⊗ₖ (1 : Matrix d d ℂ)).submatrix (Equiv.prodComm d e) (Equiv.prodComm d e) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- PHASE2_SPEC §A.4 (4) — `‖liftP B‖ ≤ ‖B‖`: `liftP B = (1 ⊗ₖ B).submatrix splitEquiv`
(`liftP_eq_submatrix`), the reindexing invariance twice (`splitEquiv`, then the swap of the
Kronecker factors), and `‖B ⊗ₖ 1‖ ≤ ‖B‖`. -/
theorem l2_opNorm_liftP_le {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) :
    ‖(liftP B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ)‖ ≤ ‖B‖ := by
  rw [liftP_eq_submatrix, l2_opNorm_submatrix_equiv, one_kronecker_eq_submatrix,
    l2_opNorm_submatrix_equiv]
  exact l2_opNorm_kronecker_one_le' B

/-- `A ⊗ₖ 1_{Reg 0}` is `A` reindexed by `d × Reg 0 ≃ d` (`Reg 0` is one point). -/
theorem kronecker_one_reg0_eq_submatrix {d : Type} (A : Matrix d d ℂ) :
    A ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ) =
      A.submatrix (Equiv.prodUnique d (Reg 0)) (Equiv.prodUnique d (Reg 0)) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  obtain rfl := reg0_unique u
  obtain rfl := reg0_unique v
  simp [Matrix.kroneckerMap_apply]

/-- PHASE2_SPEC §A.4 (4) — `‖A ⊗ₖ 1_{Reg 0}‖ = ‖A‖`. -/
theorem l2_opNorm_kronecker_one_reg0 {d : Type} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    ‖A ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)‖ = ‖A‖ := by
  rw [kronecker_one_reg0_eq_submatrix, l2_opNorm_submatrix_equiv]

/-! ### B3 — the inverse block -/

theorem liftP_sub {n m : ℕ} (A B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP (A - B) : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = liftP A - liftP B := by
  ext x y
  simp only [liftP, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem countingInverse_WF (n m : ℕ) (kmax : Option ℕ) : (countingInverse n m kmax).WF :=
  (block_inverse n m kmax).2.1

theorem countingInverse_all_unitary (n m : ℕ) (kmax : Option ℕ) :
    (countingInverse n m kmax).gates.all Gate.isUnitary = true := by
  show ((adjointGates (inverseGates m kmax)).map (Gate.shiftData n)).all Gate.isUnitary = true
  rw [List.all_map]
  exact List.all_eq_true.mpr fun g hg => by
    rw [Function.comp_apply, Gate.isUnitary_shiftData]
    exact adjointGates_unitary (inverseGates_unitary m kmax) g hg

theorem countingInverse_all_dataOnly (n m : ℕ) (kmax : Option ℕ) :
    (countingInverse n m kmax).gates.all Gate.dataOnly = true := by
  show ((adjointGates (inverseGates m kmax)).map (Gate.shiftData n)).all Gate.dataOnly = true
  rw [List.all_map]
  exact List.all_eq_true.mpr fun g hg => by
    rw [Function.comp_apply, Gate.dataOnly_shiftData]
    exact adjointGates_dataOnly (inverseGates_dataOnly m kmax) g hg

/-- The inverse block on any ancilla register is `qftInvU ⊗ 1` (`unitaryDenote_dataOnly`). -/
theorem unitaryDenote_countingInverse (n m a : ℕ) (kmax : Option ℕ) :
    unitaryDenote (n + m) a (countingInverse n m kmax).gates =
      (qftInvU n m kmax).val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) :=
  unitaryDenote_dataOnly _ (countingInverse_all_unitary n m kmax)
    (countingInverse_all_dataOnly n m kmax)

/-- PHASE2_SPEC §A.4 (4) — the operator norm of the difference of the exact and the approximate
inverse blocks: `qftInvU_val` for both, the linearity of `liftP`, `‖liftP X‖ ≤ ‖X‖`, the adjoint,
and `aqft_opNorm_le` read through `unitaryDenote_zero_eq` and `‖A ⊗ₖ 1_{Reg 0}‖ = ‖A‖`. -/
theorem inverse_opNorm_le (n m kmax : ℕ) :
    ‖(qftInvU n m none).val - (qftInvU n m (some kmax)).val‖ ≤ 2 * Real.pi * m / 2 ^ kmax := by
  rw [qftInvU_val, qftInvU_val, ← liftP_sub]
  refine (l2_opNorm_liftP_le _).trans ?_
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_sub,
    Matrix.l2_opNorm_conjTranspose]
  have h := aqft_opNorm_le m kmax
  rw [unitaryDenote_zero_eq, unitaryDenote_zero_eq, ← sub_kronecker_one' (e := Reg 0),
    l2_opNorm_kronecker_one_reg0] at h
  exact h

/-- PHASE2_SPEC §A.4 (4), report §2.3.2 — **the diamond distance of the exact and the
approximate inverse blocks** on any ancilla register `a`: `‖Ψ_exact − Ψ_aqft‖⋄ ≤ 2 ‖U_exact −
U_aqft‖ ≤ eta_aqft m kmax` (`channelDenote_of_unitary`, `diamondDist_ofUnitary_le`,
`unitaryDenote_countingInverse`, `‖X ⊗ₖ 1‖ ≤ ‖X‖`, `inverse_opNorm_le`). -/
theorem inverse_diamond_le (n m kmax a : ℕ) :
    diamondDist (channelDenote (n + m) a (countingInverse n m none))
      (channelDenote (n + m) a (countingInverse n m (some kmax))) ≤ eta_aqft m kmax := by
  rw [channelDenote_of_unitary (n + m) a (countingInverse_WF n m none)
      (countingInverse_all_unitary n m none),
    channelDenote_of_unitary (n + m) a (countingInverse_WF n m (some kmax))
      (countingInverse_all_unitary n m (some kmax))]
  refine (diamondDist_ofUnitary_le _ _).trans ?_
  change 2 * ‖unitaryDenote (n + m) a (countingInverse n m none).gates -
    unitaryDenote (n + m) a (countingInverse n m (some kmax)).gates‖ ≤ _
  rw [unitaryDenote_countingInverse, unitaryDenote_countingInverse,
    ← sub_kronecker_one' (e := Reg a)]
  have h := (l2_opNorm_kronecker_one_le' (e := Reg a) _).trans (inverse_opNorm_le n m kmax)
  have e : eta_aqft m kmax = 2 * (2 * Real.pi * m / 2 ^ kmax) := by
    unfold eta_aqft
    ring
  rw [e]
  linarith

/-- The traced form: the ancillae traced out after the inverse block (`diamondDist_compose_le`),
the `Ψ_k` of PHASE2_SPEC §A.4 (4). -/
theorem inverse_traced_diamond_le (n m kmax a : ℕ) :
    diamondDist (CPTPMap.traceRight ∘ₘ channelDenote (n + m) a (countingInverse n m none))
      (CPTPMap.traceRight ∘ₘ channelDenote (n + m) a (countingInverse n m (some kmax))) ≤
        eta_aqft m kmax :=
  (diamondDist_compose_le _ _ _).trans (inverse_diamond_le n m kmax a)

/-! ### B4 — the lemma -/

theorem ancStep_dataOnly {g : Gate} (hg : g.dataOnly = true) (k : ℕ) : ancStep k g = k := by
  unfold ancStep
  unfold Gate.dataOnly at hg
  generalize g.qubits = qs at hg
  induction qs generalizing k with
  | nil => rfl
  | cons q qs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hg
    cases q with
    | data i => exact ih k hg.2
    | anc i => simp at hg

/-- The inverse block has no ancilla (its gates are data-only). -/
theorem countingInverse_nAnc (n m : ℕ) (kmax : Option ℕ) : (countingInverse n m kmax).nAnc = 0 := by
  rw [nAnc_eq]
  have hd := countingInverse_all_dataOnly n m kmax
  generalize (countingInverse n m kmax).gates = gs at hd
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hd
    rw [List.foldl_cons, ancStep_dataOnly hd.1, ih hd.2]

/-- PHASE2_SPEC §A.4 (4), step 3 — the channel of an appended circuit factors through the
ancilla register of the whole: `Ψ ∘ Φ` with `Φ` the preparation and the first circuit and `Ψ` the
second circuit and the trace over the ancillae (`channelDenote_append`). -/
theorem groverChannel_chan_append (n : ℕ) {C₁ C₂ : Circuit} (h₁ : C₁.bitsOk = true)
    (h₂ : C₂.bitsOk = true) :
    (groverChannel n (C₁.append C₂)).chan =
      (CPTPMap.traceRight ∘ₘ channelDenote n (C₁.append C₂).nAnc C₂) ∘ₘ
        (channelDenote n (C₁.append C₂).nAnc C₁ ∘ₘ
          CPTPMap.replacement (ancZero n ⊗ᴹ ancZero (C₁.append C₂).nAnc)) := by
  have h := channelDenote_append n (C₁.append C₂).nAnc h₁ h₂
  show CPTPMap.traceRight ∘ₘ (channelDenote n (C₁.append C₂).nAnc (C₁.append C₂) ∘ₘ
    CPTPMap.replacement (ancZero n ⊗ᴹ ancZero (C₁.append C₂).nAnc)) = _
  rw [h]
  apply CPTPMap.funext
  intro ρ
  simp only [CPTPMap.compose_eq]

/-- Report §2.3.2 (Theorem 3.3b), §5.2.4, §8.2; PHASE2_SPEC §A.4 (3)–(4) — **the
amplitude-estimation parametric lemma with the approximate inverse QFT**: the synthesized
counting circuit `C` with `aqft m kmax` realizes `CountSpec m a` with `ε = ae_eps a m` and
`δ = ae_delta + eta_aqft m kmax / 2` within any grade `g ≥ Synthesis.grade C`. The five steps of
the task text: (1) the exact circuit `C₀ = body.append (countingInverse n m none)` from the same
`body` (`countingCircuit_ok`, `countingCircuit_of_body`); (2) `C.nAnc = C₀.nAnc` (the inverse
blocks have no ancilla, `countingInverse_nAnc`); (3) `(groverChannel (n+m) C).chan = Ψ_kmax ∘ Φ`
and the same for `C₀` with `Ψ_none` (`groverChannel_chan_append`); (4) the ideal composite is
`ae_realizes` on `C₀`, its probability part at grade `0`, `CountSpec` written as `Spec.comp S_g S_f`;
(5) `coherent_composition_diamond_pseudo` with `η_f = 0` (`diamondDist_self`) and
`η_g = eta_aqft m kmax` (`inverse_traced_diamond_le`). For `m ≤ 6` the bound is vacuous
(`eta_aqft ≥ 2`, Stage 18c), but the statement holds for every `m ≥ 1` and `kmax`. -/
theorem ae_parametric_lemma_aqft (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network}
    (hN : N.WF) (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} (kmax : ℕ) {C : Circuit}
    (hC : countingCircuit N gp.n m (some kmax) shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (gp.M / 2 ^ gp.n : ℝ)) (countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ))
      (groverChannel (gp.n + m) C) (ae_eps (gp.M / 2 ^ gp.n : ℝ) m)
      (ae_delta + eta_aqft m kmax / 2) g := by
  -- step 1: the exact circuit `C₀`, from the same body
  obtain ⟨hm0, body, hb, rfl⟩ := countingCircuit_ok hC
  have hC₀ := countingCircuit_of_body none hm0 hb
  set C₀ := body.append (countingInverse gp.n m none) with hC₀def
  -- step 2: the ancilla registers agree
  have hbody : body.bitsOk = true :=
    (countingPowers_block hN (block_hLayer gp.n m) hb).2.1.bitsOk
  set a := (body.append (countingInverse gp.n m (some kmax))).nAnc with ha
  have hA : C₀.nAnc = a := by
    rw [hC₀def, ha, nAnc_append, nAnc_append, countingInverse_nAnc, countingInverse_nAnc]
  -- step 3: the channel factorization, for both inverse blocks, on the shared register `a`
  set Φ : CPTPMap Unit (Reg (gp.n + m) × Reg a) :=
    channelDenote (gp.n + m) a body ∘ₘ CPTPMap.replacement (ancZero (gp.n + m) ⊗ᴹ ancZero a)
    with hΦ
  have hfac : ∀ (k : Option ℕ) (C' : Circuit) (a' : ℕ),
      C' = body.append (countingInverse gp.n m k) → C'.nAnc = a' →
      (groverChannel (gp.n + m) C').chan =
        (CPTPMap.traceRight ∘ₘ channelDenote (gp.n + m) a' (countingInverse gp.n m k)) ∘ₘ
          (channelDenote (gp.n + m) a' body ∘ₘ
            CPTPMap.replacement (ancZero (gp.n + m) ⊗ᴹ ancZero a')) := by
    intro k C' a' hC' hA'
    subst hC'
    subst hA'
    exact groverChannel_chan_append _ hbody (countingInverse_WF gp.n m k).bitsOk
  have hfacC := hfac (some kmax) _ a rfl rfl
  have hfac0 := hfac none C₀ a rfl hA
  -- step 4: the ideal composite, `ae_realizes` on `C₀`
  have hR₀ : AncRestore (gp.n + m) C₀.nAnc C₀ (U_count gp.P m none) := by
    have h := (countingCircuit_ancRestore hC₀ hN hn h1).2
    rwa [hP] at h
  have hid := (ae_realizes gp hm hR₀ (Synthesis.grade C₀) le_rfl).2
  rw [hfac0] at hid
  have hspec : Spec.comp (fun (_ : Unit) => CountSpec m (gp.M / 2 ^ gp.n : ℝ) ())
      (fun (_ _ : Unit) => True) = CountSpec m (gp.M / 2 ^ gp.n : ℝ) := by
    funext x z
    cases x
    apply propext
    simp only [Spec.comp, true_and, exists_const]
  have hideal : Realizes (Spec.comp (fun (_ : Unit) => CountSpec m (gp.M / 2 ^ gp.n : ℝ) ())
      (fun (_ _ : Unit) => True)) (countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ))
      ⟨(CPTPMap.traceRight ∘ₘ channelDenote (gp.n + m) a (countingInverse gp.n m none)) ∘ₘ Φ, 0⟩
      (ae_eps (gp.M / 2 ^ gp.n : ℝ) m) ae_delta 0 := by
    rw [hspec]
    exact ⟨le_rfl, hid⟩
  -- step 5: Theorem 3.3b on the pseudo-metric, `η_f = 0`, `η_g = eta_aqft m kmax`
  have hres := coherent_composition_diamond_pseudo (η_f := 0) (η_g := eta_aqft m kmax)
    (r := 0) (s := 0) (Φ₂ := ⟨Φ, 0⟩)
    (Ψ₂ := ⟨CPTPMap.traceRight ∘ₘ channelDenote (gp.n + m) a (countingInverse gp.n m (some kmax)),
      0⟩)
    hideal (diamondDist_self Φ).le
    (by rw [diamondDist_comm]; exact inverse_traced_diamond_le gp.n m kmax a) le_rfl le_rfl
  rw [hspec] at hres
  refine ⟨hg, fun x hx => ?_⟩
  have h := hres.2 x hx
  rw [hfacC]
  rw [zero_add] at h
  exact h

end AQFT

end CQRV.Grover

end

end
