module

public import CQRV.Grover.Restore
public import CQRV.Realizability.Realizes

/-!
# CQRV.Grover.Lemma

Report §5.2.4 (revised Lean sketch: `GroverParams`, `hM_card` a hypothesis), §8.2 (circuit
family, `p_succ = sin²((2r+1)θ)`), §8.2.4 (realization ∧ restoration), §8.3.2 (reflection
geometry), §8.3.4 / Figure 8.1 (lemma dependency graph), §6.3.2 (Theorem 3.3a once, at the
terminal measurement) — the Grover parametric lemma (Stage 7a; DECISIONS.md 2026-10-24,
Stage 7a decisions 1–5). Stage 7b proves the Figure 8.1 statements: the plane facts of §8.3.2
(`GroverParams.ketS_eq`, the inner products, `U_P ψ_g = −ψ_g`, `U_P ψ_b = ψ_b`,
`diffU_mulVec`), then `reflection_geometry`, `iteration_induction`, `terminal_measurement`,
`grover_realizes`; the lemma is sorry-free.

Figure 8.1, as formalized here:

```
oracle_reflection ─┐                       (proved, Reflections)
diffusion_reflection ┴→ reflection_geometry → iteration_induction → terminal_measurement ─┐
lemma_6_3_2 (proved) → grover_ancRestore (proved, Restore) ───────────────────────────────┤
                                       grover_realizes ←──────────────────────────────────┘
                     grover_parametric_lemma = grover_realizes ∧ grover_ancRestore
```

* The grade is derived (decision 1): the budget of `RealizesExact` is `Synthesis.grade C` of the
  synthesized circuit, not the report's formula `r⋆ (depth_U + depth_D)`.
* `r` is a parameter (decision 2): the lemma holds for every `r`, with `δ = 1 − sin²((2r+1)θ)`.
* The spec has input type `Unit` (decision 4); the channel prepares `|0…0⟩` on data and
  ancillae, runs `channelDenote` of the circuit and traces out the ancillae (`traceAnc`); the
  decoding is the computational-basis POVM (`basisPOVM`: Physlib has none).
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis Matrix
open scoped MState

noncomputable section

/-! ## Parameters (§5.2.4) -/

/-- Report §5.2.4 (revised sketch) — the Grover parameters: `n` data qubits (`N = 2ⁿ`), `M`
solutions, a certified oracle, and `hM_card`, the solution count of the oracle's predicate, as a
**hypothesis** (a specification promise, §5.1.3; never decided by enumeration). -/
structure GroverParams where
  /-- Number of data qubits, `N = 2ⁿ`. -/
  n : ℕ
  /-- Number of solutions. -/
  M : ℕ
  hM_pos : 1 ≤ M
  oracle : OracleCert n
  /-- A hypothesis (specification promise), never discharged by `decide` (§5.1.3). -/
  hM_card : (Finset.univ.filter (fun x => oracle.P x = true)).card = M

/-- Report §5.2.4, §8.2.2 — the Grover angle `θ = arcsin √(M / 2ⁿ)`. -/
def GroverParams.θ (gp : GroverParams) : ℝ := Real.arcsin (Real.sqrt ((gp.M : ℝ) / 2 ^ gp.n))

/-- Report §8.3.2 — the normalized good state `ψ_g = M^{−1/2} ∑_{P x} |x⟩`. -/
def GroverParams.psiGood (gp : GroverParams) : Reg gp.n → ℂ :=
  fun x => if gp.oracle.P x then ((Real.sqrt gp.M)⁻¹ : ℂ) else 0

/-- Report §8.3.2 — the normalized bad state `ψ_b = (N − M)^{−1/2} ∑_{¬P x} |x⟩`. -/
def GroverParams.psiBad (gp : GroverParams) : Reg gp.n → ℂ :=
  fun x => if gp.oracle.P x then 0 else ((Real.sqrt ((2 : ℝ) ^ gp.n - gp.M))⁻¹ : ℂ)

/-! ## Specification, decoding, channel (decision 4) -/

/-- Report §8.1, §2.1.1 — the search specification: the input is `Unit` (the predicate is fixed
by the instance); an output `x` is acceptable iff `P x`. -/
def SearchSpec {n : ℕ} (P : Reg n → Bool) : Spec Unit (Reg n) := fun _ x => P x = true

/-- Report §8.1 — the domain of the search spec is all of `Unit` iff there is a solution,
i.e. iff `M ≥ 1` (decision 4). -/
theorem searchSpec_dom_iff (gp : GroverParams) :
    (SearchSpec gp.oracle.P).dom = Set.univ ↔ 1 ≤ gp.M := by
  rw [← gp.hM_card]
  constructor
  · intro h
    obtain ⟨x, hx⟩ : () ∈ (SearchSpec gp.oracle.P).dom := h ▸ Set.mem_univ ()
    exact Finset.card_pos.mpr ⟨x, by simpa [SearchSpec] using hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h
    exact Set.eq_univ_of_forall fun _ => ⟨x, by simpa [SearchSpec] using hx⟩

/-- The matrix of a pure basis state `|y⟩⟨y|`. -/
theorem pure_basis_m_apply {d : Type} [Fintype d] [DecidableEq d] (y i j : d) :
    (MState.pure (Ket.basis y)).m i j = if i = y ∧ j = y then 1 else 0 := by
  simp only [MState.m, MState.pure, Ket.basis, HermitianMat.mat_mk, Matrix.vecMulVec_apply,
    Bra.eq_conj, Ket.coe_fun_eq]
  by_cases hi : i = y
  · subst hi
    by_cases hj : j = i
    · subst hj; simp
    · have hj' : ¬ i = j := fun h => hj h.symm
      simp [hj, hj']
  · have hi' : ¬ y = i := fun h => hi h.symm
    simp [hi, hi']

/-- Report §8.2.1 ("all qubits are measured"), decision 4 — the computational-basis POVM on
`Reg n`: outcome `y` has the projector `|y⟩⟨y|`. Physlib has no basis POVM; this one is
defined here and `normalized` is proved (`∑_y |y⟩⟨y| = 1`). -/
def basisPOVM (n : ℕ) : POVM (Reg n) (Reg n) where
  mats y := (MState.pure (Ket.basis y)).M
  nonneg y := (MState.pure (Ket.basis y)).nonneg
  normalized := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    ext i j
    change (∑ y, (MState.pure (Ket.basis y)).m) i j = (1 : Matrix (Reg n) (Reg n) ℂ) i j
    rw [Matrix.sum_apply]
    simp only [pure_basis_m_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      exact Finset.sum_eq_zero fun y _ =>
        ite_eq_right_iff.mpr fun h' => absurd (h'.1.trans h'.2.symm) h

/-- Report §8.2.1, §2.1.2, decision 4 — the Grover channel `Unit → Reg n` of a circuit `C`:
prepare `|0…0⟩` on the data register and on `C.nAnc` ancillae, run `channelDenote` of `C`,
trace out the ancillae (`GradedChannel.traceAnc`). Its grade is the measured grade of `C`
(decision 1). -/
def groverChannel (n : ℕ) (C : Circuit) : GradedChannel Unit (Reg n) :=
  GradedChannel.traceAnc
    ⟨channelDenote n C.nAnc C ∘ₘ CPTPMap.replacement (ancZero n ⊗ᴹ ancZero C.nAnc),
      Synthesis.grade C⟩

/-! ## Plane facts (Stage 7b item 1, §8.3.2) -/

namespace GroverParams
variable (gp : GroverParams)

/-- Report §8.2 — `k = 2^{−n/2}`, the amplitude of `|s⟩` on every basis state. -/
def amp : ℝ := (Real.sqrt 2)⁻¹ ^ gp.n

/-- `|Reg n| = 2ⁿ`. -/
theorem card_univ : (Finset.univ : Finset (Reg gp.n)).card = 2 ^ gp.n := by
  simp [Reg]

/-- Report §8.1 — `M ≤ 2ⁿ`, from `hM_card`. -/
theorem M_le : gp.M ≤ 2 ^ gp.n := by
  rw [← gp.hM_card, ← card_univ]
  exact Finset.card_filter_le _ _

/-- Report §8.3.2 — the bad set has `2ⁿ − M` elements. -/
theorem card_bad :
    (Finset.univ.filter (fun x => ¬ gp.oracle.P x = true)).card = 2 ^ gp.n - gp.M := by
  rw [← gp.hM_card, ← card_univ, Finset.filter_not,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]

/-- `√(2ⁿ) = (√2)ⁿ`. -/
theorem sqrt_N : Real.sqrt (2 ^ gp.n) = (Real.sqrt 2) ^ gp.n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) gp.n), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by norm_num)]

theorem ratio_le : (gp.M : ℝ) / 2 ^ gp.n ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact_mod_cast gp.M_le

/-- Report §8.2.2 — `sin θ = √M · 2^{−n/2}`. -/
theorem sin_θ : Real.sin gp.θ = Real.sqrt gp.M * gp.amp := by
  rw [GroverParams.θ, Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((gp.M : ℝ) / 2 ^ gp.n)])
    ((Real.sqrt_le_sqrt gp.ratio_le).trans_eq Real.sqrt_one), Real.sqrt_div' _ (by positivity),
    sqrt_N, amp, inv_pow, div_eq_mul_inv]

/-- Report §8.2.2 — `cos θ = √(2ⁿ − M) · 2^{−n/2}`. -/
theorem cos_θ : Real.cos gp.θ = Real.sqrt (2 ^ gp.n - gp.M) * gp.amp := by
  have h0 : (0 : ℝ) ≤ (gp.M : ℝ) / 2 ^ gp.n := by positivity
  rw [GroverParams.θ, Real.cos_arcsin, Real.sq_sqrt h0,
    show (1 : ℝ) - gp.M / 2 ^ gp.n = (2 ^ gp.n - gp.M) / 2 ^ gp.n by field_simp,
    Real.sqrt_div' _ (by positivity), sqrt_N, amp, inv_pow, div_eq_mul_inv]

theorem M_pos : (0 : ℝ) < gp.M := by exact_mod_cast gp.hM_pos

theorem sqrtM_sq : (Real.sqrt gp.M) ^ 2 = gp.M := Real.sq_sqrt gp.M_pos.le

theorem sqrtM_ne : (Real.sqrt gp.M : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr gp.M_pos).ne'

theorem N_sub_M_nonneg : (0 : ℝ) ≤ 2 ^ gp.n - gp.M := by
  have : (gp.M : ℝ) ≤ 2 ^ gp.n := by exact_mod_cast gp.M_le
  linarith

theorem sqrtB_sq : (Real.sqrt (2 ^ gp.n - gp.M)) ^ 2 = 2 ^ gp.n - gp.M :=
  Real.sq_sqrt gp.N_sub_M_nonneg

/-- A sum of a function that is constant on the good and on the bad set. -/
theorem sum_ite_P (α β : ℂ) :
    ∑ x, (if gp.oracle.P x then α else β) = gp.M * α + (2 ^ gp.n - gp.M) * β := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, gp.hM_card, card_bad, nsmul_eq_mul,
    nsmul_eq_mul, Nat.cast_sub gp.M_le]
  push_cast
  ring

/-- Report §8.3.2 — `∑ₓ ψ_g(x) = √M`. -/
theorem sum_psiGood : ∑ x, gp.psiGood x = (Real.sqrt gp.M : ℂ) := by
  have h := sum_ite_P gp ((Real.sqrt gp.M : ℂ)⁻¹) 0
  simp only [mul_zero, add_zero] at h
  rw [show (gp.M : ℂ) = (Real.sqrt gp.M : ℂ) ^ 2 by exact_mod_cast gp.sqrtM_sq.symm] at h
  rw [show (∑ x, gp.psiGood x) = _ from h]
  field_simp [gp.sqrtM_ne]

/-- Report §8.3.2 — `∑ₓ ψ_b(x) = √(2ⁿ − M)` (also for `M = 2ⁿ`). -/
theorem sum_psiBad : ∑ x, gp.psiBad x = (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) := by
  have h := sum_ite_P gp 0 ((Real.sqrt (2 ^ gp.n - gp.M) : ℂ)⁻¹)
  simp only [mul_zero, zero_add] at h
  rw [show ((2 : ℂ) ^ gp.n - gp.M) = (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) ^ 2 by
    exact_mod_cast gp.sqrtB_sq.symm] at h
  rw [show (∑ x, gp.psiBad x) = _ from h]
  by_cases hb : (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) = 0
  · rw [hb]; simp
  · field_simp

/-- A bad basis state exists only if `M < 2ⁿ`, and then `√(2ⁿ − M) ≠ 0`. -/
theorem sqrtB_ne_of_bad {x : Reg gp.n} (hx : ¬ gp.oracle.P x = true) :
    (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) ≠ 0 := by
  have hlt : gp.M < 2 ^ gp.n := by
    rw [← gp.hM_card, ← card_univ]
    refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => hx ?_⟩
    simpa using h (Finset.mem_univ x)
  have : (gp.M : ℝ) < 2 ^ gp.n := by exact_mod_cast hlt
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith)).ne'

/-- Report §8.2 — `|s⟩` has amplitude `2^{−n/2}` everywhere. -/
theorem ketS_apply (x : Reg gp.n) : ketS gp.n x = (gp.amp : ℂ) := by
  simp [ketS, amp]

/-- Report §8.3.2 — `|s⟩ = sin θ ψ_g + cos θ ψ_b`. -/
theorem ketS_eq :
    ketS gp.n = (Real.sin gp.θ : ℂ) • gp.psiGood + (Real.cos gp.θ : ℂ) • gp.psiBad := by
  funext x
  rw [ketS_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, sin_θ, cos_θ]
  by_cases hx : gp.oracle.P x = true
  · simp only [psiGood, psiBad, ite_eq_left hx, smul_eq_mul, mul_zero, add_zero]
    push_cast
    field_simp [gp.sqrtM_ne]
  · have hb := gp.sqrtB_ne_of_bad hx
    simp only [psiGood, psiBad, ite_eq_right hx, smul_eq_mul, mul_zero, zero_add]
    push_cast
    field_simp [hb]

theorem star_ofReal (r : ℝ) : star (r : ℂ) = r := Complex.conj_ofReal r

/-- Report §8.3.2 — `‖ψ_g‖² = 1` (`M ≥ 1`). -/
theorem psiGood_dot_self : star gp.psiGood ⬝ᵥ gp.psiGood = 1 := by
  have h : ∀ x, star (gp.psiGood x) * gp.psiGood x =
      if gp.oracle.P x then ((Real.sqrt gp.M : ℂ)⁻¹) ^ 2 else 0 := by
    intro x
    by_cases hx : gp.oracle.P x = true
    · simp only [psiGood, ite_eq_left hx, star_inv₀, star_ofReal, sq]
    · simp only [psiGood, ite_eq_right hx, star_zero, mul_zero]
  simp only [dotProduct, Pi.star_apply, h, sum_ite_P, mul_zero, add_zero]
  rw [show (gp.M : ℂ) = (Real.sqrt gp.M : ℂ) ^ 2 by exact_mod_cast gp.sqrtM_sq.symm]
  field_simp [gp.sqrtM_ne]

/-- Report §8.3.2 — `‖ψ_b‖² = 1`, or `ψ_b = 0` when `M = 2ⁿ`. -/
theorem psiBad_dot_self : star gp.psiBad ⬝ᵥ gp.psiBad = 1 ∨ gp.psiBad = 0 := by
  by_cases hb : (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) = 0
  · right
    funext x
    simp [psiBad, hb]
  · left
    have h : ∀ x, star (gp.psiBad x) * gp.psiBad x =
        if gp.oracle.P x then 0 else ((Real.sqrt (2 ^ gp.n - gp.M) : ℂ)⁻¹) ^ 2 := by
      intro x
      by_cases hx : gp.oracle.P x = true
      · simp only [psiBad, ite_eq_left hx, star_zero, mul_zero]
      · simp only [psiBad, ite_eq_right hx, star_inv₀, star_ofReal, sq]
    simp only [dotProduct, Pi.star_apply, h, sum_ite_P, mul_zero, zero_add]
    rw [show ((2 : ℂ) ^ gp.n - gp.M) = (Real.sqrt (2 ^ gp.n - gp.M) : ℂ) ^ 2 by
      exact_mod_cast gp.sqrtB_sq.symm]
    field_simp [hb]

/-- Report §8.3.2 — `⟨ψ_g, ψ_b⟩ = 0`. -/
theorem psiGood_dot_psiBad : star gp.psiGood ⬝ᵥ gp.psiBad = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : gp.oracle.P x = true
  · simp only [Pi.star_apply, psiBad, ite_eq_left hx, mul_zero]
  · simp only [Pi.star_apply, psiGood, ite_eq_right hx, star_zero, zero_mul]

/-- Report §8.2.2 — `sin θ = √(M/2ⁿ)`. -/
theorem sin_θ_eq : Real.sin gp.θ = Real.sqrt (gp.M / 2 ^ gp.n) := by
  rw [GroverParams.θ, Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((gp.M : ℝ) / 2 ^ gp.n)])
    ((Real.sqrt_le_sqrt gp.ratio_le).trans_eq Real.sqrt_one)]

/-- Report §8.2.2 — `cos θ = √(1 − M/2ⁿ)`. -/
theorem cos_θ_eq : Real.cos gp.θ = Real.sqrt (1 - gp.M / 2 ^ gp.n) := by
  rw [GroverParams.θ, Real.cos_arcsin, Real.sq_sqrt (by positivity)]

/-- Report §8.2.2 — `0 ≤ θ ≤ π/2`. -/
theorem θ_mem : 0 ≤ gp.θ ∧ gp.θ ≤ Real.pi / 2 :=
  ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _), Real.arcsin_le_pi_div_two _⟩

/-- Report §8.3.2 — `⟨s|ψ_g⟩ = sin θ`. -/
theorem ketS_dot_psiGood : star (ketS gp.n) ⬝ᵥ gp.psiGood = (Real.sin gp.θ : ℂ) := by
  simp only [dotProduct, Pi.star_apply, ketS_apply, star_ofReal]
  rw [← Finset.mul_sum, sum_psiGood, sin_θ]
  push_cast
  ring

/-- Report §8.3.2 — `⟨s|ψ_b⟩ = cos θ`. -/
theorem ketS_dot_psiBad : star (ketS gp.n) ⬝ᵥ gp.psiBad = (Real.cos gp.θ : ℂ) := by
  simp only [dotProduct, Pi.star_apply, ketS_apply, star_ofReal]
  rw [← Finset.mul_sum, sum_psiBad, cos_θ]
  push_cast
  ring

/-- Report §8.3.2 — `U_P ψ_g = −ψ_g` (from `oracle_reflection`). -/
theorem phaseOracle_psiGood : (phaseOracle gp.oracle.P).val *ᵥ gp.psiGood = -gp.psiGood := by
  rw [oracle_reflection, sub_mulVec, one_mulVec, smul_mulVec]
  funext x
  simp only [goodProj, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, mulVec_diagonal, smul_eq_mul,
    psiGood]
  by_cases hx : gp.oracle.P x = true
  · simp only [ite_eq_left hx]; ring
  · simp only [ite_eq_right hx]; ring

/-- Report §8.3.2 — `U_P ψ_b = ψ_b` (from `oracle_reflection`). -/
theorem phaseOracle_psiBad : (phaseOracle gp.oracle.P).val *ᵥ gp.psiBad = gp.psiBad := by
  rw [oracle_reflection, sub_mulVec, one_mulVec, smul_mulVec]
  funext x
  simp only [goodProj, Pi.sub_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul, psiBad]
  by_cases hx : gp.oracle.P x = true
  · simp only [ite_eq_left hx]; ring
  · simp only [ite_eq_right hx]; ring

end GroverParams

/-- Report §8.2, §8.3.2 — `U_s v = 2⟨s|v⟩ s − v` (`diffU n = 2|s⟩⟨s| − I`, which is
`H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}` by `diffusion_reflection`). -/
theorem diffU_mulVec (n : ℕ) (v : Reg n → ℂ) :
    (diffU n).val *ᵥ v = (2 * (star (ketS n) ⬝ᵥ v)) • ketS n - v := by
  change ((2 : ℂ) • projS n - 1) *ᵥ v = _
  rw [sub_mulVec, one_mulVec, smul_mulVec]
  congr 1
  funext x
  simp only [projS, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, vecMulVec_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

/-! ## Pure states and the basis POVM (Stage 7b item 4, §8.2.3) -/

/-- Report §8.2.3 — a unitary applied to `|0…0⟩⟨0…0|` gives the pure state of
`v = U |0…0⟩`: `U |0⟩⟨0| Uᴴ = |v⟩⟨v|` (matrix level). -/
theorem uConj_ancZero_m {n : ℕ} (U : 𝐔[Reg n]) :
    (U ◃ ancZero n).m =
      vecMulVec (U.val *ᵥ basisVec (zeroReg n)) (star (U.val *ᵥ basisVec (zeroReg n))) := by
  change U.val * (ancZero n).m * U.valᴴ = _
  ext i j
  simp only [Matrix.mul_apply, ancZero_m_apply, vecMulVec_apply, Pi.star_apply, mulVec_basisVec,
    conjTranspose_apply, mul_ite, mul_one, mul_zero]
  simp [ite_and, Finset.sum_ite_eq']
  rfl

/-- Report §8.2.1, §2.1.2 — the basis POVM yields `y` with probability `Re ρ_{yy}`. -/
theorem basisPOVM_measure {n : ℕ} (ρ : MState (Reg n)) (y : Reg n) :
    ((basisPOVM n).measure ρ y : ℝ) = (ρ.m y y).re := by
  show inner ℝ ((basisPOVM n).mats y) ρ.M = _
  rw [HermitianMat.inner_eq_re_trace]
  change RCLike.re ((MState.pure (Ket.basis y)).m * ρ.m).trace = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pure_basis_m_apply, ite_and,
    ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-! ## Figure 8.1 — the statements, proved in Stage 7b -/

/-- Report §8.3.2, §8.3.4 Figure 8.1 ("Reflection geometry: `G` rotates by `2θ` in the 2D
plane", est. 150 lines) — `G = U_s U_P` maps `span{ψ_g, ψ_b}` to itself as the rotation by `2θ`
(coordinates `(sin φ, cos φ) ↦ (sin(φ + 2θ), cos(φ + 2θ))`). Uses `oracle_reflection`,
`diffusion_reflection`, `|s⟩ = sin θ ψ_g + cos θ ψ_b` (from `hM_card`). -/
theorem reflection_geometry (gp : GroverParams) :
    (groverOp gp.oracle.P).val *ᵥ gp.psiGood =
        (Real.cos (2 * gp.θ) : ℂ) • gp.psiGood - (Real.sin (2 * gp.θ) : ℂ) • gp.psiBad ∧
      (groverOp gp.oracle.P).val *ᵥ gp.psiBad =
        (Real.sin (2 * gp.θ) : ℂ) • gp.psiGood + (Real.cos (2 * gp.θ) : ℂ) • gp.psiBad := by
  have hsc : (Real.sin gp.θ : ℂ) ^ 2 + (Real.cos gp.θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq gp.θ
  rw [groverOp, Matrix.UnitaryGroup.mul_val, ← mulVec_mulVec, ← mulVec_mulVec,
    gp.phaseOracle_psiGood, gp.phaseOracle_psiBad, diffU_mulVec, diffU_mulVec, dotProduct_neg,
    gp.ketS_dot_psiGood, gp.ketS_dot_psiBad, gp.ketS_eq, Real.sin_two_mul, Real.cos_two_mul]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  constructor
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (-2 * gp.psiGood x) * hsc
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Report §8.3.2, §8.3.4 Figure 8.1 ("Iteration induction: state after `r` iterations", est.
200 lines) — `G^r |s⟩ = sin((2r+1)θ) ψ_g + cos((2r+1)θ) ψ_b`, by induction on `r` from
`reflection_geometry` and `|s⟩ = sin θ ψ_g + cos θ ψ_b`. -/
theorem iteration_induction (gp : GroverParams) (r : ℕ) :
    (groverOp gp.oracle.P ^ r).val *ᵥ ketS gp.n =
      (Real.sin ((2 * r + 1) * gp.θ) : ℂ) • gp.psiGood +
        (Real.cos ((2 * r + 1) * gp.θ) : ℂ) • gp.psiBad := by
  induction r with
  | zero =>
    simp only [pow_zero, OneMemClass.coe_one, one_mulVec, Nat.cast_zero, mul_zero, zero_add,
      one_mul]
    exact gp.ketS_eq
  | succ k ih =>
    obtain ⟨hg, hb⟩ := reflection_geometry gp
    rw [pow_succ', Matrix.UnitaryGroup.mul_val, ← mulVec_mulVec, ih, mulVec_add, mulVec_smul,
      mulVec_smul, hg, hb,
      show (2 * ((k + 1 : ℕ) : ℝ) + 1) * gp.θ = (2 * k + 1) * gp.θ + 2 * gp.θ by push_cast; ring,
      Real.sin_add, Real.cos_add]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Report §8.2.3, §8.3.2 ("measurement yields a good state with probability
`sin²((2r+1)θ)`"; part of the Figure 8.1 row "Iteration induction", no separate estimate) —
on the data state `G^r H^{⊗n} |0…0⟩`, the basis POVM yields a solution with probability
`sin²((2r+1)θ)`. From `iteration_induction`, `H^{⊗n}|0⟩ = |s⟩` and `hM_card`. -/
theorem terminal_measurement (gp : GroverParams) (r : ℕ) :
    prob ((basisPOVM gp.n).measure ((groverOp gp.oracle.P ^ r * hadamardU gp.n) ◃ ancZero gp.n))
      (fun x => gp.oracle.P x = true) = Real.sin ((2 * r + 1) * gp.θ) ^ 2 := by
  set φ := (2 * (r : ℝ) + 1) * gp.θ with hφ
  have hv : (groverOp gp.oracle.P ^ r * hadamardU gp.n).val *ᵥ basisVec (zeroReg gp.n) =
      (Real.sin φ : ℂ) • gp.psiGood + (Real.cos φ : ℂ) • gp.psiBad := by
    rw [Matrix.UnitaryGroup.mul_val, ← mulVec_mulVec]
    change _ *ᵥ (hadamardMat gp.n *ᵥ _) = _
    rw [hadamardMat_mulVec_zero, iteration_induction]
  have hM : (gp.M : ℝ) ≠ 0 := gp.M_pos.ne'
  unfold prob
  calc _ = ∑ x : Reg gp.n, (if gp.oracle.P x = true then Real.sin φ ^ 2 / gp.M else 0) :=
        Finset.sum_congr rfl fun x _ => ?_
    _ = Real.sin φ ^ 2 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, gp.hM_card,
          nsmul_eq_mul]
        field_simp
  by_cases hx : gp.oracle.P x = true
  · rw [ite_eq_left hx, ite_eq_left hx, basisPOVM_measure, uConj_ancZero_m, vecMulVec_apply, hv]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, GroverParams.psiGood,
      GroverParams.psiBad, ite_eq_left hx, mul_zero, add_zero]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, GroverParams.star_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    rw [show Real.sin φ * (Real.sqrt gp.M)⁻¹ * (Real.sin φ * (Real.sqrt gp.M)⁻¹) =
      Real.sin φ ^ 2 / (Real.sqrt gp.M) ^ 2 by ring, gp.sqrtM_sq]
  · rw [ite_eq_right hx, ite_eq_right hx]

/-- Report §8.2.4, §8.3.2, §6.3.2 — **the realization conjunct**: the Grover channel of the
synthesized circuit `(0, 1 − sin²((2r+1)θ))`-realizes the search spec under the basis POVM,
within its own measured grade (decision 1). The grade part is `le_rfl`; for the probability
part (Stage 7b item 5), `grover_ancRestore` (traced, `AncRestore.traced`) reduces the channel
output on the unique input `encode ()` to `G^r H^{⊗n} |0⟩⟨0| (G^r H^{⊗n})ᴴ` (the replacement
channel ignores its input), then `terminal_measurement`. §6.3.2 invokes Theorem 3.3a once, at
the terminal measurement; in this formalization the terminal measurement is the decoding POVM
of Definition 2.2 inside `RealizesExact`, so no separate composition step is needed. -/
theorem grover_realizes (gp : GroverParams) (D : DiffusionCert gp.n) (r : ℕ) {C : Circuit}
    (hC : groverCircuit gp.oracle.N gp.n r = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
      (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) := by
  refine ⟨le_rfl, fun u _ => ?_⟩
  have hchan : (groverChannel gp.n C).chan (encode u) =
      (groverOp gp.oracle.P ^ r * hadamardU gp.n) ◃ ancZero gp.n := by
    simp only [groverChannel, GradedChannel.traceAnc, CPTPMap.compose_eq,
      CPTPMap.replacement_apply, CPTPMap.traceRight_eq_MState_traceRight]
    exact (grover_ancRestore gp.oracle D hC).traced (ancZero gp.n)
  rw [hchan]
  change _ ≤ prob _ (fun x => gp.oracle.P x = true)
  rw [terminal_measurement, sub_sub_cancel]

/-- Report §5.2.4, §8.2.4, §8.3.1, §8.3.4 Figure 8.1 ("Parametric theorem: Realization ∧
Restoration", est. 50 lines) — **the Grover parametric lemma**: for every `r` (decision 2), the
synthesized Grover circuit `C` (V1 diffusion; the MCZ certified by `D`) realizes the search spec
with `δ = 1 − sin²((2r+1)θ)` within its measured grade `Synthesis.grade C` (decision 1), and
restores its ancillae while applying `U = G^r H^{⊗n}` on the data register. -/
theorem grover_parametric_lemma (gp : GroverParams) (D : DiffusionCert gp.n) (r : ℕ)
    {C : Circuit} (hC : groverCircuit gp.oracle.N gp.n r = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
        (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) ∧
      AncRestore gp.n C.nAnc C (groverOp gp.oracle.P ^ r * hadamardU gp.n) :=
  ⟨grover_realizes gp D r hC, grover_ancRestore gp.oracle D hC⟩

/-- Report §8.2.4, §8.3.2 (Stage 12a) — the realization conjunct for either diffusion shape
(the proof of `grover_realizes` with `grover_ancRestore_shape`). -/
theorem grover_realizes_shape (gp : GroverParams) (s : DiffusionShape) (r : ℕ) {C : Circuit}
    (hC : groverCircuit gp.oracle.N gp.n r none s = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
      (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) := by
  refine ⟨le_rfl, fun u _ => ?_⟩
  have hchan : (groverChannel gp.n C).chan (encode u) =
      (groverOp gp.oracle.P ^ r * hadamardU gp.n) ◃ ancZero gp.n := by
    simp only [groverChannel, GradedChannel.traceAnc, CPTPMap.compose_eq,
      CPTPMap.replacement_apply, CPTPMap.traceRight_eq_MState_traceRight]
    exact (grover_ancRestore_shape gp.oracle s hC).traced (ancZero gp.n)
  rw [hchan]
  change _ ≤ prob _ (fun x => gp.oracle.P x = true)
  rw [terminal_measurement, sub_sub_cancel]

/-- Report §5.2.4, §8.3.4 Figure 8.1 (Stage 12a) — the Grover parametric lemma for either
diffusion shape `s` (`.tree`, the default, or `.chain`, the Stage 5b construction): same
conclusion as `grover_parametric_lemma`; the MCZ is certified from the circuit itself. -/
theorem grover_parametric_lemma_shape (gp : GroverParams) (s : DiffusionShape) (r : ℕ)
    {C : Circuit} (hC : groverCircuit gp.oracle.N gp.n r none s = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
        (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) ∧
      AncRestore gp.n C.nAnc C (groverOp gp.oracle.P ^ r * hadamardU gp.n) :=
  ⟨grover_realizes_shape gp s r hC, grover_ancRestore_shape gp.oracle s hC⟩

/-- Report §5.2.4, §8.3.4 Figure 8.1 (Stage 11a item 3) — `grover_parametric_lemma` without the
`DiffusionCert` argument: `groverCircuit … = .ok C` already synthesized the MCZ (since Stage 12a
of the balanced tree `treeNet n`), which `DiffusionCert.ofShape` certifies (`hWF` by
`synthesizeOracle_WF`). Same conclusion. -/
theorem grover_parametric_lemma' (gp : GroverParams) (r : ℕ)
    {C : Circuit} (hC : groverCircuit gp.oracle.N gp.n r = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
        (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) ∧
      AncRestore gp.n C.nAnc C (groverOp gp.oracle.P ^ r * hadamardU gp.n) :=
  grover_parametric_lemma_shape gp .tree r hC

/-! ## The instance trig fact (decision 3) -/

/-- Report §8.2.3, decision 3 — `sin²θ = 1/8 ⇒ sin²(5θ) = 121/128`: with `s = sin θ`,
`c = cos θ`, `sin 5θ = sin 3θ cos 2θ + cos 3θ sin 2θ = (11/4) s` modulo `s² = 1/8`,
`s² + c² = 1`. The range hypothesis on `θ` is not needed (`sin² 5θ` is a polynomial in
`sin² θ`); it is kept in the statement as the task gives it. -/
theorem sin_sq_five_mul {θ : ℝ} (h : Real.sin θ ^ 2 = 1 / 8)
    (_hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) : Real.sin (5 * θ) ^ 2 = 121 / 128 := by
  have h5 : Real.sin (5 * θ) =
      Real.sin (3 * θ) * Real.cos (2 * θ) + Real.cos (3 * θ) * Real.sin (2 * θ) := by
    rw [← Real.sin_add]
    ring_nf
  have hc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h11 : Real.sin (5 * θ) = 11 / 4 * Real.sin θ := by
    rw [h5, Real.sin_three_mul, Real.cos_three_mul, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination Real.sin θ * (16 * Real.sin θ ^ 2 - 18) * h +
      Real.sin θ * (16 - 24 * Real.sin θ ^ 2 + 8 * (Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1)) * hc
  rw [h11]
  linear_combination (121 / 16) * h

end

end CQRV.Grover

end
