module

public import CQRV.Grover.Restore
public import CQRV.Realizability.Realizes

/-!
# CQRV.Grover.Lemma

Report §5.2.4 (revised Lean sketch: `GroverParams`, `hM_card` a hypothesis), §8.2 (circuit
family, `p_succ = sin²((2r+1)θ)`), §8.2.4 (realization ∧ restoration), §8.3.2 (reflection
geometry), §8.3.4 / Figure 8.1 (lemma dependency graph), §6.3.2 (Theorem 3.3a once, at the
terminal measurement) — the Grover parametric lemma (Stage 7a; DECISIONS.md 2026-10-24,
Stage 7a decisions 1–5).

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

/-! ## Figure 8.1 — the open statements (Stage 7b/7c) -/

/-- Report §8.3.2, §8.3.4 Figure 8.1 ("Reflection geometry: `G` rotates by `2θ` in the 2D
plane", est. 150 lines) — `G = U_s U_P` maps `span{ψ_g, ψ_b}` to itself as the rotation by `2θ`
(coordinates `(sin φ, cos φ) ↦ (sin(φ + 2θ), cos(φ + 2θ))`). Uses `oracle_reflection`,
`diffusion_reflection`, `|s⟩ = sin θ ψ_g + cos θ ψ_b` (from `hM_card`). -/
theorem reflection_geometry (gp : GroverParams) :
    (groverOp gp.oracle.P).val *ᵥ gp.psiGood =
        (Real.cos (2 * gp.θ) : ℂ) • gp.psiGood - (Real.sin (2 * gp.θ) : ℂ) • gp.psiBad ∧
      (groverOp gp.oracle.P).val *ᵥ gp.psiBad =
        (Real.sin (2 * gp.θ) : ℂ) • gp.psiGood + (Real.cos (2 * gp.θ) : ℂ) • gp.psiBad := by
  sorry

/-- Report §8.3.2, §8.3.4 Figure 8.1 ("Iteration induction: state after `r` iterations", est.
200 lines) — `G^r |s⟩ = sin((2r+1)θ) ψ_g + cos((2r+1)θ) ψ_b`, by induction on `r` from
`reflection_geometry` and `|s⟩ = sin θ ψ_g + cos θ ψ_b`. -/
theorem iteration_induction (gp : GroverParams) (r : ℕ) :
    (groverOp gp.oracle.P ^ r).val *ᵥ ketS gp.n =
      (Real.sin ((2 * r + 1) * gp.θ) : ℂ) • gp.psiGood +
        (Real.cos ((2 * r + 1) * gp.θ) : ℂ) • gp.psiBad := by
  sorry

/-- Report §8.2.3, §8.3.2 ("measurement yields a good state with probability
`sin²((2r+1)θ)`"; part of the Figure 8.1 row "Iteration induction", no separate estimate) —
on the data state `G^r H^{⊗n} |0…0⟩`, the basis POVM yields a solution with probability
`sin²((2r+1)θ)`. From `iteration_induction`, `H^{⊗n}|0⟩ = |s⟩` and `hM_card`. -/
theorem terminal_measurement (gp : GroverParams) (r : ℕ) :
    prob ((basisPOVM gp.n).measure ((groverOp gp.oracle.P ^ r * hadamardU gp.n) ◃ ancZero gp.n))
      (fun x => gp.oracle.P x = true) = Real.sin ((2 * r + 1) * gp.θ) ^ 2 := by
  sorry

/-- Report §8.2.4, §8.3.2, §6.3.2 — **the realization conjunct**: the Grover channel of the
synthesized circuit `(0, 1 − sin²((2r+1)θ))`-realizes the search spec under the basis POVM,
within its own measured grade (decision 1). The grade part is `le_rfl`; the probability part
is open (Stage 7c): `grover_ancRestore` (traced, `AncRestore.traced`) reduces the channel
output to `G^r H^{⊗n} |0⟩⟨0| (G^r H^{⊗n})ᴴ`, then `terminal_measurement` — Theorem 3.3a enters
once, at this terminal measurement (§6.3.2). -/
theorem grover_realizes (gp : GroverParams) (D : DiffusionCert gp.n) (r : ℕ) {C : Circuit}
    (hC : groverCircuit gp.oracle.N gp.n r = .ok C) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
      (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) := by
  refine ⟨le_rfl, fun u _ => ?_⟩
  sorry

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
