module

public import CQRV.Realizability.Diamond

/-!
# CQRV.Noise.Perturb

Report §2.3.2 (Theorem 3.3b, `dist⋄`), §6.6; PHASE2_SPEC §C.4 (2); STAGE27_TASK.md 27a N2 — the
perturbation bound for a composition of step channels on one space `A`:

* `diamondDist_precompose_le`: pre-composing both channels with the same channel `Λ : A → A` does not
  increase the diamond distance (the reference system has the input's dimension on both sides, so
  `(Λ ⊗ id) ρ` is again a state in the supremum's range; post-composition is Stage 13b's
  `diamondDist_compose_le`);
* `steps`: the composition of a list of channels on `A`, first element applied first;
* `diamondDist_steps_le`: if `‖Ψᵢ − Φᵢ‖⋄ ≤ ηᵢ` for every step, the compositions are within `Σ ηᵢ`
  (the triangle inequality, one step at a time);
* `mix p Φ Φ'`: the convex combination `(1 − p) • Φ + p • Φ'` as a `CPTPMap` (Physlib's convex
  structure on `CPTPMap` is `Mixable` through Choi matrices, `CPTPMap.instMixable`; `mix` is given by
  its linear map, which the bound needs, and `mix_choi` is the bridge to that structure);
* `diamondDist_mix_le`: `‖mix p Φ Φ' − Φ‖⋄ ≤ 2p` — **the stochastic premise** (PHASE2_SPEC §C.4 (2),
  (P-stoch)): with probability at least `1 − p` the step is ideal, otherwise an arbitrary channel on
  the whole register; stated on the full register, so no stability under tensoring is needed.
-/

@[expose] public section

noncomputable section

namespace CQRV

open scoped ComplexOrder

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Pre-composition -/

/-- Report §2.3.2; PHASE2_SPEC §C.4 (2) — **`diamondDist_precompose_le`**: pre-composing with the
same channel `Λ : A → A` does not increase the diamond distance. `(Λ ⊗ id) ρ` is a state on `A × A`,
so it lies in the supremum's range. -/
theorem diamondDist_precompose_le (Λ : CPTPMap A A) (Ψ Φ : CPTPMap A B) :
    diamondDist (Ψ ∘ₘ Λ) (Φ ∘ₘ Λ) ≤ diamondDist Ψ Φ :=
  Real.iSup_le (fun ρ => by
    rw [prod_id_compose, prod_id_compose, CPTPMap.compose_eq, CPTPMap.compose_eq]
    exact le_ciSup (diamondDist_bddAbove Ψ Φ) ((Λ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ))
    (diamondDist_nonneg _ _)

/-! ## Compositions of step channels -/

/-- PHASE2_SPEC §C.4 (2) — the composition of a list of channels on one space, **first element
applied first**: `steps [Φ₀, Φ₁, …] = … ∘ Φ₁ ∘ Φ₀`. -/
def steps : List (CPTPMap A A) → CPTPMap A A
  | [] => CPTPMap.id
  | Φ :: Φs => steps Φs ∘ₘ Φ

@[simp] theorem steps_nil : steps ([] : List (CPTPMap A A)) = CPTPMap.id := rfl

@[simp] theorem steps_cons (Φ : CPTPMap A A) (Φs : List (CPTPMap A A)) :
    steps (Φ :: Φs) = steps Φs ∘ₘ Φ := rfl

theorem steps_append (Φs Ψs : List (CPTPMap A A)) :
    steps (Φs ++ Ψs) = steps Ψs ∘ₘ steps Φs := by
  induction Φs with
  | nil => simp [CPTPMap.compose_id]
  | cons Φ Φs ih => simp [ih, CPTPMap.compose_assoc]

theorem steps_replicate_id (k : ℕ) : steps (List.replicate k (CPTPMap.id : CPTPMap A A)) = CPTPMap.id := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, CPTPMap.compose_id]

/-- Report §2.3.2, Theorem 3.3b; PHASE2_SPEC §C.4 (2) — **`diamondDist_steps_le`**, list form: for
a list of triples (ideal step, noisy step, bound) with `‖Ψᵢ − Φᵢ‖⋄ ≤ ηᵢ`, the two compositions are
within `Σ ηᵢ`. Each step: `‖Ψ' ∘ Ψ − Φ' ∘ Φ‖⋄ ≤ ‖Ψ' ∘ Ψ − Ψ' ∘ Φ‖⋄ + ‖Ψ' ∘ Φ − Φ' ∘ Φ‖⋄`, the
first by `diamondDist_compose_le`, the second by `diamondDist_precompose_le`. -/
theorem diamondDist_steps_le_list (L : List (CPTPMap A A × CPTPMap A A × ℝ))
    (h : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    diamondDist (steps (L.map (·.2.1))) (steps (L.map (·.1))) ≤ (L.map (·.2.2)).sum := by
  induction L with
  | nil => simp [diamondDist_self]
  | cons t L ih =>
    simp only [List.map_cons, steps_cons, List.sum_cons]
    have ht := h t List.mem_cons_self
    have hL := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    have htri := diamondDist_triangle (steps (L.map (·.2.1)) ∘ₘ t.2.1)
      (steps (L.map (·.2.1)) ∘ₘ t.1) (steps (L.map (·.1)) ∘ₘ t.1)
    have h₁ := diamondDist_compose_le (steps (L.map (·.2.1))) t.2.1 t.1
    have h₂ := diamondDist_precompose_le t.1 (steps (L.map (·.2.1))) (steps (L.map (·.1)))
    linarith

/-- **`diamondDist_steps_le`**, indexed form: steps `Φ Ψ : Fin k → CPTPMap A A` with
`‖Ψ i − Φ i‖⋄ ≤ η i` compose to channels within `∑ i, η i`. -/
theorem diamondDist_steps_le {k : ℕ} (Φ Ψ : Fin k → CPTPMap A A) (η : Fin k → ℝ)
    (h : ∀ i, diamondDist (Ψ i) (Φ i) ≤ η i) :
    diamondDist (steps (List.ofFn Ψ)) (steps (List.ofFn Φ)) ≤ ∑ i, η i := by
  have := diamondDist_steps_le_list (List.ofFn fun i => (Φ i, Ψ i, η i))
    (fun t ht => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ht
      exact h i)
  simpa [List.map_ofFn, Function.comp_def, List.sum_ofFn] using this

/-! ## The stochastic premise -/

/-- PHASE2_SPEC §C.4 (2), (P-stoch) — the convex combination `(1 − p) • Φ + p • Φ'` of two
channels, as a channel: with probability at least `1 − p` the ideal step `Φ`, otherwise an arbitrary
channel `Φ'` on the whole register. Given by its linear map (complete positivity and trace
preservation are closed under convex combinations); `p : Prob` carries `0 ≤ p ≤ 1`. -/
def mix (p : Prob) (Φ Φ' : CPTPMap A B) : CPTPMap A B where
  toLinearMap := ((1 - (p : ℝ) : ℝ) : ℂ) • Φ.map + ((p : ℝ) : ℂ) • Φ'.map
  cp := (Φ.cp.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr Prob.coe_le_one))).add
    (Φ'.cp.smul (Complex.zero_le_real.mpr Prob.zero_le_coe))
  TP := by
    intro x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul,
      Φ.TP x, Φ'.TP x]
    push_cast
    ring

omit [DecidableEq B] in
theorem mix_map (p : Prob) (Φ Φ' : CPTPMap A B) :
    (mix p Φ Φ').map = ((1 - (p : ℝ) : ℝ) : ℂ) • Φ.map + ((p : ℝ) : ℂ) • Φ'.map := rfl

/-- The matrix of `mix p Φ Φ'` on a state: `(1 − p) • Φ ρ + p • Φ' ρ`. -/
theorem mix_apply_m (p : Prob) (Φ Φ' : CPTPMap A B) (ρ : MState A) :
    (mix p Φ Φ' ρ).m = ((1 - (p : ℝ) : ℝ) : ℂ) • (Φ ρ).m + ((p : ℝ) : ℂ) • (Φ' ρ).m := by
  simp only [CPTPMap.mat_coe_eq_apply_mat, mix_map, LinearMap.add_apply, LinearMap.smul_apply]

omit [DecidableEq B] in
/-- The bridge to Physlib's convex structure on channels (`CPTPMap.instMixable`, through Choi
matrices): the Choi matrix of `mix p Φ Φ'` is the convex combination of the Choi matrices. -/
theorem mix_choi (p : Prob) (Φ Φ' : CPTPMap A B) :
    (mix p Φ Φ').choi = ((1 - (p : ℝ) : ℝ) : ℂ) • Φ.choi + ((p : ℝ) : ℂ) • Φ'.choi := by
  simp only [CPTPMap.choi]
  change MatrixMap.choi_equiv (mix p Φ Φ').map = _
  rw [mix_map, map_add, map_smul, map_smul]
  rfl

omit [DecidableEq B] in
/-- `mix p Φ Φ'` is Physlib's `Mixable.mix_ab` with weights `1 − p` on `Φ` and `p` on `Φ'`. -/
theorem mix_eq_mix_ab (p : Prob) (Φ Φ' : CPTPMap A B) :
    mix p Φ Φ' = Mixable.mix_ab (a := 1 - (p : ℝ)) (b := (p : ℝ))
      (sub_nonneg.mpr Prob.coe_le_one) Prob.zero_le_coe (by ring) Φ Φ' := by
  apply CPTPMap.choi_ext
  rw [mix_choi]
  exact (Mixable.to_U_of_mkT (T := CPTPMap A B) _).symm

omit [DecidableEq B] in
/-- `(mix p Φ Φ') ⊗ id = mix p (Φ ⊗ id) (Φ' ⊗ id)` at the level of linear maps (the Kronecker
product of maps is bilinear). -/
theorem mix_prod_id_map (p : Prob) (Φ Φ' : CPTPMap A B) :
    ((mix p Φ Φ') ⊗ᶜᵖ CPTPMap.id (dIn := A)).map =
      ((1 - (p : ℝ) : ℝ) : ℂ) • (Φ ⊗ᶜᵖ CPTPMap.id (dIn := A)).map +
        ((p : ℝ) : ℂ) • (Φ' ⊗ᶜᵖ CPTPMap.id (dIn := A)).map := by
  change MatrixMap.kron (mix p Φ Φ').map _ = _
  rw [mix_map, MatrixMap.add_kron, MatrixMap.smul_kron, MatrixMap.smul_kron]
  rfl

/-- Report §2.3.2; PHASE2_SPEC §C.4 (2) — **`diamondDist_mix_le`**: `‖mix p Φ Φ' − Φ‖⋄ ≤ 2p`. On
every input `ρ` of the stabilized distance, `(mix ⊗ id) ρ − (Φ ⊗ id) ρ = p • ((Φ' ⊗ id) ρ − (Φ ⊗ id) ρ)`,
whose trace norm is at most `2p` (two states are at trace distance at most 1). -/
theorem diamondDist_mix_le (p : Prob) (Φ Φ' : CPTPMap A B) :
    diamondDist (mix p Φ Φ') Φ ≤ 2 * (p : ℝ) :=
  Real.iSup_le (fun ρ => by
    have hm : ((mix p Φ Φ' ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ).m =
        ((1 - (p : ℝ) : ℝ) : ℂ) • ((Φ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ).m +
          ((p : ℝ) : ℂ) • ((Φ' ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ).m := by
      rw [CPTPMap.mat_coe_eq_apply_mat, mix_prod_id_map, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply]
      rfl
    set X := (Φ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ
    set Y := (Φ' ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ
    have hm' : ((mix p Φ Φ' ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ).m - X.m = ((p : ℝ) : ℂ) • (Y.m - X.m) := by
      rw [hm]; push_cast; module
    have h1 : TrDistance Y X ≤ 1 := trDistance_le_one Y X
    simp only [TrDistance] at h1 ⊢
    rw [hm', Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg Prob.zero_le_coe]
    nlinarith [Prob.zero_le_coe (p := p), Matrix.traceNorm_nonneg (Y.m - X.m)])
    (mul_nonneg zero_le_two Prob.zero_le_coe)

end CQRV

end
