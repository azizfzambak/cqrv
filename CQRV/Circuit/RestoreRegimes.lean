module

public import CQRV.Circuit.RestoreAlgebra

/-!
# CQRV.Circuit.RestoreRegimes

Stage 23b (PHASE2_SPEC §B.2; report §6.2.1, §6.2.3, §6.2.4; Track B) — **the three regimes of
restoration**: clean (`AncRestore`, Stage 6b), dirty and conditionally clean.

* **P0. States span the matrices.** `span_states_eq_top`: the density matrices span
  `Matrix d d ℂ` (the matrix unit `E_ij` is a combination of four pure states, the polarization
  identity); `span_prodStates_eq_top`: the product states `ρ ⊗ σ` span the matrices of the
  register. So a channel equality on product states is a channel equality on every matrix
  (`AncRestoreDirty.all`).
* **P1. Dirty restoration.** `AncRestoreDirty n a C U`: on every product `ρ ⊗ σ` the circuit
  outputs `(U ρ Uᴴ) ⊗ σ` — the ancillae are returned in whatever state they were given.
  `ancRestoreDirty_of_kraus` (every Kraus operator is `l_c · (U ⊗ 1)`), `ancRestoreDirty_of_unitary`,
  the laws `toClean`, `comp`, the dirty phase gadget `dirtyGadget` (the toggle-detection form: the
  dirty ancilla is used twice, so its value cancels), and **`reset_not_dirty`**: a circuit that ends
  with the reset `measure t j; (ifBit j O); ifBit j (X t)` on an ancilla `t` is not dirty restoring
  for any `U`, because `t` reads 0 in every branch — the theorem behind "dirty ancillae cannot use
  MBU" (report §6.2.3); `mbuCircuit_not_dirty` is the corollary.
* **P2. Conditionally clean restoration.** `condSubspace cond`, the projector onto
  `V_cond = span{|x, w⟩ : cond x → w = 0}`; `AncRestoreCond n a C U cond`: on every state
  supported on `V_cond` the channel acts as `Ad(U ⊗ 1)`. The hierarchy
  `AncRestoreDirty.toCond` (dirty is conditionally clean for every `cond`),
  `AncRestoreCond.mono` (a weaker condition is a stronger statement), `AncRestoreCond.toClean`
  (for every `cond`: `V_true = {w = 0} ⊆ V_cond`), `AncRestoreCond.toDirty` (`cond ≡ false`:
  `V = everything`), `AncRestoreCond.comp` (when `U₁ ⊗ 1` maps `V_cond` into `V_cond'`, in
  particular for a diagonal `U₁`, `condSubspace_mul_diag_kron`), `ancRestoreCond_of_unitary`. The
  instance `czCondCircuit = CZ(x0, anc 0)`: conditionally clean with `U = 1` under `cond = x0`
  (`czCond_cond`), clean (`czCond_clean`), **not dirty** (`czCond_not_dirty`: on `|1⟩ ⊗ |+⟩` the
  ancilla comes out as `|−⟩`), hence not conditionally clean under `cond ≡ false`
  (`czCond_not_cond_false`). Both inclusions of the hierarchy are strict.
* **R2 (REVIEW_RESPONSE_1 row 2). Clean ⇔ Cond(true), proved.** `supportFactor`: a state
  supported on `V_true` (`P ω P = ω` for `P = ancProj`) is `traceRight ω ⊗ᴹ ancZero a` — entrywise
  (`supportFactor_m`, through `ancProj_mul_mul_apply`) every entry with `w ≠ 0` or `v ≠ 0`
  vanishes and the partial trace at `(x, y)` is the single entry `((x, 0), (y, 0))`. Hence
  `AncRestore.toCond_true` (the converse of `AncRestoreCond.toClean` at `cond ≡ true`) and
  `ancRestoreCond_true_iff`: **the clean regime is the conditional regime under the trivial
  condition**, the weakest of the conditional statements (`AncRestoreCond.mono`). The regime list is
  therefore dirty ⇒ conditionally clean under `cond` ⇒ Cond(true) = clean, with the first
  inclusion strict (`czCond_not_dirty`).
* **The KG bridge** lives in `CQRV/Grover/KGRegime.lean` (`Grover.KG.Inv.cond_value`): a
  `Circuit` module does not import `Grover`.

P3 (commutation on disjoint qubits) is not in this module: it needs a split of the data register
like Stage 23a's split of the ancillae (see DECISIONS.md).

Conventions of Stage 22: `(-1 : ℂ)`, `by_cases h : … = true`, matrix statements through
`channelDenote_m` and the Kraus operators.
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix CQRV.Synthesis
open scoped MState Kronecker

/-! ## P0 — states span the matrices -/

section Span

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The entries of a pure state: `|ψ⟩⟨ψ|_{ij} = ψ_i conj(ψ_j)`. -/
theorem pure_m_apply (ψ : Ket d) (i j : d) :
    (MState.pure ψ).m i j = ψ i * (starRingEnd ℂ) (ψ j) := by
  simp [MState.m, MState.pure, HermitianMat.mat_mk, Matrix.vecMulVec_apply, Bra.eq_conj,
    Ket.coe_fun_eq]

/-- The entries of a basis state `|y⟩⟨y|`. -/
theorem pureBasis_m_apply (y i j : d) :
    (MState.pure (Ket.basis y)).m i j = if i = y ∧ j = y then 1 else 0 := by
  simp only [MState.m, MState.pure, Ket.basis, HermitianMat.mat_mk, Matrix.vecMulVec_apply,
    Bra.eq_conj, Ket.coe_fun_eq]
  by_cases hi : i = y
  · subst hi
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  · simp [hi, Ne.symm hi]

/-- The superposition `(|i⟩ + θ |j⟩)/√2` for `i ≠ j` and `‖θ‖ = 1`. -/
def ketPair (i j : d) (hij : i ≠ j) (θ : ℂ) (hθ : ‖θ‖ = 1) : Ket d where
  vec k := if k = i then ((Real.sqrt 2)⁻¹ : ℂ) else if k = j then ((Real.sqrt 2)⁻¹ : ℂ) * θ else 0
  normalized' := by
    have hf : ∀ k, ‖(if k = i then ((Real.sqrt 2)⁻¹ : ℂ) else
        if k = j then ((Real.sqrt 2)⁻¹ : ℂ) * θ else 0)‖ ^ 2 =
        (if k = i then (1 / 2 : ℝ) else 0) + (if k = j then (1 / 2 : ℝ) else 0) := by
      intro k
      by_cases hk : k = i
      · subst hk; simp [hij]
      · by_cases hk' : k = j
        · subst hk'; simp [hk, hθ]
        · simp [hk, hk']
    simp only [hf, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num

theorem ketPair_apply (i j : d) (hij : i ≠ j) (θ : ℂ) (hθ : ‖θ‖ = 1) (k : d) :
    ketPair i j hij θ hθ k =
      if k = i then ((Real.sqrt 2)⁻¹ : ℂ) else if k = j then ((Real.sqrt 2)⁻¹ : ℂ) * θ else 0 := rfl

/-- The real amplitude `1/√2` is its own conjugate, and squares to `1/2`. -/
theorem conj_invSqrtTwo : (starRingEnd ℂ) ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [map_inv₀, Complex.conj_ofReal]

/-- **The polarization identity**: the matrix unit `E_ij` lies in the span of the density
matrices — `E_ii = |i⟩⟨i|`, and for `i ≠ j`
`E_ij = ½ (P₊ − P₋) + (i/2) (P_{+i} − P_{−i})` with `P_θ = |ψ_θ⟩⟨ψ_θ|`, `ψ_θ = (|i⟩ + θ|j⟩)/√2`. -/
theorem single_mem_span_states (i j : d) :
    Matrix.single i j (1 : ℂ) ∈ Submodule.span ℂ (Set.range (MState.m (d := d))) := by
  by_cases hij : i = j
  · subst hij
    have : Matrix.single i i (1 : ℂ) = (MState.pure (Ket.basis i)).m := by
      ext k l
      rw [pureBasis_m_apply, Matrix.single_apply]
      by_cases hk : k = i
      · subst hk
        by_cases hl : l = k
        · subst hl; simp
        · simp [hl, Ne.symm hl]
      · simp [hk, Ne.symm hk]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have hji : j ≠ i := Ne.symm hij
    have hP : ∀ (θ : ℂ) (hθ : ‖θ‖ = 1) (k l : d), (MState.pure (ketPair i j hij θ hθ)).m k l =
        (if k = i then ((Real.sqrt 2)⁻¹ : ℂ) else if k = j then ((Real.sqrt 2)⁻¹ : ℂ) * θ else 0) *
          (starRingEnd ℂ) (if l = i then ((Real.sqrt 2)⁻¹ : ℂ) else
            if l = j then ((Real.sqrt 2)⁻¹ : ℂ) * θ else 0) := fun θ hθ k l => by
      rw [pure_m_apply, ketPair_apply, ketPair_apply]
    have key : Matrix.single i j (1 : ℂ) =
        (1 / 2 : ℂ) • ((MState.pure (ketPair i j hij 1 (by simp))).m -
            (MState.pure (ketPair i j hij (-1) (by simp))).m) +
          (Complex.I / 2) • ((MState.pure (ketPair i j hij Complex.I (by simp))).m -
            (MState.pure (ketPair i j hij (-Complex.I) (by simp))).m) := by
      ext k l
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, hP, smul_eq_mul,
        Matrix.single_apply]
      by_cases hk : k = i
      · subst hk
        by_cases hl : l = k
        · subst hl
          simp [hji]
        · by_cases hl' : l = j
          · subst hl'
            simp only [hji, ite_true, ite_false, and_self, map_mul, conj_invSqrtTwo, map_neg,
              Complex.conj_I, mul_one, mul_neg, neg_neg]
            linear_combination (-2 : ℂ) * invSqrtTwo_mul_self +
              (((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ)) * Complex.I_sq
          · simp [hl, hl', Ne.symm hl']
      · by_cases hk' : k = j
        · subst hk'
          by_cases hl : l = i
          · subst hl
            simp only [hij, hji, ite_true, ite_false, and_self, conj_invSqrtTwo, mul_one, mul_neg,
              neg_mul]
            linear_combination (-(((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ))) * Complex.I_sq
          · by_cases hl' : l = k
            · subst hl'
              simp only [hij, hji, ite_true, ite_false, and_true, map_mul, conj_invSqrtTwo,
                map_neg, Complex.conj_I, mul_one, mul_neg, neg_mul, neg_neg]
              ring
            · simp [hl, hl', Ne.symm hl']
        · simp [hk, hk', Ne.symm hk]
    rw [key]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_))
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)) <;>
      exact Submodule.subset_span ⟨_, rfl⟩

/-- PHASE2_SPEC §B.2 (23b) — **the density matrices span the matrices.** -/
theorem span_states_eq_top : Submodule.span ℂ (Set.range (MState.m (d := d))) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (single_mem_span_states i j)

/-- PHASE2_SPEC §B.2 (23b) — **the product states span the matrices of a two-part register**:
`E_{(i₁,i₂),(j₁,j₂)} = E_{i₁j₁} ⊗ E_{i₂j₂}`, and each factor is a combination of states. -/
theorem span_prodStates_eq_top {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂]
    [DecidableEq d₂] :
    Submodule.span ℂ (Set.range fun p : MState d₁ × MState d₂ => (p.1 ⊗ᴹ p.2).m) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  have h1 : Matrix.single i₁ j₁ (1 : ℂ) ∈ Submodule.span ℂ (Set.range (MState.m (d := d₁))) := by
    rw [span_states_eq_top]; exact Submodule.mem_top
  have h2 : Matrix.single i₂ j₂ (1 : ℂ) ∈ Submodule.span ℂ (Set.range (MState.m (d := d₂))) := by
    rw [span_states_eq_top]; exact Submodule.mem_top
  have hk := Submodule.apply_mem_map₂ (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) h1 h2
  rw [Submodule.map₂_span_span] at hk
  have hsub : Set.image2 (fun A B => Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ) A B)
      (Set.range (MState.m (d := d₁))) (Set.range (MState.m (d := d₂))) ⊆
      Set.range fun p : MState d₁ × MState d₂ => (p.1 ⊗ᴹ p.2).m := by
    rw [Set.image2_subset_iff]
    rintro _ ⟨ρ, rfl⟩ _ ⟨σ, rfl⟩
    exact ⟨(ρ, σ), rfl⟩
  have hmem := Submodule.span_mono hsub hk
  have heq : Matrix.single (i₁, i₂) (j₁, j₂) (M (i₁, i₂) (j₁, j₂)) =
      M (i₁, i₂) (j₁, j₂) • Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)
        (Matrix.single i₁ j₁ (1 : ℂ)) (Matrix.single i₂ j₂ (1 : ℂ)) := by
    change _ = _ • (Matrix.single i₁ j₁ (1 : ℂ) ⊗ₖ Matrix.single i₂ j₂ (1 : ℂ))
    rw [Matrix.single_kronecker_single, mul_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

/-- `M ↦ K M Kᴴ` as a linear map. -/
def adMap (K : Matrix d d ℂ) : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  (LinearMap.mulRight ℂ Kᴴ).comp (LinearMap.mulLeft ℂ K)

theorem adMap_apply (K M : Matrix d d ℂ) : adMap K M = K * M * Kᴴ := rfl

end Span

/-! ## P1 — dirty restoration -/

section Dirty

variable {n a : ℕ}

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **dirty restoration**: on every data state `ρ` and
every ancilla state `σ`, the circuit outputs `(U ρ Uᴴ) ⊗ σ` — the ancillae are returned in the
state they were given, whatever it was. -/
def AncRestoreDirty (n a : ℕ) (C : Circuit) (U : 𝐔[Reg n]) : Prop :=
  ∀ (ρ : MState (Reg n)) (σ : MState (Reg a)), channelDenote n a C (ρ ⊗ᴹ σ) = (U ◃ ρ) ⊗ᴹ σ

/-- Dirty restoration implies clean restoration (`σ := |0…0⟩⟨0…0|`). -/
theorem AncRestoreDirty.toClean {C : Circuit} {U : 𝐔[Reg n]} (h : AncRestoreDirty n a C U) :
    AncRestore n a C U :=
  fun ρ => h ρ (ancZero a)

/-- Sequential composition of dirty restoring blocks. -/
theorem AncRestoreDirty.comp {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]} (h₁ : C₁.bitsOk = true)
    (h₂ : C₂.bitsOk = true) (r₁ : AncRestoreDirty n a C₁ U₁) (r₂ : AncRestoreDirty n a C₂ U₂) :
    AncRestoreDirty n a (C₁.append C₂) (U₂ * U₁) := by
  intro ρ σ
  rw [channelDenote_append n a h₁ h₂, CPTPMap.compose_eq, r₁ ρ σ, r₂, uConj_uConj]

/-- `(U ⊗ 1) (ρ ⊗ σ) (U ⊗ 1)ᴴ = (U ρ Uᴴ) ⊗ σ`. -/
theorem kron_one_conj (U : 𝐔[Reg n]) (ρ : MState (Reg n)) (σ : MState (Reg a)) :
    (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * (ρ ⊗ᴹ σ).m *
      (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ = ((U ◃ ρ) ⊗ᴹ σ).m := by
  change (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * (ρ.m ⊗ₖ σ.m) *
    (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ = (U.val * ρ.m * U.valᴴ) ⊗ₖ σ.m
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

theorem star_mul_self_eq_norm_sq (l : ℂ) : star l * l = ((‖l‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; ring

theorem mul_star_self_eq_norm_sq (l : ℂ) : l * star l = ((‖l‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self_eq_norm_sq]

/-- The weights of a dirty Kraus form sum to one (from Kraus completeness; the analogue of
`sum_norm_sq_eq_one_of_kraus` without the clean projector). -/
theorem sum_norm_sq_eq_one_of_kraus_dirty {C : Circuit} (hC : C.WF) (U : 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ)
    (hK : ∀ c, krausOps n a C.nBits C.gates c = l c • (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))) :
    ∑ c, ‖l c‖ ^ 2 = 1 := by
  have hcomp := krausOps_complete n a C hC.bitsOk
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  have hV : (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ * (U.val ⊗ₖ 1) = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hU,
      one_kronecker_one]
  have h2 : ∀ c, (krausOps n a C.nBits C.gates c)ᴴ * krausOps n a C.nBits C.gates c =
      ((‖l c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) := by
    intro c
    rw [hK c, conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_star_self_eq_norm_sq]
    rw [hV]
  simp only [h2] at hcomp
  rw [← Finset.sum_smul, ← Complex.ofReal_sum] at hcomp
  have hx := congrFun (congrFun hcomp ((fun _ => false : Reg n), (fun _ => false : Reg a)))
    ((fun _ => false : Reg n), (fun _ => false : Reg a))
  rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at hx
  exact_mod_cast hx

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **the Kraus form of dirty restoration**: if every
Kraus operator is `l_c · (U ⊗ 1)` on the whole register, the circuit is dirty restoring with `U`
(the proof of `ancRestoreMix_of_kraus` with the projector replaced by `1`). -/
theorem ancRestoreDirty_of_kraus {C : Circuit} (hC : C.WF) (U : 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ)
    (hK : ∀ c, krausOps n a C.nBits C.gates c = l c • (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))) :
    AncRestoreDirty n a C U := by
  intro ρ σ
  apply MState.ext_m
  rw [channelDenote_m hC]
  have hterm : ∀ c, krausOps n a C.nBits C.gates c * (ρ ⊗ᴹ σ).m *
      (krausOps n a C.nBits C.gates c)ᴴ = ((‖l c‖ ^ 2 : ℝ) : ℂ) • ((U ◃ ρ) ⊗ᴹ σ).m := by
    intro c
    rw [hK c, conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul_self_eq_norm_sq]
    rw [kron_one_conj]
  simp only [hterm]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, sum_norm_sq_eq_one_of_kraus_dirty hC U l hK]
  simp

/-- The common case: a measurement-free circuit whose unitary is `U ⊗ 1`. -/
theorem ancRestoreDirty_of_unitary {C : Circuit} (hC : C.WF)
    (hU : C.gates.all Gate.isUnitary = true) (U : 𝐔[Reg n])
    (h : unitaryDenote n a C.gates = U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) :
    AncRestoreDirty n a C U :=
  ancRestoreDirty_of_kraus hC U (fun _ => 1) fun c => by
    rw [krausOps_of_unitary n a _ _ hU, h, one_smul]

/-- PHASE2_SPEC §B.2 (23b) — **dirty restoration holds on every state**, not only on products:
the product states span (`span_prodStates_eq_top`) and both sides are linear in the state. -/
theorem AncRestoreDirty.all {C : Circuit} {U : 𝐔[Reg n]} (hC : C.WF) (h : AncRestoreDirty n a C U)
    (ω : MState (Reg n × Reg a)) :
    (channelDenote n a C ω).m = (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
      (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by
  have hlin : (∑ c, adMap (krausOps n a C.nBits C.gates c)) =
      adMap (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) := by
    apply LinearMap.ext_on_range (span_prodStates_eq_top (d₁ := Reg n) (d₂ := Reg a))
    rintro ⟨ρ, σ⟩
    have hm := congrArg MState.m (h ρ σ)
    rw [channelDenote_m hC] at hm
    show (∑ c, adMap (krausOps n a C.nBits C.gates c)) (ρ ⊗ᴹ σ).m = adMap _ (ρ ⊗ᴹ σ).m
    simp only [LinearMap.sum_apply, adMap_apply]
    rw [hm, kron_one_conj]
  have := congrArg (fun F : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ →ₗ[ℂ]
    Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ => F ω.m) hlin
  simp only [LinearMap.sum_apply, adMap_apply] at this
  rw [channelDenote_m hC, this]

/-! ### The reset is never dirty -/

/-- A monomial matrix with the identity permutation is a diagonal matrix. -/
theorem monoMat_id_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → ℂ) :
    monoMat id φ = Matrix.diagonal φ := by
  ext i j
  simp only [monoMat_apply, id, Matrix.diagonal_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- `projMat q v` as a diagonal matrix. -/
theorem projMat_eq_diagonal (q : Qubit) (v : Bool) :
    projMat n a q v = Matrix.diagonal fun s => if q.get s = v then (1 : ℂ) else 0 :=
  monoMat_id_diagonal _

theorem projMat_mul_self (q : Qubit) (v : Bool) :
    projMat n a q v * projMat n a q v = projMat n a q v := by
  rw [projMat_eq_diagonal, diagonal_mul_diagonal]
  congr 1
  funext s
  split_ifs <;> simp

theorem projMat_conjTranspose (q : Qubit) (v : Bool) : (projMat n a q v)ᴴ = projMat n a q v := by
  rw [projMat_eq_diagonal, diagonal_conjTranspose]
  congr 1
  funext s
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- `P₀ X_t = X_t P₁`: the reset moves `t = 1` to `t = 0`. -/
theorem projMat_false_mul_x {t : Qubit} (ht : t.inRange n a = true) :
    projMat n a t false * gateU n a (.x t) = gateU n a (.x t) * projMat n a t true := by
  simp only [gateU, projMat, monoMat_mul]
  congr 1
  funext s
  rw [Qubit.get_flip_self t ht]
  cases t.get s <;> simp

/-- A data-only diagonal commutes with the projector on a measurement outcome. -/
theorem projMat_mul_dataDiag (q : Qubit) (v : Bool) (lam : ℂ) (f : Reg n → Bool) :
    projMat n a q v * (lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))) =
      (lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))) * projMat n a q v := by
  rw [projMat_eq_diagonal, phaseDiag, ← diagonal_one, diagonal_kronecker_diagonal, Matrix.mul_smul,
    Matrix.smul_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext s
  ring

/-- **The reset puts `t` in |0⟩ in every branch**: `P₀ K = K` for the Kraus operator of
`measure t j; (ifBit j O); ifBit j (X t)` when `O` acts on the data only. -/
theorem projMat_false_mul_krausOps_reset (m j : ℕ) {t : Qubit} (ht : t.inRange n a = true)
    {O : List Gate} {f : Reg n → Bool} {lam : ℂ}
    (hO : unitaryDenote n a O = lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)))
    (c : Fin m → Bool) :
    projMat n a t false *
        krausOps n a m ([.measure t j] ++ O.map (Gate.ifBit j) ++ [.ifBit j (.x t)]) c =
      krausOps n a m ([.measure t j] ++ O.map (Gate.ifBit j) ++ [.ifBit j (.x t)]) c := by
  rw [krausOps_append_gates, krausOps_append_gates, krausOps_map_ifBit, hO]
  have hm : krausOps n a m [.measure t j] c = projMat n a t (bitVal c j) := by
    simp [krausOps, gateK]
  have hx : krausOps n a m [.ifBit j (.x t)] c = if bitVal c j then gateU n a (.x t) else 1 := by
    simp [krausOps, gateK]
  rw [hm, hx]
  cases bitVal c j
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, projMat_mul_self]
  · simp only [↓reduceIte]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, projMat_false_mul_x ht,
      Matrix.mul_assoc (gateU n a (.x t)), projMat_mul_dataDiag, Matrix.mul_assoc,
      Matrix.mul_assoc, projMat_mul_self]

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **the reset is never dirty**: a well-formed circuit
that ends with `measure t j; (ifBit j O); ifBit j (X t)` on an ancilla `t`, with `O` acting on
the data only, is not dirty restoring for any `U` — its output has `t` in |0⟩ in every branch,
while a dirty block would return the ancilla state `|e_t⟩⟨e_t|` it was given. This is the theorem
behind "dirty ancillae cannot use MBU". -/
theorem reset_not_dirty {C : Circuit} (hC : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ ([.measure t j] ++ O.map (Gate.ifBit j) ++ [.ifBit j (.x t)]))
    (hanc : ∃ i, i < a ∧ t = .anc i) {f : Reg n → Bool} {lam : ℂ}
    (hO : unitaryDenote n a O = lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)))
    (U : 𝐔[Reg n]) : ¬ AncRestoreDirty n a C U := by
  intro h
  have ht : t.inRange n a = true := by
    obtain ⟨i, hi, rfl⟩ := hanc
    simp [Qubit.inRange, hi]
  -- the witness: the data in |0⟩, the ancillae in |e_t⟩ (the qubit `t` set to 1)
  set ρ₀ : MState (Reg n) := MState.pure (Ket.basis fun _ => false) with hρ₀
  set σ₁ : MState (Reg a) := MState.pure (Ket.basis (ancBasis a t true)) with hσ₁
  have hm := congrArg MState.m (h ρ₀ σ₁)
  rw [channelDenote_m hC] at hm
  -- `P₀ K_c = K_c` for every branch
  have hP : ∀ c, projMat n a t false * krausOps n a C.nBits C.gates c =
      krausOps n a C.nBits C.gates c := by
    intro c
    rw [hgates, krausOps_append_gates, ← Matrix.mul_assoc,
      projMat_false_mul_krausOps_reset _ j ht hO]
  -- the diagonal entries of the output at the ancilla value `e_t` vanish
  have hzero : ∀ x : Reg n, (∑ c, krausOps n a C.nBits C.gates c * (ρ₀ ⊗ᴹ σ₁).m *
      (krausOps n a C.nBits C.gates c)ᴴ) (x, ancBasis a t true) (x, ancBasis a t true) = 0 := by
    intro x
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc : krausOps n a C.nBits C.gates c * (ρ₀ ⊗ᴹ σ₁).m * (krausOps n a C.nBits C.gates c)ᴴ =
        projMat n a t false * (krausOps n a C.nBits C.gates c * (ρ₀ ⊗ᴹ σ₁).m *
          (krausOps n a C.nBits C.gates c)ᴴ) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP c]
    rw [hc, projMat_eq_diagonal, diagonal_mul, get_ancBasis hanc]
    simp
  -- while the dirty output has trace one on that slice
  have htr : ∑ x : Reg n, ((U ◃ ρ₀) ⊗ᴹ σ₁).m (x, ancBasis a t true) (x, ancBasis a t true) = 1 := by
    have hσ : σ₁.m (ancBasis a t true) (ancBasis a t true) = 1 := by
      rw [hσ₁, pureBasis_m_apply]; simp
    have hx : ∀ x : Reg n, ((U ◃ ρ₀) ⊗ᴹ σ₁).m (x, ancBasis a t true) (x, ancBasis a t true) =
        (U ◃ ρ₀).m x x := fun x => by
      change (U ◃ ρ₀).m x x * σ₁.m (ancBasis a t true) (ancBasis a t true) = _
      rw [hσ, mul_one]
    simp only [hx]
    simpa [Matrix.trace, Matrix.diag] using (U ◃ ρ₀).tr'
  have h0 : ∑ x : Reg n, (∑ c, krausOps n a C.nBits C.gates c * (ρ₀ ⊗ᴹ σ₁).m *
      (krausOps n a C.nBits C.gates c)ᴴ) (x, ancBasis a t true) (x, ancBasis a t true) = 0 :=
    Finset.sum_eq_zero fun x _ => hzero x
  rw [hm, htr] at h0
  exact one_ne_zero h0

/-- The task text's form: the circuit ends with `measure t j; ifBit j (X t)`. -/
theorem reset_not_dirty' {C : Circuit} (hC : C.WF) {B : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ [.measure t j, .ifBit j (.x t)]) (hanc : ∃ i, i < a ∧ t = .anc i)
    (U : 𝐔[Reg n]) : ¬ AncRestoreDirty n a C U :=
  reset_not_dirty hC (B := B) (O := []) (j := j) (by rw [hgates]; rfl) hanc (f := fun _ => false)
    (lam := 1)
    (by rw [unitaryDenote_nil, phaseDiag_false, one_kronecker_one, one_smul]) U

/-- No MBU block (`B ++ mbuUncompute t j O`, `O` a phase implementation) is dirty restoring. -/
theorem mbu_not_dirty {C : Circuit} (hC : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} {lam : ℂ}
    (hO : unitaryDenote n a O = lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)))
    (U : 𝐔[Reg n]) : ¬ AncRestoreDirty n a C U :=
  reset_not_dirty hC (B := B ++ [.h t]) (j := j)
    (by rw [hgates, mbuUncompute]; simp [List.append_assoc]) hanc hO U

/-- Report §6.2.3 — **`mbuCircuit` is not dirty restoring** (for any `U`). -/
theorem mbuCircuit_not_dirty (U : 𝐔[Reg 2]) : ¬ AncRestoreDirty 2 1 mbuCircuit U := by
  obtain ⟨lam, -, hlam⟩ := cz_phaseImpl.phase
  exact mbu_not_dirty mbuCircuit_WF
    (B := TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)])
    (O := [.cz (.data 0) (.data 1)]) (j := 0) rfl ⟨0, by norm_num, rfl⟩ hlam U

/-! ### The dirty phase gadget -/

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **the dirty phase gadget** on `(x0, x1; d)`:
`CNOT(x0 → d); CZ(d, x1); CNOT(x0 → d); CZ(d, x1)`. The phase is
`(−1)^{(d ⊕ x0) x1 ⊕ d x1} = (−1)^{x0 x1}` for every ancilla value `d`: the dirty ancilla is
used twice, so its value cancels (the phase form of toggle detection). -/
def dirtyGadget : Circuit :=
  ⟨2, [.cnot (.data 0) (.anc 0), .cz (.anc 0) (.data 1), .cnot (.data 0) (.anc 0),
    .cz (.anc 0) (.data 1)]⟩

theorem gateU_cz_mulVec_basisVec (c t : Qubit) (s : Reg n × Reg a) :
    gateU n a (.cz c t) *ᵥ basisVec s = (if c.get s && t.get s then (-1 : ℂ) else 1) • basisVec s := by
  simp only [gateU]
  rw [monoMat_mulVec_basisVec (fun _ => rfl)]
  rfl

/-- Two matrices agreeing on every basis vector are equal. -/
theorem eq_of_mulVec_basisVec {ι : Type} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι ℂ}
    (h : ∀ s, M *ᵥ basisVec s = N *ᵥ basisVec s) : M = N := by
  ext i j
  have := congrFun (h j) i
  rwa [mulVec_basisVec, mulVec_basisVec] at this

theorem dirtyGadget_denote :
    unitaryDenote 2 1 dirtyGadget.gates = czU.val ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ) := by
  apply eq_of_mulVec_basisVec
  rintro ⟨x, w⟩
  have h01 : Qubit.data 0 ≠ Qubit.anc 0 := by decide
  change unitaryDenote 2 1 [.cnot (.data 0) (.anc 0), .cz (.anc 0) (.data 1),
    .cnot (.data 0) (.anc 0), .cz (.anc 0) (.data 1)] *ᵥ basisVec (x, w) =
    (phaseDiag (fun x : Reg 2 => x 0 && x 1) ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ)) *ᵥ basisVec (x, w)
  rw [phaseDiag_kronecker_one_mulVec_basisVec, unitaryDenote_cons_mulVec, unitaryDenote_cons_mulVec,
    unitaryDenote_cons_mulVec, unitaryDenote_cons_mulVec, unitaryDenote_nil,
    gateU_cnot_mulVec_basisVec 2 1 h01, gateU_cz_mulVec_basisVec, Matrix.mulVec_smul,
    gateU_cnot_mulVec_basisVec 2 1 h01, Matrix.mulVec_smul, gateU_cz_mulVec_basisVec,
    Matrix.one_mulVec, smul_smul, cnotPerm_involutive 2 1 h01 (x, w)]
  congr 1
  simp only [cnotPerm, Qubit.get, Qubit.flip, Qubit.set]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hw : w 0 <;>
    simp [hx0, hx1, hw, Fin.zero_eta, Fin.mk_one]

/-- The dirty phase gadget is dirty restoring with `CZ`. -/
theorem dirtyGadget_dirty : AncRestoreDirty 2 1 dirtyGadget czU :=
  ancRestoreDirty_of_unitary (by decide) (by decide) czU dirtyGadget_denote

end Dirty

/-! ## P2 — conditionally clean restoration -/

section Cond

variable {n a : ℕ}

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **the conditionally clean subspace**: the projector
onto `V_cond = span{|x, w⟩ : cond x → w = 0}` (a diagonal 0/1 matrix). -/
def condSubspace (n a : ℕ) (cond : Reg n → Bool) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  Matrix.diagonal fun u => if (cond u.1 = true → u.2 = fun _ => false) then 1 else 0

theorem condSubspace_mul_self (cond : Reg n → Bool) :
    condSubspace n a cond * condSubspace n a cond = condSubspace n a cond := by
  rw [condSubspace, diagonal_mul_diagonal]
  congr 1
  funext u
  split_ifs <;> simp

theorem condSubspace_conjTranspose (cond : Reg n → Bool) :
    (condSubspace n a cond)ᴴ = condSubspace n a cond := by
  rw [condSubspace, diagonal_conjTranspose]
  congr 1
  funext u
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- `V_true` is the clean subspace `{w = 0}`. -/
theorem condSubspace_true : condSubspace n a (fun _ => true) = ancProj n a := by
  ext ⟨x, w⟩ ⟨y, v⟩
  rw [condSubspace, ancProj, diagonal_apply, kroneckerMap_apply, one_apply, ancZero_m_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hwv : w = v
    · subst hwv
      by_cases hw : w = fun _ => false <;> simp [hw]
    · have : ¬ (w = (fun _ => false) ∧ v = (fun _ => false)) :=
        fun h => hwv (h.1.trans h.2.symm)
      simp [hwv, this]
  · simp [hxy]

/-- `V_false` is everything. -/
theorem condSubspace_false : condSubspace n a (fun _ => false) = 1 := by
  rw [condSubspace, ← diagonal_one]
  congr 1

/-- The projectors commute (all are diagonal). -/
theorem condSubspace_comm (cond cond' : Reg n → Bool) :
    condSubspace n a cond * condSubspace n a cond' = condSubspace n a cond' * condSubspace n a cond := by
  rw [condSubspace, condSubspace, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext u
  ring

/-- `V_cond' ⊆ V_cond` when `cond ≤ cond'`: `P_cond P_cond' = P_cond'`. -/
theorem condSubspace_mul_of_le {cond cond' : Reg n → Bool} (h : ∀ x, cond x = true → cond' x = true) :
    condSubspace n a cond * condSubspace n a cond' = condSubspace n a cond' := by
  rw [condSubspace, condSubspace, diagonal_mul_diagonal]
  congr 1
  funext u
  by_cases h' : (cond' u.1 = true → u.2 = fun _ => false)
  · have : (cond u.1 = true → u.2 = fun _ => false) := fun hc => h' (h u.1 hc)
    simp only [eq_true h', eq_true this, ite_true, mul_one]
  · simp only [eq_false h', ite_false, mul_zero]

/-- Report §6.2.3, PHASE2_SPEC §B.2 (23b) — **conditionally clean restoration**: on every state
`ω` of the register supported on `V_cond` (`P ω P = ω`), the circuit acts as `Ad(U ⊗ 1)`. -/
def AncRestoreCond (n a : ℕ) (C : Circuit) (U : 𝐔[Reg n]) (cond : Reg n → Bool) : Prop :=
  ∀ ω : MState (Reg n × Reg a), condSubspace n a cond * ω.m * condSubspace n a cond = ω.m →
    (channelDenote n a C ω).m = (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
      (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ

/-- **Dirty is conditionally clean** for every condition (through `AncRestoreDirty.all`). -/
theorem AncRestoreDirty.toCond {C : Circuit} {U : 𝐔[Reg n]} (hC : C.WF)
    (h : AncRestoreDirty n a C U) (cond : Reg n → Bool) : AncRestoreCond n a C U cond :=
  fun ω _ => h.all hC ω

/-- A weaker condition is a stronger statement: `cond ≤ cond'` gives `V_cond' ⊆ V_cond`. -/
theorem AncRestoreCond.mono {C : Circuit} {U : 𝐔[Reg n]} {cond cond' : Reg n → Bool}
    (h : AncRestoreCond n a C U cond) (hle : ∀ x, cond x = true → cond' x = true) :
    AncRestoreCond n a C U cond' := by
  intro ω hω
  refine h ω ?_
  calc condSubspace n a cond * ω.m * condSubspace n a cond
      = condSubspace n a cond * (condSubspace n a cond' * ω.m * condSubspace n a cond') *
          condSubspace n a cond := by rw [hω]
    _ = (condSubspace n a cond * condSubspace n a cond') * ω.m *
          (condSubspace n a cond' * condSubspace n a cond) := by simp only [Matrix.mul_assoc]
    _ = condSubspace n a cond' * ω.m * condSubspace n a cond' := by
          rw [condSubspace_mul_of_le hle, condSubspace_comm, condSubspace_mul_of_le hle]
    _ = ω.m := hω

/-- **Conditionally clean is clean**, for every condition: `V_true = {w = 0} ⊆ V_cond`. -/
theorem AncRestoreCond.toClean {C : Circuit} {U : 𝐔[Reg n]} {cond : Reg n → Bool}
    (h : AncRestoreCond n a C U cond) : AncRestore n a C U := by
  intro ρ
  apply MState.ext_m
  have h' := h.mono (cond' := fun _ => true) (fun _ _ => rfl)
  rw [h' (ρ ⊗ᴹ ancZero a) (by rw [condSubspace_true, ← prod_ancZero_m_eq]), kron_one_conj]

/-! ### R2 — Clean ⇔ Cond(true) (REVIEW_RESPONSE_1 row 2; report §6.2.3) -/

/-- The matrix of the partial trace over the second factor (the entrywise form of Physlib's
`MState.traceRight`; `CQRV/Noise/Steps.lean` states the same as `MState.traceRight_m`, which a
`Circuit` module cannot import). -/
theorem traceRight_m_eq {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (σ : MState (d₁ × d₂)) : σ.traceRight.m = σ.m.traceRight := by
  simp only [MState.m, MState.traceRight_M, HermitianMat.traceRight_mat]

/-- The entries of `P M P` for the clean projector `P = 1 ⊗ |0⟩⟨0|`: the `((x, 0), (y, 0))` entry
of `M` on the ancilla-zero block, `0` elsewhere. -/
theorem ancProj_mul_mul_apply (M : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) (x y : Reg n)
    (w v : Reg a) :
    (ancProj n a * M * ancProj n a) (x, w) (y, v) =
      if w = (fun _ => false) ∧ v = (fun _ => false) then M (x, fun _ => false) (y, fun _ => false)
      else 0 := by
  have hP : ∀ s t : Reg n × Reg a, ancProj n a s t =
      if s.1 = t.1 ∧ s.2 = (fun _ => false) ∧ t.2 = (fun _ => false) then 1 else 0 := by
    rintro ⟨x', w'⟩ ⟨y', v'⟩
    rw [ancProj, kroneckerMap_apply, one_apply, ancZero_m_apply]
    by_cases hxy : x' = y' <;> by_cases hw : w' = fun _ => false <;>
      by_cases hv : v' = fun _ => false <;> simp [hxy, hw, hv]
  rw [Matrix.mul_apply, Finset.sum_eq_single ((y, fun _ => false) : Reg n × Reg a)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single ((x, fun _ => false) : Reg n × Reg a)]
    · rw [hP, hP]
      by_cases hw : w = fun _ => false <;> by_cases hv : v = fun _ => false <;> simp [hw, hv]
    · rintro ⟨p1, p2⟩ _ hp
      rw [hP]
      split_ifs with h
      · exact (hp (Prod.ext_iff.mpr ⟨by simpa using h.1.symm, by simpa using h.2.2⟩)).elim
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · rintro ⟨q1, q2⟩ _ hq
    rw [hP]
    split_ifs with h
    · exact (hq (Prod.ext_iff.mpr ⟨by simpa using h.1, by simpa using h.2.1⟩)).elim
    · simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Support factorization, entrywise**: a state supported on `V_true = {w = 0}` is the Kronecker
product of its partial trace with `|0⟩⟨0|`. -/
theorem supportFactor_m (ω : MState (Reg n × Reg a))
    (hω : ancProj n a * ω.m * ancProj n a = ω.m) :
    ω.m = ω.traceRight.m ⊗ₖ (ancZero a).m := by
  have hentry : ∀ (x y : Reg n) (w v : Reg a), ω.m (x, w) (y, v) =
      if w = (fun _ => false) ∧ v = (fun _ => false) then ω.m (x, fun _ => false) (y, fun _ => false)
      else 0 := by
    intro x y w v
    rw [← ancProj_mul_mul_apply ω.m x y w v, hω]
  ext ⟨x, w⟩ ⟨y, v⟩
  rw [kroneckerMap_apply, traceRight_m_eq, ancZero_m_apply]
  simp only [Matrix.traceRight, Matrix.of_apply]
  have hsum : ∑ i, ω.m (x, i) (y, i) = ω.m (x, fun _ => false) (y, fun _ => false) := by
    rw [Fintype.sum_eq_single (fun _ => false)]
    intro i hi
    rw [hentry x y i i]; simp [hi]
  rw [hsum, hentry x y w v]
  split_ifs <;> simp

/-- R2 — **support factorization**: a state supported on `V_true` is `traceRight ω ⊗ᴹ |0⟩⟨0|`
(`condSubspace_true` identifies `V_true` with `ancProj`). -/
theorem supportFactor (ω : MState (Reg n × Reg a))
    (hω : ancProj n a * ω.m * ancProj n a = ω.m) :
    ω = ω.traceRight ⊗ᴹ ancZero a := by
  apply MState.ext_m
  rw [prod_ancZero_m]
  exact supportFactor_m ω hω

/-- R2 — **clean is conditionally clean under `true`**, the converse of `AncRestoreCond.toClean`
at `cond ≡ true`: factor the supported state, apply the clean statement at `traceRight ω`, and
`kron_one_conj`. -/
theorem AncRestore.toCond_true {C : Circuit} {U : 𝐔[Reg n]} (h : AncRestore n a C U) :
    AncRestoreCond n a C U (fun _ => true) := by
  intro ω hω
  rw [condSubspace_true] at hω
  have hfac := supportFactor ω hω
  calc (channelDenote n a C ω).m
      = (channelDenote n a C (ω.traceRight ⊗ᴹ ancZero a)).m := by rw [← hfac]
    _ = ((U ◃ ω.traceRight) ⊗ᴹ ancZero a).m := by rw [h ω.traceRight]
    _ = (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * (ω.traceRight ⊗ᴹ ancZero a).m *
          (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := (kron_one_conj U _ _).symm
    _ = (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
          (U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by rw [← hfac]

/-- R2 — **Clean ⇔ Cond(true)**: the clean regime is the conditional regime under the trivial
condition (report §6.2.3; REVIEW_RESPONSE_1 row 2). -/
theorem ancRestoreCond_true_iff {C : Circuit} {U : 𝐔[Reg n]} :
    AncRestoreCond n a C U (fun _ => true) ↔ AncRestore n a C U :=
  ⟨AncRestoreCond.toClean, AncRestore.toCond_true⟩

/-- Conditionally clean under `cond ≡ false` (`V = everything`) is dirty. -/
theorem AncRestoreCond.toDirty {C : Circuit} {U : 𝐔[Reg n]}
    (h : AncRestoreCond n a C U (fun _ => false)) : AncRestoreDirty n a C U := by
  intro ρ σ
  apply MState.ext_m
  rw [h (ρ ⊗ᴹ σ) (by rw [condSubspace_false, Matrix.one_mul, Matrix.mul_one]), kron_one_conj]

/-- Dirty restoration is conditionally clean restoration under `cond ≡ false`. -/
theorem ancRestoreDirty_iff_cond_false {C : Circuit} {U : 𝐔[Reg n]} (hC : C.WF) :
    AncRestoreDirty n a C U ↔ AncRestoreCond n a C U (fun _ => false) :=
  ⟨fun h => h.toCond hC _, AncRestoreCond.toDirty⟩

/-- PHASE2_SPEC §B.2 (23b) — **sequential composition of conditionally clean blocks**: if `C₁` is
conditionally clean with `U₁` under `cond`, `C₂` with `U₂` under `cond'`, and `U₁ ⊗ 1` maps
`V_cond` into `V_cond'` (`P' (U₁ ⊗ 1) P = (U₁ ⊗ 1) P`), the composite is conditionally clean with
`U₂ U₁` under `cond`. -/
theorem AncRestoreCond.comp {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]} {cond cond' : Reg n → Bool}
    (h₁ : C₁.bitsOk = true) (h₂ : C₂.bitsOk = true)
    (r₁ : AncRestoreCond n a C₁ U₁ cond) (r₂ : AncRestoreCond n a C₂ U₂ cond')
    (hmap : condSubspace n a cond' * (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
      condSubspace n a cond = (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond) :
    AncRestoreCond n a (C₁.append C₂) (U₂ * U₁) cond := by
  intro ω hω
  rw [channelDenote_append n a h₁ h₂, CPTPMap.compose_eq]
  have h1 := r₁ ω hω
  have hsupp : condSubspace n a cond' * (channelDenote n a C₁ ω).m * condSubspace n a cond' =
      (channelDenote n a C₁ ω).m := by
    rw [h1]
    calc condSubspace n a cond' * ((U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
            (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ) * condSubspace n a cond'
        = condSubspace n a cond' * ((U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
            (condSubspace n a cond * ω.m * condSubspace n a cond) *
            (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ) * condSubspace n a cond' := by rw [hω]
      _ = (condSubspace n a cond' * (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
            condSubspace n a cond) * ω.m *
            (condSubspace n a cond' * (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
            condSubspace n a cond)ᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, condSubspace_conjTranspose,
            condSubspace_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = ((U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond) * ω.m *
            ((U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond)ᴴ := by rw [hmap]
      _ = (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
            (condSubspace n a cond * ω.m * condSubspace n a cond) *
            (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by
          rw [conjTranspose_mul, condSubspace_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
            (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by rw [hω]
  rw [r₂ _ hsupp, h1]
  have hmul : ((U₂ * U₁).val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) =
      (U₂.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * (U₁.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
    rfl
  rw [hmul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- A diagonal `U₁` maps every `V_cond` into itself: `P (D ⊗ 1) P = (D ⊗ 1) P`. -/
theorem condSubspace_mul_diag_kron (cond : Reg n → Bool) (φ : Reg n → ℂ) :
    condSubspace n a cond * (Matrix.diagonal φ ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
        condSubspace n a cond =
      (Matrix.diagonal φ ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond := by
  rw [← diagonal_one, diagonal_kronecker_diagonal, condSubspace, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext u
  split_ifs <;> simp

/-- `AncRestoreCond.comp` for a diagonal `U₁` and `cond' = cond`. -/
theorem AncRestoreCond.comp_diag {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]} {cond : Reg n → Bool}
    {φ : Reg n → ℂ} (hdiag : U₁.val = Matrix.diagonal φ) (h₁ : C₁.bitsOk = true)
    (h₂ : C₂.bitsOk = true) (r₁ : AncRestoreCond n a C₁ U₁ cond) (r₂ : AncRestoreCond n a C₂ U₂ cond) :
    AncRestoreCond n a (C₁.append C₂) (U₂ * U₁) cond :=
  r₁.comp h₁ h₂ r₂ (by rw [hdiag]; exact condSubspace_mul_diag_kron cond φ)

/-- The matrix form of the channel of a measurement-free circuit. -/
theorem channelDenote_m_of_unitary {C : Circuit} (hC : C.WF) (hU : C.gates.all Gate.isUnitary = true)
    (ω : MState (Reg n × Reg a)) :
    (channelDenote n a C ω).m =
      unitaryDenote n a C.gates * ω.m * (unitaryDenote n a C.gates)ᴴ := by
  rw [channelDenote_m hC]
  simp only [krausOps_of_unitary n a _ _ hU]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Circuit.nBits_eq_zero_of_unitary hU]
  simp

/-- A measurement-free block whose unitary agrees with `V ⊗ 1` on `V_cond` is conditionally clean
with `V` under `cond`. -/
theorem ancRestoreCond_of_unitary {C : Circuit} (hC : C.WF) (hU : C.gates.all Gate.isUnitary = true)
    (V : 𝐔[Reg n]) (cond : Reg n → Bool)
    (hfix : unitaryDenote n a C.gates * condSubspace n a cond =
      (V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond) :
    AncRestoreCond n a C V cond := by
  intro ω hω
  rw [channelDenote_m_of_unitary hC hU]
  calc unitaryDenote n a C.gates * ω.m * (unitaryDenote n a C.gates)ᴴ
      = unitaryDenote n a C.gates * (condSubspace n a cond * ω.m * condSubspace n a cond) *
          (unitaryDenote n a C.gates)ᴴ := by rw [hω]
    _ = (unitaryDenote n a C.gates * condSubspace n a cond) * ω.m *
          (unitaryDenote n a C.gates * condSubspace n a cond)ᴴ := by
        rw [conjTranspose_mul, condSubspace_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = ((V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond) * ω.m *
          ((V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * condSubspace n a cond)ᴴ := by rw [hfix]
    _ = (V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *
          (condSubspace n a cond * ω.m * condSubspace n a cond) *
          (V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by
        rw [conjTranspose_mul, condSubspace_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = (V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) * ω.m *
          (V.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))ᴴ := by rw [hω]

/-! ### The instance: `CZ(x0, anc 0)` -/

/-- `CZ(x0, anc 0)` on one data qubit and one ancilla. -/
def czCondCircuit : Circuit := ⟨1, [.cz (.data 0) (.anc 0)]⟩

theorem gateU_cz_eq_diagonal (c t : Qubit) :
    gateU n a (.cz c t) = Matrix.diagonal fun s => if c.get s && t.get s then (-1 : ℂ) else 1 :=
  monoMat_id_diagonal _

theorem czCondCircuit_denote :
    unitaryDenote 1 1 czCondCircuit.gates =
      Matrix.diagonal fun s : Reg 1 × Reg 1 => if s.1 0 && s.2 0 then (-1 : ℂ) else 1 := by
  change unitaryDenote 1 1 [.cz (.data 0) (.anc 0)] = _
  rw [unitaryDenote, unitaryDenote_nil, Matrix.one_mul, gateU_cz_eq_diagonal]
  congr 1

/-- **`CZ(x0, anc 0)` is conditionally clean with `U = 1` under `cond = x0`**: on `V_cond`
(`x0 = 1 → w = 0`) the gate is the identity. -/
theorem czCond_cond : AncRestoreCond 1 1 czCondCircuit 1 (fun x => x 0) := by
  refine ancRestoreCond_of_unitary (by decide) (by decide) 1 _ ?_
  change unitaryDenote 1 1 czCondCircuit.gates * condSubspace 1 1 (fun x => x 0) =
    ((1 : Matrix (Reg 1) (Reg 1) ℂ) ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ)) *
      condSubspace 1 1 (fun x => x 0)
  rw [one_kronecker_one, Matrix.one_mul, czCondCircuit_denote, condSubspace, diagonal_mul_diagonal]
  congr 1
  funext ⟨x, w⟩
  dsimp only
  by_cases hc : (x 0 = true → w = fun _ => false)
  · have : (x 0 && w 0) = false := by
      cases hx : x 0
      · rfl
      · rw [hc hx]; rfl
    simp only [eq_true hc, ite_true, this]
    simp
  · simp only [eq_false hc, ite_false, mul_zero]

/-- `CZ(x0, anc 0)` is clean. -/
theorem czCond_clean : AncRestore 1 1 czCondCircuit 1 := czCond_cond.toClean

/-- `|+⟩` on one qubit. -/
def ketPlus : Ket (Reg 1) where
  vec _ := ((Real.sqrt 2)⁻¹ : ℂ)
  normalized' := by
    simp only [norm_sq_invSqrtTwo, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    norm_num

theorem ketPlus_m_apply (w v : Reg 1) : (MState.pure ketPlus).m w v = 1 / 2 := by
  rw [pure_m_apply]
  change ((Real.sqrt 2)⁻¹ : ℂ) * (starRingEnd ℂ) ((Real.sqrt 2)⁻¹ : ℂ) = _
  rw [conj_invSqrtTwo, invSqrtTwo_mul_self]

/-- **`CZ(x0, anc 0)` is not dirty restoring** for any `U`: on `|1⟩ ⊗ |+⟩` it outputs
`|1⟩ ⊗ |−⟩`, whose off-diagonal ancilla entry has the opposite sign. -/
theorem czCond_not_dirty (U : 𝐔[Reg 1]) : ¬ AncRestoreDirty 1 1 czCondCircuit U := by
  intro h
  set ρ₁ : MState (Reg 1) := MState.pure (Ket.basis fun _ => true) with hρ₁
  have hm := congrArg MState.m (h ρ₁ (MState.pure ketPlus))
  rw [channelDenote_m_of_unitary (by decide) (by decide), czCondCircuit_denote,
    diagonal_conjTranspose] at hm
  have hM : ∀ (x y : Reg 1) (w v : Reg 1), (ρ₁ ⊗ᴹ MState.pure ketPlus).m (x, w) (y, v) =
      ρ₁.m x y * (MState.pure ketPlus).m w v := fun _ _ _ _ => rfl
  have hM' : ∀ (x y : Reg 1) (w v : Reg 1), ((U ◃ ρ₁) ⊗ᴹ MState.pure ketPlus).m (x, w) (y, v) =
      (U ◃ ρ₁).m x y * (MState.pure ketPlus).m w v := fun _ _ _ _ => rfl
  have hρ : ρ₁.m (fun _ => true) (fun _ => true) = 1 := by
    rw [hρ₁, pureBasis_m_apply]; simp
  have e1 := congrFun (congrFun hm ((fun _ => true), fun _ => false)) ((fun _ => true), fun _ => false)
  have e2 := congrFun (congrFun hm ((fun _ => true), fun _ => false)) ((fun _ => true), fun _ => true)
  rw [mul_diagonal, diagonal_mul, hM, hM', hρ, ketPlus_m_apply] at e1 e2
  simp only [Pi.star_apply, Bool.and_false, Bool.and_true, Bool.false_eq_true, ite_true, ite_false,
    star_one, star_neg, one_mul, mul_one, mul_neg] at e1 e2
  have h10 : (1 : ℂ) = 0 := by linear_combination e1 - e2
  exact one_ne_zero h10

/-- `CZ(x0, anc 0)` is not conditionally clean under `cond ≡ false` for any `U`: the second
strictness fact, clean but not conditionally clean under every condition. -/
theorem czCond_not_cond_false (U : 𝐔[Reg 1]) :
    ¬ AncRestoreCond 1 1 czCondCircuit U (fun _ => false) :=
  fun h => czCond_not_dirty U h.toDirty

end Cond

end CQRV

end

end
