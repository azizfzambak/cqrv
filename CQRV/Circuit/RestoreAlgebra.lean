module

public import CQRV.Circuit.MBUClifford

/-!
# CQRV.Circuit.RestoreAlgebra

Stage 23a (PHASE2_SPEC §B.2; report §6.2.1, §6.2.4, §6.3.2; Track B) — **composition laws for clean
restoration**.

* **N1. Block lists.** `ancRestore_list`: local restoration implies global restoration for any list
  of blocks, by `AncRestore.comp` — the generalization of `ancRestore_foldl` from an iterate to a
  list; `ancRestore_empty` for the empty circuit.
* **N2. Restoration under measurement with a mixed data action.** `ancRestoreMix_of_kraus`: if the
  branch `c` acts on the clean-ancilla subspace as `l_c · (U_c ⊗ |0⟩⟨0|)`, the ancillae are
  restored and the data undergoes the mixture `ρ ↦ ∑_c |l_c|² U_c ρ U_cᴴ`; the weights sum to one
  by Kraus completeness (`sum_norm_sq_eq_one_of_kraus`), so the hypothesis `∑ ‖l_c‖² = 1` of
  `ancRestore_of_kraus` was redundant (`ancRestore_of_kraus'`). The example is MBU without its
  correction (`mbu_uncorrected`): the ancilla is restored, the data is dephased in the basis of `f`,
  `ρ ↦ ½ ρ + ½ O_f ρ O_fᴴ`.
* **N3. Widening, or ancilla reuse.** `AncRestore.widen`: a block certified on `a` ancillae and
  touching only those is certified on `a + b`, through the split `Reg (a + b) ≃ Reg a × Reg b`
  (`Fin.append`, `Fin.castAdd`, `Fin.natAdd`): every Kraus operator on the wider register is the
  Kraus operator on the narrower one tensored with `1` (`krausOps_wide`), and the clean projector
  factorizes (`prod_ancZero_wide`). `AncRestore.comp_widen`: two blocks certified on `a₁` and `a₂`
  ancillae compose on any `a ≥ a₁, a₂`.

Conventions of Stage 22: `(-1 : ℂ)`, `by_cases h : … = true`, matrix statements through
`channelDenote_m` and the Kraus operators.
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix CQRV.Synthesis
open scoped MState Kronecker

/-! ## N1 — block lists -/

/-- Report §6.2.4, PHASE2_SPEC §B.2 (23a) — **local restoration implies global restoration for a
list of blocks**: each block `p.1` with its unitary `p.2`, well disciplined and restoring, composed
by the shifted `Circuit.append` after `init`, restores its ancillae and applies the product of the
blocks' unitaries in order after `U` (`foldl (fun V W => W * V)`: the last block outermost). -/
theorem ancRestore_list {n a : ℕ} (blocks : List (Circuit × 𝐔[Reg n]))
    (h : ∀ p ∈ blocks, p.1.bitsOk = true ∧ AncRestore n a p.1 p.2) :
    ∀ (init : Circuit) (U : 𝐔[Reg n]), init.bitsOk = true → AncRestore n a init U →
      ((blocks.map Prod.fst).foldl Circuit.append init).bitsOk = true ∧
        AncRestore n a ((blocks.map Prod.fst).foldl Circuit.append init)
          ((blocks.map Prod.snd).foldl (fun V W => W * V) U) := by
  induction blocks with
  | nil => intro init U hi rinit; exact ⟨hi, rinit⟩
  | cons p ps ih =>
    intro init U hi rinit
    have hp := h p (List.mem_cons_self ..)
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun q hq => h q (List.mem_cons_of_mem p hq)) (init.append p.1) (p.2 * U)
      (Circuit.bitsOk_append hi hp.1) (AncRestore.comp hi hp.1 rinit hp.2)

/-- The empty circuit restores its ancillae applying the identity. -/
theorem ancRestore_empty (n a : ℕ) : AncRestore n a ⟨n, []⟩ 1 := by
  have hWF : (⟨n, []⟩ : Circuit).WF := rfl
  have hn : (⟨n, []⟩ : Circuit).nBits = 0 := rfl
  refine ancRestore_of_kraus hWF 1 (fun _ => 1) ?_ ?_
  · simp [hn]
  · intro c
    show (1 : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) * ancProj n a =
      (1 : ℂ) • ((1 : Matrix (Reg n) (Reg n) ℂ) ⊗ₖ (ancZero a).m)
    rw [Matrix.one_mul, one_smul]
    rfl

/-! ## N2 — restoration under measurement with a mixed data action -/

section Mix

variable {n a : ℕ}

/-- Report §6.2.4, PHASE2_SPEC §B.2 (23a) — **restoration under measurement with a mixed data
action**: if the Kraus operator of every branch `c` acts on the clean-ancilla subspace as
`l_c · (U_c ⊗ |0…0⟩⟨0…0|)`, the circuit maps `ρ ⊗ |0⟩⟨0|` to `∑_c ‖l_c‖² (U_c ρ U_cᴴ) ⊗ |0⟩⟨0|`: the
ancillae are restored and the data undergoes the mixture of the `U_c` with the weights `‖l_c‖²`
(the matrix form; the weights sum to one by `sum_norm_sq_eq_one_of_kraus`). -/
theorem ancRestoreMix_of_kraus {C : Circuit} (hC : C.WF) (U : (Fin C.nBits → Bool) → 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ)
    (hK : ∀ c, krausOps n a C.nBits C.gates c * ancProj n a =
      l c • ((U c).val ⊗ₖ (ancZero a).m)) (ρ : MState (Reg n)) :
    (channelDenote n a C (ρ ⊗ᴹ ancZero a)).m =
      ∑ c, ((‖l c‖ ^ 2 : ℝ) : ℂ) • ((U c ◃ ρ) ⊗ᴹ ancZero a).m := by
  rw [channelDenote_m hC, prod_ancZero_m_eq]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : krausOps n a C.nBits C.gates c *
      (ancProj n a * (ρ ⊗ᴹ ancZero a).m * ancProj n a) * (krausOps n a C.nBits C.gates c)ᴴ =
      (krausOps n a C.nBits C.gates c * ancProj n a) * (ρ ⊗ᴹ ancZero a).m *
        (krausOps n a C.nBits C.gates c * ancProj n a)ᴴ := by
    rw [Matrix.conjTranspose_mul, ancProj_conjTranspose]; simp only [Matrix.mul_assoc]
  have hs : star (l c) * l c = ((‖l c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [h1, hK, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hs, prod_ancZero_m, prod_ancZero_m, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ancZero_m_conjTranspose,
    ancZero_m_mul_self, ancZero_m_mul_self]
  rfl

/-- `P² = P` for the clean-ancilla projector. -/
theorem ancProj_mul_self (n a : ℕ) : ancProj n a * ancProj n a = ancProj n a := by
  rw [ancProj, ← Matrix.mul_kronecker_mul, Matrix.one_mul, ancZero_m_mul_self]

/-- The clean-ancilla projector has the entry `1` at `((x, 0), (x, 0))`. -/
theorem ancProj_apply_zero (n a : ℕ) (x : Reg n) :
    ancProj n a (x, fun _ => false) (x, fun _ => false) = 1 := by
  simp [ancProj, kroneckerMap_apply, one_apply, ancZero_m_apply]

/-- PHASE2_SPEC §B.2 (23a) — **the weights sum to one**: from the completeness of the Kraus
operators (`P (∑ K_cᴴ K_c) P = P`) and the clean input (`P K_cᴴ K_c P = ‖l_c‖² P`). The hypothesis
`∑ ‖l_c‖² = 1` of `ancRestore_of_kraus` is therefore redundant. -/
theorem sum_norm_sq_eq_one_of_kraus {C : Circuit} (hC : C.WF) (U : (Fin C.nBits → Bool) → 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ)
    (hK : ∀ c, krausOps n a C.nBits C.gates c * ancProj n a =
      l c • ((U c).val ⊗ₖ (ancZero a).m)) :
    ∑ c, ‖l c‖ ^ 2 = 1 := by
  have hcomp := krausOps_complete n a C hC.bitsOk
  have h1 : ancProj n a * (∑ c, (krausOps n a C.nBits C.gates c)ᴴ * krausOps n a C.nBits C.gates c)
      * ancProj n a = ancProj n a := by
    rw [hcomp, Matrix.mul_one, ancProj_mul_self]
  have h2 : ∀ c, ancProj n a * ((krausOps n a C.nBits C.gates c)ᴴ * krausOps n a C.nBits C.gates c)
      * ancProj n a = ((‖l c‖ ^ 2 : ℝ) : ℂ) • ancProj n a := by
    intro c
    have hU : (U c).valᴴ * (U c).val = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 (U c).2
    have hs : star (l c) * l c = ((‖l c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    have : ancProj n a * ((krausOps n a C.nBits C.gates c)ᴴ * krausOps n a C.nBits C.gates c) *
        ancProj n a = (krausOps n a C.nBits C.gates c * ancProj n a)ᴴ *
          (krausOps n a C.nBits C.gates c * ancProj n a) := by
      rw [Matrix.conjTranspose_mul, ancProj_conjTranspose]; simp only [Matrix.mul_assoc]
    rw [this, hK c, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, ancZero_m_conjTranspose,
      ancZero_m_mul_self]
    rfl
  rw [Matrix.mul_sum, Matrix.sum_mul] at h1
  simp only [h2] at h1
  rw [← Finset.sum_smul, ← Complex.ofReal_sum] at h1
  have hx := congrFun (congrFun h1 ((fun _ => false : Reg n), fun _ => false))
    ((fun _ => false : Reg n), fun _ => false)
  rw [Matrix.smul_apply, ancProj_apply_zero, smul_eq_mul, mul_one] at hx
  exact_mod_cast hx

/-- `ancRestore_of_kraus` without its weight hypothesis: the weights sum to one automatically. -/
theorem ancRestore_of_kraus' {C : Circuit} (hC : C.WF) (U : 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ)
    (hK : ∀ c, krausOps n a C.nBits C.gates c * ancProj n a = l c • (U.val ⊗ₖ (ancZero a).m)) :
    AncRestore n a C U :=
  ancRestore_of_kraus hC U l (sum_norm_sq_eq_one_of_kraus hC (fun _ => U) l hK) hK

/-- `1 ◃ ρ = ρ`. -/
theorem one_uConj (ρ : MState (Reg n)) : (1 : 𝐔[Reg n]) ◃ ρ = ρ := by
  apply MState.ext_m
  change (1 : Matrix (Reg n) (Reg n) ℂ) * ρ.m * (1 : Matrix (Reg n) (Reg n) ℂ)ᴴ = ρ.m
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- `diagU` depends only on the function. -/
theorem diagU_congr {φ ψ : Reg n → ℂ} (h : ∀ x, φ x = ψ x) (hφ : ∀ x, ‖φ x‖ = 1)
    (hψ : ∀ x, ‖ψ x‖ = 1) : diagU φ hφ = diagU ψ hψ :=
  Subtype.ext (by rw [diagU_val, diagU_val]; congr 1; funext x; exact h x)

/-- The norm of the branch weight of MBU, `‖1/√2‖² = 1/2`. -/
theorem norm_sq_invSqrtTwo : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The bit `j` of a well-formed `B ++ mbuUncompute t j O` is `0`. -/
theorem mbu_bit_eq_zero {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hB : B.all Gate.isUnitary = true) : j = 0 := by
  have hn := nBits_of_mbu hgates hB
  have hb := hWF.bitsOk
  rw [Circuit.bitsOk, hgates, bitsOkFrom_append_list, Bool.and_eq_true, mbuUncompute,
    bitsOkFrom_append_list, bitsOkFrom_append_list, Bool.and_eq_true, Bool.and_eq_true] at hb
  have := hb.2.1.1
  simp only [Circuit.bitsOkFrom, Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- A sum over the branches of a one-bit circuit is a sum over the bit's value. -/
theorem sum_branches_one_bit {M : Type} [AddCommMonoid M] {m : ℕ} (hm : m = 1) (j : ℕ)
    (hj : j = 0) (G : Bool → M) :
    ∑ c : Fin m → Bool, G (bitVal c j) = G true + G false := by
  subst hm hj
  rw [← Fintype.sum_bool]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _ _ fun c => by
    simp [bitVal, Equiv.funUnique]

/-- The data action of MBU without its correction in the branch `b`: `diag φ` on the branch 0,
`diag (φ · (−1)^f)` on the branch 1. -/
def mbuBranchU (φ : Reg n → ℂ) (hφ : ∀ x, ‖φ x‖ = 1) (f : Reg n → Bool) (b : Bool) : 𝐔[Reg n] :=
  diagU (fun x => φ x * (if b then (if f x then -1 else 1) else 1)) (fun x => by
    rw [norm_mul, hφ x]; cases b <;> cases f x <;> simp)

theorem mbuBranchU_false (φ : Reg n → ℂ) (hφ : ∀ x, ‖φ x‖ = 1) (f : Reg n → Bool) :
    mbuBranchU φ hφ f false = diagU φ hφ :=
  diagU_congr (fun x => by simp) _ _

theorem mbuBranchU_true (φ : Reg n → ℂ) (hφ : ∀ x, ‖φ x‖ = 1) (f : Reg n → Bool) :
    mbuBranchU φ hφ f true = diagU (fun x => φ x * (if f x then -1 else 1)) (norm_mul_sign hφ f) :=
  diagU_congr (fun x => by simp) _ _

/-- Report §6.2.2, PHASE2_SPEC §B.2 (23a) — **MBU without its correction, general compute phase**:
with a compute block for `f` with phase `φ` and the reset without correction
(`mbuUncompute t j []`), the ancilla is restored and the data undergoes the mixture of `diag φ`
(the branch 0) and `diag (φ · (−1)^f)` (the branch 1), each with weight `1/2`. -/
theorem mbu_uncorrected_mix {C : Circuit} (hWF : C.WF) {B : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j []) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} {φ : Reg n → ℂ} (hB : ComputesInto n a B t f φ) (ρ : MState (Reg n)) :
    (channelDenote n a C (ρ ⊗ᴹ ancZero a)).m =
      (1 / 2 : ℂ) • ((diagU (fun x => φ x * (if f x then -1 else 1)) (norm_mul_sign hB.norm f) ◃ ρ)
          ⊗ᴹ ancZero a).m +
      (1 / 2 : ℂ) • ((diagU φ hB.norm ◃ ρ) ⊗ᴹ ancZero a).m := by
  have hn : C.nBits = 1 := nBits_of_mbu hgates hB.unitary
  have hj : j = 0 := mbu_bit_eq_zero hWF hgates hB.unitary
  -- the two branch unitaries, by the value of the bit
  set Ub : Bool → 𝐔[Reg n] := mbuBranchU φ hB.norm f with hUb
  have hO0 : unitaryDenote n a [] = (1 : ℂ) • (phaseDiag (fun _ : Reg n => false) ⊗ₖ
      (1 : Matrix (Reg a) (Reg a) ℂ)) := by
    rw [unitaryDenote_nil, phaseDiag_false, Matrix.one_kronecker_one, one_smul]
  -- the Kraus operator of the branch `c` on |x, 0…0⟩
  have hKx : ∀ (c : Fin C.nBits → Bool) (x : Reg n),
      krausOps n a C.nBits C.gates c *ᵥ basisVec (x, fun _ => false) =
        (((Real.sqrt 2)⁻¹ : ℂ) * (φ x * (if bitVal c j then (if f x then -1 else 1) else 1))) •
          basisVec (x, fun _ => false) := by
    intro c x
    rw [hgates, krausOps_append_gates, krausOps_of_unitary n a _ B hB.unitary,
      ← Matrix.mulVec_mulVec, hB.denote x, Matrix.mulVec_smul,
      mbuUncompute_kraus_basis n a _ hanc j c hO0 x (f x), smul_smul]
    congr 1
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  have hK : ∀ c, krausOps n a C.nBits C.gates c * ancProj n a =
      ((Real.sqrt 2)⁻¹ : ℂ) • ((Ub (bitVal c j)).val ⊗ₖ (ancZero a).m) := by
    intro c
    ext i ⟨x, w⟩
    rw [← mulVec_basisVec (krausOps n a C.nBits C.gates c * ancProj n a), ← Matrix.mulVec_mulVec,
      ancProj_mulVec_basisVec]
    simp only [Matrix.smul_apply, kroneckerMap_apply, ancZero_m_apply, hUb, mbuBranchU, diagU_val,
      diagonal_apply, smul_eq_mul]
    by_cases hw : w = fun _ => false
    · subst hw
      simp only [↓reduceIte, and_true]
      rw [hKx c x]
      obtain ⟨i1, i2⟩ := i
      simp only [Pi.smul_apply, smul_eq_mul, basisVec, Prod.mk.injEq]
      by_cases h1 : i1 = x <;> by_cases h2 : i2 = fun _ => false <;> simp [h1, h2]
    · simp [hw]
  rw [ancRestoreMix_of_kraus hWF (fun c => Ub (bitVal c j)) (fun _ => ((Real.sqrt 2)⁻¹ : ℂ)) hK ρ]
  rw [sum_branches_one_bit hn j hj
    (fun b => ((‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 : ℝ) : ℂ) • ((Ub b ◃ ρ) ⊗ᴹ ancZero a).m)]
  have hw : ((‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [norm_sq_invSqrtTwo]; push_cast; ring
  rw [hw, hUb, mbuBranchU_true, mbuBranchU_false]

/-- Report §6.2.2, PHASE2_SPEC §B.2 (23a) — **MBU without its correction dephases**: a phase-exact
compute block for `f` followed by the reset without correction restores the ancilla and maps the
data to `½ ρ + ½ O_f ρ O_fᴴ` — the dephasing in the basis of `f`. This is the precise sense of
"restoration under measurement" (report §6.2.3). -/
theorem mbu_uncorrected {C : Circuit} (hWF : C.WF) {B : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j []) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} (hB : ComputesInto n a B t f fun _ => 1) (ρ : MState (Reg n)) :
    (channelDenote n a C (ρ ⊗ᴹ ancZero a)).m =
      (1 / 2 : ℂ) • (ρ ⊗ᴹ ancZero a).m +
      (1 / 2 : ℂ) • ((phaseOracle f ◃ ρ) ⊗ᴹ ancZero a).m := by
  rw [mbu_uncorrected_mix hWF hgates hanc hB ρ, diagU_one, one_uConj, diagU_one_mul_sign, add_comm]

/-- `mbu_uncorrected` with `Z t` between the compute block and the reset: the same dephasing (the
two branches exchange their roles). -/
theorem mbu_uncorrected_phase {C : Circuit} (hWF : C.WF) {B : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ [.z t] ++ mbuUncompute t j []) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} (hB : ComputesInto n a B t f fun _ => 1) (ρ : MState (Reg n)) :
    (channelDenote n a C (ρ ⊗ᴹ ancZero a)).m =
      (1 / 2 : ℂ) • (ρ ⊗ᴹ ancZero a).m +
      (1 / 2 : ℂ) • ((phaseOracle f ◃ ρ) ⊗ᴹ ancZero a).m := by
  rw [mbu_uncorrected_mix hWF hgates hanc (hB.z hanc) ρ]
  have h1 : diagU (fun x => (fun _ : Reg n => (1 : ℂ)) x * (if f x then -1 else 1) *
      (if f x then -1 else 1)) (norm_mul_sign (hB.z hanc).norm f) = 1 := by
    rw [← diagU_one (fun _ => by simp)]
    exact diagU_congr (fun x => by cases f x <;> simp) _ _
  rw [h1, one_uConj, diagU_one_mul_sign]

end Mix

/-! ## N3 — widening, or ancilla reuse -/

section Widen

variable {n a b : ℕ}

/-- The ancilla qubits of a gate list lie below `a`. -/
def Qubit.ancBelow (a : ℕ) : Qubit → Bool
  | .data _ => true
  | .anc i => decide (i < a)

/-- Every ancilla qubit of every gate lies below `a`: the block touches only the first `a`
ancillae. -/
def ancsBelow (gs : List Gate) (a : ℕ) : Bool := gs.all fun g => g.qubits.all (Qubit.ancBelow a)

/-- The split of the wider ancilla register: the first `a` and the last `b` bits. -/
def splitReg (w : Reg (a + b)) : Reg a × Reg b :=
  (fun i => w (Fin.castAdd b i), fun i => w (Fin.natAdd a i))

theorem splitReg_append (u : Reg a) (v : Reg b) : splitReg (Fin.append u v) = (u, v) := by
  simp [splitReg, Fin.append_left, Fin.append_right]

theorem append_splitReg (w : Reg (a + b)) : Fin.append (splitReg w).1 (splitReg w).2 = w :=
  Fin.append_castAdd_natAdd

/-- `Reg (a + b) ≃ Reg a × Reg b`. -/
def regEquiv (a b : ℕ) : Reg (a + b) ≃ Reg a × Reg b where
  toFun := splitReg
  invFun p := Fin.append p.1 p.2
  left_inv := append_splitReg
  right_inv p := splitReg_append p.1 p.2

/-- The wider register as the narrower register times the extra ancillae. -/
def wEquiv (n a b : ℕ) : Reg n × Reg (a + b) ≃ (Reg n × Reg a) × Reg b :=
  ((Equiv.refl (Reg n)).prodCongr (regEquiv a b)).trans (Equiv.prodAssoc _ _ _).symm

theorem wEquiv_apply (u : Reg n × Reg (a + b)) :
    wEquiv n a b u = ((u.1, (splitReg u.2).1), (splitReg u.2).2) := rfl

theorem splitReg_update_castAdd (w : Reg (a + b)) (i : Fin a) (v : Bool) :
    splitReg (Function.update w (Fin.castAdd b i) v) =
      (Function.update (splitReg w).1 i v, (splitReg w).2) := by
  simp only [splitReg, Prod.mk.injEq]
  constructor
  · funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne]
      exact fun h => hk (Fin.castAdd_injective _ _ h)
  · funext k
    rw [Function.update_of_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega

/-- `Qubit.get` on the wider register reads the narrower part (ancillae below `a`). -/
theorem get_wide {q : Qubit} (hq : q.ancBelow a = true) (u : Reg n × Reg (a + b)) :
    q.get u = q.get ((wEquiv n a b u).1) := by
  cases q with
  | data i => rfl
  | anc i =>
    have hi : i < a := by simpa [Qubit.ancBelow] using hi_of hq
    simp only [Qubit.get, wEquiv_apply, hi, show i < a + b by omega, ↓reduceDIte, splitReg]
    rfl
  where hi_of {i : ℕ} (h : (Qubit.anc i).ancBelow a = true) : (Qubit.anc i).ancBelow a = true := h

/-- `Qubit.set` on the wider register acts on the narrower part. -/
theorem set_wide {q : Qubit} (hq : q.ancBelow a = true) (v : Bool) (u : Reg n × Reg (a + b)) :
    wEquiv n a b (q.set v u) = (q.set v (wEquiv n a b u).1, (wEquiv n a b u).2) := by
  cases q with
  | data i =>
    simp only [Qubit.set, wEquiv_apply]
    split_ifs <;> rfl
  | anc i =>
    have hi : i < a := by simpa [Qubit.ancBelow] using hq
    simp only [Qubit.set, wEquiv_apply, hi, show i < a + b by omega, ↓reduceDIte]
    have : (⟨i, show i < a + b by omega⟩ : Fin (a + b)) = Fin.castAdd b ⟨i, hi⟩ := Fin.ext rfl
    rw [this, splitReg_update_castAdd]

theorem flip_wide {q : Qubit} (hq : q.ancBelow a = true) (u : Reg n × Reg (a + b)) :
    wEquiv n a b (q.flip u) = (q.flip (wEquiv n a b u).1, (wEquiv n a b u).2) := by
  rw [Qubit.flip, Qubit.flip, set_wide hq, get_wide hq]

theorem cnotPerm_wide {c t : Qubit} (hc : c.ancBelow a = true) (ht : t.ancBelow a = true)
    (u : Reg n × Reg (a + b)) :
    wEquiv n a b (cnotPerm n (a + b) c t u) =
      (cnotPerm n a c t (wEquiv n a b u).1, (wEquiv n a b u).2) := by
  rw [cnotPerm, cnotPerm, get_wide hc]
  split_ifs
  · exact flip_wide ht u
  · rfl

/-- A matrix on the narrower register, tensored with `1` on the extra ancillae, on the wider
register. -/
def wide (M : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    Matrix (Reg n × Reg (a + b)) (Reg n × Reg (a + b)) ℂ :=
  (M ⊗ₖ (1 : Matrix (Reg b) (Reg b) ℂ)).submatrix (wEquiv n a b) (wEquiv n a b)

/-- A matrix on the narrower register, tensored with |0⟩⟨0| on the extra ancillae. -/
def wideZ (M : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    Matrix (Reg n × Reg (a + b)) (Reg n × Reg (a + b)) ℂ :=
  (M ⊗ₖ (ancZero b).m).submatrix (wEquiv n a b) (wEquiv n a b)

theorem wide_mul (A B : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    wide (b := b) A * wide B = wide (A * B) := by
  rw [wide, wide, wide, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem wide_one : wide (b := b) (1 : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) = 1 := by
  rw [wide, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem wide_smul (c : ℂ) (A : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    wide (b := b) (c • A) = c • wide A := by
  rw [wide, wide, Matrix.smul_kronecker, Matrix.submatrix_smul]
  rfl

theorem wide_add (A B : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    wide (b := b) (A + B) = wide A + wide B := by
  rw [wide, wide, wide, Matrix.add_kronecker, Matrix.submatrix_add]
  rfl

theorem wide_conjTranspose (A : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    (wide (b := b) A)ᴴ = wide Aᴴ := by
  rw [wide, wide, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

theorem wide_mul_wideZ_mul_wide (A M B : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    wide (b := b) A * wideZ M * wide B = wideZ (A * M * B) := by
  rw [wide, wideZ, wide, wideZ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem wideZ_sum {ι : Type} (s : Finset ι) (F : ι → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    ∑ c ∈ s, wideZ (b := b) (F c) = wideZ (∑ c ∈ s, F c) := by
  ext i j
  simp only [wideZ, Matrix.sum_apply, Matrix.submatrix_apply, kroneckerMap_apply, Finset.sum_mul]

/-- A monomial matrix on the wider register whose permutation and phase act on the narrower part
is the widening of the narrower monomial matrix. -/
theorem monoMat_wide {σ : Reg n × Reg a → Reg n × Reg a} {φ : Reg n × Reg a → ℂ}
    {σ' : Reg n × Reg (a + b) → Reg n × Reg (a + b)} {φ' : Reg n × Reg (a + b) → ℂ}
    (hσ : ∀ u, wEquiv n a b (σ' u) = (σ (wEquiv n a b u).1, (wEquiv n a b u).2))
    (hφ : ∀ u, φ' u = φ (wEquiv n a b u).1) :
    monoMat σ' φ' = wide (monoMat σ φ) := by
  ext u v
  rw [wide, Matrix.submatrix_apply, kroneckerMap_apply, monoMat_apply, monoMat_apply, one_apply, hφ]
  have hiff : u = σ' v ↔ (wEquiv n a b u).1 = σ (wEquiv n a b v).1 ∧
      (wEquiv n a b u).2 = (wEquiv n a b v).2 := by
    rw [← (wEquiv n a b).injective.eq_iff, hσ, Prod.ext_iff]
  split_ifs <;> simp_all

/-- The qubits of a gate all lie below `a`, from `ancsBelow`. -/
theorem ancBelow_of_mem {gs : List Gate} (h : ancsBelow gs a = true) {g : Gate} (hg : g ∈ gs)
    {q : Qubit} (hq : q ∈ g.qubits) : q.ancBelow a = true := by
  rw [ancsBelow, List.all_eq_true] at h
  have := h g hg
  rw [List.all_eq_true] at this
  exact this q hq

theorem inRange_wide {q : Qubit} (hq : q.ancBelow a = true) :
    q.inRange n (a + b) = q.inRange n a := by
  cases q with
  | data i => rfl
  | anc i =>
    have hi : i < a := by simpa [Qubit.ancBelow] using hq
    simp [Qubit.inRange, hi, show i < a + b by omega]

/-- **The gate matrices widen**: a gate whose ancillae lie below `a` has, on the wider register, the
widening of its matrix on the narrower one. -/
theorem gateU_wide (g : Gate) (hg : ∀ q ∈ g.qubits, q.ancBelow a = true) :
    gateU n (a + b) g = wide (gateU n a g) := by
  have hmono : ∀ (q : Qubit) (hq : q.ancBelow a = true) (p : ℂ),
      phaseMat n (a + b) q p = wide (phaseMat n a q p) := fun q hq p =>
    monoMat_wide (fun u => by simp) (fun u => by rw [get_wide hq])
  cases g with
  | h q =>
    have hq := hg q (by simp [Gate.qubits])
    simp only [gateU, inRange_wide hq]
    split_ifs
    · rw [hMat, hMat, wide_smul, wide_add]
      congr 2
      · exact monoMat_wide (fun u => by simp) (fun u => by rw [get_wide hq])
      · exact monoMat_wide (fun u => flip_wide hq u) (fun u => rfl)
    · exact wide_one.symm
  | s q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | sdg q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | t q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | tdg q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | z q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | p m k q => exact hmono q (hg q (by simp [Gate.qubits])) _
  | x q =>
    have hq := hg q (by simp [Gate.qubits])
    exact monoMat_wide (fun u => flip_wide hq u) (fun u => rfl)
  | cnot c t =>
    have hc := hg c (by simp [Gate.qubits])
    have ht := hg t (by simp [Gate.qubits])
    simp only [gateU]
    split_ifs
    · exact wide_one.symm
    · exact monoMat_wide (fun u => cnotPerm_wide hc ht u) (fun u => rfl)
  | cz c t =>
    have hc := hg c (by simp [Gate.qubits])
    have ht := hg t (by simp [Gate.qubits])
    exact monoMat_wide (fun u => by simp) (fun u => by rw [get_wide hc, get_wide ht])
  | cp m k c t =>
    have hc := hg c (by simp [Gate.qubits])
    have ht := hg t (by simp [Gate.qubits])
    exact monoMat_wide (fun u => by simp) (fun u => by rw [get_wide hc, get_wide ht])
  | measure q j => exact wide_one.symm
  | ifBit j g => exact wide_one.symm
  | alloc q => exact wide_one.symm
  | free q => exact wide_one.symm

/-- The Kraus factors widen. -/
theorem gateK_wide {m : ℕ} (c : Fin m → Bool) (g : Gate) (hg : ∀ q ∈ g.qubits, q.ancBelow a = true) :
    gateK n (a + b) c g = wide (gateK n a c g) := by
  cases g with
  | measure q j =>
    have hq := hg q (by simp [Gate.qubits])
    simp only [gateK, projMat]
    exact monoMat_wide (fun u => by simp) (fun u => by rw [get_wide hq])
  | ifBit j g' =>
    simp only [gateK]
    split_ifs
    · exact gateU_wide g' hg
    · exact wide_one.symm
  | _ => exact gateU_wide _ hg

/-- **The Kraus operators widen.** -/
theorem krausOps_wide {m : ℕ} (gs : List Gate) (hgs : ancsBelow gs a = true) (c : Fin m → Bool) :
    krausOps n (a + b) m gs c = wide (krausOps n a m gs c) := by
  induction gs with
  | nil => exact wide_one.symm
  | cons g gs ih =>
    have hg : ancsBelow gs a = true := by
      rw [ancsBelow, List.all_eq_true] at hgs ⊢
      exact fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    rw [krausOps, krausOps, ih hg, gateK_wide c g (fun q hq => ancBelow_of_mem hgs
      (List.mem_cons_self ..) hq), wide_mul]

theorem splitReg_zero : splitReg (fun _ : Fin (a + b) => false) = (fun _ => false, fun _ => false) := by
  simp [splitReg]

theorem splitReg_eq_zero_iff (w : Reg (a + b)) :
    w = (fun _ => false) ↔ (splitReg w).1 = (fun _ => false) ∧ (splitReg w).2 = (fun _ => false) := by
  constructor
  · rintro rfl
    rw [splitReg_zero]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← append_splitReg w, h1, h2]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]

/-- **The clean input and output factorize**: `σ ⊗ |0…0⟩⟨0…0|` on `a + b` ancillae is the widening
by |0⟩⟨0| of `σ ⊗ |0…0⟩⟨0…0|` on `a` ancillae. -/
theorem prod_ancZero_wide (σ : MState (Reg n)) :
    (σ ⊗ᴹ ancZero (a + b)).m = wideZ ((σ ⊗ᴹ ancZero a).m) := by
  ext ⟨x, w⟩ ⟨y, v⟩
  rw [prod_ancZero_m, prod_ancZero_m, wideZ, Matrix.submatrix_apply, kroneckerMap_apply,
    kroneckerMap_apply, kroneckerMap_apply, wEquiv_apply, wEquiv_apply, ancZero_m_apply,
    ancZero_m_apply, ancZero_m_apply]
  simp only [splitReg_eq_zero_iff w, splitReg_eq_zero_iff v]
  by_cases h1 : (splitReg w).1 = fun _ => false <;> by_cases h2 : (splitReg w).2 = fun _ => false <;>
  by_cases h3 : (splitReg v).1 = fun _ => false <;> by_cases h4 : (splitReg v).2 = fun _ => false <;>
    simp [h1, h2, h3, h4]

/-- Report §6.2.4, PHASE2_SPEC §B.2 (23a) — **widening, or ancilla reuse**: a block whose ancillae
lie below `a` and which restores its `a` ancillae applying `U` restores its `a + b` ancillae
applying `U`. Every Kraus operator on the wider register is the narrower one tensored with `1`
(`krausOps_wide`), and the clean input and output factorize (`prod_ancZero_wide`). -/
theorem AncRestore.widen {C : Circuit} (hC : C.WF) (hq : ancsBelow C.gates a = true) {U : 𝐔[Reg n]}
    (h : AncRestore n a C U) : AncRestore n (a + b) C U := by
  intro ρ
  apply MState.ext_m
  have hm := congrArg MState.m (h ρ)
  rw [channelDenote_m hC] at hm
  rw [channelDenote_m hC, prod_ancZero_wide, prod_ancZero_wide]
  simp only [krausOps_wide C.gates hq, wide_conjTranspose, wide_mul_wideZ_mul_wide]
  rw [wideZ_sum, hm]

/-- PHASE2_SPEC §B.2 (23a) — **ancilla reuse across certified blocks**: two blocks certified on
`a₁` and `a₂` ancillae compose on any register with `a ≥ a₁, a₂` ancillae. -/
theorem AncRestore.comp_widen {a₁ a₂ a : ℕ} {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]} (h₁ : C₁.WF)
    (h₂ : C₂.WF) (hq₁ : ancsBelow C₁.gates a₁ = true) (hq₂ : ancsBelow C₂.gates a₂ = true)
    (ha₁ : a₁ ≤ a) (ha₂ : a₂ ≤ a) (r₁ : AncRestore n a₁ C₁ U₁) (r₂ : AncRestore n a₂ C₂ U₂) :
    AncRestore n a (C₁.append C₂) (U₂ * U₁) := by
  obtain ⟨b₁, rfl⟩ := Nat.exists_eq_add_of_le ha₁
  obtain ⟨b₂, hb₂⟩ := Nat.exists_eq_add_of_le ha₂
  have w₁ : AncRestore n (a₁ + b₁) C₁ U₁ := r₁.widen h₁ hq₁
  have w₂ : AncRestore n (a₂ + b₂) C₂ U₂ := r₂.widen h₂ hq₂
  rw [← hb₂] at w₂
  exact AncRestore.comp h₁.bitsOk h₂.bitsOk w₁ w₂

end Widen

end CQRV

end

end
