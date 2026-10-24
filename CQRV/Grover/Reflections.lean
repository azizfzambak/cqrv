module

public import CQRV.Circuit.OracleCorrect

/-!
# CQRV.Grover.Reflections

Report §8.2 (`U_s = 2|s⟩⟨s| − I = H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}`), §8.3.2 (the oracle reflects about
the bad subspace, the diffusion about `|s⟩`), §8.3.4 / Figure 8.1 (rows "Oracle reflection",
"Diffusion reflection") — the linear algebra of the Grover operator on
`Matrix (Reg n) (Reg n) ℂ` (Stage 7a item 3; DECISIONS.md 2026-10-24, Stage 7a decision 5):

* `H^{⊗n}` is `hadamardMat n`, entries `∏ᵢ (−1)^{xᵢ yᵢ}/√2 = (−1)^{x·y}/√2ⁿ`; it is its own
  inverse (`hadamardMat_mul_self`, a product of one-qubit sums).
* `oracle_reflection`: `U_P = I − 2Π_good`; `diffusion_reflection`:
  `H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n} = 2|s⟩⟨s| − I`; `diffU n` is `2|s⟩⟨s| − I` as a unitary.
* The circuit's diffusion is `H X · MCZ · X H = −(2|s⟩⟨s| − I)` (`diffusion_circuit_matrix`);
  the sign is global and invisible to the channel (`uConj_neg`, decision 5).
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis Matrix
open scoped MState

noncomputable section

/-! ## Matrices on the data register -/

/-- Report §8.2 — one Hadamard entry `⟨b|H|c⟩ = (−1)^{b c}/√2`. -/
def hEntry (b c : Bool) : ℂ := (if b && c then -1 else 1) * ((Real.sqrt 2)⁻¹ : ℂ)

/-- Report §8.2 — `H^{⊗n}` on `Reg n`: `⟨x|H^{⊗n}|y⟩ = ∏ᵢ (−1)^{xᵢ yᵢ}/√2`, i.e.
`(−1)^{x·y}/√2ⁿ` (`hadamardMat_apply`). -/
def hadamardMat (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, hEntry (x i) (y i)

/-- Report §8.2 — the basis state `0…0` of the data register. -/
def zeroReg (n : ℕ) : Reg n := fun _ => false

/-- Report §8.2 — bitwise negation, the action of `X^{⊗n}` on basis states. -/
def notAll {n : ℕ} (x : Reg n) : Reg n := fun i => !x i

/-- Report §8.2 — `X^{⊗n}` on `Reg n`. -/
def xAllMat (n : ℕ) : Matrix (Reg n) (Reg n) ℂ := monoMat notAll (fun _ => 1)

/-- Report §8.2 — `|0…0⟩⟨0…0|` on `Reg n`. -/
def proj0 (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => if x = zeroReg n ∧ y = zeroReg n then 1 else 0

/-- Report §8.2, §8.3.2 — the uniform superposition `|s⟩ = 2^{−n/2} ∑ₓ |x⟩ = H^{⊗n}|0…0⟩`. -/
def ketS (n : ℕ) : Reg n → ℂ := fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ n

/-- Report §8.2 — `|s⟩⟨s|`. -/
def projS (n : ℕ) : Matrix (Reg n) (Reg n) ℂ := Matrix.vecMulVec (ketS n) (star (ketS n))

/-- Report §8.3.2 — the projector `Π_good` onto the solutions of `P`. -/
def goodProj {n : ℕ} (P : Reg n → Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if P x then 1 else 0

/-- Report §8.2 — `P_all(y) = y₀ ∧ … ∧ y_{n−1}`, the predicate of the MCZ. -/
def allOnes {n : ℕ} (x : Reg n) : Bool := decide (∀ i, x i = true)

/-! ## `H^{⊗n}` -/

theorem hEntry_comm (b c : Bool) : hEntry b c = hEntry c b := by
  simp only [hEntry, Bool.and_comm]

theorem star_invSqrtTwo : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp

theorem star_hEntry (b c : Bool) : star (hEntry b c) = hEntry b c := by
  unfold hEntry
  rw [star_mul', star_invSqrtTwo]
  split_ifs <;> simp

/-- One-qubit `H · H = 1`, entrywise. -/
theorem hEntry_mul_sum (b d : Bool) :
    ∑ c, hEntry b c * hEntry c d = if b = d then 1 else 0 := by
  rw [Fintype.sum_bool]
  cases b <;> cases d <;> simp [hEntry] <;> linear_combination 2 * invSqrtTwo_mul_self

/-- Report §8.2 — the entries of `H^{⊗n}` are `(−1)^{x·y}/√2ⁿ`, with `x·y` the number of
positions where both bits are 1. -/
theorem hadamardMat_apply {n : ℕ} (x y : Reg n) :
    hadamardMat n x y =
      (-1) ^ (Finset.univ.filter fun i => (x i && y i) = true).card *
        ((Real.sqrt 2)⁻¹ : ℂ) ^ n := by
  simp only [hadamardMat, Matrix.of_apply, hEntry, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const, one_pow, mul_one, Finset.card_univ, Fintype.card_fin]

/-- Report §8.2 — `H^{⊗n} H^{⊗n} = 1`: `∑_y ∏ᵢ hᵢ(x, y) hᵢ(y, z) = ∏ᵢ ∑_c h(xᵢ, c) h(c, zᵢ)`. -/
theorem hadamardMat_mul_self (n : ℕ) : hadamardMat n * hadamardMat n = 1 := by
  ext x z
  rw [Matrix.mul_apply]
  simp only [hadamardMat, Matrix.of_apply]
  have key : ∑ y : Reg n, (∏ i, hEntry (x i) (y i)) * ∏ i, hEntry (y i) (z i) =
      ∏ i, ∑ c, hEntry (x i) c * hEntry c (z i) := by
    rw [Fintype.prod_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm
  rw [key]
  simp only [hEntry_mul_sum, Matrix.one_apply]
  by_cases hxz : x = z
  · subst hxz
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxz
    simp only [hxz, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem star_hadamardMat (n : ℕ) : star (hadamardMat n) = hadamardMat n := by
  ext x y
  simp only [Matrix.star_apply, hadamardMat, Matrix.of_apply, star_prod, star_hEntry]
  exact Finset.prod_congr rfl fun i _ => hEntry_comm _ _

theorem hadamardMat_mem (n : ℕ) : hadamardMat n ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_hadamardMat, hadamardMat_mul_self]

/-- Report §8.2 — `H^{⊗n}` as a unitary. -/
def hadamardU (n : ℕ) : 𝐔[Reg n] := ⟨hadamardMat n, hadamardMat_mem n⟩

theorem hadamardMat_zero_right {n : ℕ} (x : Reg n) :
    hadamardMat n x (zeroReg n) = ((Real.sqrt 2)⁻¹ : ℂ) ^ n := by
  simp [hadamardMat, zeroReg, hEntry]

theorem hadamardMat_zero_left {n : ℕ} (y : Reg n) :
    hadamardMat n (zeroReg n) y = ((Real.sqrt 2)⁻¹ : ℂ) ^ n := by
  simp [hadamardMat, zeroReg, hEntry]

/-- Report §8.2 — `H^{⊗n}|0…0⟩ = |s⟩`, column form. -/
theorem hadamardMat_mulVec_zero (n : ℕ) :
    hadamardMat n *ᵥ basisVec (zeroReg n) = ketS n := by
  funext x
  rw [mulVec_basisVec, hadamardMat_zero_right]
  rfl

/-! ## `X^{⊗n}` -/

theorem notAll_involutive {n : ℕ} : Function.Involutive (notAll (n := n)) := fun x => by
  funext i
  simp [notAll]

theorem xAllMat_mem (n : ℕ) : xAllMat n ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  monoMat_mem_unitaryGroup notAll_involutive (fun _ => by simp)

/-- Report §8.2 — `X^{⊗n}` as a unitary. -/
def xAllU (n : ℕ) : 𝐔[Reg n] := ⟨xAllMat n, xAllMat_mem n⟩

/-! ## The two reflections (Figure 8.1) -/

/-- Report §8.3.2, §8.3.4 Figure 8.1 ("Oracle reflection: `U_P` reflects about `ψ_b`",
est. 80 lines) — the phase oracle is `U_P = I − 2Π_good`. -/
theorem oracle_reflection {n : ℕ} (P : Reg n → Bool) :
    (phaseOracle P).val = 1 - (2 : ℂ) • goodProj P := by
  ext x y
  simp only [phaseOracle, phaseDiag, goodProj, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    cases P x <;> norm_num
  · simp [hxy]

/-- `H^{⊗n} |0⟩⟨0| H^{⊗n} = |s⟩⟨s|`. -/
theorem hadamard_proj0_hadamard (n : ℕ) :
    hadamardMat n * proj0 n * hadamardMat n = projS n := by
  ext x z
  have h1 : ∀ y, (hadamardMat n * proj0 n) x y =
      if y = zeroReg n then ((Real.sqrt 2)⁻¹ : ℂ) ^ n else 0 := by
    intro y
    rw [Matrix.mul_apply, Finset.sum_eq_single (zeroReg n)]
    · by_cases hy : y = zeroReg n
      · simp [proj0, hy, hadamardMat_zero_right]
      · simp [proj0, hy]
    · intro w _ hw
      simp [proj0, hw]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (zeroReg n)]
  · rw [h1, hadamardMat_zero_left]
    simp [projS, ketS, Matrix.vecMulVec_apply]
  · intro y _ hy
    simp [h1, hy]
  · simp

/-- Report §8.2, §8.3.2, §8.3.4 Figure 8.1 ("Diffusion reflection", est. 120 lines) —
`H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n} = 2|s⟩⟨s| − I`. -/
theorem diffusion_reflection (n : ℕ) :
    hadamardMat n * ((2 : ℂ) • proj0 n - 1) * hadamardMat n = (2 : ℂ) • projS n - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hadamardMat_mul_self, Matrix.mul_smul,
    Matrix.smul_mul, hadamard_proj0_hadamard]

/-- `2|0⟩⟨0| − I = −U_{[x = 0]}`: a diagonal of signs. -/
theorem two_proj0_sub_one (n : ℕ) :
    (2 : ℂ) • proj0 n - 1 = -(phaseOracle fun x => decide (x = zeroReg n)).val := by
  ext x y
  simp only [proj0, phaseOracle, phaseDiag, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.neg_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = zeroReg n <;> norm_num [hx]
  · have h : ¬ (x = zeroReg n ∧ y = zeroReg n) := fun h => hxy (h.1.trans h.2.symm)
    simp [hxy, h]

theorem neg_mem_unitaryGroup {n : ℕ} {A : Matrix (Reg n) (Reg n) ℂ}
    (h : A ∈ Matrix.unitaryGroup (Reg n) ℂ) : -A ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at h ⊢
  rw [star_neg, neg_mul_neg, h]

theorem diffMat_mem (n : ℕ) : (2 : ℂ) • projS n - 1 ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [← diffusion_reflection, two_proj0_sub_one]
  exact mul_mem (mul_mem (hadamardMat_mem n) (neg_mem_unitaryGroup (phaseOracle _).2))
    (hadamardMat_mem n)

/-- Report §8.2 — the diffusion `U_s = 2|s⟩⟨s| − I` as a unitary. -/
def diffU (n : ℕ) : 𝐔[Reg n] := ⟨(2 : ℂ) • projS n - 1, diffMat_mem n⟩

/-- Report §8.2, §3.2.4 — the Grover operator `G = U_s U_P` of the predicate `P`. -/
def groverOp {n : ℕ} (P : Reg n → Bool) : 𝐔[Reg n] := diffU n * phaseOracle P

/-! ## The circuit's diffusion and the global phase (decision 5) -/

theorem diagonal_eq_monoMat {n : ℕ} (d : Reg n → ℂ) : Matrix.diagonal d = monoMat id d := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [monoMat_apply]
  · simp [monoMat_apply, h]

/-- `X^{⊗n} U_P X^{⊗n} = U_{P ∘ ¬}`. -/
theorem xAll_phase_xAll {n : ℕ} (P : Reg n → Bool) :
    xAllMat n * (phaseOracle P).val * xAllMat n = (phaseOracle fun x => P (notAll x)).val := by
  change xAllMat n * phaseDiag P * xAllMat n = phaseDiag fun x => P (notAll x)
  rw [phaseDiag, phaseDiag, diagonal_eq_monoMat, diagonal_eq_monoMat, xAllMat, monoMat_mul,
    monoMat_mul]
  congr 1
  · funext x
    exact notAll_involutive x
  · funext x
    simp

theorem allOnes_notAll {n : ℕ} :
    (fun x : Reg n => allOnes (notAll x)) = fun x => decide (x = zeroReg n) := by
  funext x
  simp [allOnes, notAll, zeroReg, funext_iff]

/-- Report §8.2, decision 5 — the diffusion circuit's matrix `(H X)(MCZ (X H))` is
`−(2|s⟩⟨s| − I)`: `X^{⊗n} · MCZ · X^{⊗n} = U_{[x = 0]} = −(2|0⟩⟨0| − I)`, then
`diffusion_reflection`. -/
theorem diffusion_circuit_matrix (n : ℕ) :
    (hadamardMat n * xAllMat n) * ((phaseOracle (allOnes (n := n))).val *
      (xAllMat n * hadamardMat n)) = -(diffU n).val := by
  change _ = -((2 : ℂ) • projS n - 1)
  rw [← diffusion_reflection, two_proj0_sub_one, ← allOnes_notAll, ← xAll_phase_xAll]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

/-- Report §8.2, decision 5 — the channel does not see a global sign:
`(−V) ρ (−V)ᴴ = V ρ Vᴴ`. -/
theorem uConj_neg {n : ℕ} {U V : 𝐔[Reg n]} (h : U.val = -V.val) (ρ : MState (Reg n)) :
    U ◃ ρ = V ◃ ρ := by
  apply MState.ext_m
  change U.val * ρ.m * U.valᴴ = V.val * ρ.m * V.valᴴ
  rw [h, Matrix.conjTranspose_neg, Matrix.neg_mul, neg_mul_neg]

end

end CQRV.Grover

end
