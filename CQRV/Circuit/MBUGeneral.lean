module

public import CQRV.Circuit.Restoration
public import CQRV.Circuit.UnitaryChannel
public import CQRV.Circuit.OracleBlocks

/-!
# CQRV.Circuit.MBUGeneral

Stage 22a (PHASE2_SPEC §B.1; report §6.2.1, §6.2.2, §6.2.4; Track B) — **the general MBU
theorem**. `mbu_channel_correct` (Stage 6b-1) proves measurement-based uncomputation for one
gadget, the temporary logical-AND with the correction `CZ`. This module proves it for every
phase-exact compute block: if a measurement-free block `B` computes a Boolean function `f` of the
data's computational basis into a clean ancilla `t` (`ComputesInto`, with a phase `φ x` per basis
state), and `O` is a phase implementation of `f` on the data (`PhaseImpl`: `λ · (diag((−1)^f) ⊗ 1)`),
then "H t; measure t → j; if j: O; if j: X t" (`mbuUncompute t j O`) restores the ancilla and
applies `diag φ` to the data (`mbu_general`); with `Z t` between compute and uncompute it applies
`diag(φ · (−1)^f)` (`mbu_general_phase`). At `φ = 1` the two conclusions are the identity and
`phaseOracle f`.

In words: in the X basis, the outcome 1 leaves the phase `(−1)^{f x}` on the data, and `O` removes
it; the outcome 0 leaves nothing; the reset returns the ancilla to |0⟩. A compute phase `φ` is
**not** removed by MBU — the compute block must be phase-exact, or `diag φ` stays on the data. The
temporary AND is phase-exact (`tempLogicalAND_correct_lift`), and `mbu_channel_correct_of_general`
re-derives the Stage 6b-1 statement from `mbu_general_phase` with `B = TempLogicalAND`,
`f = a ∧ b`, `O = [CZ a b]`, `φ = 1`. The Stage 6b-1 proof stays.

Proof route (report §6.2.4 Layer 3 template): `ancRestore_of_kraus` with `l_c = λ_c/√2`, `λ_c = 1`
on the branch 0 and `λ` on the branch 1; `K_c · P` is computed column by column
(`krausOps_append_gates`, `krausOps_of_unitary` on `B`, `ComputesInto` on |x, 0⟩, then the gates of
`mbuUncompute` on |x, e_t(f x)⟩ through basis-vector lemmas).
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix CQRV.Synthesis
open scoped MState Kronecker

/-! ## K1 — definitions -/

/-- A data qubit (`x[i]`). -/
def Qubit.isData : Qubit → Bool
  | .data _ => true
  | .anc _ => false

/-- Report §6.2.1 — the ancilla basis state `e_t(b)`: the ancilla qubit `t` holds `b`, every other
ancilla `0` (for `t = anc i`; for a data qubit `t` it is |0…0⟩). -/
def ancBasis (a : ℕ) (t : Qubit) (b : Bool) : Reg a :=
  fun k => if t = .anc k.val then b else false

theorem ancBasis_false (a : ℕ) (t : Qubit) : ancBasis a t false = fun _ => false := by
  funext k
  simp [ancBasis]

theorem get_ancBasis {n a : ℕ} {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (x : Reg n)
    (b : Bool) : t.get (x, ancBasis a t b) = b := by
  obtain ⟨i, hi, rfl⟩ := hanc
  simp [Qubit.get, hi, ancBasis]

theorem flip_ancBasis {n a : ℕ} {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (x : Reg n)
    (b : Bool) : t.flip (x, ancBasis a t b) = (x, ancBasis a t (!b)) := by
  obtain ⟨i, hi, rfl⟩ := hanc
  simp only [Qubit.flip, Qubit.get, Qubit.set, hi, ↓reduceDIte, Prod.mk.injEq, true_and]
  funext k
  simp only [Function.update_apply, ancBasis, Qubit.anc.injEq]
  by_cases hk : k = ⟨i, hi⟩
  · subst hk
    simp
  · have hik : ¬ i = k.val := fun h => hk (Fin.ext h.symm)
    simp [hk, hik]

/-- The ancilla qubit `t` reads `0` on |0…0⟩. -/
theorem get_ancZero {n a : ℕ} {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (x : Reg n) :
    t.get (x, (fun _ => false : Reg a)) = false := by
  obtain ⟨i, hi, rfl⟩ := hanc
  simp [Qubit.get, hi]

/-- Setting `t` on |0…0⟩ gives `e_t(b)`. -/
theorem set_ancBasis {n a : ℕ} {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (x : Reg n)
    (b : Bool) : t.set b (x, fun _ => false) = (x, ancBasis a t b) := by
  obtain ⟨i, hi, rfl⟩ := hanc
  simp only [Qubit.set, hi, ↓reduceDIte, Prod.mk.injEq, true_and]
  funext k
  simp only [Function.update_apply, ancBasis, Qubit.anc.injEq]
  by_cases hk : k = ⟨i, hi⟩
  · subst hk
    simp
  · have hik : ¬ i = k.val := fun h => hk (Fin.ext h.symm)
    simp [hk, hik]

/-- The value of a data qubit in a basis state. -/
theorem get_data {n a : ℕ} (i : ℕ) (h : i < n) (x : Reg n) (w : Reg a) :
    (Qubit.data i).get (x, w) = x ⟨i, h⟩ := by
  simp [Qubit.get, h]

/-- PHASE2_SPEC §B.1 — **a compute block** for `f` with phase `φ` (|φ x| = 1): a measurement-free
gate list mapping |x, 0…0⟩ to `φ x · |x, e_t(f x)⟩` for every data basis state `x`. Other
ancillae may be used inside `B` but come back to 0. -/
structure ComputesInto (n a : ℕ) (B : List Gate) (t : Qubit) (f : Reg n → Bool) (φ : Reg n → ℂ) :
    Prop where
  unitary : B.all Gate.isUnitary = true
  norm : ∀ x, ‖φ x‖ = 1
  denote : ∀ x : Reg n, unitaryDenote n a B *ᵥ basisVec (x, fun _ => false) =
    φ x • basisVec (x, ancBasis a t (f x))

/-- PHASE2_SPEC §B.1 — **a phase implementation** of `f`: a measurement-free gate list on data
qubits only whose unitary semantics is `λ · (diag((−1)^f) ⊗ 1)` for some |λ| = 1 (a global phase
is allowed: it lives in one measurement branch, and a scalar per branch does not disturb
restoration, `ancRestore_of_kraus`). -/
structure PhaseImpl (n a : ℕ) (O : List Gate) (f : Reg n → Bool) : Prop where
  unitary : O.all Gate.isUnitary = true
  dataOnly : O.all (fun g => g.qubits.all Qubit.isData) = true
  phase : ∃ lam : ℂ, ‖lam‖ = 1 ∧
    unitaryDenote n a O = lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))

/-- Report §6.2.2, PHASE2_SPEC §B.1 — **the MBU uncompute**: `H t; measure t → j; if j: O;
if j: X t` (the reset of the §6.2.2 erratum). -/
def mbuUncompute (t : Qubit) (j : ℕ) (O : List Gate) : List Gate :=
  [.h t, .measure t j] ++ O.map (Gate.ifBit j) ++ [.ifBit j (.x t)]

/-- Report §6.2.2 — the §6.2.2 listing is the instance with `O = [CZ a b]`. -/
theorem uncomputeTempLogicalAND_eq (a b t : Qubit) (m : ℕ) :
    UncomputeTempLogicalAND a b t m = mbuUncompute t m [.cz a b] := rfl

/-- Report §6.1.1 — the diagonal unitary `diag φ` of a phase function (|φ x| = 1). -/
def diagU {n : ℕ} (φ : Reg n → ℂ) (hφ : ∀ x, ‖φ x‖ = 1) : 𝐔[Reg n] :=
  ⟨Matrix.diagonal φ, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    simp only [Pi.star_apply]
    rw [Complex.star_def, Complex.conj_mul', hφ x]
    simp⟩

theorem diagU_val {n : ℕ} (φ : Reg n → ℂ) (hφ : ∀ x, ‖φ x‖ = 1) :
    (diagU φ hφ).val = Matrix.diagonal φ := rfl

/-- `diag 1 = 1`. -/
theorem diagU_one {n : ℕ} (h : ∀ _ : Reg n, ‖(1 : ℂ)‖ = 1) : diagU (fun _ => (1 : ℂ)) h = 1 :=
  Subtype.ext (by rw [diagU_val, Matrix.diagonal_one]; rfl)

/-- Report §6.1.1 — the phase oracle is `diag` of the sign function. -/
theorem phaseOracle_eq_diagU {n : ℕ} (f : Reg n → Bool)
    (h : ∀ x : Reg n, ‖(if f x then (-1 : ℂ) else 1)‖ = 1) :
    phaseOracle f = diagU (fun x => if f x then -1 else 1) h := rfl

theorem norm_sign {n : ℕ} (f : Reg n → Bool) : ∀ x : Reg n, ‖(if f x then (-1 : ℂ) else 1)‖ = 1 :=
  fun x => by split_ifs <;> simp

theorem norm_mul_sign {n : ℕ} {φ : Reg n → ℂ} (hφ : ∀ x, ‖φ x‖ = 1) (f : Reg n → Bool) :
    ∀ x, ‖φ x * (if f x then (-1 : ℂ) else 1)‖ = 1 := fun x => by
  rw [norm_mul, hφ x, norm_sign f x, one_mul]

/-- `diag(1 · (−1)^f) = phaseOracle f`. -/
theorem diagU_one_mul_sign {n : ℕ} (f : Reg n → Bool)
    (h : ∀ x : Reg n, ‖(1 : ℂ) * (if f x then (-1 : ℂ) else 1)‖ = 1) :
    diagU (fun x => (1 : ℂ) * (if f x then -1 else 1)) h = phaseOracle f :=
  Subtype.ext (by
    rw [diagU_val]
    show Matrix.diagonal _ = Matrix.diagonal _
    simp only [one_mul])

/-! ## Basis-vector forms of the gate matrices -/

section Vectors

variable (n a : ℕ)

theorem gateU_h_mulVec_basisVec {q : Qubit} (hq : q.inRange n a = true) (s : Reg n × Reg a) :
    gateU n a (.h q) *ᵥ basisVec s =
      ((Real.sqrt 2)⁻¹ : ℂ) • ((if q.get s then (-1 : ℂ) else 1) • basisVec s + basisVec (q.flip s)) := by
  funext i
  rw [gateU_h_mulVec n a hq]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVec, (Qubit.flip_involutive q).eq_iff]
  by_cases h : i = s
  · subst h
    simp
  · simp [h]

theorem projMat_mulVec_basisVec (q : Qubit) (v : Bool) (s : Reg n × Reg a) :
    projMat n a q v *ᵥ basisVec s = if q.get s = v then basisVec s else 0 := by
  funext i
  rw [projMat_mulVec]
  by_cases h : i = s
  · subst h
    by_cases hv : q.get i = v <;> simp [basisVec, hv]
  · by_cases hv : q.get s = v <;> simp [basisVec, h, hv]

theorem gateU_x_mulVec_basisVec (q : Qubit) (s : Reg n × Reg a) :
    gateU n a (.x q) *ᵥ basisVec s = basisVec (q.flip s) := by
  funext i
  rw [gateU_x_mulVec]
  simp only [basisVec, (Qubit.flip_involutive q).eq_iff]

theorem gateU_cnot_mulVec_basisVec {c t : Qubit} (hct : c ≠ t) (s : Reg n × Reg a) :
    gateU n a (.cnot c t) *ᵥ basisVec s = basisVec (cnotPerm n a c t s) := by
  funext i
  rw [gateU_cnot_mulVec n a hct]
  simp only [basisVec, (cnotPerm_involutive n a hct).eq_iff]

theorem phaseMat_mulVec_basisVec (q : Qubit) (p : ℂ) (s : Reg n × Reg a) :
    phaseMat n a q p *ᵥ basisVec s = (if q.get s then p else 1) • basisVec s := by
  funext i
  rw [phaseMat_mulVec]
  by_cases h : i = s
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

theorem phaseDiag_kronecker_one_mulVec_basisVec (f : Reg n → Bool) (x : Reg n) (w : Reg a) :
    (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) *ᵥ basisVec (x, w) =
      (if f x then (-1 : ℂ) else 1) • basisVec (x, w) := by
  funext ⟨i1, i2⟩
  rw [mulVec_basisVec, kroneckerMap_apply, phaseDiag, diagonal_apply, one_apply]
  simp only [Pi.smul_apply, basisVec, Prod.mk.injEq]
  by_cases h1 : i1 = x <;> by_cases h2 : i2 = w <;> simp [h1, h2]

/-- `CZ` on two data qubits is the phase oracle of their AND, tensored with the identity on the
ancillae. -/
theorem gateU_cz_data (i₁ i₂ : ℕ) (h₁ : i₁ < n) (h₂ : i₂ < n) :
    gateU n a (.cz (.data i₁) (.data i₂)) =
      phaseDiag (fun x => x ⟨i₁, h₁⟩ && x ⟨i₂, h₂⟩) ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  ext ⟨x, w⟩ ⟨y, v⟩
  simp only [gateU, monoMat_apply, kroneckerMap_apply, phaseDiag, diagonal_apply, one_apply, id,
    Qubit.get, h₁, h₂, ↓reduceDIte, Prod.mk.injEq]
  by_cases hxy : x = y <;> by_cases hwv : w = v <;> simp [hxy, hwv]

/-- `Z` on a data qubit is the phase oracle of that bit, tensored with the identity. -/
theorem gateU_z_data (i : ℕ) (h : i < n) :
    gateU n a (.z (.data i)) =
      phaseDiag (fun x => x ⟨i, h⟩) ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  ext ⟨x, w⟩ ⟨y, v⟩
  simp only [gateU, phaseMat, monoMat_apply, kroneckerMap_apply, phaseDiag, diagonal_apply,
    one_apply, id, Qubit.get, h, ↓reduceDIte, Prod.mk.injEq]
  by_cases hxy : x = y <;> by_cases hwv : w = v <;> simp [hxy, hwv]

theorem unitaryDenote_singleton (g : Gate) : unitaryDenote n a [g] = gateU n a g := by
  simp [unitaryDenote]

end Vectors

/-- Phase oracles multiply as their predicates XOR. -/
theorem phaseDiag_mul {n : ℕ} (P Q : Reg n → Bool) :
    phaseDiag P * phaseDiag Q = phaseDiag (fun x => xor (P x) (Q x)) := by
  simp only [phaseDiag, diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hP : P x = true <;> by_cases hQ : Q x = true <;> simp [hP, hQ]

/-! ## The Kraus operators of `mbuUncompute` -/

section Kraus

variable (n a : ℕ)

/-- In the branch `c`, the classically controlled gates `O.map (ifBit j)` act as `O` when bit `j`
reads 1 and as the identity otherwise. -/
theorem krausOps_map_ifBit (m j : ℕ) (O : List Gate) (c : Fin m → Bool) :
    krausOps n a m (O.map (Gate.ifBit j)) c = if bitVal c j then unitaryDenote n a O else 1 := by
  induction O with
  | nil => simp [krausOps, unitaryDenote]
  | cons g gs ih =>
    rw [List.map_cons, krausOps, ih, unitaryDenote]
    simp only [gateK]
    split_ifs <;> simp

theorem written_map_ifBit (j : ℕ) (O : List Gate) :
    Circuit.written (O.map (Gate.ifBit j)) = [] := by
  induction O with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.written, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

/-- `mbuUncompute` writes exactly the bit `j`. -/
theorem written_mbuUncompute (t : Qubit) (j : ℕ) (O : List Gate) :
    Circuit.written (mbuUncompute t j O) = [j] := by
  simp only [mbuUncompute, written_append_list, written_map_ifBit]
  rfl

/-- A compute block followed by one MBU uncompute has one classical bit. -/
theorem nBits_of_mbu {C : Circuit} {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hB : B.all Gate.isUnitary = true) :
    C.nBits = 1 := by
  rw [Circuit.nBits, hgates, written_append_list, Circuit.written_eq_nil_of_unitary hB,
    written_mbuUncompute]
  rfl

/-- Report §6.2.2, §6.2.4 Layer 2 — **the per-branch identity of MBU on a basis input**: in the
branch `c`, `mbuUncompute t j O` maps |x, e_t(b)⟩ to `(1/√2) · λ_c · |x, 0…0⟩`, where `λ_c = 1`
when bit `j` reads 0 and `λ · (−1)^{f x} · (−1)^b` when it reads 1 (so `λ` at `b = f x`). -/
theorem mbuUncompute_kraus_basis (m : ℕ) {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (j : ℕ)
    (c : Fin m → Bool) {O : List Gate} {f : Reg n → Bool} {lam : ℂ}
    (hO : unitaryDenote n a O = lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)))
    (x : Reg n) (b : Bool) :
    krausOps n a m (mbuUncompute t j O) c *ᵥ basisVec (x, ancBasis a t b) =
      (((Real.sqrt 2)⁻¹ : ℂ) * (if bitVal c j then
          lam * (if f x then -1 else 1) * (if b then -1 else 1) else 1)) •
        basisVec (x, fun _ => false) := by
  have ht : t.inRange n a = true := by
    obtain ⟨i, hi, rfl⟩ := hanc
    simp [Qubit.inRange, hi]
  have hsplit : mbuUncompute t j O =
      .h t :: .measure t j :: (O.map (Gate.ifBit j) ++ [.ifBit j (.x t)]) := rfl
  have hK_h : gateK n a c (.h t) = gateU n a (.h t) := rfl
  have hK_m : gateK n a c (.measure t j) = projMat n a t (bitVal c j) := rfl
  have hK_x : gateK n a c (.ifBit j (.x t)) = if bitVal c j then gateU n a (.x t) else 1 := rfl
  rw [hsplit, krausOps_cons_mulVec, krausOps_cons_mulVec, krausOps_append, ← Matrix.mulVec_mulVec,
    krausOps_map_ifBit, hK_h, hK_m, hK_x, gateU_h_mulVec_basisVec n a ht, get_ancBasis hanc,
    flip_ancBasis hanc]
  cases hv : bitVal c j <;> cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, smul_zero, add_zero, zero_add, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.one_mulVec, projMat_mulVec_basisVec, get_ancBasis hanc, get_ancZero hanc, hO,
      Matrix.smul_mulVec, phaseDiag_kronecker_one_mulVec_basisVec, gateU_x_mulVec_basisVec,
      flip_ancBasis hanc, ancBasis_false, smul_smul, one_smul, mul_one]
  -- the branch 1 at b = 1: `(1/√2) · (−1) · λ · (−1)^{f x}`
  congr 1
  ring

end Kraus

/-! ## K2 — the theorems -/

/-- Report §6.2.2, §6.2.4, PHASE2_SPEC §B.1 — **the general MBU theorem.** A well-formed circuit
whose gates are a compute block `B` for `f` with phase `φ` into the in-range ancilla `t`, followed
by `mbuUncompute t j O` with `O` a phase implementation of `f`, restores its ancillae and applies
`diag φ` to the data. The circuit's only measurement is that of `mbuUncompute`, so `C.nBits = 1`
(`nBits_of_mbu`; the hypothesis `C.nBits = j + 1` of the task text follows from `C.WF`, which
forces `j = 0`, and is not needed). Proof: `ancRestore_of_kraus` with `l_c = λ_c/√2`
(`mbuUncompute_kraus_basis`). -/
theorem mbu_general {n a : ℕ} {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} {φ : Reg n → ℂ} (hB : ComputesInto n a B t f φ) (hO : PhaseImpl n a O f) :
    AncRestore n a C (diagU φ hB.norm) := by
  obtain ⟨lam, hlam, hden⟩ := hO.phase
  have hn : C.nBits = 1 := nBits_of_mbu hgates hB.unitary
  have hsgn : ∀ x : Reg n, (if f x then (-1 : ℂ) else 1) * (if f x then -1 else 1) = 1 :=
    fun x => by split_ifs <;> norm_num
  -- the Kraus operator of the branch `c` on |x, 0…0⟩
  have hKx : ∀ (c : Fin C.nBits → Bool) (x : Reg n),
      krausOps n a C.nBits C.gates c *ᵥ basisVec (x, fun _ => false) =
        (((Real.sqrt 2)⁻¹ : ℂ) * (if bitVal c j then lam else 1) * φ x) •
          basisVec (x, fun _ => false) := by
    intro c x
    rw [hgates, krausOps_append_gates, krausOps_of_unitary n a _ B hB.unitary,
      ← Matrix.mulVec_mulVec, hB.denote x, Matrix.mulVec_smul,
      mbuUncompute_kraus_basis n a _ hanc j c hden x (f x), smul_smul]
    congr 1
    by_cases hv : bitVal c j = true
    · have h3 : lam * (if f x then (-1 : ℂ) else 1) * (if f x then -1 else 1) = lam := by
        rw [mul_assoc, hsgn x, mul_one]
      simp only [hv, ↓reduceIte, h3]
      ring
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      ring
  refine ancRestore_of_kraus hWF (diagU φ hB.norm)
    (fun c => ((Real.sqrt 2)⁻¹ : ℂ) * (if bitVal c j then lam else 1)) ?_ ?_
  · have h2 : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = 1 / 2 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
        inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hnorm : ∀ c : Fin C.nBits → Bool,
        ‖((Real.sqrt 2)⁻¹ : ℂ) * (if bitVal c j then lam else 1)‖ ^ 2 = 1 / 2 := by
      intro c
      rw [norm_mul, mul_pow, h2]
      split_ifs <;> simp [hlam]
    simp only [hnorm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, hn]
    norm_num
  · intro c
    ext i ⟨x, w⟩
    rw [← mulVec_basisVec (krausOps n a C.nBits C.gates c * ancProj n a), ← Matrix.mulVec_mulVec,
      ancProj_mulVec_basisVec]
    simp only [Matrix.smul_apply, kroneckerMap_apply, ancZero_m_apply, diagU_val, diagonal_apply,
      smul_eq_mul]
    by_cases hw : w = fun _ => false
    · subst hw
      simp only [↓reduceIte, and_true]
      rw [hKx c x]
      obtain ⟨i1, i2⟩ := i
      simp only [Pi.smul_apply, smul_eq_mul, basisVec, Prod.mk.injEq]
      by_cases h1 : i1 = x <;> by_cases h2 : i2 = fun _ => false <;> simp [h1, h2]
    · simp [hw]

/-- Report §6.2.2 — a compute block followed by `Z t` computes `f` with the phase `φ · (−1)^f`. -/
theorem ComputesInto.z {n a : ℕ} {B : List Gate} {t : Qubit} {f : Reg n → Bool} {φ : Reg n → ℂ}
    (hanc : ∃ i, i < a ∧ t = .anc i) (hB : ComputesInto n a B t f φ) :
    ComputesInto n a (B ++ [.z t]) t f (fun x => φ x * (if f x then -1 else 1)) where
  unitary := by rw [List.all_append, hB.unitary]; rfl
  norm := norm_mul_sign hB.norm f
  denote x := by
    rw [unitaryDenote_append, ← Matrix.mulVec_mulVec, hB.denote x, Matrix.mulVec_smul,
      unitaryDenote_singleton, gateU_z, phaseMat_mulVec_basisVec, get_ancBasis hanc, smul_smul]

/-- Report §6.2.2, PHASE2_SPEC §B.1 — **the general MBU theorem, phase form**: with `Z t` between
the compute block and the MBU uncompute, the circuit restores its ancillae and applies
`diag(φ · (−1)^f)` to the data — the oracle of `f` up to the compute phase. -/
theorem mbu_general_phase {n a : ℕ} {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit}
    {j : ℕ} (hgates : C.gates = B ++ [.z t] ++ mbuUncompute t j O)
    (hanc : ∃ i, i < a ∧ t = .anc i) {f : Reg n → Bool} {φ : Reg n → ℂ}
    (hB : ComputesInto n a B t f φ) (hO : PhaseImpl n a O f) :
    AncRestore n a C (diagU (fun x => φ x * (if f x then -1 else 1)) (norm_mul_sign hB.norm f)) :=
  mbu_general hWF hgates hanc (hB.z hanc) hO

/-- The φ = 1 corollary: a phase-exact compute block with MBU uncompute is the identity. -/
theorem mbu_general_one {n a : ℕ} {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} (hB : ComputesInto n a B t f fun _ => 1) (hO : PhaseImpl n a O f) :
    AncRestore n a C 1 := by
  have h := mbu_general hWF hgates hanc hB hO
  rwa [diagU_one] at h

/-- The φ = 1 corollary, phase form: a phase-exact compute block, `Z t`, and MBU uncompute apply
`phaseOracle f` — the oracle of `f` from any phase-exact way of computing `f` into an ancilla. -/
theorem mbu_general_phase_one {n a : ℕ} {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit}
    {j : ℕ} (hgates : C.gates = B ++ [.z t] ++ mbuUncompute t j O)
    (hanc : ∃ i, i < a ∧ t = .anc i) {f : Reg n → Bool}
    (hB : ComputesInto n a B t f fun _ => 1) (hO : PhaseImpl n a O f) :
    AncRestore n a C (phaseOracle f) := by
  have h := mbu_general_phase hWF hgates hanc hB hO
  rwa [diagU_one_mul_sign] at h

/-! ## The AND instance re-derived -/

/-- Report §6.2.2 — the temporary logical-AND on (x[0], x[1], anc[0]) is a phase-exact compute block
for `x0 ∧ x1` (`tempLogicalAND_correct_lift`). -/
theorem tempLogicalAND_computesInto :
    ComputesInto 2 1 (TempLogicalAND (.data 0) (.data 1) (.anc 0)) (.anc 0)
      (fun x => x 0 && x 1) (fun _ => 1) where
  unitary := by decide
  norm _ := by simp
  denote x := by
    have hanc : ∃ i, i < 1 ∧ (Qubit.anc 0) = .anc i := ⟨0, by norm_num, rfl⟩
    rw [tempLogicalAND_correct_lift (.data 0) (.data 1) (.anc 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (x, fun _ => false) rfl, set_ancBasis hanc]
    simp only [one_smul]
    rfl

/-- Report §6.2.2 — `[CZ x0 x1]` is a phase implementation of `x0 ∧ x1`. -/
theorem cz_phaseImpl : PhaseImpl 2 1 [.cz (.data 0) (.data 1)] (fun x => x 0 && x 1) where
  unitary := by decide
  dataOnly := by decide
  phase := ⟨1, by simp, by
    rw [one_smul, unitaryDenote_singleton]
    exact gateU_cz_data 2 1 0 1 (by norm_num) (by norm_num)⟩

/-- Report §6.2.2 — **`mbu_channel_correct` re-derived from `mbu_general_phase`**: the statement of
the Stage 6b-1 theorem, word for word, with `B = TempLogicalAND`, `f = x0 ∧ x1`, `O = [CZ x0 x1]`,
`φ = 1` (`czU` is `phaseOracle (x0 ∧ x1)`). A second proof; the Stage 6b-1 proof stays. -/
theorem mbu_channel_correct_of_general (ρ : MState (Reg 2)) :
    channelDenote 2 1 mbuCircuit (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 := by
  have hanc : ∃ i, i < 1 ∧ (Qubit.anc 0) = .anc i := ⟨0, by norm_num, rfl⟩
  have hg : mbuCircuit.gates = TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)] ++
      mbuUncompute (.anc 0) 0 [.cz (.data 0) (.data 1)] := rfl
  exact mbu_general_phase_one mbuCircuit_WF hg hanc tempLogicalAND_computesInto cz_phaseImpl ρ

end CQRV

end

end
