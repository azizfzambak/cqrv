module

public import CQRV.Circuit.Semantics

/-!
# CQRV.Circuit.Basis

PHASE2_SPEC.md §A.2 (Stage 18b, docs/tasks/STAGE18_TASK.md B2) — the integer encodings of a
register `Reg m = Fin m → Bool`, with the convention of the harness
(`tests/diff/statevector.py`: **qubit 0 is the most significant bit** of the basis index):

* `Reg.toNat s = ∑_j [s j] 2^(m − 1 − j)` (big-endian, qubit 0 the MSB),
  `Reg.toNatLE s = ∑_j [s j] 2^j` (little-endian), `Reg.ofNat m x = fun j => x.testBit (m − 1 − j)`,
  `bitRev s = fun j => s (Fin.rev j)` with `(bitRev s).toNat = s.toNatLE`, and `reg0`, the
  unique element of `Reg 0` (the ancilla register of an ancilla-free circuit).
* `Reg.bit s l` reads bit `l : ℕ` of `s` (`false` outside the register); it is definitionally
  `Qubit.get (.data l)` on `Reg m × Reg a`, which lets the gate-by-gate proofs of
  `CQRV.Circuit.QFTCorrect` stay indexed by `ℕ`.
* Lemmas: `toNat_lt`, `ofNat_toNat`, `toNat_ofNat`, `toNat_injective`, `toNat_bitRev`,
  `bitRev_bitRev`, the range forms `toNat_eq_sum_range` / `toNatLE_eq_sum_range`, and the binary
  fraction `0.x_j … x_{m−1}` that block `j` of the QFT writes:
  `toNat_mod : s.toNat % 2^(m − j) = ∑ i : Fin m, if j ≤ i ∧ s i then 2^(m − 1 − i) else 0`
  (with the `Finset.Ico` form `toNat_mod_eq_sum_Ico`).
* `basisVec` and `mulVec_basisVec` stay in `CQRV.Circuit.Restoration` (the import layering did not
  need them here).
-/

@[expose] public section

namespace CQRV

/-- PHASE2_SPEC.md §A.2 — the unique element of `Reg 0`. -/
def reg0 : Reg 0 := fun i => i.elim0

theorem reg0_unique (s : Reg 0) : s = reg0 := funext fun i => i.elim0

namespace Reg

/-- Bit `l` of a register, `false` outside it (definitionally `Qubit.get (.data l)` on the data
component of `Reg m × Reg a`). -/
def bit {m : ℕ} (s : Reg m) (l : ℕ) : Bool := if h : l < m then s ⟨l, h⟩ else false

theorem bit_of_lt {m : ℕ} (s : Reg m) {l : ℕ} (h : l < m) : s.bit l = s ⟨l, h⟩ := by
  simp [bit, h]

theorem bit_of_le {m : ℕ} (s : Reg m) {l : ℕ} (h : m ≤ l) : s.bit l = false := by
  simp [bit, Nat.not_lt.mpr h]

theorem bit_fin {m : ℕ} (s : Reg m) (i : Fin m) : s.bit i = s i := bit_of_lt s i.isLt

theorem get_data {m a : ℕ} (l : ℕ) (p : Reg m × Reg a) : (Qubit.data l).get p = p.1.bit l := rfl

/-- Two registers with the same bits are equal. -/
theorem ext_bit {m : ℕ} {s t : Reg m} (h : ∀ l, s.bit l = t.bit l) : s = t :=
  funext fun i => by simpa [bit_fin] using h i

/-- PHASE2_SPEC.md §A.2 — the basis index, qubit 0 the most significant bit (the harness
convention). -/
def toNat {m : ℕ} (s : Reg m) : ℕ := ∑ j : Fin m, if s j then 2 ^ (m - 1 - j) else 0

/-- PHASE2_SPEC.md §A.2 — the little-endian reading. -/
def toNatLE {m : ℕ} (s : Reg m) : ℕ := ∑ j : Fin m, if s j then 2 ^ (j : ℕ) else 0

/-- PHASE2_SPEC.md §A.2 — the register with basis index `x` (qubit 0 the MSB). -/
def ofNat (m x : ℕ) : Reg m := fun j => x.testBit (m - 1 - j)

/-! ### The castSucc recursion -/

theorem toNat_succ {m : ℕ} (s : Reg (m + 1)) :
    s.toNat = 2 * toNat (Fin.init s) + (if s (Fin.last m) then 1 else 0) := by
  unfold toNat
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    have h : m + 1 - 1 - (j.castSucc : ℕ) = (m - 1 - j) + 1 := by
      rw [Fin.val_castSucc]; omega
    rw [h, pow_succ]
    by_cases hs : s j.castSucc = true
    · simp [Fin.init, hs, mul_comm]
    · simp [Fin.init, hs]
  · simp

theorem toNat_lt {m : ℕ} (s : Reg m) : s.toNat < 2 ^ m := by
  induction m with
  | zero => simp [toNat]
  | succ m ih =>
    rw [toNat_succ, pow_succ]
    have := ih (Fin.init s)
    split_ifs <;> omega

theorem ofNat_last (m x : ℕ) : ofNat (m + 1) x (Fin.last m) = decide (x % 2 = 1) := by
  simp [ofNat, Nat.testBit_zero]

theorem ofNat_castSucc (m x : ℕ) (j : Fin m) : ofNat (m + 1) x j.castSucc = ofNat m (x / 2) j := by
  simp only [ofNat, Fin.val_castSucc]
  have h : m + 1 - 1 - (j : ℕ) = (m - 1 - j) + 1 := by omega
  rw [h, Nat.testBit_succ]

theorem init_ofNat (m x : ℕ) : Fin.init (ofNat (m + 1) x) = ofNat m (x / 2) :=
  funext (ofNat_castSucc m x)

theorem ofNat_toNat {m : ℕ} (s : Reg m) : ofNat m s.toNat = s := by
  induction m with
  | zero => exact funext fun i => i.elim0
  | succ m ih =>
    have hdiv : s.toNat / 2 = toNat (Fin.init s) := by
      rw [toNat_succ]; split_ifs <;> omega
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [ofNat_last, toNat_succ]
      split_ifs with h <;> simp [h]
    · rw [ofNat_castSucc, hdiv, ih (Fin.init s)]
      rfl

theorem toNat_ofNat {m x : ℕ} (hx : x < 2 ^ m) : (ofNat m x).toNat = x := by
  induction m generalizing x with
  | zero => simp [toNat]; omega
  | succ m ih =>
    rw [toNat_succ, init_ofNat, ih (by rw [pow_succ] at hx; omega), ofNat_last]
    split_ifs with h <;> simp only [decide_eq_true_eq] at h <;> omega

theorem toNat_injective {m : ℕ} : Function.Injective (toNat (m := m)) :=
  fun s t h => by rw [← ofNat_toNat s, h, ofNat_toNat]

/-! ### Range forms (sums over `Finset.range m` through `Reg.bit`) -/

theorem toNat_eq_sum_range {m : ℕ} (s : Reg m) :
    s.toNat = ∑ l ∈ Finset.range m, if s.bit l then 2 ^ (m - 1 - l) else 0 := by
  unfold toNat
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l < m
  · simp [h, bit]
  · simp [h, bit]

theorem toNatLE_eq_sum_range {m : ℕ} (s : Reg m) :
    s.toNatLE = ∑ l ∈ Finset.range m, if s.bit l then 2 ^ l else 0 := by
  unfold toNatLE
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l < m
  · simp [h, bit]
  · simp [h, bit]

/-- The bits of a `k`-digit binary number read from the top: `∑_{i<k} [b i] 2^(k−1−i) < 2^k`. -/
theorem sum_range_pow_lt (k : ℕ) (b : ℕ → Bool) :
    (∑ i ∈ Finset.range k, if b i then 2 ^ (k - 1 - i) else 0) < 2 ^ k := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ', pow_succ]
    have h1 : (∑ i ∈ Finset.range k, if b (i + 1) then 2 ^ (k + 1 - 1 - (i + 1)) else 0) =
        ∑ i ∈ Finset.range k, if b (i + 1) then 2 ^ (k - 1 - i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
      rw [this]
    rw [h1]
    have h2 := ih (fun i => b (i + 1))
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    split_ifs <;> omega

/-- PHASE2_SPEC.md §A.2 — the binary fraction `0.x_j … x_{m−1}` as an integer: the low `m − j`
bits of `s.toNat` are the bits `j .. m − 1`. -/
theorem toNat_mod_eq_sum_Ico {m : ℕ} (s : Reg m) {j : ℕ} (hj : j ≤ m) :
    s.toNat % 2 ^ (m - j) = ∑ l ∈ Finset.Ico j m, if s.bit l then 2 ^ (m - 1 - l) else 0 := by
  rw [toNat_eq_sum_range, ← Finset.sum_range_add_sum_Ico _ hj]
  have hA : 2 ^ (m - j) ∣ ∑ l ∈ Finset.range j, if s.bit l then 2 ^ (m - 1 - l) else 0 := by
    apply Finset.dvd_sum
    intro l hl
    rw [Finset.mem_range] at hl
    split_ifs
    · exact pow_dvd_pow 2 (by omega)
    · exact dvd_zero _
  have hB : (∑ l ∈ Finset.Ico j m, if s.bit l then 2 ^ (m - 1 - l) else 0) < 2 ^ (m - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h := sum_range_pow_lt (m - j) (fun i => s.bit (j + i))
    refine lt_of_eq_of_lt ?_ h
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have : m - 1 - (j + i) = m - j - 1 - i := by omega
    rw [this]
  obtain ⟨q, hq⟩ := hA
  rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hB]

/-- PHASE2_SPEC.md §A.2 — `toNat_mod` in the form of the task text, a sum over `Fin m`
restricted to the bits `j ≤ i`. -/
theorem toNat_mod {m : ℕ} (s : Reg m) (j : ℕ) :
    s.toNat % 2 ^ (m - j) = ∑ i : Fin m, if j ≤ (i : ℕ) ∧ s i then 2 ^ (m - 1 - i) else 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  by_cases hj : j ≤ m
  · rw [toNat_mod_eq_sum_Ico s hj, ← Finset.sum_range_add_sum_Ico _ hj]
    have h0 : (∑ l ∈ Finset.range j, if h : l < m then
        (if j ≤ l ∧ s ⟨l, h⟩ then 2 ^ (m - 1 - l) else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [Finset.mem_range] at hl
      split_ifs <;> first | rfl | omega
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Ico] at hl
    simp [hl.1, hl.2, bit]
  · have hmj : m - j = 0 := by omega
    rw [hmj, pow_zero, Nat.mod_one]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    split_ifs <;> first | rfl | omega

end Reg

/-- PHASE2_SPEC.md §A.2 — the bit-reversal permutation of a register. -/
def bitRev {m : ℕ} (s : Reg m) : Reg m := fun j => s (Fin.rev j)

theorem bitRev_bitRev {m : ℕ} (s : Reg m) : bitRev (bitRev s) = s :=
  funext fun j => by simp [bitRev, Fin.rev_rev]

/-- PHASE2_SPEC.md §A.2 — reading the reversed register big-endian is reading the register
little-endian. -/
theorem Reg.toNat_bitRev {m : ℕ} (s : Reg m) : (bitRev s).toNat = s.toNatLE := by
  unfold toNat toNatLE bitRev
  rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin m => if s j then 2 ^ (j : ℕ) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have : m - 1 - (j : ℕ) = m - ((j : ℕ) + 1) := by omega
  rw [this]

end CQRV

end
