module

public import CQRV.Certify.FrontEnd
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# CQRV.Certify.Count

Report §8.2 (M as a parameter of the search problem), §5.1.3, §8.4.1, §8.4.4 — the solution
count decided by the kernel (Stage 14a; DECISIONS.md 2026-10-29).

Until Stage 13 every certificate took the solution count as the hypothesis `hM_card :
(Finset.univ.filter fun x => Network.pred net n x = true).card = M` (§5.2.4, "supplied, never
decided"). For small `n` the count is a finite computation, and the kernel can do it:

* `Network.countSat N n` counts the inputs `k < 2ⁿ` whose bit vector (`inputBits n k`: bit `i`
  of `k` at index `i`) satisfies `Network.pred N n`. It is written for kernel evaluation
  (`List.range`, `List.countP`, `Nat.shiftRight`): no `Finset`, no `native_decide`.
* `Network.countSat_eq_card` identifies it with the `Finset` cardinality of the certificate
  statement, through the bit-vector bijection `bitsEquiv n : Fin (2 ^ n) ≃ (Fin n → Bool)`
  (Mathlib's `finFunctionFinEquiv` composed with `finTwoEquiv`; `finFunctionFinEquiv.symm k i =
  k / 2ⁱ % 2` is the bit `i` of `k`).

A generated certificate (`CQRV.Certify.Generate`) then proves `hM_count : (Finset.univ.filter
…).card = M` by `rw [← Network.countSat_eq_card]; decide +kernel` and `cert` takes no
hypothesis; `cqr certify --count-limit k` (default 10 since Stage 14c; 12 in Stage 14a) decides which
certificates do so.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.Certify

/-- Report §8.2 — the number of inputs `k < 2ⁿ` on which the one-output network `N` is `true`
(bit `i` of `k` = input bit `i`, as `inputBits`). Kernel-evaluable: `List.range`, `List.countP`,
`Nat.shiftRight`. -/
def Network.countSat (N : Network) (n : Nat) : Nat :=
  (List.range (2 ^ n)).countP fun k => N.pred n (inputBits n k)

/-- Report §8.2 — the bit-vector bijection `Fin (2 ^ n) ≃ (Fin n → Bool)`: `k ↦ inputBits n k`
(`bitsEquiv_apply`), from Mathlib's `finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2 ^ n)` and
`finTwoEquiv : Fin 2 ≃ Bool`. -/
def bitsEquiv (n : Nat) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  (finFunctionFinEquiv (m := 2) (n := n)).symm.trans (Equiv.piCongrRight fun _ => finTwoEquiv)

/-- `bitsEquiv n k` is the bit vector of `k`. -/
theorem bitsEquiv_apply (n : Nat) (k : Fin (2 ^ n)) : bitsEquiv n k = inputBits n k.val := by
  funext i
  have h : (finFunctionFinEquiv (m := 2) (n := n)).symm k i = ⟨k.val / 2 ^ i.val % 2,
      Nat.mod_lt _ (by decide)⟩ := rfl
  simp only [bitsEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, h,
    inputBits, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (k.val / 2 ^ i.val) with h2 | h2 <;>
    simp [finTwoEquiv, h2]

/-- Report §8.2, §8.4.1 (Stage 14a) — **the count is the cardinality**: `Network.countSat N n`
equals the `Finset` cardinality that the certificate statement (`hM_card`) is about. -/
theorem Network.countSat_eq_card (N : Network) (n : Nat) :
    N.countSat n = (Finset.univ.filter fun x => Network.pred N n x = true).card := by
  have hA : (Finset.univ.filter fun x => Network.pred N n x = true).card =
      (Finset.univ.filter fun k : Fin (2 ^ n) =>
        Network.pred N n (inputBits n k.val) = true).card := by
    symm
    apply Finset.card_equiv (bitsEquiv n)
    intro k
    simp [bitsEquiv_apply]
  rw [hA, Network.countSat, Finset.card_def, Finset.filter_val, Fin.univ_def,
    Multiset.filter_coe, Multiset.coe_card, ← List.countP_eq_length_filter,
    ← List.map_coe_finRange_eq_range, List.countP_map]
  congr 1

end CQRV.Synthesis

end
