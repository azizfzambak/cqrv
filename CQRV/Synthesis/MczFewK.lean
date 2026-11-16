module

public import CQRV.Synthesis.MczFew
public import Mathlib.Data.List.Sort

/-!
# CQRV.Synthesis.MczFewK

Report §6.1.4 (Stage 12b/12c), PHASE2_SPEC §B.3 (2) (Stage 30a, A1) — **the kernel-evaluable form of
the few-ancilla MCZ schedule**, once. `MczFew.substeps` sorts with `List.mergeSort`, which the kernel
does not evaluate; `substepsK` sorts by insertion (`sortNat`), `doublingK` and `planK` replace the
sort, and `plan_eq_planK` proves the schedule unchanged. Stage 12c had this Physlib-side in
`CQRV.Grover.FewSchedule`; Stage 23c repeated it Physlib-free in `CQRV.Synthesis.Problem1`. Both now
alias this module (their declaration names are unchanged), which is Physlib-free and sits in
`Synthesis`, so that `Circuit` and `Synthesis` never import `Grover`.
-/

@[expose] public section

namespace CQRV.Synthesis.FewScheduleK

open CQRV.Synthesis.MczFew

/-- Insert into a sorted list of naturals (exposed, kernel-evaluable). -/
def insNat (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insNat a l

/-- Insertion sort on naturals (exposed, kernel-evaluable). -/
def sortNat : List ℕ → List ℕ
  | [] => []
  | a :: l => insNat a (sortNat l)

theorem insNat_eq (a : ℕ) (l : List ℕ) : insNat a l = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => simp [insNat]
  | cons b l ih => simp [insNat, List.orderedInsert_cons, ih]

/-- `sortNat` is `List.mergeSort` on `ℕ` with `≤`. -/
theorem sortNat_eq (l : List ℕ) : l.mergeSort (fun a b => decide (a ≤ b)) = sortNat l := by
  rw [List.mergeSort_eq_insertionSort (· ≤ ·)]
  induction l with
  | nil => simp [sortNat]
  | cons a l ih => simp [sortNat, List.insertionSort_cons, ih, insNat_eq]

/-- `MczFew.substeps` with `sortNat` for `mergeSort`. -/
def substepsK : Nat → List Nat → List Nat → List Op
  | 0, P, Q =>
    match P, Q with
    | p₀ :: _, q₀ :: q₁ :: _ => [(p₀, q₀, q₁)]
    | _, _ => []
  | f + 1, P, Q =>
    let m := P.length / 2
    let ops := (List.range m).map fun k =>
      (P.getD (P.length - 1 - k) 0, Q.getD (2 * k + 1) 0, Q.getD (2 * k + 2) 0)
    let used := ops.flatMap fun o => [o.2.1, o.2.2]
    let Q' := sortNat (Q.filter (!used.contains ·) ++ ops.map (·.1))
    ops ++ substepsK f (P.take (P.length - m)) Q'

theorem substeps_eq : ∀ f P Q, substeps f P Q = substepsK f P Q
  | 0, P, Q => by
    rcases P with _ | ⟨p, P⟩ <;> rcases Q with _ | ⟨q₀, _ | ⟨q₁, Q⟩⟩ <;> rfl
  | f + 1, P, Q => by simp only [substeps, substepsK, sortNat_eq, substeps_eq f]

/-- `MczFew.doubling` with `substepsK` (kernel-evaluable; equal by `doubling_eq`). -/
def doublingK (n : ℕ) : List Op :=
  ((List.range n).filter fun i => i + 2 ^ (i + 1) ≤ n).flatMap fun i =>
    substepsK i ((List.range (2 ^ i)).map (i + ·)) ((List.range (2 ^ i + 1)).map (i + 2 ^ i + ·))

theorem doubling_eq (n : ℕ) : doubling n = doublingK n := by
  unfold doubling doublingK
  congr 1
  funext i
  simp only [timestep, substeps_eq]

/-- `MczFew.plan` with `doublingK` for `doubling`: the same schedule, evaluable by the kernel
(`plan_eq_planK`). -/
def planK (n : ℕ) : MczVariant → List Step × List Qubit
  | .ladder => plan n .ladder
  | .logDepth =>
    let data := (List.range n).map Qubit.data
    if n ≤ 2 then ([], data) else
    let qs := Qubit.anc 0 :: data
    let d := doublingK n
    let A₁ := d.foldl applyOp (true :: List.replicate n false)
    let (g, A₂) := greedy qs.length A₁
    let (s₂, us) := accumulate (.anc 1) (unmarkedQubits qs A₂)
    (stepsOf qs (d ++ g) ++ s₂, us)

theorem plan_eq_planK (n : ℕ) (v : MczVariant) : plan n v = planK n v := by
  cases v
  · rfl
  · simp only [plan, planK, doubling_eq, doublingK]

end CQRV.Synthesis.FewScheduleK
