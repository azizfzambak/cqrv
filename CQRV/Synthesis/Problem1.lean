module

public import CQRV.Synthesis.MczFew
public import CQRV.Synthesis.MczFewK
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# CQRV.Synthesis.Problem1

Stage 23c (PHASE2_SPEC §B.2; report §6.1.4, §6.2.3; `docs/MCZ_NOTES.md`) — **the 8n − 24 theorem**
on Khattar–Gidney Problem 1 schedules, under a stated cost model, and candidate B attaining it.

* **Q1. The schedule model.** `P1State L`: an array `avail : Fin L → Bool` (`true` = available as a
  target, `false` = holds a live value) and `fresh : Fin L → Bool` (the clean indices not yet
  targeted). `P1Op L = (t, x, y)`: valid when `t` is available, `x` and `y` hold live values and
  the three are distinct; the step makes `t` live, `x` and `y` available, and removes `t` from
  `fresh`. **The cost model** (the KG family's): 4 for a step whose target is fresh (Gidney's AND,
  uncomputed by MBU at 0 T), 8 otherwise (a relative-phase Toffoli pair, Maslov's 4 T each — the
  stated assumption of the model, not a proved lower bound on circuits). `valid`, `run`, `cost`,
  `nFresh`, `live` (the number of live values), `freshCard`.
* **Q2. The bound.** `live_step` (a valid step lowers `live` by exactly one), `freshCard_step`
  (`fresh` only shrinks), `nFresh_le` (at most `|fresh₀|` steps cost 4), `cost_add`
  (`cost + 4 · nFresh = 8 · length`), `live_run`, the general form `cost_lower_bound`
  (`8 (n − k) − 4 min(|fresh₀|, n − k) ≤ cost`, `k` the final number of live values) and
  **`problem1_T_lower_bound`**: from `n ≥ 4` live values with two clean indices down to at most two
  live values (the final phase is a `CZ`, 0 T, or a `Z`), every valid schedule costs at least
  `8n − 24`. It is a theorem about the KG Problem 1 family under this model, not a lower bound on
  the T-count of every MCZ circuit.
* **Q3. Candidate B attains it.** `planB n` translates `plan n .logDepth` of `CQRV.Synthesis.MczFew`
  (the doubling, the §5.2 greedy, the accumulation over `anc 1`) into the model on `Fin (n + 2)`
  (`anc 0 ↦ 0`, `data i ↦ i + 1`, `anc 1 ↦ n + 1`; `initB n` has the data live and the two
  ancillae fresh). `planB_valid` (n = 4 … 12), `planB_cost` (`8n − 24` for **n = 6 … 12**),
  `planB_cost_small` (`8n − 20` at n = 4, 5: the second clean ancilla is not used — the task text's
  range n = 4 … 12 was wrong at its two first values), `planB_tCount` (the T-count of the emitted
  `mczFew n .logDepth` equals the plan's cost, n = 4 … 12), `planB_bound` (the theorem applied to
  the plan). All by `decide +kernel` after rewriting `plan` into its kernel-evaluable form `planK`
  (`plan_eq`): `MczFew.substeps` sorts with `List.mergeSort`, which the kernel does not evaluate, so
  the Stage 12c idiom (`CQRV.Grover.FewSchedule`, Physlib-side) is repeated here Physlib-free
  (`insNat`, `sortNat`, `sortNat_eq`, `substepsK`, `substeps_eq`, `doublingK`, `doubling_eq`).
  The all-n forms are not reached (see DECISIONS.md).

Not imported by `Apps/cqr/Main.lean`: the cqr closure is unchanged.
-/

@[expose] public section

namespace CQRV.Synthesis.Problem1

open CQRV.Synthesis.MczFew

/-! ## Q1 — the schedule model -/

/-- KG Problem 1 (§5.1), PHASE2_SPEC §B.2 (23c) — the state of an array of `L` indices: `avail i`
(`true`: available as a target, `false`: holds a live value) and `fresh i` (a clean index not yet
targeted). -/
structure P1State (L : ℕ) where
  avail : Fin L → Bool
  fresh : Fin L → Bool

/-- An operation `(t, x, y)`: store `x ∧ y` on `t`. -/
abbrev P1Op (L : ℕ) := Fin L × Fin L × Fin L

variable {L : ℕ}

/-- Valid: `t` available, `x` and `y` live, the three distinct. -/
def P1Op.validB (s : P1State L) (o : P1Op L) : Bool :=
  s.avail o.1 && !s.avail o.2.1 && !s.avail o.2.2 && o.1 != o.2.1 && o.1 != o.2.2 && o.2.1 != o.2.2

theorem P1Op.validB_iff (s : P1State L) (o : P1Op L) :
    o.validB s = true ↔ s.avail o.1 = true ∧ s.avail o.2.1 = false ∧ s.avail o.2.2 = false ∧
      o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2 := by
  simp [P1Op.validB, and_assoc]

/-- The step: `t` becomes live, `x` and `y` available, `t` is no longer fresh. -/
def P1State.step (s : P1State L) (o : P1Op L) : P1State L :=
  ⟨Function.update (Function.update (Function.update s.avail o.1 false) o.2.1 true) o.2.2 true,
    Function.update s.fresh o.1 false⟩

/-- The cost model: 4 T on a fresh clean target (AND, MBU uncompute), 8 T otherwise (a
relative-phase Toffoli pair). -/
def stepCost (s : P1State L) (o : P1Op L) : ℕ := if s.fresh o.1 then 4 else 8

/-- A schedule is valid step by step. -/
def valid : P1State L → List (P1Op L) → Bool
  | _, [] => true
  | s, o :: os => o.validB s && valid (s.step o) os

/-- The state after a schedule. -/
def run : P1State L → List (P1Op L) → P1State L
  | s, [] => s
  | s, o :: os => run (s.step o) os

/-- The cost of a schedule: the sum of its step costs. -/
def cost : P1State L → List (P1Op L) → ℕ
  | _, [] => 0
  | s, o :: os => stepCost s o + cost (s.step o) os

/-- The number of steps that target a fresh clean index (the steps that cost 4). -/
def nFresh : P1State L → List (P1Op L) → ℕ
  | _, [] => 0
  | s, o :: os => (if s.fresh o.1 then 1 else 0) + nFresh (s.step o) os

/-- The number of indices at which `f` reads `b`. -/
def cnt (f : Fin L → Bool) (b : Bool) : ℕ := ∑ i, if f i = b then 1 else 0

/-- The number of live values. -/
def P1State.live (s : P1State L) : ℕ := cnt s.avail false

/-- The number of fresh clean indices. -/
def P1State.freshCard (s : P1State L) : ℕ := cnt s.fresh true

/-! ## Q2 — the bound -/

/-- Updating one entry changes the count by the entry's contribution. -/
theorem cnt_update (f : Fin L → Bool) (a : Fin L) (v b : Bool) :
    cnt (Function.update f a v) b + (if f a = b then 1 else 0) =
      cnt f b + (if v = b then 1 else 0) := by
  unfold cnt
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase Finset.univ (fun i => if f i = b then 1 else 0) (Finset.mem_univ a),
    Function.update_self]
  have : ∑ i ∈ Finset.univ.erase a, (if Function.update f a v i = b then 1 else 0) =
      ∑ i ∈ Finset.univ.erase a, (if f i = b then 1 else 0) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.mem_erase.1 hi).1]
  rw [this]
  omega

/-- PHASE2_SPEC §B.2 (23c) — **a valid step lowers the number of live values by exactly one**:
`t` becomes live, `x` and `y` stop being live. -/
theorem live_step {s : P1State L} {o : P1Op L} (h : o.validB s = true) :
    (s.step o).live + 1 = s.live := by
  obtain ⟨ht, hx, hy, htx, hty, hxy⟩ := (P1Op.validB_iff s o).1 h
  unfold P1State.live P1State.step
  dsimp only
  have h1 := cnt_update s.avail o.1 false false
  have h2 := cnt_update (Function.update s.avail o.1 false) o.2.1 true false
  have h3 := cnt_update (Function.update (Function.update s.avail o.1 false) o.2.1 true) o.2.2
    true false
  rw [ht] at h1
  rw [Function.update_of_ne (Ne.symm htx), hx] at h2
  rw [Function.update_of_ne (Ne.symm hxy), Function.update_of_ne (Ne.symm hty), hy] at h3
  simp only [Bool.true_eq_false, ↓reduceIte, add_zero] at h1 h2 h3
  omega

/-- **`fresh` only shrinks**: a step removes its target from the fresh indices. -/
theorem freshCard_step (s : P1State L) (o : P1Op L) :
    (s.step o).freshCard + (if s.fresh o.1 then 1 else 0) = s.freshCard := by
  have h := cnt_update s.fresh o.1 false true
  unfold P1State.freshCard P1State.step
  dsimp only
  simpa using h

/-- **At most `|fresh₀|` steps cost 4.** -/
theorem nFresh_le (s : P1State L) (os : List (P1Op L)) : nFresh s os ≤ s.freshCard := by
  induction os generalizing s with
  | nil => simp [nFresh]
  | cons o os ih =>
    have h := freshCard_step s o
    have h' := ih (s.step o)
    simp only [nFresh]
    split_ifs at h ⊢ <;> omega

theorem nFresh_le_length (s : P1State L) (os : List (P1Op L)) : nFresh s os ≤ os.length := by
  induction os generalizing s with
  | nil => simp [nFresh]
  | cons o os ih =>
    have h' := ih (s.step o)
    simp only [nFresh, List.length_cons]
    split_ifs <;> omega

/-- `cost + 4 · nFresh = 8 · length`: every step costs 8, less 4 on a fresh target. -/
theorem cost_add (s : P1State L) (os : List (P1Op L)) :
    cost s os + 4 * nFresh s os = 8 * os.length := by
  induction os generalizing s with
  | nil => simp [cost, nFresh]
  | cons o os ih =>
    have h' := ih (s.step o)
    simp only [cost, nFresh, stepCost, List.length_cons]
    split_ifs <;> omega

/-- A valid schedule of `m` steps lowers `live` by `m`. -/
theorem live_run {s : P1State L} {os : List (P1Op L)} (h : valid s os = true) :
    (run s os).live + os.length = s.live := by
  induction os generalizing s with
  | nil => simp [run]
  | cons o os ih =>
    simp only [valid, Bool.and_eq_true] at h
    have h1 := live_step h.1
    have h2 := ih h.2
    simp only [run, List.length_cons]
    omega

/-- PHASE2_SPEC §B.2 (23c) — **the general form**: a valid schedule from `n` live values down to `k`
costs at least `8 (n − k) − 4 min(|fresh₀|, n − k)`. -/
theorem cost_lower_bound {s : P1State L} {os : List (P1Op L)} (h : valid s os = true) :
    8 * (s.live - (run s os).live) - 4 * min s.freshCard (s.live - (run s os).live) ≤
      cost s os := by
  have h1 := live_run h
  have h2 := cost_add s os
  have h3 := nFresh_le s os
  have h4 := nFresh_le_length s os
  omega

/-- Report §6.1.4, `docs/MCZ_NOTES.md`, PHASE2_SPEC §B.2 (23c) — **the 8n − 24 theorem**: a valid
Problem 1 schedule from `n ≥ 4` live values with two clean indices, ending with at most two live
values (the final phase is a `CZ`, 0 T, or a `Z`), costs at least `8n − 24`.

The model's assumptions: 4 T per fresh-clean conjunction (Gidney's AND, MBU uncompute at 0 T);
8 T per other conjunction (a relative-phase Toffoli pair, Maslov's 4 T each — assumed, not
proved as a lower bound on circuits); the final phase on at most two live values. It is a theorem
about the KG Problem 1 family under this model, not a lower bound on the T-count of every MCZ
circuit. -/
theorem problem1_T_lower_bound {s : P1State L} {os : List (P1Op L)} {n : ℕ}
    (h : valid s os = true) (hn : s.live = n) (hf : s.freshCard = 2) (hk : (run s os).live ≤ 2)
    (h4 : 4 ≤ n) : 8 * n - 24 ≤ cost s os := by
  have h1 := live_run h
  have h2 := cost_add s os
  have h3 := nFresh_le s os
  have h4' := nFresh_le_length s os
  omega

/-! ## Q3 — candidate B attains it -/

/-! ### A kernel-evaluable form of `plan n .logDepth`

`MczFew.substeps` sorts with `List.mergeSort`, which the kernel does not evaluate. Stage 23c repeated
the Stage 12c idiom here; since Stage 30a (A1) the single definition is `CQRV.Synthesis.FewScheduleK`,
and the names below are its aliases (the `planB_*` theorems are unchanged). -/

abbrev insNat := FewScheduleK.insNat
abbrev sortNat := FewScheduleK.sortNat

theorem insNat_eq (a : ℕ) (l : List ℕ) : insNat a l = l.orderedInsert (· ≤ ·) a :=
  FewScheduleK.insNat_eq a l

theorem sortNat_eq (l : List ℕ) : l.mergeSort (fun a b => decide (a ≤ b)) = sortNat l :=
  FewScheduleK.sortNat_eq l

abbrev substepsK := FewScheduleK.substepsK

theorem substeps_eq : ∀ f P Q, substeps f P Q = substepsK f P Q := FewScheduleK.substeps_eq

abbrev doublingK := FewScheduleK.doublingK

theorem doubling_eq (n : ℕ) : doubling n = doublingK n := FewScheduleK.doubling_eq n

/-- `plan n .logDepth` with `doublingK`: `FewScheduleK.planK n .logDepth`. -/
def planK (n : ℕ) : List Step × List Qubit := FewScheduleK.planK n .logDepth

theorem plan_eq (n : ℕ) : plan n .logDepth = planK n := FewScheduleK.plan_eq_planK n .logDepth

/-! ### The translation -/

/-- The model index of a qubit of candidate B: `anc 0 ↦ 0`, `data i ↦ i + 1`, `anc 1 ↦ n + 1`
(the two arrays of the plan share the index set `Fin (n + 2)`; a qubit outside the register,
which the plan never produces, maps to `0`). -/
def qubitIdx (n : ℕ) : Qubit → Fin (n + 2)
  | .data i => if h : i < n then ⟨i + 1, by omega⟩ else ⟨0, by omega⟩
  | .anc i => if i = 0 then ⟨0, by omega⟩ else ⟨n + 1, by omega⟩

/-- A step `(x, y, t, clean)` of the plan as the operation `(t, x, y)` of the model. -/
def toP1Op (n : ℕ) : Step → P1Op (n + 2)
  | (x, y, t, _) => (qubitIdx n t, qubitIdx n x, qubitIdx n y)

/-- Candidate B's plan in the model. -/
def planB (n : ℕ) : List (P1Op (n + 2)) := (plan n .logDepth).1.map (toP1Op n)

/-- The initial state of candidate B: the `n` data indices live, the two ancillae available and
fresh. -/
def initB (n : ℕ) : P1State (n + 2) :=
  ⟨fun i => decide (i.val = 0 ∨ i.val = n + 1), fun i => decide (i.val = 0 ∨ i.val = n + 1)⟩

set_option maxRecDepth 8000 in
/-- **Candidate B's plan is valid in the model**, n = 4 … 12. -/
theorem planB_valid : ∀ n ∈ List.range' 4 9, valid (initB n) (planB n) = true := by
  simp only [planB, plan_eq]
  decide +kernel

set_option maxRecDepth 8000 in
/-- The initial state has `n` live values and two fresh indices, and the plan ends with at most
two live values (the two qubits of the final `CZ`), n = 4 … 12. -/
theorem planB_live : ∀ n ∈ List.range' 4 9,
    (initB n).live = n ∧ (initB n).freshCard = 2 ∧ (run (initB n) (planB n)).live ≤ 2 := by
  simp only [planB, plan_eq]
  decide +kernel

set_option maxRecDepth 8000 in
/-- **Candidate B attains the bound** for n = 6 … 12: its plan costs `8n − 24`. -/
theorem planB_cost : ∀ n ∈ List.range' 6 7, cost (initB n) (planB n) = 8 * n - 24 := by
  simp only [planB, plan_eq]
  decide +kernel

set_option maxRecDepth 8000 in
/-- At n = 4 and 5 candidate B costs `8n − 20`, one AND more than the bound: the second clean
ancilla is not used (the greedy leaves exactly two unmarked qubits after the first array, so
`accumulate` over `anc 1` does nothing). The bound `8n − 24` is attainable in the model at these
sizes (`tests/CQRVTests/Problem1.lean`), but not by this plan. -/
theorem planB_cost_small : ∀ n ∈ [4, 5], cost (initB n) (planB n) = 8 * n - 20 := by
  simp only [planB, plan_eq]
  decide +kernel

set_option maxRecDepth 8000 in
/-- **The emitted T-count equals the plan's cost**: `Circuit.tCount` of `mczFew n .logDepth` is
the cost of `planB n`, n = 4 … 12 (an AND compute is 4 T and its MBU uncompute 0 T; a
relative-phase Toffoli pair is 8 T; the phase is 0 T). -/
theorem planB_tCount : ∀ n ∈ List.range' 4 9,
    (mczFew n .logDepth).toOption.map Circuit.tCount = some (cost (initB n) (planB n)) := by
  simp only [planB, mczFew, plan_eq]
  decide +kernel

/-- The theorem applied to the plan: for n = 4 … 12, `8n − 24 ≤ cost (planB n)`. -/
theorem planB_bound (n : ℕ) (hn : n ∈ List.range' 4 9) : 8 * n - 24 ≤ cost (initB n) (planB n) :=
  problem1_T_lower_bound (planB_valid n hn) (planB_live n hn).1 (planB_live n hn).2.1
    (planB_live n hn).2.2 (by obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hn; omega)

end CQRV.Synthesis.Problem1

end
