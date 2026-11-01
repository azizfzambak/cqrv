module

public import CQRV.Circuit.Schedule
public import CQRV.Grades.Order
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# CQRV.Circuit.GradeCompose

Report §3.1.1, Table 3.1 (⊕); PHASE2_SPEC.md §A.3 item 2 and amendment (6) (Stage 19a,
docs/tasks/STAGE19_TASK.md A1–A4) — the measured grade of a sequential composition
`C₁.append C₂` against ⊕ of the measured grades:

* `liveEnd` (A1): the live-ancilla count at the end of a gate list, the first component of the
  fold whose second component is `peakAncilla` (copied, `peakAncilla` untouched). `Circuit.WF`
  does not check the `alloc` / `free` discipline, so `C₁.liveEnd = 0` is a hypothesis of its own.
* The components (A2): `tCount` adds; with `C₁.liveEnd = 0`, `peakAncilla` and `width` (same
  data register) are maxima; `depth (C₁.append C₂) ≤ depth C₁ + depth C₂` with **no**
  hypothesis — the decision-4 scheduler places every gate of the `C₂` part at most `depth C₁`
  layers later than in `C₂` alone (`SchedState.Dom`, the invariant along `SchedState.step`).
* The grade theorems (A3): `grade_append_le`, the list form `grade_foldl_append_le` and the
  n-fold form `grade_replicate_le` (`n • g` of the `AddCommMonoid Grade`).
* The `GradeExt` analogue (A4): `twoQ`, `rot`, `meas`, `ff` add (equalities); `tDepth (C₁.append
  C₂) ≤ tDepth C₁ + tCount C₂` — the sum of the two T-depths is **not** a bound (the
  counterexample is in `tests/CQRVTests/GradeCompose.lean`).

Nothing the certificates evaluate is edited: the scheduler, `peakAncilla`, `tCount`, `gradeExt`
are read, not changed. Physlib-free (PHASE2_SPEC §A.8 item 6).
-/

@[expose] public section

namespace CQRV

/-- The scheduler writes `Nat.max`; `omega` reads `max` (the same function). -/
theorem natMax_eq_max (a b : Nat) : Nat.max a b = max a b := rfl

/-! ## Gate facts: `shiftBits` and the classifiers -/

namespace Gate

/-- A gate the decision-4 scheduler places in a layer: everything but `alloc` / `free`. -/
def isSched : Gate → Bool
  | .alloc _ | .free _ => false
  | _ => true

theorem qubits_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).qubits = g.qubits := by
  cases g <;> rfl

theorem isSched_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isSched = g.isSched := by
  cases g <;> rfl

theorem isTPower_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isTPower = g.isTPower := by
  cases g <;> rfl

theorem isTwoQubit_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isTwoQubit = g.isTwoQubit := by
  cases g <;> rfl

theorem isRotation_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isRotation = g.isRotation := by
  cases g <;> rfl

theorem isMeasure_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isMeasure = g.isMeasure := by
  cases g <;> rfl

theorem isIfBit_shiftBits (k : Nat) (g : Gate) : (g.shiftBits k).isIfBit = g.isIfBit := by
  cases g <;> rfl

end Gate

namespace Circuit

theorem gates_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).gates = C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits) := rfl

theorem nData_append (C₁ C₂ : Circuit) : (C₁.append C₂).nData = C₁.nData := rfl

/-- `countP` of a classifier that `shiftBits` preserves, over the appended gate list. -/
theorem countP_gates_append (C₁ C₂ : Circuit) (p : Gate → Bool)
    (hp : ∀ k g, p (Gate.shiftBits k g) = p g) :
    (C₁.append C₂).gates.countP p = C₁.gates.countP p + C₂.gates.countP p := by
  rw [gates_append, List.countP_append, List.countP_map]
  have : (p ∘ Gate.shiftBits C₁.nBits) = p := funext (hp C₁.nBits)
  rw [this]

/-! ## A1. `liveEnd` -/

/-- Report §3.1.1; PHASE2_SPEC §A.3 (Stage 19a) — the number of live ancillae at the end of the
gate list: the first component of **the same fold** as `peakAncilla` (`alloc` +1, `free` −1,
truncated). `WF` does not check `alloc` / `free`, so `liveEnd C = 0` is stated as a hypothesis
where it is needed. -/
def liveEnd (c : Circuit) : Nat :=
  (c.gates.foldl (fun (live, peak) g =>
    match g with
    | .alloc _ => (live + 1, Nat.max peak (live + 1))
    | .free _ => (live - 1, peak)
    | _ => (live, peak)) (0, 0)).1

/-- The step of the `peakAncilla` / `liveEnd` fold, named (the same lambda). -/
def ancStep : Nat × Nat → Gate → Nat × Nat := fun (live, peak) g =>
  match g with
  | .alloc _ => (live + 1, Nat.max peak (live + 1))
  | .free _ => (live - 1, peak)
  | _ => (live, peak)

theorem liveEnd_eq (c : Circuit) : c.liveEnd = (c.gates.foldl ancStep (0, 0)).1 := rfl

theorem peakAncilla_eq (c : Circuit) : c.peakAncilla = (c.gates.foldl ancStep (0, 0)).2 := rfl

/-- The fold pair: from `(a, p)` the fold ends at the live count of the fold from `(a, 0)` and
at `max p` of its peak. -/
theorem foldl_ancStep (l : List Gate) (a p : Nat) :
    l.foldl ancStep (a, p) =
      ((l.foldl ancStep (a, 0)).1, Nat.max p (l.foldl ancStep (a, 0)).2) := by
  induction l generalizing a p with
  | nil => simp
  | cons g l ih =>
    cases g <;> simp only [List.foldl_cons, ancStep]
    case alloc q =>
      rw [ih (a + 1) (Nat.max p (a + 1)), ih (a + 1) (Nat.max 0 (a + 1))]
      refine Prod.ext rfl ?_
      simp only [natMax_eq_max]
      omega
    case free q => exact ih (a - 1) p
    all_goals exact ih a p

theorem ancStep_shiftBits (s : Nat × Nat) (k : Nat) (g : Gate) :
    ancStep s (g.shiftBits k) = ancStep s g := by
  obtain ⟨a, p⟩ := s
  cases g <;> rfl

theorem foldl_ancStep_map_shiftBits (l : List Gate) (k : Nat) (s : Nat × Nat) :
    (l.map (Gate.shiftBits k)).foldl ancStep s = l.foldl ancStep s := by
  rw [List.foldl_map]
  simp only [ancStep_shiftBits]

/-- The fold over the appended gate list, when `C₁` ends with no live ancilla. -/
theorem foldl_ancStep_append {C₁ C₂ : Circuit} (h : C₁.liveEnd = 0) :
    (C₁.append C₂).gates.foldl ancStep (0, 0) =
      ((C₂.gates.foldl ancStep (0, 0)).1,
        Nat.max C₁.peakAncilla (C₂.gates.foldl ancStep (0, 0)).2) := by
  rw [gates_append, List.foldl_append, foldl_ancStep_map_shiftBits]
  have h1 : C₁.gates.foldl ancStep (0, 0) = (0, C₁.peakAncilla) := by
    rw [peakAncilla_eq]
    exact Prod.ext h rfl
  rw [h1, foldl_ancStep]

/-! ## A2. The components: `tCount`, `liveEnd`, `peakAncilla`, `width` -/

/-- Report §3.1.1, Table 3.1 — the T-count adds. -/
theorem tCount_append (C₁ C₂ : Circuit) : (C₁.append C₂).tCount = C₁.tCount + C₂.tCount := by
  rw [tCount_eq_countP, tCount_eq_countP, tCount_eq_countP]
  exact countP_gates_append C₁ C₂ Gate.isTPower Gate.isTPower_shiftBits

theorem liveEnd_append {C₁ C₂ : Circuit} (h : C₁.liveEnd = 0) :
    (C₁.append C₂).liveEnd = C₂.liveEnd := by
  rw [liveEnd_eq, foldl_ancStep_append h]
  rfl

/-- Report §3.1.1, Table 3.1 — ancillae are a maximum when `C₁` ends with none live. -/
theorem peakAncilla_append {C₁ C₂ : Circuit} (h : C₁.liveEnd = 0) :
    (C₁.append C₂).peakAncilla = max C₁.peakAncilla C₂.peakAncilla := by
  rw [peakAncilla_eq, foldl_ancStep_append h]
  rfl

/-- Report §3.1.1, Table 3.1 — the width is a maximum (same data register, no live ancilla). -/
theorem width_append {C₁ C₂ : Circuit} (hn : C₁.nData = C₂.nData) (h : C₁.liveEnd = 0) :
    (C₁.append C₂).width = max C₁.width C₂.width := by
  simp only [width, nData_append, peakAncilla_append h]
  rw [← hn]
  omega

end Circuit

/-! ## A2. The depth: the scheduler invariant -/

namespace SchedState

/-- The last occupied layer of a qubit (absent = 0), as `step` reads it. -/
def qr (st : SchedState) (q : Qubit) : Nat := (st.qReady.lookup q).getD 0

/-- The layer of a measured bit (absent = 0), as `step` reads it. -/
def cr (st : SchedState) (c : Nat) : Nat := (st.cReady.lookup c).getD 0

/-- The largest placed layer. -/
def maxLayer (st : SchedState) : Nat := st.placed.foldl (fun m p => Nat.max m p.2) 0

/-- The qubit part of the ASAP readiness of a gate. -/
def readyQ (st : SchedState) (g : Gate) : Nat :=
  g.qubits.foldl (fun m q => Nat.max m ((st.qReady.lookup q).getD 0)) 0

/-- The ASAP readiness of a gate (`ifBit` also waits for its bit). -/
def readyOf (st : SchedState) (g : Gate) : Nat :=
  match g with
  | .ifBit c _ => Nat.max (st.readyQ g) ((st.cReady.lookup c).getD 0)
  | _ => st.readyQ g

/-- The layer `step` gives a scheduled gate. -/
def layerOf (st : SchedState) (g : Gate) : Nat := st.readyOf g + 1

/-- `step` on a scheduled gate, unfolded. -/
theorem step_sched (st : SchedState) {g : Gate} (h : g.isSched = true) :
    st.step g =
      { qReady := g.qubits.foldl (fun r q => (q, st.layerOf g) :: r.filter (·.1 != q)) st.qReady
        cReady := match g with
          | .measure _ c => (c, st.layerOf g) :: st.cReady.filter (·.1 != c)
          | _ => st.cReady
        placed := (g, st.layerOf g) :: st.placed } := by
  cases g <;> first | rfl | simp [Gate.isSched] at h

/-- `step` on `alloc` / `free`: layer 0, the ready lists untouched. -/
theorem step_unsched (st : SchedState) {g : Gate} (h : g.isSched = false) :
    st.step g = { st with placed := (g, 0) :: st.placed } := by
  cases g <;> first | rfl | simp [Gate.isSched] at h

/-! ### `lookup` after the ready-list updates -/

theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] {k k' : α} (h : k' ≠ k) (v : β)
    (r : List (α × β)) : ((k, v) :: r).lookup k' = r.lookup k' := by
  rw [List.lookup_cons]
  have : (k' == k) = false := beq_eq_false_iff_ne.mpr h
  simp [this]

theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α] {k k' : α} (h : k' ≠ k)
    (r : List (α × β)) : (r.filter (·.1 != k)).lookup k' = r.lookup k' := by
  induction r with
  | nil => rfl
  | cons kv r ih =>
    obtain ⟨a, v⟩ := kv
    by_cases ha : a = k
    · subst ha
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih, lookup_cons_ne h]
    · have hne : (a != k) = true := bne_iff_ne.mpr ha
      simp only [List.filter_cons, hne, ↓reduceIte]
      by_cases hk : k' = a
      · subst hk; simp
      · rw [lookup_cons_ne hk, lookup_cons_ne hk, ih]

theorem lookup_foldl_insert {α : Type} [BEq α] [LawfulBEq α] (qs : List α) (r : List (α × Nat))
    (L : Nat) (q' : α) :
    (qs.foldl (fun r q => (q, L) :: r.filter (·.1 != q)) r).lookup q' =
      if q' ∈ qs then some L else r.lookup q' := by
  induction qs generalizing r with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih]
    by_cases hq : q' ∈ qs
    · simp [hq]
    · by_cases he : q' = q
      · subst he; simp
      · have hm : q' ∉ q :: qs := by simp [he, hq]
        simp only [hq, hm, ↓reduceIte]
        rw [lookup_cons_ne he, lookup_filter_ne he]

/-- The qubit readiness after a scheduled gate. -/
theorem qr_step_sched (st : SchedState) {g : Gate} (h : g.isSched = true) (q' : Qubit) :
    (st.step g).qr q' = if q' ∈ g.qubits then st.layerOf g else st.qr q' := by
  rw [step_sched st h]
  simp only [qr, lookup_foldl_insert]
  split <;> rfl

/-- The bit readiness after a measurement. -/
theorem cr_step_measure (st : SchedState) (q : Qubit) (c c' : Nat) :
    (st.step (.measure q c)).cr c' = if c' = c then st.layerOf (.measure q c) else st.cr c' := by
  rw [step_sched st rfl]
  simp only [cr]
  by_cases hc : c' = c
  · subst hc; simp
  · simp only [hc, ↓reduceIte]
    rw [lookup_cons_ne hc, lookup_filter_ne hc]

/-- The bit readiness after a scheduled gate that is not a measurement. -/
theorem cr_step_sched_of_not_measure (st : SchedState) {g : Gate} (h : g.isSched = true)
    (hm : g.isMeasure = false) (c' : Nat) : (st.step g).cr c' = st.cr c' := by
  rw [step_sched st h]
  cases g <;> first | rfl | simp [Gate.isMeasure] at hm

theorem qr_step_unsched (st : SchedState) {g : Gate} (h : g.isSched = false) (q' : Qubit) :
    (st.step g).qr q' = st.qr q' := by
  rw [step_unsched st h]
  rfl

theorem cr_step_unsched (st : SchedState) {g : Gate} (h : g.isSched = false) (c' : Nat) :
    (st.step g).cr c' = st.cr c' := by
  rw [step_unsched st h]
  rfl

/-! ### `maxLayer` -/

theorem foldl_max_le_iff (l : List (Gate × Nat)) (a B : Nat) :
    l.foldl (fun m p => Nat.max m p.2) a ≤ B ↔ a ≤ B ∧ ∀ p ∈ l, p.2 ≤ B := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons, forall_eq_or_imp, natMax_eq_max]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega, h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h3⟩

theorem le_foldl_max (l : List (Gate × Nat)) (a : Nat) :
    a ≤ l.foldl (fun m p => Nat.max m p.2) a ∧
      ∀ p ∈ l, p.2 ≤ l.foldl (fun m p => Nat.max m p.2) a :=
  (foldl_max_le_iff l a _).mp (Nat.le_refl _)

theorem foldl_max_reverse (l : List (Gate × Nat)) :
    l.reverse.foldl (fun m p => Nat.max m p.2) 0 = l.foldl (fun m p => Nat.max m p.2) 0 := by
  apply Nat.le_antisymm
  · rw [foldl_max_le_iff]
    exact ⟨Nat.zero_le _, fun p hp => (le_foldl_max l 0).2 p (List.mem_reverse.mp hp)⟩
  · rw [foldl_max_le_iff]
    exact ⟨Nat.zero_le _, fun p hp => (le_foldl_max l.reverse 0).2 p (List.mem_reverse.mpr hp)⟩

theorem le_maxLayer_of_mem {st : SchedState} {p : Gate × Nat} (hp : p ∈ st.placed) :
    p.2 ≤ st.maxLayer :=
  (le_foldl_max st.placed 0).2 p hp

theorem maxLayer_le {st : SchedState} {B : Nat} (h : ∀ p ∈ st.placed, p.2 ≤ B) :
    st.maxLayer ≤ B :=
  (foldl_max_le_iff st.placed 0 B).mpr ⟨Nat.zero_le _, h⟩

theorem maxLayer_le_step (st : SchedState) (g : Gate) : st.maxLayer ≤ (st.step g).maxLayer := by
  obtain ⟨l, hl⟩ := SchedState.step_placed st g
  apply maxLayer_le
  intro p hp
  apply le_maxLayer_of_mem
  rw [hl]
  exact List.mem_cons_of_mem _ hp

theorem layerOf_le_maxLayer_step (st : SchedState) {g : Gate} (h : g.isSched = true) :
    st.layerOf g ≤ (st.step g).maxLayer := by
  have hm : (g, st.layerOf g) ∈ (st.step g).placed := by
    rw [step_sched st h]
    exact List.mem_cons_self
  exact le_maxLayer_of_mem hm

theorem maxLayer_le_foldl (gs : List Gate) (st : SchedState) :
    st.maxLayer ≤ (gs.foldl SchedState.step st).maxLayer := by
  induction gs generalizing st with
  | nil => exact Nat.le_refl _
  | cons g gs ih => exact Nat.le_trans (maxLayer_le_step st g) (ih (st.step g))

/-- The placed list of a fold is the new entries in front of the old ones, the new gates being
the folded gates most recent first. -/
theorem placed_foldl (gs : List Gate) (st : SchedState) :
    ∃ new : List (Gate × Nat), (gs.foldl SchedState.step st).placed = new ++ st.placed ∧
      new.map Prod.fst = gs.reverse := by
  induction gs generalizing st with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨new, h1, h2⟩ := ih (st.step g)
    obtain ⟨l, hl⟩ := SchedState.step_placed st g
    refine ⟨new ++ [(g, l)], ?_, ?_⟩
    · rw [List.foldl_cons, h1, hl, List.append_assoc, List.singleton_append]
    · rw [List.map_append, h2, List.reverse_cons]
      rfl

/-! ### Every ready entry is a placed layer -/

/-- The ready lists of a state reached from `{}` hold placed layers. -/
def Reached (st : SchedState) : Prop :=
  (∀ q, st.qr q ≤ st.maxLayer) ∧ (∀ c, st.cr c ≤ st.maxLayer)

theorem reached_empty : Reached {} := ⟨fun _ => Nat.le_refl 0, fun _ => Nat.le_refl 0⟩

theorem reached_step {st : SchedState} (hst : Reached st) (g : Gate) : Reached (st.step g) := by
  have hmono := maxLayer_le_step st g
  by_cases hs : g.isSched = true
  · have hL := layerOf_le_maxLayer_step st hs
    refine ⟨fun q => ?_, fun c => ?_⟩
    · rw [qr_step_sched st hs]
      split
      · exact hL
      · exact Nat.le_trans (hst.1 q) hmono
    · cases hm : g.isMeasure
      · rw [cr_step_sched_of_not_measure st hs hm]
        exact Nat.le_trans (hst.2 c) hmono
      · cases g <;> simp [Gate.isMeasure] at hm
        rename_i q' c'
        rw [cr_step_measure]
        split
        · exact hL
        · exact Nat.le_trans (hst.2 c) hmono
  · have hs' : g.isSched = false := by simpa using hs
    refine ⟨fun q => ?_, fun c => ?_⟩
    · rw [qr_step_unsched st hs']
      exact Nat.le_trans (hst.1 q) hmono
    · rw [cr_step_unsched st hs']
      exact Nat.le_trans (hst.2 c) hmono

theorem reached_foldl (gs : List Gate) : Reached (gs.foldl SchedState.step {}) := by
  have key : ∀ (gs : List Gate) (st : SchedState), Reached st →
      Reached (gs.foldl SchedState.step st) := by
    intro gs
    induction gs with
    | nil => intro st h; exact h
    | cons g gs ih => intro st h; exact ih _ (reached_step h g)
  exact key gs {} reached_empty

/-! ### The invariant between the appended run and the run of `C₂` alone -/

/-- PHASE2_SPEC §A.3 amendment (6), the depth route (STAGE18/19 task text): the state `st` of the
appended run dominates the state `st₂` of `C₂` alone by at most `D` layers, the bits of the
appended run being shifted by `k`. -/
def Dom (D k : Nat) (st st₂ : SchedState) : Prop :=
  (∀ q, st.qr q ≤ D + st₂.qr q) ∧ (∀ c, st.cr (c + k) ≤ D + st₂.cr c)

theorem foldl_max_le_of_le (qs : List Qubit) (f f₂ : Qubit → Nat) (D : Nat)
    (hf : ∀ q, f q ≤ D + f₂ q) (a b : Nat) (hab : a ≤ D + b) :
    qs.foldl (fun m q => Nat.max m (f q)) a ≤ D + qs.foldl (fun m q => Nat.max m (f₂ q)) b := by
  induction qs generalizing a b with
  | nil => exact hab
  | cons q qs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    have := hf q
    simp only [natMax_eq_max]
    omega

theorem readyQ_le_of_Dom {D k : Nat} {st st₂ : SchedState} (hD : Dom D k st st₂) (g : Gate) :
    st.readyQ (g.shiftBits k) ≤ D + st₂.readyQ g := by
  simp only [readyQ, Gate.qubits_shiftBits]
  exact foldl_max_le_of_le g.qubits (fun q => st.qr q) (fun q => st₂.qr q) D hD.1 0 0
    (Nat.zero_le _)

theorem layerOf_le_of_Dom {D k : Nat} {st st₂ : SchedState} (hD : Dom D k st st₂) (g : Gate) :
    st.layerOf (g.shiftBits k) ≤ D + st₂.layerOf g := by
  have hq := readyQ_le_of_Dom hD g
  cases g with
  | ifBit c g' =>
    have hc := hD.2 c
    simp only [layerOf, readyOf, Gate.shiftBits, natMax_eq_max] at hq hc ⊢
    simp only [cr] at hc
    omega
  | _ => simp only [layerOf, readyOf, Gate.shiftBits] at hq ⊢; omega

theorem Dom_step {D k : Nat} {st st₂ : SchedState} (hD : Dom D k st st₂) (g : Gate) :
    Dom D k (st.step (g.shiftBits k)) (st₂.step g) := by
  by_cases hs : g.isSched = true
  · have hs' : (g.shiftBits k).isSched = true := by rw [Gate.isSched_shiftBits]; exact hs
    have hL := layerOf_le_of_Dom hD g
    refine ⟨fun q => ?_, fun c => ?_⟩
    · rw [qr_step_sched st hs', qr_step_sched st₂ hs, Gate.qubits_shiftBits]
      split
      · exact hL
      · exact hD.1 q
    · cases hm : g.isMeasure
      · have hm' : (g.shiftBits k).isMeasure = false := by rw [Gate.isMeasure_shiftBits]; exact hm
        rw [cr_step_sched_of_not_measure st hs' hm', cr_step_sched_of_not_measure st₂ hs hm]
        exact hD.2 c
      · cases g <;> simp [Gate.isMeasure] at hm
        rename_i q' c'
        simp only [Gate.shiftBits] at hL ⊢
        rw [cr_step_measure, cr_step_measure]
        by_cases hc : c = c'
        · subst hc
          simp only [ite_true]
          exact hL
        · have hc' : ¬ (c + k = c' + k) := fun h => hc (Nat.add_right_cancel h)
          simp only [hc, hc', ↓reduceIte]
          exact hD.2 c
  · have hs' : g.isSched = false := by simpa using hs
    have hs'' : (g.shiftBits k).isSched = false := by rw [Gate.isSched_shiftBits]; exact hs'
    refine ⟨fun q => ?_, fun c => ?_⟩
    · rw [qr_step_unsched st hs'', qr_step_unsched st₂ hs']
      exact hD.1 q
    · rw [cr_step_unsched st hs'', cr_step_unsched st₂ hs']
      exact hD.2 c

/-- Every layer placed by the appended run is at most `D` plus the final maximum of the run of
`C₂` alone. -/
theorem placed_le_of_Dom (D k : Nat) (gs : List Gate) :
    ∀ (st st₂ : SchedState) (M : Nat), Dom D k st st₂ →
      (gs.foldl SchedState.step st₂).maxLayer ≤ M → (∀ p ∈ st.placed, p.2 ≤ D + M) →
      ∀ p ∈ ((gs.map (Gate.shiftBits k)).foldl SchedState.step st).placed, p.2 ≤ D + M := by
  induction gs with
  | nil => intro st st₂ M _ _ hp; simpa using hp
  | cons g gs ih =>
    intro st st₂ M hD hM hp
    rw [List.map_cons, List.foldl_cons]
    rw [List.foldl_cons] at hM
    refine ih (st.step (g.shiftBits k)) (st₂.step g) M (Dom_step hD g) hM ?_
    intro p hpm
    by_cases hs : g.isSched = true
    · have hs' : (g.shiftBits k).isSched = true := by rw [Gate.isSched_shiftBits]; exact hs
      rw [step_sched st hs'] at hpm
      simp only [List.mem_cons] at hpm
      rcases hpm with rfl | hpm
      · have h1 := layerOf_le_of_Dom hD g
        have h2 := layerOf_le_maxLayer_step st₂ hs
        have h3 := maxLayer_le_foldl gs (st₂.step g)
        simp only
        omega
      · exact hp p hpm
    · have hs' : (g.shiftBits k).isSched = false := by
        rw [Gate.isSched_shiftBits]; simpa using hs
      rw [step_unsched st hs'] at hpm
      simp only [List.mem_cons] at hpm
      rcases hpm with rfl | hpm
      · exact Nat.zero_le _
      · exact hp p hpm

end SchedState

namespace Circuit

/-- The depth is the largest placed layer of the final scheduler state. -/
theorem depth_eq_maxLayer (c : Circuit) :
    c.depth = (c.gates.foldl SchedState.step {}).maxLayer := by
  simp only [depth, schedule, SchedState.maxLayer]
  rw [← Array.foldl_toList]
  exact SchedState.foldl_max_reverse _

/-- Report §3.1.1, Table 3.1; PHASE2_SPEC §A.3 amendment (6) — the depth of a sequential
composition is at most the sum, with no hypothesis: the ASAP scheduler places every gate of the
`C₂` part at most `depth C₁` layers later than in `C₂` alone. -/
theorem depth_append_le (C₁ C₂ : Circuit) : (C₁.append C₂).depth ≤ C₁.depth + C₂.depth := by
  rw [depth_eq_maxLayer, depth_eq_maxLayer, depth_eq_maxLayer, gates_append, List.foldl_append]
  set S₁ := C₁.gates.foldl SchedState.step {} with hS₁
  have hR : SchedState.Reached S₁ := SchedState.reached_foldl C₁.gates
  have hD : SchedState.Dom S₁.maxLayer C₁.nBits S₁ {} :=
    ⟨fun q => Nat.le_trans (hR.1 q) (Nat.le_add_right _ _),
     fun c => Nat.le_trans (hR.2 (c + C₁.nBits)) (Nat.le_add_right _ _)⟩
  apply SchedState.maxLayer_le
  refine SchedState.placed_le_of_Dom S₁.maxLayer C₁.nBits C₂.gates S₁ {} _ hD (Nat.le_refl _) ?_
  intro p hp
  exact Nat.le_trans (SchedState.le_maxLayer_of_mem hp) (Nat.le_add_right _ _)

/-! ## A3. The grade theorems -/

/-- Report §3.1.1, Table 3.1 (⊕); PHASE2_SPEC §A.3 item 2 — the measured grade of `C₁.append
C₂` is at most ⊕ of the measured grades: width, T-count and ancillae exactly, depth as a bound. -/
theorem grade_append_le {C₁ C₂ : Circuit} (hn : C₁.nData = C₂.nData) (h : C₁.liveEnd = 0) :
    (C₁.append C₂).grade ≤ C₁.grade + C₂.grade := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (C₁.append C₂).width ≤ max C₁.width C₂.width
    exact Nat.le_of_eq (width_append hn h)
  · show (C₁.append C₂).depth ≤ C₁.depth + C₂.depth
    exact depth_append_le C₁ C₂
  · show (C₁.append C₂).tCount ≤ C₁.tCount + C₂.tCount
    exact Nat.le_of_eq (tCount_append C₁ C₂)
  · show (C₁.append C₂).peakAncilla ≤ max C₁.peakAncilla C₂.peakAncilla
    exact Nat.le_of_eq (peakAncilla_append h)

/-- The list form: a fold of appends, each block on the same data register and ending with no
live ancilla. -/
theorem grade_foldl_append_le (init : Circuit) (bs : List Circuit)
    (hn : ∀ b ∈ bs, b.nData = init.nData) (hi : init.liveEnd = 0) (hb : ∀ b ∈ bs, b.liveEnd = 0) :
    (bs.foldl Circuit.append init).grade ≤ init.grade + (bs.map Circuit.grade).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    have hb0 : b ∈ b :: bs := List.mem_cons_self
    have h1 := ih (init.append b)
      (fun b' hb' => by rw [nData_append]; exact hn b' (List.mem_cons_of_mem _ hb'))
      (by rw [liveEnd_append hi]; exact hb b hb0)
      (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
    refine le_trans h1 (Grade.seqComp_mono ?_ (le_refl _))
    exact grade_append_le (hn b hb0).symm hi

/-- Report §3.1.4 — the n-fold form: `r` copies of one block (`groverCircuit`'s shape). -/
theorem grade_replicate_le (init it : Circuit) (r : ℕ) (hn : it.nData = init.nData)
    (hi : init.liveEnd = 0) (ht : it.liveEnd = 0) :
    ((List.replicate r it).foldl Circuit.append init).grade ≤ init.grade + r • it.grade := by
  have h := grade_foldl_append_le init (List.replicate r it)
    (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact hn) hi
    (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact ht)
  rwa [List.map_replicate, List.sum_replicate] at h

/-! ## A4. The `GradeExt` analogue -/

theorem gradeExt_twoQ_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.twoQ = C₁.gradeExt.twoQ + C₂.gradeExt.twoQ :=
  countP_gates_append C₁ C₂ Gate.isTwoQubit Gate.isTwoQubit_shiftBits

theorem gradeExt_rot_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.rot = C₁.gradeExt.rot + C₂.gradeExt.rot :=
  countP_gates_append C₁ C₂ Gate.isRotation Gate.isRotation_shiftBits

theorem gradeExt_meas_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.meas = C₁.gradeExt.meas + C₂.gradeExt.meas :=
  countP_gates_append C₁ C₂ Gate.isMeasure Gate.isMeasure_shiftBits

theorem gradeExt_ff_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.ff = C₁.gradeExt.ff + C₂.gradeExt.ff :=
  countP_gates_append C₁ C₂ Gate.isIfBit Gate.isIfBit_shiftBits

/-- `tDepth` read off the final scheduler state. -/
theorem gradeExt_tDepth_eq (c : Circuit) :
    c.gradeExt.tDepth = (List.range c.depth).countP fun k =>
      (c.gates.foldl SchedState.step {}).placed.reverse.any fun gl =>
        gl.2 == k + 1 && gl.1.isTPower := rfl

/-- A predicate false from `D` on counts no more over `range N` than over `range D`. -/
theorem countP_range_le_of_false (P : Nat → Bool) (D N : Nat) (h : ∀ k, D ≤ k → P k = false) :
    (List.range N).countP P ≤ (List.range D).countP P := by
  rcases Nat.lt_or_ge N D with hlt | hge
  · exact List.Sublist.countP_le (List.range_sublist.mpr (Nat.le_of_lt hlt))
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    induction j with
    | zero => exact Nat.le_refl _
    | succ j ih =>
      rw [Nat.add_succ, List.range_succ, List.countP_append]
      have h0 : [D + j].countP P = 0 := by
        rw [List.countP_eq_zero]
        intro a ha
        rw [List.mem_singleton] at ha
        subst ha
        simp [h (D + j) (Nat.le_add_right D j)]
      rw [h0, Nat.add_zero]
      exact ih (Nat.le_add_right D j)

/-- PHASE2_SPEC §A.3 amendment (6) — the T-depth of a composition is at most the T-depth of
`C₁` plus the T-count of `C₂`: the T-layers of the `C₁` part are those of `C₁`, and each T-power
gate of the `C₂` part adds at most one layer. The sum of the two T-depths is not a bound. -/
theorem tDepth_append_le (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.tDepth ≤ C₁.gradeExt.tDepth + C₂.tCount := by
  rw [gradeExt_tDepth_eq, gradeExt_tDepth_eq, gates_append, List.foldl_append]
  set S₁ := C₁.gates.foldl SchedState.step {} with hS₁
  obtain ⟨new, hnew, hmap⟩ := SchedState.placed_foldl (C₂.gates.map (Gate.shiftBits C₁.nBits)) S₁
  rw [hnew, List.reverse_append]
  simp only [List.any_append]
  refine Nat.le_trans (countP_or_le _ _ _) (Nat.add_le_add ?_ ?_)
  · -- the `C₁` part: its layers are at most `depth C₁`
    apply countP_range_le_of_false
    intro k hk
    rw [depth_eq_maxLayer, ← hS₁] at hk
    simp only [Bool.eq_false_iff, ne_eq, List.any_eq_true, not_exists, not_and]
    intro gl hgl
    have h1 := SchedState.le_maxLayer_of_mem (List.mem_reverse.mp hgl)
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro h2
    omega
  · -- the `C₂` part: at most one layer per T-power gate
    refine Nat.le_trans (countP_tLayers_le _ _) ?_
    rw [List.countP_reverse, tCount_eq_countP]
    have : (fun gl : Gate × Nat => gl.1.isTPower) = (Gate.isTPower ∘ Prod.fst) := rfl
    rw [this, ← List.countP_map, hmap, List.countP_reverse, List.countP_map]
    have h2 : (Gate.isTPower ∘ Gate.shiftBits C₁.nBits) = Gate.isTPower :=
      funext (Gate.isTPower_shiftBits C₁.nBits)
    rw [h2]
    exact Nat.le_refl _

/-! ### List forms -/

theorem tCount_foldl_append (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).tCount = init.tCount + (bs.map Circuit.tCount).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, tCount_append]
    omega

theorem gradeExt_tDepth_foldl_append_le (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).gradeExt.tDepth ≤
      init.gradeExt.tDepth + (bs.map Circuit.tCount).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := ih (init.append b)
    have h2 := tDepth_append_le init b
    omega

theorem gradeExt_tDepth_replicate_le (init it : Circuit) (r : ℕ) :
    ((List.replicate r it).foldl Circuit.append init).gradeExt.tDepth ≤
      init.gradeExt.tDepth + r * it.tCount := by
  have h := gradeExt_tDepth_foldl_append_le init (List.replicate r it)
  rw [List.map_replicate, List.sum_replicate] at h
  exact h

theorem gradeExt_twoQ_foldl_append (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).gradeExt.twoQ =
      init.gradeExt.twoQ + (bs.map fun b => b.gradeExt.twoQ).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, gradeExt_twoQ_append]
    omega

theorem gradeExt_rot_foldl_append (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).gradeExt.rot =
      init.gradeExt.rot + (bs.map fun b => b.gradeExt.rot).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, gradeExt_rot_append]
    omega

theorem gradeExt_meas_foldl_append (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).gradeExt.meas =
      init.gradeExt.meas + (bs.map fun b => b.gradeExt.meas).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, gradeExt_meas_append]
    omega

theorem gradeExt_ff_foldl_append (init : Circuit) (bs : List Circuit) :
    (bs.foldl Circuit.append init).gradeExt.ff =
      init.gradeExt.ff + (bs.map fun b => b.gradeExt.ff).sum := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, gradeExt_ff_append]
    omega

end Circuit

end CQRV

end
