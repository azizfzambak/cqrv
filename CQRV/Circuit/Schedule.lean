module

public import CQRV.Circuit.IR
public import CQRV.Grades.Basic
public import CQRV.Grades.Ext

/-!
# CQRV.Circuit.Schedule

Report §3.1.1 (the grade components), §6.1.4 (Table 3, depth column) — the one fixed
scheduler that measures depth (DECISIONS.md 2026-10-23, Stage 5 decision 4):

* ASAP layering in program order: a gate is placed in the first layer after every earlier
  gate on any qubit it touches;
* a gate occupies every qubit it touches (an `ifBit` gate: the qubits of the controlled gate);
* a classically controlled gate is placed after the measurement that writes its bit
  (two `ifBit` gates on the same bit may share a layer);
* `alloc` and `free` take no layer.

It is not tuned to reproduce any number of the report.

Stage 17a (PHASE2_SPEC.md §A.1): `Circuit.gradeExt` reads the second record `GradeExt` off the
**same** schedule (no second scheduler); `SchedState.step`, `schedule`, `depth`, `tCount`,
`grade` are unchanged.

Stage 18a (docs/tasks/STAGE18_TASK.md A1; DECISIONS.md 2026-10-31): the scheduler state keeps the
placed gates as a **cons list, most recent first**, and `schedule` is `Array.mk` of its reverse.
The placement rule and the value of `schedule` are unchanged (`tests/CQRVTests/Schedule.lean`
checks `scheduleOld c == schedule c` against a verbatim copy of the Stage 17b definitions). Why:
the former `Array.push` per gate nests one `List.concat` per gate inside the kernel's term, and
the first traversal of a 1953-gate schedule hit the kernel's recursion guard
(`bench/scaling/out/rand_a64_r1_h/lean.log`, `grade_eq`, Stage 14b); a cons list and one
tail-recursive `List.reverse` do not.
-/

@[expose] public section

namespace CQRV

/-- Scheduler state: the last occupied layer of each qubit and the layer of each measured bit
(association lists; absent = 0). -/
structure SchedState where
  qReady : List (Qubit × Nat) := []
  cReady : List (Nat × Nat) := []
  /-- `(gate, layer)`, **most recent first** (a cons list, Stage 18a); `alloc`/`free` have
  layer 0. -/
  placed : List (Gate × Nat) := []

/-- Report §6.1.4, decision 4 — place one gate ASAP. -/
def SchedState.step (st : SchedState) (g : Gate) : SchedState :=
  match g with
  | .alloc _ | .free _ => { st with placed := (g, 0) :: st.placed }
  | _ =>
    let qs := g.qubits
    let ready := qs.foldl (fun m q => Nat.max m ((st.qReady.lookup q).getD 0)) 0
    let ready := match g with
      | .ifBit c _ => Nat.max ready ((st.cReady.lookup c).getD 0)
      | _ => ready
    let layer := ready + 1
    let qReady := qs.foldl (fun r q => (q, layer) :: r.filter (·.1 != q)) st.qReady
    let cReady := match g with
      | .measure _ c => (c, layer) :: st.cReady.filter (·.1 != c)
      | _ => st.cReady
    { qReady, cReady, placed := (g, layer) :: st.placed }

/-- Report §6.1.4, decision 4 — every gate with its ASAP layer (1-based; `alloc`/`free`: 0), in
program order: the structure constructor `Array.mk` on the reversed cons list (Stage 18a; not
`List.toArray`, which pushes element by element and would nest again). -/
def schedule (c : Circuit) : Array (Gate × Nat) :=
  ⟨(c.gates.foldl SchedState.step {}).placed.reverse⟩

namespace Circuit

/-- Report §3.1.1 — depth `d`: the number of layers of the decision-4 schedule. -/
def depth (c : Circuit) : Nat := (schedule c).foldl (fun m p => Nat.max m p.2) 0

/-- Report §3.1.1, §6.1.2 — executed T-count `t` (T and T†). -/
def tCount (c : Circuit) : Nat := c.gates.foldl (fun n g => n + g.tCount) 0

/-- Report §3.1.1 — `a`: peak number of ancillae allocated at the same time (program order). -/
def peakAncilla (c : Circuit) : Nat :=
  (c.gates.foldl (fun (live, peak) g =>
    match g with
    | .alloc _ => (live + 1, Nat.max peak (live + 1))
    | .free _ => (live - 1, peak)
    | _ => (live, peak)) (0, 0)).2

/-- Report §3.1.1 — width `w`: the data register plus the peak number of live ancillae. -/
def width (c : Circuit) : Nat := c.nData + c.peakAncilla

/-- Report §3.1.1, Eq. (5) — the grade `(w, d, t, a)` of a circuit, measured. -/
def grade (c : Circuit) : Grade := ⟨c.width, c.depth, c.tCount, c.peakAncilla⟩

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — the second record, from the same decision-4 schedule as
`grade`: `twoQ`, `rot`, `meas`, `ff` count gates (through `ifBit`); `tDepth` is the number of
layers `k ≥ 1` in which some placed gate is a T-power (`Gate.isTPower`). Measured, not composed
(no ⊕ / ⊗ for `GradeExt` in this stage). -/
def gradeExt (c : Circuit) : GradeExt :=
  let s := (schedule c).toList
  { twoQ := c.gates.countP Gate.isTwoQubit
    tDepth := (List.range c.depth).countP fun k => s.any fun gl => gl.2 == k + 1 && gl.1.isTPower
    rot := c.gates.countP Gate.isRotation
    meas := c.gates.countP Gate.isMeasure
    ff := c.gates.countP Gate.isIfBit }

/-! ### Sanity theorems on `gradeExt` (PHASE2_SPEC.md §A.1, Stage 17a) -/

/-- `tDepth` counts layers of the schedule, so it is at most the depth. -/
theorem gradeExt_tDepth_le_depth (c : Circuit) : c.gradeExt.tDepth ≤ c.depth := by
  simp only [gradeExt]
  exact Nat.le_trans List.countP_le_length (Nat.le_of_eq List.length_range)

theorem length_written_eq_countP (gs : List Gate) :
    (gs.flatMap Gate.writes).length = gs.countP Gate.isMeasure := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.countP_cons]
    cases g <;> simp [Gate.writes, Gate.isMeasure, Nat.add_comm]

/-- `meas` is the number of classical bits: one per `measure`. -/
theorem gradeExt_meas_eq_nBits (c : Circuit) : c.gradeExt.meas = c.nBits := by
  simp only [gradeExt, nBits, written]
  exact (length_written_eq_countP c.gates).symm

/-- One scheduler step conses the gate onto `placed` (in some layer; Stage 18a form). -/
theorem _root_.CQRV.SchedState.step_placed (st : SchedState) (g : Gate) :
    ∃ l, (st.step g).placed = (g, l) :: st.placed := by
  cases g <;> exact ⟨_, rfl⟩

/-- The gates of the fold are the gates of the list, most recent first (Stage 18a form). -/
theorem foldl_step_placed (gs : List Gate) (st : SchedState) :
    (gs.foldl SchedState.step st).placed.map Prod.fst = gs.reverse ++ st.placed.map Prod.fst := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨l, hl⟩ := SchedState.step_placed st g
    rw [hl, List.map_cons]
    simp

/-- The gates of the schedule are the gates of the circuit, in program order. -/
theorem schedule_gates (c : Circuit) : (schedule c).toList.map Prod.fst = c.gates := by
  simp [schedule, List.map_reverse, foldl_step_placed]

theorem countP_or_le {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons]
    cases p x <;> cases q x <;> simp <;> omega

/-- At most one `k < d` has `k + 1 = m`. -/
theorem countP_succ_eq_range_le_one (m d : Nat) :
    (List.range d).countP (fun k => m == k + 1) ≤ 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.countP_append]
    have h1 : [d].countP (fun k => m == k + 1) ≤ 1 := by
      simpa using (List.countP_le_length (p := fun k => m == k + 1) (l := [d]))
    by_cases h : m = d + 1
    · have h0 : (List.range d).countP (fun k => m == k + 1) = 0 := by
        rw [List.countP_eq_zero]
        intro k hk
        rw [List.mem_range] at hk
        simp only [beq_iff_eq]
        omega
      omega
    · have h0 : [d].countP (fun k => m == k + 1) = 0 := by
        rw [List.countP_eq_zero]
        intro k hk
        simp only [List.mem_singleton] at hk
        subst hk
        simp only [beq_iff_eq]
        exact h
      omega

/-- The layers holding a T-power gate are at most the T-power gates. -/
theorem countP_tLayers_le (d : Nat) (L : List (Gate × Nat)) :
    (List.range d).countP (fun k => L.any fun gl => gl.2 == k + 1 && gl.1.isTPower) ≤
      L.countP (fun gl => gl.1.isTPower) := by
  induction L with
  | nil => simp
  | cons gl L ih =>
    simp only [List.any_cons, List.countP_cons]
    refine Nat.le_trans (countP_or_le _ _ _) ?_
    cases hg : gl.1.isTPower
    · simpa using ih
    · have h1 := countP_succ_eq_range_le_one gl.2 d
      simp only [Bool.and_true, ite_true]
      omega

/-- `Circuit.tCount` is the number of T-power gates (`Gate.tCount_eq_isTPower`). -/
theorem tCount_eq_countP (c : Circuit) : c.tCount = c.gates.countP Gate.isTPower := by
  have key : ∀ (gs : List Gate) (n : Nat),
      gs.foldl (fun n g => n + g.tCount) n = n + gs.countP Gate.isTPower := by
    intro gs
    induction gs with
    | nil => intro n; simp
    | cons g gs ih =>
      intro n
      rw [List.foldl_cons, ih, List.countP_cons, Gate.tCount_eq_isTPower]
      split <;> omega
  simpa [tCount] using key c.gates 0

/-- `tDepth` is at most the T-count: every T-layer holds a T-power gate. -/
theorem gradeExt_tDepth_le_tCount (c : Circuit) : c.gradeExt.tDepth ≤ c.tCount := by
  rw [tCount_eq_countP, ← schedule_gates c, List.countP_map]
  simp only [gradeExt]
  exact countP_tLayers_le c.depth (schedule c).toList

/-- The layers of the schedule: `layers[k]` holds the gates of layer `k + 1` in program order. -/
def layers (c : Circuit) : Array (List Gate) :=
  let s := schedule c
  (Array.range c.depth).map fun k => (s.filter (·.2 == k + 1)).toList.map (·.1)

/-- Layer dump for debugging (`cqr synthesize --layers`): one line per layer. -/
def layerDump (c : Circuit) : String :=
  String.intercalate "\n" <| (c.layers.toList.zipIdx).map fun (gs, k) =>
    s!"L{k + 1}: " ++ String.intercalate "; " (gs.map (·.render))

end Circuit

end CQRV

end
