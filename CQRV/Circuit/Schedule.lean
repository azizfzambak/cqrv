module

public import CQRV.Circuit.IR
public import CQRV.Grades.Basic

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
-/

@[expose] public section

namespace CQRV

/-- Scheduler state: the last occupied layer of each qubit and the layer of each measured bit
(association lists; absent = 0). -/
structure SchedState where
  qReady : List (Qubit × Nat) := []
  cReady : List (Nat × Nat) := []
  /-- `(gate, layer)` in program order; `alloc`/`free` have layer 0. -/
  placed : Array (Gate × Nat) := #[]

/-- Report §6.1.4, decision 4 — place one gate ASAP. -/
def SchedState.step (st : SchedState) (g : Gate) : SchedState :=
  match g with
  | .alloc _ | .free _ => { st with placed := st.placed.push (g, 0) }
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
    { qReady, cReady, placed := st.placed.push (g, layer) }

/-- Report §6.1.4, decision 4 — every gate with its ASAP layer (1-based; `alloc`/`free`: 0). -/
def schedule (c : Circuit) : Array (Gate × Nat) :=
  (c.gates.foldl SchedState.step {}).placed

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
