module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
import CQRV.Emit.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic
meta import CQRV.Emit.Basic

/-!
# The scheduler state as a cons list (Stage 18a, docs/tasks/STAGE18_TASK.md A1)

`SchedStateOld` / `scheduleOld` are the Stage 17b definitions **verbatim** (`placed : Array`,
built by `Array.push`); `schedule` keeps the placed gates as a cons list and returns
`Array.mk` of its reverse. The acceptance is `#guard scheduleOld c == schedule c` on every corpus
oracle (both uncomputation modes), the diffusion circuits for n = 1..10 (both modes), the
few-ancilla MCZ for n = 3..10, the Grover circuits of the running example (r = 2, both modes) and
of `simple_alu_x0_1` (r = 1), and the emitter sample circuit; `schedule_eq_old` is the general
statement (a simulation of the two folds). The placement rule and every measured value are
unchanged (report §3.1.1, §6.1.4; DECISIONS.md 2026-10-23 decision 4; 2026-10-31, Stage 18a).
-/

namespace CQRV.Tests.Schedule

open CQRV CQRV.DSL CQRV.Synthesis

/-! ## The Stage 17b scheduler, verbatim -/

/-- Stage 17b `SchedState`: the placed gates in an `Array`, built by `push`. -/
structure SchedStateOld where
  qReady : List (Qubit × Nat) := []
  cReady : List (Nat × Nat) := []
  placed : Array (Gate × Nat) := #[]

/-- Stage 17b `SchedState.step`, verbatim. -/
def SchedStateOld.step (st : SchedStateOld) (g : Gate) : SchedStateOld :=
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

/-- Stage 17b `schedule`, verbatim. -/
def scheduleOld (c : Circuit) : Array (Gate × Nat) :=
  (c.gates.foldl SchedStateOld.step {}).placed

/-! ## The simulation theorem -/

/-- One step of each fold from related states: equal `qReady` / `cReady`, `placed` reversed. -/
theorem step_sim (so : SchedStateOld) (s : SchedState) (h1 : so.qReady = s.qReady)
    (h2 : so.cReady = s.cReady) (h3 : so.placed.toList = s.placed.reverse) (g : Gate) :
    (so.step g).qReady = (s.step g).qReady ∧ (so.step g).cReady = (s.step g).cReady ∧
      (so.step g).placed.toList = (s.step g).placed.reverse := by
  obtain ⟨q1, c1, p1⟩ := so
  obtain ⟨q2, c2, p2⟩ := s
  simp only at h1 h2 h3
  subst h1 h2
  cases g <;> simp [SchedStateOld.step, SchedState.step, Array.toList_push, h3]

theorem foldl_sim (gs : List Gate) : ∀ (so : SchedStateOld) (s : SchedState),
    so.qReady = s.qReady → so.cReady = s.cReady → so.placed.toList = s.placed.reverse →
      (gs.foldl SchedStateOld.step so).placed.toList =
        (gs.foldl SchedState.step s).placed.reverse := by
  induction gs with
  | nil => intro so s _ _ h3; simpa using h3
  | cons g gs ih =>
    intro so s h1 h2 h3
    obtain ⟨e1, e2, e3⟩ := step_sim so s h1 h2 h3 g
    exact ih _ _ e1 e2 e3

/-- The two schedulers agree on every circuit. -/
theorem schedule_eq_old (c : Circuit) : scheduleOld c = schedule c := by
  unfold scheduleOld schedule
  rw [← foldl_sim c.gates {} {} rfl rfl rfl]

/-! ## The `#guard`s (the acceptance of A1) -/

def agree (c : Circuit) : Bool := scheduleOld c == schedule c
def agreeE (c : Except Diagnostic Circuit) : Bool :=
  match c with | .ok c => agree c | .error _ => false

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
def orSrc : String := include_str "../../examples/search_or.cqr"
def chainSrc : String := include_str "../../examples/and_chain_8.cqr"
def aluSrc : String := include_str "../../examples/simple_alu_x0_1.cqr"
def forSrc : String :=
  "fn f(x: Vec Bool 4) -> Bool { for i in [0 ..< 4] with acc = false do acc or idx(x, i) }"
def ifSrc : String :=
  "fn f(x: Vec Bool 3) -> Bool { if idx(x, 0) then idx(x, 1) else idx(x, 2) }"
def callSrc : String :=
  "fn g(a: Bool, b: Bool) -> Bool { a and b }\n\
   fn f(x: Vec Bool 4) -> Bool { g(idx(x, 0), idx(x, 1)) xor g(idx(x, 2), not idx(x, 3)) }"
def letSrc : String :=
  "fn f(x: Vec Bool 3) -> Bool { let u = idx(x, 0) and idx(x, 1) in u or (u and idx(x, 2)) }"

def typed (src : String) : Except Diagnostic TypedProgram := parse src >>= check
def oracle (src : String) : Except Diagnostic Circuit := typed src >>= toNetwork >>= synthesizeOracle
def oracleC (src : String) : Except Diagnostic Circuit :=
  typed src >>= toNetwork >>= (synthesizeOracle · .coherent)

-- the seven corpus oracles, both modes
#guard [groverSrc, orSrc, chainSrc, ifSrc, callSrc, letSrc, forSrc].all fun s =>
  agreeE (oracle s) && agreeE (oracleC s)
-- the diffusion for n = 1..10, both modes
#guard (List.range 10).all fun i =>
  agreeE (diffusion (i + 1) none) && agreeE (diffusion (i + 1) none .tree .coherent)
-- the few-ancilla MCZ for n = 3..10
#guard (List.range 8).all fun i => agreeE (mczFew (i + 3) .logDepth)
-- the Grover circuits of the running example (r = 2, both modes) and of simple_alu_x0_1 (r = 1)
#guard agreeE (typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2))
#guard agreeE (typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2 none .tree .coherent))
#guard agreeE (typed aluSrc >>= toNetwork >>= (groverCircuit · 6 1))
-- the emitter sample circuit (every gate constructor)
#guard agree Emit.sampleCircuit
-- a hand-written circuit with every scheduler case: alloc / free in layer 0, a classically
-- controlled gate waiting for its measurement, two `ifBit` on one bit sharing a layer
#guard agree ⟨2, [.alloc (.anc 0), .h (.data 0), .cnot (.data 0) (.anc 0), .measure (.anc 0) 0,
  .ifBit 0 (.x (.data 0)), .ifBit 0 (.z (.data 1)), .free (.anc 0), .alloc (.anc 0),
  .free (.anc 0)]⟩
-- the measured values are unchanged (the running example and the sample)
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2)).map fun c =>
  (c.grade, c.gradeExt)).toOption == some (⟨15, 134, 72, 7⟩, ⟨126, 39, 0, 18, 36⟩)
#guard ((typed groverSrc >>= toNetwork >>= (groverCircuit · 8 2 none .tree .coherent)).map fun c =>
  (c.grade, c.gradeExt)).toOption == some (⟨15, 200, 144, 7⟩, ⟨216, 74, 0, 0, 0⟩)
#guard (schedule Emit.sampleCircuit).toList.map Prod.fst == Emit.sampleCircuit.gates
#guard (schedule Emit.sampleCircuit).size == Emit.sampleCircuit.gates.length

end CQRV.Tests.Schedule
