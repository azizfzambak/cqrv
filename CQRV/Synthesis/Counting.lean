module

public import CQRV.Synthesis.Diffusion
public import CQRV.Synthesis.QFT
public import CQRV.Synthesis.NetworkCorrect
public import CQRV.Circuit.GradeCompose

/-!
# CQRV.Synthesis.Counting

PHASE2_SPEC.md §A.3 as amended before Stage 19 (amendments (1)–(4)); report §8.2, §6.1.4;
docs/tasks/STAGE19_TASK.md B1, B3 (Stage 19b) — the counting circuit of certified amplitude
estimation, built from the existing synthesizer and the existing builders, **Physlib-free** (the
`cqr` closure stays Lean core + Mathlib, §A.8 item 6; the semantic theorems are
`CQRV.Circuit.CountingCorrect`).

* Layout (amendment (1)): search register `data 0..n−1` (as every Grover builder), phase register
  `data n..n+m−1`, phase qubit `j` = `data (n+j)`; the data register has `n + m` qubits.
* `Network.withControl N m j` (B1): the network on `N.nInputs + m` inputs whose output is
  `and (input (N.nInputs + j)) (out N)`; `N`'s nodes and input numbering are unchanged, two nodes
  are appended. Its phase oracle is exactly controlled-`O_P` (`withControl_pred`), so Lemma 6.3.2
  applies unchanged; the final conjunction is the AND node of `withControl` (amendment (3)).
* `controlledDiffusion n m j` (B3): `H^{⊗n} X^{⊗n}` on the search register, the phase oracle of
  `(diffusionNet shape n).withControl m j` (an MCZ on `n + 1` qubits), `X^{⊗n} H^{⊗n}`; the data
  layers are uncontrolled because they cancel when the control is 0.
* `controlledGrover N n m j` (B3): the controlled oracle, the controlled diffusion and the phase
  fix `z (data (n+j))` (amendment (2)): the circuit's diffusion is `−U_s`, so the controlled
  block would apply `ctrl_j(−G)`; the `Z` on the control turns it into exactly `ctrl_j(G)`.
* `countingCircuit N n m kmax` (B3, amendment (4)): `H` on all `n + m` data qubits, then for
  `j = 0..m−1` the `2^j` copies of `controlledGrover N n m j`, then the inverse (A)QFT on the
  phase register, `(adjointGates (qftGates m)).map (Gate.shiftData n)` (or `aqftGates m kmax`).
  The iterates are joined by `Circuit.append` (bits shifted), through `countingPowers`, a
  recursion on `j` whose step is `(List.replicate (2^j) b_j).foldl Circuit.append acc`, so that
  the restoration proof (`countingCircuit_ancRestore_raw`) is one `ancRestore_foldl` per `j`.
* Diagnostics (existing codes only): `unsupported_network` for a predicate on the wrong number
  of inputs, a network with several outputs, `n = 0` and `m = 0` (as `diffusion` refuses `n = 0`);
  `unsupported_combination` for a phase-qubit index `j ≥ m`. No few-ancilla or Bennett variant.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL

/-! ## B1 — `Network.withControl` -/

/-- PHASE2_SPEC.md §A.3 amendment (1), (3) (Stage 19b) — the network of `c ∧ P` on
`N.nInputs + m` inputs, control input `N.nInputs + j`: `N`'s nodes unchanged, then the input node
of the control and the AND of `N`'s (single) output with it; the new AND is the output. -/
def Network.withControl (N : Network) (m j : Nat) : Network :=
  let o := N.outputs.headD 0
  let s := N.nodes.size
  { nInputs := N.nInputs + m,
    nodes := N.nodes ++ #[.input (N.nInputs + j), .and o s],
    outputs := [s + 1] }

theorem Network.withControl_nInputs (N : Network) (m j : Nat) :
    (N.withControl m j).nInputs = N.nInputs + m := rfl

theorem Network.withControl_outputs_length (N : Network) (m j : Nat) :
    (N.withControl m j).outputs.length = 1 := rfl

/-- The two appended nodes, as pushes (`Array.append` of a literal reduces). -/
theorem Network.withControl_nodes (N : Network) (m j : Nat) :
    (N.withControl m j).nodes =
      (N.nodes.push (.input (N.nInputs + j))).push (.and (N.outputs.headD 0) N.nodes.size) := rfl

/-- Report §6.1.2 — in a well-formed network every `input k` node has `k < nInputs`
(by membership; `Network.WF.input_lt` of `CQRV.Circuit.OracleCorrect` is by index and imports
Physlib). -/
theorem Network.WF.inputLt_of_mem {N : Network} (hN : N.WF) {k : Nat}
    (h : Node.input k ∈ N.nodes) : k < N.nInputs := by
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp h
  have hsz : i < N.nodes.size := by
    rcases Nat.lt_or_ge i N.nodes.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none hge] at hi
      cases hi
  unfold Network.WF Network.wf at hN
  rw [Bool.and_eq_true, List.all_eq_true] at hN
  have := hN.1 i (List.mem_range.mpr hsz)
  rw [hi] at this
  simpa using this

/-- Report §6.1.2 — in a well-formed network every output index is a node. -/
theorem Network.WF.outputLt_of_mem {N : Network} (hN : N.WF) {o : Nat} (h : o ∈ N.outputs) :
    o < N.nodes.size := by
  unfold Network.WF Network.wf at hN
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hN
  simpa using hN.2 o h

/-- PHASE2_SPEC.md §A.3 (Stage 19b) — `withControl` of a well-formed one-output network is well
formed for `j < m`: the old nodes keep their clauses (the input bound only grows), the control
input is below `N.nInputs + m`, and the new AND reads the output node and the control node. -/
theorem Network.withControl_WF {N : Network} {m j : Nat} (hN : N.WF)
    (h1 : N.outputs.length = 1) (hj : j < m) : (N.withControl m j).WF := by
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp h1
  have hos : o < N.nodes.size := hN.outputLt_of_mem (by simp [ho])
  have hN' := hN
  unfold Network.WF Network.wf at hN' ⊢
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hN' ⊢
  obtain ⟨hnodes, -⟩ := hN'
  have hsize : (N.withControl m j).nodes.size = N.nodes.size + 2 := by
    simp [Network.withControl]
  refine ⟨fun k hk => ?_, fun o' ho' => ?_⟩
  · rw [List.mem_range, hsize] at hk
    show (match (N.nodes ++ #[.input (N.nInputs + j), .and (N.outputs.headD 0) N.nodes.size])[k]?
        with
      | some (Node.input i) => decide (i < N.nInputs + m)
      | some (Node.const _) => true
      | some (Node.not i) => decide (i < k)
      | some (Node.and i j) | some (Node.xor i j) => decide (i < k) && decide (j < k)
      | none => true) = true
    by_cases hk' : k < N.nodes.size
    · rw [Array.getElem?_append_left hk']
      have h := hnodes k (List.mem_range.mpr hk')
      cases hv : N.nodes[k]? with
      | none => rfl
      | some v =>
        rw [hv] at h
        cases v <;> simp_all
        omega
    · rw [Array.getElem?_append_right (by omega)]
      rcases (by omega : k - N.nodes.size = 0 ∨ k - N.nodes.size = 1) with h0 | h0
      · rw [h0]
        simpa using hj
      · rw [h0]
        simp only [ho, List.headD_cons, List.getElem?_toArray, List.getElem?_cons_succ,
          List.getElem?_cons_zero]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
  · simp only [Network.withControl, List.mem_singleton] at ho'
    rw [hsize, ho']
    simp

/-- One step of `Network.values` reads `x` only at an `input` node. -/
theorem foldl_nodeStep_congr {x y : Nat → Bool} :
    ∀ (l : List Node), (∀ k, Node.input k ∈ l → x k = y k) →
      ∀ acc : Array Bool, l.foldl (nodeStep x) acc = l.foldl (nodeStep y) acc
  | [], _, _ => rfl
  | v :: l, h, acc => by
    rw [List.foldl_cons, List.foldl_cons,
      foldl_nodeStep_congr l (fun k hk => h k (List.mem_cons_of_mem _ hk))]
    congr 1
    cases v with
    | input k => simp only [nodeStep]; rw [h k List.mem_cons_self]
    | _ => rfl

/-- Report §6.1.2 — the node values depend on the input assignment only at the `input` nodes. -/
theorem nodeVals_congr {ns : Array Node} {x y : Nat → Bool}
    (h : ∀ k, Node.input k ∈ ns → x k = y k) : nodeVals ns x = nodeVals ns y := by
  unfold nodeVals
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_nodeStep_congr ns.toList (fun k hk => h k (Array.mem_def.mpr hk)) #[]

/-- PHASE2_SPEC.md §A.3 (Stage 19b) — the predicate of `withControl` is the conjunction of the
control bit with `N`'s predicate on the first `N.nInputs` bits: the values of `N`'s nodes do not
change when nodes are appended (`nodeVal_push_lt`) and do not read the inputs `≥ N.nInputs`
(`nodeVals_congr` with `N.WF`). -/
theorem Network.withControl_pred {N : Network} {m j : Nat} (hN : N.WF)
    (h1 : N.outputs.length = 1) (hj : j < m) (x : Fin (N.nInputs + m) → Bool) :
    (N.withControl m j).pred (N.nInputs + m) x =
      (x ⟨N.nInputs + j, by omega⟩ && N.pred N.nInputs (fun i => x (Fin.castAdd m i))) := by
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp h1
  have hos : o < N.nodes.size := hN.outputLt_of_mem (by simp [ho])
  -- the two input assignments agree on `N`'s inputs
  have hagree : nodeVals N.nodes (fun k => if h : k < N.nInputs + m then x ⟨k, h⟩ else false) =
      nodeVals N.nodes (fun k => if h : k < N.nInputs then x (Fin.castAdd m ⟨k, h⟩) else false) := by
    refine nodeVals_congr fun k hk => ?_
    have hk' : k < N.nInputs := hN.inputLt_of_mem hk
    simp only [hk', show k < N.nInputs + m by omega, ↓reduceDIte]
    rfl
  -- the left-hand side is the value of the appended AND
  have hL : (N.withControl m j).pred (N.nInputs + m) x =
      nodeVal (N.withControl m j).nodes
        (fun k => if h : k < N.nInputs + m then x ⟨k, h⟩ else false) (N.nodes.size + 1) := by
    simp only [Network.pred, Network.eval, Network.withControl, List.map_cons, List.map_nil,
      List.headD_cons]
    rfl
  have hR : N.pred N.nInputs (fun i => x (Fin.castAdd m i)) =
      nodeVal N.nodes (fun k => if h : k < N.nInputs then x (Fin.castAdd m ⟨k, h⟩) else false) o := by
    simp only [Network.pred, Network.eval, ho, List.map_cons, List.map_nil, List.headD_cons]
    rfl
  rw [hL, hR, Network.withControl_nodes, ho, List.headD_cons,
    show N.nodes.size + 1 = (N.nodes.push (Node.input (N.nInputs + j))).size from
      (Array.size_push _).symm,
    nodeVal_push_and, nodeVal_push_lt hos, nodeVal_push_self, Bool.and_comm]
  unfold nodeVal
  rw [hagree]
  simp only [show N.nInputs + j < N.nInputs + m by omega, ↓reduceDIte]

/-! ## B3 — the builders -/

open Diffusion

/-- PHASE2_SPEC.md §A.3 "Controlled diffusion", amendment (1) (Stage 19b) — `H^{⊗n} X^{⊗n}` on
the search register, the phase oracle of `(diffusionNet shape n).withControl m j` (an MCZ on the
`n` search qubits and phase qubit `j`), `X^{⊗n} H^{⊗n}`, on the data register of `n + m` qubits;
the data layers are uncontrolled (they cancel when the control is 0). The MCZ is synthesized in
`mode`; ancillae from `anc[0]`. -/
def controlledDiffusion (n m j : Nat) (shape : DiffusionShape := .tree)
    (mode : UncomputeMode := .mbu) : Except Diagnostic Circuit := do
  let mcz ← synthesizeOracle ((diffusionNet shape n).withControl m j) mode
  return ((⟨n + m, onAll .h n ++ onAll .x n⟩ : Circuit).append mcz).append
    ⟨n + m, onAll .x n ++ onAll .h n⟩

/-- PHASE2_SPEC.md §A.3 amendments (1)–(3) (Stage 19b) — the controlled Grover iterate on phase
qubit `j`: the oracle of `N.withControl m j` (controlled-`U_P`), the controlled diffusion
(`ctrl_j(−U_s)`), and the phase fix `z (data (n+j))`, so that the block applies exactly
`ctrl_j(G)`, `G = U_s U_P`. Refused: a predicate on `≠ n` inputs or with `≠ 1` outputs, `n = 0`
(`unsupported_network`), a phase qubit `j ≥ m` (`unsupported_combination`). -/
def controlledGrover (N : Network) (n m j : Nat) (shape : DiffusionShape := .tree)
    (mode : UncomputeMode := .mbu) : Except Diagnostic Circuit :=
  if N.nInputs != n then
    fail .unsupportedNetwork s!"the predicate has {N.nInputs} inputs, the search register {n}"
  else if N.outputs.length != 1 then
    fail .unsupportedNetwork s!"the counting circuit needs a one-bit predicate, the network has \
      {N.outputs.length} outputs"
  else if m ≤ j then
    fail .unsupportedCombination s!"phase qubit {j} is outside the phase register of {m} qubits"
  else if n == 0 then
    fail .unsupportedNetwork "the counting circuit needs at least one search qubit"
  else do
    let o ← synthesizeOracle (N.withControl m j) mode
    let d ← controlledDiffusion n m j shape mode
    return (o.append d).append ⟨n + m, [.z (.data (n + j))]⟩

/-- PHASE2_SPEC.md §A.3 amendment (4) (Stage 19b) — the controlled iterates up to phase qubit
`j`, after `init`: for `i < j`, the `2^i` copies of `controlledGrover N n m i` in program order,
joined by `Circuit.append` (`(List.replicate (2^i) b_i).foldl Circuit.append acc`, the shape of
`groverCircuit` and of `ancRestore_foldl`). -/
def countingPowers (N : Network) (n m : Nat) (shape : DiffusionShape) (mode : UncomputeMode)
    (init : Circuit) : Nat → Except Diagnostic Circuit
  | 0 => pure init
  | j + 1 => do
    let acc ← countingPowers N n m shape mode init j
    let b ← controlledGrover N n m j shape mode
    return (List.replicate (2 ^ j) b).foldl Circuit.append acc

/-- PHASE2_SPEC.md §A.3 amendment (4) (Stage 19b) — the initial layer: `H` on all `n + m` data
qubits (`|s⟩` on the search register, `|+⟩^{⊗m}` on the phase register). -/
def countingHLayer (n m : Nat) : Circuit := ⟨n + m, onAll .h (n + m)⟩

/-- PHASE2_SPEC.md §A.3 amendment (4) (Stage 19b) — the gate list the inverse is taken of:
`qftGates m`, or `aqftGates m kmax` when a `kmax` is given. -/
def inverseGates (m : Nat) (kmax : Option Nat) : List Gate :=
  match kmax with
  | some k => aqftGates m k
  | none => qftGates m

/-- PHASE2_SPEC.md §A.3 amendment (4) (Stage 19b) — the inverse (A)QFT on the phase register:
`adjointGates` of `inverseGates m kmax` (`qftGates m`, or `aqftGates m kmax`), shifted onto
`data n..n+m−1` by `Gate.shiftData n`. -/
def countingInverse (n m : Nat) (kmax : Option Nat) : Circuit :=
  ⟨n + m, (adjointGates (inverseGates m kmax)).map (Gate.shiftData n)⟩

/-- PHASE2_SPEC.md §A.3 amendment (4) (Stage 19b) — the counting circuit: `H` on all `n + m`
data qubits; for `j = 0..m−1` the `2^j` copies of `controlledGrover N n m j`; the inverse (A)QFT
on the phase register. The phase register is read by the decoding of §A.4, not measured in the IR.
Refused: `m = 0` (`unsupported_network`), and whatever `controlledGrover` refuses. -/
def countingCircuit (N : Network) (n m : Nat) (kmax : Option Nat := none)
    (shape : DiffusionShape := .tree) (mode : UncomputeMode := .mbu) :
    Except Diagnostic Circuit :=
  if m == 0 then fail .unsupportedNetwork "the counting circuit needs at least one phase qubit"
  else do
    let body ← countingPowers N n m shape mode (countingHLayer n m) m
    return body.append (countingInverse n m kmax)

/-! ### The shape of a successful build (Physlib-free; used by `CQRV.Circuit.CountingCorrect`) -/

theorem fail_ne_ok {α : Type} (code : Code) (msg : String) (a : α) :
    Diffusion.fail code msg ≠ .ok a := by
  simp [Diffusion.fail, throw, throwThe, MonadExceptOf.throw]

/-- `controlledDiffusion` succeeds exactly when its MCZ is synthesized, and is then the
`H X ; MCZ ; X H` sandwich on `n + m` data qubits. -/
theorem controlledDiffusion_ok {n m j : Nat} {shape : DiffusionShape} {mode : UncomputeMode}
    {D : Circuit} (h : controlledDiffusion n m j shape mode = .ok D) :
    ∃ mcz, synthesizeOracle ((diffusionNet shape n).withControl m j) mode = .ok mcz ∧
      D = ((⟨n + m, onAll .h n ++ onAll .x n⟩ : Circuit).append mcz).append
        ⟨n + m, onAll .x n ++ onAll .h n⟩ := by
  unfold controlledDiffusion at h
  cases hs : synthesizeOracle ((diffusionNet shape n).withControl m j) mode with
  | error e => simp [hs, bind, Except.bind] at h
  | ok mcz =>
    refine ⟨mcz, rfl, ?_⟩
    simp [hs, bind, Except.bind, pure, Except.pure] at h
    exact h.symm

/-- `controlledGrover` succeeds only on a one-output predicate on `n ≥ 1` inputs with `j < m`,
and is then the controlled oracle, the controlled diffusion and the phase fix. -/
theorem controlledGrover_ok {N : Network} {n m j : Nat} {shape : DiffusionShape}
    {mode : UncomputeMode} {G : Circuit} (h : controlledGrover N n m j shape mode = .ok G) :
    N.nInputs = n ∧ N.outputs.length = 1 ∧ j < m ∧ n ≠ 0 ∧
      ∃ o d, synthesizeOracle (N.withControl m j) mode = .ok o ∧
        controlledDiffusion n m j shape mode = .ok d ∧
        G = (o.append d).append ⟨n + m, [.z (.data (n + j))]⟩ := by
  unfold controlledGrover at h
  split at h
  · exact absurd h (fail_ne_ok _ _ _)
  split at h
  · exact absurd h (fail_ne_ok _ _ _)
  split at h
  · exact absurd h (fail_ne_ok _ _ _)
  split at h
  · exact absurd h (fail_ne_ok _ _ _)
  rename_i h1 h2 h3 h4
  refine ⟨by simpa using h1, by simpa using h2, by omega, by simpa using h4, ?_⟩
  cases ho : synthesizeOracle (N.withControl m j) mode with
  | error e => simp [ho, bind, Except.bind] at h
  | ok o =>
    cases hd : controlledDiffusion n m j shape mode with
    | error e => simp [ho, hd, bind, Except.bind] at h
    | ok d =>
      refine ⟨o, d, rfl, rfl, ?_⟩
      simp [ho, hd, bind, Except.bind, pure, Except.pure] at h
      exact h.symm

theorem countingPowers_zero (N : Network) (n m : Nat) (shape : DiffusionShape)
    (mode : UncomputeMode) (init : Circuit) : countingPowers N n m shape mode init 0 = .ok init :=
  rfl

/-- One more phase qubit: the previous powers, then `2^j` copies of block `j`. -/
theorem countingPowers_succ_ok {N : Network} {n m : Nat} {shape : DiffusionShape}
    {mode : UncomputeMode} {init C : Circuit} {j : Nat}
    (h : countingPowers N n m shape mode init (j + 1) = .ok C) :
    ∃ acc b, countingPowers N n m shape mode init j = .ok acc ∧
      controlledGrover N n m j shape mode = .ok b ∧
      C = (List.replicate (2 ^ j) b).foldl Circuit.append acc := by
  unfold countingPowers at h
  cases ha : countingPowers N n m shape mode init j with
  | error e => simp [ha, bind, Except.bind] at h
  | ok acc =>
    cases hb : controlledGrover N n m j shape mode with
    | error e => simp [ha, hb, bind, Except.bind] at h
    | ok b =>
      refine ⟨acc, b, rfl, rfl, ?_⟩
      simp [ha, hb, bind, Except.bind, pure, Except.pure] at h
      exact h.symm

/-- `countingCircuit` succeeds only for `m ≥ 1`, and is then the powers after the Hadamard layer
followed by the shifted inverse (A)QFT. -/
theorem countingCircuit_ok {N : Network} {n m : Nat} {kmax : Option Nat} {shape : DiffusionShape}
    {mode : UncomputeMode} {C : Circuit} (h : countingCircuit N n m kmax shape mode = .ok C) :
    m ≠ 0 ∧ ∃ body, countingPowers N n m shape mode (countingHLayer n m) m = .ok body ∧
      C = body.append (countingInverse n m kmax) := by
  unfold countingCircuit at h
  split at h
  · exact absurd h (fail_ne_ok _ _ _)
  rename_i hm
  refine ⟨by simpa using hm, ?_⟩
  cases hb : countingPowers N n m shape mode (countingHLayer n m) m with
  | error e => simp [hb, bind, Except.bind] at h
  | ok body =>
    refine ⟨body, rfl, ?_⟩
    simp [hb, bind, Except.bind, pure, Except.pure] at h
    exact h.symm

/-- The converse of `countingCircuit_ok` (Stage 20b2, PHASE2_SPEC.md §A.4 (4)): for `m ≠ 0`, from
the powers `body`, `countingCircuit` is the body followed by the shifted inverse (A)QFT — for every
`kmax`, so the exact and the approximate circuits share their `body`. -/
theorem countingCircuit_of_body {N : Network} {n m : Nat} (kmax : Option Nat)
    {shape : DiffusionShape} {mode : UncomputeMode} {body : Circuit} (hm : m ≠ 0)
    (hb : countingPowers N n m shape mode (countingHLayer n m) m = .ok body) :
    countingCircuit N n m kmax shape mode = .ok (body.append (countingInverse n m kmax)) := by
  unfold countingCircuit
  simp [hm, hb, bind, Except.bind, pure, Except.pure]

/-! ## Stage 20b3 (C1; PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3" (2)) — the counting
circuit assembled from its distinct blocks, for the compositional certificate -/

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)) — the counting circuit assembled from
its distinct blocks: the fold of `Circuit.append` from `init` over the `2^j` copies of block `j`
in program order (the list form of `Circuit.grade_foldl_append_le`), then the inverse block. The
lambda is written with projections (`p.1`, `p.2`), not `fun (b, j) =>`: a pattern-matching lambda
elaborates to its own matcher at every occurrence, which `rw` does not identify. -/
def assembleCounting (init : Circuit) (bs : List Circuit) (inv : Circuit) : Circuit :=
  ((bs.zipIdx.flatMap fun p => List.replicate (2 ^ p.2) p.1).foldl Circuit.append init).append inv

/-- One more phase qubit, forward: from the powers up to `j` and block `j`. -/
theorem countingPowers_succ {N : Network} {n m : Nat} {shape : DiffusionShape}
    {mode : UncomputeMode} {init acc b : Circuit} {j : Nat}
    (h : countingPowers N n m shape mode init j = .ok acc)
    (hb : controlledGrover N n m j shape mode = .ok b) :
    countingPowers N n m shape mode init (j + 1) =
      .ok ((List.replicate (2 ^ j) b).foldl Circuit.append acc) := by
  unfold countingPowers
  simp [h, hb, bind, Except.bind, pure, Except.pure]

/-- The powers up to `k` from the first `k` blocks: the fold over the `2^j` copies of block
`j`, `j < k`. -/
theorem countingPowers_eq_foldl {N : Network} {n m : Nat} {shape : DiffusionShape}
    {mode : UncomputeMode} (init : Circuit) (bs : List Circuit) :
    ∀ (k : Nat) (hk : k ≤ bs.length),
      (∀ j (h : j < k), controlledGrover N n m j shape mode =
        .ok (bs[j]'(Nat.lt_of_lt_of_le h hk))) →
      countingPowers N n m shape mode init k =
        .ok (((bs.take k).zipIdx.flatMap fun p => List.replicate (2 ^ p.2) p.1).foldl
          Circuit.append init)
  | 0, _, _ => by simp [countingPowers_zero]
  | k + 1, hk, hbs => by
    have hk' : k < bs.length := hk
    have ih := countingPowers_eq_foldl init bs k (Nat.le_of_lt hk')
      fun j hj => hbs j (Nat.lt_succ_of_lt hj)
    rw [countingPowers_succ ih (hbs k (Nat.lt_succ_self k)), List.take_succ_eq_append_getElem hk',
      List.zipIdx_append, List.length_take_of_le (Nat.le_of_lt hk'), Nat.zero_add,
      List.zipIdx_singleton, List.flatMap_append, List.flatMap_singleton, List.foldl_append]

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)) — **the converse direction of
`countingCircuit_ok`** for the certificate: with `m ≠ 0` and the `m` controlled iterates given
as blocks, `countingCircuit` is `assembleCounting` of the Hadamard layer, the blocks and the
inverse (A)QFT — so `emitted_ok` needs no kernel evaluation of the whole circuit, only of each
block's link `controlledGrover … = .ok block`. -/
theorem countingCircuit_of_blocks {N : Network} {n m : Nat} (kmax : Option Nat)
    {shape : DiffusionShape} {mode : UncomputeMode} {bs : List Circuit} (hm : m ≠ 0)
    (hlen : bs.length = m)
    (hbs : ∀ j (h : j < m), controlledGrover N n m j shape mode = .ok (bs[j]'(hlen ▸ h))) :
    countingCircuit N n m kmax shape mode =
      .ok (assembleCounting (countingHLayer n m) bs (countingInverse n m kmax)) := by
  subst hlen
  have h := countingPowers_eq_foldl (N := N) (shape := shape) (mode := mode)
    (countingHLayer n bs.length) bs bs.length (Nat.le_refl _) fun j hj => hbs j hj
  rw [List.take_length] at h
  exact countingCircuit_of_body kmax hm h

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)), report §3.1.4 — **the composed grade
bound of the assembled counting circuit**: every block on the data register of `init` and
ending with no live ancilla, `grade ≤ grade init ⊕ ∑_j 2^j • grade (block j) ⊕ grade inv`
(`Circuit.grade_foldl_append_le`, `Circuit.grade_append_le`). A certificate rewrites the right-hand
side with the blocks' `grade_eq` and closes the arithmetic by `decide`. -/
theorem grade_assembleCounting_le (init : Circuit) (bs : List Circuit) (inv : Circuit)
    (hn : ∀ b ∈ bs, b.nData = init.nData) (hinv : inv.nData = init.nData)
    (hi : init.liveEnd = 0) (hb : ∀ b ∈ bs, b.liveEnd = 0) :
    Synthesis.grade (assembleCounting init bs inv) ≤
      Synthesis.grade init + (bs.zipIdx.map fun p => 2 ^ p.2 • Synthesis.grade p.1).sum +
        Synthesis.grade inv := by
  unfold assembleCounting Synthesis.grade
  have hnL : ∀ c ∈ bs.zipIdx.flatMap fun p => List.replicate (2 ^ p.2) p.1,
      c.nData = init.nData := fun c hc => by
    rw [List.mem_flatMap] at hc
    obtain ⟨⟨b, j⟩, hbj, hc⟩ := hc
    rw [List.eq_of_mem_replicate hc]
    exact hn b (List.fst_mem_of_mem_zipIdx hbj)
  have hbL : ∀ c ∈ bs.zipIdx.flatMap fun p => List.replicate (2 ^ p.2) p.1,
      c.liveEnd = 0 := fun c hc => by
    rw [List.mem_flatMap] at hc
    obtain ⟨⟨b, j⟩, hbj, hc⟩ := hc
    rw [List.eq_of_mem_replicate hc]
    exact hb b (List.fst_mem_of_mem_zipIdx hbj)
  have h1 := Circuit.grade_foldl_append_le init _ hnL hi hbL
  have h2 := Circuit.grade_append_le (C₂ := inv)
    (by rw [Circuit.nData_foldl_append]; exact hinv.symm) (Circuit.liveEnd_foldl_append init _ hi hbL)
  exact le_trans h2 (Grade.seqComp_mono (le_trans h1 (le_of_eq (congrArg (init.grade + ·)
    (Circuit.sum_map_flatMap_replicate bs.zipIdx Circuit.grade)))) (le_refl _))

/-- PHASE2_SPEC.md §A.4 (amendments before Stage 20b3, (2)), §A.1, §A.3 amendment (6) — **the
composed second record of the assembled counting circuit**: `twoQ`, `rot`, `meas`, `ff` are the
sums over the blocks with their multiplicities, and the T-depth is at most
`tDepth init + ∑_j 2^j · tCount (block j) + tCount inv` (19a's `gradeExt_*_foldl_append`,
`gradeExt_tDepth_foldl_append_le`, `tDepth_append_le`); no hypothesis. -/
theorem gradeExt_assembleCounting (init : Circuit) (bs : List Circuit) (inv : Circuit) :
    (Synthesis.gradeExt (assembleCounting init bs inv)).twoQ =
        (Synthesis.gradeExt init).twoQ +
          (bs.zipIdx.map fun p => 2 ^ p.2 * (Synthesis.gradeExt p.1).twoQ).sum +
          (Synthesis.gradeExt inv).twoQ ∧
      (Synthesis.gradeExt (assembleCounting init bs inv)).rot =
        (Synthesis.gradeExt init).rot +
          (bs.zipIdx.map fun p => 2 ^ p.2 * (Synthesis.gradeExt p.1).rot).sum +
          (Synthesis.gradeExt inv).rot ∧
      (Synthesis.gradeExt (assembleCounting init bs inv)).meas =
        (Synthesis.gradeExt init).meas +
          (bs.zipIdx.map fun p => 2 ^ p.2 * (Synthesis.gradeExt p.1).meas).sum +
          (Synthesis.gradeExt inv).meas ∧
      (Synthesis.gradeExt (assembleCounting init bs inv)).ff =
        (Synthesis.gradeExt init).ff +
          (bs.zipIdx.map fun p => 2 ^ p.2 * (Synthesis.gradeExt p.1).ff).sum +
          (Synthesis.gradeExt inv).ff ∧
      (Synthesis.gradeExt (assembleCounting init bs inv)).tDepth ≤
        (Synthesis.gradeExt init).tDepth +
          (bs.zipIdx.map fun p => 2 ^ p.2 * (Synthesis.grade p.1).t).sum +
          (Synthesis.grade inv).t := by
  unfold assembleCounting Synthesis.gradeExt Synthesis.grade
  have key : ∀ (f : Circuit → Nat), ((bs.zipIdx.flatMap fun p =>
      List.replicate (2 ^ p.2) p.1).map f).sum = (bs.zipIdx.map fun p => 2 ^ p.2 * f p.1).sum := by
    intro f
    exact Circuit.sum_map_flatMap_replicate_nat bs.zipIdx f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Circuit.gradeExt_twoQ_append, Circuit.gradeExt_twoQ_foldl_append]
    exact congrArg (fun x => init.gradeExt.twoQ + x + inv.gradeExt.twoQ) (key _)
  · rw [Circuit.gradeExt_rot_append, Circuit.gradeExt_rot_foldl_append]
    exact congrArg (fun x => init.gradeExt.rot + x + inv.gradeExt.rot) (key _)
  · rw [Circuit.gradeExt_meas_append, Circuit.gradeExt_meas_foldl_append]
    exact congrArg (fun x => init.gradeExt.meas + x + inv.gradeExt.meas) (key _)
  · rw [Circuit.gradeExt_ff_append, Circuit.gradeExt_ff_foldl_append]
    exact congrArg (fun x => init.gradeExt.ff + x + inv.gradeExt.ff) (key _)
  · refine Nat.le_trans (Circuit.tDepth_append_le _ _) ?_
    have h := Circuit.gradeExt_tDepth_foldl_append_le init
      (bs.zipIdx.flatMap fun p => List.replicate (2 ^ p.2) p.1)
    exact Nat.add_le_add_right (Nat.le_trans h (Nat.le_of_eq
      (congrArg (init.gradeExt.tDepth + ·) (key Circuit.tCount)))) _

end CQRV.Synthesis

end
