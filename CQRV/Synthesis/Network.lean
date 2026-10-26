module

public import CQRV.DSL.Check
public import CQRV.DSL.Diagnostic

/-!
# CQRV.Synthesis.Network

Report §6.1.2 ("the certifying synthesizer accepts a Boolean network (extracted from the input
DSL term), counts its AND nodes") — the synthesis input (DECISIONS.md 2026-10-23, Stage 5
decision 1): a Boolean network of AND / NOT / XOR nodes over the input bits, built from the
typed term by `toNetwork`, not from `SigmaIn` (which carries counts only).

`toNetwork` follows the counting rules of ℰ (`CQRV.DSL.Extract`) node for node, so the number
of AND nodes is ĉ∧:
* `or` by De Morgan: `¬(¬a ∧ ¬b)` (one AND), never DNF;
* `if c then a else b`: the Stage 3 mux `b ⊕ (c ∧ (a ⊕ b))`, one AND per result bit;
* `let`: the bound value is built once and shared;
* `for`: unrolled, `n` copies of the body;
* `loop … while`: rejected (`unbounded_loop`): no finite network.
Values are lists of node indices, one per bit (`Ty.width`); inputs are laid out from bit 0 in
parameter order, as in ℰ. A `Nat m` value is little-endian (bit `j` = `(k >>> j) &&& 1`).
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL

/-- Report §6.1.2 — a node of a Boolean network over the basis {∧, ⊕, ¬, constants}.
Operands are indices of earlier nodes (the node array is topologically ordered). -/
inductive Node where
  | input (k : Nat)
  | const (b : Bool)
  | not (i : Nat)
  | and (i j : Nat)
  | xor (i j : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Report §6.1.2 — a Boolean network: `nInputs` input bits, nodes in topological order (node
`k < nInputs` is `input k`), and the output bits. -/
structure Network where
  nInputs : Nat
  nodes : Array Node
  outputs : List Nat
  deriving Repr, Inhabited

/-- Report §6.1.2 — the number of AND nodes (ĉ∧ of the network). -/
def Network.andCount (N : Network) : Nat :=
  N.nodes.foldl (fun n v => match v with | .and _ _ => n + 1 | _ => n) 0

/-- Report §6.1.2 — evaluate every node on an input assignment (`x k` = input bit `k`). -/
def Network.values (N : Network) (x : Nat → Bool) : Array Bool :=
  N.nodes.foldl (fun vs v => vs.push <| match v with
    | .input k => x k
    | .const b => b
    | .not i => !vs.getD i false
    | .and i j => vs.getD i false && vs.getD j false
    | .xor i j => vs.getD i false ^^ vs.getD j false) #[]

/-- Report §6.1.2 — the output bits on an input assignment. -/
def Network.eval (N : Network) (x : Nat → Bool) : List Bool :=
  let vs := N.values x
  N.outputs.map (vs.getD · false)

/-- Report §6.3.2 — the predicate `P : Reg n → Bool` of a one-output network (`Reg n = Fin n →
Bool`): the first output bit, input bit `k` being `x[k]` (`false` beyond `n`). Moved unchanged
from `CQRV/Circuit/Restoration.lean` (Stage 9b) so that the CLI's front-end validation can use it
without linking Physlib. -/
def Network.pred (N : Network) (n : Nat) (x : Fin n → Bool) : Bool :=
  (N.eval fun k => if h : k < n then x ⟨k, h⟩ else false).headD false

/-- Report §6.1.2, §6.3.2 — a well-formed network (decidable check; Stage 9a review): every
`input k` has `k < nInputs`, every operand index is smaller than its node's index (topological
order), and every output index is a node. The side condition of
`synthesizeOracle_WF` (`CQRV.Circuit.OracleCorrect`, Stage 11a); without it the synthesizer can emit a data qubit
outside the register (`⟨0, #[.input 5], [0]⟩` ↦ `Z x[5]`). -/
def Network.wf (N : Network) : Bool :=
  (List.range N.nodes.size).all (fun k =>
    match N.nodes[k]? with
    | some (.input i) => decide (i < N.nInputs)
    | some (.const _) => true
    | some (.not i) => decide (i < k)
    | some (.and i j) | some (.xor i j) => decide (i < k) && decide (j < k)
    | none => true) &&
  N.outputs.all (· < N.nodes.size)

/-- Report §6.1.2, §6.3.2 — `Network.wf` as a proposition (as `Circuit.WF`). -/
def Network.WF (N : Network) : Prop := N.wf = true

instance (N : Network) : Decidable N.WF := inferInstanceAs (Decidable (N.wf = true))

namespace ToNetwork

/-- What a name denotes while building: the bits of a value, or a `for` index fixed by
unrolling. -/
inductive NVal where
  | bits (bs : List Nat)
  | index (k : Nat)

/-- Builder monad: the node array under construction. -/
abbrev NM := StateT (Array Node) (Except Diagnostic)

/-- Append a node, return its index. -/
def push (v : Node) : NM Nat := modifyGet fun ns => (ns.size, ns.push v)

/-- Raise a synthesis diagnostic (the typed term carries no positions). -/
def fail {α : Type} (code : Code) (msg : String) : NM α :=
  throw (Diagnostic.at .synthesis code ⟨1, 1⟩ msg)

/-- Report §6.1.2 — `ite` on one bit: `b ⊕ (c ∧ (a ⊕ b))` (Stage 3 mux rule). -/
def mux (c a b : Nat) : NM Nat := do
  let d ← push (.xor a b)
  let e ← push (.and c d)
  push (.xor b e)

/-- Constant bits of `k : Nat m`, little-endian, `Ty.width (.nat m)` of them. -/
def natBits (m k : Nat) : NM (List Nat) :=
  (List.range (Ty.width (.nat m))).mapM fun j => push (.const ((k >>> j) % 2 == 1))

/-- Report §6.1.2 — the network of a typed term, structurally recursive (like ℰ). -/
def build : {τ : Ty} → TExpr τ → List (String × NVal) → NM (List Nat)
  | τ, .var x _, env =>
    match env.lookup x, τ with
    | some (.bits bs), _ => pure bs
    | some (.index k), .nat m => natBits m k
    | _, _ => fail .unsupportedNetwork s!"internal: `{x}` has no bits"
  | _, .lit b, _ => return [← push (.const b)]
  | _, .not a, env => do
    let [i] ← build a env | fail .unsupportedNetwork "internal: `not` of a non-bit"
    return [← push (.not i)]
  | _, .and a b, env => do
    let [i] ← build a env | fail .unsupportedNetwork "internal: `and` of a non-bit"
    let [j] ← build b env | fail .unsupportedNetwork "internal: `and` of a non-bit"
    return [← push (.and i j)]
  | _, .or a b, env => do
    let [i] ← build a env | fail .unsupportedNetwork "internal: `or` of a non-bit"
    let [j] ← build b env | fail .unsupportedNetwork "internal: `or` of a non-bit"
    let ni ← push (.not i)
    let nj ← push (.not j)
    let c ← push (.and ni nj)
    return [← push (.not c)]
  | _, .xor a b, env => do
    let [i] ← build a env | fail .unsupportedNetwork "internal: `xor` of a non-bit"
    let [j] ← build b env | fail .unsupportedNetwork "internal: `xor` of a non-bit"
    return [← push (.xor i j)]
  | _, .idx v k, env => do
    let bs ← build v env
    let pos ← match k with
      | .lit k => pure k.val
      | .loopVar x _ _ =>
        match env.lookup x with
        | some (.index k) => pure k
        | _ => fail .unsupportedNetwork s!"internal: loop variable `{x}` is not fixed"
    match bs[pos]? with
    | some b => pure [b]
    | none => fail .unsupportedNetwork "internal: index out of range"
  | _, .ite c a b, env => do
    let [ic] ← build c env | fail .unsupportedNetwork "internal: `if` on a non-bit"
    let as ← build a env
    let bs ← build b env
    (as.zip bs).mapM fun (x, y) => mux ic x y
  | _, .letE x e₁ e₂, env => do
    let v ← build e₁ env
    build e₂ ((x, .bits v) :: env)
  | _, .forE i n acc init body, env => do
    let v₀ ← build init env
    (List.range n).foldlM (fun v k => build body ((acc, .bits v) :: (i, .index k) :: env)) v₀
  | _, .loopE .., _ =>
    fail .unboundedLoop "`loop … while` has data-dependent termination: no finite Boolean \
      network (report §4.2.2, §6.1.2)"

end ToNetwork

open ToNetwork in
/-- Report §6.1.2, DECISIONS.md 2026-10-23 (Stage 5 decision 1) — the Boolean network of a
typed program. Fails only on `loop … while` (`unbounded_loop`). -/
def toNetwork (tp : TypedProgram) : Except Diagnostic Network := do
  let n := (tp.params.map (·.2.width)).sum
  let inputs : Array Node := (Array.range n).map .input
  let (_, env) := tp.params.foldl (fun (o, env) (x, τ) =>
    (o + τ.width, (x, NVal.bits (List.range' o τ.width)) :: env)) (0, [])
  let (outs, nodes) ← (build tp.body env).run inputs
  return { nInputs := n, nodes, outputs := outs }

end CQRV.Synthesis

end
