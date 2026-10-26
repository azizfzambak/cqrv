module

public import CQRV.Synthesis.Oracle
public import CQRV.Synthesis.Bennett

/-!
# CQRV.Synthesis.Diffusion

Report §8.2 (`U_s = 2|s⟩⟨s| − I = H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}`), §3.1.4 / Table 3.3 (diffusion
row), §6.1.4 / Table 3, §3.2.4 (circuit family) — the Grover diffusion operator and the Grover
circuit, built from the existing synthesizer (DECISIONS.md 2026-10-24, Stage 5b decisions 1–3):

* `2|0⟩⟨0| − I = −X^{⊗n} · MCZ · X^{⊗n}`, and `MCZ` is the phase oracle of
  `P_all(y) = y₀ ∧ … ∧ y_{n−1}`: since Stage 12a the balanced tree `treeNet n` (`n − 1` ANDs in
  `⌈log₂ n⌉` levels), `--shape chain` the AND chain `allNet n` of Stage 5b. So
  `diffusion n = H^{⊗n} ; X^{⊗n} ; oracle(P_all) ; X^{⊗n} ; H^{⊗n}`, equal to `U_s` up to the
  global phase −1. V1 (`aMax = none`): the straight-line oracle of `synthesizeOracle`
  (Lemma 6.3.2 applies, xor-free); V2 (`aMax = some k`): the Bennett pebbling of the chain
  (`pebbleChain`, Stage 5 decision 3), grade and harness only.
* The diffusion's ancillae start at `anc[0]`, so the oracle's restored ancillae are reused
  (§3.1.4): under the scheduler `a` of an iteration is `max(a_oracle, a_diffusion)`.
* `groverIteration P n = oracle(P).append (diffusion n)` (the shifted append of 6b-1);
  `groverCircuit P n r = H^{⊗n}` then `r` iterations. No final measurement in the IR.
* `rStar n M = ⌊π / (4θ)⌋`, `sin²θ = M / 2ⁿ` (§3.2.4, §8), computed in `Float`.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL

namespace Diffusion

/-- Raise a synthesis diagnostic. -/
def fail {α : Type} (code : Code) (msg : String) : Except Diagnostic α :=
  throw (Diagnostic.at .synthesis code ⟨1, 1⟩ msg)

/-- One gate per data qubit `x[0..n)`. -/
def onAll (g : Qubit → Gate) (n : Nat) : List Gate := (List.range n).map fun i => g (.data i)

end Diffusion

open Diffusion

/-- Report §8.2 — the network of `P_all(y) = y₀ ∧ … ∧ y_{n−1}` on `n ≥ 1` inputs: nodes
`0..n−1` are the inputs, node `n` is `AND(y₀, y₁)`, node `n + k − 1` is `AND(node n+k−2, y_k)`
(`k ≥ 2`). The output is the last AND (`y₀` itself when `n = 1`). A chain in the sense of
`Bennett.chainOf`, with operands `0, …, n − 1`. The node array is built from `List.range`, not
`Array.range`, whose body is not exposed to importing modules, so that the kernel can evaluate
the diffusion (`decide +kernel` in `CQRV.Grover.Instance`; DECISIONS.md, Stage 7a). -/
def allNet (n : Nat) : Network :=
  let ands := (List.range (n - 1)).map fun k =>
    if k == 0 then Node.and 0 1 else Node.and (n + k - 1) (k + 1)
  { nInputs := n, nodes := ((List.range n).map Node.input).toArray ++ ands.toArray,
    outputs := [if n ≤ 1 then 0 else 2 * n - 2] }

/-- Report §8.2, §6.1.4 (Stage 12a decision 1) — one level of the balanced AND tree: pair the
node indices `l` left to right, `AND(l₀, l₁)`, `AND(l₂, l₃)`, …, the new nodes numbered from
`k`; an odd last index is carried up unchanged. Returns the new nodes and the next level. -/
def treeLevel : List Nat → Nat → List Node × List Nat
  | [], _ => ([], [])
  | [i], _ => ([], [i])
  | i :: j :: rest, k =>
    let r := treeLevel rest (k + 1)
    (Node.and i j :: r.1, k :: r.2)

/-- Report §8.2 (Stage 12a decision 1) — the levels of the balanced AND tree over the node
indices `l`, new nodes numbered from `k`, at most `fuel` levels (`l.length ≤ fuel + 1` suffices:
each level of two or more indices is shorter by at least one). Returns the AND nodes and the
root (the last remaining index). Structural in `fuel`, so the kernel can evaluate it. -/
def treeBuild : Nat → List Nat → Nat → List Node × Nat
  | 0, l, _ => ([], l.headD 0)
  | f + 1, l, k =>
    if l.length ≤ 1 then ([], l.headD 0) else
    let r := treeLevel l k
    let s := treeBuild f r.2 (k + r.1.length)
    (r.1 ++ s.1, s.2)

/-- Report §8.2, §6.1.4, §3.3.3 / Table 3.5 (Stage 12a decision 1) — the network of
`P_all(y) = y₀ ∧ … ∧ y_{n−1}` as a **balanced tree**: nodes `0..n−1` are the inputs, then the AND
nodes level by level (`treeLevel`; for `n = 8`: `((y₀∧y₁)∧(y₂∧y₃))∧((y₄∧y₅)∧(y₆∧y₇))`). The same
`n − 1` ANDs as the chain `allNet n`, but `⌈log₂ n⌉` AND levels, so the scheduler runs the ANDs
of one level in parallel. Inputs from `List.range` (kernel evaluation, as `allNet`). -/
def treeNet (n : Nat) : Network :=
  let r := treeBuild n (List.range n) n
  { nInputs := n, nodes := ((List.range n).map Node.input).toArray ++ r.1.toArray,
    outputs := [r.2] }

/-- Report §8.2, §6.1.4 (Stage 12a decision 3) — the shape of the network of the diffusion's MCZ:
the balanced tree `treeNet n` (the default since Stage 12a) or the chain `allNet n` (the Stage 5b
construction, kept as `--shape chain`; the only shape with a Bennett pebbling, V2). -/
inductive DiffusionShape where
  | tree
  | chain
  deriving Repr, DecidableEq, Inhabited

/-- Report §8.2 — the network of `P_all` of the given shape. -/
def diffusionNet : DiffusionShape → Nat → Network
  | .tree, n => treeNet n
  | .chain, n => allNet n

/-- Report §6.1.3–6.1.4 — the oracle circuit of a network under ancilla budget `aMax`, with the
name of its schedule: straight-line when the budget covers every AND of `synthesizeOracle`
(or no budget is given); otherwise a Bennett pebbling, which decision 3 allows only for AND
chains (`infeasible_budget` when no pebbling exists). This is the logic of `cqr synthesize
--amax`, shared by the CLI and the V2 diffusion. -/
def synthesizeWithBudget (N : Network) (aMax : Option Nat) :
    Except Diagnostic (String × Circuit) := do
  let full ← synthesizeOracle N
  match aMax with
  | some k =>
    if k ≥ full.peakAncilla then return ("straight-line", full)
    let some lits := Bennett.chainOf N
      | fail .unsupportedNetwork s!"--amax {k} is below the {full.peakAncilla} ancillae of the \
          straight-line schedule; Bennett pebbling is implemented only for AND chains \
          (report §6.1.3, Stage 5 decision 3)"
    match pebbleChain (lits.length - 1) k with
    | .ok ms => return (s!"bennett(amax={k})", Bennett.chainCircuit N.nInputs lits ms)
    | .error e => fail .infeasibleBudget e
  | none => return ("straight-line", full)

/-- Report §8.2, §6.1.4 — the diffusion `D_n = H^{⊗n} X^{⊗n} · oracle(P_all) · X^{⊗n} H^{⊗n}`
(`= −U_s`) with the schedule name of its MCZ: V1 for `aMax = none`, V2 (Bennett) for
`aMax = some k`. Ancillae from `anc[0]` (Stage 5b decision 3). The MCZ is the oracle of
`diffusionNet shape n`, the balanced tree by default (Stage 12a decision 3); a Bennett pebbling
exists only for the chain. -/
def diffusionWith (n : Nat) (aMax : Option Nat) (shape : DiffusionShape := .tree) :
    Except Diagnostic (String × Circuit) := do
  if n == 0 then fail .unsupportedNetwork "the diffusion needs at least one data qubit"
  let (sched, mcz) ← synthesizeWithBudget (diffusionNet shape n) aMax
  let pre : Circuit := ⟨n, onAll .h n ++ onAll .x n⟩
  let post : Circuit := ⟨n, onAll .x n ++ onAll .h n⟩
  return (sched, (pre.append mcz).append post)

/-- Report §8.2, §3.1.4 (Table 3.3, diffusion row) — the diffusion circuit on `x[0..n)`
(Stage 5b decision 1: V1 when `aMax = none`, V2 with Bennett when `aMax = some k`; the MCZ
network a balanced tree unless `shape = .chain`, Stage 12a decision 3). -/
def diffusion (n : Nat) (aMax : Option Nat) (shape : DiffusionShape := .tree) :
    Except Diagnostic Circuit :=
  (·.2) <$> diffusionWith n aMax shape

/-- Report §8.2, §3.2.4 — one Grover iteration `U_s U_P`: the straight-line oracle of `P`
(`synthesizeOracle`, unchanged), then the diffusion on the same `n` data qubits, by the
shifted append of 6b-1 (the diffusion's bits follow the oracle's). -/
def groverIteration (P : Network) (n : Nat) (aMax : Option Nat := none)
    (shape : DiffusionShape := .tree) : Except Diagnostic Circuit := do
  if P.nInputs != n then
    fail .unsupportedNetwork s!"the predicate has {P.nInputs} inputs, the diffusion {n}"
  let oracle ← synthesizeOracle P
  let d ← diffusion n aMax shape
  return oracle.append d

/-- Report §3.2.4 — the Grover circuit `H^{⊗n}` then `r` iterations; the final measurement of
the data register is not part of the IR (the harness measures). -/
def groverCircuit (P : Network) (n r : Nat) (aMax : Option Nat := none)
    (shape : DiffusionShape := .tree) : Except Diagnostic Circuit := do
  let it ← groverIteration P n aMax shape
  return (List.replicate r it).foldl Circuit.append ⟨n, onAll .h n⟩

/-- Report §3.2.4, §8 — `r⋆ = ⌊π / (4θ)⌋` with `sin²θ = M / 2ⁿ`, for `1 ≤ M ≤ 2ⁿ`; computed in
`Float` (an engineering value for the CLI; the certificate will need an exact bound). -/
def rStar (n M : Nat) : Option Nat :=
  if M == 0 || M > 2 ^ n then none else
  let θ := Float.asin (Float.sqrt (M.toFloat / (2 ^ n : Nat).toFloat))
  let pi := 2 * Float.asin 1
  some (Float.floor (pi / (4 * θ))).toUInt64.toNat

end CQRV.Synthesis

end
