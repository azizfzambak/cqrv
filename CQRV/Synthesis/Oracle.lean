module

public import CQRV.Circuit.Schedule
public import CQRV.Synthesis.Network
public import CQRV.Synthesis.TempAnd

/-!
# CQRV.Synthesis.Oracle

Report §6.1.1, §6.1.2, §6.1.4, §6.3.1 (Eq. 5) — `synthesizeOracle : Network → Circuit`, the
straight-line full-ancilla schedule (DECISIONS.md 2026-10-23, Stage 5 decisions 2 and 3):

* only the cone of the output is synthesized; one fresh ancilla per AND node of the cone,
  computed by `TempLogicalAND` (4 T) in topological order;
* `Z` on the qubit holding P(x) — the ancilla of the last AND, or a data qubit when ĉ∧ = 0
  (§6.1.1: no phase qubit);
* every AND uncomputed in reverse order: by MBU (`UncomputeTempLogicalAND`, 0 T) in the
  default mode `mbu`, or by the adjoint of its compute block (`UncomputeTempLogicalANDCoherent`,
  4 T, no measurement) in mode `coherent` (PHASE2_SPEC.md §A.0.1, Stage 15a; the mode is the
  last, defaulted argument of `step` and `synthesizeOracle`, so `mbu` is the Phase 1 code path
  gate for gate).

NOT and XOR nodes cost no ancilla. A node's value is kept as an affine function `(lin, c)`
over *atoms* (input bits, AND results; atom = its home qubit): `lin` is a set of atoms, `c` a
constant (NOT flips it). Before an AND, its two operands are brought onto two qubits by CNOTs
onto an operand qubit (in-place XOR) and X gates (polarity); these are undone right after the
AND and replayed around its MBU. The register therefore holds the atoms whenever no AND is in
progress and the width stays `n + ĉ∧` (decision 2: XOR and `if` are implemented).
An AND whose operands are a constant or have the same linear part is folded by the exact
identities `1 ∧ v = v`, `0 ∧ v = 0`, `u ∧ u = u`, `u ∧ ¬u = 0` (no gate, no ancilla), so
`a ≤ ĉ∧` and `t ≤ 4ĉ∧` (Eq. 2 as a bound; DECISIONS.md 2026-10-23, Stage 5 interpretations).
Rejected (`unsupported_network`): a network with more than one output bit.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL

/-- Report §6.1.2 — an affine function over GF(2): the XOR of the atoms `lin` (sorted by
`Qubit.key`, no repeats), plus the constant `c`. -/
structure Aff where
  lin : List Qubit
  c : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Insert `x` before the first `y` with `le x y` (structural recursion: the kernel evaluates
it; `List.mergeSort` is well-founded and blocks `decide +kernel`, DECISIONS.md 2026-10-25,
Stage 8b). -/
def insertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

/-- Symmetric difference of two atom sets, sorted (stable insertion sort; the same list as the
former `mergeSort`). -/
def symDiff (a b : List Qubit) : List Qubit :=
  ((a.filter (!b.contains ·)) ++ (b.filter (!a.contains ·))).foldr
    (insertBy fun p q => p.key.1 < q.key.1 || (p.key.1 == q.key.1 && p.key.2 ≤ q.key.2)) []

namespace Oracle

/-- Raise a synthesis diagnostic. -/
def fail {α : Type} (msg : String) : Except Diagnostic α :=
  throw (Diagnostic.at .synthesis .unsupportedNetwork ⟨1, 1⟩ msg)

/-- Nodes in the cone of `out` (the nodes P(x) depends on). -/
def cone (N : Network) (out : Nat) : Array Bool :=
  (List.range N.nodes.size).reverse.foldl (fun mark k =>
    if !mark.getD k false then mark else
    match N.nodes[k]? with
    | some (.not i) => mark.set! i true
    | some (.and i j) | some (.xor i j) => (mark.set! i true).set! j true
    | _ => mark) ((Array.replicate N.nodes.size false).set! out true)

/-- CNOTs that put the XOR of the qubits `S` onto its first element (the pivot). -/
def gather (S : List Qubit) (p : Qubit) : List Gate :=
  (S.filter (· != p)).map fun s => .cnot s p

/-- Report §6.1.2 — bring two affine operands onto two distinct qubits `(pu, pv)`:
the preparation gates (CNOTs, then X for negative polarity) and the two qubits. -/
def prepare (u v : Aff) : Except Diagnostic (List Gate × Qubit × Qubit) := do
  let pu ← match u.lin with
    | p :: _ => pure p
    | [] => fail "internal: AND with a constant operand (folded by `fold`)"
  -- After `gather u.lin pu`, qubit `pu` holds lin(u); the others still hold their atoms.
  let Sv := if v.lin.contains pu then pu :: symDiff (u.lin.erase pu) (v.lin.erase pu)
            else v.lin
  let pv ← match Sv.filter (· != pu) with
    | p :: _ => pure p
    | [] => fail "internal: AND operands with the same linear part (folded by `fold`)"
  let xs := (if u.c then [Gate.x pu] else []) ++ (if v.c then [Gate.x pv] else [])
  return (gather u.lin pu ++ gather Sv pv ++ xs, pu, pv)

/-- Report §6.1.2 — exact identities for an AND whose operands are a constant or share their
linear part: `1 ∧ v = v`, `0 ∧ v = 0`, `u ∧ u = u`, `u ∧ ¬u = 0`; `none` otherwise. -/
def fold (u v : Aff) : Option Aff :=
  if u.lin.isEmpty then some (if u.c then v else ⟨[], false⟩)
  else if v.lin.isEmpty then some (if v.c then u else ⟨[], false⟩)
  else if u.lin == v.lin then some (if u.c == v.c then u else ⟨[], false⟩)
  else none

/-- Synthesis state: node values, the compute blocks and the uncompute blocks (in order of
the ANDs; uncompute runs them reversed; each block measures into bit 0 and is shifted to its
measurement-order bit when emitted), the next ancilla. -/
structure St where
  vals : Array (Option Aff)
  compute : Array (List Gate) := #[]
  uncompute : Array (List Gate) := #[]
  nextAnc : Nat := 0

/-- Report §6.1.2, §6.2.2 — one node of the cone. The uncompute block of a non-folded AND is
chosen by `mode` (PHASE2_SPEC.md §A.0.1): MBU, measuring into bit 0 (shifted to its
measurement-order bit when emitted), or the coherent adjoint (no bit). -/
def step (N : Network) (mark : Array Bool) (st : St) (k : Nat)
    (mode : UncomputeMode := .mbu) : Except Diagnostic St := do
  if !mark.getD k false then return { st with vals := st.vals.push none }
  let get (i : Nat) : Except Diagnostic Aff :=
    match st.vals.getD i none with
    | some a => pure a
    | none => fail "internal: operand outside the cone"
  match N.nodes[k]? with
  | some (.input i) => return { st with vals := st.vals.push (some ⟨[.data i], false⟩) }
  | some (.const b) => return { st with vals := st.vals.push (some ⟨[], b⟩) }
  | some (.not i) =>
    let a ← get i
    return { st with vals := st.vals.push (some { a with c := !a.c }) }
  | some (.xor i j) =>
    let a ← get i
    let b ← get j
    return { st with vals := st.vals.push (some ⟨symDiff a.lin b.lin, a.c ^^ b.c⟩) }
  | some (.and i j) =>
    let u ← get i
    let v ← get j
    if let some r := fold u v then return { st with vals := st.vals.push (some r) }
    let (pre, pu, pv) ← prepare u v
    let t := Qubit.anc st.nextAnc
    let cmp := pre ++ [.alloc t] ++ TempLogicalAND pu pv t ++ pre.reverse
    let unc := pre ++ (match mode with
      | .mbu => UncomputeTempLogicalAND pu pv t 0
      | .coherent => UncomputeTempLogicalANDCoherent pu pv t) ++ [.free t] ++ pre.reverse
    return { vals := st.vals.push (some ⟨[t], false⟩), compute := st.compute.push cmp,
             uncompute := st.uncompute.push unc, nextAnc := st.nextAnc + 1 }
  | none => fail "internal: node index out of range"

/-- Report §6.1.1, §6.1.4 Step 3 — the phase flip `(−1)^P(x)` for `P = (lin, c)`: `Z` on a
qubit holding lin (gathered by CNOTs and undone), sandwiched by `X` when `c = 1`
(`X Z X = −Z`). For a constant P the phase is global and no gate is emitted. -/
def phaseFlip (p : Aff) : List Gate :=
  match p.lin with
  | [] => []
  | q :: _ =>
    let pre := gather p.lin q ++ (if p.c then [Gate.x q] else [])
    pre ++ [.z q] ++ pre.reverse

end Oracle

open Oracle in
/-- Report §6.1.4, decision 2 — the phase oracle of a one-output network on `x[0..n)` with
`anc[0..ĉ∧)`: compute blocks, phase flip, uncompute blocks in reverse order. Classical bits
are numbered in measurement order: the `i`-th executed uncompute block measures into bit `i`
(DECISIONS.md, Stage 6b-1 review: the oracle is literally a shifted `Circuit.append` of its
pieces). `mode` (PHASE2_SPEC.md §A.0.1, Stage 15a): `mbu` (default) or `coherent`; in mode
`coherent` no block has a bit, so the shift is the identity on every block. -/
def synthesizeOracle (N : Network) (mode : UncomputeMode := .mbu) :
    Except Diagnostic Circuit := do
  let out ← match N.outputs with
    | [o] => pure o
    | os => fail s!"the oracle needs a one-bit predicate, the network has {os.length} outputs"
  let mark := cone N out
  let st ← (List.range N.nodes.size).foldlM (fun st k => step N mark st k mode) { vals := #[] }
  let p ← match st.vals.getD out none with
    | some p => pure p
    | none => fail "internal: output outside the cone"
  let unc := st.uncompute.toList.reverse.mapIdx fun i blk => blk.map (Gate.shiftBits i)
  let gates := st.compute.toList.flatten ++ phaseFlip p ++ unc.flatten
  return { nData := N.nInputs, gates }

/-- Report §6.1.4 (Table 3), §6.3.1 (Eq. 5) — the measured grade of a circuit:
(width, depth, T-count, peak ancilla) from the decision-4 scheduler. -/
def grade (c : Circuit) : Grade := c.grade

/-- PHASE2_SPEC.md §A.1 (Stage 17a) — the second record `GradeExt` of a circuit, from the same
decision-4 schedule as `grade` (stated in every certificate as `gradeExt_eq` from Stage 17b). -/
def gradeExt (c : Circuit) : GradeExt := c.gradeExt

end CQRV.Synthesis

end
