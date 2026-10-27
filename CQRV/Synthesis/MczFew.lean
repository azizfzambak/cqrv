module

public import CQRV.Synthesis.Diffusion

/-!
# CQRV.Synthesis.MczFew

Report §3.1.4 / Table 3.3, §6.1.4 (v2's "multi-controlled Z decomposed with 2 clean ancilla",
v3 erratum 8), §6.2, §9.5.2 — Stage 12b: an n-qubit multi-controlled Z with **at most two clean
ancillae**, from the literature (DECISIONS.md 2026-10-26, Stage 12b; `docs/MCZ_NOTES.md`).
Status (`MczVariant.status`): `logDepth` — restoration proved (Stage 12c); certified per instance via `cqr certify --shape few:log` (Stage 12d): the restoration is proved for every
`n` given the classical KG fact (`mczFew_ancRestore_of_classical`, `CQRV.Grover.MczFew`), which a
certificate checks for its own `n`; `ladder` — classical step checked at n = 8, restoration not certified (`cqr synthesize … --shape
few:ladder` only).

Both variants solve Khattar–Gidney's "Problem 1" (arXiv:2407.17966, *Quantum* 9, 1752 (2025),
§5.1): an array `A[0..n]`, `A[0] = 1` (the clean ancilla), `A[i] = 0` (data qubit `x[i−1]`); an
operation `(t, x, y)` with `t < x < y`, `A[t] = 1`, `A[x] = A[y] = 0` sets `A[t] = 0`,
`A[x] = A[y] = 1`. It stores `x ∧ y` on `t`: on the clean ancilla (`t = 0`) by Gidney's AND
(`TempLogicalAND`, 4 T; uncomputed by MBU, 0 T); on a *conditionally clean* qubit (`t > 0`, in
|1⟩ whenever the qubits left of it hold 1) by `Toffoli(x, y; t); X t` (KG Theorem 5.1). The
product of the unmarked qubits is then `y₀ ∧ … ∧ y_{n−1}` (KG §3, §5.1), and the MCZ is a `CZ`
(two unmarked) or `Z` (one) on them, followed by the operations in reverse.

Each Toffoli on a conditionally clean target is Maslov's relative-phase Toffoli (`rtof`,
PRA 93, 022311 (2016), §B: 4 T, 3 CNOT, 2 H, the counts of his Fig. 3) instead of a 7-T Toffoli. It equals
`D · Toffoli` with `D` diagonal on its three qubits; the uncompute is the same gate list (it is
self-inverse), and everything between a compute and its uncompute restores those three qubits,
so `D` commutes with it and cancels (Maslov 2016, Proposition 1 and Corollary 2). This is an
argument, not a proof here; the proof is `CQRV.Grover.MczFew` (Stage 12c: `rtof_basis`,
`rtofPhase_pair`), and the harness (`tests/diff/mcz_diff.py`) checks the circuits independently.

* `MczVariant.ladder` — KG §5.2: the greedy schedule (rightmost marked `t` with two unmarked to
  its right; leftmost such pair). One clean ancilla, `n − 2` operations, linear depth.
* `MczVariant.logDepth` — KG §5.3: the doubling timesteps (`2^i` marked elements after step `i`)
  while a full timestep fits; the KG §5.2 greedy on the remaining array (the truncated last step,
  which the paper leaves to its figure); then the remaining unmarked qubits accumulated by the
  KG §5.2 greedy over a second clean ancilla `anc[1]`. At most two clean ancillae.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL Diffusion

/-- Report §6.1.4, Stage 12b decision 2 — the two implemented few-ancilla MCZ constructions. -/
inductive MczVariant where
  | ladder
  | logDepth
  deriving Repr, DecidableEq, Inhabited

/-- The CLI / JSON name of a variant (`--shape few:<name>`). -/
def MczVariant.name : MczVariant → String
  | .ladder => "ladder"
  | .logDepth => "log"

/-- The source of a variant, for the JSON `schedule` field. -/
def MczVariant.source : MczVariant → String
  | .ladder => "Khattar-Gidney 2024 §5.2 + Maslov 2016 RTOF"
  | .logDepth => "Khattar-Gidney 2024 §5.3 + Maslov 2016 RTOF"

/-- The status label of a few-ancilla MCZ in all output (Stage 12b decision 4; Stage 12d
decision 5: per variant). -/
def MczVariant.status : MczVariant → String
  | .ladder => "classical step checked at n = 8, restoration not certified"
  | .logDepth =>
    "restoration proved (Stage 12c); certified per instance via `cqr certify --shape few:log` (Stage 12d)"

namespace MczFew

/-- An operation `(t, x, y)` of KG Problem 1 (indices into the array). -/
abbrev Op := Nat × Nat × Nat

/-- Maslov 2016, §B — a relative-phase Toffoli on target `t` with the counts of his Fig. 3
(dashed): 4 T, 3 CNOT, 2 H. The figure's gate order is not legible in the text we could extract;
this is the standard Margolus-form list with those counts, and `tests/diff/mcz_diff.py` (0)
checks that it is `D · Toffoli`, `D = diag(1, 1, 1, 1, 1, −1, −i, i)`. Self-inverse as a gate
list (reverse and adjoint give the same list). -/
def rtof (a b t : Qubit) : List Gate :=
  [.h t, .t t, .cnot b t, .tdg t, .cnot a t, .t t, .cnot b t, .tdg t, .h t]

/-- Unmarked indices of `A` strictly above `t`, ascending. -/
def unmarkedAbove (A : List Bool) (t : Nat) : List Nat :=
  (List.range A.length).filter fun i => t < i && !A.getD i true

/-- KG §5.2 — one greedy choice: the rightmost marked `t` with two unmarked indices to its
right, and the leftmost such pair. -/
def greedyStep (A : List Bool) : Option Op := do
  let t ← (List.range A.length).reverse.find? fun t =>
    A.getD t false && (unmarkedAbove A t).length ≥ 2
  match unmarkedAbove A t with
  | x :: y :: _ => some (t, x, y)
  | _ => none

/-- KG Problem 1 — apply one operation: `A[t] = 0`, `A[x] = A[y] = 1`. -/
def applyOp (A : List Bool) (o : Op) : List Bool :=
  ((A.set o.1 false).set o.2.1 true).set o.2.2 true

/-- KG Problem 1 (§5.1) — the operation `o = (t, x, y)` is valid on `A`: `t < x < y`,
`A[t] = 1`, `A[x] = A[y] = 0` (Stage 13a; the test-file check of Stage 12b, moved here). -/
def validOp (A : List Bool) (o : Op) : Bool :=
  o.1 < o.2.1 && o.2.1 < o.2.2 && A.getD o.1 false && !A.getD o.2.1 true && !A.getD o.2.2 true

/-- KG Problem 1 — every operation of `ops` is valid on the array it is applied to. -/
def valid : List Bool → List Op → Bool
  | _, [] => true
  | A, o :: ops => validOp A o && valid (applyOp A o) ops

/-- KG §5.2 — the greedy schedule from `A` (at most `fuel` operations; each removes one
unmarked index, so `A.length` suffices). Returns the operations and the final array. -/
def greedy : Nat → List Bool → List Op × List Bool
  | 0, A => ([], A)
  | f + 1, A =>
    match greedyStep A with
    | none => ([], A)
    | some o => let r := greedy f (applyOp A o); (o :: r.1, r.2)

/-- KG §5.3 — the sub-steps `j = 0, …, i` of timestep `i` (`fuel = i − j`): with
`P = {p₀ < … }` the workspace and `Q = {q₀ < … }` the unmarked elements, apply `|P|/2`
operations `(p_{|P|−1−k}, q_{2k+1}, q_{2k+2})`; the last sub-step is `(p₀, q₀, q₁)`. -/
def substeps : Nat → List Nat → List Nat → List Op
  | 0, P, Q =>
    match P, Q with
    | p₀ :: _, q₀ :: q₁ :: _ => [(p₀, q₀, q₁)]
    | _, _ => []
  | f + 1, P, Q =>
    let m := P.length / 2
    let ops := (List.range m).map fun k =>
      (P.getD (P.length - 1 - k) 0, Q.getD (2 * k + 1) 0, Q.getD (2 * k + 2) 0)
    let used := ops.flatMap fun o => [o.2.1, o.2.2]
    let Q' := (Q.filter (!used.contains ·) ++ ops.map (·.1)).mergeSort (· ≤ ·)
    ops ++ substeps f (P.take (P.length - m)) Q'

/-- KG §5.3 — timestep `i`: from `0^i 1^{2^i} 0…` to `0^{i+1} 1^{2^{i+1}} 0…`, with
`P₀ = {i, …, i + 2^i − 1}` and `Q₀ = {i + 2^i, …, i + 2^{i+1}}` (`2^i` operations). -/
def timestep (i : Nat) : List Op :=
  substeps i ((List.range (2 ^ i)).map (i + ·)) ((List.range (2 ^ i + 1)).map (i + 2 ^ i + ·))

/-- KG §5.3 — every full timestep that fits in an array of `n + 1` elements
(`i + 2^{i+1} ≤ n`). -/
def doubling (n : Nat) : List Op :=
  ((List.range n).filter fun i => i + 2 ^ (i + 1) ≤ n).flatMap timestep

/-- One step of the compute phase on qubits: `(x, y, t, clean)`; `clean` iff `t` is the clean
ancilla of its array (index 0). -/
abbrev Step := Qubit × Qubit × Qubit × Bool

/-- Map Problem-1 operations over the array `qs` to steps. -/
def stepsOf (qs : List Qubit) (ops : List Op) : List Step :=
  ops.map fun o => (qs.getD o.2.1 default, qs.getD o.2.2 default, qs.getD o.1 default, o.1 == 0)

/-- The qubits of the unmarked indices of `A` over the array `qs`, in index order. -/
def unmarkedQubits (qs : List Qubit) (A : List Bool) : List Qubit :=
  ((List.range A.length).filter (!A.getD · true)).map (qs.getD · default)

/-- KG §5.2 over a fresh clean ancilla `c` and the system qubits `us`: steps and the qubits
left unmarked. Nothing to do for at most two qubits. -/
def accumulate (c : Qubit) (us : List Qubit) : List Step × List Qubit :=
  if us.length ≤ 2 then ([], us) else
  let qs := c :: us
  let (ops, A) := greedy qs.length (true :: List.replicate us.length false)
  (stepsOf qs ops, unmarkedQubits qs A)

/-- Report §6.1.4, Stage 12b — the compute steps of the MCZ on `x[0..n)` and the qubits that
carry the final `CZ` / `Z`: KG §5.2 over `anc[0]` (`ladder`), or KG §5.3 doubling over `anc[0]`,
the §5.2 greedy on the rest, and KG §5.2 over `anc[1]` on the unmarked qubits (`logDepth`). -/
def plan (n : Nat) : MczVariant → List Step × List Qubit
  | .ladder => accumulate (.anc 0) ((List.range n).map Qubit.data)
  | .logDepth =>
    let data := (List.range n).map Qubit.data
    if n ≤ 2 then ([], data) else
    let qs := Qubit.anc 0 :: data
    let d := doubling n
    let A₁ := d.foldl applyOp (true :: List.replicate n false)
    let (g, A₂) := greedy qs.length A₁
    let (s₂, us) := accumulate (.anc 1) (unmarkedQubits qs A₂)
    (stepsOf qs (d ++ g) ++ s₂, us)

/-- Compute gates of one step: `alloc` + Gidney's AND on a clean target; `rtof; X t` on a
conditionally clean one (KG Theorem 5.1). -/
def computeGates : Step → List Gate
  | (x, y, t, true) => [.alloc t] ++ TempLogicalAND x y t
  | (x, y, t, false) => rtof x y t ++ [.x t]

/-- Uncompute gates of one step, measuring into bit `m` when it is an AND (MBU). -/
def uncomputeGates (m : Nat) : Step → List Gate
  | (x, y, t, true) => UncomputeTempLogicalAND x y t m ++ [.free t]
  | (x, y, t, false) => [.x t] ++ rtof x y t

/-- The phase on the qubits left unmarked: `CZ` on two, `Z` on one. -/
def phase : List Qubit → List Gate
  | [a] => [.z a]
  | [a, b] => [.cz a b]
  | _ => []

/-- The uncompute phase: the steps in reverse; bits numbered in measurement order from `m`. -/
def uncomputeAll : Nat → List Step → List Gate
  | _, [] => []
  | m, s :: rest =>
    uncomputeGates m s ++ uncomputeAll (if s.2.2.2 then m + 1 else m) rest

end MczFew

open MczFew

/-- Report §6.1.4, §3.1.4 (Stage 12b decision 2) — the few-ancilla MCZ on `x[0..n)`,
`n ≥ 1`: the compute steps of `plan`, the phase, the steps in reverse. Status:
`MczVariant.status` (`logDepth` certified per instance, Stage 12d). -/
def mczFew (n : Nat) (v : MczVariant) : Except Diagnostic Circuit := do
  if n == 0 then fail .unsupportedNetwork "the MCZ needs at least one data qubit"
  let (steps, us) := plan n v
  if us.length == 0 || us.length > 2 then
    fail .unsupportedNetwork s!"few:{v.name}: {us.length} qubits left unmarked for n = {n}"
  return ⟨n, steps.flatMap computeGates ++ phase us ++ uncomputeAll 0 steps.reverse⟩

/-- Report §8.2 (Stage 12b decision 2) — `D_n = H^{⊗n} X^{⊗n} · mczFew n v · X^{⊗n} H^{⊗n}`,
as `diffusionWith`, with the few-ancilla MCZ (status: `MczVariant.status`). -/
def diffusionFew (n : Nat) (v : MczVariant) : Except Diagnostic Circuit := do
  let mcz ← mczFew n v
  let pre : Circuit := ⟨n, onAll .h n ++ onAll .x n⟩
  let post : Circuit := ⟨n, onAll .x n ++ onAll .h n⟩
  return (pre.append mcz).append post

/-- Report §8.2, §3.2.4 — one Grover iteration with the few-ancilla diffusion (as
`groverIteration`; status: `MczVariant.status`). -/
def groverIterationFew (P : Network) (n : Nat) (v : MczVariant) : Except Diagnostic Circuit := do
  if P.nInputs != n then
    fail .unsupportedNetwork s!"the predicate has {P.nInputs} inputs, the diffusion {n}"
  let oracle ← synthesizeOracle P
  let d ← diffusionFew n v
  return oracle.append d

/-- Report §3.2.4 — `H^{⊗n}` then `r` iterations with the few-ancilla diffusion (as
`groverCircuit`; status: `MczVariant.status`). With `.logDepth` it is the circuit of
`cqr certify --shape few:log` (Stage 12d). -/
def groverCircuitFew (P : Network) (n r : Nat) (v : MczVariant) : Except Diagnostic Circuit := do
  let it ← groverIterationFew P n v
  return (List.replicate r it).foldl Circuit.append ⟨n, onAll .h n⟩

end CQRV.Synthesis

end
