import CQRV.DSL.Basic
import CQRV.Matching.Basic
import CQRV.Synthesis.Basic

/-!
# `cqr` command-line interface

Report §9.1 (Phase I), CLAUDE.md layout `Apps/cqr/`. Stage 3 implements `check` and `extract`
(report §4.2.2, §7.2), Stage 4 `match` (report §4.2.4, §4.3.2), Stage 5 `synthesize` (report
§6.1–6.2); the other subcommands exit with code 2 and name their stage.

* `cqr check <file>` — parse + surface check; exit 0, or print the diagnostic JSON and exit 1.
* `cqr extract <file> [--solutions M]` — print the `SigmaIn` JSON (exit 0), or the diagnostic
  JSON (exit 1). `--solutions M` supplies the ground solution count when ℰ cannot compute it
  (DECISIONS.md 2026-10-23, decision 5); a value that contradicts ℰ's is a diagnostic with
  stage `hypothesis`, code `solution_count_mismatch` (exit 1).
* `cqr match <file> [--solutions M] [--text]` — check → extract → Algorithm 2 against the
  library. One match: `{pattern, subst, side_conditions}` JSON, exit 0. Otherwise one repair
  hint (Table 4; stage `match`, code `no_matching_pattern`), exit 1; `--text` prints it as text.
* `cqr synthesize <file> [--amax k] [--json] [--layers]` — check → `toNetwork` → oracle
  synthesis (report §6.1.4; straight-line, or Bennett pebbling of an AND chain when `k < ĉ∧`,
  §6.1.3). Prints `{name, schedule, and_complexity, grade: {w, d, t, a}}` (exit 0); `--json`
  adds the IR (`circuit`, the flat format of `tests/diff/`) and prints one line; `--layers`
  appends the layer dump of the depth scheduler. Failures: diagnostic JSON, exit 1.
* `cqr synthesize --diffusion n [--amax k] [--json] [--layers]` — the Grover diffusion on `n`
  data qubits (report §8.2; Stage 5b): V1 (straight-line MCZ) without `--amax`, V2 (Bennett
  MCZ) with it. Prints `{name, n, schedule, grade}`; `--json`/`--layers` as above.
* `cqr synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]` — the
  Grover circuit `H^{⊗n}` then `r` iterations of oracle ⊕ diffusion V1 (report §3.2.4, §8).
  Default `r = r⋆ = ⌊π/(4θ)⌋`, `sin²θ = M/2ⁿ` (M from ℰ or `--solutions`). Prints the grades of
  the oracle, the diffusion, one iteration (measured, and the ⊕ of the two measured parts) and
  the full circuit, and `r_star`; `--json` adds `circuit` and `iteration_circuit` (one line).
-/

open CQRV CQRV.DSL CQRV.Matching CQRV.Synthesis

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    "  check <file>\n  extract <file> [--solutions M]\n  match <file> [--solutions M] [--text]\n" ++
    "  synthesize <file> [--amax k] [--json] [--layers]\n" ++
    "  synthesize --diffusion n [--amax k] [--json] [--layers]\n" ++
    "  synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]\n" ++
    String.join ((subcommands.drop 4).map fun (c, _) => s!"  {c}\n")

/-- Report §4.2.2 — parse and surface-check a source file; also returns the position of the
entry `fn` (the last one), used by the `--solutions` diagnostic. -/
def frontEnd (path : String) : IO (Except Diagnostic (TypedProgram × Pos)) := do
  let src ← IO.FS.readFile path
  return do
    let prog ← parse src
    let tp ← check prog
    return (tp, (prog.fns.getLast?.map (·.pos)).getD ⟨1, 1⟩)

/-- `cqr check <file>`. -/
def runCheck (path : String) : IO UInt32 := do
  match ← frontEnd path with
  | .ok _ => return 0
  | .error d => IO.println d.toJson.compress; return 1

/-- Report §4.1.4, §7.2 — front end + ℰ + the `--solutions` hypothesis: the signature, or the
diagnostic to print (a front-end failure or `solution_count_mismatch`). -/
def signature (path : String) (solutions : Option Nat) : IO (Except Diagnostic SigmaIn) := do
  match ← frontEnd path with
  | .error d => return .error d
  | .ok (tp, p) =>
    let sig := extract tp
    match sig.solutionCount, solutions with
    | some m, some m' =>
      if m != m' then
        let msg := s!"--solutions {m'} contradicts the solution count {m} computed from the \
          predicate `{tp.name}` (report §4.1.4)"
        return .error (Diagnostic.at .hypothesis .solutionCountMismatch p msg)
      return .ok sig
    | _, _ => return .ok { sig with solutionCount := sig.solutionCount <|> solutions }

/-- `cqr extract <file> [--solutions M]`. -/
def runExtract (path : String) (solutions : Option Nat) : IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig => IO.println sig.toJson.pretty; return 0

/-- `cqr match <file> [--solutions M] [--text]` — report §4.2.4 (Algorithm 2), §4.3.2. -/
def runMatch (path : String) (solutions : Option Nat) (text : Bool) : IO UInt32 := do
  match ← signature path solutions with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok sig =>
    let t := sig.toTerm.normalize
    match matchLibrary library t with
    | .matched e σ ds => IO.println (matchJson e σ ds).pretty; return 0
    | r@(.noMatch _ _ _ _ dist) =>
      let hs := renderHints t r
      if text then IO.print (hintsText hs dist)
      else
        match hs with
        | h :: _ => IO.println (h.toJson dist hs.length).compress
        | [] => IO.println "{}"
      return 1
    | .empty => IO.eprintln "cqr match: the pattern library is empty"; return 1

/-- Parse `[--solutions M] [--text]` in any order. -/
def matchFlags : List String → Option (Option Nat × Bool)
  | [] => some (none, false)
  | "--text" :: rest => (matchFlags rest).map fun (m, _) => (m, true)
  | "--solutions" :: m :: rest => do
    let k ← m.toNat?
    let (_, t) ← matchFlags rest
    return (some k, t)
  | _ => none

/-- Report §6.1.3–6.1.4 — the oracle circuit of a typed program under ancilla budget `aMax`
(`synthesizeWithBudget`: straight-line, or a Bennett pebbling of an AND chain). Returns the
schedule name and ĉ∧ of the network. -/
def synthesizeWith (tp : TypedProgram) (aMax : Option Nat) :
    Except Diagnostic (String × Nat × Circuit) := do
  let N ← toNetwork tp
  let (sched, c) ← synthesizeWithBudget N aMax
  return (sched, N.andCount, c)

/-- Report §3.1.1 — a grade as JSON `{w, d, t, a}`. -/
def gradeJson (g : Grade) : Lean.Json :=
  Lean.Json.mkObj [("w", g.w), ("d", g.d), ("t", g.t), ("a", g.a)]

/-- Print a result object: one compressed line with the IR fields `extra` under `--json`,
pretty otherwise; then the layer dump of `c` under `--layers`. -/
def printResult (base extra : List (String × Lean.Json)) (c : Circuit) (json layers : Bool) :
    IO Unit := do
  if json then IO.println (Lean.Json.mkObj (base ++ extra)).compress
  else IO.println (Lean.Json.mkObj base).pretty
  if layers then IO.println c.layerDump

/-- `cqr synthesize <file> [--amax k] [--json] [--layers]` — report §6.1.4, §6.3.1 (Eq. 5). -/
def runSynthesize (path : String) (aMax : Option Nat) (json layers : Bool) : IO UInt32 := do
  match ← frontEnd path with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _) =>
    match synthesizeWith tp aMax with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (sched, cand, c) =>
      let base := [("name", Lean.toJson tp.name), ("schedule", Lean.toJson sched),
                   ("and_complexity", Lean.toJson cand), ("grade", gradeJson c.grade)]
      printResult base [("circuit", c.toJson)] c json layers
      return 0

/-- `cqr synthesize --diffusion n [--amax k] [--json] [--layers]` — report §8.2, Stage 5b. -/
def runDiffusion (n : Nat) (aMax : Option Nat) (json layers : Bool) : IO UInt32 := do
  match diffusionWith n aMax with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok (sched, c) =>
    let base := [("name", Lean.toJson "diffusion"), ("n", Lean.toJson n),
                 ("schedule", Lean.toJson s!"mcz {sched}"), ("grade", gradeJson c.grade)]
    printResult base [("circuit", c.toJson)] c json layers
    return 0

/-- `cqr synthesize <file> --grover [--iterations r] [--solutions M] [--json] [--layers]` —
report §3.2.4, §8 (Stage 5b): oracle ⊕ diffusion V1, `r` (default r⋆) iterations. -/
def runGrover (path : String) (iters solutions : Option Nat) (json layers : Bool) :
    IO UInt32 := do
  match ← frontEnd path, ← signature path solutions with
  | .error d, _ | _, .error d => IO.println d.toJson.compress; return 1
  | .ok (tp, _), .ok sig =>
    let n := sig.arity
    let rs := sig.solutionCount.bind (rStar n)
    let some r := iters <|> rs
      | IO.eprintln s!"cqr synthesize --grover: give --iterations r, or a solution count M \
          with 1 ≤ M ≤ 2^{n} (from ℰ or --solutions M) to compute r⋆"
        return 2
    let res : Except Diagnostic (Circuit × Circuit × Circuit × Circuit) := do
      let N ← toNetwork tp
      return (← synthesizeOracle N, ← diffusion n none, ← groverIteration N n,
        ← groverCircuit N n r)
    match res with
    | .error d => IO.println d.toJson.compress; return 1
    | .ok (o, d, it, g) =>
      let base := [("name", Lean.toJson tp.name), ("n", Lean.toJson n),
        ("solutions", Lean.toJson sig.solutionCount), ("r_star", Lean.toJson rs),
        ("iterations", Lean.toJson r),
        ("grades", Lean.Json.mkObj [("oracle", gradeJson o.grade),
          ("diffusion", gradeJson d.grade), ("iteration", gradeJson it.grade),
          ("oracle_plus_diffusion", gradeJson (o.grade + d.grade)),
          ("circuit", gradeJson g.grade)])]
      printResult base [("circuit", g.toJson), ("iteration_circuit", it.toJson)] g json layers
      return 0

/-- Parse `[--iterations r] [--solutions M] [--json] [--layers]` (after `--grover`). -/
def groverFlags : List String → Option (Option Nat × Option Nat × Bool × Bool)
  | [] => some (none, none, false, false)
  | "--json" :: rest => (groverFlags rest).map fun (r, m, _, l) => (r, m, true, l)
  | "--layers" :: rest => (groverFlags rest).map fun (r, m, j, _) => (r, m, j, true)
  | "--iterations" :: r :: rest => do
    let r ← r.toNat?
    let (_, m, j, l) ← groverFlags rest
    return (some r, m, j, l)
  | "--solutions" :: m :: rest => do
    let m ← m.toNat?
    let (r, _, j, l) ← groverFlags rest
    return (r, some m, j, l)
  | _ => none

/-- Parse `[--amax k] [--json] [--layers]` in any order. -/
def synthFlags : List String → Option (Option Nat × Bool × Bool)
  | [] => some (none, false, false)
  | "--json" :: rest => (synthFlags rest).map fun (k, _, l) => (k, true, l)
  | "--layers" :: rest => (synthFlags rest).map fun (k, j, _) => (k, j, true)
  | "--amax" :: k :: rest => do
    let k ← k.toNat?
    let (_, j, l) ← synthFlags rest
    return (some k, j, l)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", file] => runCheck file
  | ["extract", file] => runExtract file none
  | ["extract", file, "--solutions", m] =>
    match m.toNat? with
    | some m => runExtract file (some m)
    | none => IO.eprintln s!"cqr extract: --solutions expects a natural number, got `{m}`"; return 2
  | "match" :: file :: flags =>
    match matchFlags flags with
    | some (m, t) => runMatch file m t
    | none => IO.eprint usage; return 2
  | "synthesize" :: "--diffusion" :: n :: flags =>
    match n.toNat?, synthFlags flags with
    | some n, some (k, j, l) => runDiffusion n k j l
    | _, _ => IO.eprint usage; return 2
  | "synthesize" :: file :: "--grover" :: flags =>
    match groverFlags flags with
    | some (r, m, j, l) => runGrover file r m j l
    | none => IO.eprint usage; return 2
  | "synthesize" :: file :: flags =>
    match synthFlags flags with
    | some (k, j, l) => runSynthesize file k j l
    | none => IO.eprint usage; return 2
  | cmd :: _ =>
    match subcommands.lookup cmd with
    | some stage =>
      if stage ≤ 5 then IO.eprint usage; return 2
      IO.eprintln s!"cqr {cmd}: not implemented (Stage {stage})"
      return 2
    | none =>
      IO.eprint usage
      return 2
  | [] =>
    IO.eprint usage
    return 2
