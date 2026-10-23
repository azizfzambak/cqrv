import CQRV.DSL.Basic

/-!
# `cqr` command-line interface

Report §9.1 (Phase I), CLAUDE.md layout `Apps/cqr/`. Stage 3 implements `check` and `extract`
(report §4.2.2, §7.2); the other subcommands exit with code 2 and name their stage.

* `cqr check <file>` — parse + surface check; exit 0, or print the diagnostic JSON and exit 1.
* `cqr extract <file> [--solutions M]` — print the `SigmaIn` JSON (exit 0), or the diagnostic
  JSON (exit 1). `--solutions M` supplies the ground solution count when ℰ cannot compute it
  (DECISIONS.md 2026-10-23, decision 5); a value that contradicts ℰ's is an error (exit 1).
-/

open CQRV.DSL

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    "  check <file>\n  extract <file> [--solutions M]\n" ++
    String.join ((subcommands.drop 2).map fun (c, _) => s!"  {c}\n")

/-- Report §4.2.2 — parse and surface-check a source file. -/
def frontEnd (path : String) : IO (Except Diagnostic TypedProgram) := do
  let src ← IO.FS.readFile path
  return parse src >>= check

/-- `cqr check <file>`. -/
def runCheck (path : String) : IO UInt32 := do
  match ← frontEnd path with
  | .ok _ => return 0
  | .error d => IO.println d.toJson.compress; return 1

/-- `cqr extract <file> [--solutions M]`. -/
def runExtract (path : String) (solutions : Option Nat) : IO UInt32 := do
  match ← frontEnd path with
  | .error d => IO.println d.toJson.compress; return 1
  | .ok tp =>
    let sig := extract tp
    match sig.solutionCount, solutions with
    | some m, some m' =>
      if m != m' then
        IO.eprintln s!"cqr extract: --solutions {m'} contradicts the solution count {m} \
          computed from the predicate"
        return 1
      IO.println sig.toJson.pretty
      return 0
    | _, _ =>
      IO.println { sig with solutionCount := sig.solutionCount <|> solutions }.toJson.pretty
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", file] => runCheck file
  | ["extract", file] => runExtract file none
  | ["extract", file, "--solutions", m] =>
    match m.toNat? with
    | some m => runExtract file (some m)
    | none => IO.eprintln s!"cqr extract: --solutions expects a natural number, got `{m}`"; return 2
  | cmd :: _ =>
    match subcommands.lookup cmd with
    | some stage =>
      if stage == 3 then IO.eprint usage; return 2
      IO.eprintln s!"cqr {cmd}: not implemented (Stage {stage})"
      return 2
    | none =>
      IO.eprint usage
      return 2
  | [] =>
    IO.eprint usage
    return 2
