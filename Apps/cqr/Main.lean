/-!
# `cqr` command-line interface

Report §9.1 (Phase I), CLAUDE.md layout `Apps/cqr/`. Stage 0 stub: every subcommand
exits with code 2 and names the stage that will implement it.
-/

/-- Subcommands and the stage (docs/PLAN.md) that implements each. -/
def subcommands : List (String × Nat) :=
  [("check", 3), ("extract", 3), ("match", 4), ("synthesize", 5), ("certify", 8), ("emit", 8)]

def usage : String :=
  "usage: cqr <command> [args]\n\ncommands:\n" ++
    String.join (subcommands.map fun (c, _) => s!"  {c}\n")

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: _ =>
    match subcommands.lookup cmd with
    | some stage =>
      IO.eprintln s!"cqr {cmd}: not implemented (Stage {stage})"
      return 2
    | none =>
      IO.eprint usage
      return 2
  | [] =>
    IO.eprint usage
    return 2
