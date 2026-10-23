module

public import Lean.Data.Json
public import CQRV.DSL.Syntax

/-!
# CQRV.DSL.Diagnostic

Report §4.2.2 ("two layers of acceptance") and §4.2.3 Table 3 ("Extraction failure with
structural reason") — diagnostics of the parser and of the surface checker. The JSON format is
flat (one object, scalar fields) so that it can move to LSP later (docs/PLAN.md §0).
-/

@[expose] public section

namespace CQRV.DSL

open Lean

/-- Report §4.2.2 — the front-end stage that issued a diagnostic. `extract` is used only for
the ground solution count supplied with `--solutions` (§4.1.4; DECISIONS.md 2026-10-23). -/
inductive Stage where
  | parse
  | surface
  | extract
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.2.2–4.2.3 — diagnostic codes of the front end. -/
inductive Code where
  | syntaxError
  | typeError
  | nonStructuralRecursion
  | unboundVariable
  | indexOutOfBounds
  | foldDiscipline
  | solutionCountMismatch
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.2.3 — JSON name of a stage. -/
def Stage.name : Stage → String
  | .parse => "parse"
  | .surface => "surface"
  | .extract => "extract"

/-- Report §4.2.3 — JSON name of a diagnostic code. -/
def Code.name : Code → String
  | .syntaxError => "syntax_error"
  | .typeError => "type_error"
  | .nonStructuralRecursion => "non_structural_recursion"
  | .unboundVariable => "unbound_variable"
  | .indexOutOfBounds => "index_out_of_bounds"
  | .foldDiscipline => "fold_discipline"
  | .solutionCountMismatch => "solution_count_mismatch"

/-- Report §4.2.2–4.2.3 — a front-end diagnostic; `line`/`col` are 1-based. -/
structure Diagnostic where
  stage : Stage
  code : Code
  message : String
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.2.3 — build a diagnostic at a source position. -/
def Diagnostic.at (stage : Stage) (code : Code) (p : Pos) (message : String) : Diagnostic :=
  { stage, code, message, line := p.line, col := p.col }

/-- Report §4.2.3 — flat JSON object `{stage, code, message, line, col}`. -/
def Diagnostic.toJson (d : Diagnostic) : Json :=
  Json.mkObj
    [("stage", d.stage.name), ("code", d.code.name), ("message", d.message),
     ("line", d.line), ("col", d.col)]

end CQRV.DSL

end
