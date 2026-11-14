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

/-- Report §4.2.2 — the front-end stage that issued a diagnostic. `hypothesis`: a user-supplied
hypothesis (the ground solution count `--solutions`, §4.1.4) contradicts the extracted value;
ℰ itself never fails (§7.2.1; DECISIONS.md 2026-10-23). `matching`: the matcher found no library
pattern (§4.2.4, Algorithm 2; JSON name `match`). `synthesis`: the oracle synthesizer cannot
build the Boolean network or the circuit (§6.1.2; JSON name `synthesize`). `validation`: the
exhaustive front-end validation found an input on which the DSL evaluator and the network
disagree (§5.3.3; Stage 9b, decision 1; JSON name `validate`). `emit`: the QIR emitter has no
form for a gate (PHASE2_SPEC.md §A.1, Stage 17b: a classically controlled `cp`; JSON name
`emit`). -/
inductive Stage where
  | parse
  | surface
  | hypothesis
  | matching
  | synthesis
  | validation
  | emit
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.2.2–4.2.3, §4.2.4, §6.1.2, §5.3.3 — diagnostic codes of the front end, the
matcher, the synthesizer, the front-end validation and (Stage 17b) the QIR emitter. -/
inductive Code where
  | syntaxError
  | typeError
  | nonStructuralRecursion
  | unboundVariable
  | indexOutOfBounds
  | foldDiscipline
  | solutionCountMismatch
  | noSolutions
  | noMatchingPattern
  | unboundedLoop
  | unsupportedNetwork
  | infeasibleBudget
  | frontEndMismatch
  | unsupportedCombination
  | unsupportedInQir
  | budgetUnsatisfiable
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.2.3 — JSON name of a stage. -/
def Stage.name : Stage → String
  | .parse => "parse"
  | .surface => "surface"
  | .hypothesis => "hypothesis"
  | .matching => "match"
  | .synthesis => "synthesize"
  | .validation => "validate"
  | .emit => "emit"

/-- Report §4.2.3 — JSON name of a diagnostic code. -/
def Code.name : Code → String
  | .syntaxError => "syntax_error"
  | .typeError => "type_error"
  | .nonStructuralRecursion => "non_structural_recursion"
  | .unboundVariable => "unbound_variable"
  | .indexOutOfBounds => "index_out_of_bounds"
  | .foldDiscipline => "fold_discipline"
  | .solutionCountMismatch => "solution_count_mismatch"
  | .noSolutions => "no_solutions"
  | .noMatchingPattern => "no_matching_pattern"
  | .unboundedLoop => "unbounded_loop"
  | .unsupportedNetwork => "unsupported_network"
  | .infeasibleBudget => "infeasible_budget"
  | .frontEndMismatch => "front_end_mismatch"
  | .unsupportedCombination => "unsupported_combination"
  | .unsupportedInQir => "unsupported_in_qir"
  | .budgetUnsatisfiable => "budget_unsatisfiable"

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
