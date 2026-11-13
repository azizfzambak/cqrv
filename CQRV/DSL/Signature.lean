module

public import Lean.Data.Json
public import CQRV.DSL.Syntax

/-!
# CQRV.DSL.Signature

Report §7.2.2 (Table 2, signature structure) and §7.2.3 (the Grover signature) — the ground
spec signature σ_in produced by ℰ, with the ground solution count of §4.1.4 and the iteration
field of §4.3.3. `andComplexity` is ĉ∧ = c∧^D, the *syntactic upper bound* on the
multiplicative complexity (§7.2.2), not the minimum.
-/

@[expose] public section

namespace CQRV.DSL

open Lean

/-- Report §7.2.2, Table 2 — problem class `Search ∥ Decision ∥ Numeric`; PHASE2_SPEC.md §A.5
(amendments before Stage 21, (3)) — `Count`, the counting (amplitude-estimation) problem of a
request `--problem count`: the extractor ℰ never produces it. -/
inductive ProblemClass where
  | search
  | decision
  | numeric
  | count
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.3 — target of a phase-kickback oracle (`target = Multiplicative`). -/
inductive OracleTarget where
  | multiplicative
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.2, Table 2 — oracle / access structure `Phase ∥ Block ∥ BlackBox`; `support`
is the sorted, duplicate-free set of input bit positions read by the predicate (§7.2.3). -/
inductive OracleStructure where
  | phaseKickback (target : OracleTarget) (support : List Nat)
  | block
  | blackBox
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.2, Table 2 — algebraic structure `Monoid ∥ Group ∥ Ring ∥ BoolAlg`. -/
inductive AlgStructure where
  | boolAlg
  | monoid
  | group
  | ring
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.3.3 — the iteration field: `bounded k` (straight-line code is `bounded 1`) or
`unbounded` (any `loop … while`). -/
inductive IterBound where
  | bounded (k : Nat)
  | unbounded
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.2–7.2.3, §4.1.4 — the ground spec signature σ_in. -/
structure SigmaIn where
  problemClass : ProblemClass
  /-- input arity n (number of input bits) -/
  arity : Nat
  /-- ground solution count M (§4.1.4); `none` when ℰ cannot compute it symbolically -/
  solutionCount : Option Nat
  /-- ĉ∧ = c∧^D, syntactic upper bound on the number of AND gates (§7.2.2) -/
  andComplexity : Nat
  /-- depth of the Boolean network in AND gates (§7.2.3) -/
  andDepth : Nat
  /-- one ancilla per AND gate (§7.2.3; DECISIONS.md 2026-10-23, decision 4) -/
  ancillaBudget : Nat
  oracle : OracleStructure
  algebra : AlgStructure
  /-- parameter types of the entry `fn` (their product is the domain) -/
  domain : List Ty
  codomain : Ty
  iter : IterBound
  /-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (3)) — the precision `m` (phase qubits)
  of a counting request; `none` for every signature ℰ produces -/
  precision : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (3)) — the problem of a request:
`search` (the default and the Phase 1 behaviour) or `count m` (`--problem count --precision m`). -/
inductive Problem where
  | search
  | count (m : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (3)) — the request's problem on a signature:
`search` is the identity; `count m` sets the class to `Count` and the precision to `m`, whatever
ℰ found (a program that is not a predicate then fails at the `P` field of the Count entry with a
hint: the class is the request's, the type is the program's). -/
def SigmaIn.withProblem : Problem → SigmaIn → SigmaIn
  | .search, s => s
  | .count m, s => { s with problemClass := .count, precision := some m }

/-- Report §7.2.3 — JSON name of a problem class. -/
def ProblemClass.name : ProblemClass → String
  | .search => "Search"
  | .decision => "Decision"
  | .numeric => "Numeric"
  | .count => "Count"

/-- Report §7.2.3 — JSON name of an algebraic structure. -/
def AlgStructure.name : AlgStructure → String
  | .boolAlg => "BoolAlg"
  | .monoid => "Monoid"
  | .group => "Group"
  | .ring => "Ring"

/-- Report §7.2.3 — JSON of the oracle structure. -/
def OracleStructure.toJson : OracleStructure → Json
  | .phaseKickback .multiplicative s =>
    Json.mkObj [("kind", "PhaseKickback"), ("target", "Multiplicative"),
                ("support", Json.arr (s.map (fun (k : Nat) => (k : Json))).toArray)]
  | .block => Json.mkObj [("kind", "Block")]
  | .blackBox => Json.mkObj [("kind", "BlackBox")]

/-- Report §4.3.3 — JSON of the iteration field. -/
def IterBound.toJson : IterBound → Json
  | .bounded k => Json.mkObj [("kind", "bounded"), ("bound", k)]
  | .unbounded => Json.mkObj [("kind", "unbounded")]

/-- Report §7.2.3 — the signature as JSON, with the field names of §7.2.3. -/
def SigmaIn.toJson (s : SigmaIn) : Json :=
  let base : List (String × Json) :=
    [("problem_class", s.problemClass.name),
     ("arity", s.arity),
     ("solution_count", match s.solutionCount with | some m => (m : Json) | none => Json.null),
     ("and_complexity", s.andComplexity),
     ("and_depth", s.andDepth),
     ("ancilla_budget", s.ancillaBudget),
     ("oracle_structure", s.oracle.toJson),
     ("algebraic_structure", s.algebra.name),
     ("domain", " × ".intercalate (s.domain.map Ty.render)),
     ("codomain", s.codomain.render),
     ("iter", s.iter.toJson)]
  -- Stage 21a1: the precision only when the request gave one, so the search JSON is unchanged
  Json.mkObj (base ++ match s.precision with | some m => [("precision", (m : Json))] | none => [])

end CQRV.DSL

end
