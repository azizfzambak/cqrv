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

/-- Report §7.2.2, Table 2 — problem class `Search ∥ Decision ∥ Numeric`. -/
inductive ProblemClass where
  | search
  | decision
  | numeric
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
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.3 — JSON name of a problem class. -/
def ProblemClass.name : ProblemClass → String
  | .search => "Search"
  | .decision => "Decision"
  | .numeric => "Numeric"

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
  Json.mkObj
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

end CQRV.DSL

end
