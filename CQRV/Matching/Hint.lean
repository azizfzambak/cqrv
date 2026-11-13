module

public import Lean.Data.Json
public import CQRV.Matching.Library
public import CQRV.DSL.Diagnostic

/-!
# CQRV.Matching.Hint

Report §4.3.2 (Table 4, repair-hint structure) and §4.3.3 (the while near-miss) — the lgg gap
of Algorithm 2 rendered as the five fields Location, Expected, Found, Explanation, Suggestion.
Location / Expected / Found come from the gap (the path of `Gᵢ` in the lgg, `σ₂(Gᵢ)`,
`σ₁(Gᵢ)`); Explanation / Suggestion come from a lookup table keyed by the disagreement pattern,
with templates filled from the input signature. One pass over the gap: linear in the lgg size.
-/

@[expose] public section

namespace CQRV.Matching

open Lean Term CQRV.DSL

/-- Report §4.3.2 — disagreement patterns of the lookup table. -/
inductive GapKind where
  /-- `unbounded` found where `bounded(F)` is expected (§4.3.3) -/
  | unboundedIter
  /-- the rigid constant `unknown` found where a `Nat`-sorted metavariable is expected
  (decision 3) -/
  | unknownCount
  /-- the side condition `F₂ ≥ 1` on the solution count is false -/
  | noSolutions
  /-- another side condition is false or not evaluable -/
  | sideCondition
  /-- anything else -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.3.2 — classify a gap `(found, expected)`. -/
def classifyGap : Term → Term → GapKind
  | .const "unbounded" [], .const "bounded" [_] => .unboundedIter
  | .const "unknown" [], .mvar m [] => if m.sort = .nat then .unknownCount else .other
  | _, _ => .other

/-- Report §4.3.2 — classify a failure without a gap (a side condition after substitution). -/
def classifyFailure (f : MatchFailure) (location : String) : GapKind :=
  match f.cond with
  | some (.ge _ (.nat 1)) => if location = "M" then .noSolutions else .sideCondition
  | some _ => .sideCondition
  | none => .other

/-- Report §4.3.2 — values of the input signature the suggestion templates substitute. -/
structure HintCtx where
  pattern : String
  location : String
  expected : String
  /-- input arity n, if the signature has one -/
  arity : Option Nat

/-- Report §4.3.3 — the Grover query bound ⌈π/4·√(2^n)⌉ quoted in the `max_iter` suggestion. -/
def groverQueries (n : Nat) : Nat :=
  (3.141592653589793 / 4 * Float.sqrt (Float.ofNat (2 ^ n))).ceil.toUInt64.toNat

/-- Report §4.3.2 — the lookup table: explanation and suggestion per disagreement pattern. -/
def hintText (k : GapKind) (c : HintCtx) : String × String :=
  match k with
  | .unboundedIter =>
    ("Unbounded iteration prevents static ancilla budget computation; the injective-after-\
      ancilla (reversible) embedding requires a statically known iteration count, so no \
      reversible circuit can be certified within a resource grade (report §4.3.3).",
     "Replace the data-dependent `loop … while …` with a bounded fold `for i in [0 ..< max_iter] \
      with … do …` where max_iter is a compile-time constant" ++
      match c.arity with
      | some n => s!"; for a search over Bool^{n}, max_iter ≥ ⌈π/4·√2^{n}⌉ = {groverQueries n} \
          preserves the Grover search semantics."
      | none => ".")
  | .unknownCount =>
    ("The solution count M is a hypothesis of the Grover certificate (it fixes the iteration \
      count); the extractor computes it only for a conjunction of literals on distinct bits, \
      which this predicate is not (report §4.1.4).",
     "Supply the number of satisfying assignments: `cqr match <file> --solutions M`.")
  | .noSolutions =>
    (s!"The side condition {c.expected} fails: the predicate has no satisfying assignment, so \
      there is nothing to search for — {c.pattern} is not applicable (report §4.1.4).",
     "Check the predicate and the `--solutions` value; a predicate with no solutions needs no \
      quantum search.")
  | .sideCondition =>
    (s!"The side condition {c.expected} of pattern {c.pattern} is false after substitution \
      (report §4.1.4).",
     s!"Change the program so that {c.expected} holds.")
  | .other =>
    (s!"Field `{c.location}` of the spec signature differs from what pattern {c.pattern} \
      requires; no instance of the pattern's metavariables bridges the difference \
      (report §4.3.1).",
     s!"Change the program so that field `{c.location}` has the form {c.expected}.")

/-- Report §4.3.2, Table 4 — a rendered repair hint (one per gap). -/
structure Hint where
  pattern : String
  location : String
  expected : String
  found : String
  explanation : String
  suggestion : String
  deriving Repr, Inhabited

/-- Report §4.3.2 — "Expected" with the sorts of its `Nat` metavariables named
(Table 4: "bounded(F₃) where F₃ is a natural number"). -/
def renderExpected (e : Term) : String :=
  let ms := (e.mvars.filter (·.sort = .nat)).eraseDups
  match ms with
  | [] => e.render
  | _ => e.render ++ " where " ++ ", ".intercalate (ms.map (·.name)) ++
      (if ms.length = 1 then " is a natural number" else " are natural numbers")

/-- Report §4.1.4 — the arity field `n` of a signature term. -/
def arityOf : Term → Option Nat
  | .const "sig" (_ :: .nat n :: _) => some n
  | _ => none

/-- Report §4.3.2 — render the hints of a near miss: one per fresh metavariable of the lgg
(in order `G₁, G₂, …`), or one for the failure itself when the gap is empty (a false side
condition, or a failure no generalization explains). `t` is σ_in. -/
def renderHints (t : Term) : LibResult → List Hint
  | .noMatch e f g (σ₁, σ₂) _ =>
    let paths := g.mvarPaths []
    let gaps := σ₁.filterMap fun (m, b₁) =>
      match σ₂.lookup m, paths.lookup m with
      | some b₂, some p => some (p, b₁.body, b₂.body)
      | _, _ => none
    let mk (k : GapKind) (loc exp found : String) : Hint :=
      let (ex, sg) := hintText k ⟨e.name, loc, exp, arityOf t⟩
      ⟨e.name, loc, exp, found, ex, sg⟩
    match gaps with
    | [] =>
      let loc := pathLabel t f.path
      let exp := match f.cond with
        | some c => c.render
        | none => renderExpected f.expected
      [mk (classifyFailure f loc) loc exp f.found.render]
    | _ => gaps.map fun (p, found, exp) =>
      mk (classifyGap found exp) (pathLabel t p) (renderExpected exp) found.render
  | _ => []

/-- Report §4.3.2 — the hint as flat JSON (like `Diagnostic`): stage `match`, code
`no_matching_pattern`, the five fields of Table 4, the nearest pattern, `dist`, the number
of gaps (the five fields describe the first gap; `text` lists all), and — Stage 21a2, PHASE2_SPEC
§A.5 amendment (4) — `non_match: proved`: by `matchLibrary_spec` (Proposition 5.1), a
non-`matched` result of Algorithm 2 on the ground term means that no library entry matches. -/
def Hint.toJson (h : Hint) (dist : Nat × Nat) (gapCount : Nat) : Json :=
  Json.mkObj
    [("stage", Stage.matching.name), ("code", Code.noMatchingPattern.name),
     ("message", "specification outside the realizable fragment Cl♭: no library pattern matches"),
     ("pattern", h.pattern), ("dist", dist.1), ("location", h.location),
     ("expected", h.expected), ("found", h.found), ("explanation", h.explanation),
     ("suggestion", h.suggestion), ("gap_count", gapCount), ("non_match", "proved")]

/-- Report §4.3.2–4.3.3 — the hint as text, in the order of Table 4. -/
def Hint.toText (h : Hint) : String :=
  s!"Location:    field `{h.location}` of the spec signature\n\
     Expected:    {h.expected}\n\
     Found:       {h.found}\n\
     Explanation: {h.explanation}\n\
     Suggestion:  {h.suggestion}\n"

/-- Report §4.3.3 — the full text report of a near miss. -/
def hintsText (hs : List Hint) (dist : Nat × Nat) : String :=
  let pat := (hs.head?.map (·.pattern)).getD "?"
  s!"Error: specification outside the realizable fragment Cl♭ (nearest pattern: {pat}, \
    dist {dist.1}).\n" ++ "\n".intercalate (hs.map Hint.toText)

/-! ## Match output (report §4.1.4: σ and the discharged side conditions) -/

/-- Report §4.1.4 — JSON value of a binding: a number, an array of numbers, or the rendered
term. -/
def Binding.toJson (b : Binding) : Json :=
  match b.arity, b.body with
  | 0, .nat n => n
  | 0, .acSet as =>
    if as.all (fun | .nat _ => true | _ => false) then
      Json.arr (as.filterMap (fun | .nat n => some (n : Json) | _ => none)).toArray
    else b.body.render
  | _, _ => b.body.render

/-- Report §4.1.4 — `{pattern, subst, side_conditions}`; bindings sorted by metavariable. -/
def matchJson (e : LibEntry) (σ : Subst) (ds : List Discharged) : Json :=
  let σs := σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt
  Json.mkObj
    [("pattern", e.name),
     ("subst", Json.mkObj (σs.map fun (m, b) => (m.name, b.toJson))),
     ("side_conditions", Json.arr (ds.map fun d =>
        Json.mkObj [("condition", d.cond.render), ("instance", d.render)]).toArray)]

end CQRV.Matching

end
