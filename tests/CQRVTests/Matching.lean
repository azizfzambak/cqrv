module

import CQRV.DSL.Basic
import CQRV.Matching.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Matching.Basic

/-!
# Tests for `CQRV.Matching` (report §4.1.1–4.1.4, §4.2.4, §4.3.1–4.3.3)

The corpus files of `examples/` go through parse → check → ℰ → `SigmaIn.toTerm` → `normalize`
→ Algorithm 2; hand-built terms exercise each step of Algorithm 1, the lgg reuse rule and the
normal form.
-/

namespace CQRV.Tests.Matching

open CQRV.DSL CQRV.Matching CQRV.Matching.Term

/-- §7.1.4 / §4.1.4. -/
def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
/-- §4.3.3. -/
def whileSrc : String := include_str "../../examples/search_while.cqr"
/-- decision 3: an `or` predicate, M not computed by ℰ. -/
def orSrc : String := include_str "../../examples/search_or.cqr"

/-- Front end + ℰ + `--solutions` (as in `cqr match`), as a normalized term. -/
def sigTerm (src : String) (solutions : Option Nat := none) : Option Term :=
  match extract <$> (parse src >>= check) with
  | .ok s => some (normalize { s with solutionCount := s.solutionCount <|> solutions }.toTerm)
  | .error _ => none

/-- Algorithm 2 on a source. -/
def run (src : String) (solutions : Option Nat := none) : Option LibResult :=
  (sigTerm src solutions).map (matchLibrary library)

/-- The substitution of a match, as `(name, rendered body)` pairs sorted by metavariable. -/
def substOf : Option LibResult → Option (List (String × String))
  | some (.matched _ σ _) =>
    some ((σ.mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt).map fun (m, b) =>
      (m.name, b.body.render))
  | _ => none

/-- The discharged side conditions of a match, rendered. -/
def factsOf : Option LibResult → Option (List String)
  | some (.matched _ _ ds) => some (ds.map Discharged.render)
  | _ => none

/-- The hints of a near miss, with the source term. -/
def hintsOf (src : String) (solutions : Option Nat := none) : List Hint :=
  match sigTerm src solutions with
  | some t => renderHints t (matchLibrary library t)
  | none => []

/-- (nearest pattern, number of fresh metavariables of the lgg, dist) of a near miss. -/
def missOf : Option LibResult → Option (String × List String × Nat)
  | some (.noMatch e _ _ (σ₁, _) d) => some (e.name, σ₁.map (·.1.name), d.1)
  | _ => none

/-! ## The library is in the Miller fragment (Proposition 5.1 hypothesis) -/

#guard library.all fun e => e.precondition.isMillerPattern
#guard library.all fun e => normalize e.precondition == e.precondition

/-! ## §4.1.4 — `grover_pred_037` matches φ_Grover -/

#guard substOf (run groverSrc) ==
  some [("F₁", "8"), ("F₂", "32"), ("F₃", "1"), ("F₄", "{0, 3, 7}")]
#guard factsOf (run groverSrc) == some ["32 ≥ 1"]

-- Soundness on the instance: φσ = σ_in.
#guard match sigTerm groverSrc with
  | some t => match millerMatch phiGrover t with
    | .ok σ => phiGrover.subst σ == t
    | .error _ => false
  | none => false

/-! ## §4.3.3 — `search_while` is a near miss of Grover -/

-- With M supplied, exactly one fresh G₁, at `iter`; dist = 1.
#guard missOf (run whileSrc (some 64)) == some ("Grover", ["G₁"], 1)
#guard (hintsOf whileSrc (some 64)).map (fun h => (h.location, h.expected, h.found)) ==
  [("iter", "bounded(F₃) where F₃ is a natural number", "unbounded")]
#guard (hintsOf whileSrc (some 64)).all fun h => (h.suggestion.splitOn "max_iter").length > 1
-- The lgg itself: σ_in with G₁ at `iter`; the gap is G₁ ↦ unbounded / G₁ ↦ bounded(F₃).
#guard match run whileSrc (some 64) with
  | some (.noMatch _ _ g (σ₁, σ₂) _) =>
    g.render == "⟨class: Search, n: 8, M: 64, P: Bool^8 → Bool, iter: G₁, \
      oracle: PhaseKickback(Multiplicative, {0, 3})⟩" &&
    σ₁.map (fun (m, b) => (m.name, b.body.render)) == [("G₁", "unbounded")] &&
    σ₂.map (fun (m, b) => (m.name, b.body.render)) == [("G₁", "bounded(F₃)")]
  | _ => false
-- Without M: two gaps, M first (field order), then iter.
#guard (hintsOf whileSrc).map (·.location) == ["M", "iter"]

/-! ## θ̂ is deterministic (Stage 4 review) -/

/-- θ̂ of φ_Grover against a source, as `(name, rendered body)` pairs sorted by metavariable. -/
def thetaOf (src : String) (solutions : Option Nat := none) : Option (List (String × String)) :=
  (sigTerm src solutions).map fun t =>
    ((looseAt phiGrover t []).mergeSort fun a b => Term.MVar.cmp a.1 b.1 != .gt).map
      fun (m, b) => (m.name, b.body.render)

/-- The full `cqr match` output of a near miss (JSON line and text), as one string. -/
def hintOutput (src : String) (solutions : Option Nat := none) : String :=
  match sigTerm src solutions with
  | some t =>
    match matchLibrary library t with
    | r@(.noMatch _ _ _ _ d) =>
      let hs := renderHints t r
      String.join (hs.map fun h => (h.toJson d hs.length).compress) ++ hintsText hs d
    | _ => ""
  | none => ""

-- search_while: θ̂ binds F₁, F₂, F₄; the iter clash is skipped, so F₃ stays unbound (rigid).
#guard thetaOf whileSrc (some 64) == some [("F₁", "8"), ("F₂", "64"), ("F₄", "{0, 3}")]
-- The while hint is identical across two runs (two independent evaluations).
def whileRun₁ : String := hintOutput whileSrc (some 64)
def whileRun₂ : String := hintOutput (include_str "../../examples/search_while.cqr") (some 64)
#guard whileRun₁ != "" && whileRun₁ == whileRun₂
#guard hintOutput whileSrc == hintOutput whileSrc

/-! ## Decision 3 — unknown M -/

#guard missOf (run orSrc) == some ("Grover", ["G₁"], 1)
#guard (hintsOf orSrc).map (fun h => (h.location, h.found)) == [("M", "unknown")]
#guard (hintsOf orSrc).all fun h => (h.suggestion.splitOn "--solutions M").length > 1
#guard (substOf (run orSrc (some 5))).map (·.lookup "F₂") == some (some "5")

/-! ## Hand-built terms -/

/-- σ_in of a hand-built signature (normalized term). -/
def sigOf (n m : Nat) (support : List Nat) : Term :=
  let s : SigmaIn :=
    { problemClass := .search, arity := n, solutionCount := some m, andComplexity := 0,
      andDepth := 0, ancillaBudget := 0, oracle := .phaseKickback .multiplicative support,
      algebra := .boolAlg, domain := [.vec n], codomain := .bool, iter := .bounded 1 }
  normalize s.toTerm

-- Scope check (step 2): `λ. F₁` (no arguments) against `λ. #0`.
#guard match millerMatch (.lam (.mvar (.f 1 .any) [])) (.lam (.bvar 0)) with
  | .error f => f.reason == .scope && f.path == [0]
  | .ok _ => false
-- … while `λ. F₁ #0` against `λ. c(#0)` binds F₁ ↦ λ. c(#0).
#guard match millerMatch (.lam (.mvar (.f 1 .any) [.bvar 0])) (.lam (.const "c" [.bvar 0])) with
  | .ok [(_, b)] => b == ⟨1, .const "c" [.bvar 0]⟩
  | _ => false

-- Occurs check (step 3), on a non-ground t.
#guard match millerMatch (.mvar (.f 1 .any) []) (.const "g" [.mvar (.f 1 .any) []]) with
  | .error f => f.reason == .occurs
  | .ok _ => false

-- Consistency (step 4): F₁ bound to 8 at `n` and to 7 at `Bool^F₁`.
def inconsistentSig : Term :=
  match sigOf 8 32 [0] with
  | .const "sig" [c, n, m, _, it, o] =>
    .const "sig" [c, n, m, .const "→" [.const "Bool^" [.nat 7], .const "Bool" []], it, o]
  | t => t
#guard match millerMatch phiGrover inconsistentSig with
  | .error f => f.reason == .inconsistent && f.path == [3, 0, 0]
  | .ok _ => false
#guard (renderHints inconsistentSig (matchLibrary library inconsistentSig)).map
  (fun h => (h.location, h.expected, h.found)) == [("P (position 0.0)", "8", "7")]
-- θ̂ binds F₁ at its first consistent occurrence (`n` ↦ 8); the later 7 does not rebind it.
#guard (looseAt phiGrover inconsistentSig []).lookup F₁ == some ⟨0, .nat 8⟩

-- Side condition (§4.1.4): M = 0 binds F₂ ↦ 0, then `F₂ ≥ 1` fails.
#guard match matchPrecondition phiGrover groverEntry.sides (sigOf 8 0 [0]) with
  | .error f => f.reason == .sideCondition && f.path == [2]
  | .ok _ => false
#guard (renderHints (sigOf 8 0 [0]) (matchLibrary library (sigOf 8 0 [0]))).map
  (fun h => (h.location, h.expected, h.found, decide ((h.explanation.splitOn "not applicable").length > 1)))
  == [("M", "F₂ ≥ 1", "0", true)]

-- A sort clash (decision 3): `unknown` is not a `Nat`.
#guard match millerMatch (.mvar F₂ []) (.const "unknown" []) with
  | .error f => f.reason == .clash
  | .ok _ => false

-- lgg reuse (§4.3.1): the same disagreement pair twice → the same G₁.
#guard lgg (.const "f" [.nat 1, .nat 1, .nat 3]) (.const "f" [.nat 2, .nat 2, .nat 4]) ==
  (.const "f" [.mvar ⟨.G, 1, .any⟩ [], .mvar ⟨.G, 1, .any⟩ [], .mvar ⟨.G, 2, .any⟩ []],
   [(⟨.G, 1, .any⟩, ⟨0, .nat 1⟩), (⟨.G, 2, .any⟩, ⟨0, .nat 3⟩)],
   [(⟨.G, 1, .any⟩, ⟨0, .nat 2⟩), (⟨.G, 2, .any⟩, ⟨0, .nat 4⟩)])
#guard dist (.const "f" [.nat 1, .nat 1, .nat 3]) (.const "f" [.nat 2, .nat 2, .nat 4]) == (2, 4)
-- Pattern metavariables are rigid for the lgg: (8, F₁) is a disagreement.
#guard (lgg (.nat 8) (.mvar F₁ [])).2.1.length == 1

-- Normalization: `support = {7, 0, 3}` is sorted; nested sets flatten; duplicates go; idempotent.
def supp : Term := .acSet [.nat 7, .nat 0, .nat 3]
#guard normalize supp == .acSet [.nat 0, .nat 3, .nat 7]
#guard normalize (normalize supp) == normalize supp
#guard normalize (.acSet [.nat 3, .acSet [.nat 7, .nat 3], .nat 0]) == .acSet [.nat 0, .nat 3, .nat 7]

-- `isMillerPattern` rejects `F x x` and `F (suc x)`, accepts `F x y`.
#guard !(Term.lam (.lam (.mvar F₁ [.bvar 0, .bvar 0]))).isMillerPattern
#guard !(Term.lam (.mvar F₁ [.const "suc" [.bvar 0]])).isMillerPattern
#guard (Term.lam (.lam (.mvar F₁ [.bvar 1, .bvar 0]))).isMillerPattern
-- … and a metavariable inside an AC list, and an unbound argument.
#guard !(Term.acSet [.mvar F₁ [], .nat 5]).isMillerPattern
#guard !(Term.mvar F₁ [.bvar 0]).isMillerPattern

/-! ## `millerMatch_sound` is sorry-free: expected axioms `propext`, `Classical.choice`,
`Quot.sound` only (no `sorryAx`) -/

#print axioms millerMatch_sound

end CQRV.Tests.Matching
