module

public import CQRV.Matching.Lgg

/-!
# CQRV.Matching.Library

Report §4.1.4 (φ_Grover), §4.2.4 (Algorithm 2: library matching with early exit) and §4.2.1
(Proposition 5.1). Stage 4 needs only the preconditions: a `LibEntry` is a name, a priority,
a precondition φ and its side conditions. The full `QPLP` record (§3.2) is built later in
`CQRV/Patterns` (DECISIONS.md 2026-10-23, Stage 4 decision 4).
-/

@[expose] public section

namespace CQRV.Matching

open Term

/-- Report §4.2.4 — a library entry: the precondition part of a QPLP. Lower `priority` is
scanned first (most specific first). -/
structure LibEntry where
  name : String
  priority : Nat
  precondition : Term
  sides : List SideCond
  deriving Repr, Inhabited

/-- Report §4.1.4 — `F₁`: the arity n. -/
def F₁ : MVar := .f 1 .nat
/-- Report §4.1.4 — `F₂`: the solution count M. -/
def F₂ : MVar := .f 2 .nat
/-- Report §4.3.3, Table 4 — `F₃`: the iteration bound. -/
def F₃ : MVar := .f 3 .nat
/-- Report §7.2.3 — `F₄`: the support set of the phase-kickback oracle (a whole AC list). -/
def F₄ : MVar := .f 4 .natSet

/-- Report §4.1.4 (decision 1) — φ_Grover =
`⟨Search, n: F₁, M: F₂, P: Bool^F₁ → Bool, iter: bounded(F₃),
  oracle: PhaseKickback(Multiplicative, F₄)⟩`. `F₁` occurs twice (consistency, step 4).
`U_P ∈ Poly(F₁)` is discharged by construction (ℰ is linear in the derivation, §7.2.2) and
appears as the rigid `PhaseKickback` field (decision 2). -/
def phiGrover : Term :=
  .const "sig"
    [.const "Search" [],
     .mvar F₁ [],
     .mvar F₂ [],
     .const "→" [.const "Bool^" [.mvar F₁ []], .const "Bool" []],
     .const "bounded" [.mvar F₃ []],
     .const "PhaseKickback" [.const "Multiplicative" [], .mvar F₄ []]]

/-- Report §4.1.4 — the Grover entry, side condition `F₂ ≥ 1`. -/
def groverEntry : LibEntry :=
  { name := "Grover", priority := 0, precondition := phiGrover,
    sides := [.ge (.mvar F₂ []) (.nat 1)] }

/-- Report §4.2.4 — the pattern library (Stage 4: φ_Grover only). -/
def library : List LibEntry := [groverEntry]

/-! ## Algorithm 2 -/

mutual
/-- Report §4.3.1 — the bindings Algorithm 1 can make before (and despite) a failure:
the same traversal as `matchAt`, but a failing position is skipped instead of aborting. The
lgg is taken against φ under these bindings, so that positions φ's metavariables match are
not counted as disagreements (DECISIONS.md 2026-10-23, Stage 4 interpretations). -/
def looseAt : Term → Term → Subst → Subst
  | .mvar m args, t, σ =>
    match assign [] m args t σ with
    | .ok σ' => σ'
    | .error _ => σ
  | .const c as, .const d bs, σ =>
    if c = d ∧ as.length = bs.length then looseList as bs σ else σ
  | .lam a, .lam b, σ => looseAt a b σ
  | .acSet as, .acSet bs, σ => if as.length = bs.length then looseList as bs σ else σ
  | _, _, σ => σ
/-- `looseAt` on argument lists. -/
def looseList : List Term → List Term → Subst → Subst
  | a :: as, b :: bs, σ => looseList as bs (looseAt a b σ)
  | _, _, σ => σ
end

/-- Report §4.2.4 — result of Algorithm 2: one match, or the nearest entry with its failure,
lgg and gap. Never a list (Proposition 5.1). -/
inductive LibResult where
  /-- step 2: a matcher of the entry's precondition, with the discharged side conditions -/
  | matched (e : LibEntry) (σ : Subst) (facts : List Discharged)
  /-- step 4: non-realizable-by-library; `gap = (σ₁, σ₂)` with `lgg σ₁ = σ_in`,
  `lgg σ₂ = φθ̂` -/
  | noMatch (nearest : LibEntry) (failure : MatchFailure) (lgg : Term) (gap : Subst × Subst)
      (dist : Nat × Nat)
  /-- the library is empty -/
  | empty

/-- Report §4.2.4, step 3 — the near-miss record of an entry whose match failed. -/
def nearMiss (e : LibEntry) (f : MatchFailure) (t : Term) : LibResult :=
  let φ₀ := normalize e.precondition
  let φ := φ₀.subst (looseAt φ₀ t [])
  let (g, σ₁, σ₂) := lgg t φ
  .noMatch e f g (σ₁, σ₂) (σ₁.length, σ₁.size + σ₂.size)

/-- Report §4.2.4, Algorithm 2 — scan by priority, early exit on the first match, otherwise
keep the entry with minimal `dist` (the first one on ties). `t` is the normalized σ_in. -/
def matchLibrary (lib : List LibEntry) (t : Term) : LibResult :=
  let sorted := lib.mergeSort fun a b => a.priority ≤ b.priority
  go sorted .empty
where
  /-- the linear scan; `best` is the nearest miss so far -/
  go : List LibEntry → LibResult → LibResult
    | [], best => best
    | e :: es, best =>
      match matchPrecondition (normalize e.precondition) e.sides t with
      | .ok (σ, ds) => .matched e σ ds
      | .error f =>
        let r := nearMiss e f t
        match r, best with
        | .noMatch _ _ _ _ d, .noMatch _ _ _ _ d' => go es (if distLt d d' then r else best)
        | _, _ => go es r

end CQRV.Matching

end
