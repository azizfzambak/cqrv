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

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (2)) — `F₅`: the precision m of a counting
request (phase qubits). -/
def F₅ : MVar := .f 5 .nat
/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (2)) — `F₆`: the solution count of a counting
request, of sort `any`: the counting certificate is universal in M (§A.4, amendments before
Stage 20b3 (3)), so the entry does not constrain it and `unknown` matches. -/
def F₆ : MVar := .f 6 .any

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (2)), report §4.1.4, §9.3.2 — φ_Count =
`⟨Count, n: F₁, M: F₆, P: Bool^F₁ → Bool, iter: bounded(F₃),
  oracle: PhaseKickback(Multiplicative, F₄), m: F₅⟩`: the Count term has seven fields; the
`iter` field is part of it, so the cross-entry iter hint of a `loop … while` applies. -/
def phiCount : Term :=
  .const "sig"
    [.const "Count" [],
     .mvar F₁ [],
     .mvar F₆ [],
     .const "→" [.const "Bool^" [.mvar F₁ []], .const "Bool" []],
     .const "bounded" [.mvar F₃ []],
     .const "PhaseKickback" [.const "Multiplicative" [], .mvar F₄ []],
     .mvar F₅ []]

/-- PHASE2_SPEC.md §A.5 (amendments before Stage 21, (2)) — the Count entry, priority 1, side
condition `F₅ ≥ 1` (at least one phase qubit). -/
def countEntry : LibEntry :=
  { name := "Count", priority := 1, precondition := phiCount,
    sides := [.ge (.mvar F₅ []) (.nat 1)] }

/-- Report §4.2.4, PHASE2_SPEC.md §A.5 — the pattern library: φ_Grover (Stage 4) and φ_Count
(Stage 21a1). The two entries never match the same term: they differ in the class constant and in
the argument count, so a search request's nearest miss stays Grover and a Count request's is
Count. -/
def library : List LibEntry := [groverEntry, countEntry]

/-! ## Algorithm 2 -/

mutual
/-- Report §4.3.1 — θ̂, the bindings Algorithm 1 can make before (and despite) a failure.
The lgg is taken against φθ̂, so that positions φ's metavariables match are not counted as
disagreements (DECISIONS.md 2026-10-23, Stage 4 interpretations (3); reviewer, Stage 4 review).

θ̂ is deterministic — a pure function of (φ, σ_in), computed as follows:
* **fixed traversal order**: the same order as `matchAt` — pre-order, arguments left to right
  (the field order of `sigFields` at the root), the body of a `lam` after the binder;
* **first consistent occurrence**: a metavariable is bound at its first occurrence in that
  order whose candidate passes steps 2–4 of `assign` (sort, scope, occurs, consistency with
  the bindings so far); later occurrences only re-check consistency and never rebind it;
* **clashes are skipped**: a rigid clash (different head, arity or literal) skips that whole
  subterm, and a failing `assign` leaves θ̂ unchanged; the scan continues with the next
  sibling. No backtracking, no choice point. -/
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

/-- Stage 21a1 (PHASE2_SPEC.md §A.5 amendment (2), corrected at the 21a1 stop) — the root shape
of a term: the head constant and the argument count of a constant application (`sig` with six or
seven fields); the class constant is not part of it. -/
def rootShape : Term → Option (String × Nat)
  | .const c as => some (c, as.length)
  | _ => none

/-- Report §4.2.4, Algorithm 2 — scan by priority, early exit on the first match, otherwise
keep the entry with minimal `dist` (the first one on ties). `t` is the normalized σ_in.

Stage 21a1 (PHASE2_SPEC.md §A.5 amendment (2), corrected at the 21a1 stop): the match is sought
over every entry; the nearest miss is taken among the entries whose precondition has the term's
root shape (`rootShape`: the same head constant and argument count, the class constant not
included), and among all entries when none has it. A root clash generalizes the whole term to one
metavariable (`dist = 1`), which would otherwise beat an entry with two gaps — the search request
`search_while` without `--solutions` got the nearest miss Count instead of Grover. With the
filter, every six-field term (Search or Decision) has Grover as its only candidate and a seven-field
Count term has Count, so every Stage 4 output is unchanged by construction. `nearMiss`,
`looseAt`, `distLt` and the printed `dist` are as they were. -/
def matchLibrary (lib : List LibEntry) (t : Term) : LibResult :=
  let sorted := lib.mergeSort fun a b => a.priority ≤ b.priority
  match sorted.findSome? fun e =>
      match matchPrecondition (normalize e.precondition) e.sides t with
      | .ok (σ, ds) => some (LibResult.matched e σ ds)
      | .error _ => none with
  | some r => r
  | none =>
    let same := sorted.filter fun e => rootShape (normalize e.precondition) == rootShape t
    go (if same.isEmpty then sorted else same) .empty
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
