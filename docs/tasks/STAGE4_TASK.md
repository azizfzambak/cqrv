# Stage 4 — Matcher, anti-unification, repair hints

Report sections: §4.1.1 (precondition language, normalization instead of E-unification),
§4.1.2 (Algorithm 1, revised steps: scope check, occurs check, consistency, normal-form
invariant), §4.1.3 (lgg), §4.1.4 (φ_Grover, side conditions after substitution), §4.2.1
(Proposition 5.1: match set empty or singleton), §4.2.4 (Algorithm 2), §4.3.1–4.3.3 (lgg with
reuse, `dist`, Table 4 five-field hint, the while near-miss).
Precondition: Stage 3 accepted (main = stage-3 = 2fca00b). `git switch -c stage-4 main`; one
commit; include this file (untracked) in it. Windows: `LEAN_NUM_THREADS=4`. Module system.
No Physlib import in `CQRV/Matching`.

## Reviewer decisions (record each in DECISIONS.md, dated, with "Rejected:")

1. **Metavariable names (the F₁ clash, Stage 3 open question).** The report uses F₁ for the
   arity in §4.1.4 and for the iteration bound in §4.3.3, and §4.3.1 even writes
   `iter = bounded(n)`. Fix: φ_Grover =
   `⟨Search, n: F₁, M: F₂, side F₂ ≥ 1, P: Bool^F₁, iter: bounded(F₃), oracle: PhaseKickback(…)⟩`
   — F₁ occurs twice (consistency check exercised), F₃ is the iteration bound (Table 4's
   "Expected: bounded(F₃)"). Fresh metavariables introduced by `lgg` live in a separate
   namespace `G₁, G₂, …` (§4.3.1: pattern metavariables are rigid for the lgg), so the while
   hint reads `iter = G₁` with gap `G₁ ↦ unbounded` / `G₁ ↦ bounded(F₃)`.
   Rejected: reusing F₃ for the lgg variable (same name, two meanings).
2. **"U_P ∈ Poly(F₁)"** is discharged by construction (ℰ is linear in the derivation, §7.2.2),
   not by a side condition: it appears in φ as the rigid `oracle: PhaseKickback` field.
   Rejected: a side condition `ĉ∧ ≤ p(F₁)` (polynomiality cannot be decided on one instance).
3. **Unknown M.** A signature with `solutionCount = none` encodes M as the rigid constant
   `unknown`; it fails against F₂ with a hint whose suggestion is "supply `--solutions M`".
   Rejected: binding F₂ to a placeholder.
4. **Where the library lives.** Stage 4 needs only preconditions: `CQRV/Matching/Library.lean`
   holds `structure LibEntry (name, priority, precondition φ, side conditions)` and the list with
   φ_Grover. The full `QPLP` record (§3.2) is built later in `CQRV/Patterns`.

## Tasks (`CQRV/Matching/`, doc-comment every declaration with its report §)

1. **`Term.lean`** — Σ-terms: rigid constants/constructors with argument lists, natural-number
   literals, bound variables (de Bruijn), λ-binders, metavariable applications `F x₁ … x_k`
   (only to bound variables), and one AC symbol (`acSet`, for sets such as `support`). A
   validity check `isMillerPattern φ` (args distinct bound variables; no metavariable over a
   proper sub-multiset of an AC list — §4.1.1). `SigmaIn.toTerm` (ground; field order fixed).
2. **`Normalize.lean`** — `normalize`: flatten nested `acSet`, sort arguments under a fixed total
   order, deduplicate where the symbol is a set. Applied to both φ and σ_in **before** matching
   (normal-form invariant, Algorithm 1 step 5); idempotence `#guard`/`example`.
3. **`Miller.lean`** — `millerMatch (φ : Term) (t : Term) : Except MatchFailure Subst`
   implementing Algorithm 1 exactly: (1) rigid decomposition; (2) flexible-rigid assignment with
   the **scope check**; (3) **occurs check**; (4) **consistency** for repeated metavariables
   (syntactic equality on normal forms); then side conditions evaluated **after** substitution by
   `decide` and returned as a list of discharged facts (for the certificate, §4.1.4).
   `MatchFailure` records the failing position (path) and reason (`clash`, `scope`, `occurs`,
   `inconsistent`, `sideCondition`). No backtracking, no `List` of results: the return type
   itself is "empty or singleton" (Proposition 5.1).
   **Soundness:** state `millerMatch_sound : millerMatch φ t = .ok σ → φ.subst σ = t` (on
   normal forms). Attempt it; if not closed in 3 build–fix rounds leave a tracked `sorry` with
   the sub-lemmas in SORRIES.md.
4. **`Lgg.lean`** — `lgg (t₁ t₂ : Term) : Term × Subst × Subst` with fresh `G_i`, **reusing**
   the same `G_i` for an identical disagreement pair (§4.3.1); pattern metavariables are rigid;
   `dist` = number of fresh metavariables, ties broken by total size of the two substitutions.
5. **`Library.lean`** — `LibEntry`, `library : List LibEntry` = [φ_Grover] (decision 1);
   `matchLibrary` = Algorithm 2: scan by priority, early exit on success, otherwise keep the
   entry with minimal `dist` and return `noMatch nearest lgg gap`.
6. **`Hint.lean`** — `renderHint` → the five fields of Table 4 (Location, Expected, Found,
   Explanation, Suggestion) as JSON (flat, like `Diagnostic`) and as text. Explanations/
   suggestions come from a lookup table keyed by the disagreement pattern: `unbounded` vs
   `bounded` (text of §4.3.3, suggestion with `max_iter`), `unknown` vs `F₂`
   (supply `--solutions M`), side condition `F₂ ≥ 1` false (no solutions — Grover not
   applicable), anything else → generic text naming the field. Linear in the lgg size.
7. **CLI** `cqr match <file> [--solutions M] [--text]`: runs check → extract → match; on success
   prints `{pattern, subst, side_conditions}` JSON, exit 0; on failure prints the hint, exit 1
   (diagnostic stage `match`, code `no_matching_pattern`). Extend `scripts/cli_smoke.sh`.

## Tests (`tests/CQRVTests/Matching.lean` + cli_smoke)

- `grover_pred_037` matches φ_Grover with σ(F₁) = 8, σ(F₂) = 32, σ(F₃) = 1, and the side condition
  discharged as `32 ≥ 1`.
- `search_while` fails; nearest = Grover; lgg has exactly one fresh `G₁` at `iter`; `dist = 1`;
  hint: Location `iter`, Expected `bounded(F₃)`, Found `unbounded`, suggestion mentions `max_iter`.
- A predicate with an `or` (M not computed) without `--solutions` fails with the "supply
  `--solutions M`" hint; with `--solutions 5` it matches with σ(F₂) = 5.
- Hand-built terms: scope-check failure (bound variable outside F's arguments); consistency
  failure (F₁ bound to 8 at `n` and 7 at `Bool^F₁`); side-condition failure (M = 0);
  lgg reuse (the same disagreement pair twice → the same `G_i`); normalization sorts
  `support = {7,0,3}` and is idempotent; `isMillerPattern` rejects `F x x` and `F (suc x)`.

## Acceptance

- `lake build` green; check scripts pass; any new `sorry` (only `millerMatch_sound` may get one)
  is in SORRIES.md.
- All tests pass; `cqr match` output is either one match or one hint — never a list.
- DECISIONS.md: decisions 1–4 and any interpretation you had to make.

## Stop conditions

- The five fields of Table 4 cannot be filled from the lgg gap without a hand-written rule per
  input → stop and report (the report claims they come from the gap plus a lookup table).
- Do not start Stage 5; do not build the `QPLP` record.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): whether `millerMatch_sound` closed, and any place where
the report's Algorithm 1 steps needed interpretation.
