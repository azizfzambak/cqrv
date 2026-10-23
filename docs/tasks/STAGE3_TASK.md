# Stage 3 — DSL front end and the extractor ℰ

Report sections: §7.1 (design principles, BNF §7.1.4 with the fold form of `for`), §7.2 (ℰ as a
total compiler, signature §7.2.2, Grover signature §7.2.3, syntactic ĉ∧ via De Morgan), §7.3.2
(Table 3: construct → feature), §4.2.2 (two layers of acceptance), §4.2.3 (Tables 2–3),
§4.1.4 (ground values M, n in the signature).
Precondition: Stage 2 accepted (main = stage-2 incl. the SORRIES hash follow-up).
`git switch -c stage-3 main`; one commit; include this file (untracked) in it.
Windows: `LEAN_NUM_THREADS=4`; Python: `.venv/Scripts/python.exe -I`. Module system in every new
file. Do not import Physlib in `CQRV/DSL` (the front end is classical; keep it light).

## Pipeline shape (this is the point of the stage)

```
parse  : String        → Except Diagnostic Program      -- syntax errors
check  : Program       → Except Diagnostic TypedProgram -- Stage-1 surface checker
extract: TypedProgram  → SigmaIn                        -- ℰ: TOTAL, no Except, no partial
```
`extract` must be a plain total function (no `partial def`, no `Except`, no `panic!`); that is
the report's "ℰ is total on surface-typed derivations" (§7.2.1, §4.2.2). Ill-formed programs stop
at `check`; well-formed programs outside Cl♭ (`while`) pass `check` and are rejected later by
the matcher (Stage 4).

## Decisions made by the reviewer (record each in DECISIONS.md, dated, with "Rejected:")

1. **Surface syntax beyond the BNF.** §7.1.4's grammar has no `while`, no function calls and no
   recursion, but §4.2.2 needs a `while` that elaborates and an `allocate_tree` that is rejected.
   Add exactly two surface forms:
   - `loop <var> = <expr> while <expr> do <expr>` — a functional while (accumulator, condition,
     body; same fold discipline as `for`). Passes `check`; ℰ gives `iter = unbounded`.
   - calls `<name>(<expr>, …)` to top-level `fn`s. `check` builds the call graph and rejects any
     cycle (direct or mutual) with code `non_structural_recursion` (the grammar has no
     inductive types, so no recursion is structural yet). Non-recursive calls are inlined
     before extraction.
   Rejected: imperative `while` with assignment (the DSL has no assignment, §7.1.1).
2. **Loop index in `idx`.** `idx(<expr>, <nat>)` accepts a literal or a `for`-bound loop variable;
   support of `idx(x, i)` inside `for i in [0 ..< n]` is `{0, …, n−1}`.
3. **ĉ∧ and AND-depth rules** (Table 3; ĉ∧ is a *syntactic upper bound* c∧^D ≥ c∧P — never
   call it "minimum" in names, doc-comments or JSON):
   `and`: ĉ∧ = ĉ₁+ĉ₂+1, depth = max+1. `or`: same as `and` (De Morgan, one AND, never DNF).
   `not`, `xor`, literals, `idx`: no AND (linear over GF(2)); depth = max of subterms.
   `if c then a else b` (Bool): mux `b ⊕ (c ∧ (a ⊕ b))` → ĉ∧ = ĉc+ĉa+ĉb+1, depth = max+1
   (the report gives no AND count for `if`; this is the reviewer's rule, needed for the Stage 9
   predicate). `let x = e₁ in e₂`: ĉ∧ = ĉ(e₁)+ĉ(e₂) with uses of `x` free (shared), depth of `x` =
   depth of `e₁`. `for` with bound n: ĉ∧ = n·ĉ(body) (+ the init), depth = n·depth(body) (+init).
   `loop … while`: body counted once, `iter = unbounded`.
4. **Ancilla budget = ĉ∧** (one ancilla per AND, all held until the phase flip — the oracle
   schedule of §6.1.4; §7.2.3 "one per AND gate"). This is a sound upper bound
   (loose-but-proved, §9.5.2). The live-range release of §7.3.2's `let` row and the `for`
   "max(body)" case are *scheduling* refinements and belong to the Bennett scheduler (Stage 5).
   Rejected: live-range accounting in ℰ now (it would make the signature depend on a schedule).
5. **Solution count M.** §7.2.3 shows `solution_count >= 1`, but §4.1.4 and §8.4 need the ground
   value (M = 32 binds F₂). ℰ computes M **symbolically** when the predicate is a conjunction of
   literals on distinct indices (M = 2^(n − |literals|)); otherwise `solutionCount = none` and
   the user must supply it (CLI flag `--solutions M`; §5.1.3 / Chapter 8 treat M as a hypothesis
   of the certificate, never decided by enumeration). Rejected: brute-force enumeration in ℰ.
6. **Problem class.** A program of type `Vec Bool n → Bool` is extracted as `Search`; other
   result types as `Decision` for now. `Numeric` is declared but unused.
7. **`iter` field.** `iter : IterBound := .bounded k | .unbounded`; straight-line code is
   `.bounded 1`, `for` multiplies static bounds, any `loop … while` makes it `.unbounded`.
   (§4.3.3 uses this field; how φ_Grover constrains it is a Stage 4 question — note in open
   questions that §4.1.4 and §4.3.3 both use the name F₁ for different positions.)

## Tasks (`CQRV/DSL/`, doc-comment every declaration with its report §)

1. `Syntax.lean`: AST for §7.1.4 + the two additions; types `Bool | Vec Bool n | Nat n | Unit`;
   source positions on every node (for diagnostics).
2. `Parser.lean`: a parser for the concrete syntax of §7.1.4 (Lean's `Std.Internal.Parsec` or
   hand-written; `#check` what the pinned toolchain provides). Comments `--` to end of line.
3. `Diagnostic.lean`: `structure Diagnostic` with `stage` (`parse | surface`), `code`
   (`syntax_error`, `type_error`, `non_structural_recursion`, `unbound_variable`,
   `index_out_of_bounds`, `fold_discipline`), `message`, `line`, `col`; `toJson` via
   `Lean.Data.Json` (keep the format flat — it will move to LSP later, PLAN.md §0).
4. `Check.lean`: surface type checker (types; `idx` bounds; branches same type; the fold
   discipline of `for`/`loop`: the body may refer only to the loop variable, the accumulator and
   outer bindings; call-graph cycle check). Produces `TypedProgram`.
5. `Signature.lean`: `structure SigmaIn` with exactly the §7.2.3 content: problem class;
   `arity n`; `solutionCount : Option Nat`; `andComplexity` (ĉ∧); `andDepth`; `ancillaBudget`;
   oracle structure (`phaseKickback` with target `multiplicative` and `support : List Nat`
   sorted, deduplicated | `block` | `blackBox`); algebraic structure (`boolAlg | monoid | group
   | ring`); domain and codomain types; `iter`. `deriving Repr, DecidableEq`; `toJson`.
6. `Extract.lean`: `extract : TypedProgram → SigmaIn`, total, structurally recursive.
7. CLI (`Apps/cqr`): `cqr check <file>` (exit 0 / prints diagnostic JSON, exit 1) and
   `cqr extract <file> [--solutions M]` (prints `SigmaIn` JSON). Other subcommands unchanged.
8. Corpus `examples/`: `grover_pred_037.cqr` (verbatim §7.1.4), `search_while.cqr`
   (e.g. `loop found = false while not found do (idx(x,0) and idx(x,3)) or found` inside a
   `fn … (x: Vec Bool 8) -> Bool`), `allocate_tree.cqr`
   (`fn allocate_tree(depth: Nat 8) -> Bool { allocate_tree(depth) and allocate_tree(depth) }`).

## Tests (`tests/CQRVTests/DSL.lean`, `#guard` / `example … := by decide` or `native_decide`
only if `decide` times out — say which)

- `grover_pred_037` → Search, n = 8, M = some 32, ĉ∧ = 2, and_depth = 2, ancilla = 2,
  support = [0,3,7], BoolAlg, iter = bounded 1. (§7.2.2's table says "8, 2, 3" but its own text
  and §7.2.3 say and_depth = 2 — test 2 and list the table entry in open questions.)
- `search_while` passes `check` and extracts with `iter = unbounded`.
- `allocate_tree` fails `check` with `stage = surface`, `code = non_structural_recursion`.
- One `or` case (De Morgan: one AND), one `if` case (mux rule), one `for` case with `idx(x, i)`
  (support = full range, ĉ∧ = n·body).
- Parser round-trip on the three corpus files (parse succeeds; positions present).
- CLI smoke: `cqr extract examples/grover_pred_037.cqr` JSON contains `"and_complexity": 2`
  and no field named `*minimum*`; run from a script in `scripts/` that CI calls.

## Acceptance

- `lake build` green; no new `sorry` (none is expected in this stage); check scripts pass.
- All tests above pass; the three corpus files behave as in §4.2.3 Table 2.
- DECISIONS.md: the seven decisions above.

## Stop conditions

- The report contradicts one of the reviewer decisions above in a way not already noted → stop.
- Parser library missing from the pinned toolchain and a hand-written parser exceeds ~400 lines
  → stop and report before writing more.
- Do not start Stage 4 (no matcher, no patterns).

## Closing reply

CLAUDE.md format, under 40 lines; in (e) at least: the §7.2.2 "8, 2, 3" entry, the F₁ naming
clash, and anything in Table 3 you had to interpret beyond the decisions above.
