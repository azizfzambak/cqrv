# Design decisions

One dated entry per decision. Never delete entries; supersede them with a new entry that references the old one.

## 2026-10-21 — Planning decisions taken before Stage 0
Decision: (1) if Physlib / Lean-QuantumInfo does not build against the pinned Mathlib, start with an abstract `Channel` interface (named trust boundary) and revisit when it does; (2) the metric on specification outputs is a type parameter, MVP uses the discrete case (ε = 0); (3) SHA3-256 for certificate hashes is implemented in Lean (single-language TCB).
Why: see docs/PLAN.md §4.
Rejected: Python front end / external hashing tool (larger TCB, FFI trust gap).
Report §: 9.1.1, 2.1.2, 8.4.2, 9.5.3.

## 2026-10-21 — Toolchain and Mathlib pin (Stage 0)
Decision: `lean-toolchain` = `leanprover/lean4:v4.35.0`; Mathlib required in `lakefile.lean` at release tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (recorded in `lake-manifest.json`). Mathlib oleans come from `lake exe cache get`; Mathlib is never built from source.
Why: `v4.35.0` is the newest Mathlib release tag (`v4.36.0-rc1` is a pre-release); the toolchain is exactly the one that tag's own `lean-toolchain` names. It coincides with the latest stable Lean release (v4.35.0), so no override was needed. A release tag gives a reproducible, cache-backed pin (Table 9.5, dependency-drift row; §9.5.1 reference configuration).
Rejected: Mathlib `master` (moves daily, breaks reproducibility); `v4.36.0-rc1` (release candidate); `lakefile.toml` (the task prescribes `lakefile.lean`).
Report §: 9.1, 9.5.1, 9.5.3(i), Table 9.5.

## 2026-10-21 — Package layout: one Lake package, one module tree per component (decided by the reviewer)
Decision: a single Lake package `cqrv` with one top-level module tree per chapter-level component (`CQRV/{Grades,Realizability,Patterns,DSL,Matching,Circuit,Synthesis,Certify,Emit,Grover}`), root `CQRV.lean`, plus `lean_lib CQRVTests` (`tests/`) and `lean_exe cqr` (`Apps/cqr/Main.lean`). This is the reviewer's interpretation of §9.5.3(i) "one Lean 4 package per chapter-level component".
Why: component boundaries are kept as module trees; one manifest means one set of pins to maintain and audit.
Rejected: one Lake package per component — ten manifests to pin, no gain for the MVP.
Report §: 9.5.3(i).

## 2026-10-21 — CI design: pinned (blocking) + candidate (non-blocking, monthly)
Decision: `.github/workflows/ci.yml` has two jobs. `pinned` (push / pull_request, blocking): install elan → `lake exe cache get` → `lake build` (log tee'd) → `scripts/check_warnings.sh` → `scripts/check_sorries.sh` (+ `--self-test`) → `scripts/print_axioms.sh` → `pip install -r tests/diff/requirements.txt` → `python -I tests/diff/statevector.py --selftest`. `candidate` (monthly `schedule` + `workflow_dispatch`, `continue-on-error: true`): `scripts/candidate_build.sh` copies the tree to a temp directory, retargets the copy to the newest Mathlib release tag and that tag's toolchain, and runs the same build and checks; committed pins are never modified (CLAUDE.md rule 4). The sorry audit is file-level (count per file = open rows in SORRIES.md); the axiom printout is informational until Stage 8, when it becomes blocking on `sorryAx`/unlisted axioms. No Python or external hashing step besides the test-only simulator (2026-10-21 decision 3).
Why: implements Table 9.5 "Monthly: CI green on both pinned and candidate toolchains" without letting upstream drift block day-to-day work.
Rejected: candidate on every push (slow, non-actionable red builds); line-level sorry matching (line numbers drift); `leanprover/lean-action` (plain elan install keeps every step explicit and reproducible in Git Bash). Open: §9.5.3(ii) asks for candidate-toolchain checking "on each commit" for certificates — to be revisited at Stage 8 (see Stage 0 closing reply).
Report §: 9.5.1, 9.5.3(ii), Table 9.5.

## 2026-10-21 — Physlib / Lean-QuantumInfo: builds against the Mathlib pin, added
Decision: Lean-QuantumInfo is no longer a standalone project: `github.com/Timeroot/Lean-QuantumInfo` (last push 2026-09-10, toolchain v4.28.0) states in its README that it merged with PhysLean in March 2026 to form Physlib, and `github.com/leanprover-community/physlib` contains the `QuantumInfo/` tree (verified, not assumed). Tested commit: `leanprover-community/physlib@96a6bc5e3c50a2856c64a6c9951c0a1c23790b58` (master, 2026-10-21), whose own manifest pins Mathlib `v4.35.0` = `56a005855ea17e0b0958f73ec801ae140b0a1679`, i.e. our pin, with identical transitive dependency commits. In a throwaway clone (outside the repo), `lake build QuantumInfo` completed (3915 jobs, Mathlib from `lake exe cache get`, no Mathlib source build). Added to `lakefile.lean` as `require Physlib … @ "96a6bc5e…"` (manifest diff: only the Physlib entry; Mathlib unchanged). Scratch check (`.lake/scratch/PhyslibCheck.lean`, not committed) importing `QuantumInfo.Channels.CPTP` and `QuantumInfo.States.Mixed.MState` compiles; `#check` resolves `CPTPMap`, `CPTPMap.compose`, `MState`. Stage 2 can therefore build `Channel` on Physlib's `CPTPMap`/`MState`; the 2026-10-21 abstract-`Channel` fallback is not triggered.
Why: §9.1.1 reuses Physlib's density matrices, CPTP maps, partial trace and trace distance instead of rebuilding them.
Environment note: the first attempt on the reviewer's Windows machine (20 logical CPUs, 16 GB RAM, ~18 GB commit limit) failed with `failed to read file '…\Std\Internal\ForIn\Basic.ir.sig': Invalid argument` and similar read errors on toolchain/dependency `.olean`/`.ir` files — memory exhaustion from parallel Lean processes, not an incompatibility. Fix (attempt 1 of 3): `LEAN_NUM_THREADS=4 lake build …` succeeded with no source change. Use the same setting for Physlib builds on Windows.
Physlib's own sorries: Physlib compiles with `-Dwarn.sorry=false` and contains sorries (grep: ~14 occurrences in 5 `QuantumInfo` files, none in `Channels/CPTP.lean` or `States/Mixed/MState.lean`). They are outside SORRIES.md by design (`scripts/check_sorries.sh` never scans `.lake/`); any certificate that depends on one is caught by the Stage 8 axiom audit (`sorryAx`, blocking from Stage 8).
Rejected: abstract `Channel` interface as the starting point (unnecessary while Physlib builds); changing our Mathlib pin to fit Physlib (not needed, and forbidden by the task).
Report §: 9.1.1, 5.2.3, 9.5.1, Table 9.5.

## 2026-10-21 — Warning check scoped to our sources (reviewer decision)
Decision: `scripts/check_warnings.sh` fails only on warnings whose source path is `CQRV.lean` or under `CQRV/`, `Apps/`, `tests/` (relative or absolute, `\` normalized), excluding "declaration uses `sorry`" (either quoting). Warnings from dependencies (anything under `.lake/`, or with another package's relative paths) and warnings naming no file are ignored.
Why: CLAUDE.md rule 3 governs our code; dependency warnings (Mathlib, Physlib) are not actionable here and must not block CI or the choice of dependency.
Rejected: grep over the whole build log (rejects dependencies for their own lint warnings).
Report §: 9.5.1.

## 2026-10-21 — Physlib smoke test in CQRVTests (reviewer decision)
Decision: `tests/PhyslibSmoke.lean` (a root of `lean_lib CQRVTests`, imported by `tests/CQRVTests.lean`) imports `QuantumInfo.Channels.CPTP` and `QuantumInfo.States.Mixed.MState` and elaborates `MState (Fin 2)`, `CPTPMap (Fin 2) (Fin 4)` and `CPTPMap.compose`, so every CI build (ubuntu) compiles the pinned Physlib against the pinned Mathlib. Verified after adding it: `lake-manifest.json` pins mathlib `rev 56a005855ea17e0b0958f73ec801ae140b0a1679` (`inputRev v4.35.0`, `inherited: false`, i.e. our own require, not Physlib's) and Physlib `rev 96a6bc5e3c50a2856c64a6c9951c0a1c23790b58`; Physlib's own manifest requires the same Mathlib commit.
Why: the Windows-only verification of the Physlib entry above becomes a CI fact; Table 9.5 dependency-drift detection.
Rejected: a separate `workflow_dispatch` Physlib job (would not run on every commit). Cost: CI compiles the imported Physlib modules from source (~3300 jobs incl. replayed Mathlib) on each run until a Physlib artifact cache is used.
Report §: 9.1.1, Table 9.5.

## 2026-10-21 — Per-commit candidate-toolchain certificate checks deferred to Stage 8 (open item)
Decision: the `candidate` CI job stays monthly (`schedule`) + `workflow_dispatch`. Report §9.5.3(ii) requires every certificate to be kernel-checked on each commit on the pinned and on a candidate-upgrade toolchain; certificates do not exist before Stage 8, so the per-commit candidate check of certificates is deferred to Stage 8. Open item for Stage 8: add it alongside the blocking `sorryAx`/axiom audit.
Why: before Stage 8 there is nothing for §9.5.3(ii) to check per commit; Table 9.5's monthly gate is met by the current job.
Rejected: running the candidate build on every push now (cost without a certificate to check).
Report §: 9.5.3(ii), Table 9.5.

## 2026-10-23 — ⊕ is `AddCommMonoid Grade`; ⊗ is a named function (Stage 1)
Decision: sequential composition ⊕ is `Grade.seqComp`, installed as `instance : Add Grade := ⟨seqComp⟩` and bundled into `AddCommMonoid Grade` (`+` = ⊕, `0` = (0,0,0,0), `n • r` = n-fold ⊕ for `for` loops and the r⋆-fold Grover iteration). The parallel product ⊗ is `Grade.parComp`, not an instance, with named laws `parComp_comm`, `parComp_assoc`, `parComp_zero`. No notation is added. `nsmul := nsmulRec`: in the pinned Mathlib `AddMonoid.nsmul` has no default value (build error "Fields missing: `nsmul`"), so the field is set to Mathlib's repeated-addition `nsmulRec`, and `nsmul_zero`/`nsmul_succ` are closed by the structure's default `rfl` proofs; no hand-written `nsmul` and no `nsmul_*` lemmas.
Why: the additive class gives `n • r` for k-fold sequential composition; keeping `seqComp` keeps the report's name in the code; one `+` only avoids confusing ⊕ with ⊗.
Rejected: multiplicative `CommMonoid` (`r ^ k` for k-fold sequential composition reads wrong); a custom `⊕` notation (clashes with Lean's `Sum` notation `α ⊕ β`); making ⊗ a second instance (two monoid structures on one type).
Report §: 3.1.1, Table 3.1, 3.1.4.

## 2026-10-23 — `HardwareProfile` target is a type parameter (Stage 1)
Decision: `structure HardwareProfile (P : Type) [Preorder P] where map : Grade → P; mono : Monotone map`. `ρNISQ tgate tT : HardwareProfile Grade` with `map r = ⟨r.w, r.d * tgate, r.t * tT, r.a⟩` (durations in ns; no value of `tT` is fixed because the report gives none).
Why: §3.1.3 defines ρ : R → R_phys, a monotone map into a physical cost space that need not be `Grade` (e.g. surface-code overhead, factory count).
Rejected: `Grade → Grade` (PLAN.md wording) — it would hard-wire R_phys = R.
Report §: 3.1.3, 3.3.3, Table 3.5.

## 2026-10-23 — `CQRV/Grades` files use the Lean module system (Stage 1)
Decision: `CQRV/Grades/{Basic,Order,Hardware}.lean` start with `module`, use `public import`, and wrap their content in `@[expose] public section` (bodies exposed so that `rfl`/`decide` work in importers, e.g. the Table 3.3 tests).
Why: the pinned Mathlib is flagged `requiresModuleSystem`; a non-`module` file importing it makes Lake emit "imports `Mathlib…` from package `mathlib`, which is designed for use with the module system; consider adding `module`", a warning in our sources that `scripts/check_warnings.sh` would reject (CLAUDE.md rule 3). Files that import only our own modules (`CQRV.lean`, `tests/*.lean`) need no change.
Rejected: `allowNonModules := true` in `lakefile.lean` (silences the warning package-wide; rejected by the reviewer 2026-10-23).
Report §: 9.5.1.
Reviewer confirmed 2026-10-23: all later stages use the module system.

## 2026-10-23 — Classical inputs are encoded in the computational basis (Stage 2)
Decision: `encode (x : X) : MState X := MState.ofClassical (ProbDistribution.constant x)` — the Hilbert space of a classical input is indexed by the input type itself, and the encoding is fixed, not a parameter of `Realizes`.
Why: with this encoding the measure-and-re-encode step of Theorem 3.3a is exactly Physlib's `POVM.measureDiscard` (`measureDiscard_apply`: output `ofClassical (measure ρ)`, a mixture of `encode y`), so the measured interface needs no extra re-encoding channel.
Rejected: an encoding parameter `enc : X → MState dX` (the interface would need a separate re-encoding channel and a compatibility hypothesis between `enc` and the decoding POVM).
Report §: 2.1.2, 2.3.2.

## 2026-10-23 — "Within grade r" is fibre membership `grade ≤ r` (Stage 2)
Decision: `Realizes S dec Φ ε δ r` requires `Φ.grade ≤ r` (component-wise order of Stage 1).
Why: §3.1.2 reads a grade as a budget; the fibre over `r` contains every channel with grade `≤ r`, and budget relaxation (`Fibre.relax`) must preserve realization.
Rejected: `Φ.grade = r` (not closed under budget relaxation; Theorem 3.3a would only hold for the exact sum grade).
Report §: 2.3.1, 3.1.2.

## 2026-10-23 — Measured interface counted at grade 0 (Stage 2, open for the reviewer)
Decision: `measuredComp Φ dec_f Ψ` has grade `Φ.grade + Ψ.grade`; the intermediate measurement (`dec_f.measureDiscard`) and the basis re-encoding contribute nothing.
Why: Theorem 3.3a and Table 3 (§2.3.3) state the composite grade as `r ⊕ s`.
Rejected: charging the measurement a grade of its own now (no number for it in the report). Open question to the reviewer: the measurement has a physical cost (depth ≥ 1 layer, classical feed-forward); whether a later stage should add a measurement grade.
Report §: 2.3.2, 2.3.3, 3.1.1.
Reviewer decided 2026-10-23: the interface grade stays 0 (consistent with §2.3.3); revisit at Stage 9 for multi-stage pipelines.

## 2026-10-23 — Explicit δ-range hypotheses in Theorem 3.3a (Stage 2)
Decision: `measured_composition_exact` and `measured_composition` assume `0 ≤ δ_f`, `0 ≤ δ_g`, `δ_g ≤ 1`.
Why: the union-bound step `(1 − δ_f)(1 − δ_g) ≥ 1 − δ_f − δ_g` needs `δ_f δ_g ≥ 0`, and multiplying `Pr_f ≥ 1 − δ_f` by `1 − δ_g` needs `1 − δ_g ≥ 0`. The report leaves these ranges implicit (δ is a failure probability).
Rejected: putting the ranges into `Realizes` (Definition 2.2 does not restrict δ).
Report §: 2.3.2.

## 2026-10-23 — Non-expansiveness of S_g stated on dom S_g (Stage 2, reviewer decision)
Decision: hypothesis (ii) of Theorem 3.3a (general ε) is `∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y'`.
Why: the task's unrestricted form (`∀ y y' z'`) forces `dom S_g = Y` whenever `S_g` is non-empty, which is strictly stronger than §2.3.2's `L_g ≤ 1` (example: identity on `dom = [0,1]` has `L_g = 1` but fails it at `y = 2`). For a function on its domain the restricted form is exactly 1-Lipschitz. The proof only uses it at the exact intermediate `y₀` (`S_f x y₀`), which lies in `dom S_g` by domain compatibility; `0 ≤ ε_f` is then implied by `dist y y₀ ≤ ε_f`, so no extra hypothesis is needed.
Rejected: the task text's unrestricted form (changes the meaning of the report's hypothesis).
Report §: 2.3.2.

## 2026-10-23 — Diamond norm is a parameter of Theorem 3.3b until Phase III (Stage 2)
Decision: `coherent_composition` takes a channel distance `distD` (a family over channel types, since `Φ` and `Ψ` have different spaces) with the single hypothesis `2 · TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ distD Λ₁ Λ₂` for all inputs `ρ`. The ½ in `δ₀ + ½(η_f + η_g)` matches Physlib's `TrDistance = ½‖·‖₁`. The ideal channels `Φ₁`, `Ψ₁` carry no grade (grade 0 against budget 0); ε₀ is a general parameter ("ε is inherited from the ideal composite", §2.3.2).
Why: neither Mathlib nor Physlib has a diamond norm; the statement must still be type-correct and usable.
Rejected: defining the diamond norm now (Phase III scope, §9.3); adding it as an `axiom` (violates §9.5.1's no-new-axioms discipline).
Report §: 2.3.2, 9.3, 9.5.1.
Reviewer confirmed 2026-10-23: the `distD` family and the general ε₀ are accepted.

## 2026-10-23 — Theorem 3.1 stated in its concrete linear-algebra form (Stage 2)
Decision: `no_cloning_obstruction` states: for finite `d` with `2 ≤ Fintype.card d`, no `ℂ`-linear `C : (d → ℂ) → (d × d → ℂ)` satisfies `C ψ = ψ ⊗ ψ` for all `ψ`. The categorical form (no monoidal functor `Cl_det → U` preserving (Δ, !)) is deferred — a documented gap between the report's statement and the formalized one.
Why: Neither Mathlib nor Physlib has the category U; the report's "equivalently" form is the mathematical core and is stateable with Mathlib alone.
Rejected: building U in Mathlib's `CategoryTheory` now (out of Stage 2 scope).
Report §: 2.2.2.
Reviewer confirmed 2026-10-23: the categorical form stays deferred. The concrete form was proved in the Stage 2 review (`no_cloning_obstruction`, Mathlib only).

## 2026-10-23 — Test layout: `tests/CQRVTests/` picked up by a glob (Stage 2)
Decision: Lean tests live under `tests/CQRVTests/` (modules `CQRVTests.*`); `lean_lib CQRVTests` keeps `roots := #[`CQRVTests, `PhyslibSmoke]` and adds `globs := #[.one `CQRVTests, .one `PhyslibSmoke, .submodules `CQRVTests]`, so a new test file is built without editing the lakefile or `tests/CQRVTests.lean`. `tests/Grades.lean` moved to `tests/CQRVTests/Grades.lean`; `PhyslibSmoke` unchanged.
Why: listing each test root by hand (Stage 1) does not scale (Stage 1 review).
Rejected: importing every test module from `tests/CQRVTests.lean` (a second list to keep in sync).
Report §: 9.5.1.

## 2026-10-23 — `RealizesExact`: the discrete case needs no metric (Stage 2 review, reviewer decision)
Decision: `RealizesExact S dec Φ δ r := Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 − δ ≤ prob (dec.measure (Φ.chan (encode x))) (S x)` has no metric instance on `Y`; `realizes_zero_iff [MetricSpace Y] : Realizes S dec Φ 0 δ r ↔ RealizesExact S dec Φ δ r` (via `Spec.relax_zero`). `measured_composition_exact` is stated over `RealizesExact`, with no `MetricSpace` instances; the proof is unchanged apart from dropping the `relax_zero` rewrites. This implements the 2026-10-21 decision (metric is a type parameter; the MVP uses ε = 0).
Why: the pinned Mathlib has no `MetricSpace (Fin n)` or `MetricSpace Bool`, and the Grover output type is `Fin (2^n)` (Stage 7); the ε = 0 case never uses the metric.
Rejected: adding a `MetricSpace` instance on `Fin n` (an orphan instance on a Mathlib type, and a choice of metric the discrete case does not need).
Report §: 2.1.2, 2.3.2.

## 2026-10-23 — DSL surface syntax beyond the §7.1.4 BNF (Stage 3, reviewer decision 1)
Decision: exactly two surface forms are added to the grammar of §7.1.4: (a) `loop <var> = <expr> while <expr> do <expr>`, a functional while (accumulator, condition, body; same fold discipline as `for`), which passes the surface checker and is extracted with `iter = unbounded`; (b) calls `<name>(<expr>, …)` to top-level `fn`s. The checker builds the call graph and rejects any cycle, direct or mutual, with code `non_structural_recursion` (the grammar has no inductive types, so no recursion is structural yet); non-recursive calls are inlined (as `let`s of fresh names around the callee body) before extraction.
Why: §4.2.2 needs a `while` that elaborates and an `allocate_tree` that is rejected at the surface layer; the BNF has neither `while` nor calls.
Rejected: an imperative `while` with assignment (the DSL has no assignment, §7.1.1).
Report §: 7.1.1, 7.1.2, 7.1.4, 4.2.2, 4.2.3.

## 2026-10-23 — Loop index in `idx` (Stage 3, reviewer decision 2)
Decision: `idx(<expr>, <nat>)` accepts a literal or a `for`-bound loop variable; the support of `idx(x, i)` inside `for i in [0 ..< n]` is `{0, …, n−1}`. Any other variable as index is a `type_error`; a loop range beyond the vector length is `index_out_of_bounds`.
Why: a `for` over the bits of the input (§4.2.3 Table 2, row 1) must be able to read bit i.
Rejected: arbitrary `Nat`-typed index expressions (no static support set).
Report §: 7.1.4, 7.3.2.

## 2026-10-23 — ĉ∧ and AND-depth rules of ℰ (Stage 3, reviewer decision 3)
Decision: ĉ∧ is the syntactic upper bound c∧^D ≥ c∧P of §7.2.2 (never called "minimum" in names, doc-comments or JSON). `and`: ĉ∧ = ĉ₁+ĉ₂+1, depth = max+1. `or`: the same (De Morgan, one AND, never DNF). `not`, `xor`, literals, `idx`: no AND (linear over GF(2)); depth = max of subterms. `if c then a else b` (Bool): mux `b ⊕ (c ∧ (a ⊕ b))`, ĉ∧ = ĉc+ĉa+ĉb+1, depth = max+1. `let x = e₁ in e₂`: ĉ∧ = ĉ(e₁)+ĉ(e₂), uses of `x` free (shared), depth of `x` = depth of `e₁`. `for` with bound n: ĉ∧ = ĉ(init) + n·ĉ(body), depth = depth(init) + n·depth(body). `loop … while`: body counted once, `iter = unbounded`.
Why: Table 3 (§7.3.2) gives no AND count for `if`; the mux rule is needed for the Stage 9 predicate.
Rejected: computing the minimum multiplicative complexity (NP-hard, §7.2.2); DNF lowering of `or` (exponential).
Report §: 7.2.1, 7.2.2, 7.3.2, 9.5.2.

## 2026-10-23 — Ancilla budget = ĉ∧ (Stage 3, reviewer decision 4)
Decision: `ancillaBudget = andComplexity`: one ancilla per AND, all held until the phase flip (the oracle schedule of §6.1.4; §7.2.3 "one per AND gate"). A sound upper bound (loose-but-proved, §9.5.2). The live-range release of §7.3.2's `let` row and the `for` "max(body)" case are scheduling refinements for the Bennett scheduler (Stage 5).
Rejected: live-range accounting in ℰ now (it would make the signature depend on a schedule).
Report §: 6.1.4, 7.2.3, 7.3.2, 9.5.2.

## 2026-10-23 — Solution count M (Stage 3, reviewer decision 5)
Decision: ℰ computes M symbolically when the predicate is a conjunction of literals on distinct bits (M = 2^(n − |literals|)); otherwise `solutionCount = none` and the user supplies it with `cqr extract <file> --solutions M`. M is a hypothesis of the certificate (§5.1.3, Chapter 8), never decided by enumeration. Implementation detail: a `--solutions` value that contradicts a symbolically computed M is an error (exit 1).
Why: §7.2.3 shows `solution_count >= 1`, but §4.1.4 and §8.4 need the ground value (M = 32 binds F₂).
Rejected: brute-force enumeration in ℰ.
Report §: 4.1.4, 5.1.3, 7.2.3, 8.4.

## 2026-10-23 — Problem class (Stage 3, reviewer decision 6)
Decision: an entry `fn` of type `Vec Bool n → Bool` is extracted as `Search`; other types as `Decision`. `Numeric` is declared but unused.
Rejected: inferring `Numeric` now (the DSL has no arithmetic yet).
Report §: 7.2.2.

## 2026-10-23 — `iter` field (Stage 3, reviewer decision 7)
Decision: `iter : IterBound := .bounded k | .unbounded`. Straight-line code is `.bounded 1`; `for` multiplies static bounds (`for` over n with body bound k gives n·k); any `loop … while` makes it `.unbounded`. Interpretation (implementation): sibling sub-terms (operands, `let` parts, `for` init vs. body) combine by maximum, so that two straight-line operands stay `.bounded 1`.
Why: §4.3.3 matches on this field; how φ_Grover constrains it is a Stage 4 question.
Rejected: sum over siblings (straight-line `a and b` would become `.bounded 2`).
Report §: 4.3.3, 7.1.2.

## 2026-10-23 — Stage 3 front-end interpretations not fixed by the task (Stage 3)
Decision: (1) Parser: hand-written lexer and recursive descent (294 lines), total by fuel bounded by the input size; `Std.Internal.Parsec` exists in the pinned toolchain but is an internal API and its recursive grammars need `partial`. Precedence `or` < `xor` < `and` < `not` < atoms, binary operators left-associative (`b0 and b3 and b7` = `(b0 and b3) and b7`, the §7.2.3 comment); `let`/`if`/`for`/`loop` are atoms extending to the right. (2) `fn` takes a comma-separated parameter list (the BNF shows one parameter; calls `f(e₁, …)` need several). (3) A file is a list of `fn`s; the entry point is the last one. (4) Fold discipline (`fold_discipline`): the loop variable and accumulator must differ, and the body must return the accumulator type; references to anything else are scoping errors (`unbound_variable`) since the language is pure and lexically scoped. (5) Signature fields beyond the task: input arity = total input bits (`Nat n` takes ⌈log₂ n⌉ bits); `oracle = phaseKickback multiplicative support` when the codomain is `Bool`, else `blackBox`; `algebra = boolAlg` always (the DSL has only Boolean operations); a non-Bool `if` costs one AND per result bit. (6) `extract` is checked by `decide` on a hand-built typed term (it reduces in the kernel). (7) Diagnostics: 1-based `line`/`col`.
Why: needed to implement the task; none is stated by the report.
Rejected: `partial def` parser (not provable later); entry point by name `main` (no such convention in the report).
Report §: 7.1.4, 7.2.2, 7.3.2.

## 2026-10-23 — Report erratum: §7.2.2 Table 2 complexity tuple "8, 2, 3" (Stage 3 review, reviewer decision)
Decision: the Grover example entry of §7.2.2 Table 2, "8, 2, 3: 8-bit input, 2 ANDs, AND-depth 2", is a report erratum: the tuple (n, c∧, d) is (8, 2, 2). and_depth = 2, as in the entry's own description and in §7.2.3 (`(x0 & x3) & x7`, two AND levels). The code and tests use 2. To be fixed in report v3.
Why: the description and §7.2.3 agree on 2; the "3" contradicts both.
Rejected: and_depth = 3 (no AND network of `b0 and b3 and b7` has depth 3).
Report §: 7.2.2 (Table 2), 7.2.3.

## 2026-10-23 — `--solutions` mismatch is a diagnostic `solution_count_mismatch` (Stage 3 review, reviewer decision)
Decision: when ℰ computed M symbolically and `cqr extract --solutions M'` gives M' ≠ M, `cqr` prints a diagnostic JSON on stdout (same flat format as the front end) with code `solution_count_mismatch` and exits 1. Its stage is a new value `hypothesis`: ℰ is total (§7.2.1), so no diagnostic may say that extraction failed; the mismatch is between a user-supplied hypothesis (`--solutions`) and the extracted value; `line`/`col` are those of the entry `fn`. `--solutions M` equal to ℰ's M is accepted (exit 0).
Why: reviewer answer to the Stage 3 open question (6); every front-end failure is machine-readable in one format.
Rejected: a plain stderr message (the Stage 3 implementation); stage `extract` (reads as an extraction failure; first version of this entry, renamed by the reviewer in the Stage 3 review); stage `surface` (the program passed the surface check).
Report §: 4.1.4, 4.2.3, 7.2.1.

## 2026-10-23 — Metavariable names in φ_Grover; `G` namespace for lgg (Stage 4, reviewer decision 1)
Decision: φ_Grover = `⟨Search, n: F₁, M: F₂, P: Bool^F₁ → Bool, iter: bounded(F₃), oracle: PhaseKickback(Multiplicative, F₄)⟩`, side condition `F₂ ≥ 1` (`CQRV/Matching/Library.lean`). F₁ occurs twice (step 4, consistency, is exercised); F₃ is the iteration bound (Table 4 "Expected: bounded(F₃)"). Fresh lgg metavariables live in a separate namespace `G₁, G₂, …` (`MNs.G`); pattern metavariables are rigid for the lgg (§4.3.1). The while hint reads `iter = G₁` with gap `G₁ ↦ unbounded` / `G₁ ↦ bounded(F₃)`. Interpretation (implementation): the "(…)" of `PhaseKickback(…)` is the support set, bound by a fourth metavariable F₄ of sort `natSet` that ranges over the whole AC list (allowed by §4.1.1: never a proper sub-multiset); `grover_pred_037` gives F₄ ↦ {0, 3, 7}.
Rejected: reusing F₃ for the lgg variable (same name, two meanings); dropping the support from σ_in (the task puts `support` in an `acSet`).
Report §: 4.1.4, 4.3.1, 4.3.3, Table 4.

## 2026-10-23 — `U_P ∈ Poly(F₁)` discharged by construction (Stage 4, reviewer decision 2)
Decision: polynomiality of the oracle is not a side condition; it is the rigid `PhaseKickback(Multiplicative, …)` field of φ_Grover, justified by ℰ being linear in the derivation (§7.2.2).
Rejected: a side condition `ĉ∧ ≤ p(F₁)` (polynomiality cannot be decided on one instance).
Report §: 4.1.4, 7.2.2.

## 2026-10-23 — Unknown M is the rigid constant `unknown` (Stage 4, reviewer decision 3)
Decision: `SigmaIn.toTerm` encodes `solutionCount = none` as `unknown`. Metavariables carry a sort (`MSort.nat | natSet | any`, §4.1.1 Table 1 "metavariables over sorts", §4.1.4 "F₁ and F₂ … ranging over natural numbers"); step 2 of Algorithm 1 checks it (`MSort.admits`), and a value outside the sort is a `clash`. So `unknown` fails against F₂; the lgg gap `(unknown, F₂)` is keyed in the hint table to the suggestion "supply `--solutions M`".
Rejected: binding F₂ to a placeholder; letting F₂ bind `unknown` and failing in the side condition (F₂ would not range over naturals).
Report §: 4.1.1, 4.1.4.

## 2026-10-23 — The Stage 4 library holds preconditions only (Stage 4, reviewer decision 4)
Decision: `CQRV/Matching/Library.lean` has `structure LibEntry (name, priority, precondition, sides)` and `library = [groverEntry]`. Lower `priority` is scanned first (Algorithm 2 "most specific first"). The `QPLP` record (§3.2) is built later in `CQRV/Patterns`.
Rejected: building `QPLP` now (Stage 5+ scope).
Report §: 3.2, 4.2.4.

## 2026-10-23 — Stage 4 interpretations of §4.1–4.3 not fixed by the task (Stage 4)
Decision:
(1) σ_in as a term: `sig(class, n, M, P, iter, oracle)` with P = `→(dom, cod)`, `Vec Bool n` ↦ `Bool^(n)`, several parameters ↦ `×(τ₁, …)`, iter ↦ `bounded(k)` / `unbounded`, support ↦ `acSet`. ĉ∧, AND-depth, ancilla budget and algebra are not in the term (they feed the grade, Chapter 3; no precondition constrains them yet).
(2) No metavariable inside an `acSet` in a pattern (`isMillerPattern`): an element metavariable in a sorted list is already AC matching (finitary). A metavariable may stand for a whole AC list. With this, positional matching of normalized `acSet`s is exact.
(3) The lgg used for `dist` and the hint is `lgg σ_in (φθ̂)`, where θ̂ are the bindings Algorithm 1 can make despite the failure (`looseAt`: same traversal, failing positions skipped). Taken literally against φ with rigid metavariables, every metavariable position would disagree: `dist(search_while, φ_Grover)` would be 4 (n/P, M, iter, support), contradicting §4.3.1's example and the task's `dist = 1`. With θ̂, metavariables left unbound (F₃ in `bounded(F₃)`) stay rigid, as §4.3.1 requires.
(4) A failure with an empty gap (a false side condition after a structural match) is rendered from the failure itself: Location = field of the condition's first metavariable in φ, Expected = the condition (`F₂ ≥ 1`), Found = its substituted value.
(5) Several gaps: the text output lists one Table-4 block per `Gᵢ`; the JSON stays flat (like `Diagnostic`) and gives the first gap in field order plus `gap_count` (search_while without `--solutions` has 2: M, iter).
(6) The lgg under binders applies a fresh G to the bound variables free in either side (pattern lgg); AC lists of equal length are generalized positionally (normal forms), unequal ones as a whole.
(7) `Term` is nested (`List Term`); the `DecidableEq` deriving handler does not apply in the pinned toolchain, so equality is a structural `Term.beq` with `eq_of_beq`/`beq_refl` proofs.
(8) The matcher's diagnostic stage is the new `Stage.matching` (JSON name `match`) with code `no_matching_pattern` in `CQRV/DSL/Diagnostic.lean`.
(9) `millerMatch_sound` is proved without a normal-form hypothesis (`φσ = t` syntactically); normalization is what makes this matching modulo AC.
Why: needed to implement the task; the report leaves these open.
Rejected: (3) the literal lgg against φ (gives dist 4 and a gap at every metavariable); (5) a JSON list of hints (the output must be one hint, never a list).
Report §: 4.1.1, 4.1.2, 4.1.3, 4.1.4, 4.2.4, 4.3.1, 4.3.2.

## 2026-10-23 — θ̂ is deterministic; the matching term is a projection of SigmaIn (Stage 4 review, reviewer decisions)
Decision: (1) The lgg against φθ̂ (Stage 4 interpretations (3)) is accepted. θ̂ (`looseAt`, `CQRV/Matching/Library.lean`) is a pure function of (φ, σ_in): fixed traversal order (that of `matchAt`: pre-order, arguments left to right, i.e. `sigFields` order at the root); a metavariable is bound at its first consistent occurrence (the first candidate that passes steps 2–4 of `assign`; it is never rebound); clashes are skipped (a rigid clash skips the subterm, a failing `assign` leaves θ̂ unchanged), with no backtracking. Documented in the doc-comment of `looseAt`; tests: θ̂ of `search_while` = {F₁ ↦ 8, F₂ ↦ 64, F₄ ↦ {0, 3}} with F₃ unbound, first-occurrence binding F₁ ↦ 8 on the inconsistent signature, and the while hint (JSON + text) identical across two runs. (2) The sort check in step 2 is accepted. (3) F₄ ranging over the whole support set is confirmed. (4) The matching term is a library-chosen projection of `SigmaIn`; fields are added to it when a pattern first constrains them; ĉ∧/depth/ancilla still feed the grade. (5), (7) of the Stage 4 interpretations are accepted.
Why: reviewer answers to the Stage 4 open questions.
Rejected: a θ̂ that depends on search order or backtracking (the hint would not be reproducible); putting every `SigmaIn` field into the term now (unconstrained fields would need wildcard metavariables in every pattern).
Report §: 4.1.1, 4.1.4, 4.3.1, 4.3.2, 3.1.

## 2026-10-23 — Synthesis input is a Boolean network built by `toNetwork` (Stage 5, reviewer decision 1)
Decision: `CQRV/Synthesis/Network.lean`: `Network = {nInputs, nodes : Array Node, outputs}` with `Node = input | const | not | and | xor` (topological order) and `toNetwork : TypedProgram → Except Diagnostic Network`, structurally recursive on `TExpr` like ℰ: `or` by De Morgan `¬(¬a ∧ ¬b)`, `if` by the Stage 3 mux `b ⊕ (c ∧ (a ⊕ b))` per result bit, `let` shared, `for` unrolled, inputs laid out from bit 0 in parameter order (as ℰ), a `Nat m` value little-endian. `loop … while` has no finite network: diagnostic stage `synthesis` (JSON `synthesize`), code `unbounded_loop`. Test: AND count = ĉ∧ of ℰ on grover_pred_037, search_or, and_chain_8 and five inline programs (`for`, `if` on Bool and on `Vec Bool 3`, calls + `xor`, `let`).
Why: `SigmaIn` carries counts only; the network is the structure the synthesizer needs. The return type is `Except` (the task writes `TypedProgram → Network`) because of `loop … while`.
Rejected: re-parsing the source in the synthesizer; DNF for `or`.
Report §: 6.1.2, 7.2.2, 7.3.2.

## 2026-10-23 — Scope of the oracle synthesizer; XOR and `if` implemented (Stage 5, reviewer decision 2)
Decision: `synthesizeOracle : Network → Except Diagnostic Circuit` synthesizes the cone of the single output: one fresh ancilla per AND, `TempLogicalAND` in topological order, `Z` on the qubit holding P(x) (last AND ancilla, or a data qubit when ĉ∧ = 0), MBU in reverse order. NOT and XOR cost no qubit: a node value is an affine form over atoms (input bits, AND results); before an AND its operands are brought onto two qubits by CNOTs onto an operand qubit (in-place XOR) and X for negative polarity, undone right after, and replayed around its MBU. Width stays n + ĉ∧, so XOR and `if` are implemented (the harness checks 30 xor/`if` predicates). A negative output literal gets `X Z X` (= −Z, exact). Rejected with `unsupported_network`: more than one output bit.
Why: in-place XOR keeps the width of Eq. 5, which is the condition decision 2 sets.
Rejected: an extra qubit per XOR (changes Eq. 5); deferring XOR/`if` to Stage 9 (not needed).
Report §: 6.1.1, 6.1.2, 6.1.4, 6.3.1.

## 2026-10-23 — Bennett pebbling only for AND chains; minimal forward placements (Stage 5, reviewer decision 3)
Decision: `pebbleChain (L aMax) : Except String (List Move)` (`CQRV/Synthesis/Bennett.lean`). Moves as decided: `place i` / `remove i` only when node i−1 is pebbled (node 0: always); at most `aMax` pebbles; the last node is placed exactly once (Z right after it); start and end with no pebble. Among valid schedules it returns one with the fewest forward placements (executed T = 4 × placements), found by a 0-1 BFS over the 2^(L+1) states (L ≤ 16) with a fixed move order, so the result is deterministic. Infeasible budget → error (`cqr synthesize --amax k`: diagnostic `infeasible_budget`), never a circuit. `--amax k` below the straight-line ancilla count is accepted only when `Bennett.chainOf` recognizes the network as a chain of positive literals; otherwise `unsupported_network`. Measured quantities: "rounds" = the largest number of placements of any single node; depth = decision-4 depth of `chainCircuit` (lowest free ancilla index per placement); depth multiplier = depth / depth of the a_max = L schedule.
Why: decision 3; minimal placements is the quantity the T column of Table 2 bounds.
Rejected: a closed-form recursive Bennett strategy (not minimal in T); pebbling general networks.
Report §: 6.1.3, Eq. 3, Table 2.

## 2026-10-23 — Depth scheduler (Stage 5, reviewer decision 4)
Decision: `CQRV/Circuit/Schedule.lean`: ASAP in program order; a gate occupies every qubit it touches (for `ifBit`, the qubits of the controlled gate); an `ifBit c` gate is placed after the measurement writing c (two `ifBit` gates on the same bit may share a layer); `alloc`/`free` take no layer. `depth`, `tCount` (T and T†), `peakAncilla` (live ancillae in program order), `width` = data register + peak ancilla, `layerDump` (`cqr synthesize --layers`). Not tuned to any report number.
Rejected: tuning the scheduler to reproduce a number from the report.
Report §: 3.1.1, 6.1.4.

## 2026-10-23 — Report erratum: the §6.2.2 MBU listing has no reset (Stage 5)
Decision: `UncomputeTempLogicalAND a b t m = [H t, measure t → m, if m: CZ a b, if m: X t]`. The listing says the target is "restored to |0⟩ (reset)" but contains no reset; after the X-basis measurement the target is |m⟩. The added `if m: X t` is Clifford, 0 T, and shares the layer of the CZ. The compute phase is the listing gate for gate and is exact (|a, b, 0⟩ ↦ |a, b, a∧b⟩, no phase; harness self-test). The harness self-test shows that the listing without the fix fails the restoration check (`free` sees |1⟩ in the m = 1 branch).
Rejected: a `reset` instruction (not in the IR; the classically controlled X suffices).
Report §: 6.2.2, 6.2.4.

## 2026-10-23 — Report erratum: measured Grover oracle depth is 27, not 21 (Stage 5)
Decision: `cqr synthesize examples/grover_pred_037.cqr` measures (w, d, t, a) = (10, 27, 8, 2); w, t, a agree with Table 3. Table 3 counts depth 7 per compute phase, but in the §6.2.2 listing 11 of the 13 compute gates act on the target (H, T, 4 CNOT, T, 2 CNOT, H, S), so no schedule fits a compute phase in fewer than 11 layers. Layer dump (decision-4 scheduler): L1 `H anc0; H anc1`, L2 `T anc0; T anc1`, L3–L11 the rest of AND(x0, x3) → anc0 (T† x0 shares L6, T† x3 and T anc0 share L7), L12–L20 AND(anc0, x7) → anc1 (its H, T already in L1–L2), L21 `Z anc1`, L22–L24 MBU anc1 (`H; measure; if c1: CZ anc0 x7; if c1: X anc1`), L25–L27 MBU anc0. So 11 + 9 + 1 + 3 + 3 = 27. The test asserts 27. Not changed: the scheduler and the circuit.
Consequence (not acted on in Stage 5): the per-iteration depth 21 + 16 = 37 of Table 3 and the slice depth d = 74 (Table 3.3) rest on the 21; with the measured oracle they become 27 + 16 = 43 and 86, if the diffusion depth 16 holds (diffusion is a separate task).
Report §: 6.1.4 (Table 3), 3.3 (Table 3.3).

## 2026-10-23 — Report erratum: Table 2 rows a_max = 2 and 1 are infeasible (Stage 5)
Decision: measured for the c∧ = 8 chain (`examples/and_chain_8.cqr`, n = 9): a_max = 8: feasible, 1 round, depth 99 (×1), T = 32; a_max = 4: feasible, 2 rounds, 12 placements, depth 144 (×1.45), T = 48 ≤ 32 × 2; a_max = 2 and a_max = 1: infeasible under decision 3 (with p pebbles the farthest reachable chain node is 2^p − 1, so 8 nodes need p ≥ 4; a_max = 3 is infeasible too). Table 2 lists a_max = 2 (4 rounds, ×8, ≤ 256) and a_max = 1 (8 rounds, ×128, ≤ 4096); under the decided move rules these rows are errata. No schedule was invented for them. The a_max ∈ {8, 4} chains of length 8 pass the harness in every measurement branch.
Report §: 6.1.3 (Table 2, Eq. 3).

## 2026-10-23 — Stage 5 interpretations not fixed by the task (Stage 5)
Decision:
(1) `Circuit` is a structure `{nData, gates : List Gate}`, not a bare `List Gate`: untouched data qubits (x1, x2, … in the Grover oracle) count in the width. `Qubit = data i | anc i`; `Gate` adds `ifBit c g` (Clifford only, checked by `Circuit.validate`) and `alloc`/`free`. The IR types live in namespace `CQRV` (like `Grade`): `CQRV.Circuit.Circuit` trips the duplicated-namespace linter.
(2) `synthesizeOracle` returns `Except Diagnostic Circuit` (multi-output networks are rejected).
(3) ANDs whose operands are a constant or have the same linear part are folded by exact identities (`1 ∧ v = v`, `0 ∧ v = 0`, `u ∧ u = u`, `u ∧ ¬u = 0`): no gate, no ancilla. Hence a ≤ ĉ∧ and t ≤ 4ĉ∧ (Eq. 2 as a bound, equality when nothing folds). Example: `for i in [0 ..< 4] with acc = false do acc or idx(x, i)` has ĉ∧ = 4 and synthesizes with t = 12, a = 3. Only the cone of the output is synthesized.
(4) `cqr synthesize <file> [--amax k] [--json] [--layers]` prints `{name, schedule, and_complexity, grade: {w, d, t, a}}`; `--json` adds `circuit` (flat: `{n_data, n_anc, gates: [{op, q, c?, if?}]}`, data qubits 0..n_data, ancillae after) on one line; `--layers` appends the dump.
(5) Harness: `MAX_QUBITS` = 20 (data ≤ 12 plus ancillae); each predicate is checked on 2 random complex superpositions; in every branch the overlap with U_P|ψ⟩ ⊗ |0…0⟩ must be ≥ 1 − 1e−9; `alloc`/`free` assert |0⟩ in every branch. The random predicates repeat variables freely, so folding is exercised. Driver `scripts/diff_oracles.sh`, CI step after the simulator self-test.
Why: needed to implement the task; the report leaves these open.
Rejected: (3) rejecting such ANDs (would reject the standard `for … acc = false do acc or …` fold).
Report §: 6.1.2, 6.1.4, 6.2.4, 3.1.1.

## 2026-10-23 — Headline grade is the measured grade (Stage 5 review, reviewer decision)
Decision: the headline grade (w, d, t, a) = (10, 74, 72, 2) of the report (Table 3.3, Chapter 8) assumes oracle depth 21 (Table 3), which the §6.2.2 TempLogicalAND listing cannot meet: the decision-4 scheduler measures 27 (entry "Report erratum: measured Grover oracle depth is 27, not 21"). The certified grade will be the circuit's measured grade, never a number copied from the report. Table 3, Table 3.3 and Chapter 8 are to be corrected in report v3. Stage 9 acceptance becomes "measured grade, deviations documented". The Stage 1 tests stay as they are: they check the report's grade arithmetic, not the circuit. Also accepted: the Table 2 errata (a_max = 2, 1 infeasible) and the "rounds" definition (largest number of placements of any single node); constant folding (Stage 5 interpretations (3)): the certificate grade is always the measured grade of the circuit, and ĉ∧ in `SigmaIn` stays an upper bound; Stage 5 interpretations (1), (2) (`Circuit` with `nData`; `Except` results).
Why: CLAUDE.md rule 9 and §9.5.1: no grade is claimed that the synthesized circuit does not have.
Rejected: tuning the scheduler or the circuit to reach d = 21; editing the Stage 1 tests to the measured value.
Report §: 3.3 (Table 3.3), 6.1.3 (Table 2), 6.1.4 (Table 3), 8, 9.5.1.

## 2026-10-23 — Register `Reg k := Fin k → Bool`; circuits act on `Reg n × Reg a` (Stage 6, reviewer decision 1)
Decision: basis index `Reg k := Fin k → Bool` (`CQRV/Circuit/Semantics.lean`); a circuit acts on `Reg n × Reg a` (data × ancilla), `x[i] = s.1 i`, `anc[i] = s.2 i`, so `MState.traceRight` / `CPTPMap.traceRight` traces out the ancilla. `channelDenote n a C` and `AncRestore n a C U` take the dimensions explicitly; Lemma 6.3.2 uses `n = C.nData`, `a = C.nAnc`.
Why: reviewer decision 1; explicit dimensions keep the types of the 3-qubit statements (`Reg 2 × Reg 1`) syntactic, without reducing `Circuit.nAnc`.
Rejected: a flat register `Reg (n + a)` (needs a reindexing equivalence before every partial trace).
Report §: 9.1.1, 6.2.1.

## 2026-10-23 — Measurement semantics by branches (Kraus) (Stage 6, reviewer decision 2)
Decision: for `m = C.nBits` classical bits (one per `measure`), each `c : Fin m → Bool` gives `krausOps n a m gs c`, the gate product in which `measure q → j` is the projector onto `q = c j` and `ifBit j g` is `g` if `c j`, else `1`; `channelDenote n a C = CPTPMap.of_kraus_CPTPMap (krausOps …)`. `alloc`/`free` denote the identity. Completeness `∑_c K_cᴴ K_c = 1` is proved (`krausOps_complete`, no `sorry`) from the invariant "K_c depends only on the bits written so far and `2^|written| • ∑_c K_cᴴ K_c = 2^m • 1`" by induction from the end of the gate list (a fresh measurement halves the multiplicity by pairing `c` with `c` flipped at `j`). A circuit without the classical-bit discipline (`Circuit.bitsOk`) is mapped to `CPTPMap.id`, since `of_kraus_CPTPMap` needs the completeness proof.
Why: reviewer decision 2; it is what the Python harness enumerates.
Rejected: a classical-register channel on `Reg n × Reg a × Reg m` (heavier, no gain for MBU); taking a `WF` proof as an argument of `channelDenote` (every statement would carry it in its type).
Report §: 9.1.1, 6.2.2.

## 2026-10-23 — `Circuit.WF` (Stage 6, reviewer decision 3)
Decision: `Circuit.wf : Circuit → Bool`, `WF C := C.wf = true` (decidable, checked by `#guard`): every data index `< nData` (ancilla indices are `< nAnc` by definition of `nAnc`); `cnot`/`cz` operands distinct, also under `ifBit`; classical bits: each `measure q → j` writes a fresh `j < nBits`, each `ifBit j g` reads a bit already written and controls a Clifford gate. Semantics outside `WF`: a gate on a qubit outside the register and a `cnot` with a repeated operand act as the identity, so every gate matrix is unitary unconditionally (`gateU_mem_unitaryGroup`).
Why: reviewer decision 3. Making the out-of-range cases the identity keeps `gateU` total and unitary without hypotheses.
Rejected: indexing qubits by `Fin` in the IR (would change the Stage 5 IR and synthesizer).
Report §: 9.1.1, 6.2.2.

## 2026-10-23 — Stage 6a interpretations not fixed by the task (Stage 6)
Decision:
(1) Gates are monomial matrices (`monoMat σ φ`: basis permutation σ times phase φ) except `H = (1/√2)(Z + X)`; `T = diag(1, ω)`, `T† = diag(1, ω̄)`, `ω = exp(π/4 · i)` with `ω² = i`, `ω⁴ = −1`, `ω̄ ω = 1`, `ω̄ = −ω³` proved. `unitaryDenote` treats `measure`/`ifBit` as `1`; on the unitary fragment it equals every Kraus operator (`krausOps_of_unitary`).
(2) `lemma_6_3_2` carries the hypothesis `N.xorFree` (no XOR node), reading "for AND/NOT/OR networks" literally; the predicate is `Network.pred N n x` = first output bit with input `k` = `x[k]`. The synthesizer also handles XOR (Stage 5 decision 2); dropping the hypothesis is a reviewer decision.
(3) CZ in `mbu_channel_correct` is `czU := phaseOracle (fun x => x 0 && x 1)` (CZ is the phase oracle of AND), and `U ρ Uᴴ` is Physlib's `U ◃ ρ` (`MState.uConj`).
(4) The traced corollary is stated with `MState.traceRight` (`(channelDenote … ).traceRight`): `CPTPMap.traceRight (…)` applied to an `MState` does not elaborate without explicit type arguments; the two are equal by Physlib's `CPTPMap.traceRight_eq_MState_traceRight` (rfl).
(5) The Grover instance is stated for a hand-written `groverNet` (inputs 0..7, `AND(0,3)`, `AND(8,7)`) and `groverOracle` (the §6.1.4 listing) and derived from `lemma_6_3_2`; `synthesizeOracle groverNet = .ok groverOracle` is proved by `rfl`, `WF` and `xorFree` by `decide`, the predicate by `rfl`. `tests/` checks by `#guard` that the DSL front end produces the same oracle and truth table. In a `module` file `decide` cannot unfold the Batteries `DecidableEq (Except …)` instance (body not exposed), hence `rfl` for the synthesizer equation.
Why: needed to implement the task; the report leaves these open.
Rejected: (2) stating Lemma 6.3.2 for all accepted networks (stronger than asked; the 6b split covers no XOR gathers); (5) a separate `sorry` for the Grover instance.
Report §: 6.1.1, 6.1.4, 6.2.2, 6.3.2, 8, 9.1.1.

## 2026-10-23 — Stage 6a review: WF → bitsOk, XOR deferred, DSL bridge for `groverNet` (Stage 6 review, reviewer decisions)
Decision: (1) `Circuit.WF.bitsOk : C.WF → C.bitsOk = true` and `channelDenote_of_WF` are proved, so no theorem relies on the `CPTPMap.id` fallback of `channelDenote`. (5) `lemma_6_3_2` keeps the hypothesis `N.xorFree`; the XOR case is the planned obligation `lemma_6_3_2_xor` (SORRIES.md, status "planned, before Stage 9", no `sorry` in code). `scripts/check_sorries.sh` skips rows whose status starts with "planned", like "closed": such a row has no `sorry` to count. (6) `tests/CQRVTests/Semantics.lean` checks by `#guard` that `toNetwork` of `examples/grover_pred_037.cqr` equals `groverNet` field by field (`Network` has no `BEq`) and that `groverPred` is `x0 && x3 && x7` on all 256 inputs.
Why: reviewer decisions on Stage 6a; the audit change is needed for a planned row to pass the sorry audit.
Rejected: (5) a placeholder `sorry` for `lemma_6_3_2_xor` now; a planned row under a pseudo-path (would hide which file the obligation belongs to).
Report §: 6.1.2, 6.3.2, 8, 9.1.1, 9.5.1.

## 2026-10-23 — Restoration template lemma `ancRestore_of_kraus` (Stage 6b-1)
Decision: restoration proofs go through one template (`CQRV/Circuit/Restoration.lean`). With `P := ancProj n a = 1 ⊗ₖ (ancZero a).m` (`⊗ₖ` = Mathlib `Matrix.kroneckerMap (· * ·)`), `ancRestore_of_kraus` assumes `C.WF`, scalars `l : (Fin C.nBits → Bool) → ℂ` with `∑_c ‖l c‖² = 1`, and `K_c * P = l c • (U.val ⊗ₖ (ancZero a).m)` for every branch, and concludes `AncRestore n a C U`. The Kronecker shape is the one Physlib unfolds to: `(ρ ⊗ᴹ σ).m = ρ.m ⊗ₖ σ.m` holds by `rfl` (`MState.prod` is `HermitianMat.kronecker`, whose `mat` is `Matrix.kroneckerMap`); `(ancZero a).m` is `vecMulVec` of `Ket.basis 0`, used through `ancZero_m_apply` (entrywise), `ancZero_m_conjTranspose`, `ancZero_m_mul_self`. Proof: `prod_ancZero_m_eq` (`ρ ⊗ |0…0⟩⟨0…0| = P (ρ ⊗ |0…0⟩⟨0…0|) P`), push `P` into each Kraus operator (`Pᴴ = P`), `mul_kronecker_mul`, sum `‖l c‖²`. `mbu_channel_correct` is the instance `U = czU`, `l c = 1/√2`: `mbu_kraus_basis` (4 inputs × 2 branches on `basisVec`, compute block by `tempLogicalAND_correct`) → `mbu_kraus` (matrix identity column by column, `mulVec_basisVec`).
Why: task 1; every remaining restoration step (per-AND lift, Z = phase, AND-list induction) has the same shape, and the hypothesis is a matrix identity per branch that can be checked on basis vectors.
Rejected: proving `mbu_channel_correct` directly on the `of_kraus` sum (the 1/√2 bookkeeping would be redone for every later restoration lemma); stating the hypothesis on `MState`s (needs a state per basis vector; matrices are linear).
Report §: 6.2.1, 6.2.2, 6.2.4 (Layer 3), 9.1.1.

## 2026-10-23 — Composition lemma not stated: bit numbering of `krausOps` (Stage 6b-1, stop condition of task 3)
Decision: tasks 3 (`channelDenote_append`) and 4 (`AncRestore.comp`) are stopped under the task's stop condition; `krausOps` and `channelDenote` are unchanged. Finding: with `m = nBits`, `Circuit.bitsOk` forces every measurement to write a fresh bit `< nBits`, so a WF circuit writes exactly the bits `0..nBits−1`. Two WF circuits therefore have disjoint classical bits only if one of them has no measurement, and the statement "for WF `C₁`, `C₂` with disjoint bits" covers only a unitary prefix or suffix. It cannot split the uncompute half of an oracle: no cut of `groverOracle` between its two MBU blocks (bits 1 then 0) gives two WF circuits, since the prefix through `free anc1` writes bit 1 with `nBits = 1` and is not WF, so its `channelDenote` is the `CPTPMap.id` fallback (`#guard` in `tests/CQRVTests/Semantics.lean`). Proposal for the reviewer: (A) `Circuit.append C₁ C₂` renumbers `C₂`'s bits by `+ C₁.nBits` (`Gate.shiftBits`); then `C₁.WF → C₂.WF → (C₁.append C₂).WF` holds automatically and `channelDenote (C₁.append C₂) = channelDenote C₂ ∘ₘ channelDenote C₁` is provable by splitting `Fin (m₁ + m₂) → Bool` (`Fin.append`), with `krausOps_append_gates` (proved) per branch. Relating it to `groverOracle` additionally needs either (A1) a lemma `channelDenote_renameBits` (invariance under a permutation of the bit indices; reindex the sum over `c`) or (A2) the synthesizer numbering bits in measurement order (uncompute order), which changes the Stage 5 JSON but not the harness verdicts. (B) A channel semantics with an explicit ambient bit count: rejected in this proposal (completeness needs a `2^unused` normalization).
Why: the task forbids changing `krausOps` silently; the plain-`++` statement would be true but unusable for the 6b induction.
Rejected: proving the degenerate statement (one side measurement-free) as if it were task 3.
Report §: 6.2.2, 6.3.2, 9.1.1.

## 2026-10-23 — Shifted `Circuit.append`; bits in measurement order (Stage 6b-1 review, reviewer decision)
Decision: (A) `Circuit.append C₁ C₂ = ⟨C₁.nData, C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)⟩` (`CQRV/Circuit/Semantics.lean`; `Gate.shiftBits k` in `CQRV/Circuit/IR.lean` adds `k` to the bit of `measure` and `ifBit`). No disjointness hypothesis is needed: `Circuit.bitsOk_append` derives the discipline of the append from `C₁.bitsOk` and `C₂.bitsOk`, and `nBits` adds up. `channelDenote_append` (hypotheses `C₁.bitsOk = true`, `C₂.bitsOk = true`, implied by `WF` via `Circuit.WF.bitsOk`): `channelDenote n a (C₁.append C₂) = channelDenote n a C₂ ∘ₘ channelDenote n a C₁`, proved by splitting the branch assignment (`appendEquiv`: `Fin (m₁ + m₂) → Bool ≃ (Fin m₁ → Bool) × (Fin m₂ → Bool)`, inverse `Fin.append`), `krausOps_castAdd` (a disciplined prefix reads only the first `m₁` bits), `krausOps_shift` (the shifted part reads only the last `m₂`). `AncRestore.comp`: `AncRestore C₁ U₁ → AncRestore C₂ U₂ → AncRestore (C₁.append C₂) (U₂ * U₁)`, via `uConj_uConj`. (A2) `synthesizeOracle` numbers classical bits in measurement order (first measured bit = 0): each uncompute block is built with bit 0 and the `i`-th executed one is shifted by `i`. `groverOracle` now measures anc[1] into bit 0 and anc[0] into bit 1; `tests/` checks by `#guard` that it equals `groverPiece₁.append groverPiece₂` at the MBU cut (after `free anc[1]`). Grades unchanged: grover_pred_037 (w, d, t, a) = (10, 27, 8, 2), and_chain_8 `--amax 4` = (13, 144, 48, 4) (`cli_smoke`); `diff_oracles.sh` passes 101/101. Only the bit labels changed (`L27: if c1: …`, the expected Stage 5 listing). `chainCircuit` (Bennett) already numbered bits in measurement order.
Why: reviewer decision on the Stage 6b-1 stop: with shifting, the composition lemma needs no bit hypotheses, and the synthesized oracle is literally a chain of shifted appends, which the 6b induction needs.
Rejected: (A1) a permutation-invariance lemma for bit indices (more proof, not needed once the synthesizer numbers bits in measurement order); (B) an explicit ambient bit count in `channelDenote`.
Report §: 6.1.4, 6.2.2, 6.2.4, 6.3.2, 9.1.1.

## 2026-10-24 — Basis-vector route for Lemma 6.3.2 (Stage 6b-2, reviewer plan)
Decision: Lemma 6.3.2 is proved through `ancRestore_of_kraus` and one fact per Kraus branch `c` on basis inputs, `K_c |x, 0…0⟩ = 2^{-k/2} (−1)^{P(x)} |x, 0…0⟩` (k ANDs), obtained block by block on basis vectors (`CQRV/Circuit/OracleBlocks.lean`): compute block `|s⟩ ↦ |s[t ↦ s a ∧ s b]⟩` (`tempLogicalAND_correct_lift`, `tempLogicalAND_kraus_basis`), `Z t` = `(−1)^{s t}` (`z_basis`), uncompute block `|s⟩ ↦ (1/√2) |s[t ↦ 0]⟩` in every branch when `t` holds `a ∧ b` (`mbu_branch_basis`), X gates permute basis states (`x_basis`). Blocks of the synthesizer's flat gate list chain in one branch with absolute bits (`krausOps_append_mulVec`); `krausOps_append_shift_mulVec` is the same for `Circuit.append`. Interpretations: (1) `mbu_branch_basis` has no hypothesis on the bit `j` (for `j ≥ nBits`, `bitVal c j = false` and the branch-0 computation applies) and needs only `a ≠ t`, `b ≠ t`, `t` in range; (2) the lift went generic (no locality lemma): the gates are evaluated on the 3-qubit slice `Qubit.slice a b t s x y z = s[a ↦ x, b ↦ y, t ↦ z]` with `Qubit.set_comm` and the `get/flip_slice_*` lemmas, for the 4 values of `(x, y)`; (3) `tempLogicalAND_correct_lift` moved from `Restoration.lean` to `OracleBlocks.lean` (which imports `Restoration`, for `basisVec` and the TempLogicalAND listing); nothing used it. Channel composition (`channelDenote_append`, `AncRestore.comp`) stays, for Stage 7.
Why: on basis vectors there is no superposition to track across blocks; the phase appears once (at `Z`), every MBU contributes a branch-independent `1/√2`, and `∑_c ‖2^{-k/2}‖² = 1`.
Rejected: induction via channel composition (`AncRestore.comp`) — nested compute/uncompute brackets do not split into independent restoring blocks (the compute block of AND i leaves its ancilla at `a ∧ b`, restored only by the matching uncompute after the inner blocks); a locality lemma (gate list touching only `{a, b, t}` acts through the 3-qubit action) — not needed once the generic slice computation went through.
Report §: 6.1.4, 6.2.2, 6.2.4 (Layers 1, 3), 6.3.2, 9.1.1.

## 2026-10-24 — Synthesizer unchanged; the AND records live in the invariant (Stage 6b-3, reviewer decisions 1 and 2)
Decision: (1) No proof-only bookkeeping was added to `Oracle.St`: the records of the non-folded ANDs (`AndRec = (p, cu, q, cv)`: operand atoms and polarities; the target `anc j` is the position `j`) exist only existentially in `Inv` (`CQRV/Circuit/OracleCorrect.lean`), which states `st.compute.toList = recs.mapIdx (·.cmp ·)` and `st.uncompute.toList = recs.mapIdx (·.unc · 0)`. The byte-identity check of decision 1 exists anyway: `tests/diff/oracle_json.py` / `scripts/check_oracle_json.sh` (CI, after `diff_oracles.sh`) compares `cqr synthesize --json` on grover_pred_037, search_or, and_chain_8 and 20 random predicates (seed 20261024; 10 AND/NOT/OR, 10 with XOR/`if`) with `tests/diff/oracle_json_golden.txt`, generated from a3586f4 before any change; it passes, and `diff_oracles.sh` stays 101/101. (2) The monadic fold is handled by `fold_inv` (induction on `m` with `List.range_succ`, `List.foldlM_append`, `except_bind_eq_ok`) and `step_ok_inv : step N mark st k = .ok st' → Inv k st → Inv (k + 1) st'`, as proposed.
Why: reviewer decisions 1, 2; the existential records were enough, so the synthesizer did not need to change.
Rejected: an `St` field for the records (allowed by decision 1, not needed); changing the gate sequence.
Report §: 6.1.2, 6.1.4, 6.3.2.

## 2026-10-24 — Stage 6b-3 interpretations not fixed by the task (Stage 6b-3)
Decision:
(1) `lemma_6_3_2`, `lemma_6_3_2_traced` and `grover_pred_037_ancRestore` moved from `Restoration.lean` to `OracleCorrect.lean` (statements unchanged): the proof uses `OracleBlocks`, which imports `Restoration`.
(2) `Inv N n k st` holds the following. `vals.size = k`. `nextAnc = |recs|`. The compute/uncompute arrays are the records' blocks. Each record has `p ≠ q`, and `p`, `q` are data atoms or `anc i` with `i < j` (so the synthesizer never makes an operand equal to its target). Every `vals[i] = some u` is `Good`: `|u.lin| ≤ 1`; its atoms are data qubits or ancillae below `anc |recs|`; and for every ancilla register size `a ≥ |recs|` and every `x`, `u.eval (runC recs 0 (x, 0…0))` is node `i`'s value in `valuesUpTo N (inputOf x) k`, the fold of `Network.values` over the first `k` nodes. The atom state of item 1 is `runC recs 0 (x, 0…0)`. A data atom outside the register (`input i`, `i ≥ n`) reads `false`, as `inputOf` does.
(3) Qubit ranges and target distinctness inside the blocks come from `C.WF` on the final circuit (`Circuit.WF.gatesOk`: data indices from `qubitsOk`, ancilla indices from `Circuit.anc_lt_nAnc`, which follows from the definition of `nAnc`, and CNOT operands distinct), not from `Inv`.
(4) `C.nAnc = K` is not proved; `K ≤ C.nAnc` suffices (`cmpBlocks_length_le`: `alloc (anc j)` lies in the register for each record). Ancillae `≥ K` are never touched and stay 0. `C.nBits = K` is proved from `written`.
(5) Item 4, constant `P` (`p.lin = []`): no gate, so the branch scalar is `l c = (1/√2)^K · ε` with `ε = (−1)^{p.c}`, `|ε| = 1`, and `∑_c ‖l c‖² = 2^K · 2^{−K} = 1`. It is not stated as a separate case. For `p.lin = [q]`, `ε = 1`.
(6) The nested brackets are one induction, `chain_kraus`, with `cmpBlocks rs j ++ Φ ++ uncBlocks rs j`: the uncompute blocks are taken in reverse order, and the AND with target `anc j` measures into bit `|rs| − 1 − j`. The classical bit does not matter (`unc_kraus` holds for every bit and every branch). `flatten_mapIdx_cmp` / `flatten_mapIdx_unc` identify the synthesizer's `mapIdx`/`reverse`/`shiftBits` lists with these blocks.
(7) No stop condition was hit: the invariant holds for every synthesized xor-free circuit, and `pu ≠ pv` after folding is `fold`'s `u.lin == v.lin` check.
Why: needed to implement the task; the task leaves these open.
Rejected: (3) carrying register ranges in `Inv` (the fold does not know the final `nAnc`); (5) a separate theorem for constant predicates.
Report §: 6.1.1, 6.1.2, 6.1.4, 6.2.2, 6.2.4, 6.3.2, 9.1.1.
