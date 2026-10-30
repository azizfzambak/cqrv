# Stage 16 — the front end proved: `toNetwork_pred`, `toNetwork_WF`; certificates state it

Report §7.2–7.4 (the extractor ℰ as a total compiler on typing derivations), §5.3.3 (declared
trust boundaries), §6.1.2 (the Boolean network), §8.4.1 (what the certificate states);
PHASE2_ROADMAP.md row 16. Two tasks, **two commits**: do **16a**, reply, stop; start **16b**
after the reviewer accepts 16a.

Precondition: Stage 15b accepted; main = the 15b review commit. `git switch -c stage-16a main`
(16b: `stage-16b` from `stage-16a`). The 16a commit includes this file (untracked until then; do
not edit it). Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`.
Windows: `LEAN_NUM_THREADS=4`. Process: `lake build` in the foreground; `scripts/ci_local.sh` and
any Lean run longer than a few minutes are the user's separate terminal, one Lean process at a
time; when the build is green and the tests you can run yourself pass, stop and say "ready for
CI"; after the user's run, read `.lake/ci_local/*.log`, commit, closing reply.

**Invariants of both tasks.** `evalExpr`, `evalProgram` (`CQRV/DSL/Eval.lean`), `ToNetwork.build`,
`toNetwork`, `Network.pred`, `Network.wf` (`CQRV/Synthesis/Network.lean`) and `check` are **not
modified**: the evaluator is the reference semantics, the builder produces the committed `net`
literals. If a proof seems to need a change in one of them, stop and propose. No existing theorem
statement changes.

## Why a scoping predicate

`TExpr τ` is intrinsically typed except for variables: `.var x τ` and `.idx _ (.loopVar x m _)`
carry a name, and nothing in the term ties the name to its binder's type. `evalExpr (.var x _) env`
returns `(env.lookup x).getD .unit`; `build (.var x _) env` fails unless `x` has bits (or is a
loop index of type `Nat m`). The surface checker guarantees the discipline but that is not a
theorem about `TExpr`. So the theorems take a decidable hypothesis `tp.scoped = true`, checked by
`decide` in every certificate (16b) and by `#guard` on the corpus (16a). Proving that `check`
produces scoped terms is **not** part of Stage 16 (say so in the trust report: parser and surface
checker remain unverified).

---

## 16a — the theorems (proof stage; no generator, CLI or test-script change)

### A1. Scoping, value typing, node values (new `CQRV/DSL/Scope.lean`, new `CQRV/Synthesis/NetworkCorrect.lean`)

- `inductive Scope | val (τ : Ty) | loop (m : Nat)`; `abbrev Ctx := List (String × Scope)`
  (innermost first, like `Env`).
- `TExpr.scoped : {τ : Ty} → TExpr τ → Ctx → Bool`:
  `var x τ` — `ctx.lookup x = some (.val τ)`, or `τ = .nat m` and `ctx.lookup x = some (.loop m)`
  (a `for` index used as a value, as `evalExpr`/`build` allow);
  `idx v (.loopVar x m _)` — `ctx.lookup x = some (.loop m)` and `v` scoped; `idx v (.lit _)` — `v`;
  `letE x e₁ e₂` — `e₁` in `ctx`, `e₂` in `(x, .val σ) :: ctx`;
  `forE i n acc init body` — `init` in `ctx`, `body` in `(acc, .val σ) :: (i, .loop n) :: ctx`;
  `loopE acc init cond body` — `init` in `ctx`, `cond` and `body` in `(acc, .val σ) :: ctx`;
  the other constructors: all subterms. Structural, total, `decide`-able.
- `TypedProgram.ctx tp : Ctx` built from `tp.params` by the **same** `foldl` as `evalProgram`
  and `toNetwork` build their environments (so a repeated parameter name shadows identically);
  `TypedProgram.scoped tp := tp.body.scoped tp.ctx`; `TypedProgram.arity tp :=
  (tp.params.map (·.2.width)).sum` (the `n` of `toNetwork`; lemma `toNetwork_nInputs`).
- `ValOk : Ty → Val → Prop`: `.bool ↔ .bool _`; `.vec m ↔ .vec bs ∧ bs.length = m`;
  `.nat m ↔ .nat _` (no bound: both sides read bits `j < Ty.width (.nat m)` of `k`);
  `.unit ↔ .unit`. Lemma: `ValOk τ v → (v.bitsAt τ).length = τ.width`.
- Node values of a node array independent of `Network`: `nodeVals (ns : Array Node) (x : Nat →
  Bool) : Array Bool` with `(Network.mk n ns outs).values x = nodeVals ns x` (by `rfl` or one
  lemma); `nodeVals_size`, `nodeVals_push : nodeVals (ns.push v) x = (nodeVals ns x).push (…)`
  (`Array.foldl_push`, Init/Data/Array/Lemmas.lean — confirm with `#check`), and stability:
  `i < ns.size → (nodeVals (ns.push v) x).getD i d = (nodeVals ns x).getD i d`
  (`Array.getElem?_push_lt` / `Array.getD` — confirm names). `nodeVal ns x i := (nodeVals ns x).getD i false`.
- `WfPrefix (nIn : Nat) (ns : Array Node) : Prop`: every node `k` of `ns` satisfies the clause of
  `Network.wf` at index `k` (inputs `< nIn`, operands `< k`); `WfPrefix nIn ns → operands of v <
  ns.size → WfPrefix nIn (ns.push v)`; `WfPrefix nIn ns → outs ⊆ [0, ns.size) → (Network.mk nIn
  ns outs).wf = true`.

### A2. The invariant and the main lemma

- `EnvOk (x : Nat → Bool) (ns : Array Node) (ctx : Ctx) (envV : List (String × Val)) (envN :
  List (String × NVal)) : Prop`, **lookup-based** (shadowing comes for free):
  for every `y`, `ctx.lookup y = some (.val τ)` → `∃ v bs, envV.lookup y = some v ∧ envN.lookup y
  = some (.bits bs) ∧ ValOk τ v ∧ (∀ i ∈ bs, i < ns.size) ∧ bs.map (nodeVal ns x) = v.bitsAt τ`;
  and `ctx.lookup y = some (.loop m)` → `∃ k, k < m ∧ envV.lookup y = some (.nat k) ∧
  envN.lookup y = some (.index k)`. Lemmas: `EnvOk` is preserved by `push` (stability of
  `nodeVal` below `ns.size`) and by consing a new binding on all three lists at once.
- **`build_spec`** (induction on `e`, generalizing `ctx envV envN ns`):
  `e.scoped ctx = true → e.hasLoop = false → EnvOk x ns ctx envV envN →
   ∃ bs ns', (build e envN).run ns = .ok (bs, ns') ∧ ns'.size ≥ ns.size ∧
   (∀ i < ns.size, nodeVal ns' x i = nodeVal ns x i) ∧ (WfPrefix nIn ns → WfPrefix nIn ns') ∧
   bs.length = τ.width ∧ (∀ i ∈ bs, i < ns'.size) ∧
   bs.map (nodeVal ns' x) = (evalExpr e envV).bitsAt τ ∧ ValOk τ (evalExpr e envV)`.
  Success and correctness in one statement: every `fail` of `build` is excluded by the invariant
  (`not`/`and`/`or`/`xor`/`ite` on a non-singleton: `Ty.width .bool = 1`; `idx` out of range:
  `k < n = bs.length`, or `k < m ≤ n` for a loop index; a variable without bits: scoping; `loopE`:
  `hasLoop = false`). Helpers: `mux_spec` (three pushes, value `if c then a else b`), `natBits_spec`
  (`mapM push` over `List.range w`: bit `j` of `k`), a `List.foldlM` lemma for `forE` by induction
  on an arbitrary list generalizing the accumulator, the node array and both environments (the
  body is a subterm, so the structural induction hypothesis applies inside), `StateT.run`/`Except`
  bind equations (`except_bind_eq_ok` exists in the repository; find the `StateT` ones with
  `exact?`/`simp?`, do not guess names).
- Initial environment: `paramsOk`: for `tp.params` laid out from bit `0`, with `bit k := if k < n
  then x k else false`, `Val.ofInput bit o τ` against `NVal.bits (List.range' o τ.width)` on the
  input nodes `(Array.range n).map .input`: per type; `.nat m` needs the one arithmetic lemma
  `testBit_sum`: for `j < w`, `((∑ i < w, if b i then 2^i else 0) >>> j) % 2 == 1 ↔ b j`
  (route: `Nat.testBit` with `Nat.testBit_two_pow_add_eq`, `Nat.testBit_two_pow_add_gt`
  (Init/Data/Nat/Bitwise/Lemmas.lean) and `Nat.testBit_eq_decide_div_mod_eq` or the `%`/`>>>`
  form — confirm names; or an induction on `w` splitting the top summand; say which).

### A3. The theorems (`CQRV/Synthesis/NetworkCorrect.lean`)

```
theorem toNetwork_succeeds (tp : TypedProgram) (hl : tp.hasLoop = false) (hsc : tp.scoped = true) :
    ∃ N, toNetwork tp = .ok N
theorem toNetwork_WF (tp : TypedProgram) (N : Network) (hN : toNetwork tp = .ok N)
    (hsc : tp.scoped = true) : N.WF
theorem toNetwork_pred (tp : TypedProgram) (N : Network) (hN : toNetwork tp = .ok N)
    (hsc : tp.scoped = true) : ∀ x : Fin tp.arity → Bool, N.pred tp.arity x = evalProgram tp x
```
`toNetwork_pred` needs no `hasLoop` hypothesis: a `loopE` that `build` reaches makes `toNetwork`
fail, and one it does not reach (a `for` with bound 0) is not evaluated either — the induction
handles it (state `build_spec` so that this works, e.g. with `hasLoop` of the *reached* term, or
derive `_pred` from a variant without the `hasLoop` premise: say which). `toNetwork_nInputs :
toNetwork tp = .ok N → N.nInputs = tp.arity`. `N.pred` and `evalProgram` both read `false` beyond
`n`, both take `headD false` of the output bits.

### Acceptance (16a)

- `lake build` green, sorry-free, warning-free; guarded `#print axioms` (new
  `tests/CQRVTests/FrontEnd.lean`) for the three theorems: the standard three.
- `#guard tp.scoped = true` for the corpus: `examples/grover_pred_037`, `and_chain_8`,
  `search_or`, `simple_alu_x0_1`, `tests/certify/xor_pred`, `if_pred`, and the `mixSrc`/`natSrc`
  programs of `tests/CQRVTests/Eval.lean`; `#guard` that `tp.scoped` is `false` for one hand-built
  `TExpr` with a free variable and one with a variable at the wrong type.
- `example`/`#guard`: `toNetwork_pred` instantiated on `grover_pred_037` agrees with
  `validateFrontEnd` (the validation is now a regression test of the executable path).
- `scripts/ci_local.sh` all PASS (nothing else changes). DECISIONS.md entry: the scoping
  predicate (why it exists, where it is checked), the lookup-based `EnvOk`, the `build_spec`
  shape (success and correctness together), the arithmetic lemma's route, line counts.
  PROJECT_STATUS.md: the front-end row of §3 becomes "typed term → network: proved
  (`toNetwork_pred`, `toNetwork_WF`); parser and surface checker unverified; certificates state it
  from Stage 16b". SORRIES.md: no new rows.

### Stop conditions (16a)

- `build_spec` does not close within 3 build–fix rounds per constructor group (`var`/`lit`/`not`/
  binary; `idx`/`ite`; `letE`/`forE`), or the whole of 16a exceeds about 1 500 lines → stop,
  report the remaining goals; ship nothing of A2–A3 (A1 may be committed alone only if the
  reviewer says so).
- Any of the invariant definitions above would have to change (`evalExpr`, `build`, `toNetwork`,
  `Network.pred`, `Network.wf`, `check`) → stop and propose.

---

## 16b — certificates state the theorem; regeneration (generator stage)

### B1. The typed-term literal and the theorem in `Cert.lean` (`CQRV/Certify/Generate.lean`, new `CQRV/DSL/Render.lean`)

- `TypedProgram.renderLean : TypedProgram → String`: the Lean literal of `tp` (`Ty`, `IdxArg`,
  `TExpr` with explicit type arguments where elaboration needs them; `.lit k` as
  `(.lit ⟨k, by decide⟩)`, `.loopVar x m h` as `(.loopVar "x" m (by decide))`; strings by
  `String.quote`). Structural, one line per constructor. `#guard` its output on a small
  hand-written program against the expected string; the kernel check of `net_ok` below ties the
  literal to `net` for every certificate (a wrong literal gives a different network).
- Every generated `Cert.lean` (all templates: `mbu`, `few:log`, `coherent`) gains, after `net`:
  `def prog : TypedProgram := …`; `theorem prog_scoped : prog.scoped = true := by decide`;
  `theorem net_ok : toNetwork prog = .ok net := by decide +kernel`;
  `theorem front_end : ∀ x : Fin 8 → Bool, evalProgram prog x = Network.pred net 8 x`
  (with the arity as a numeral; from `toNetwork_pred prog net net_ok prog_scoped`). **`cert`,
  `net`, `emitted` and every existing declaration of the committed `Cert.lean` files are
  byte-identical**; only the new declarations are added (check by diff in `check_certify.sh`).
- `cqr certify` no longer runs `validateFrontEnd` (the theorem replaces the differential test
  for the typed term); `validateFrontEnd`, `cqr check --truth-table`, `tests/diff/frontend_diff.py`
  and the `#guard`s of `tests/CQRVTests/Eval.lean` stay as regression tests of the executable
  path against the Python reference. `Code.frontEndMismatch` stays (retired: documented as
  unreachable from `certify`; `check --truth-table` keeps its exit codes).

### B2. The envelope and the run report (`Certificate.lean`, `RunReport.lean`, `docs/certificate.schema.json`, `tests/diff/cert_schema.py`)

- **Schema 1.8.0** (this renumbers Stage 17's `grade_ext` to 1.9.0: PHASE2_SPEC §A.1 says so):
  `trust_boundary.front_end` gains the third wording "DSL typed term → network: proved
  (toNetwork_pred; kernel-checked net_ok and front_end in Cert.lean); parser, surface checker and
  the typed-term printer unverified; predicate_hash binds the source"; **`uncompute` becomes
  required in every certificate** (`"mbu"` written explicitly; the 15b omission convention is
  retired as decided); `solution_count` required; every certificate written since says "1.8.0".
  `cert_schema.py`: the new envelope validates, 1.7.0/1.6.0 envelopes still validate, 1.8.0
  without `uncompute` or with the old front-end wording is rejected.
- Run report: row 1b (typed AST → network) becomes `kernel-checked` with the theorem names;
  the front-end `Verification` wording "exhaustively validated" is no longer produced by `certify`.
- Regenerate the four committed certificates (`--profile illustrative_sc --bench 5 --report`;
  `grover_pred_037_few` with `--shape few:log`, `grover_pred_037_coh` with `--uncompute coherent`).
  Expected diffs: `Cert.lean` new declarations only; `certificate.json` schema, `uncompute`,
  `front_end`, hashes and machine fields; run reports. QIR/QASM byte-identical.
- Measure the kernel time of all four (`bench_kernel.sh` protocol; may run in the foreground) and
  report old → new in (e); the new `net_ok` runs the builder in the kernel, so a rise is expected
  — the stop condition below bounds it.

### Docs (16b)

DECISIONS.md: the literal route (chosen) against a source string in `Cert.lean` with the parser
run in the kernel (rejected: `String` evaluation in the kernel is slow and the parser is
unverified either way) and against stating `front_end` inside `cert` (rejected: `grover_certificate`
and the committed constructions stay unchanged); the schema bump and the renumbering of Stage 17;
the retired validation at certify time. PROJECT_STATUS.md §3 front-end row ("validated" →
"proved"), the certificate paragraph, README status line.

### Acceptance (16b)

- Build green, sorry-free; `#print axioms` for every `front_end` theorem of the four
  certificates: the standard three (`print_axioms.sh` covers them).
- The four certificates re-certify byte-identically in CI; `ci_local.sh` all PASS; `cli_smoke.sh`
  and `check_certify.sh` updated (CRLF note: patch in binary mode).
- (e): kernel time old → new per certificate, the size of the typed-term literal per certificate,
  the line counts of 16a and 16b.

### Stop conditions (16b)

- A committed `cert`, `net` or `emitted` would change → stop.
- A certificate's median kernel time rises by more than 10 s → stop and report the numbers
  before committing (Stage 14a precedent).
- `by decide` on `prog_scoped` or `decide +kernel` on `net_ok` fails or exceeds 60 s for any
  committed example → stop, report which, propose (e.g. a smaller evaluation form), do not
  weaken the statement.

---

## Closing reply (each task)

CLAUDE.md format, under 40 lines. In (e) for 16a: the shape of `build_spec`, the line counts
(A1/A2/A3), which lemma names were confirmed with `#check`, and the arithmetic route. For 16b:
the kernel-time table, the literal sizes, and the exact new `front_end` wording.
