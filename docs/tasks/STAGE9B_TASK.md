# Stage 9b — M2 integration: front-end validation, second predicate, run report, M2_REPORT

Report sections: §8.5 (pipeline walkthrough; Table 8.5.2 stage results), §8.4.4 (certificate
contents, "target" values), §9.2 Table 9.2 (second predicate row), §8.5.3 (scope note),
§5.1.3 (M supplied as a hypothesis), §5.3.3 (declared trust boundaries), §9.5.1 (reference
configuration). Precondition: Stage 9a accepted (`lemma_6_3_2_xor` closed).
`git switch -c stage-9b main`; one commit; include this file (untracked).
Windows: `LEAN_NUM_THREADS=4`; Python `.venv`. **CI stays local**: add `scripts/ci_local.sh`
that runs, in order, every step of `.github/workflows/ci.yml` that can run on this machine and
prints a one-line PASS/FAIL per step; M2 acceptance is judged on its output.

## Reviewer decisions (record in DECISIONS.md)

1. **Front-end validation (8b trust gap).** Add a small DSL evaluator `evalProgram :
   TypedProgram → (Reg n → Bool)` (total, structural, `for`/`let`/`if`/calls inlined;
   `loop … while` is rejected before evaluation). `cqr certify` checks, for n ≤ 16, that
   `evalProgram` and `Network.pred (toNetwork …)` agree on **all** 2ⁿ inputs and writes
   `trust_boundary.front_end = "DSL → network: exhaustively validated (2^n inputs) by the
   unverified evaluator; not kernel-checked"`; for n > 16 it keeps the 8b wording. Disagreement →
   no "certified", exit with a diagnostic. Rejected: kernel-checking the parser (partial).
2. **Second predicate.** Take one single-output function with ≤ 12 inputs, at least one XOR
   chain and one conditional, from the **EPFL combinational benchmark suite** or **RevLib**.
   Record in `examples/<name>.cqr` and DECISIONS.md: suite, benchmark name, URL, version/commit,
   which output bit, and how you transcribed it (XOR chain → `xor`, mux → `if`). If you cannot
   access either source from this machine, **stop and report** — do not invent a "benchmark".
   If the original has more inputs/outputs, take a documented cone of one output with ≤ 12
   inputs and say so.
3. **M for the second predicate.** ℰ will not compute it symbolically (XOR). Compute it in the
   Python harness by enumeration **as a test oracle only**, pass it with `--solutions M`; the
   certificate stays conditional on `solution_count = M` (§5.1.3: never decided by enumeration in
   the certificate). The status line must say so.
4. **Run report** `cqr certify … --report` writes `run_report.md` (and JSON) with one row per
   pipeline stage exactly in the shape of Table 8.5.2: stage, input, output, verification status
   (kernel-checked / exhaustively validated / declared trust boundary / unverified), resources —
   **measured** values, never the report's targets.

## Tasks

1. DSL evaluator + exhaustive check (decision 1); tests: the corpus files, 100 random predicates
   from the harness generator (evaluator vs network vs the Python reference evaluator).
2. Second predicate (decision 2): DSL file; `cqr check`, `extract`, `match`, `synthesize` (grade,
   layers), differential harness (all branches) for its oracle and its Grover circuit;
   success probability vs `sin²((2r⋆+1)θ)` with exact rational δ; `cqr certify`.
3. Run report (decision 4) for both predicates; commit both certificate directories under
   `examples/certs/`.
4. `scripts/ci_local.sh` (see above) and `scripts/bench_kernel.sh` for both certificates.
5. **`docs/M2_REPORT.md`** (≤ 3 pages): what is certified (theorem names, `#print axioms`
   output), the two certificates (grade, δ exact, hypotheses, hashes, kernel-check time + CPU),
   the remaining tracked obligations (`measured_composition`, `coherent_composition`, and any
   planned rows), the declared trust boundaries (front end, emitter), and a table "report claim
   vs measured value" listing **every erratum found so far** with its DECISIONS.md entry:
   oracle depth 27 vs 21; MBU reset gate missing; Table 2 rows a_max = 2, 1 infeasible and ×1.45
   vs ×2; §7.2.2 "8, 2, 3"; F₁ naming clash; diffusion (15, 89, 28, 7) vs (10, 16, 28, 2); Grover
   (15, 230, 72, 7) vs (10, 74, 72, 2); kernel check 7.43 s vs 0.3 s; Theorem 3.3a wording at
   the terminal measurement; plus any found in 9a/9b. This is the input for report v3.

## Acceptance (= MVP / M2, as revised in the Stage 5 review)

- `scripts/ci_local.sh`: every step PASS (paste it).
- Two certificates `certified (conditional on: solution_count = M)` with the standard three
  axioms, measured grades, exact δ, run reports; front end exhaustively validated for both.
- `docs/M2_REPORT.md` complete; README "Status" updated to "M2 reached (local CI)".

## Stop conditions

- No access to EPFL/RevLib (decision 2) → stop and report.
- Evaluator and network disagree on some input → stop and report the input (front-end bug).
- Do not change any proved statement; do not start Phase III items (3.3b, diamond norm).

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the second predicate's source and grade, both status
lines, the `ci_local.sh` summary, and the errata table's row count.
