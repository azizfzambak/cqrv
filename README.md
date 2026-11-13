# CQRV — Certified Quantum Realization

Implementation of *Applying Certified Quantum Realization: A Practical Implementation Guide*
(`docs/cqrv_report_revised_v3.docx`). The report is the specification; `docs/PLAN.md` is the
stage-by-stage execution plan; `CLAUDE.md` holds the rules every Claude Code session follows.

Status: **M2 reached; Stages 0–20 complete, Stage 21a in progress (21a1 built), sorry-free (local CI)**; Phase 2 started (coherent uncomputation mode `--uncompute coherent` for `synthesize` and `certify`, Stages 15a–15b; a fourth certificate `examples/certs/grover_pred_037_coh`; the front end proved and stated in every certificate, Stages 16a–16b; the IR and grade extension — exact phase gates `p` / `cp` in the IR and both emitters, the second resource record `GradeExt` stated in every certificate as `gradeExt_eq` and recorded as `grade_ext`, schema 1.9.0 — Stages 17a–17b; `docs/PHASE2_ROADMAP.md`). Two Grover certificates, `grover_pred_037` and the
RevLib benchmark cone `simple_alu_x0_1` (and the few-ancilla variant `grover_pred_037_few`), are
`certified`: kernel-checked, axioms exactly `propext`, `Classical.choice`, `Quot.sound`, measured
grades, exact δ, the front end proved (`toNetwork_pred`; `front_end` kernel-checked in every `Cert.lean`, Stage 16b), and since Stage 14a the solution count M is
decided by the kernel for n ≤ 10 (`hM_count`; `--count-limit k`, default 10 since Stage 14c; larger n stay `certified
(conditional on: solution_count = M)`) (`examples/certs/`, with run reports). Acceptance is
the output of `scripts/ci_local.sh` (CI is not run remotely). Summary, open obligations, trust
boundaries and the report errata: `docs/M2_REPORT.md`.
Current state (Stages 0–20 and 21a1, one page: machine-checked results, certificates, trust
boundaries, open items): `docs/PROJECT_STATUS.md`.

Layout: see CLAUDE.md. Obligations: `docs/SORRIES.md`. Decisions: `docs/DECISIONS.md`.

## Certifying a predicate

```bash
lake exe cqr certify examples/grover_pred_037.cqr --report
lake exe cqr certify examples/simple_alu_x0_1.cqr --solutions 30 --report   # M from the harness
lake exe cqr certify examples/grover_pred_037.cqr --profile illustrative_sc  # + declared budget
lake exe cqr certify examples/grover_pred_037.cqr --count-limit 0           # M as a hypothesis
scripts/ci_local.sh                                                         # local CI
```

## Building on Windows

Builds that compile Physlib (e.g. `lake build CQRVTests`) can exhaust memory on Windows when
Lake runs one Lean process per core, failing with `failed to read file '…olean': Invalid argument`.
Limit parallelism (Git Bash):

```bash
export LEAN_NUM_THREADS=4
lake exe cache get && lake build
```

Setting up a new workstation (repository and toolchain on an SSD, build, CI): `docs/SETUP_WORKSTATION.md`.
