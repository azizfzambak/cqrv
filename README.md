# CQRV — Certified Quantum Realization

Implementation of *Applying Certified Quantum Realization: A Practical Implementation Guide*
(`docs/cqrv_report_revised_v3.docx`). The report is the specification; `docs/PLAN.md` is the
stage-by-stage execution plan; `CLAUDE.md` holds the rules every Claude Code session follows.

Status: **M2 reached (local CI)** — Stage 9b. Two Grover certificates, `grover_pred_037` and the
RevLib benchmark cone `simple_alu_x0_1`, are `certified (conditional on: solution_count = M)`:
kernel-checked, axioms exactly `propext`, `Classical.choice`, `Quot.sound`, measured grades,
exact δ, front end exhaustively validated (`examples/certs/`, with run reports). Acceptance is
the output of `scripts/ci_local.sh` (CI is not run remotely). Summary, open obligations, trust
boundaries and the report errata: `docs/M2_REPORT.md`.

Layout: see CLAUDE.md. Obligations: `docs/SORRIES.md`. Decisions: `docs/DECISIONS.md`.

## Certifying a predicate

```bash
lake exe cqr certify examples/grover_pred_037.cqr --report
lake exe cqr certify examples/simple_alu_x0_1.cqr --solutions 30 --report   # M from the harness
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
