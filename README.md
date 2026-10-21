# CQRV — Certified Quantum Realization

Implementation of *Applying Certified Quantum Realization: A Practical Implementation Guide*
(`docs/cqrv_report_revised_v2.docx`). The report is the specification; `docs/PLAN.md` is the
stage-by-stage execution plan; `CLAUDE.md` holds the rules every Claude Code session follows.

Status: Stage 0 complete (repository, toolchain, CI).

Layout after Stage 0: see CLAUDE.md. Obligations: `docs/SORRIES.md`. Decisions: `docs/DECISIONS.md`.

## Building on Windows

Builds that compile Physlib (e.g. `lake build CQRVTests`) can exhaust memory on Windows when
Lake runs one Lean process per core, failing with `failed to read file '…olean': Invalid argument`.
Limit parallelism (Git Bash):

```bash
export LEAN_NUM_THREADS=4
lake exe cache get && lake build
```
