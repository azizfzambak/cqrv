#!/usr/bin/env bash
# Stage 19b B6 (docs/tasks/STAGE19_TASK.md; PHASE2_SPEC.md §A.3) — the block probe of the
# counting circuit: grover_pred_037 at m = 4, both uncomputation modes; the block table of
# `counting-sample`, the generated bench/counting/Blocks_<mode>.lean (each distinct block as a
# literal with `… = .ok block` and `grade_eq` / `gradeExt_eq` by `decide +kernel`), measured per
# declaration with the Stage 18a machinery (900 s timeout, 8 GB kill); writes
# docs/benchmarks/COUNTING_BLOCKS.md. Report only; not in CI; no certificate.
#
# Usage (after `lake build`, from anywhere; run it in your own terminal, one Lean process at a time):
#   export LEAN_NUM_THREADS=4
#   PYTHON=.venv/Scripts/python.exe scripts/counting_blocks.sh [--timeout 900] [--threshold-ms 100]
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
cd "$ROOT"
exec "$PY" -I scripts/counting_blocks.py "$@"
