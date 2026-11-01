#!/usr/bin/env bash
# Stage 18a (docs/tasks/STAGE18_TASK.md A0, A2) — the kernel-evaluation probe: rand_a64 at
# r = 1, 2, 3 per declaration (memory guard 9 GB), the `Nat m` front-end block, and `grade_eq` /
# `gradeExt_eq` alone for the four committed certificates; writes bench/forms/out/ (git-ignored)
# and docs/benchmarks/KERNEL_FORMS.md. Measurement only; one Lean process at a time; 900 s per
# Lean run. Details and options: scripts/kernel_forms.py.
#
# Usage (after `lake build`, from anywhere; run it in your own terminal, it takes up to an hour):
#   export LEAN_NUM_THREADS=4
#   PYTHON=.venv/Scripts/python.exe scripts/kernel_forms.sh [--only rand,natm,committed] [--r-max 3]
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
cd "$ROOT"
exec "$PY" -I scripts/kernel_forms.py "$@"
