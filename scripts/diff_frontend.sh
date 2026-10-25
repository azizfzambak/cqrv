#!/usr/bin/env bash
# Front-end validation — report §5.3.3, §7.2, §9.5.1 (Stage 9b, reviewer decision 1).
#
# Runs tests/diff/frontend_diff.py against the built `cqr` executable: `cqr check --truth-table`
# (the Lean DSL evaluator and Network.pred (toNetwork …)) must equal a Python reference on every
# input, for the corpus files and 100 random predicates (and/or/xor/if, n <= 12, fixed seed).
#
# Usage (after `lake build`):  scripts/diff_frontend.sh [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_frontend.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "diff_frontend: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/frontend_diff.py" --cqr "$CQR" "$@"
