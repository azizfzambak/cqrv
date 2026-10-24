#!/usr/bin/env bash
# Differential diffusion / Grover test — report §8.2, §3.2.4, §6.2.4; CLAUDE.md rule 9 (Stage 5b).
#
# Runs tests/diff/grover_diff.py against the built `cqr` executable: (a) the diffusion for
# n = 1..10 (V1) and Bennett budgets (V2) in every measurement branch, (b) one Grover iteration
# of grover_pred_037 in every branch, (c) the full Grover circuit at r* = 2 (sampled branch),
# success probability = sin^2(5 theta) to 1e-9.
#
# Usage (after `lake build`):  scripts/diff_grover.sh [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_grover.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "diff_grover: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/grover_diff.py" --cqr "$CQR" "$@"
