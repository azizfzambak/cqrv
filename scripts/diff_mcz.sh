#!/usr/bin/env bash
# Differential test of the few-ancilla MCZ — report §3.1.4, §6.1.4, §6.2, §8.2; CLAUDE.md rule 9
# (Stage 12b decision 3). The circuits are unproved; this is the only evidence of correctness.
#
# Runs tests/diff/mcz_diff.py against the built `cqr` executable: relative-phase Toffoli gadget
# check, the diffusion with `--shape few:ladder|few:log` for n = 1..10 in every measurement branch
# (data register exact, ancillae back to |0>), negative controls (uncancelled relative phase,
# corrupted gadget), one Grover iteration of grover_pred_037 in every branch and the full circuit
# at r* = 2 (success probability exactly 121/128), both variants.
#
# Usage (after `lake build`):  scripts/diff_mcz.sh [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_mcz.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "diff_mcz: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/mcz_diff.py" --cqr "$CQR" "$@"
