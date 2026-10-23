#!/usr/bin/env bash
# Differential oracle test — report §6.1.4, §6.2.2, §6.2.4; CLAUDE.md rule 9 (Stage 5).
#
# Runs tests/diff/oracle_diff.py against the built `cqr` executable: 100 random AND/NOT/OR
# predicates (fixed seed, n ≤ 12) + grover_pred_037, 30 xor/if predicates and Bennett chains;
# every measurement branch is checked on random complex superpositions.
#
# Usage (after `lake build`):  scripts/diff_oracles.sh [--seed S]
#   PYTHON=.venv/Scripts/python.exe scripts/diff_oracles.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "diff_oracles: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/oracle_diff.py" --cqr "$CQR" "$@"
