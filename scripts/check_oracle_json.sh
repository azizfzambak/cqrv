#!/usr/bin/env bash
# Synthesized-circuit byte identity — Stage 6b-3, reviewer decision 1 (report §6.1.4, §6.3.2).
#
# Runs tests/diff/oracle_json.py: `cqr synthesize --json` on the three corpus files and on 20
# random predicates (fixed seed) must be byte-identical to tests/diff/oracle_json_golden.txt.
#
# Usage (after `lake build`):  scripts/check_oracle_json.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_oracle_json.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_oracle_json: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/oracle_json.py" --cqr "$CQR" "$@"
