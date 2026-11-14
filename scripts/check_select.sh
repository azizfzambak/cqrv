#!/usr/bin/env bash
# Stage 21a4 — certified selection under a budget (PHASE2_SPEC.md §A.6 amendment (8), refinement
# (8′); report §3.1.2, §6.1.3): `cqr certify --budget w,d,t,a --prefer width|depth|t|anc`.
#
#   tests/diff/select_check.py   the committed examples/certs/grover_pred_037_sel regenerated
#                                (--budget 12,200,100,8 --prefer depth --report): certified, bytes
#                                and JSON (outside reference_configuration) equal, fewLogMbu
#                                selected, the three candidate grades = the committed Grover
#                                certificates' grades, .qir / .qasm = grover_pred_037_few's,
#                                Cert.lean minus the selection block = grover_pred_037_few's;
#                                a second run (--budget 20,300,200,8 --prefer depth → treeMbu,
#                                .qir / .qasm = grover_pred_037's); the semantic rules
#                                (admissible, order, argmin with ties by list order); no fit →
#                                budget_unsatisfiable, exit 1, nothing written; the refusals of
#                                G3 (exit 2); two negative kernel tests (budget raised → `selected`
#                                fails; a candidate grade lowered → the kernel check fails)
#
# Usage (after `lake build`, from anywhere):  scripts/check_select.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_select.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_select: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/select_check.py" --cqr "$CQR"
echo "check_select: all checks passed"
