#!/usr/bin/env bash
# Stage 8b checks — report §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3 (`cqr certify`).
#
#   tests/diff/certify_check.py  cqr certify examples/grover_pred_037.cqr: status line, schema
#                                v1.1.0, grade, δ, axioms; circuit hash = SHA3 of the IR literal
#                                of Cert.lean (hashlib); .qasm / .qir re-parse to the literal;
#                                second run byte-identical (JSON except kernel_check); the
#                                committed examples/certs/grover_pred_037 agrees; negative tests
#                                (XOR → lemma_6_3_2_xor, injected sorry → sorryAx, native_decide
#                                → its auxiliary axiom, search_while → Stage 4 hint)
#
# Usage (after `lake build`, from anywhere):  scripts/check_certify.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_certify.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_certify: $CQR not found (run lake build first)" >&2; exit 2; }
"$PY" -I "$ROOT/tests/diff/certify_check.py" --cqr "$CQR"
echo "check_certify: all checks passed"
