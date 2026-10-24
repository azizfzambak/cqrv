#!/usr/bin/env bash
# Stage 8a checks — report §5.3, §8.4.2–8.4.4, §9.5.3 (SHA3, certificate schema, emitters).
#
#   tests/diff/sha3_diff.py    Lean SHA3-256 vs hashlib: 2 vectors + 200 random strings
#   tests/diff/cert_schema.py  sample certificate (Lean) against docs/certificate.schema.json
#   tests/diff/emit_diff.py    QIR / QASM of grover_pred_037 re-parse to exactly the Lean IR;
#                              the re-parsed QASM oracle is simulated in every branch;
#                              llvm-as assembles the QIR (skipped with a message when absent,
#                              mandatory with REQUIRE_LLVM_AS=1, as in CI)
#
# Usage (after `lake build`):  scripts/check_emit.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_emit.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PY="${PYTHON:-python}"
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_emit: $CQR not found (run lake build first)" >&2; exit 2; }
llvm=()
[ "${REQUIRE_LLVM_AS:-0}" = "1" ] && llvm=(--require-llvm-as)
"$PY" -I "$ROOT/tests/diff/sha3_diff.py"
"$PY" -I "$ROOT/tests/diff/cert_schema.py" --cqr "$CQR"
"$PY" -I "$ROOT/tests/diff/emit_diff.py" --cqr "$CQR" "${llvm[@]}"
echo "check_emit: all checks passed"
