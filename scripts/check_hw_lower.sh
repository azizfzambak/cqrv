#!/usr/bin/env bash
# Stage 24b — the lowering and the branch-by-branch comparison on Aer (PHASE2_SPEC §C.1
# "Lowering", Track C; report §5.3, §6.2.2).
#
#   tests/diff/hw_lower_check.py   hw/lower.py (canonical circuit JSON → Qiskit dynamic circuit)
#                                  against the statevector harness, branch by branch: the phase
#                                  convention of p / cp on Aer; the MBU gadget and its uncorrected
#                                  variants, the parity instance, the dirty gadget (every basis
#                                  input); the oracles of search_or (n = 4) and simple_alu_x0_1
#                                  (n = 6) in both uncomputation modes on every basis input; their
#                                  Grover circuits with one iteration (tree mbu / coherent, few:log
#                                  mbu); the counting circuit of search_or with m = 2 (p / cp, both
#                                  modes, through CertifyTool counting-sample); per branch the
#                                  probability to 1e-9 and the state to 1e-9 in fidelity
#
# Runs with the hardware venv (.venv-hw, hw/README.md); needs the built cqr and `lake` on PATH
# (CertifyTool counting-sample is one Lean process).
# Usage (after `lake build`, from anywhere):  scripts/check_hw_lower.sh
#   PYTHON_HW=.venv-hw/Scripts/python.exe scripts/check_hw_lower.sh   # local Windows venv
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PYTHON_HW:-}" ]; then
  if [ -x "$ROOT/.venv-hw/Scripts/python.exe" ]; then PYTHON_HW="$ROOT/.venv-hw/Scripts/python.exe"
  elif [ -x "$ROOT/.venv-hw/bin/python" ]; then PYTHON_HW="$ROOT/.venv-hw/bin/python"
  else echo "check_hw_lower: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_hw_lower: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"
"$PYTHON_HW" -I "$ROOT/tests/diff/hw_lower_check.py" --cqr "$CQR"
echo "check_hw_lower: all checks passed"
