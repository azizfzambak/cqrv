#!/usr/bin/env bash
# Stage 25a — transpile with a witness (PHASE2_SPEC §C.2, Track C; report §5.3).
#
#   tests/diff/hw_transpile_check.py --schema-only   (.venv, jsonschema): the committed witness.json
#                                   and manifest.json of hw/artifacts/ against docs/hw_witness.schema.json
#                                   and docs/hw_artifact.schema.json
#   tests/diff/hw_transpile_check.py --cqr           (.venv-hw): the decomposition table numerically;
#                                   for every instance and target the pipeline reproduces the committed
#                                   artifact byte for byte (reconstruction = physical circuit, coupling
#                                   edges, blocks restore the layout, final layout = Qiskit's, seed
#                                   search deterministic); the manifest hashes recomputed; the bound
#                                   recomputed from the committed QASM 3; the ideal-equivalence check
#                                   of the physical circuit against the statevector harness
#
# Usage (after `lake build`, from anywhere):  scripts/check_hw_transpile.sh
#   PYTHON=.venv/Scripts/python.exe PYTHON_HW=.venv-hw/Scripts/python.exe scripts/check_hw_transpile.sh
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PYTHON:-}" ]; then
  if [ -x "$ROOT/.venv/Scripts/python.exe" ]; then PYTHON="$ROOT/.venv/Scripts/python.exe"
  elif [ -x "$ROOT/.venv/bin/python" ]; then PYTHON="$ROOT/.venv/bin/python"
  else PYTHON=python; fi
fi
if [ -z "${PYTHON_HW:-}" ]; then
  if [ -x "$ROOT/.venv-hw/Scripts/python.exe" ]; then PYTHON_HW="$ROOT/.venv-hw/Scripts/python.exe"
  elif [ -x "$ROOT/.venv-hw/bin/python" ]; then PYTHON_HW="$ROOT/.venv-hw/bin/python"
  else echo "check_hw_transpile: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_hw_transpile: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"
"$PYTHON" -I "$ROOT/tests/diff/hw_transpile_check.py" --schema-only
"$PYTHON_HW" -I "$ROOT/tests/diff/hw_transpile_check.py" --cqr "$CQR"
echo "check_hw_transpile: all checks passed"
