#!/usr/bin/env bash
# Stage 25b — emulator runs on the fake backend's noise model (PHASE2_SPEC §C.2 "The runs"; report §5.3).
#
#   tests/diff/hw_run_check.py --schema-only   (.venv, jsonschema): the committed run reports of
#                                   docs/hw_runs/*.json against docs/hw_run.schema.json, their
#                                   Clopper–Pearson figures and check arithmetic recomputed
#   tests/diff/hw_run_check.py --cqr           (.venv-hw): the CI subset — the wrapped MBU gadget,
#                                   hw_n2 and hw_n3 on FakeTorino at 2000 shots — run in-process:
#                                   the noiseless run within 5 sigma of the reference, the figures
#                                   recomputed, the manifest hash link, determinism, the wording
#
# The full set (docs/hw_runs/RUNS.md) is produced by scripts/hw_runs.sh, not here.
# Usage (after `lake build`, from anywhere):  scripts/check_hw_runs.sh
#   PYTHON=.venv/Scripts/python.exe PYTHON_HW=.venv-hw/Scripts/python.exe scripts/check_hw_runs.sh
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
  else echo "check_hw_runs: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_hw_runs: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"
"$PYTHON" -I "$ROOT/tests/diff/hw_run_check.py" --schema-only
"$PYTHON_HW" -I "$ROOT/tests/diff/hw_run_check.py" --cqr "$CQR"
echo "check_hw_runs: all checks passed"
