#!/usr/bin/env bash
# Stage 24a — the hardware target model (PHASE2_SPEC §C.1, Track C; report §3.1.3, §5.3).
#
#   tests/diff/hw_target_check.py   both committed targets of hw/targets/ validate against
#                                   docs/hardware_target.schema.json (--schema-only, with the
#                                   harness venv's jsonschema; Stage 24b); re-extracting each from its
#                                   fake backend is byte-identical; snapshot.hash = hashlib's
#                                   SHA3-256 of the canonical calibration; `cqr hw capabilities`
#                                   prints the expected modes and `snapshot hash ok` (Lean's
#                                   canonical form and SHA3 = Python's), exit 0; a corrupted
#                                   calibration number exits 1; a missing file exits 2
#
# The schema validation runs with the harness venv (.venv, PYTHON; jsonschema 4.26.0), the rest with
# the hardware venv (.venv-hw, pinned by hw/requirements.lock; see hw/README.md).
# Usage (after `lake build`, from anywhere):  scripts/check_hw_target.sh
#   PYTHON=.venv/Scripts/python.exe PYTHON_HW=.venv-hw/Scripts/python.exe scripts/check_hw_target.sh
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
  else echo "check_hw_target: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_hw_target: $CQR not found (run lake build first)" >&2; exit 2; }
"$PYTHON" -I "$ROOT/tests/diff/hw_target_check.py" --schema-only
"$PYTHON_HW" -I "$ROOT/tests/diff/hw_target_check.py" --cqr "$CQR"
echo "check_hw_target: all checks passed"
