#!/usr/bin/env bash
# Stage 26c1b — the per-instance hardware checks (PHASE2_SPEC §C.3 "26c1b"; report §5.3, §9.1.1).
#
#   tests/diff/hw_checks_check.py --cqr <cqr>   (.venv): for every committed examples/hw_checks/*/Check.lean,
#                                   the hashes in its header are those of the artifact's logical.json,
#                                   witness.json and physical.json and of the target's snapshot, and the
#                                   file is byte-identical to what `cqr hw check` regenerates from the
#                                   artifact (the literals are the artifact's);
#   lake env lean <Check.lean>      the kernel checks every theorem of the file (`rfl`, `decide +kernel`);
#                                   the two `#print axioms` lines must name exactly the standard three
#                                   axioms; the wall time of each file is printed.
#
# Budget: 15 min for the step (the twelve files take about 4 min in total on the reference machine).
# Usage (after `lake build`, from anywhere):  scripts/check_hw_checks.sh
#   PYTHON=.venv/Scripts/python.exe scripts/check_hw_checks.sh
# Portable: bash; ubuntu and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PYTHON:-}" ]; then
  if [ -x "$ROOT/.venv/Scripts/python.exe" ]; then PYTHON="$ROOT/.venv/Scripts/python.exe"
  elif [ -x "$ROOT/.venv/bin/python" ]; then PYTHON="$ROOT/.venv/bin/python"
  else PYTHON=python; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_hw_checks: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"

"$PYTHON" -I "$ROOT/tests/diff/hw_checks_check.py" --cqr "$CQR"

# `#print axioms` wraps long names over several lines: compare with whitespace removed.
fail=0
for f in examples/hw_checks/*/Check.lean; do
  name="$(basename "$(dirname "$f")")"
  start=$(date +%s)
  out="$(LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} lake env lean "$f" 2>&1)" || { echo "check_hw_checks: $name: lake env lean failed"; echo "$out" | head -20; fail=1; continue; }
  end=$(date +%s)
  if echo "$out" | grep -q "error"; then
    echo "check_hw_checks: $name: errors"; echo "$out" | head -20; fail=1; continue
  fi
  norm="$(echo "$out" | tr -d ' 
')"
  n_ax="$(echo "$norm" | grep -o "dependsonaxioms:\[propext,Classical.choice,Quot.sound\]" | wc -l | tr -d ' ')"
  if [ "$n_ax" -ne 2 ]; then
    echo "check_hw_checks: $name: expected two axiom lines with the standard three axioms, got:"; echo "$out" | head -20; fail=1; continue
  fi
  if echo "$out" | grep -q "sorryAx\|ofReduceBool"; then
    echo "check_hw_checks: $name: forbidden axiom"; echo "$out" | head -20; fail=1; continue
  fi
  echo "check_hw_checks: $name: ok ($((end - start)) s)"
done
[ "$fail" -eq 0 ] || exit 1
echo "check_hw_checks: all checks passed"
