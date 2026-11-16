#!/usr/bin/env bash
# Stage 26c2 / 26c2b — the physical certificate and the selections (PHASE2_SPEC §C.3; report §3.1.3, §5.3, §8.4).
#
#   tests/diff/hw_physgrade_check.py --cqr   (.venv):    `cqr hw grade --json` = hw/physgrade.py on all artifacts at L = 0, 1000
#   tests/diff/hw_physcert_check.py --cqr    (.venv-hw): examples/certs/grover_pred_037_torino — hashes, status words,
#                                                        grades, regeneration, physical.qasm parses back (qiskit.qasm3)
#   tests/diff/hw_select_check.py --cqr      (.venv):    the four examples/hw_select/*/Select.lean — hash links to the
#                                                        Check.lean files, regeneration, the budget test (none on FakeTorino)
#   lake env lean                            PhysCert.lean (emitted_eq without axioms; cert, front_end, phys_channel,
#                                            phys_zero, phys_realizes with the standard three) and the four Select.lean
#                                            (choice_spec with the standard three)
#
# Usage (after `lake build`, from anywhere):  scripts/check_physcert.sh
#   PYTHON=.venv/Scripts/python.exe PYTHON_HW=.venv-hw/Scripts/python.exe scripts/check_physcert.sh
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
  else echo "check_physcert: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_physcert: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"

"$PYTHON" -I "$ROOT/tests/diff/hw_physgrade_check.py" --cqr "$CQR" | tail -1
"$PYTHON_HW" -I "$ROOT/tests/diff/hw_physcert_check.py" --cqr "$CQR"
"$PYTHON" -I "$ROOT/tests/diff/hw_select_check.py" --cqr "$CQR"

# `#print axioms` wraps long names over several lines: compare with whitespace removed.
STD="dependsonaxioms:\[propext,Classical.choice,Quot.sound\]"
fail=0
check_file() {  # check_file <file> <expected standard-three lines> <expected axiom-free lines>
  local f="$1" want="$2" wantfree="$3"
  local start end out norm n nfree
  start=$(date +%s)
  out="$(LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} lake env lean "$f" 2>&1)" || { echo "check_physcert: $f: lake env lean failed"; echo "$out" | head -20; fail=1; return; }
  end=$(date +%s)
  if echo "$out" | grep -q "error"; then echo "check_physcert: $f: errors"; echo "$out" | head -20; fail=1; return; fi
  norm="$(echo "$out" | tr -d ' \n\r')"
  # (grep -o exits 1 on no match; under pipefail that would abort the script, so count with || true)
  n="$( { echo "$norm" | grep -o "$STD" || true; } | wc -l | tr -d ' ')"
  nfree="$( { echo "$norm" | grep -o "doesnotdependonanyaxioms" || true; } | wc -l | tr -d ' ')"
  if [ "$n" -ne "$want" ] || [ "$nfree" -ne "$wantfree" ]; then
    echo "check_physcert: $f: expected $want standard-three and $wantfree axiom-free lines, got $n and $nfree:"; echo "$out" | head -20; fail=1; return
  fi
  if echo "$out" | grep -q "sorryAx\|ofReduceBool"; then echo "check_physcert: $f: forbidden axiom"; fail=1; return; fi
  echo "check_physcert: $f: ok ($((end - start)) s)"
}
check_file examples/certs/grover_pred_037_torino/PhysCert.lean 5 1
for f in examples/hw_select/*/Select.lean; do check_file "$f" 1 0; done
[ "$fail" -eq 0 ] || exit 1
echo "check_physcert: all checks passed"
