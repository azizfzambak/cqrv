#!/usr/bin/env bash
# Stage 25b V2 — the full set of emulator runs on the fake backends' noise models (PHASE2_SPEC §C.2
# "The runs"; report §5.3): every committed physical artifact of hw/artifacts/ that has a success
# predicate (the unwrapped MBU gadget has none: its wrapped form is its own artifact) is run by
# hw/run.py --sim at seed 25 — 4000 shots for the artifacts on at most 5 physical qubits, 2000 for
# the larger ones (a 16-qubit run takes ~50 s at 2000 shots on this machine; 4000 would exceed the
# ~60 s guideline) — and the per-run JSONs plus the table docs/hw_runs/RUNS.md (with the comment
# docs/hw_runs/COMMENT.md appended) are written. Not a CI step (several minutes); the committed
# report is its output. The wording is "emulator run on the fake backend's noise model".
#
# Usage (after `lake build`, from anywhere):  scripts/hw_runs.sh
#   PYTHON_HW=.venv-hw/Scripts/python.exe scripts/hw_runs.sh

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PYTHON_HW:-}" ]; then
  if [ -x "$ROOT/.venv-hw/Scripts/python.exe" ]; then PYTHON_HW="$ROOT/.venv-hw/Scripts/python.exe"
  elif [ -x "$ROOT/.venv-hw/bin/python" ]; then PYTHON_HW="$ROOT/.venv-hw/bin/python"
  else echo "hw_runs: no .venv-hw (hw/README.md)" >&2; exit 2; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "hw_runs: $CQR not found (run lake build first)" >&2; exit 2; }
OUT="$ROOT/docs/hw_runs"
mkdir -p "$OUT"
SEED=25
cd "$ROOT"
for d in hw/artifacts/*/; do
  name="$(basename "$d")"
  case "$name" in mbu_gadget__*) continue;; esac
  used="$("$PYTHON_HW" -I -c "import json,sys; print(len(json.load(open(sys.argv[1]))['layout']['used_qubits']))" "$d/manifest.json")"
  if [ "$used" -le 5 ]; then shots=4000; else shots=2000; fi
  t0=$SECONDS
  "$PYTHON_HW" -I hw/run.py --sim "$d" --shots "$shots" --seed "$SEED" --cqr "$CQR" --json "$OUT/$name.json"
  echo "  ($((SECONDS - t0)) s, $shots shots)"
done
"$PYTHON_HW" -I hw/run.py --table "$OUT"/*.json --out "$OUT/RUNS.md" ${COMMENT:+--comment "$COMMENT"} \
  $( [ -f "$OUT/COMMENT.md" ] && [ -z "${COMMENT:-}" ] && echo --comment "$OUT/COMMENT.md" )
echo "hw_runs: wrote $OUT/RUNS.md"
