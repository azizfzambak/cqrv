#!/usr/bin/env bash
# Stage 27b / 27b2 — the noise certificates (PHASE2_SPEC §C.4; report §2.3.2, §6.6, §8.4).
#
#   tests/diff/hw_noise_check.py --cqr      (.venv): `cqr hw noise --json` = hw/noisebound.py on all twelve artifacts
#   tests/diff/hw_noisecert_check.py --cqr  (.venv): the three conditional certificates — hashes, premises, bounds,
#                                                    the emulator comparison at delta', byte-identical regeneration
#   lake env lean                           examples/certs/hw_n2/Cert.lean, hw_n3/Cert.lean (front_end, cert),
#                                           hw_n2_torino/PhysCert.lean, hw_n3_torino/PhysCert.lean (emitted_eq axiom-free;
#                                           front_end, cert, phys_channel, phys_zero, phys_realizes, phys_noisy_inst),
#                                           mbu_gadget_torino/NoiseCert.lean (c_eq axiom-free; phys_channel, gadget_noisy)
#
# Usage (after `lake build`, from anywhere):  scripts/check_noisecerts.sh
# Portable: bash; ubuntu and Git Bash on Windows. Conditional on the premises; nothing is "verified on hardware".

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PYTHON:-}" ]; then
  if [ -x "$ROOT/.venv/Scripts/python.exe" ]; then PYTHON="$ROOT/.venv/Scripts/python.exe"
  elif [ -x "$ROOT/.venv/bin/python" ]; then PYTHON="$ROOT/.venv/bin/python"
  else PYTHON=python; fi
fi
CQR="$ROOT/.lake/build/bin/cqr"
[ -f "$CQR.exe" ] && CQR="$CQR.exe"
[ -f "$CQR" ] || { echo "check_noisecerts: $CQR not found (run lake build first)" >&2; exit 2; }
cd "$ROOT"

"$PYTHON" -I "$ROOT/tests/diff/hw_noise_check.py" --cqr "$CQR" | tail -1
"$PYTHON" -I "$ROOT/tests/diff/hw_noisecert_check.py" --cqr "$CQR"

STD="dependsonaxioms:\[propext,Classical.choice,Quot.sound\]"
fail=0
check_file() {  # check_file <file> <expected standard-three lines> <expected axiom-free lines>
  local f="$1" want="$2" wantfree="$3"
  local start end out norm n nfree
  start=$(date +%s)
  out="$(LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} lake env lean "$f" 2>&1)" || { echo "check_noisecerts: $f: lake env lean failed"; echo "$out" | head -20; fail=1; return; }
  end=$(date +%s)
  if echo "$out" | grep -q "error"; then echo "check_noisecerts: $f: errors"; echo "$out" | head -20; fail=1; return; fi
  norm="$(echo "$out" | tr -d ' \n\r')"
  n="$( { echo "$norm" | grep -o "$STD" || true; } | wc -l | tr -d ' ')"
  nfree="$( { echo "$norm" | grep -o "doesnotdependonanyaxioms" || true; } | wc -l | tr -d ' ')"
  if [ "$n" -ne "$want" ] || [ "$nfree" -ne "$wantfree" ]; then
    echo "check_noisecerts: $f: expected $want standard-three and $wantfree axiom-free lines, got $n and $nfree:"; echo "$out" | head -20; fail=1; return
  fi
  if echo "$out" | grep -q "sorryAx\|ofReduceBool"; then echo "check_noisecerts: $f: forbidden axiom"; fail=1; return; fi
  echo "check_noisecerts: $f: ok ($((end - start)) s)"
}
check_file examples/certs/hw_n2/Cert.lean 2 0
check_file examples/certs/hw_n3/Cert.lean 2 0
check_file examples/certs/hw_n2_torino/PhysCert.lean 6 1
check_file examples/certs/hw_n3_torino/PhysCert.lean 6 1
check_file examples/certs/mbu_gadget_torino/NoiseCert.lean 2 1
[ "$fail" -eq 0 ] || exit 1
echo "check_noisecerts: all checks passed"
