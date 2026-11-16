#!/usr/bin/env bash
# Stage 30a (A5) — the layering check (CLAUDE.md "Layout"; PHASE2_SPEC §B.3 (2)).
#
# The packages are layered as CLAUDE.md lists them: Grades < Realizability < Patterns < DSL < Matching
# < Circuit < Synthesis < Certify < Emit < Grover < Hardware < Noise. The hard rule, which FAILS the
# check: no module of CQRV/Circuit/ or CQRV/Synthesis/ imports a module of CQRV/Grover/. Any other
# upward import (a module importing a module of a higher layer) is LISTED and reported, not failed.
#
# Usage (from anywhere): scripts/check_layering.sh      Exit 0 iff the hard rule holds.

set -uo pipefail
cd "$(dirname "$0")/.."

layers=(Grades Realizability Patterns DSL Matching Circuit Synthesis Certify Emit Grover Hardware Noise)
idx() { local i; for i in "${!layers[@]}"; do [ "${layers[$i]}" = "$1" ] && { echo "$i"; return; }; done; echo -1; }

fail=0 upward=0
for f in $(find CQRV -name '*.lean' | sort); do
  from=$(echo "$f" | cut -d/ -f2)
  [ -f "$f" ] || continue
  fi_=$(idx "$from")
  for m in $(grep -E '^(public |meta )?import CQRV\.' "$f" | sed -E 's/^(public |meta )?import //'); do
    to=$(echo "$m" | cut -d. -f2)
    ti=$(idx "$to")
    [ "$ti" -lt 0 ] && continue
    if { [ "$from" = Circuit ] || [ "$from" = Synthesis ]; } && [ "$to" = Grover ]; then
      echo "check_layering: FAIL $f imports $m (Circuit/Synthesis must not import Grover)"
      fail=1
    elif [ "$fi_" -ge 0 ] && [ "$ti" -gt "$fi_" ]; then
      echo "check_layering: upward import (reported, not failed): $f imports $m"
      upward=$((upward + 1))
    fi
  done
done
echo "check_layering: $upward other upward import(s) listed"
[ "$fail" -eq 0 ] && echo "check_layering: OK (no Circuit/Synthesis module imports Grover)"
exit "$fail"
