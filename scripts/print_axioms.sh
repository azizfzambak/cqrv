#!/usr/bin/env bash
# Axiom audit — report §9.5.1 (master discipline), §9.5.3, CLAUDE.md rule 10.
#
# Blocking since Stage 8b (DECISIONS.md 2026-10-25):
#   1. every named theorem declared in a module under CQRV/Certify (scripts/PrintAxioms.lean;
#      auto-generated injEq / sizeOf_spec / eq_* lemmas are skipped) must pass
#      CQRV.Certify.auditAxioms: no sorryAx, only propext, Classical.choice, Quot.sound or an
#      entry of the trust-boundary table (CQRV/Certify/Audit.lean, empty today);
#   2. the committed example certificates examples/certs/{grover_pred_037,simple_alu_x0_1,
#      grover_pred_037_few,grover_pred_037_coh}/Cert.lean (the second since Stage 9b, the third
#      since Stage 14a, the fourth — mode coherent — since Stage 15b) must
#      kernel-check and their theorems `cert` and (Stage 16b) `front_end` must pass the same
#      audit (scripts/CertifyTool.lean `audit`, one Lean run per file); since Stage 14a `cert` has
#      no hypothesis there (`hM_count`).
# Exits non-zero on any failure. Run after `lake build`.
#
# Portable: bash only; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/PrintAxioms.lean 2>&1 | tr -d '\r' \
  | sed -E 's/^.*PrintAxioms\.lean:[0-9]+:[0-9]+: (info: )?//'
# <directory>:<theorem namespace>
for spec in grover_pred_037:grover_pred_037 simple_alu_x0_1:simple_alu_x0_1 \
    grover_pred_037_few:grover_pred_037 grover_pred_037_coh:grover_pred_037; do
  lake env lean --run scripts/CertifyTool.lean audit \
    "examples/certs/${spec%%:*}/Cert.lean" "CQRV.Cert.${spec#*:}.cert" \
    "CQRV.Cert.${spec#*:}.front_end"
done
