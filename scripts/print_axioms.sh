#!/usr/bin/env bash
# Axiom audit — report §9.5.1 (master discipline), §9.5.3, CLAUDE.md rule 10.
#
# Blocking since Stage 8b (DECISIONS.md 2026-10-25):
#   1. every named theorem declared in a module under CQRV/Certify (scripts/PrintAxioms.lean;
#      auto-generated injEq / sizeOf_spec / eq_* lemmas are skipped) must pass
#      CQRV.Certify.auditAxioms: no sorryAx, only propext, Classical.choice, Quot.sound or an
#      entry of the trust-boundary table (CQRV/Certify/Audit.lean, empty today);
#   2. the committed example certificates examples/certs/{grover_pred_037,simple_alu_x0_1}/
#      Cert.lean (the second since Stage 9b) must kernel-check and their theorem `cert` must pass
#      the same audit (scripts/CertifyTool.lean `audit`).
# Exits non-zero on any failure. Run after `lake build`.
#
# Portable: bash only; ubuntu and Git Bash on Windows.

set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/PrintAxioms.lean 2>&1 | tr -d '\r' \
  | sed -E 's/^.*PrintAxioms\.lean:[0-9]+:[0-9]+: (info: )?//'
for name in grover_pred_037 simple_alu_x0_1; do
  lake env lean --run scripts/CertifyTool.lean audit \
    "examples/certs/$name/Cert.lean" "CQRV.Cert.$name.cert"
done
