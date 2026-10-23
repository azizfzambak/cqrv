#!/usr/bin/env bash
# CLI smoke test for `cqr check` / `cqr extract` — report §4.2.2, §4.2.3 Table 2, §7.2.3.
#
# Runs the three corpus files of examples/ through the built `cqr` executable:
#   grover_pred_037  extracts with "and_complexity": 2 and no field named *minimum*
#                    (ĉ∧ is a syntactic upper bound, §7.2.2);
#                    with --solutions 31 (contradicts M = 32): stage extract,
#                    code solution_count_mismatch, exit 1;
#   search_while     passes `check`, extracts with iter = unbounded;
#   allocate_tree    fails `check`: stage surface, code non_structural_recursion, exit 1.
#
# Usage (after `lake build`): scripts/cli_smoke.sh
# Portable: bash + grep; ubuntu and Git Bash on Windows.

set -uo pipefail

cqr=(lake exe cqr)
fail=0
ok()  { echo "ok:   $1"; }
bad() { echo "FAIL: $1"; fail=1; }

# expect <description> <expected exit> <output> <actual exit>
expect_exit() { [ "$4" -eq "$2" ] && ok "$1 (exit $4)" || bad "$1: exit $4, expected $2"; }
expect_has() { grep -qF -- "$2" <<<"$3" && ok "$1" || { bad "$1: missing $2"; echo "$3"; }; }

out="$("${cqr[@]}" extract examples/grover_pred_037.cqr | tr -d '\r')"; rc=$?
expect_exit "extract grover_pred_037" 0 "$out" "$rc"
expect_has "grover_pred_037 and_complexity" '"and_complexity": 2' "$out"
expect_has "grover_pred_037 and_depth" '"and_depth": 2' "$out"
expect_has "grover_pred_037 ancilla_budget" '"ancilla_budget": 2' "$out"
expect_has "grover_pred_037 solution_count" '"solution_count": 32' "$out"
expect_has "grover_pred_037 support" '"support": [0, 3, 7]' "$out"
if grep -qiE '"[^"]*minimum[^"]*"[[:space:]]*:' <<<"$out"; then
  bad "grover_pred_037 has a field named *minimum*"
else
  ok "grover_pred_037 has no field named *minimum*"
fi

out="$("${cqr[@]}" extract examples/grover_pred_037.cqr --solutions 31 | tr -d '\r')"; rc=$?
expect_exit "extract grover_pred_037 --solutions 31 (contradicts M = 32)" 1 "$out" "$rc"
expect_has "grover_pred_037 --solutions 31 stage" '"stage":"extract"' "$out"
expect_has "grover_pred_037 --solutions 31 code" '"code":"solution_count_mismatch"' "$out"
out="$("${cqr[@]}" extract examples/grover_pred_037.cqr --solutions 32 | tr -d '\r')"; rc=$?
expect_exit "extract grover_pred_037 --solutions 32 (agrees with M = 32)" 0 "$out" "$rc"

"${cqr[@]}" check examples/search_while.cqr >/dev/null; rc=$?
expect_exit "check search_while" 0 "" "$rc"
out="$("${cqr[@]}" extract examples/search_while.cqr --solutions 64 | tr -d '\r')"; rc=$?
expect_exit "extract search_while --solutions 64" 0 "$out" "$rc"
expect_has "search_while iter" '"iter": {"kind": "unbounded"}' "$out"
expect_has "search_while solution_count from --solutions" '"solution_count": 64' "$out"

out="$("${cqr[@]}" check examples/allocate_tree.cqr | tr -d '\r')"; rc=$?
expect_exit "check allocate_tree" 1 "$out" "$rc"
expect_has "allocate_tree stage" '"stage":"surface"' "$out"
expect_has "allocate_tree code" '"code":"non_structural_recursion"' "$out"
out="$("${cqr[@]}" extract examples/allocate_tree.cqr | tr -d '\r')"; rc=$?
expect_exit "extract allocate_tree" 1 "$out" "$rc"

[ "$fail" -eq 0 ] && echo "cli_smoke: all checks passed" || echo "cli_smoke: FAILED"
exit "$fail"
