#!/usr/bin/env bash
# CLI smoke test for `cqr check` / `cqr extract` / `cqr match` — report §4.2.2, §4.2.3 Table 2,
# §7.2.3, §4.2.4, §4.3.2–4.3.3.
#
# Runs the three corpus files of examples/ through the built `cqr` executable:
#   grover_pred_037  extracts with "and_complexity": 2 and no field named *minimum*
#                    (ĉ∧ is a syntactic upper bound, §7.2.2);
#                    with --solutions 31 (contradicts M = 32): stage hypothesis,
#                    code solution_count_mismatch, exit 1;
#   search_while     passes `check`, extracts with iter = unbounded;
#   allocate_tree    fails `check`: stage surface, code non_structural_recursion, exit 1.
# and `cqr match`: grover_pred_037 matches Grover (F₁=8, F₂=32, F₃=1, 32 ≥ 1); search_while
# --solutions 64 gives the iter hint; search_or needs --solutions (5 matches, 0 fails F₂ ≥ 1).
#
# and `cqr synthesize` (Stage 5): the Grover oracle grade (10, 27, 8, 2) and its layer dump, the
# and_chain_8 budgets (--amax 4 feasible, --amax 2 infeasible), search_while → unbounded_loop.
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
expect_has "grover_pred_037 --solutions 31 stage" '"stage":"hypothesis"' "$out"
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

# Stage 4 — `cqr match` (report §4.1.4, §4.2.4, §4.3.2–4.3.3): one match or one hint, never a list.
out="$("${cqr[@]}" match examples/grover_pred_037.cqr | tr -d '\r')"; rc=$?
expect_exit "match grover_pred_037" 0 "$out" "$rc"
expect_has "grover_pred_037 pattern" '"pattern": "Grover"' "$out"
expect_has "grover_pred_037 F₁" '"F₁": 8' "$out"
expect_has "grover_pred_037 F₂" '"F₂": 32' "$out"
expect_has "grover_pred_037 F₃" '"F₃": 1' "$out"
expect_has "grover_pred_037 side condition" '"instance": "32 ≥ 1"' "$out"

out="$("${cqr[@]}" match examples/search_while.cqr --solutions 64 | tr -d '\r')"; rc=$?
expect_exit "match search_while --solutions 64" 1 "$out" "$rc"
expect_has "search_while stage" '"stage":"match"' "$out"
expect_has "search_while code" '"code":"no_matching_pattern"' "$out"
expect_has "search_while location" '"location":"iter"' "$out"
expect_has "search_while expected" '"expected":"bounded(F₃)' "$out"
expect_has "search_while found" '"found":"unbounded"' "$out"
expect_has "search_while dist" '"dist":1' "$out"
expect_has "search_while suggestion" 'max_iter' "$out"
out="$("${cqr[@]}" match examples/search_while.cqr --solutions 64 --text | tr -d '\r')"; rc=$?
expect_exit "match search_while --solutions 64 --text" 1 "$out" "$rc"
expect_has "search_while text Location" 'Location:    field `iter`' "$out"

out="$("${cqr[@]}" match examples/search_or.cqr | tr -d '\r')"; rc=$?
expect_exit "match search_or (M unknown)" 1 "$out" "$rc"
expect_has "search_or found unknown" '"found":"unknown"' "$out"
expect_has "search_or suggestion" '--solutions M' "$out"
out="$("${cqr[@]}" match examples/search_or.cqr --solutions 5 | tr -d '\r')"; rc=$?
expect_exit "match search_or --solutions 5" 0 "$out" "$rc"
expect_has "search_or F₂" '"F₂": 5' "$out"
out="$("${cqr[@]}" match examples/search_or.cqr --solutions 0 | tr -d '\r')"; rc=$?
expect_exit "match search_or --solutions 0 (F₂ ≥ 1 false)" 1 "$out" "$rc"
expect_has "search_or --solutions 0 expected" '"expected":"F₂ ≥ 1"' "$out"

out="$("${cqr[@]}" match examples/allocate_tree.cqr | tr -d '\r')"; rc=$?
expect_exit "match allocate_tree (stops at the surface checker)" 1 "$out" "$rc"
expect_has "allocate_tree match stage" '"stage":"surface"' "$out"

# Stage 5 — `cqr synthesize` (report §6.1.3–6.1.4, §6.3.1): the measured Grover oracle grade
# (Table 3 claims d = 21; the decision-4 scheduler measures 27, DECISIONS.md 2026-10-23),
# the Table 2 budgets of the c∧ = 8 chain, and the two rejections.
out="$("${cqr[@]}" synthesize examples/grover_pred_037.cqr --layers | tr -d '')"; rc=$?
expect_exit "synthesize grover_pred_037" 0 "$out" "$rc"
expect_has "grover_pred_037 oracle grade" '"grade": {"w": 10, "t": 8, "d": 27, "a": 2}' "$out"
expect_has "grover_pred_037 layer 27" 'L27: if c1: CZ x[0] x[3]; if c1: X anc[0]' "$out"
out="$("${cqr[@]}" synthesize examples/grover_pred_037.cqr --json | tr -d '')"; rc=$?
expect_exit "synthesize grover_pred_037 --json" 0 "$out" "$rc"
expect_has "grover_pred_037 IR" '"circuit":{"gates":[{"op":"alloc","q":[8]}' "$out"
out="$("${cqr[@]}" synthesize examples/and_chain_8.cqr --amax 4 | tr -d '')"; rc=$?
expect_exit "synthesize and_chain_8 --amax 4" 0 "$out" "$rc"
expect_has "and_chain_8 --amax 4 grade" '"grade": {"w": 13, "t": 48, "d": 144, "a": 4}' "$out"
out="$("${cqr[@]}" synthesize examples/and_chain_8.cqr --amax 2 | tr -d '')"; rc=$?
expect_exit "synthesize and_chain_8 --amax 2 (infeasible, Table 2 erratum)" 1 "$out" "$rc"
expect_has "and_chain_8 --amax 2 code" '"code":"infeasible_budget"' "$out"
out="$("${cqr[@]}" synthesize examples/search_while.cqr | tr -d '')"; rc=$?
expect_exit "synthesize search_while" 1 "$out" "$rc"
expect_has "search_while synthesize code" '"code":"unbounded_loop"' "$out"

[ "$fail" -eq 0 ] && echo "cli_smoke: all checks passed" || echo "cli_smoke: FAILED"
exit "$fail"
