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
# and `cqr emit` (Stage 8a): QIR / QASM of the Grover circuit.
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

# Stage 5b — diffusion and Grover circuit (report §8.2, §3.2.4; DECISIONS.md 2026-10-24): the
# measured grades (Table 3.3 claims (10, 16, 28, 2) for D₈ and (10, 74, 72, 2) for r⋆ = 2).
out="$("${cqr[@]}" synthesize --diffusion 8 | tr -d '\r')"; rc=$?
expect_exit "synthesize --diffusion 8" 0 "$out" "$rc"
expect_has "diffusion 8 V1 grade" '"grade": {"w": 15, "t": 28, "d": 89, "a": 7}' "$out"
out="$("${cqr[@]}" synthesize --diffusion 8 --amax 3 | tr -d '\r')"; rc=$?
expect_exit "synthesize --diffusion 8 --amax 3" 0 "$out" "$rc"
expect_has "diffusion 8 V2 grade" '"grade": {"w": 11, "t": 52, "d": 157, "a": 3}' "$out"
out="$("${cqr[@]}" synthesize --diffusion 8 --amax 2 | tr -d '\r')"; rc=$?
expect_exit "synthesize --diffusion 8 --amax 2 (infeasible)" 1 "$out" "$rc"
expect_has "diffusion 8 --amax 2 code" '"code":"infeasible_budget"' "$out"
out="$("${cqr[@]}" synthesize examples/grover_pred_037.cqr --grover | tr -d '\r')"; rc=$?
expect_exit "synthesize grover_pred_037 --grover" 0 "$out" "$rc"
expect_has "grover r_star" '"r_star": 2' "$out"
expect_has "grover iteration grade" '"iteration": {"w": 15, "t": 36, "d": 116, "a": 7}' "$out"
expect_has "grover oracle ⊕ diffusion" '"oracle_plus_diffusion": {"w": 15, "t": 36, "d": 116, "a": 7}' "$out"
expect_has "grover circuit grade" '"circuit": {"w": 15, "t": 72, "d": 230, "a": 7}' "$out"
out="$("${cqr[@]}" synthesize examples/grover_pred_037.cqr --grover --iterations 1 | tr -d '\r')"; rc=$?
expect_exit "synthesize grover_pred_037 --grover --iterations 1" 0 "$out" "$rc"
expect_has "grover --iterations 1" '"iterations": 1' "$out"
"${cqr[@]}" synthesize examples/search_or.cqr --grover >/dev/null 2>&1; rc=$?
expect_exit "synthesize search_or --grover (M unknown, no --iterations)" 2 "" "$rc"

# Stage 8a — `cqr emit` (report §8.4.3): QIR Adaptive Profile and OpenQASM 3 of the Grover
# circuit at r* = 2; one terminal measurement block over the 8 data qubits. The re-parse against
# the Lean IR is scripts/check_emit.sh.
out="$("${cqr[@]}" emit examples/grover_pred_037.cqr --format qir | tr -d '')"; rc=$?
expect_exit "emit grover_pred_037 --format qir" 0 "$out" "$rc"
expect_has "qir adaptive profile" '"qir_profiles"="adaptive_profile"' "$out"
expect_has "qir required_num_qubits" '"required_num_qubits"="15"' "$out"
expect_has "qir required_num_results" '"required_num_results"="26"' "$out"
expect_has "qir dynamic_qubit_management" '!"dynamic_qubit_management", i1 false' "$out"
nblk=$(grep -c '^measurements:$' <<<"$out")
nmz=$(sed -n '/^measurements:$/,/^  br label %output$/p' <<<"$out" | grep -c '__quantum__qis__mz__body')
[ "$nblk" -eq 1 ] && [ "$nmz" -eq 8 ] && ok "qir: one terminal measurement block, 8 mz"   || bad "qir: $nblk measurement blocks, $nmz mz in the terminal block (expected 1, 8)"
out="$("${cqr[@]}" emit examples/grover_pred_037.cqr --format qasm --iterations 1 | tr -d '')"; rc=$?
expect_exit "emit grover_pred_037 --format qasm --iterations 1" 0 "$out" "$rc"
expect_has "qasm header" 'OPENQASM 3.0;' "$out"
expect_has "qasm registers" 'qubit[7] anc;' "$out"
expect_has "qasm conditional" 'if (c[0]) { cz anc[0], x[7]; }' "$out"
expect_has "qasm terminal measurement" 'out = measure x;' "$out"
"${cqr[@]}" emit examples/grover_pred_037.cqr >/dev/null 2>&1; rc=$?
expect_exit "emit without --format" 2 "" "$rc"
out="$("${cqr[@]}" emit examples/search_or.cqr --format qir | tr -d '')"; rc=$?
expect_exit "emit search_or (M unknown: no match, as cqr match)" 1 "$out" "$rc"
expect_has "emit search_or code" '"code":"no_matching_pattern"' "$out"
"${cqr[@]}" emit examples/search_or.cqr --format qasm --solutions 5 >/dev/null; rc=$?
expect_exit "emit search_or --solutions 5" 0 "" "$rc"
out="$("${cqr[@]}" emit examples/search_while.cqr --format qir --solutions 64 | tr -d '')"; rc=$?
expect_exit "emit search_while --solutions 64 (no match)" 1 "$out" "$rc"
expect_has "emit search_while code" '"code":"no_matching_pattern"' "$out"

[ "$fail" -eq 0 ] && echo "cli_smoke: all checks passed" || echo "cli_smoke: FAILED"
exit "$fail"
