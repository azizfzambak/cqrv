#!/usr/bin/env bash
# Sorry audit — report §9.5.1 (sorry discipline), CLAUDE.md rule 3.
#
# Counts `sorry` tokens per .lean file in the repository (never inside .lake/) and fails unless,
# for every file, the count equals the number of rows in docs/SORRIES.md whose File:line
# column names that file and whose Status is not "closed". Matching is per file, not per
# line, because line numbers drift. With an empty table, any `sorry` fails.
#
# Limitations (this is a lexical scan, not a Lean parse):
#   * `--` line comments and `/- … -/` block comments (nested, doc-comments included) are
#     skipped; "…" string literals (with \" escapes) are skipped.
#   * `sorry` counts only as a whole token: not when adjacent to an identifier character
#     [A-Za-z0-9_'.!?], so `sorryAx`, `Foo.sorry`, `no_sorry` are ignored.
#   * Not handled: char literals containing `"` or `-`, raw strings r#"…"#, `sorry`
#     produced by macros or tactics defined elsewhere. Those are caught by the axiom audit
#     (scripts/print_axioms.sh, `sorryAx`), which becomes blocking in Stage 8.
#
# Usage:  scripts/check_sorries.sh              # audit the tree
#         scripts/check_sorries.sh --self-test  # show that an untracked sorry fails
# Portable: bash + POSIX awk/sort/find; runs on ubuntu (mawk) and Git Bash on Windows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SORRIES_MD="${SORRIES_MD:-$ROOT/docs/SORRIES.md}"  # override only for the self-test

count_sorries() {
  # Prints "<relative path> <count>" for every .lean file with count > 0.
  # .lake/ (dependencies such as Mathlib/Physlib, build outputs) is pruned at any depth:
  # dependency sorries are not ours to track; see docs/DECISIONS.md (Stage 0, warning scope).
  (cd "$ROOT" && find . \( -name .lake -o -name lake-packages -o -name .git -o -name .venv \) -prune       -o -name '*.lean' -print \
      | sed 's#^\./##' | LC_ALL=C sort) | while IFS= read -r f; do
    n=$(tr -d '\r' < "$ROOT/$f" | awk '
      function isid(c) { return c ~ /[A-Za-z0-9_.!?'"'"']/ }
      BEGIN { depth = 0; instr = 0; n = 0 }
      {
        line = $0; L = length(line); i = 1
        while (i <= L) {
          c = substr(line, i, 1); c2 = substr(line, i, 2)
          if (depth > 0) {
            if (c2 == "/-") { depth++; i += 2 }
            else if (c2 == "-/") { depth--; i += 2 }
            else i++
          } else if (instr) {
            if (c == "\\") i += 2
            else { if (c == "\"") instr = 0; i++ }
          } else if (c2 == "--") {
            break
          } else if (c2 == "/-") {
            depth = 1; i += 2
          } else if (c == "\"") {
            instr = 1; i++
          } else if (substr(line, i, 5) == "sorry" && (i == 1 || !isid(substr(line, i - 1, 1))) \
                     && (i + 5 > L || !isid(substr(line, i + 5, 1)))) {
            n++; i += 5
          } else i++
        }
      }
      END { print n }')
    if [ "$n" -gt 0 ]; then echo "$f $n"; fi
  done
}

expected_sorries() {
  # Prints "<path> <count>" from docs/SORRIES.md rows with Status != closed.
  tr -d '\r' < "$SORRIES_MD" | awk -F'|' '
    /^[[:space:]]*\|/ {
      file = $2; status = $7
      gsub(/^[[:space:]`]+|[[:space:]`]+$/, "", file)
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", status)
      if (file == "" || file == "File:line" || file ~ /^-+$/) next
      sub(/:[0-9]+(-[0-9]+)?$/, "", file); sub(/^\.\//, "", file)
      if (tolower(substr(status, 1, 6)) == "closed") next
      cnt[file]++
    }
    END { for (f in cnt) print f, cnt[f] }' | LC_ALL=C sort
}

audit() {
  local actual expected
  actual="$(count_sorries)"
  expected="$(expected_sorries)"
  # Join on path; a missing side counts as 0.
  if printf '%s\n--\n%s\n' "$actual" "$expected" | awk '
      $0 == "--" { side = 2; next }
      NF == 2 { if (side == 2) e[$1] = $2; else a[$1] = $2; seen[$1] = 1 }
      END {
        bad = 0
        for (f in seen) {
          av = (f in a) ? a[f] : 0; ev = (f in e) ? e[f] : 0
          if (av != ev) { printf "MISMATCH %s: %d sorry in file, %d open row(s) in docs/SORRIES.md\n", f, av, ev; bad = 1 }
        }
        exit bad
      }'; then
    echo "check_sorries: OK ($(printf '%s' "$actual" | awk 'NF==2{s+=$2} END{print s+0}') tracked sorry, all files match docs/SORRIES.md)"
    return 0
  else
    echo "check_sorries: FAIL — every sorry needs an open row in docs/SORRIES.md (CLAUDE.md rule 3)"
    return 1
  fi
}

PROBE="$ROOT/CQRV/SorrySelfTestProbe.lean"
TMP_TABLE="$ROOT/.lake/sorries-selftest.md"

self_test() {
  trap 'rm -f "$PROBE" "$TMP_TABLE"' EXIT
  mkdir -p "$ROOT/.lake"
  echo "self-test 1: sorry only in comments/strings/identifiers must pass"
  printf '%s
' '-- sorry' '/- sorry /- nested sorry -/ sorry -/' 'def s := "sorry"'     'def no_sorry := 0' > "$PROBE"
  audit || { echo "self-test FAILED: false positive"; exit 1; }
  echo "self-test 2: an untracked sorry must fail"
  printf '%s
' 'theorem probe : True := sorry' > "$PROBE"
  if audit; then echo "self-test FAILED: untracked sorry was accepted"; exit 1; fi
  echo "self-test 3: the same sorry with an open row must pass"
  { cat "$ROOT/docs/SORRIES.md"
    echo '| CQRV/SorrySelfTestProbe.lean:1 | probe | — | — | 1 | open |'; } > "$TMP_TABLE"
  SORRIES_MD="$TMP_TABLE" audit || { echo "self-test FAILED: tracked sorry rejected"; exit 1; }
  echo "self-test 4: a closed row does not cover the sorry"
  { cat "$ROOT/docs/SORRIES.md"
    echo '| CQRV/SorrySelfTestProbe.lean:1 | probe | — | — | 1 | closed (abc123) |'; } > "$TMP_TABLE"
  if SORRIES_MD="$TMP_TABLE" audit; then echo "self-test FAILED: closed row accepted"; exit 1; fi
  rm -f "$PROBE" "$TMP_TABLE"
  echo "self-test 5: clean tree must pass again"
  audit || { echo "self-test FAILED: clean tree rejected"; exit 1; }
  echo "check_sorries self-test: OK"
}

case "${1:-}" in
  --self-test) self_test ;;
  "") audit ;;
  *) echo "usage: $0 [--self-test]" >&2; exit 2 ;;
esac
