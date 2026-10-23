# Stage 0 — Repository, toolchain, CI

Report sections: §9.1 (Phase I), §9.1.1, §9.5.1, §9.5.3, Table 9.5 (dependency-drift row).
Read `CLAUDE.md`, `docs/PLAN.md` (Stage 0) and `docs/DECISIONS.md` before starting.
Work on branch `stage-0`; the whole stage is one buildable commit (one PR).

## Already decided — do not reopen (DECISIONS.md, 2026-10-21)

1. If Physlib / Lean-QuantumInfo does not build against the pinned Mathlib, it is left out
   and Stage 2 starts from an abstract `Channel` interface (named trust boundary).
2. The metric on specification outputs will be a type parameter; MVP uses the discrete case.
   Nothing to implement in this stage.
3. SHA3-256 will be implemented in Lean. Do not add any Python or external hashing step
   to CI or to the repository.

## Repository state you start from

`CLAUDE.md`, `README.md`, `.gitignore`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`docs/SORRIES.md` (header only) and both report documents already exist in `docs/`.
Do **not** recreate or overwrite them: append to DECISIONS.md, leave SORRIES.md's table
empty, and only update README.md's "Status" line at the end. If the repo is not yet a git
repository, `git init` it first.

## Environment

The reviewer works on Windows. All scripts are bash and must run both in GitHub Actions
(ubuntu) and in Git Bash on Windows (no GNU-only flags without a fallback; LF line endings —
add a `.gitattributes` with `*.sh text eol=lf`). The first `lake exe cache get` downloads
several GB of Mathlib cache and is the longest step of this stage; run it once, in the
background if your shell allows, and do not retry it in a loop.

## Tasks

1. **Toolchain and Mathlib.** Pick the latest Mathlib *release tag* (not `master`) and set
   `lean-toolchain` to exactly the toolchain that tag's own `lean-toolchain` names — if that
   differs from the latest stable Lean release, Mathlib's choice wins. Use `lakefile.lean`
   (not `lakefile.toml`), require Mathlib at that tag, run `lake update` once, commit
   `lake-manifest.json`. Use `lake exe cache get`; never build Mathlib from source.
   DECISIONS.md entry: Lean version, Mathlib tag + commit hash, why this tag.

2. **Physlib check.** Find out where Lean-QuantumInfo currently lives (standalone repo, or
   merged into Physlib / PhysLean — the report says "now part of Physlib", verify it, do not
   assume). Record the exact repository URL and commit you tested. In a throwaway directory
   outside the repo, try building it against the Mathlib commit from step 1.
   - Builds → add it to the lakefile pinned to that commit, and import one module
     (e.g. its density-matrix or CPTP file) in a scratch check to confirm it compiles.
   - Does not build → leave it out. DECISIONS.md entry: the error (first ~10 lines),
     the Mathlib version it does require, and "Stage 2 uses the abstract `Channel`
     interface per the 2026-10-21 decision".
   Timebox: if the build is still going/failing after 3 fix attempts, stop and record
   it as incompatible. Do not change our Mathlib pin to make Physlib fit.

3. **Package layout.** One Lake package `cqrv` with the modules in CLAUDE.md:
   `CQRV/{Grades,Realizability,Patterns,DSL,Matching,Circuit,Synthesis,Certify,Emit,Grover}`,
   each with a `Basic.lean` (or same-named root file) containing only a module doc-comment
   naming its report sections (copy them from the CLAUDE.md layout table), plus a root
   `CQRV.lean` importing all of them. No definitions yet.
   Note: §9.5.3(i) says "one Lean 4 package per chapter-level component". The reviewer has
   decided (2026-10-21): one Lake package with one top-level module tree per component; do
   not create ten Lake packages. Record this in DECISIONS.md as decided by the reviewer
   (Rejected: one Lake package per component — ten manifests to pin, no gain for the MVP).
   - `Apps/cqr/Main.lean`: `lean_exe cqr` that prints usage listing
     `check | extract | match | synthesize | certify | emit` and exits with code 2 and
     "not implemented (Stage N)" for each. Nothing more.
   - `tests/`: a `lean_lib CQRVTests` with one trivial `#guard` so the test target exists.

4. **Sorry audit script** `scripts/check_sorries.sh` (bash, runs in CI and in Git Bash on
   Windows): counts `sorry` occurrences per `.lean` file (ignore comments and the word inside
   identifiers/strings as best a grep allows; document the limitation in the script header),
   and fails unless, for every file, the count equals the number of rows in `docs/SORRIES.md`
   with that file path and Status ≠ closed. File-level matching, not line-level (line numbers
   drift). With an empty table, any `sorry` fails. Add a self-test: temporarily introduce a
   sorry, show the script fails, remove it.

5. **Warning check.** `lake build` output must contain no warnings other than
   "declaration uses 'sorry'" (CLAUDE.md rule 3). Implement as a grep over the build log in
   the same script or a sibling one.

6. **Axiom audit** `scripts/print_axioms.sh` (or a Lean script run via `lake env lean`):
   for every `theorem` declared in modules under `CQRV/Certify`, print `#print axioms`.
   It must succeed and print "no theorems in CQRV.Certify" when there are none (the case
   now). In Stage 0 it only prints; it becomes blocking on `sorryAx`/unlisted axioms in
   Stage 8 — say so in the script header.

7. **GitHub Actions** `.github/workflows/ci.yml`:
   - Job `pinned` (blocking, on push/PR): checkout → install elan with the pinned toolchain
     (`leanprover/lean-action` is fine) → `lake exe cache get` → `lake build` (tee the log)
     → warning check → sorry check → axiom printout → `pip install -r tests/diff/requirements.txt`
     → simulator self-test (step 8).
   - Job `candidate` (non-blocking, `continue-on-error: true`, monthly `schedule` +
     `workflow_dispatch` only): same build against the newest Mathlib release tag in a
     temporary copy of the lakefile. This implements Table 9.5's "CI green on both pinned and
     candidate toolchains"; it must never modify the committed pins (rule 4).

8. **Python harness placeholder** `tests/diff/`: `requirements.txt` with an exact pinned numpy
   version; `statevector.py` with a minimal simulator (apply H, X, CNOT to an n-qubit state,
   n ≤ 12) and a `--selftest` that checks H·H = I and a Bell state; README note that the IR
   executor comes in Stage 5. Run it with `python -I` style invocation from the repo root.

9. **Docs.** Verify the two `.docx` files are in `docs/` (they are — do not copy anything).
   Update README "Status" to "Stage 0 complete". Do not touch PLAN.md.

## Acceptance

- `lake build` green and warning-free; `lake build CQRVTests` and `lake build cqr` green.
- `scripts/check_sorries.sh` passes on the clean tree and fails on the self-test sorry.
- Axiom script runs and prints the "no theorems" line.
- `python tests/diff/statevector.py --selftest` passes.
- DECISIONS.md has new dated entries: toolchain/Mathlib pin, Physlib outcome, package-layout
  interpretation, CI design (pinned + candidate). Format per PLAN.md §5.
- SORRIES.md table still empty (no sorry expected in Stage 0).

## Stop conditions

- More than 3 build–fix rounds on the same error → stop and report (PLAN.md §1).
- Anything in the report contradicting CLAUDE.md or this task → stop and report, do not pick.
- Do not start Stage 1.

## Closing reply

CLAUDE.md "How to end every task" format, under 40 lines: (a) files changed, (b) last lines
of `lake build`, (c) test / script outputs, (d) SORRIES.md changes (expected: none),
(e) open questions — at minimum the Physlib outcome.
