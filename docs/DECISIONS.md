# Design decisions

One dated entry per decision. Never delete entries; supersede them with a new entry that references the old one.

## 2026-10-21 — Planning decisions taken before Stage 0
Decision: (1) if Physlib / Lean-QuantumInfo does not build against the pinned Mathlib, start with an abstract `Channel` interface (named trust boundary) and revisit when it does; (2) the metric on specification outputs is a type parameter, MVP uses the discrete case (ε = 0); (3) SHA3-256 for certificate hashes is implemented in Lean (single-language TCB).
Why: see docs/PLAN.md §4.
Rejected: Python front end / external hashing tool (larger TCB, FFI trust gap).
Report §: 9.1.1, 2.1.2, 8.4.2, 9.5.3.

## 2026-10-21 — Toolchain and Mathlib pin (Stage 0)
Decision: `lean-toolchain` = `leanprover/lean4:v4.35.0`; Mathlib required in `lakefile.lean` at release tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (recorded in `lake-manifest.json`). Mathlib oleans come from `lake exe cache get`; Mathlib is never built from source.
Why: `v4.35.0` is the newest Mathlib release tag (`v4.36.0-rc1` is a pre-release); the toolchain is exactly the one that tag's own `lean-toolchain` names. It coincides with the latest stable Lean release (v4.35.0), so no override was needed. A release tag gives a reproducible, cache-backed pin (Table 9.5, dependency-drift row; §9.5.1 reference configuration).
Rejected: Mathlib `master` (moves daily, breaks reproducibility); `v4.36.0-rc1` (release candidate); `lakefile.toml` (the task prescribes `lakefile.lean`).
Report §: 9.1, 9.5.1, 9.5.3(i), Table 9.5.

## 2026-10-21 — Package layout: one Lake package, one module tree per component (decided by the reviewer)
Decision: a single Lake package `cqrv` with one top-level module tree per chapter-level component (`CQRV/{Grades,Realizability,Patterns,DSL,Matching,Circuit,Synthesis,Certify,Emit,Grover}`), root `CQRV.lean`, plus `lean_lib CQRVTests` (`tests/`) and `lean_exe cqr` (`Apps/cqr/Main.lean`). This is the reviewer's interpretation of §9.5.3(i) "one Lean 4 package per chapter-level component".
Why: component boundaries are kept as module trees; one manifest means one set of pins to maintain and audit.
Rejected: one Lake package per component — ten manifests to pin, no gain for the MVP.
Report §: 9.5.3(i).

## 2026-10-21 — CI design: pinned (blocking) + candidate (non-blocking, monthly)
Decision: `.github/workflows/ci.yml` has two jobs. `pinned` (push / pull_request, blocking): install elan → `lake exe cache get` → `lake build` (log tee'd) → `scripts/check_warnings.sh` → `scripts/check_sorries.sh` (+ `--self-test`) → `scripts/print_axioms.sh` → `pip install -r tests/diff/requirements.txt` → `python -I tests/diff/statevector.py --selftest`. `candidate` (monthly `schedule` + `workflow_dispatch`, `continue-on-error: true`): `scripts/candidate_build.sh` copies the tree to a temp directory, retargets the copy to the newest Mathlib release tag and that tag's toolchain, and runs the same build and checks; committed pins are never modified (CLAUDE.md rule 4). The sorry audit is file-level (count per file = open rows in SORRIES.md); the axiom printout is informational until Stage 8, when it becomes blocking on `sorryAx`/unlisted axioms. No Python or external hashing step besides the test-only simulator (2026-10-21 decision 3).
Why: implements Table 9.5 "Monthly: CI green on both pinned and candidate toolchains" without letting upstream drift block day-to-day work.
Rejected: candidate on every push (slow, non-actionable red builds); line-level sorry matching (line numbers drift); `leanprover/lean-action` (plain elan install keeps every step explicit and reproducible in Git Bash). Open: §9.5.3(ii) asks for candidate-toolchain checking "on each commit" for certificates — to be revisited at Stage 8 (see Stage 0 closing reply).
Report §: 9.5.1, 9.5.3(ii), Table 9.5.

## 2026-10-21 — Physlib / Lean-QuantumInfo: builds against the Mathlib pin, added
Decision: Lean-QuantumInfo is no longer a standalone project: `github.com/Timeroot/Lean-QuantumInfo` (last push 2026-09-10, toolchain v4.28.0) states in its README that it merged with PhysLean in March 2026 to form Physlib, and `github.com/leanprover-community/physlib` contains the `QuantumInfo/` tree (verified, not assumed). Tested commit: `leanprover-community/physlib@96a6bc5e3c50a2856c64a6c9951c0a1c23790b58` (master, 2026-10-21), whose own manifest pins Mathlib `v4.35.0` = `56a005855ea17e0b0958f73ec801ae140b0a1679`, i.e. our pin, with identical transitive dependency commits. In a throwaway clone (outside the repo), `lake build QuantumInfo` completed (3915 jobs, Mathlib from `lake exe cache get`, no Mathlib source build). Added to `lakefile.lean` as `require Physlib … @ "96a6bc5e…"` (manifest diff: only the Physlib entry; Mathlib unchanged). Scratch check (`.lake/scratch/PhyslibCheck.lean`, not committed) importing `QuantumInfo.Channels.CPTP` and `QuantumInfo.States.Mixed.MState` compiles; `#check` resolves `CPTPMap`, `CPTPMap.compose`, `MState`. Stage 2 can therefore build `Channel` on Physlib's `CPTPMap`/`MState`; the 2026-10-21 abstract-`Channel` fallback is not triggered.
Why: §9.1.1 reuses Physlib's density matrices, CPTP maps, partial trace and trace distance instead of rebuilding them.
Environment note: the first attempt on the reviewer's Windows machine (20 logical CPUs, 16 GB RAM, ~18 GB commit limit) failed with `failed to read file '…\Std\Internal\ForIn\Basic.ir.sig': Invalid argument` and similar read errors on toolchain/dependency `.olean`/`.ir` files — memory exhaustion from parallel Lean processes, not an incompatibility. Fix (attempt 1 of 3): `LEAN_NUM_THREADS=4 lake build …` succeeded with no source change. Use the same setting for Physlib builds on Windows.
Physlib's own sorries: Physlib compiles with `-Dwarn.sorry=false` and contains sorries (grep: ~14 occurrences in 5 `QuantumInfo` files, none in `Channels/CPTP.lean` or `States/Mixed/MState.lean`). They are outside SORRIES.md by design (`scripts/check_sorries.sh` never scans `.lake/`); any certificate that depends on one is caught by the Stage 8 axiom audit (`sorryAx`, blocking from Stage 8).
Rejected: abstract `Channel` interface as the starting point (unnecessary while Physlib builds); changing our Mathlib pin to fit Physlib (not needed, and forbidden by the task).
Report §: 9.1.1, 5.2.3, 9.5.1, Table 9.5.

## 2026-10-21 — Warning check scoped to our sources (reviewer decision)
Decision: `scripts/check_warnings.sh` fails only on warnings whose source path is `CQRV.lean` or under `CQRV/`, `Apps/`, `tests/` (relative or absolute, `\` normalized), excluding "declaration uses `sorry`" (either quoting). Warnings from dependencies (anything under `.lake/`, or with another package's relative paths) and warnings naming no file are ignored.
Why: CLAUDE.md rule 3 governs our code; dependency warnings (Mathlib, Physlib) are not actionable here and must not block CI or the choice of dependency.
Rejected: grep over the whole build log (rejects dependencies for their own lint warnings).
Report §: 9.5.1.
