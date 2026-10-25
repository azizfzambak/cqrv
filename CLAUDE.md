# CQRV — Certified Quantum Realization: project conventions

This repository implements the technical report *Applying Certified Quantum Realization:
A Practical Implementation Guide* (`docs/cqrv_report_revised_v2.docx`; the revision
package `docs/revision_package.docx` records the design decisions that differ from the
proposal). The report is the specification. When code and report disagree, stop and
report the disagreement; do not silently pick one.

## What this project is

A certifying compiler: classical specification (DSL, Chapter 7) → ground signature
(§7.2) → Miller-pattern match against a library of proof-carrying patterns (Chapter 4)
→ instantiation and resource grade (Chapter 3) → oracle synthesis with measurement-based
uncomputation (Chapter 6) → Lean 4 certificate (Chapter 5) → QIR / OpenQASM 3 text
(§5.3, §8.4.3). The MVP is the Grover vertical slice of Chapter 8 with grade
(w, d, t, a) = (15, 230, 72, 7), as measured (report v3; v2 said (10, 74, 72, 2)).

## Layout (one Lean package per chapter-level component)

```
lakefile.lean / lean-toolchain      pinned toolchain and dependency commits (never bump ad hoc)
CQRV/Grades/        §3.1   resource grade (w,d,t,a), ⊕ and ⊗ monoids, budget order, fibre test
CQRV/Realizability/ §2.1–2.3 specifications as relations, (ε,δ)-realization, Theorems 3.3a/b
CQRV/Patterns/      §3.2–3.3 QPLP record, instantiation, grade evaluation
CQRV/DSL/           §7     syntax, parser, surface typing, Cl♭ judgment, extractor ℰ
CQRV/Matching/      §4     normalization, Miller-pattern matcher, anti-unification, repair hints
CQRV/Circuit/       §6, §9.1.1 gate-level IR, denotational semantics, TempLogicalAND, MBU
CQRV/Synthesis/     §6.1   Boolean network → oracle circuit, Bennett schedule, grade computation
CQRV/Certify/       §5, §8.4 parametric lemmas, specialization, certificate record, sorry audit
CQRV/Emit/          §5.3, §8.4.3 QIR / OpenQASM 3 emitter (Adaptive Profile)
CQRV/Grover/        §8     the vertical slice: predicate, QPLP instance, parametric lemma
Apps/cqr/           CLI: check | extract | match | synthesize | certify | emit
tests/              Lean tests (`#guard`, `example`) and the Python differential harness
docs/               report, revision package, SORRIES.md, DECISIONS.md
```

## Rules that are not negotiable

1. **Every change builds.** Run `lake build` before reporting a task as done and paste
   the tail of the log in the summary. A task that does not build is not done.
2. **No invented lemma names.** Before using a Mathlib/Physlib lemma, confirm it exists
   with `#check` or find it with `exact?` / `apply?` / `rw?`. If it does not exist, say
   so and state the obligation instead of guessing a name.
3. **`sorry` is allowed only as a tracked obligation.** Every `sorry` must have an entry
   in `docs/SORRIES.md`: file:line, the statement, which report section it comes from,
   what it depends on, estimated size. Never remove an entry without closing the sorry.
   `lake build` must stay warning-free except for these listed sorries.
4. **No toolchain or dependency bumps** without an explicit instruction; the versions in
   `lean-toolchain` and `lake-manifest.json` are pinned on purpose (risk register, Table 9.5).
5. **Report sections are the source of truth.** Name the section you are implementing in
   the commit message and in a doc-comment at the top of each definition
   (`/-- Report §3.1.1, Table 3.1 -/`). Keep the report's names: `Grade`, `QPLP`,
   `Realizes`, `AncRestore`, `SigmaIn`, `lgg`, `TempLogicalAND`, `MBU`.
6. **Design decisions go to `docs/DECISIONS.md`**, one dated entry each, never only in
   chat: what was decided, why, which alternative was rejected.
7. **Small steps.** One task = one buildable commit. Do not refactor files outside the
   task's scope. Do not start the next task on your own.
8. **Proofs:** state the theorem exactly as in the report first (with explicit hypotheses
   as revised: Theorem 3.1 non-degeneracy, Theorem 3.3a domain/non-expansiveness,
   Lemma 6.3.2 on density operators). Attempt the proof only when asked; otherwise leave
   a tracked `sorry` and list the sub-lemmas you would need.
9. **Tests accompany code.** Pure functions get `#guard`/`example` tests in `tests/`;
   synthesized circuits are checked against the Python statevector harness
   (`tests/diff/`) for n ≤ 12 before any grade is claimed.
10. **Never claim a certificate is "verified" in output text unless the proof term is
    sorry-free and axiom-audited** (`#print axioms`) — the report's master discipline (§9.5.1).

## How to end every task

Reply with: (a) files changed, (b) `lake build` tail, (c) test output, (d) new or closed
entries in SORRIES.md, (e) open questions for the reviewer. Keep it under 40 lines; the
reviewer reads this before anything else.
