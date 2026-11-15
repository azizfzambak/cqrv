# Stage 23 — The restoration algebra (PHASE2_SPEC §B.2; Track B, Paper 2; milestone M4)

PHASE2_SPEC.md §B.2. Report: §6.2.1, §6.2.3 (Table 4), §6.2.4, §6.3.2. PHASE2_ROADMAP row 23.
Written at the 22c review (2026-11-15) by the reviewer, under the author's delegation.

Stage 23 has three tasks, one commit each:
- **23a**, composition laws for clean restoration, is specified here;
- **23b**, the three regimes, is outlined here and gets its detailed text at the 23a review;
- **23c**, the 8n − 24 theorem, is outlined in §B.2 and gets its detailed text at the 23b review.

Precondition: main = the 22c review commit. Start with `git switch -c stage-23a main`.
Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows:
`LEAN_NUM_THREADS=4`.

The process is the delegated one:
1. The reviewer session sends the prompt.
2. You implement, and say "ready for CI".
3. The reviewer audits and runs CI.
4. You commit on the reviewer's prompt.

**Invariants of Stage 23** (as Stage 22):
- No existing theorem statement changes; `Circuit.WF` and `channelDenote` are unchanged.
- No certificate, CLI or harness change.
- The `cqr` closure is unchanged: the new modules are Physlib-side.
- No new CI step; the pass mark stays 19 PASS, 0 FAIL, 4 n/a.
- No `sorry`.
- If a statement here is false, give the counterexample and the corrected form.
- CLAUDE.md rule 2.
- Keep Stage 22's conventions: (-1 : ℂ), `.data i.val`, `by_cases h : … = true`, no `rw` inside
  `decide`, the symplectic representation, `ZMod 2`.

---

## 23a — Composition laws for clean restoration (`CQRV/Circuit/RestoreAlgebra.lean`, new)

### N1. Block lists

**`ancRestore_list`.** For a list of circuits `Cs`, each with `bitsOk` and
`AncRestore n a Cᵢ Uᵢ`, the left fold `Cs.foldl Circuit.append init` restores its ancillas, and
applies the product of the Uᵢ in reverse order after the initial U. It is the generalization of
`ancRestore_foldl` (which iterates one block) to any list, by `AncRestore.comp`. State the product
with `List.foldl` or `List.prod` of the reversed list, whichever makes the proof direct.

### N2. Restoration under measurement with a mixed data action

**`ancRestoreMix_of_kraus`.** Let C be well formed, and let l : branches → ℂ and
U : branches → 𝐔[Reg n] satisfy, for every branch c,
`krausOps n a C.nBits C.gates c * ancProj n a = l c • ((U c).val ⊗ₖ (ancZero a).m)`. Then for
every data state ρ, `(channelDenote n a C (ρ ⊗ᴹ ancZero a)).m = ∑ c, ‖l c‖² • ((U c ◃ ρ) ⊗ᴹ
ancZero a).m`. Prove also `∑ c, ‖l c‖² = 1`, which follows from the completeness of the Kraus
operators and the clean input.

Use the matrix form. Physlib's `MState` has no convex-combination API that you need to introduce
for this; if one exists (rule 2), you may state the mixture as an `MState` too.

**Corollaries.**
- When every U c equals U, the conclusion is `AncRestore n a C U`. This re-derives the case of
  `ancRestore_of_kraus`; leave the existing proof as it is.
- **`mbu_uncorrected`.** With the hypotheses of `mbu_general` at φ = 1, but O = [] (that is,
  `mbuUncompute t j []`, the reset without correction), the data undergoes
  ρ ↦ ½ ρ + ½ (phaseOracle f) ρ (phaseOracle f)ᴴ: the ancilla is restored, and the data is
  dephased in the basis of f. Reuse the per-branch computation of `MBUGeneral.lean`.

### N3. Widening, or ancilla reuse

**`AncRestore.widen`.** Suppose every qubit of every gate of C is a data qubit or `.anc i` with
i < a, and `AncRestore n a C U` holds. Then `AncRestore n (a + b) C U` holds.
- Route: `Reg (a + b) ≃ Reg a × Reg b` (through `Fin.append`, or the equivalence Mathlib provides;
  rule 2).
- Under that equivalence, every Kraus operator of C on `Reg n × Reg (a + b)` is the Kraus operator
  on `Reg n × Reg a`, tensored with 1 on `Reg b`; the clean projector factorizes the same way.
- Then use `ancRestore_of_kraus`, or the channel equality directly.

**`AncRestore.comp_widen`.** Two blocks certified on a₁ and a₂ ancillas compose on max a₁ a₂.
This is the "ancilla reuse across certified blocks" of the roadmap row.

### N4. Tests (`tests/CQRVTests/RestoreAlgebra.lean`, new)

- `#guard_msgs` on the axioms of `ancRestore_list`, `ancRestoreMix_of_kraus`, `mbu_uncorrected`,
  `AncRestore.widen` and `AncRestore.comp_widen`.
- `mbu_uncorrected` at the AND (`mbuCircuit` without its CZ).
- `AncRestore.widen` applied to the 22a linear instance (from a = 1 to a = 2).
- A two-block list: the AND oracle of `mbuCircuit` followed by the parity instance.

### 23a Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the axioms as in N4.

Stop and ask in any of these cases:
- `AncRestore.widen` needs more than about 400 lines, or the module more than about 1 000 (then
  propose a split);
- a statement of mine is false;
- a Lean process above 8 GB.

---

## 23b — The three regimes (outline; detailed at the 23a review)

PHASE2_SPEC §B.2.
- **Dirty.** `AncRestoreDirty`; dirty ⇒ clean; sequential composition; a dirty instance (a phase
  gadget that uses a dirty ancilla twice so that its value cancels, for example CNOT(x0 → d);
  CZ(d, x1); CNOT(x0 → d); CZ(d, x1) gives the phase (−1)^{x0 x1} for every d).
- **Conditionally clean**, defined after Khattar–Gidney §2 against the invariant in
  `MczFewAll.lean`.
- **Commutation of blocks on disjoint qubits.**

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
