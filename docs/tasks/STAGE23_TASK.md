# Stage 23 — The restoration algebra (PHASE2_SPEC §B.2; Track B, Paper 2; milestone M4)

PHASE2_SPEC.md §B.2. Report: §6.2.1, §6.2.3 (Table 4), §6.2.4, §6.3.2. PHASE2_ROADMAP row 23.
Written at the 22c review (2026-11-15) by the reviewer, under the author's delegation.

Stage 23 has three tasks, one commit each:
- **23a**, composition laws for clean restoration, is specified here;
- **23b**, the three regimes, is specified below (written at the 23a review);
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

## 23b — The three regimes (written at the 23a review, 2026-11-15)

PHASE2_SPEC §B.2, the "23a done" paragraph and its refinement. Precondition: main = the 23a review
commit. Start with `git switch -c stage-23b main`. New module `CQRV/Circuit/RestoreRegimes.lean`
(Physlib-side), importing `RestoreAlgebra`. The invariants of Stage 23 hold.

### P1. Dirty restoration

- **`AncRestoreDirty n a C U`.** `∀ ρ σ, channelDenote n a C (ρ ⊗ᴹ σ) = (U ◃ ρ) ⊗ᴹ σ`.
- **`ancRestoreDirty_of_kraus`.** If every Kraus operator is l c • (U.val ⊗ₖ 1) on the whole
  space, then the circuit is dirty restoring. Reuse the proof of `ancRestoreMix_of_kraus` with the
  projector replaced by 1. A measurement-free circuit whose `unitaryDenote` is U ⊗ 1 is the
  common case.
- **Laws:**
  - `AncRestoreDirty.toClean` (σ := ancZero a);
  - `AncRestoreDirty.comp` (sequential composition);
  - `AncRestoreDirty.widen`, if it follows cheaply from 23a's machinery.
- **The instance.** A dirty phase gadget on n = 2, a = 1:
  `[.cnot (.data 0) (.anc 0), .cz (.anc 0) (.data 1), .cnot (.data 0) (.anc 0), .cz (.anc 0)
  (.data 1)]` is `AncRestoreDirty 2 1 _ czU`. The phase is (−1)^{(d ⊕ x0) x1 ⊕ d x1} =
  (−1)^{x0 x1} for every ancilla value d. This is the phase form of "toggle detection": the dirty
  ancilla is used twice, so its value cancels.
- **`reset_not_dirty`.** A circuit that ends with `measure t j; ifBit j (.x t)` on an ancilla t,
  with a ≥ 1, is not dirty restoring for any U, because its output ancilla t is |0⟩ in every
  branch. Corollary: `mbuCircuit` is not dirty restoring. This is the theorem behind the report's
  "dirty ancillas cannot use MBU" (§6.2.3).

### P2. Conditionally clean restoration

- **`condSubspace cond`.** The projector onto V_cond = span{|x, w⟩ : cond x = true → w = 0}, a
  diagonal 0/1 matrix on `Reg n × Reg a`.
- **`AncRestoreCond n a C U cond`.** For every state ω on `Reg n × Reg a` with
  `condSubspace cond * ω.m * condSubspace cond = ω.m`, the channel acts as
  `(channelDenote n a C ω).m = (U.val ⊗ₖ 1) * ω.m * (U.val ⊗ₖ 1)ᴴ`.
- **The hierarchy:**
  - `AncRestoreDirty.toCond`: dirty is conditionally clean for every cond. Prove that dirty
    restoration holds on every state, because product states span, or prove it directly through
    Kraus.
  - `AncRestoreCond.toClean`: at cond ≡ true, V is the clean subspace, which gives
    `AncRestore n a C U`.
  - Each implication is strict, shown by the instances below.
- **`AncRestoreCond.comp`.** If C₁ is conditionally clean with U₁ under cond, C₂ with U₂ under
  cond', and U₁ ⊗ 1 maps V_cond into V_cond' (true for instance when U₁ is diagonal and
  cond' = cond), then the composite is conditionally clean with U₂ U₁ under cond.
- **Instances:**
  - `[.cz (.data 0) (.anc 0)]` is conditionally clean with U = 1 under cond = x0. It is not dirty
    restoring (on x0 = 1, w = 1 it gives −1), and it is clean.
  - The KG bridge: a lemma that restates `Inv.cond` of `MczFewAll.lean` as "the value of a marked
    t > 0 is fixed by the indices below it" at the level of basis values, so that Paper 2 can cite
    the code's invariant in the regime's terms. If this costs more than about 150 lines, write it
    as a documented remark instead.

### P3. Commutation on disjoint qubits (optional)

`channelDenote_append_comm`: two well-formed circuits acting on disjoint sets of qubits, with
disjoint classical bits after the shift of `append`, have commuting channels. If this needs more
than about 300 lines (a split of `Reg n` like 23a's split of the ancillas), skip it and say so in
(e); it then moves to Stage 23c or the M4 review.

### P4. Tests (`tests/CQRVTests/RestoreRegimes.lean`)

- `#guard_msgs` on the axioms of `ancRestoreDirty_of_kraus`, `AncRestoreDirty.toClean`,
  `AncRestoreDirty.comp`, `reset_not_dirty`, `AncRestoreDirty.toCond`, `AncRestoreCond.toClean`
  and `AncRestoreCond.comp`;
- the dirty gadget is dirty restoring;
- `mbuCircuit` is not dirty restoring;
- the conditionally clean instance, with both strictness facts.

### 23b Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the axioms as in P4.

Stop and ask in any of these cases:
- the definition of `AncRestoreCond` does not support `toClean` and `comp` as stated (propose the
  one that does);
- a statement of mine is false;
- a single proof above about 400 lines, or the module above about 1 000;
- a Lean process above 8 GB.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
