# Revision task A — R1, R2, R15

Written 2026-11-16 by the reviewer session. The author decided on 2026-11-16 to start the revision
tasks with R1, R2 and R15 (`docs/DECISIONS.md`, same date; `docs/REVIEW_RESPONSE_1.md` §4).

**Start:** branch `rev-a` from `main` at `9220b36`. **End:** three commits on `rev-a`, one per item
(R1, R2, R15), each buildable, warning-free, sorry-free. This file goes into the first commit.
Read `docs/REVIEW_RESPONSE_1.md` rows 2, 8 and "Witness classical-bit map" first.

Do not touch `docs/paper/`, `docs/cqrv_report_revised_v4.docx`, `docs/notes/`, `docs/PHASE3_*.md`
(untracked files of the author and the reviewer). No download, no dependency change.

---

## R1 — no-cloning: the linear form for every non-empty space, and the pure-state form

File: `CQRV/Realizability/Obstruction.lean` (Report §2.2.2, Theorem 3.1). Keep
`no_cloning_obstruction` unchanged.

**(a) `no_cloning_linear`.** For `[Fintype d] [Nonempty d]`: no `C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ)` with
`C ψ = fun ij => ψ ij.1 * ψ ij.2` for every `ψ`. Proof plan (verify every step): scaling — at
`ψ = Pi.single i 1` and index `(i, i)`, `C (2 • ψ)` gives 4 while `2 • C ψ` gives 2.

**(b) `no_cloning_pure`.** The form that survives restriction to normalized states. For
`[Fintype d] [DecidableEq d]` with `2 ≤ Fintype.card d`: no ℂ-linear
`Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ` with
`Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ)` for every `ψ` with
`∑ i, Complex.normSq (ψ i) = 1` (or an equivalent unit-norm hypothesis; say which you chose).
Proof plan (verify every step): take `i ≠ j` and `ψ± = (e_i ± e_j)/√2`. Then
`P₊ + P₋ = E_ii + E_jj` (both unit vectors e_i, e_j are pure states too), so by linearity
`Φ P₊ + Φ P₋ = E_ii ⊗ E_ii + E_jj ⊗ E_jj`. At row `(i, i)`, column `(j, j)` the right side is 0;
the left side is `P₊ i j ^ 2 + P₋ i j ^ 2 = 1/4 + 1/4 = 1/2`.

**(c) Sharpness, `pure_cloning_of_card_one`.** For `Fintype.card d = 1` such a Φ exists
(e.g. `Φ M = M ⊗ₖ 1`). A theorem, so the paper can say the hypothesis `2 ≤ |d|` is exactly right.

Tests in `tests/CQRVTests/Realizability.lean`: `#print axioms` lines for the three (standard three
only). Update the module doc-string of `Obstruction.lean` (what each theorem says, and why (b) and
not (a) is the physically meaningful one).

**Guard:** if (b) needs more than about 200 lines or a lemma you cannot find (rule 2), commit (a)
and (c), state the obligation for (b) in the report, and go on to R2.

## R2 — Clean ⇒ Cond(true)

File: `CQRV/Circuit/RestoreRegimes.lean` (Report §6.2.3; PHASE2_SPEC §B.2, 23b). Today the file has
`AncRestoreCond.toClean` (every condition) but not the converse for `cond ≡ true`.

1. **Support factorization.** For `ω : MState (Reg n × Reg a)` with
   `ancProj n a * ω.m * ancProj n a = ω.m`: `ω.m = (traceRight ω).m ⊗ₖ (ancZero a).m`, and hence
   `ω = traceRight ω ⊗ᴹ ancZero a` (use the file's names for the partial trace and the product;
   `condSubspace_true` already identifies `V_true` with `ancProj`). Proof idea: the support
   hypothesis makes every entry with `w ≠ 0` or `v ≠ 0` vanish; the partial trace at `(x, y)` is then
   the single entry `((x, 0), (y, 0))`.
2. **`AncRestore.toCond_true`**: `AncRestore n a C U → AncRestoreCond n a C U (fun _ => true)`,
   via 1, the clean statement at `traceRight ω`, and `kron_one_conj`.
3. **`ancRestoreCond_true_iff`**: `AncRestoreCond n a C U (fun _ => true) ↔ AncRestore n a C U`.

Tests in `tests/CQRVTests/RestoreRegimes.lean`: `#print axioms` for 1–3; one use of the iff on an
existing clean instance (for example the MBU gadget's `AncRestore`). Update the file's module
doc-string: the regime list there should now say that Cond(true) and Clean are equivalent (proved).

**Guard:** about 300 lines for R2 in all; above it, stop and report.

## R15 — the witness's classical-bit map as an explicit check

Files: `CQRV/Hardware/Witness.lean` (`applyWitness`), `CQRV/Hardware/Check.lean`
(`applyWitnessQ`), and their soundness files. Today `Witness.clbitMap` is parsed and unused; the
reconstruction keeps the logical bit numbering, so a non-identity map already makes `recon` fail —
soundly, but without saying why. All 15 committed witnesses have the identity map
`[0, …, k−1]` (k = 1 for the coherent circuits, which have no bits).

1. Add one `ensure` to both `applyWitness` and `applyWitnessQ`, next to the existing witness checks:
   `w.clbitMap == List.range w.clbitMap.length && decide (C.nBits ≤ w.clbitMap.length)`, message
   `"witness: the classical-bit map is not the identity on the circuit's bits"`. If you find that
   this exact form is wrong for one of the 15 artifacts (for example `C.nBits` larger than the map),
   stop and report; do not weaken it to make it pass.
2. Re-establish every theorem about the two functions with unchanged statements:
   `applyWitnessQ_ok`, `applyWitness_sound`, `applyWitness_sound_core`, `applyWitnessQ_sound`, and
   whatever in `CQRV/Noise/` unfolds them. The check is a pure precondition, so each proof should
   only peel one more `ensure`.
3. Tests in `tests/CQRVTests/HardwareWitness.lean`: the gadget's witness with `clbitMap := [1]` is
   rejected with the new message, with `[0]` accepted (by `decide` or `rfl` on the `Except`).
4. Documentation lines only: the witness description in `hw/README.md` and the `clbit_map`
   description in `docs/hw_witness.schema.json` (no schema-version change, no field change).
5. The 15 artifacts, the 15 `examples/hw_checks/*/Check.lean`, the physical certificate, the noise
   certificates and the selection files are **not** regenerated by hand. Regenerate one check file
   with `cqr hw check` and confirm it is byte-identical; the CI steps 28–30 re-check the rest.

**Guard:** any committed file that is no longer byte-identical after regeneration, or any check file
whose kernel time grows by more than 20 % — stop and report.

---

## Acceptance

- `lake build` green, 0 warnings, 0 `sorry`; `#print axioms` of every new theorem: the standard
  three only.
- Run one Lean process at a time. Do **not** run the full CI; the reviewer runs it (26 PASS / 4 n/a
  is the pass mark; no new CI step).
- A `docs/DECISIONS.md` entry per item if you decide anything the task leaves open (for example the
  unit-norm form in R1(b)).
- No new entry in `docs/SORRIES.md`.
- The report in the usual format (CLAUDE.md, under 40 lines): files changed, `lake build` tail, test
  output, SORRIES changes (none expected), open questions. Commit messages name the report sections
  and "REVIEW_RESPONSE_1 R1 / R2 / R15"; use your usual Co-Authored-By line.
