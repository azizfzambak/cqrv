# Stage 13b — the diamond norm, and Theorem 3.3b with the real channel distance

Report sections: §2.3.2 (Theorem 3.3b, coherent-interface composition, `dist⋄`), §9.3 (Phase III),
§9.5.1. Closes the PROJECT_STATUS §4 row "Diamond norm and the domination lemma".
Precondition: main = fedabb2 (Stage 13a′ review). `git switch -c stage-13b main`; one commit;
include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix rounds
per item; repository stays sorry-free (a stuck item is reported, not left as a `sorry`).
**No existing statement changes**: `coherent_composition` keeps its abstract `distD`; the
diamond-norm version is a new corollary.

## Today

`CQRV/Realizability/Coherent.lean`: Theorem 3.3b is proved for any `distD` with
`hdistD : 2 · TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ distD Λ₁ Λ₂` for every `ρ` (DECISIONS.md 2026-10-23,
2026-10-25: "neither Mathlib nor Physlib has the diamond norm"). Re-check that claim first
against the pinned Physlib (96a6bc5): if a diamond norm or completely bounded trace norm exists
there, use it and say so instead of defining one.

## Reviewer decisions (record in DECISIONS.md)

1. **Definition** (new file `CQRV/Realizability/Diamond.lean`, imported by `Realizability.Basic`):
   for `Λ₁ Λ₂ : CPTPMap A B`,
   `diamondDist Λ₁ Λ₂ := ⨆ ρ : MState (A × A), 2 * TrDistance ((Λ₁ ⊗ id) ρ) ((Λ₂ ⊗ id) ρ)`,
   i.e. `‖Λ₁ − Λ₂‖⋄` as the stabilized trace-norm distance with a reference system of the input's
   dimension, restricted to density operators (Watrous, *The Theory of Quantum Information*,
   2018, §3.3: for a difference of channels the supremum over density operators on `A ⊗ A`
   attains the diamond norm — cite it in the docstring as the reason for this form; do **not**
   prove the equivalence with the operator-norm definition). Use Physlib's tensor of channels
   with the identity and product states — find the names with `#check` / `exact?`; if Physlib
   has no `Λ ⊗ id` on `CPTPMap`, stop and report what exists.
2. **Basic facts**, each proved: `BddAbove` of the range (by `trDistance_le_one`), so the `⨆`
   is a real `ciSup`; `0 ≤ diamondDist`, `diamondDist Λ Λ = 0`, symmetry, triangle inequality,
   `diamondDist ≤ 2`.
3. **Domination lemma** (the Phase III item):
   `diamond_dominates : 2 * TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ diamondDist Λ₁ Λ₂` for every `ρ : MState A`.
   Route (reviewer, verify): take `ρ ⊗ σ` for a fixed `σ : MState A`; the partial trace over the
   reference is a CPTP map, so `trDistance_cptp_le` gives `TrD(Λ₁ρ, Λ₂ρ) = TrD(tr_R((Λ₁⊗id)(ρ⊗σ)),
   tr_R((Λ₂⊗id)(ρ⊗σ))) ≤ TrD((Λ₁⊗id)(ρ⊗σ), (Λ₂⊗id)(ρ⊗σ))`; the needed identity is
   `tr_R((Λ⊗id)(ρ⊗σ)) = Λ ρ`. `MState A` must be nonempty (`Fintype A`, `Nonempty A` — add the
   hypothesis if Physlib needs it and say so).
4. **Theorem 3.3b with the diamond norm**, new name `coherent_composition_diamond`: the
   statement of `coherent_composition` with `distD := diamondDist` and no `hdistD` argument
   (proof: apply `coherent_composition` with `diamond_dominates`). Optional, only if short:
   `diamondDist (Ψ ∘ₘ Φ₁) (Ψ ∘ₘ Φ₂) ≤ diamondDist Φ₁ Φ₂` (data processing) — skip if it needs
   more than the facts above.
5. **Docs.** Coherent.lean module docstring: the diamond norm is now defined; DECISIONS.md entry
   (definition, why density operators on `A ⊗ A`, the Physlib names used, rejected: operator-norm
   definition / proving the Watrous equivalence). PROJECT_STATUS.md: remove the diamond row from
   §4 "Open", update the header to "(2026-10-28) … after Stages 0–13b". SORRIES.md: the
   Theorem 3.3b row gets a follow-up line naming `coherent_composition_diamond` (nothing to close).

## Acceptance

- `lake build` green, sorry-free; guarded `#print axioms` (tests/CQRVTests) for `diamondDist`'s
  facts, `diamond_dominates`, `coherent_composition_diamond`: only `propext`, `Classical.choice`,
  `Quot.sound`.
- `scripts/ci_local.sh` all PASS (or `check_certify.sh` alone if step 20 runs out of memory);
  certificates byte-identical (nothing in Certify changes).

## Stop conditions

- Physlib lacks the tensor of a channel with the identity or the partial trace as a CPTP map →
  stop and report what exists (do not define them from scratch in this stage).
- Any existing statement would have to change → stop and propose.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the Physlib names used, whether a diamond norm already
existed there, whether item 4's optional lemma was done, line counts.
