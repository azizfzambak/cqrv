# Stage 7b — Reflection geometry, iteration induction, terminal measurement, realization

Report sections: §8.3.2 (decomposition `|s⟩ = sin θ ψ_g + cos θ ψ_b`, `G = U_s U_P` rotates by 2θ,
induction on r, measurement), §8.2.3 (p_succ), §8.3.4 / Figure 8.1, §6.3.2 (Theorem 3.3a only at
the terminal measurement), §2.1.2 (Definition 2.2).
Precondition: Stage 7a accepted (main = 7a review commit). `git switch -c stage-7b main`; one
commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. Module system.
**Proof stage**: prove items 1–5 in order; 3 build–fix rounds per item, then a tracked `sorry`
with the goal verbatim and continue with the next item that does not depend on it.
**Do not change any statement** proved or stated in 7a (`reflection_geometry`,
`iteration_induction`, `terminal_measurement`, `grover_realizes`, `grover_parametric_lemma`).
If one of them is false as stated, stop and report (see stop conditions).

## The reviewer checked the statements by hand (signs and the edge case)

With `U_P ψ_g = −ψ_g`, `U_P ψ_b = ψ_b`, `U_s v = 2⟨s|v⟩ s − v`, `⟨s|ψ_g⟩ = sin θ`,
`⟨s|ψ_b⟩ = cos θ`:
`G ψ_g = −U_s ψ_g = ψ_g − 2 sin θ |s⟩ = cos 2θ ψ_g − sin 2θ ψ_b`;
`G ψ_b = U_s ψ_b = 2 cos θ |s⟩ − ψ_b = sin 2θ ψ_g + cos 2θ ψ_b` — the 7a statement.
Then `G (sin φ ψ_g + cos φ ψ_b) = sin(φ + 2θ) ψ_g + cos(φ + 2θ) ψ_b` (angle addition).
Edge case M = 2ⁿ: `psiBad = 0`, θ = π/2, `sin 2θ = 0`, `cos θ = 0` — the statements still hold;
handle it by a case split, do not add a hypothesis `M < 2ⁿ`.

## Tasks (`CQRV/Grover/Geometry.lean` or inside `Lemma.lean`; doc-comment each with its §)

1. **Plane facts — prove.** From `hM_card`: `‖ψ_g‖ = 1` (M ≥ 1), `‖ψ_b‖ = 1` or `ψ_b = 0`
   (M = 2ⁿ), `⟨ψ_g, ψ_b⟩ = 0`; `sin θ = √(M/2ⁿ)`, `cos θ = √(1 − M/2ⁿ)`, `0 ≤ θ ≤ π/2`
   (Mathlib `Real.sin_arcsin`, `Real.cos_arcsin` — `#check` them);
   `ketS n = (sin θ : ℂ) • ψ_g + (cos θ : ℂ) • ψ_b` (sum split by `P x`, `card` = M via `hM_card`);
   `⟨s|ψ_g⟩ = sin θ`, `⟨s|ψ_b⟩ = cos θ`; `U_P ψ_g = −ψ_g`, `U_P ψ_b = ψ_b` (from
   `oracle_reflection`); `U_s v = 2⟨s|v⟩ s − v` (from `diffusion_reflection`).
2. **`reflection_geometry` — prove** from item 1 (`Real.sin_two_mul`, `Real.cos_two_mul`,
   `sin²+cos² = 1`).
3. **`iteration_induction` — prove** by induction on r from item 2 and the angle-addition step
   above (`Real.sin_add`, `Real.cos_add`); base case `ketS = sin θ ψ_g + cos θ ψ_b`.
4. **`terminal_measurement` — prove.** `hadamardU n * |0…0⟩ = ketS n` (state it at the vector level
   and lift to `◃ ancZero` = the pure state of `G^r |s⟩`), then the basis-POVM probability of
   `P` on a pure state `|φ⟩` is `Σ_{P x} |φ x|²`, which on `sin φ' ψ_g + cos φ' ψ_b` equals
   `sin² φ'` (the ψ_b part vanishes on good x, `Σ_{P x} |ψ_g x|² = 1`).
5. **`grover_realizes` — prove.** The channel prepares `ancZero n ⊗ ancZero nAnc`, runs `C`, traces
   the ancillae: by `grover_ancRestore` (7a) and `AncRestore.traced` the traced state is
   `(G^r H^{⊗n}) ◃ ancZero n`; `encode ()` is the unique input; the replacement channel ignores
   it; then item 4 gives probability = sin²((2r+1)θ) = 1 − δ. The grade conjunct is already
   proved (`le_rfl`). Theorem 3.3a is **not** used here (one terminal measurement, §6.3.2).
6. With 1–5 closed, `grover_parametric_lemma` and `grover_pred_037_certified_statement` become
   sorry-free: paste their `#print axioms` (expected: `propext`, `Classical.choice`,
   `Quot.sound`). Close the four SORRIES.md rows (hash in a follow-up line/commit as before).

## Also (small, decided in the 7a review)

- Add a **planned** SORRIES.md row `synthesizeOracle_WF : synthesizeOracle N = .ok C → C.WF`
  (would remove the `hWF` fields and the need for `DiffusionCert` for general n). Not part of
  7b's acceptance; do not attempt it.

## Acceptance

- `lake build` green, checks pass, harnesses green, oracle JSON byte-identical.
- Items 1–5 proved, or each stuck item a tracked sorry with its goal verbatim.
- If all closed: the Grover parametric lemma (realization ∧ restoration) and the
  `grover_pred_037` instance with grade (15, 230, 72, 7) and δ = 7/128 are axiom-audited and
  sorry-free.

## Stop conditions

- A 7a statement is false (e.g. a sign, or the M = 2ⁿ case) → stop and report the failing case;
  do not edit the statement.
- `basisPOVM.measure` on a pure state does not unfold to `|φ x|²` with the available Physlib
  lemmas → stop and report what is missing (name, shape) instead of axiomatizing it.
- Do not start Stage 8; do not touch `lemma_6_3_2_xor` or `synthesizeOracle_WF`.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which items closed, the `#print axioms` of the main
lemma and the instance, and the remaining sorries (expected: only `measured_composition` and
`coherent_composition` from Stage 2, Phase III).
