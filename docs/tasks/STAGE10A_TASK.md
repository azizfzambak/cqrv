# Stage 10a (Phase III, item 1) — Theorem 3.3a for general ε: close `measured_composition`

Report sections: §2.3.2 (Theorem 3.3a, "Hypotheses made explicit" (i) domain compatibility,
(ii) non-expansiveness, L_g ≤ 1), §2.1.2 (ε-relaxation), §2.3.3 (pipeline). The statement was
fixed in Stage 2 (with the non-expansiveness hypothesis restricted to `dom S_g`, DECISIONS.md
2026-10-23); **do not change it**.
Precondition: report v3 committed (main = the "Report v3" commit). `git switch -c stage-10a main`;
one commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. Module system.
**Proof stage**, 3 build–fix rounds per item; CI stays local (`scripts/ci_local.sh`).

## Proof plan (reviewer; check it, do not trust it)

Reuse everything from `measured_composition_exact` (`prob_mixture`, `measure_chan_ofClassical`,
`prob_mono`, `prob_nonneg`, `measuredComp`, the `(1−δ_f)(1−δ_g) ≥ 1−δ_f−δ_g` step). Only the
event inclusion is new:

**Key lemma `relax_comp`** — if `S_f.relax ε_f x y` and `S_g.relax ε_g y z`, and the hypotheses
`hdom`, `hnonexp` hold, and `x ∈ S_f.dom`, then `(S_g.comp S_f).relax (ε_f + ε_g) x z`.
1. From `S_f.relax ε_f x y`: some `y₀` with `S_f x y₀` and `dist y y₀ ≤ ε_f`; hence `0 ≤ ε_f`.
2. `y₀ ∈ S_g.dom`: apply `hdom` at `y₀` (it is in its own ε_f-relaxation since
   `dist y₀ y₀ = 0 ≤ ε_f`).
3. From `S_g.relax ε_g y z`: some `z'` with `S_g y z'` and `dist z z' ≤ ε_g`.
4. Non-expansiveness at `y₀ ∈ dom S_g`, with `y' := y`, `z'`: some `z₀` with `S_g y₀ z₀` and
   `dist z₀ z' ≤ dist y₀ y ≤ ε_f`.
5. `(S_g.comp S_f) x z₀` (via `y₀`), and `dist z z₀ ≤ dist z z' + dist z' z₀ ≤ ε_g + ε_f`
   (`dist_triangle`, `dist_comm` — `#check` the names).

**Main proof.** As in the exact case: for `x ∈ (S_g.comp S_f).dom` (so `x ∈ S_f.dom`), the
composite's success probability is `Σ_y p_f(y) · Pr_g(y)[(S_g∘S_f).relax (ε_f+ε_g) x ·]`; restrict
the sum to `y` with `S_f.relax ε_f x y` (each in `dom S_g` by `hdom`), bound each inner probability
below by `Pr_g(y)[S_g.relax ε_g y ·] ≥ 1 − δ_g` using `relax_comp` + `prob_mono`, then
`≥ (1 − δ_g)(1 − δ_f) ≥ 1 − δ_f − δ_g`. Grade part: `Grade.seqComp_mono` as before.

## Tasks

1. Prove `relax_comp` (own theorem, doc-comment §2.3.2 (i)(ii)).
2. Prove `measured_composition` (remove the `sorry`; statement unchanged). If the exact-case
   proof can be refactored into a shared lemma parameterized by the events, do it only if it
   stays short; otherwise duplicate the ~30 lines — clarity over cleverness.
3. Corollary check: `measured_composition_exact` should follow from the general theorem with
   ε = 0 via `realizes_zero_iff` — state `measured_composition_exact'` as that corollary and prove
   it (keep the original theorem; this is a consistency test of the two statements).
4. Test: the §2.3.3 three-stage pipeline numbers — a small `example` instantiating the theorem
   twice on abstract stages with `ε = 0` and δ = 0.01, 0.005, 0.002, giving `δ ≤ 0.017` and grade
   (12, 280, 900, 8) (Stage 1 already checks the grade arithmetic; here the point is that the
   theorem composes).

## Acceptance

- `lake build` green; `measured_composition` sorry-free; `#print axioms` (guarded with
  `#guard_msgs`) for `relax_comp`, `measured_composition`, `measured_composition_exact'`: only
  `propext`, `Classical.choice`, `Quot.sound`. SORRIES.md row closed (hash in a follow-up line).
- `scripts/ci_local.sh`: every step PASS (paste the summary). One tracked `sorry` remains in the
  repository: `coherent_composition` (Theorem 3.3b).

## Stop conditions

- The statement turns out false (e.g. a counterexample to `relax_comp` under the stated
  hypotheses) → stop and report it; do not change the statement.
- Do not touch Theorem 3.3b, the diamond norm, or any Grover/certify file.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): whether the shared-lemma refactor was done, and the
`#print axioms` lines.
