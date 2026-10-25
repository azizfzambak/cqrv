# Stage 10b (Phase III, item 2) — Theorem 3.3b: close `coherent_composition`

Report sections: §2.3.2 (Theorem 3.3b, "Reading of the four channels": ideal Φ₁, Ψ₁; implemented
Φ₂, Ψ₂; `‖Φ₂ − Φ₁‖⋄ ≤ η_f`, `‖Ψ₂ − Ψ₁‖⋄ ≤ η_g`; `δ_tot ≤ δ₀ + ½(η_f + η_g)` via the variational
characterization of the trace distance), §2.1.2 (Definition 2.2), §9.3 (Phase III).
Precondition: Stage 10a accepted (main = 10a review commit). `git switch -c stage-10b main`; one
commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix
rounds per item; a stuck item becomes a tracked `sorry` with its own SORRIES.md row.
**Do not change the statement of `coherent_composition`** (Stage 2; DECISIONS.md: the diamond norm
is a parameter `distD` whose only assumed property is `2 · TrDistance (Λ₁ ρ) (Λ₂ ρ) ≤ distD Λ₁ Λ₂`).

## Why this is provable without a diamond norm (reviewer)

With that statement the theorem needs only three trace-distance facts, all classical results:
1. **Triangle inequality** `TrDistance ρ τ ≤ TrDistance ρ σ + TrDistance σ τ` — from Physlib's
   `Matrix.traceNorm_add_le` (exists at the pinned commit; `#check` it).
2. **Data processing** `TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ` for every `CPTPMap Λ` — standard
   proof: write `ρ.m − σ.m = P − N` with `P = (ρ − σ)⁺`, `N = (ρ − σ)⁻` positive semidefinite and
   `tr P = tr N = TrDistance ρ σ` (Physlib has `HermitianMat` `posPart`/`negPart`,
   `ForMathlib/HermitianMat/Proj.lean`); then `Λ(ρ − σ) = Λ P − Λ N` (linearity), both PSD with
   traces `tr P`, `tr N` (trace preservation; CP ⇒ positive), and
   `‖Λ P − Λ N‖₁ ≤ ‖Λ P‖₁ + ‖Λ N‖₁ = tr P + tr N`.
3. **Measurement bound** `|Pr_{dec.measure ρ}[E] − Pr_{dec.measure σ}[E]| ≤ TrDistance ρ σ` for any
   POVM and event `E`: the difference is `Re tr(M_E (ρ − σ))` with `0 ≤ M_E = Σ_{z∈E} M_z ≤ 1`, and
   `tr(M_E (P − N)) ≤ tr(M_E P) ≤ tr P = TrDistance`. (This is the "variational characterization"
   direction the report uses.)
Then: for every input `x`, with `ρ = encode x`,
`TrDistance (Ψ₂Φ₂ρ) (Ψ₁Φ₁ρ) ≤ TrDistance (Ψ₂Φ₂ρ) (Ψ₂Φ₁ρ) + TrDistance (Ψ₂Φ₁ρ) (Ψ₁Φ₁ρ)
≤ TrDistance (Φ₂ρ) (Φ₁ρ) + η_g/2 ≤ η_f/2 + η_g/2` (data processing for `Ψ₂`, then `hdistD` twice),
and by fact 3 the success probability drops by at most that much: `≥ 1 − δ₀ − (η_f + η_g)/2`.
Grade conjunct: `Grade.seqComp_mono` as in 3.3a. Check the signs of every step yourself.

## Tasks (`CQRV/Realizability/TraceDistance.lean` for 1–3, then `Coherent.lean`)

1. `trDistance_triangle` — prove.
2. `trDistance_cptp_le` (data processing) — prove. If Physlib already has it under another name,
   use it and say which (search `TraceDistance.lean`, `Channels/`, `ForMathlib/`); if it exists
   only with a `sorry` upstream, do **not** use it — prove ours.
3. `prob_sub_le_trDistance` (measurement bound) — prove, for our `prob` and `POVM.measure`.
4. `coherent_composition` — prove from 1–3 and the hypotheses; remove its `sorry`.
5. Sanity example: with `distD := fun _ _ => 2` (which satisfies `hdistD` since
   `TrDistance ≤ 1`), the theorem instantiates — a non-vacuity check of the hypotheses.

## Acceptance

- `lake build` green; **no `sorry` left in the repository**; `#print axioms` (guarded) for the
  three facts and `coherent_composition`: only `propext`, `Classical.choice`, `Quot.sound`.
- SORRIES.md: `coherent_composition` closed (hash in a follow-up line); DECISIONS.md entry noting
  that 3.3b is proved for the abstract `distD` (any distance dominating twice the trace distance on
  inputs), and that instantiating it with the real diamond norm needs only the domination lemma
  `‖Λ₁ρ − Λ₂ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄` once a diamond norm exists — a remaining Phase III item.
- `scripts/ci_local.sh`: all PASS (paste the summary). Update `docs/M2_REPORT.md` §3 only by a
  dated one-line "post-M2 note" listing 3.3a (general ε) and 3.3b as closed — do not rewrite the
  frozen report.

## Stop conditions

- Physlib lacks a piece you need (e.g. PSD-ness of `Λ P` for a CPTP map, or `posPart` trace
  identities) and proving it exceeds ~150 lines → stop and report what is missing.
- A fact is false as stated (e.g. a sign) → stop and report.
- Do not define a diamond norm; do not touch Grover/certify files.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which Physlib lemmas were reused, the size of the
data-processing proof, and the `#print axioms` lines.
