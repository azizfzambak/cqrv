# Stage 2 — Realizability definitions and the statements of Theorems 3.3a, 3.3b, 3.1

Report sections: §2.1.1 (Definition 2.1), §2.1.2 (Definition 2.2), §2.2.2 (Theorem 3.1, revised:
`Cl_det`, non-degeneracy), §2.3.1 (Definition 3.2), §2.3.2 (Theorems 3.3a/3.3b, "Hypotheses made
explicit", "Reading of the four channels"), §9.1.1 (reuse of Physlib).
Precondition: Stage 1 accepted (main = stage-1 = dedec96). `git switch -c stage-2 main`; one commit.
Windows builds: `LEAN_NUM_THREADS=4`. Python: `.venv/Scripts/python.exe -I`. Module system in every
new file (`module`, `public import`, `@[expose] public section` only where `rfl`/`decide` need bodies).

## Already decided — do not reopen

- **Physlib builds** (DECISIONS.md, Stage 0), so the abstract-`Channel` fallback of PLAN.md is
  **void**: channels are Physlib `CPTPMap`, states `MState`, decoding `POVM`, distance `TrDistance`.
  Do not define a `Channel` structure of our own and add no `axiom`.
- The output metric is a type parameter; the MVP uses only ε = 0 (DECISIONS.md 2026-10-21).
- ⊕ is `+` on `Grade`, budgets use `≤` / `fits` (Stage 1).

## Physlib API to use (verified by the reviewer to exist at the pinned commit; still `#check` each — rule 2)

`CPTPMap dIn dOut`, composition `Λ₂ ∘ₘ Λ₁`, `CPTPMap.compose_eq`, `CPTPMap.traceRight`,
`MState d`, `MState.ofClassical`, `ProbDistribution.constant`, `POVM X d`, `POVM.measure`,
`POVM.measureDiscard : CPTPMap d X`, `POVM.measureDiscard_apply`
(`Λ.measureDiscard ρ = MState.ofClassical (Λ.measure ρ)`), `TrDistance`.
`CPTP.lean`, `MState.lean`, `POVM.lean`, `TraceDistance.lean` contain no `sorry`.
Physlib has **no diamond norm** (grep found none in `QuantumInfo/Channels`).

## Tasks (in `CQRV/Realizability/`; doc-comment every declaration with its report §)

1. **`Spec.lean` — Definition 2.1.** `def Spec (X Y : Type) := X → Y → Prop`; `Spec.dom`;
   relational composition `Spec.comp (g : Spec Y Z) (f : Spec X Y)` (∃ intermediate y);
   `Spec.relax [PseudoMetricSpace Y] (S : Spec X Y) (ε : ℝ) : Spec X Y`
   (`∃ y', S x y' ∧ dist y y' ≤ ε`) and `relax_zero [MetricSpace Y] : S.relax 0 = S`
   (find the Mathlib lemma for `dist ≤ 0 ↔ =` with `exact?`; do not guess its name).
   If an output type we need later (`Bool`, `Fin n`) lacks a `MetricSpace` instance, say so in
   open questions — do not add an instance in this stage.

2. **`Realizes.lean` — Definition 2.2 and Definition 3.2.**
   - Classical inputs are encoded in the **computational basis** of a Hilbert space indexed by
     the input type itself: `encode (x : X) : MState X := MState.ofClassical (ProbDistribution.constant x)`.
     Fixing the encoding (not a parameter) is what makes the measured interface of 3.3a exactly
     `POVM.measureDiscard` — record this in DECISIONS.md.
   - `structure GradedChannel (X : Type) (dY : Type) [..]` with `chan : CPTPMap X dY` and
     `grade : Grade`. Doc-comment: in Stage 2 the grade is declared data; it is *derived* from a
     circuit only from Stage 5/6 on (name this as a trust gap in the doc-comment).
   - `def Realizes (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (ε δ : ℝ) (r : Grade) : Prop`
     := `Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 − δ ≤ Pr_{y ∼ dec.measure (Φ.chan (encode x))}[S.relax ε x y]`.
     Use whatever Physlib/Mathlib offers for the probability of an event under a
     `ProbDistribution` (find it; classical decidability of the event is fine). "Within grade r"
     is read as fibre membership `grade ≤ r` (§3.1.2) — record in DECISIONS.md, rejected: `grade = r`.
   - Ancilla: Definition 2.2 is about the channel *after* ancilla trace-out. Provide
     `GradedChannel.traceAnc : GradedChannel X (dY × A) → GradedChannel X dY` via
     `CPTPMap.traceRight`, grade unchanged, with a doc-comment pointing to `AncRestore` (Stage 6).
   - Tests (`tests/CQRVTests/Realizability.lean`): `Spec.dom`/`Spec.comp` on a small `Fin` example
     by `decide`; `relax_zero` used once. No numeric test of `Realizes` is expected yet.

3. **`Composition.lean` — Theorem 3.3a.** The measured interface is
   `Ψ.chan ∘ₘ dec_f.measureDiscard ∘ₘ Φ.chan` with grade `Φ.grade + Ψ.grade` (the measurement
   and re-encoding are counted at grade 0, as in the report's `r ⊕ s`; flag this in open questions).
   - `theorem measured_composition_exact` (ε_f = ε_g = 0): hypotheses
     `Realizes S_f dec_f Φ 0 δ_f r`, `Realizes S_g dec_g Ψ 0 δ_g s`, **domain compatibility**
     `∀ x ∈ S_f.dom, ∀ y, S_f x y → y ∈ S_g.dom` (§2.3.2 (i), ε_f = 0 form), and
     `0 ≤ δ_f`, `0 ≤ δ_g`, `δ_g ≤ 1` (needed for `(1−δ_f)(1−δ_g) ≥ 1−δ_f−δ_g`; record that the
     report leaves these implicit). Conclusion: `Realizes (S_g.comp S_f) dec_g (composite) 0 (δ_f + δ_g) (r + s)`.
     Grade part: from `Grade.seqComp_mono`. Probability part: sketch
     `Pr[(g∘f)] ≥ Σ_{y ∈ S_f x} p_f(y)·(1−δ_g) ≥ (1−δ_f)(1−δ_g)`, using `measureDiscard_apply` and
     linearity of `Ψ.chan` on the mixture `ofClassical (dec_f.measure …)`.
     **Attempt the proof.** If it does not close within 3 build–fix rounds, leave a tracked `sorry`
     and split it in SORRIES.md into the sub-lemmas you would need (e.g. "CPTPMap applied to
     `ofClassical p` is the p-mixture of the images of basis states" — check whether Physlib
     already has it before listing it).
   - `theorem measured_composition` (general ε): additionally `[MetricSpace Y] [MetricSpace Z]`,
     domain compatibility in the relaxed form `∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom`,
     and **non-expansiveness** of `S_g` (§2.3.2 (ii)), stated as
     `∀ y y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y'`; conclusion with `ε_f + ε_g`,
     `δ_f + δ_g`, `r + s`. Check that this formulation matches the report's "L_g ≤ 1" reading; if
     you think it does not, stop and say why. **State only, tracked `sorry`.**

4. **`Coherent.lean` — Theorem 3.3b, statement only.** There is no diamond norm to import, so
   take the channel distance as an explicit parameter `dist⋄ : CPTPMap X dY → CPTPMap X dY → ℝ`
   with the hypothesis that it dominates the trace distance on every input
   (`∀ ρ, 2 * TrDistance (Φ₁ ρ) (Φ₂ ρ) ≤ dist⋄ Φ₁ Φ₂` — check the ½ convention against
   §2.3.2: `δ_tot ≤ δ₀ + ½(η_f + η_g)`). Channels as in "Reading of the four channels": ideal
   Φ₁, Ψ₁ with the composite `(0, δ₀)`-realizing `g ∘ f`; implemented Φ₂, Ψ₂ with
   `dist⋄ Φ₂ Φ₁ ≤ η_f`, `dist⋄ Ψ₂ Ψ₁ ≤ η_g`; conclusion `δ_tot ≤ δ₀ + (η_f + η_g)/2`, grade `r + s`.
   Tracked `sorry`; **do not attempt.** DECISIONS.md: diamond norm is a parameter until Phase III
   (rejected: defining it now — out of scope; adding it as an `axiom` — violates §9.5.1).

5. **`Obstruction.lean` — Theorem 3.1, statement only.** Neither Mathlib nor Physlib has the
   category U, so state the report's "equivalently" form concretely: for a finite type `d` with
   `2 ≤ Fintype.card d` (non-degeneracy, `dim F(Bool) ≥ 2`), there is no linear map
   `C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ)` with `C ψ = ψ ⊗ ψ` for **all** vectors ψ (natural w.r.t. all
   states, not only basis states). Doc-comment: the categorical packaging (monoidal functor
   `Cl_det → U` preserving (Δ, !)) is deferred; record the gap in DECISIONS.md and in open
   questions. Tracked `sorry`; **do not attempt** (the reviewer will decide whether to prove this
   concrete form — it is short).

6. **Test layout (carried over from the Stage 1 review).** Move `tests/Grades.lean` to
   `tests/CQRVTests/Grades.lean` (module `CQRVTests.Grades`), put new tests under
   `tests/CQRVTests/`, and wire them with `globs := #[.submodules `CQRVTests]` (or the
   equivalent the pinned Lake supports) instead of listing roots one by one. `PhyslibSmoke`
   stays as it is. This is the only change outside `CQRV/Realizability` and `tests/` allowed.

## Acceptance

- `lake build` green; the only warnings are "declaration uses `sorry`" for rows in SORRIES.md;
  `check_warnings.sh`, `check_sorries.sh` pass.
- Four theorems compile with the hypotheses above. `measured_composition_exact` is either closed
  (paste `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`) or
  split into sub-lemmas in SORRIES.md.
- SORRIES.md rows for every remaining sorry (file:line, statement, report §, depends on, est. lines).
- DECISIONS.md entries: fixed basis encoding, `grade ≤ r` reading, interface at grade 0,
  δ-range hypotheses of 3.3a, `dist⋄` parameter for 3.3b, concrete form of 3.1, test layout.

## Stop conditions

- A Physlib name from the list above does not exist at the pinned commit → stop and report.
- The report's hypotheses cannot be stated with the types above without changing their
  meaning → stop and report; do not weaken a hypothesis silently.
- Do not attempt 3.3b or 3.1, do not start Stage 3.

## Closing reply

CLAUDE.md format, under 40 lines: (a) files, (b) `lake build` tail, (c) test output and any
`#print axioms`, (d) SORRIES.md rows added/closed, (e) open questions — at minimum the interface
grade and any missing `MetricSpace` instance.
