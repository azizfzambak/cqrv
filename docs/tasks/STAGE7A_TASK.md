# Stage 7a — Grover parametric lemma: definitions, statements, the linear-algebra lemmas

Report sections: §5.2.4 (revised Lean sketch: `OracleCert`, `GroverParams`, `hM_card` as a
hypothesis), §8.2 (circuit family, `U_s = H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}`, p_succ = sin²((2r+1)θ)),
§8.3.2 (reflection geometry), §8.3.4 / Figure 8.1 (lemma dependency graph), §8.2.4
(realization ∧ restoration), §6.3.2 (Theorem 3.3a used once, at the terminal measurement).
Precondition: Stage 5b accepted (main = Stage 5b review commit). `git switch -c stage-7a main`;
one commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. Module system.
**Proof stage**: state everything first; prove only items marked *prove*; 3 build–fix rounds per
item, then a tracked `sorry` with the goal verbatim.

## What is already proved and must be reused (do not re-prove)

- `lemma_6_3_2` (xor-free networks): every synthesized oracle satisfies
  `AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData))` — on density operators.
- `AncRestore.comp`, `channelDenote_append` (shifted append), `ancRestore_of_kraus`.
- Stage 5b: `diffusion`, `groverIteration`, `groverCircuit` (V1, straight-line), measured grade
  of the `grover_pred_037` instance (15, 230, 72, 7); simulated p_succ = 121/128.

## Reviewer decisions (record in DECISIONS.md)

1. **Grade is derived, not declared.** The certificate's grade is `Synthesis.grade` of the
   Grover circuit (the measured grade), not the report's formula `r⋆·(depth_U + depth_D)`
   (the scheduler overlaps boundaries — Stage 5b found 230 < 233). This closes the Stage 2 trust
   gap "grade is declared data" for the Grover slice. Rejected: the report's formula.
2. **r is a parameter.** The lemma holds for every `r`: `p_succ(r) = sin²((2r+1)θ)`. The choice
   r = r⋆ (floating point in the CLI) is outside the proof; any r yields a valid certificate.
3. **Exact δ for the instance.** sin²((2r+1)θ) is a polynomial in sin²θ = M/N. For n = 8, M = 32,
   r = 2: `sin²(5θ) = 121/128`, so `δ = 7/128` exactly (reviewer's hand computation:
   sin 5θ = s(16s⁴ − 20s² + 5) = (11/4)s with s² = 1/8). The instance corollary states δ = 7/128.
4. **Spec shape.** The search spec has input type `Unit` (P is fixed by the instance):
   `SearchSpec P : Spec Unit (Reg n) := fun _ x => P x = true`; `dom` is all of `Unit` iff
   M ≥ 1. The channel `Unit → Reg n` is: prepare |0…0⟩ (data and ancillae), run
   `channelDenote` of the Grover circuit, trace out the ancillae (`traceAnc` of Stage 2); decoding
   is the computational-basis POVM on `Reg n` (define it and prove it is a POVM if Physlib has
   none — check first). Realization is `RealizesExact` (Stage 2: no metric needed).
5. **Global phase.** `H^{⊗n} X^{⊗n} MCZ X^{⊗n} H^{⊗n} = −(2|s⟩⟨s| − I)`; prove `(−U) ◃ ρ = U ◃ ρ`
   once and use it — the channel does not see the sign.

## Tasks (`CQRV/Grover/`; doc-comment each with its §)

1. **Records** (§5.2.4, adapted): `OracleCert n` bundles a network `N` (xor-free), its synthesized
   circuit `C`, `hC : synthesizeOracle N = .ok C`, `hWF`, and the restoration fact from
   `lemma_6_3_2` (a field filled by the lemma, not assumed). `GroverParams` with `n`, `M`,
   `hM_pos : 1 ≤ M`, `oracle`, and `hM_card : (univ.filter (oracle.P · = true)).card = M` as a
   **hypothesis** (§5.1.3: never decided by enumeration).
2. **Statements of Figure 8.1** (six named theorems, each with a doc-comment giving its report
   line and the effort estimate from the figure's table):
   `oracle_reflection` (U_P = I − 2Π_good on `Reg n`), `diffusion_reflection`
   (`H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n} = 2|s⟩⟨s| − I`), `reflection_geometry` (G = U_s U_P maps the
   plane span{ψ_g, ψ_b} to itself, rotation by 2θ), `iteration_induction`
   (`G^r |s⟩ = sin((2r+1)θ) ψ_g + cos((2r+1)θ) ψ_b`), `terminal_measurement`
   (p_succ = sin²((2r+1)θ) under the basis POVM), and `grover_parametric_lemma`
   (`RealizesExact (SearchSpec P) basisPOVM groverChannel (1 − sin²((2r+1)θ)) (grade C)` ∧
   `AncRestore` of the full circuit with `U = G^r H^{⊗n}`), with θ = arcsin √(M/2ⁿ) as in §5.2.4.
3. ***Prove*** `oracle_reflection` and `diffusion_reflection` (pure linear algebra on
   `Matrix (Reg n) (Reg n) ℂ`; H^{⊗n} entries are `(−1)^{x·y}/√2ⁿ`).
4. ***Prove*** the restoration side for the circuit pieces: a data-only unitary layer (H^{⊗n},
   X^{⊗n}) satisfies `AncRestore` with its matrix; the diffusion circuit satisfies `AncRestore`
   with `2|s⟩⟨s| − I` (from `lemma_6_3_2` on `allNet n`, the wrappers, `AncRestore.comp`, and
   decision 5); one iteration satisfies `AncRestore` with `G`; by induction the full circuit
   satisfies `AncRestore` with `G^r H^{⊗n}` — this is the **restoration conjunct of
   `grover_parametric_lemma`**; if it closes, state it as its own theorem
   `grover_ancRestore` and use it in the main lemma.
5. ***Prove (attempt)*** the instance trig fact `sin_sq_five_mul (h : sin θ ^ 2 = 1/8) (hθ : 0 ≤ θ ≤ π/2) :
   sin (5θ) ^ 2 = 121/128` (find Mathlib's multiple-angle lemmas with `exact?`/`#check`; do not
   guess names). Leave `reflection_geometry`, `iteration_induction`, `terminal_measurement` and
   the realization conjunct as tracked `sorry`s — they are 7b/7c.
6. **Instance** `grover_pred_037_certified_statement`: the main lemma at the `grover_pred_037`
   oracle (via `groverNet`, the DSL bridge of 6a), `n = 8`, `M = 32` (`hM_card` supplied as a
   hypothesis of the statement, not decided), `r = 2`, grade `(15, 230, 72, 7)` by `decide`/`rfl`
   on the computed grade, δ rewritten to `7/128` via item 5.
7. **SORRIES.md**: one row per remaining sorry, with the Figure 8.1 dependency and estimate;
   mark which ones depend only on linear algebra over the 2-D plane (the SQIR-style part).

## Tests

`tests/CQRVTests/Grover.lean`: `#print axioms` for every proved theorem (standard three only)
and for the instance (it will show `sorryAx` through the open lemmas — say which).
`#guard` that the computed grade of the Grover circuit is `(15, 230, 72, 7)`.

## Acceptance

- `lake build` green, checks pass, oracle JSON byte-identical, harnesses still green.
- Proved: items 3, 4 (restoration conjunct), and 5 if it closes. Stated: all of Figure 8.1.
- DECISIONS.md: decisions 1–5.

## Stop conditions

- `diffusion_reflection` or the diffusion `AncRestore` is false as stated (e.g. a sign that does
  not cancel) → stop and report.
- The `RealizesExact` shape of decision 4 cannot express "prepare |0…0⟩, run, trace, measure"
  with the Stage 2 definitions → stop and propose a shape; do not change `Realizes`.
- Do not attempt `reflection_geometry`, `iteration_induction`, `terminal_measurement`;
  do not start Stage 8.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which items closed, the exact form of the restoration
conjunct, and the open sorries with their Figure 8.1 position.
