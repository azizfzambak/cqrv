# Stage 6b-1 — Restoration template lemma, `mbu_channel_correct`, channel composition

Report sections: §6.2.2 (MBU correctness is a channel-level statement), §6.2.4 (Layers 1–3),
§6.3.2 (Lemma 6.3.2 on density operators), §9.1.1 (partial-trace / uncomputation tactics).
Precondition: Stage 6a closed (main = 5422010). `git switch -c stage-6b1 main`; one commit;
include this file (untracked) in it. Windows: `LEAN_NUM_THREADS=4`. Module system.
**Proof stage:** prove what is asked below; 3 build–fix rounds per item, then stop that item and
record the stuck goal (PLAN.md §1). Do not touch `lemma_6_3_2` itself.

## Why this order

Every remaining restoration proof (MBU now; per-AND lift, Z = phase, the induction over the AND
list later) has the same shape: on the subspace where the ancillae are |0…0⟩, every Kraus
operator of the circuit acts as a scalar multiple of `U ⊗ |0…0⟩⟨0…0|`. Prove that template once
(task 1), use it for MBU (task 2), and prove the composition lemma the later induction needs
(task 3).

## The reviewer's hand computation for MBU (use it as the proof plan; check it, don't trust it)

After compute and `Z t` the state is `Σ α_ab (−1)^{ab} |ab⟩|ab⟩`. After `H t`:
`Σ α_ab (−1)^{ab} |ab⟩ (|0⟩ + (−1)^{ab}|1⟩)/√2`.
Branch c = 0: projector keeps `Σ α_ab (−1)^{ab} |ab⟩|0⟩ / √2` = `(CZ ψ) ⊗ |0⟩ / √2`; no fix-up.
Branch c = 1: projector keeps `Σ α_ab |ab⟩|1⟩ / √2`; `CZ` gives `Σ α_ab (−1)^{ab}|ab⟩|1⟩ / √2`;
`X t` gives `(CZ ψ) ⊗ |0⟩ / √2`.
So **each** Kraus operator satisfies `K_c · (1 ⊗ |0⟩⟨0|) = (1/√2) · (CZ ⊗ |0⟩⟨0|)`, and
`Σ_c |1/√2|² = 1`. (Without the Stage 5 `ifBit m (X t)` reset, branch 1 would leave |1⟩ —
the erratum the harness found.)

## Tasks (`CQRV/Circuit/Restoration.lean`, or a new `CQRV/Circuit/RestoreTemplate.lean`)

1. **Template lemma — prove.** Let `P := 1 ⊗ |0…0⟩⟨0…0|` on `Reg n × Reg a`. If `C.WF` and
   there are scalars `λ : (Fin m → Bool) → ℂ` with `Σ_c ‖λ c‖² = 1` and, for every branch `c`,
   `krausOps … c * P = λ c • (U ⊗ₖ |0…0⟩⟨0…0|)` (state the Kronecker form in whatever shape
   Physlib's `MState.prod` / `ancZero` unfold to — find it with `#check`/`simp?`, do not guess),
   then `AncRestore n a C U`. Proof idea: `ρ ⊗ ancZero = P (ρ ⊗ ancZero) P`, push `P` into each
   Kraus operator, sum the `‖λ c‖²`. Name it `ancRestore_of_kraus` (doc-comment: §6.2.4 Layer 3
   template). Prove a matrix-level helper `ρ ⊗ᴹ ancZero a` has matrix `P * … * P` separately.
2. **`mbu_channel_correct` — prove** with task 1, `U := czU`, `λ c := 1/√2`. Establish the
   per-branch identity on basis vectors (`*ᵥ` on `basisVec`, 4 data inputs × 2 branches),
   reusing the Stage 6a gate lemmas (`gateU_*_mulVec`, `invSqrtTwo_mul_self`, the ω lemmas),
   then extend to the matrix identity by `Matrix.ext`/linearity. Close its SORRIES.md row with
   this commit's hash (follow-up line in the same commit message is fine: "closes …").
3. **Composition — prove** `channelDenote_append`: for well-formed `C₁`, `C₂` on the same
   register whose classical bits are disjoint and such that `C₂` reads no bit written by `C₁`,
   `channelDenote (C₁ ++ C₂) = channelDenote C₂ ∘ₘ channelDenote C₁` (define `Circuit.append`
   if missing; state the bit hypotheses as `Bool` checks with a `decide`-friendly form so later
   instances discharge them automatically). If the bit-numbering of `krausOps` (`bitVal` with
   `m = nBits`) makes the statement false or awkward, **stop and report** with a proposal
   (e.g. renumbering bits on append) — do not change `krausOps` silently; it is used by the
   proved `krausOps_complete`.
4. **Corollary — prove** `AncRestore.comp`: `AncRestore C₁ U₁ → AncRestore C₂ U₂ →`
   (hypotheses of task 3) `→ AncRestore (C₁ ++ C₂) (U₂ * U₁)`. This is the step the 6b induction
   over the AND list will use.

## Tests

`tests/CQRVTests/Semantics.lean`: `#print axioms` for `ancRestore_of_kraus`,
`mbu_channel_correct`, `channelDenote_append`, `AncRestore.comp` — each must show only `propext`,
`Classical.choice`, `Quot.sound`. One `#guard` that the bit-disjointness check of task 3 holds
for (compute-AND₁ ++ compute-AND₂) of the Grover oracle and fails for a pair that shares a bit.

## Acceptance

- `lake build` green, check scripts pass; SORRIES.md: `mbu_channel_correct` closed (hash), no
  new rows unless an item got stuck (then: the stuck goal, verbatim, in the row).
- DECISIONS.md: the template-lemma approach and the bit hypotheses of the composition lemma.

## Stop conditions

- Task 3 needs a change to `krausOps` or `channelDenote` → stop and report (see above).
- The per-branch identity of task 2 is false in Lean for some basis input → stop and report
  the computed vector (it would contradict both the hand computation and the Stage 5 harness).
- Do not start the per-AND lift, the Z-phase lemma or `lemma_6_3_2`.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which items closed, the exact Kronecker shape you had
to use for `ρ ⊗ᴹ ancZero`, and anything the later induction will need that is still missing.
