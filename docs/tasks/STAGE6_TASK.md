# Stage 6a — Circuit semantics, TempLogicalAND correctness, statements of MBU and Lemma 6.3.2

Report sections: §9.1.1 (gate-level AST with unitary and density-matrix semantics into Physlib
channels), §6.2.2 (TempLogicalAND listing; MBU correctness is a channel-level statement),
§6.2.4 (restoration proof structure, Layers 1–3; Layer 2 uses Lemma 6.3.2, **not** Theorem 3.3a),
§6.3.2 (Lemma 6.3.2 on density operators), §6.2.1 (factorization |ψ_out⟩ ⊗ |0…0⟩_anc).
Precondition: Stage 5 accepted (main = faf8e43). `git switch -c stage-6 main`; one commit;
include this file (untracked) in it. Windows: `LEAN_NUM_THREADS=4`. Module system.
This is a **proof stage**: state first, prove only what is asked (CLAUDE.md rule 8).

## Facts the reviewer already checked (do not re-derive, but do not trust blindly either)

- The §6.2.2 compute listing (13 gates) maps |a, b, 0⟩ ↦ |a, b, a∧b⟩ **exactly, with phase 1**,
  for all four (a, b) (numpy check by the reviewer; Stage 5 harness agrees). So
  `tempLogicalAND_correct` below is a true statement.
- Physlib (pinned commit, no `sorry` in these files): `CPTPMap.of_kraus_CPTPMap`
  (`Channels/Bundled.lean`, needs `∑ k, (M k)ᴴ * M k = 1`), `CPTPMap.ofUnitary`
  (`𝐔[d]` = `Matrix.unitaryGroup d ℂ`), `CPTPMap.traceRight`, `MState.prod` (`⊗ᴹ`),
  `MState.traceRight_prod_eq`, `MState.pure`. `#check` each before use (rule 2); if one is
  missing, stop.

## Reviewer decisions (record each in DECISIONS.md, dated, with "Rejected:")

1. **Register.** Basis index `Reg k := Fin k → Bool`; the oracle acts on `Reg n × Reg a`
   (data × ancilla) so that `CPTPMap.traceRight` traces out the ancilla.
2. **Measurement semantics by branches (Kraus).** For a circuit with m classical bits, each
   assignment `c : Fin m → Bool` gives one Kraus operator `K_c` = the gate product in which
   `measure q → j` is the projector onto `q = c j` and `ifBit j g` is `g` if `c j` else `1`.
   The channel is `ρ ↦ ∑_c K_c ρ K_cᴴ` via `of_kraus_CPTPMap`. This is exactly what the Python
   harness enumerates. `alloc`/`free` are the identity (the register has fixed size; that
   ancillae come back as |0⟩ is what `AncRestore` proves, not something the semantics assumes).
   Rejected: a classical-register channel `Reg n × Reg a × Reg m` (heavier, no gain for MBU).
3. **Well-formedness** `Circuit.WF`: qubit indices in range, every classical bit written by
   exactly one `measure` before any `ifBit` reads it, gate operands distinct. All theorems
   assume `WF`.

## Tasks (`CQRV/Circuit/Semantics.lean`, `CQRV/Circuit/Restoration.lean`; doc-comment each with its §)

1. **Unitary fragment.** `gateMatrix` for H, S, S†, T, T†, X, Z, CNOT, CZ on `Reg k`
   (define by basis action; `T` phase `ω := Complex.exp (π/4 · I)` with the lemmas you need
   such as `ω ^ 2 = I`, `ω * star ω = 1` proved, not assumed); `unitaryDenote` for circuits
   without `measure`/`ifBit`; **prove** each gate matrix is in `unitaryGroup` and that
   `unitaryDenote` of a unitary-fragment circuit is too.
2. **Kraus semantics** (decision 2): `krausOps`, the completeness lemma
   `∑ c, (K_c)ᴴ * K_c = 1` (**attempt**: induction over the gate list — unitary gates preserve
   it, a measurement splits it by `P₀ + P₁ = 1`, an `ifBit` after its measurement keeps it);
   then `channelDenote : CPTPMap (Reg n × Reg a) (Reg n × Reg a)`. If completeness does not close
   in 3 build–fix rounds, it becomes a tracked `sorry` — note that every downstream theorem then
   inherits `sorryAx`, and list its sub-lemmas in SORRIES.md.
3. **`tempLogicalAND_correct`** (Layer 1 core) — **prove**: on 3 qubits (a, b, t) = (0, 1, 2),
   for all a b : Bool, `unitaryDenote TempLogicalAND · |a, b, false⟩ = |a, b, a && b⟩`.
   Work on state vectors over basis inputs (gate by gate, `simp`/`ring_nf` with the ω lemmas),
   not by multiplying 8×8 matrices. If it does not close in 3 rounds, record exactly which gate
   step is stuck. Also **state** the lift to an arbitrary register (distinct `a b t`, `s t = false`)
   — prove it if the 3-qubit proof transfers directly, otherwise tracked `sorry`.
4. **`mbu_channel_correct`** — **state only**: on 3 qubits, for every `ρ : MState (Reg 2)`,
   `channelDenote [TempLogicalAND; Z t; UncomputeTempLogicalAND] (ρ ⊗ᴹ |0⟩⟨0|) =
   (CZ ρ CZᴴ) ⊗ᴹ |0⟩⟨0|` (Z on a target holding a∧b is CZ on the controls; the target returns
   to |0⟩). Uncompute is the Stage 5 version **with** the `ifBit m (X t)` reset.
5. **`AncRestore`** (CLAUDE.md name, §6.2.1/§6.2.4 Layer 3): `AncRestore C U :=
   ∀ ρ : MState (Reg n), channelDenote C (ρ ⊗ᴹ |0…0⟩⟨0…0|) = (U ρ Uᴴ) ⊗ᴹ |0…0⟩⟨0…0|`.
   `phaseOracle P : 𝐔[Reg n]` = diag((−1)^P(x)) with its unitarity **proved**.
6. **`lemma_6_3_2`** — **state only**, parametric over the Stage 5 synthesizer:
   `synthesizeOracle N = .ok C → C.WF → AncRestore C (phaseOracle N.eval)` for AND/NOT/OR
   networks (Stage 5 decision 2). Then **prove** the report's traced form as a corollary from
   it: `traceRight (channelDenote C (ρ ⊗ᴹ |0⟩⟨0|)) = U ρ Uᴴ` (via `MState.traceRight_prod_eq`).
   Also state the `grover_pred_037` instance. Doc-comment: the statement is on density
   operators (not basis states — §6.2.4: on basis states the phase cancels), and Theorem 3.3a is
   **not** used inside the oracle (§6.3.2).
7. **SORRIES.md**: one row per remaining `sorry`, plus — for `lemma_6_3_2` — the proposed
   split into sub-lemmas for session 6b following §6.2.4 (per-AND compute lemma, per-AND MBU
   lemma via `mbu_channel_correct`, Z-on-last-ancilla = phase, induction over the AND list,
   the NOT/OR wrappers). The reviewer will turn each into its own task.

## Tests

`tests/CQRVTests/Semantics.lean`: `#print axioms` for every proved theorem (gate unitarity,
`tempLogicalAND_correct`, the traced corollary — the corollary will show `sorryAx` through
`lemma_6_3_2`; say so). A `#guard`-level check that `Circuit.WF` holds for the Stage 5 Grover
oracle and fails for a circuit reading a classical bit before writing it.

## Acceptance

- `lake build` green; every `sorry` in SORRIES.md with report §, dependencies, size.
- Proved: gate unitarity, `phaseOracle` unitarity, `tempLogicalAND_correct` (3-qubit) — or the
  stuck step documented; the traced corollary from `lemma_6_3_2`.
- Stated with the exact shapes above: Kraus completeness (proved or tracked), MBU, `AncRestore`,
  `lemma_6_3_2`, the Grover instance.
- DECISIONS.md: decisions 1–3.

## Stop conditions

- A Physlib name above is missing or has a different shape → stop.
- `tempLogicalAND_correct` turns out false in Lean (not just hard) → stop and report the
  computed output (it contradicts the reviewer's numpy check, so something is off in the
  semantics).
- Do not attempt `mbu_channel_correct` or `lemma_6_3_2`; do not start Stage 7 or 8.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): whether Kraus completeness closed, the proposed 6b
split, and any place where Physlib's API forced a different statement shape.
