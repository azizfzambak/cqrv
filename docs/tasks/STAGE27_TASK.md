# Stage 27 — The noise theorem and the conditional certificate (PHASE2_SPEC §C.4; Track C, Paper 1)

PHASE2_SPEC.md §C.4. Report: §2.3.2 (Theorem 3.3b), §6.6, §3.1.3. PHASE2_ROADMAP row 27. Written
at the 26c2b review (2026-11-16) by the reviewer, under the author's delegation.

Stage 27 has three tasks, one commit each:
- **27a**, the Lean theory, is specified here;
- **27b**, the conditional certificates, and **27c**, the frontier, are outlined and get their
  detailed text at the 27a review.

Precondition: main = the 26c2b review commit. Start with `git switch -c stage-27a main`.

**Invariants of Stage 27:**
- No existing theorem statement changes; `channelDenote`, `Circuit.WF` and `diamondDist` are
  unchanged.
- No committed certificate, check file or artifact is regenerated. New ones may be added in
  27b–27c.
- Every existing `cqr` output stays byte-identical. The cqr closure stays Lean + Mathlib, so the
  noise theory is Physlib-side.
- No `sorry`, no `native_decide`, no new download. No output says "verified on hardware". A
  conditional certificate names every premise it rests on.
- If a statement here is false, give the counterexample and the corrected form. CLAUDE.md rule 2
  applies.

---

## 27a — The step semantics, the perturbation bound, `noisy_realization`

### N1. The extended register and the step channels (`CQRV/Noise/Steps.lean`)

- **The register.** `X⁺ := (Reg n × Reg a) × Bits m`, with `Bits m := Fin m → Bool` as a basis
  type (or `Reg m`; say which).
- **The step channels** (`stepK`, or a `CPTPMap` per gate, your choice of form):
  - a unitary gate: `Ad(gateU g ⊗ 1)`;
  - `measure q → j`: the Kraus operators `projMat q v ⊗ flip_j^v`, v ∈ {0, 1}, where `flip_j`
    exchanges bit j. Prove it is a channel on every input;
  - `ifBit j g`: the controlled unitary `|0⟩⟨0|_j ⊗ 1 + |1⟩⟨1|_j ⊗ gateU g`.
- **`stepChan P`**: the composition over P's gates, first gate first. Also its list form, for the
  perturbation bound.
- **`traceBits`**, and `withBits ρ := ρ ⊗ |0…0⟩⟨0…0|`.
- **`channelDenote_eq_steps`**: for `P.WF`,
  `channelDenote n a P ρ = traceBits (stepChan P (withBits ρ))`.
  The suggested route:
  1. the product of the step Kraus operators along an outcome choice c is
     `krausOps n a m P.gates c ⊗ |c⟩⟨0|`; `bitsOk` gives each bit written once, from 0, before
     it is read;
  2. tracing out the bits leaves `Σ_c K_c ρ K_cᴴ`.

### N2. The perturbation bound (`CQRV/Noise/Perturb.lean`)

- **`diamondDist_precompose_le`**: `diamondDist (Ψ ∘ₘ Λ) (Φ ∘ₘ Λ) ≤ diamondDist Ψ Φ` for
  `Λ : CPTPMap B B` and `Ψ Φ : CPTPMap B C`. `(Λ ⊗ id) ρ` is again a state on `B × B`, which lies
  in the supremum's range.
- **`diamondDist_steps_le`**: for lists of channels on one type with
  `diamondDist (Ψs i) (Φs i) ≤ η i`, the compositions are within `Σ η i`.
- **`diamondDist_mix_le`**: `diamondDist (mix p Φ Φ') Φ ≤ 2 * p` for `0 ≤ p ≤ 1`, where
  `mix p Φ Φ' := (1 − p) • Φ + p • Φ'` as a `CPTPMap`. Use Physlib's convex combination of
  channels if it exists (`#check` it first), otherwise define it.

### N3. `noisy_realization` (`CQRV/Noise/Realize.lean`)

- **`noisy_realization`**, stated for `RealizesExact` and for `Realizes`:
  - *hypotheses:* the ideal composite `Γ ∘ₘ traceBits ∘ₘ steps Φs ∘ₘ prep` realizes S with δ at
    grade r, and the noisy steps `Ψs` satisfy `diamondDist (Ψs i) (Φs i) ≤ η i`;
  - *conclusion:* the noisy composite realizes S with `δ + (Σ η i) / 2`, at the same grade.
  - Readout steps are ordinary list entries, placed after the circuit's steps.
- **`noisy_realization_stochastic`**: if `Ψs i = mix (p i) (Φs i) (Φ'ₛ i)`, the bound is
  `δ + Σ p i`.
- **`phys_noisy`**: the instance form on Stage 26's `physGroverChannel`.
  - *hypotheses:* `realizesExact_phys`'s hypotheses, plus a noisy step list for
    `physCircuit N G` and the data readouts, with per-step bounds;
  - *conclusion:* the noisy physical channel `RealizesExact` S with δ plus half the sum.
  - It follows from `channelDenote_eq_steps` and `noisy_realization`.

### N4. Tests (`tests/CQRVTests/Noise.lean`)

- `channelDenote_eq_steps` on the MBU gadget.
- `diamondDist_mix_le` at p = 0 (the distance is 0) and p = 1.
- `noisy_realization_stochastic` on a toy one-gate circuit.
- `#print axioms` of `channelDenote_eq_steps`, `diamondDist_steps_le`, `diamondDist_mix_le`,
  `noisy_realization` and `phys_noisy`.

### 27a Docs / Acceptance / Stop

- **Docs:** DECISIONS.md (one entry), PROJECT_STATUS.md, the README status line.
- **Acceptance:**
  - `lake build` green and warning-free;
  - the axiom lines, the standard three;
  - the existing CI pass mark (25) unchanged; 27a adds no CI step.
- **Guards.** Stop and report if:
  - 27a goes above about 1 200 lines, or a single proof above about 500;
  - a hypothesis is missing.

  `channelDenote_eq_steps` is the one proof allowed to approach 500. If it goes beyond, stop
  after N1 and report.

## 27b — The conditional certificates (outline)

- **The bound.** `noiseBound`, Physlib-free: `δ + Σ (d_i + 1)/d_i · r_i + Σ r_j`, exact, on the
  rate tables. Lean equals Python on all twelve artifacts, and 25a's `p = r` figure is reported
  beside it.
  - The rate of an operation is keyed as `rateOf` keys it: the directed pair or its reverse.
  - The literals of `SelCand` and `selectFile` are reused, not generated anew.
- **The `noise` preference.** `noiseBound` becomes a `PhysPref` component. A budget `noise < 1`
  is then a certified admissibility test: an admissible candidate has a non-vacuous conditional
  realization.
- **Logical certificates for hw_n2 and hw_n3**, new directories made by `cqr certify`.
- **The conditional certificates of hw_n2, hw_n3 and the MBU gadget on FakeTorino:**
  - `phys_noisy` at the instance, with the premises (P-cal) as a hash and (P-stoch), (P-ro) as the
    hypotheses' form;
  - the gadget in channel form;
  - the status word `noise_conditional` with the list of premises;
  - (P-idle) stated in the manifest.

## 27c — The feasibility frontier (outline)

- **The family:** Grover on n = 2…8 with an increasing number of ANDs, in the three modes, on
  both targets.
- **Routing** also on the coupling map with the edges of error ≥ 0.5 removed, with the witness and
  `edges_ok` unchanged.
- **The table**, in `docs/hw_frontier/FRONTIER.md`: two-qubit count, depth, the conditional
  bound, and the largest non-vacuous instance per target and mode.
- **The idle-exposure diagnostic**, from the ASAP schedule: idle time over T2 per qubit. It is
  reported, not certified.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
