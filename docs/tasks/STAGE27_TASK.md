# Stage 27 — The noise theorem and the conditional certificate (PHASE2_SPEC §C.4; Track C, Paper 1)

PHASE2_SPEC.md §C.4. Report: §2.3.2 (Theorem 3.3b), §6.6, §3.1.3. PHASE2_ROADMAP row 27. Written
at the 26c2b review (2026-11-16) by the reviewer, under the author's delegation.

Stage 27 has three tasks, one commit each:
- **27a**, the Lean theory, is specified here;
- **27b**, the conditional certificates, is specified below (written at the 27a review);
- **27c**, the frontier, is outlined and gets its detailed text at the 27b review.

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

## 27b — The conditional certificates (written at the 27a review, 2026-11-16)

Precondition: main = the 27a review commit; start with `git switch -c stage-27b main`.

### B1. `phys_noisy_stochastic` (Physlib-side, `CQRV/Noise/Realize.lean` or a new file)

- **Basis operations.** The premise attaches to basis operations, not IR gates: `sx` expands to
  three IR steps (`h, s, h`).
- **`steps_flatMap`.** `steps (G.flatMap (stepList ∘ expand))` equals the composite of the
  per-basis-gate composites `steps (stepList (expand g))`.
- **The statement.** Take:
  - per basis gate g of G, a `p_g : Prob`;
  - per data readout j, an `r_j : Prob`;
  - arbitrary channels `Φ'_g` and `Φ'_j` on `X⁺`, universally quantified.

  The noisy channel replaces each basis gate's composite by `mix p_g (composite) Φ'_g` and
  appends `mix r_j id Φ'_j` per data qubit. **The claim:** for every choice of the Φ', the noisy
  physical channel `RealizesExact` S with `δ + Σ p_g + Σ r_j`.
- **The proof.** It follows from `phys_noisy` and `diamondDist_mix_le` termwise. The certificate's
  theorem is then a one-line instance.

### B2. `noiseBound` (Physlib-free; in the cqr closure)

- **The definition.** `noiseBound = δ + Σ_g p_g + Σ_j r_j`, exact in `Rat`, on the rate tables of
  `PhysGrade` (`rateOf`: the directed pair or its reverse).
- **(P-stoch).** For a gate on k qubits, `p_g = min 1 ((d+1)/d · r_g)` with d = 2^k:
  - this is 3/2 · r for `sx` and `x`, and 5/4 · r for `cz`;
  - `rz` is virtual: r = 0, so p = 0;
  - a conditioned gate takes the rate of its gate.
- **(P-ro).** A mid-circuit measurement and a data readout take `p = r_j`, the readout rate, with
  no factor.
- **The clamp.** A `clamped` flag records whether some p reached the clamp. Then the bound is ≥ 1,
  so vacuous. The fakes' error-1.0 edges give 5/4 before the clamp.
- **Python.** A mirror in `hw/`. Lean must equal Python on all twelve artifacts. 25a's `p = r`
  figure is printed beside it.
- **Selection.** `PhysPref.noise`, with the `noise` rows added to `examples/hw_select/README.md`.
  The committed `Select.lean` files are not regenerated.

### B3. Logical certificates for hw_n2 and hw_n3

- **The certificates.** `cqr certify` on `examples/hw_n2.cqr` (n = 2, M = 1, r = 1) and
  `examples/hw_n3.cqr` (n = 3, M = 1, r = 2), tree, mbu. They are new directories
  `examples/certs/hw_n2` and `examples/certs/hw_n3`; no existing certificate changes.
- **The link.** Their `emitted` must be the artifacts' logical circuits, by the same `circuitHash`.
  If not, stop and report.

### B4. The conditional certificates (`cqr hw certify --noise`, or a new subcommand; say which)

- **For hw_n2 and hw_n3 on FakeTorino:**
  - `examples/certs/hw_n2_torino` and `examples/certs/hw_n3_torino`;
  - 26c2's content: `emitted_eq`, `phys_channel`, `phys_zero`, `phys_realizes`, `PhysGrade`;
  - **`phys_noisy_inst`**: for every choice of the arbitrary channels, the noisy physical channel
    realizes the specification with δ' = `noiseBound` (as a real). The link between the real sum
    of the `Prob`s and the `Rat` is decided by the kernel;
  - `noiseBound_eq` by `decide +kernel`.
- **For the MBU gadget**, the channel form. For every choice of the arbitrary channels, the noisy
  physical channel's output is within `Σ p_g` in trace distance of σ_f's embedding of the gadget's
  correct output (`mbu_channel_correct` through `phys_channel`).
- **The manifest:**
  - the status word `noise_conditional`, with `noise_bound` (exact, plus a rounded display),
    `noise_bound_vacuous`, `clamped` and the 25a figure;
  - the four premises as text: (P-cal) with the snapshot hash and "shipped with
    qiskit-ibm-runtime, recorded from a real device on a past date"; (P-stoch) with the Pauli
    reading and the clamp; (P-ro); (P-idle);
  - **the meaning sentence:** "conditional on the premises, the device's success probability is at
    least 1 − δ'; the premises are assumptions about the device, not facts proved here; not
    verified on hardware".
- **The emulator comparison.** Apply 25b's own acceptance criterion to the recorded run JSON with
  the new δ'; do not re-run. Give `emulator_validated` only if it passes. Report the comparison,
  and note that the emulator's noise model is not of the (P-stoch) form.

### B5. CI

A step "Noise certificates" runs:
- `lake env lean` on the two new logical certificates and the three conditional ones;
- the Lean–Python `noiseBound` equality on the twelve artifacts;
- the regeneration of the new files byte for byte.

The pass mark becomes 26.

### 27b Acceptance / Stop

- **Acceptance:**
  - `lake build` green and warning-free;
  - the axiom lines of `phys_noisy_stochastic` and of each `phys_noisy_inst`;
  - the table of the twelve artifacts: 25a's figure, `noiseBound`, `clamped`, vacuous;
  - the δ' of hw_n2, hw_n3 and the gadget, with the emulator comparison.
- **Guards.** Stop and report if:
  - the task goes above about 1 200 hand-written lines (generated files do not count), or a
    single proof above about 500;
  - a hypothesis is missing;
  - B3's hash link fails.

  If the line guard comes near, stop after B3 and leave B4–B5 to a 27b2.

### 27b2 — B4–B5, the conditional certificates and the CI step (note added at the 27b review, 2026-11-16)

27b stopped after B3 at its guard. 27b2 does B4 and B5 above. Precondition: main = the 27b review
commit; start with `git switch -c stage-27b2 main`.

**Step 0, a time-boxed diagnosis (30 min, report only).** `examples/certs/hw_n2/Cert.lean` takes
256 s, hw_n3's 13 s.
- Find the slow declaration with `set_option profiler true` on a scratch copy, and say why it is
  slow.
- Neither the committed file nor the generator changes in 27b2. If the cause calls for a
  generator change, propose it for the 27b2 review.

**B4 as specified, with the implementer's design:**
- `phys_noisy_inst` for hw_n2 and hw_n3, a one-line instance of `phys_noisy_inst_of`, with
  `hkey` decided by the kernel;
- the gadget through `phys_noisy_channel_stochastic` and `mbu_channel_correct`, after
  `C = mbuCircuit` by the kernel. Its bound is 0.0995;
- the manifest with `noise_conditional`, the four premises and the meaning sentence;
- the emulator comparison computed by the generator, exactly in `Rat`, from the recorded run's
  `p_hat`, `shots` and `alpha`. `emulator_validated` is given only on a pass.

**Which runs exist.** The bare gadget has no recorded run, because 25b ran the wrapped gadget.
- The bare gadget's certificate carries `emulator_run: "no run recorded for this artifact"`.
- Whether the wrapped gadget gets a conditional certificate too is the implementer's call. It is
  not required.

**B5 as specified.** The pass mark becomes 26.

**The guards** of 27b hold; generated files do not count.

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
