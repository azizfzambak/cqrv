# Paper 1 revision: a draft for the author (Stage 30c)

Written by the reviewer on 2026-11-16, under the author's delegation, for the author's approval.

**What this file is.** The current text of Paper 1 lives in `docs/paper/`, which the reviewer does
not read or edit (decision of 2026-10-29). This file is therefore self-contained:
- the revised claims, with their evidence and exact scope;
- a proposed structure for the revision;
- the numbers to quote, each with its source;
- draft paragraphs for the new parts.

The author merges what fits into the paper; the final text is the author's.

The sources are `docs/M3_REPORT.md` §7 (the M3 claims, carried over), `docs/M5_REPORT.md` (the
numbers at M5), PHASE2_SPEC §C (Track C) and `docs/DECISIONS.md`.

---

## 1. The paper's thesis, as M5 supports it

> A certifying compiler for quantum programs can carry a classical specification to a Lean
> certificate of (ε, δ)-realization, and further, through an untrusted industrial transpiler, to a
> physical circuit on a device description, with every step either checked by the Lean kernel or
> stated as a named premise.

**The two halves of the evidence:**
1. **The logical half (M3).** Grover search and quantum counting are certified end to end.
   Selection under a budget is certified, the front end is proved, and Theorems 3.3a and 3.3b are
   proved and used.
2. **The physical half (Track C, Stages 24–27).**
   - For the committed instances, Lean checks the chain from the logical certificate to the routed
     physical circuit on a fake IBM backend: the translation, the routing and reordering, and the
     instance facts.
   - A certified realization transfers to the physical circuit.
   - Under four named premises, a conditional realization holds with an exact noise bound.

**The honest headline** (27c review, decision 2). The framework reaches a device description. It
does not reach useful problem sizes on the 2025-era calibrations shipped with the fake backends:
- the conditional bound is non-vacuous only for n ≤ 3 on FakeTorino and n ≤ 2 on FakeWashington;
- the 8-qubit running example stands at 2.9.

## 2. Claims (carried from M3, updated, and new)

### 2.1 Carried from M3 §7, unchanged

These are carried unchanged; M3 §7 gives the evidence and scope column for each:
- Grover search is certified end to end.
- Quantum counting is certified for the committed instance, universally in M ≥ 1.
- The matcher is sound and complete on its fragment.
- Both patterns are instances of Definition 4.1.
- Selection under a budget is certified.
- The front end is proved.

### 2.2 Updated

| Claim | Evidence | Exact scope |
|---|---|---|
| Theorem 3.3a is exercised | `search_unknown_M`, `domain_8_32_5`, `search_unknown_M_8_32_5` (21b2) | (n, M, m) = (8, 32, 5); honest g2 (15, 794, 432, 7) at r = 12; composite (21, 3656, 1796, 8); no composition certificate |

### 2.3 New (Track C)

| Claim | Evidence | Exact scope |
|---|---|---|
| The table translation preserves the channel | `decomp_sound` (every entry, with `irPhase`), `translate_sound` | the two bases (cz, cx) of the targets; global phases cancel per branch |
| Routing by an untrusted transpiler is validated | `applyWitness_sound`, through `applyWitnessQ_ok`; the per-instance `recon` (kernel) | SabreLayout routing with the order-recording witness; injective initial layout; block SWAPs that compose to the identity |
| Every committed routed circuit is checked | 15 `examples/hw_checks/*/Check.lean`: `recon`, `edges_ok`, `phys_channel`, `phys_zero` | the committed artifacts; ideal device; start from all-\|0⟩ on the used qubits |
| A certified realization transfers to the physical circuit | `phys_realizes` in `examples/certs/grover_pred_037_torino/PhysCert.lean`; the link `emitted_eq` (no axioms) | δ = 7/128 on the routed 2 541-gate circuit on FakeTorino; ideal device |
| The physical grade and selection by it are certified | `PhysGrade` by kernel; `selectPhys_spec`, `selectKey_spec`, `selectNoise_spec`; 4 `Select.lean` | exact ASAP depth at a named feed-forward latency (an assumption); Lean = Python on the committed artifacts |
| Noise is bounded under named premises | `noisy_realization`, `channelDenote_eq_steps`, `diamondDist_mix_le`, `phys_noisy_stochastic` | any noise within η_i per listed step; (P-stoch) gives 2p per operation on the full register |
| Conditional certificates exist for small instances | `phys_noisy_inst` (hw_n2 0.1793, hw_n3 0.7521, three frontier instances 0.21–0.78), `gadget_noisy` (0.0995) | (P-cal) the shipped snapshot; (P-stoch) the Pauli reading p = (d + 1)/d · r with clamp; (P-ro); (P-idle) |
| The feasibility frontier on two fake devices | `docs/hw_frontier/FRONTIER.md` | Grover on x_0 ∧ … ∧ x_{n−1}, M = 1, n = 2…7, three modes, two routings; measured, not certified |

### 2.4 Claims not to make (M3's list, extended)

- "verified on hardware", or that any run validates a certificate. No device was run; the
  emulator comparisons are sanity checks, and the emulator's noise model is not of the (P-stoch)
  form.
- That the premises hold of a device. (P-stoch) is a reading of RB errors; (P-idle) is the
  furthest from a device (idle/T2 up to 0.38 at the frontier, above 1 at n = 5); (P-cal) is a
  shipped snapshot from a past date.
- That the framework reaches useful sizes on today's calibrations.
- That Qiskit or Aer is verified. Each is an untrusted tool whose output is checked or stated as
  a premise.
- That routing is optimal, or noise-aware beyond the pruned coupling map.
- Everything in M3's list of claims not to make: the counting grade is a composed bound; no claim
  for M = 0; matcher completeness only on the fragment; the emitted QIR / QASM is
  translation-validated only.

## 3. Proposed structure of the revision

1. **Introduction:** the thesis of §1, and the contributions (logical half, physical half,
   frontier).
2. **Background:** realizability, grades, QPLP, the kernel discipline (as before, shortened).
3. **The logical pipeline:** as before, with Theorem 3.3a exercised (21b2) and the counting
   pattern.
4. **(new) From certificate to device.** The witness architecture (untrusted tool, checked
   witness), the theorem chain (translation, routing, reordering, the embedding), the linear
   kernel check, and the per-instance files.
5. **(new) The physical certificate.** `phys_realizes`, `PhysGrade` with its timing model, the
   status words, and selection by a physical component.
6. **(new) Noise as a premise.** The step semantics, `noisy_realization`, the four premises, the
   conditional certificates, the frontier and the idle diagnostic.
7. **Evaluation.**
   - Kernel times: the logical certificates, and the 15 check files at 10–31 s and ≤ 4.1 GB.
   - The CI: 26 steps.
   - The frontier table.
8. **Related work.** Verified compilation (SQIR / VOQC and others; see `docs/STAGE29_NOTE.md` for
   what is and is not compared), translation validation, and certified resource analysis.
9. **Limitations and future work.** Device runs (Stage 28, the author's decision), randomized
   compiling, idle noise in the bound, count selection, noise-aware routing.

## 4. Numbers to quote, with sources

| Figure | Value | Source |
|---|---|---|
| Running example, logical | (15, 134, 72, 7), δ = 7/128 | `examples/certs/grover_pred_037` |
| Running example, physical on FakeTorino | 16 qubits, 315 two-qubit, 18 mid-circuit measurements, 624 feed-forward; depth ≈ 33 740 ns at L = 0, ≈ 43 740 ns at L = 1 000 ns | `examples/certs/grover_pred_037_torino` (`physGrade_L0`, `physGrade_L1000`) |
| Running example, conditional bound | 2.8990 (vacuous); 25a's p = r reading 2.4495 | `cqr hw noise`; `docs/hw_frontier/FRONTIER.md` |
| hw_n2, hw_n3 on FakeTorino | δ' 0.1793, 0.7521 | `examples/certs/hw_n2_torino`, `hw_n3_torino` |
| The MBU gadget | δ' 0.0995 | `examples/certs/mbu_gadget_torino` |
| Frontier | n = 3 on FakeTorino (all modes), n = 2 on FakeWashington | `docs/hw_frontier/FRONTIER.md` |
| Check files | 15 files, 10–31 s each, ≤ 4.1 GB | `examples/hw_checks/README.md`; M5_REPORT §1.2 |
| Physical certificate kernel time | 53–55 s, 4.1 GB | M5_REPORT §1.2 (53 s in the 30a CI log) |
| Code size | 39 114 lines of Lean in 111 modules; the `cqr` closure (62 modules) is Physlib-free | M5_REPORT §4 |

Every figure is to be re-read from M5_REPORT before quoting.

## 5. Draft paragraphs

**Contribution (physical half).** We extend the certifying pipeline past the logical circuit. An
industrial transpiler (Qiskit) routes the circuit on a device's coupling map; it is untrusted, and
records a witness of its choices. A Lean function reconstructs the physical circuit from the
logical one and the witness, and the kernel checks the reconstruction against the transpiler's
output. A theorem, `applyWitness_sound`, states that whenever the reconstruction succeeds, the
physical channel is the logical channel up to the initial and final layouts. A certified
realization therefore transfers to the routed circuit without re-verifying the circuit.

**Noise.** We do not claim a device behaves as its calibration says. We state the bridge as
premises and prove the rest:
- if every operation is, with probability at least 1 − p_i, its ideal channel and otherwise
  arbitrary, the realization holds with δ + Σ p_i;
- the p_i are read from the calibration by the Pauli reading of randomized-benchmarking errors.

The resulting certificates are conditional, and every manifest names its premises. On two fake
IBM backends the bound is non-vacuous only up to three data qubits, a measured frontier rather
than a limitation of the method's soundness.
