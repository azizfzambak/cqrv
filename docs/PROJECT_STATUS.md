# CQRV — project status (2026-10-26)

One-page state of the repository after Stages 0–12b. The specification is report v3
(`docs/cqrv_report_revised_v3.docx`, tracked changes over v2, errata appendix). Details:
`docs/M2_REPORT.md` (milestone M2, frozen, with post-M2 notes), `docs/DECISIONS.md` (every decision),
`docs/SORRIES.md` (obligations). Toolchain: Lean 4.35.0, Mathlib v4.35.0, Physlib 96a6bc5.

## 1. Machine-checked (no `sorry` in the repository; axioms only `propext`, `Classical.choice`, `Quot.sound`)

| Result | Report § |
|---|---|
| Grover parametric lemma — realization ∧ ancilla restoration, every `r` (`grover_parametric_lemma`, `grover_parametric_lemma'`) | §8.2–8.3, Fig. 8.1 |
| Lemma 6.3.2 for every network the synthesizer accepts, XOR and `if` included (`lemma_6_3_2_xor`); every synthesized oracle is well formed (`synthesizeOracle_WF`) | §6.3.2, §6.2.4 |
| MBU correctness on density operators (`mbu_channel_correct`); Gidney's TempLogicalAND on any register | §6.2.2 |
| Theorem 3.3a, measured composition, ε = 0 and general ε (`measured_composition_exact`, `measured_composition`) | §2.3.2 |
| Theorem 3.3b, coherent composition, for any channel distance dominating twice the trace distance (`coherent_composition`); trace-distance triangle, data processing, measurement bound | §2.3.2 |
| Theorem 3.1 in its concrete linear-algebra form (`no_cloning_obstruction`) | §2.2.2 |
| Soundness of the Miller-pattern matcher (`millerMatch_sound`) | §4.1.2 |
| Exact δ for every `r` (`sin_sq_odd_mul`); balanced-tree MCZ computes y₀ ∧ … ∧ yₙ₋₁ (`treeNet_pred`) | §8.2, §6.1.4 |

## 2. Certificates (`cqr certify`, `examples/certs/`)

| | `grover_pred_037` (Chapter 8) | `simple_alu_x0_1` (RevLib Simple ALU, one bit) |
|---|---|---|
| Status | certified (conditional on: solution_count = 32) | certified (conditional on: solution_count = 30) |
| Grade (w, d, t, a), measured | (15, 134, 72, 7) | (16, 121, 60, 10) |
| δ (exact) | 7/128 | 833/2048 |
| Kernel check (i9-13900H, 4 threads) | 7.2 s | 6.4 s |
| `--profile ibm_kyiv` (report Table 3.5 figures) | fits all budgets; δ_hw ≤ 2531/640 (vacuous) | fits all budgets; δ_hw ≤ 39493/10240 (vacuous) |
| `--shape few:log` (2-ancilla diffusion, Stage 12d; `examples/certs/grover_pred_037_few`) | certified (conditional on: solution_count = 32) via the every-n theorem (`grover_certificate_few_all`, KG Theorem 5.1 for every n; Stage 13a, 13a′; no per-instance classical check); (10, 172, 96, 2); δ 7/128; kernel 22.6 s (slow regime; 5.9 s fast, DECISIONS.md 2026-10-28); ibm_kyiv fits all budgets, δ_hw ≤ 2467/640 (vacuous) | — (not requested) |

The chain-shaped diffusion of the earlier stages, (15, 230, 72, 7), is kept as `*_chain` theorems.

## 3. Declared trust boundaries (outside the kernel)

- **Front end**: DSL → network (`toNetwork`) — exhaustively validated on all 2ⁿ inputs (n ≤ 16), not proved.
- **Emitter**: QIR (Adaptive Profile) / OpenQASM 3 text — unverified, translation-validated by re-parse; QIR verified with llvmlite.
- **Solution count M**: a hypothesis of every certificate (`hM_card`), never decided by enumeration.
- **Hardware**: routing, native-gate translation and calibration noise are the backend's; the profile check uses the report's illustrative Kyiv figures. δ_hw is vacuous at p̄ = 10⁻² (G·p̄ ≥ 1) — needs error correction or mitigation.

## 4. Open

| Item | Kind |
|---|---|
| Diamond norm and the domination lemma ‖Λ₁ρ − Λ₂ρ‖₁ ≤ ‖Λ₁ − Λ₂‖⋄, to instantiate Theorem 3.3b concretely | Phase III proof |
| `synthesizeOracle_succeeds` (synthesis succeeds on every well-formed one-output network) | planned row |
| Theorem 3.1 in categorical form; `toNetwork` well-formedness proof | documented gaps |
| Remote CI (only `scripts/ci_local.sh` has run) | engineering, reviewer's choice |

## 5. Reproduce

```bash
lake exe cache get && lake build
scripts/ci_local.sh
.lake/build/bin/cqr certify examples/grover_pred_037.cqr --profile ibm_kyiv
```
