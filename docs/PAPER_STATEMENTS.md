# The paper's Lean statements, aligned with the library (revision R10)

REVIEW_RESPONSE_1 §4 R10; docs/tasks/REVB_TASK.md. Paper v2, Appendix A, transliterates the library's
statements by hand with implicit and instance arguments abbreviated. `tests/CQRVTests/PaperStatements.lean`
restates each of them in full as an `example` proved by the library name applied to its arguments, so the
kernel confirms that the stated form is the library's (it builds with `lake build`; no CI step changes).
The table gives, for every name of the appendix, the declaration in the library and the lines of the
restatement. Line numbers are those of the R10 commit on `rev-b` and move with later edits; the names do not.

Comparison with Appendix A (2026-11-16): no statement differs in substance. The abbreviations the appendix
uses are the ones its preamble announces (implicit arguments and type-class assumptions dropped,
`N = n + (a + bb)`, `X⁺`, `g_phys`), plus three notational ones: `grover_parametric_lemma_diff` takes `C`
implicitly in the library; `mbu_exactly_quadratic` writes `g.qubitsOk n = true ∧ g.isUnitary = true`
(Bool equalities, not coerced propositions); `diamondDist_mix_le` has the explicit cast `2 * (p : ℝ)`.

| Name | Library | Test lines |
|---|---|---|
| `Realizes` | `CQRV/Realizability/Realizes.lean:59` | 56–61 |
| `RealizesExact` | `CQRV/Realizability/Realizes.lean:68` | 63–67 |
| `AncRestore` | `CQRV/Circuit/Restoration.lean:132` | 69–72 |
| `diamondDist` | `CQRV/Realizability/Diamond.lean:33` | 74–77 |
| `no_cloning_linear` | `CQRV/Realizability/Obstruction.lean:66` | 81–83 |
| `no_cloning_pure` | `CQRV/Realizability/Obstruction.lean:128` | 85–89 |
| `pure_cloning_of_card_one` | `CQRV/Realizability/Obstruction.lean:151` | 91–95 |
| `measured_composition_pseudo` | `CQRV/Realizability/Composition.lean:207` | 99–109 |
| `coherent_composition_diamond` | `CQRV/Realizability/Coherent.lean:77` | 111–121 |
| `lemma_6_3_2_xor` | `CQRV/Circuit/OracleCorrect.lean:1146` | 125–127 |
| `synthesizeOracle_WF` | `CQRV/Circuit/OracleCorrect.lean:1693` | 129–130 |
| `synthesizeOracle_succeeds` | `CQRV/Circuit/OracleCorrect.lean:2109` | 132–134 |
| `grover_parametric_lemma_diff` | `CQRV/Grover/Lemma.lean:760` | 138–144 |
| `mczFew_logDepth_ok` | `CQRV/Grover/MczFewAll.lean:1450` | 146–146 |
| `mczFew_logDepth_ancRestore` | `CQRV/Grover/MczFewAll.lean:1370` | 148–150 |
| `diffusionFew_logDepth_ancRestore` | `CQRV/Grover/MczFewAll.lean:1390` | 152–154 |
| `qpe_success` | `CQRV/Grover/Counting.lean:419` | 159–163 |
| `ae_parametric_lemma` | `CQRV/Grover/AmplitudeEstimation.lean:226` | 165–172 |
| `aqft_diamond_le` | `CQRV/Circuit/QFTCorrect.lean:718` | 174–177 |
| `mbu_general` | `CQRV/Circuit/MBUGeneral.lean:338` | 181–185 |
| `clifford_iff_quadratic` | `CQRV/Circuit/MBUClifford.lean:522` | 187–188 |
| `mbu_exactly_quadratic` | `CQRV/Circuit/MBUBoundary.lean:742` | 190–194 |
| `supportFactor` | `CQRV/Circuit/RestoreRegimes.lean:691` | 196–198 |
| `ancRestoreCond_true_iff` | `CQRV/Circuit/RestoreRegimes.lean:716` | 200–202 |
| `problem1_T_lower_bound` | `CQRV/Synthesis/Problem1.lean:215` | 206–209 |
| `applyWitness_sound` | `CQRV/Hardware/WitnessSound.lean:1118` | 213–225 |
| `applyWitnessQ_ok` | `CQRV/Hardware/CheckSound.lean:743` | 227–229 |
| `applyWitnessQ_sound` | `CQRV/Hardware/CheckSound.lean:780` | 231–242 |
| `channelDenote_eq_steps` | `CQRV/Noise/Steps.lean:443` | 246–250 |
| `diamondDist_mix_le` | `CQRV/Noise/Perturb.lean:161` | 252–254 |
| `noisy_realization` | `CQRV/Noise/Realize.lean:89` | 256–265 |
| `phys_noisy_stochastic` | `CQRV/Noise/Stochastic.lean:166` | 267–293 |
