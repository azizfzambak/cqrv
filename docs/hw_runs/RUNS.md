# Emulator runs on the fake backends' noise models (Stage 25b; PHASE2_SPEC §C.2)

Every row is an **emulator run on the fake backend's noise model** of a committed physical artifact of
Stage 25a (`hw/artifacts/`), by `hw/run.py --sim` (`scripts/hw_runs.sh`): Aer's `NoiseModel.from_backend`
restricted to the used qubits, the n data qubits read out at their final physical positions, the
success predicate P(x) (the all-zero readout for the wrapped MBU gadget). δ_hw is the bound on the
physical circuit from the artifact's manifest; the check is p̂ ≥ 1 − δ_hw − √(ln(1/α)/(2·shots)) at
α = 0.05, "vacuous" when δ_hw ≥ 1. Mid-circuit measurements carry the readout error (the Stage 24c
assumption). Nothing here is a device run or a validation of a certificate; the figures are reported,
not certified (Stage 27).

| instance | target | seed | shots | δ | δ_hw | ideal | p̂ | 95 % CP interval | check |
|---|---|---|---|---|---|---|---|---|---|
| grover_pred_037_fewlog_mbu | fake_torino | 25 | 2000 | 7/128 | 1.722 (vac.) | 0.9510 | 0.2865 | [0.2668, 0.3069] | vacuous (delta_hw >= 1) |
| grover_pred_037_tree_coherent | fake_torino | 25 | 2000 | 7/128 | 1.914 (vac.) | 0.9510 | 0.2775 | [0.2580, 0.2977] | vacuous (delta_hw >= 1) |
| grover_pred_037_tree_coherent | fake_washington | 25 | 2000 | 7/128 | 5.025 (vac.) | 0.9435 | 0.1355 | [0.1208, 0.1513] | vacuous (delta_hw >= 1) |
| grover_pred_037_tree_mbu | fake_torino | 25 | 2000 | 7/128 | 2.449 (vac.) | 0.9450 | 0.2510 | [0.2321, 0.2706] | vacuous (delta_hw >= 1) |
| hw_n2_tree_mbu | fake_torino | 25 | 4000 | 0 | 0.15 | 1.0000 | 0.8818 | [0.8713, 0.8916] | passes |
| hw_n3_tree_mbu | fake_torino | 25 | 4000 | 7/128 | 0.6484 | 0.9477 | 0.5903 | [0.5748, 0.6055] | passes |
| mbu_gadget_wrapped | fake_torino | 25 | 4000 | 0 | 0.1052 | 1.0000 | 0.8995 | [0.8898, 0.9086] | passes |
| simple_alu_x0_1_fewlog_mbu | fake_torino | 25 | 2000 | 833/2048 | 3.438 (vac.) | 0.6070 | 0.4565 | [0.4345, 0.4786] | vacuous (delta_hw >= 1) |
| simple_alu_x0_1_tree_coherent | fake_torino | 25 | 2000 | 833/2048 | 3.503 (vac.) | 0.5800 | 0.4770 | [0.4549, 0.4992] | vacuous (delta_hw >= 1) |
| simple_alu_x0_1_tree_coherent | fake_washington | 25 | 2000 | 833/2048 | 7.19 (vac.) | 0.6045 | 0.4500 | [0.4280, 0.4721] | vacuous (delta_hw >= 1) |
| simple_alu_x0_1_tree_mbu | fake_torino | 25 | 2000 | 833/2048 | 3.808 (vac.) | 0.5815 | 0.4615 | [0.4395, 0.4836] | vacuous (delta_hw >= 1) |

## Comment

Three instances have a non-vacuous bound on their physical circuit, and all three pass the one-sided
check: the wrapped MBU gadget (δ_hw 0.105; noisy p̂ 0.900 against the threshold 0.875), Grover n = 2
(δ_hw 0.150; p̂ 0.882 against 0.831) and Grover n = 3 (δ_hw 0.648; p̂ 0.590 against 0.332). In each
case the noisy frequency sits between the ideal (1.000, 1.000, 0.948) and the bound's floor
1 − δ_hw (0.895, 0.850, 0.352), as the union bound predicts: the bound is loose by a factor of 2–3
on the gadget and n = 2 (10 % loss observed against 10–15 % allowed) and by a factor of 1.2 on n = 3
(36 % observed against 65 % allowed). The eight committed-example instances have vacuous bounds
(δ_hw 1.7–7.2) and the check says so; their noisy frequencies fall to 0.25–0.29 for grover_pred_037
on FakeTorino (ideal 0.95) and 0.14 on FakeWashingtonV2, and to 0.45–0.48 for simple_alu_x0_1 (ideal
0.58–0.61, reference 1 − δ = 0.593) — the 260–540 two-qubit gates of the routed circuits at
0.3–1 % each, plus 8–18 mid-circuit measurements at 2–17 %, consume most of the signal on the
Torino model and nearly all of it on the Washington model. The bound covers the three small
instances only; for the committed examples the emulator figures are observations without a bound.
The noiseless runs agree with 1 − δ within shot noise everywhere. All of this is an emulator run on
the fake backends' noise models (mid-circuit measurements carrying the readout error, the Stage 24c
assumption); none of it is a device run or a validation of a certificate.

Per-run reports: the JSON files next to this table (`docs/hw_run.schema.json`).
