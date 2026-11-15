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
