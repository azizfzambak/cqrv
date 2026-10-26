# Stage 11b (improvement 2) — `cqr certify --profile`: hardware budget and perturbation bound

Report sections: §3.1.3 (hardware profile = monotone map ρ : R → R_phys, change of base),
§3.3.2–3.3.3 (budget feasibility as fibre membership; ρNISQ; Table 3.5 against IBM Kyiv;
hardware-perturbation corollary δ_hw ≤ δ + G·p̄), §5.3.1 (backend compilation is outside the
trust boundary), §9.5.3 (JSON envelope carries the hardware-perturbation conjunct).
Precondition: Stage 11a accepted (main = 063cfe6). `git switch -c stage-11b main`; one commit;
include this file (untracked). Windows: `LEAN_NUM_THREADS=4`; Python `.venv`.
**Engineering stage, no new proofs**; the repository stays sorry-free.

## What it adds (and what it does not)

Today the certificate states the *logical* grade and the formula δ_hw ≤ δ + G·p̄ with
`p_bar = "profile parameter"`. This stage lets the user name a hardware profile; the certificate
and run report then say, **with numbers**, whether the measured grade fits that profile's budget
and what the perturbation bound is. It does **not** model routing, native-gate translation or
calibration noise (backend, outside the trust boundary, §5.3.1) — say so in the output.

## Reviewer decisions (record in DECISIONS.md)

1. **Profile file** `profiles/<name>.json`, schema `docs/profile.schema.json` (v1.0.0): `name`,
   `source` (where each number comes from — a citation or "report §3.3.3"; no invented figures),
   `budget` {w, d, t, a} as natural numbers or `null` for "not limiting" (Table 3.5's "native"
   T-count), `t_gate_ns`, `t_T_ns` (nullable), `p_bar` (mean per-operation error, a decimal string).
   Ship `profiles/ibm_kyiv.json` with exactly the report's Table 3.5 / §3.3.3 values: w = 127,
   d ≈ 200 (coherence-limited, T1 ≈ 100 μs / t_gate ≈ 500 ns), T not limiting, a = 127,
   p̄ = 1e-2 ("current two-qubit error rates of about 10⁻²", §3.3.3). Record that these are the
   report's illustrative figures, not calibration data.
2. **Budget check in Lean.** Map `null` components to "no bound" (e.g. compare only the given
   components; implement as a `Grade`-level `fitsPartial` with a `#guard`-tested agreement with
   `Grade.fits` when all components are present). Report each component: required, budget,
   fits/exceeds.
3. **Perturbation bound** computed exactly as a rational from the certificate's δ (exact) and
   G (gate-count breakdown of Stage 8a) and p̄: `δ_hw = δ + G·p̄`, and flag
   `"vacuous": true` when δ_hw ≥ 1 (§3.3.3: "the bound is vacuous (Gp ≳ 1)").
4. **Status line** unchanged in meaning: hardware fitness is **not** part of "certified" (the
   certificate is about the ideal channel). Print a second line, e.g.
   `hardware profile ibm_kyiv: exceeds depth budget (230 > 200); δ_hw ≤ 7/128 + 390·1/100 (vacuous)`.
5. **Schema** `certificate.schema.json` minor bump: new optional object `hardware` {profile name,
   profile hash (SHA3 of the profile file), per-component check, δ_hw, vacuous, note:
   "routing, native gates and calibration are outside the trust boundary"}. Without `--profile`
   the certificate is byte-identical to today's (committed examples must not change).

## Tasks

1. `CQRV/Grades/Profile.lean`: profile structure, `fitsPartial`, tests (Kyiv: grover_pred_037
   exceeds d only; simple_alu_x0_1 (16, 145, 60, 10) fits; ρNISQ consistency: d·t_gate ≤ T1).
2. JSON reading of profiles in the CLI; `cqr certify <file> --profile <name|path>`; run report
   gets one extra row "Hardware profile" with status "checked against declared profile (not a
   proof about hardware)".
3. `profiles/ibm_kyiv.json`, `docs/profile.schema.json`, Python schema test.
4. Extend `scripts/check_certify.sh`: Grover with `--profile ibm_kyiv` → exceeds depth, δ_hw
   vacuous; ALU → fits all, δ_hw vacuous (G·p̄ ≥ 1 there too — report it); without `--profile`
   → certificate byte-identical to the committed one.

## Acceptance

- `lake build` green, sorry-free, `scripts/ci_local.sh` all PASS (if step 19 runs out of memory,
  rerun `scripts/check_certify.sh` alone and paste it).
- The two status lines for Grover with `--profile ibm_kyiv` pasted in the closing reply.
- Committed example certificates unchanged.

## Stop conditions

- A profile number cannot be traced to the report or a cited source → leave it `null` and say so;
  never invent hardware figures.
- Do not install Qiskit or other new dependencies; routing-aware depth is a separate, optional
  later task.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): both status lines, the Kyiv per-component table, and
any profile value left `null`.
