# Run report: grover_pred_037

Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value of this run, never a report target.

- source: `examples/grover_pred_037.cqr`
- instance: n = 8, M = 32 (hypothesis), r = 2
- status: **certified (conditional on: solution_count = 32)**

| Stage | Input | Output | Verification | Resources |
|---|---|---|---|---|
| 1a. DSL Input: parser, surface checker | examples/grover_pred_037.cqr (predicate_hash d5f128217996…) | Typed AST `grover_pred_037` | declared trust boundary | — |
| 1b. DSL Input: typed AST → network | Typed AST `grover_pred_037` | Boolean network (toNetwork) | exhaustively validated | n = 8 input bits; 2^8 = 256 inputs compared, 0 disagree |
| 2. Spec Extraction | Typed AST | Ground signature σ_in: Search, n = 8, M = 32, iter = bounded(1) | unverified | ĉ∧ = 2 (upper bound), AND-depth 2, ancilla budget 2 |
| 3. Pattern Matching | Signature σ_in | Grover: σ = {F₁ ↦ 8, F₂ ↦ 32, F₃ ↦ 1, F₄ ↦ [0,3,7]} | unverified | side conditions discharged: F₂ ≥ 1: 32 ≥ 1 |
| 4. QPLP Instant. | QPLP Grover + σ, r = 2 | Concrete circuit H^⊗8 · (U_s U_P)^2 (`emitted` in Cert.lean) | kernel-checked | grade (w, d, t, a) = (10, 172, 96, 2) (measured); δ = 7/128 exact |
| 5. Oracle Synthesis | Boolean network (10 nodes, 2 AND) | U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le) | kernel-checked | oracle (w, d, t, a) = (10, 27, 8, 2); 2 AND nodes vs ĉ∧ = 2 |
| 6. Ancilla Restore | Oracle U_P and diffusion MCZ | Restored circuit (AncRestore conjunct of `cert`) | kernel-checked | T after the first measurement: oracle 0, diffusion 16; 8 MBU measurements, 16 classically controlled gates; a = 2 |
| 7. Certificate Gen | Proof + grade | examples/certs/grover_pred_037_few/Cert.lean, certificate.json (theorem CQRV.Cert.grover_pred_037.cert) | kernel-checked | kernel 22.60 s, wall 43.25 s (median of 5 (first run excluded)); axioms: propext, Classical.choice, Quot.sound |
| 8. QIR Export | Internal circuit (`emitted`) | QIR text (grover_pred_037.qir), OpenQASM 3 (grover_pred_037.qasm) | declared trust boundary | G = 380 noisy operations (348 unitary, 8 mid-circuit measurements, 16 classically controlled, 8 terminal measurements) |
| Hardware profile | profile ibm_kyiv (profile_hash 551369d44550…), grade, δ, G | hardware profile ibm_kyiv: fits all budgets; δ_hw ≤ 7/128 + 380·1/100 = 2467/640 (vacuous) | checked against declared profile (not a proof about hardware) | width 10 / 127: fits; depth 172 / 200: fits; T-count 96 / —: not limiting; ancilla 2 / 127: fits; G = 380 |

What each status covers:

1. parser and surface checker: declared trust boundary (shared by both sides of the comparison in 1b, so 1b cannot detect their errors); the source text is bound by predicate_hash only
2. typed AST → network: exhaustively validated (2^8 inputs), `evalProgram` (reference evaluator) vs `Network.pred (toNetwork …)` on every input; both are unverified Lean code and the check is not kernel-checked; declared as trust_boundary.front_end = "DSL → network: exhaustively validated (2^8 inputs) by the unverified evaluator; not kernel-checked"
3. ℰ is total but not proved correct; the certificate theorem does not use σ_in (Cert.lean restates n, M and the network); M is the hypothesis hM_card, never decided
4. Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, this run is not kernel-checked; the certificate theorem states the Grover instance directly
5. emitted_ok (hash link: synthesizer output = IR literal), grade_eq, nAnc_eq, delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via sin_sq_odd_mul
6. OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by `decide +kernel`; restoration by lemma_6_3_2_xor_of_le
7. AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators (Lemma 6.3.2 per oracle call; few-ancilla MCZ by mczFew_logDepth_ancRestore, KG Theorem 5.1 for every n, Stage 13a; no per-instance classical check)
8. lake env lean exit 0; #print axioms audited; status: certified (conditional on: solution_count = 32)
9. emitter unverified; translation-validated by re-parse in tests/diff (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text
10. declared profile figures, not calibration data; routing, native gates and calibration are outside the trust boundary (report §5.3.1); not part of the certified status (the certificate is about the ideal channel)
