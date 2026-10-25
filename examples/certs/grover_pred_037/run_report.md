# Run report: grover_pred_037

Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value of this run, never a report target.

- source: `examples/grover_pred_037.cqr`
- instance: n = 8, M = 32 (hypothesis), r = 2
- status: **certified (conditional on: solution_count = 32)**

| Stage | Input | Output | Verification | Resources |
|---|---|---|---|---|
| 1. DSL Input | examples/grover_pred_037.cqr (predicate_hash d5f128217996…) | Typed AST `grover_pred_037` + Boolean network (toNetwork) | exhaustively validated | n = 8 input bits; 2^8 = 256 inputs compared, 0 disagree |
| 2. Spec Extraction | Typed AST | Ground signature σ_in: Search, n = 8, M = 32, iter = bounded(1) | unverified | ĉ∧ = 2 (upper bound), AND-depth 2, ancilla budget 2 |
| 3. Pattern Matching | Signature σ_in | Grover: σ = {F₁ ↦ 8, F₂ ↦ 32, F₃ ↦ 1, F₄ ↦ [0,3,7]} | unverified | side conditions discharged: F₂ ≥ 1: 32 ≥ 1 |
| 4. QPLP Instant. | QPLP Grover + σ, r = 2 | Concrete circuit H^⊗8 · (U_s U_P)^2 (`emitted` in Cert.lean) | kernel-checked | grade (w, d, t, a) = (15, 230, 72, 7) (measured); δ = 7/128 exact |
| 5. Oracle Synthesis | Boolean network (10 nodes, 2 AND) | U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le) | kernel-checked | oracle (w, d, t, a) = (10, 27, 8, 2); 2 AND nodes vs ĉ∧ = 2 |
| 6. Ancilla Restore | Oracle U_P and diffusion MCZ | Restored circuit (AncRestore conjunct of `cert`) | kernel-checked | T after the first measurement: oracle 0, diffusion 0; 18 MBU measurements, 36 classically controlled gates; a = 7 |
| 7. Certificate Gen | Proof + grade | examples/certs/grover_pred_037/Cert.lean, certificate.json (theorem CQRV.Cert.grover_pred_037.cert) | kernel-checked | kernel 7.20 s, wall 17.08 s (median of 5 (first run excluded)); axioms: propext, Classical.choice, Quot.sound |
| 8. QIR Export | Internal circuit (`emitted`) | QIR text (grover_pred_037.qir), OpenQASM 3 (grover_pred_037.qasm) | declared trust boundary | G = 390 noisy operations (328 unitary, 18 mid-circuit measurements, 36 classically controlled, 8 terminal measurements) |

What each status covers:

1. what is validated: the typed AST → network translation, `evalProgram` (reference evaluator) vs `Network.pred (toNetwork …)` on every input; both are unverified Lean code and the check is not kernel-checked; the parser and surface checker are shared by both sides (the source is bound by predicate_hash); declared as trust_boundary.front_end = "DSL → network: exhaustively validated (2^8 inputs) by the unverified evaluator; not kernel-checked"
2. ℰ is total but not proved correct; the certificate theorem does not use σ_in (Cert.lean restates n, M and the network); M is the hypothesis hM_card, never decided
3. Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, this run is not kernel-checked; the certificate theorem states the Grover instance directly
4. emitted_ok (hash link: synthesizer output = IR literal), grade_eq, nAnc_eq, delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via sin_sq_odd_mul
5. OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by `decide +kernel`; restoration by lemma_6_3_2_xor_of_le
6. AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators (Lemma 6.3.2 per oracle call, DiffusionCert for the MCZ)
7. lake env lean exit 0; #print axioms audited; status: certified (conditional on: solution_count = 32)
8. emitter unverified; translation-validated by re-parse in tests/diff (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text
