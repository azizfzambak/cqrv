# Run report: grover_pred_037

Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value of this run, never a report target.

- source: `examples/grover_pred_037.cqr`
- instance: n = 8, M = 32 (kernel-decided), r = 2, uncompute = mbu
- status: **certified**

| Stage | Input | Output | Verification | Resources |
|---|---|---|---|---|
| 1a. DSL Input: parser, surface checker | examples/grover_pred_037.cqr (predicate_hash d5f128217996…) | Typed AST `grover_pred_037` | declared trust boundary | — |
| 1b. DSL Input: typed AST → network | Typed AST `grover_pred_037` | Boolean network (toNetwork) | kernel-checked | n = 8 input bits; `front_end` covers all 2^8 = 256 inputs (a theorem, not an enumeration) |
| 2. Spec Extraction | Typed AST | Ground signature σ_in: Search, n = 8, M = 32, iter = bounded(1) | unverified | ĉ∧ = 2 (upper bound), AND-depth 2, ancilla budget 2 |
| 3. Pattern Matching | Signature σ_in | Grover: σ = {F₁ ↦ 8, F₂ ↦ 32, F₃ ↦ 1, F₄ ↦ [0,3,7]} | unverified | side conditions discharged: F₂ ≥ 1: 32 ≥ 1 |
| 4. QPLP Instant. | QPLP Grover + σ, r = 2, uncompute = mbu | Concrete circuit H^⊗8 · (U_s U_P)^2 (`emitted` in Cert.lean) | kernel-checked | grade (w, d, t, a) = (15, 134, 72, 7) (measured); δ = 7/128 exact; ext: 2Q 126, T-depth 39, rot 0, meas 18, ff 36 (measured) |
| 5. Oracle Synthesis | Boolean network (10 nodes, 2 AND) | U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le) | kernel-checked | oracle (w, d, t, a) = (10, 27, 8, 2); 2 AND nodes vs ĉ∧ = 2 |
| 6. Ancilla Restore | Oracle U_P and diffusion MCZ | Restored circuit (AncRestore conjunct of `cert`) | kernel-checked | T after the first measurement: oracle 0, diffusion 0; 18 MBU measurements, 36 classically controlled gates; a = 7 |
| 7. Certificate Gen | Proof + grade | examples/certs/grover_pred_037/Cert.lean, certificate.json (theorem CQRV.Cert.grover_pred_037.cert) | kernel-checked | kernel 12.90 s, wall 23.12 s (median of 5 (first run excluded)); axioms: propext, Classical.choice, Quot.sound |
| 8. QIR Export | Internal circuit (`emitted`) | QIR text (grover_pred_037.qir), OpenQASM 3 (grover_pred_037.qasm) | declared trust boundary | G = 390 noisy operations (328 unitary, 18 mid-circuit measurements, 36 classically controlled, 8 terminal measurements) |

What each status covers:

1. parser, surface checker and the typed-term printer: declared trust boundary (the theorem of 1b starts at the typed-term literal `prog` of Cert.lean, so an error before it is not detected there); the source text is bound by predicate_hash only
2. typed AST → network: proved (`toNetwork_pred`, Stage 16a) and kernel-checked at this instance in Cert.lean — `prog` (the typed-term literal), `prog_scoped` (decide), `net_ok : toNetwork prog = .ok net` (decide +kernel), `front_end : ∀ x, evalProgram prog x = Network.pred net 8 x`; the literal printer is unverified (a wrong literal gives a different network and fails net_ok); declared as trust_boundary.front_end = "DSL typed term → network: proved (toNetwork_pred; kernel-checked net_ok and front_end in Cert.lean); parser, surface checker and the typed-term printer unverified; predicate_hash binds the source"
3. ℰ is total but not proved correct; the certificate theorem does not use σ_in (Cert.lean restates n, M and the network); M is decided by the kernel (hM_count: Network.countSat on all 2^8 inputs, Network.countSat_eq_card)
4. Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, this run is not kernel-checked; the certificate theorem states the Grover instance directly
5. emitted_ok (hash link: synthesizer output = IR literal), grade_eq, gradeExt_eq, nAnc_eq, delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via sin_sq_odd_mul
6. OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by `decide +kernel`; restoration by lemma_6_3_2_xor_of_le
7. AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators (Lemma 6.3.2 per oracle call, DiffusionCert for the MCZ)
8. lake env lean exit 0; #print axioms audited; status: certified
9. emitter unverified; translation-validated by re-parse in tests/diff (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text; a phase gate p is emitted to QIR as rz with a hex-float angle, rz(θ) = e^(−iθ/2)·p(θ): a global phase per gate (per branch under ifBit), irrelevant to every statement of the certificate; a top-level cp is its five-gate decomposition (decomposeCp_unitary_wf)
