# Run report: simple_alu_x0_1

Report §8.5.2 (Table 8.5.2 shape), Stage 9b decision 4: every resource is a measured value of this run, never a report target.

- source: `examples/simple_alu_x0_1.cqr`
- instance: n = 6, M = 30 (hypothesis), r = 1
- status: **certified (conditional on: solution_count = 30)**

| Stage | Input | Output | Verification | Resources |
|---|---|---|---|---|
| 1. DSL Input | examples/simple_alu_x0_1.cqr (predicate_hash 07acc1e757ce…) | Typed AST `simple_alu_x0_1` + Boolean network (toNetwork) | exhaustively validated | n = 6 input bits; 2^6 = 64 inputs compared, 0 disagree |
| 2. Spec Extraction | Typed AST | Ground signature σ_in: Search, n = 6, M = 30, iter = bounded(1) | unverified | ĉ∧ = 10 (upper bound), AND-depth 4, ancilla budget 10 |
| 3. Pattern Matching | Signature σ_in | Grover: σ = {F₁ ↦ 6, F₂ ↦ 30, F₃ ↦ 1, F₄ ↦ [0,1,2,3,4,5]} | unverified | side conditions discharged: F₂ ≥ 1: 30 ≥ 1 |
| 4. QPLP Instant. | QPLP Grover + σ, r = 1 | Concrete circuit H^⊗6 · (U_s U_P)^1 (`emitted` in Cert.lean) | kernel-checked | grade (w, d, t, a) = (16, 145, 60, 10) (measured); δ = 833/2048 exact |
| 5. Oracle Synthesis | Boolean network (33 nodes, 10 AND) | U_P + proof (Lemma 6.3.2, lemma_6_3_2_xor_of_le) | kernel-checked | oracle (w, d, t, a) = (16, 80, 40, 10); 10 AND nodes vs ĉ∧ = 10 |
| 6. Ancilla Restore | Oracle U_P and diffusion MCZ | Restored circuit (AncRestore conjunct of `cert`) | kernel-checked | T after the first measurement: oracle 0, diffusion 0; 15 MBU measurements, 30 classically controlled gates; a = 10 |
| 7. Certificate Gen | Proof + grade | examples/certs/simple_alu_x0_1/Cert.lean, certificate.json (theorem CQRV.Cert.simple_alu_x0_1.cert) | kernel-checked | kernel 6.34 s, wall 16.15 s (median of 5 (first run excluded)); axioms: propext, Classical.choice, Quot.sound |
| 8. QIR Export | Internal circuit (`emitted`) | QIR text (simple_alu_x0_1.qir), OpenQASM 3 (simple_alu_x0_1.qasm) | declared trust boundary | G = 345 noisy operations (294 unitary, 15 mid-circuit measurements, 30 classically controlled, 6 terminal measurements) |

What each status covers:

1. what is validated: the typed AST → network translation, `evalProgram` (reference evaluator) vs `Network.pred (toNetwork …)` on every input; both are unverified Lean code and the check is not kernel-checked; the parser and surface checker are shared by both sides (the source is bound by predicate_hash); declared as trust_boundary.front_end = "DSL → network: exhaustively validated (2^6 inputs) by the unverified evaluator; not kernel-checked"
2. ℰ is total but not proved correct; the certificate theorem does not use σ_in (Cert.lean restates n, M and the network); M is the hypothesis hM_card, never decided
3. Algorithm 1 (Miller pattern); `millerMatch_sound` is proved for the algorithm, this run is not kernel-checked; the certificate theorem states the Grover instance directly
4. emitted_ok (hash link: synthesizer output = IR literal), grade_eq, nAnc_eq, delta_eq by `decide +kernel` in Cert.lean; δ = 1 − sin²((2r+1)θ) via sin_sq_odd_mul
5. OracleCert of the network literal: synthesizeOracle net = .ok … and C.WF by `decide +kernel`; restoration by lemma_6_3_2_xor_of_le
6. AncRestore n a emitted (groverOp P ^ r * hadamardU n), on density operators (Lemma 6.3.2 per oracle call, DiffusionCert for the MCZ)
7. lake env lean exit 0; #print axioms audited; status: certified (conditional on: solution_count = 30)
8. emitter unverified; translation-validated by re-parse in tests/diff (check_emit.sh, certify_check.py), not in this run; trust_boundary.emitted = QIR text
