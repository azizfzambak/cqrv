# Stage 15 — coherent uncomputation mode (`--uncompute coherent`)

Spec: PHASE2_SPEC.md §A.0.1 (extends report §6.1.4, §6.2.2, §10.1.1). Two tasks, **two
commits**: do **15a**, reply, stop; start **15b** after the reviewer accepts 15a.
Precondition: Stage 14c accepted; main = the 14c commit (14a–14c included). `git switch -c stage-15a main`
(15b: `stage-15b` from `stage-15a`). The 15a commit includes this file, `docs/PHASE2_ROADMAP.md`
and `docs/PHASE2_SPEC.md` (all untracked until then). Windows: `LEAN_NUM_THREADS=4`. **Proof stage** (3 build–fix
rounds per item); repository sorry-free and warning-free throughout.
Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`.
Process on this laptop (16 GB): `lake build` in the foreground; `scripts/ci_local.sh` and any Lean
run longer than a few minutes are run by the user in a separate terminal, one Lean process at a
time. When the build is green and the tests you can run yourself pass, stop and say "ready for CI";
after the user's run, read `.lake/ci_local/*.log`, commit, and give the closing reply.

**Invariants of both tasks.** No existing theorem *statement* changes (adding a defaulted
argument `(mode : UncomputeMode := .mbu)` to a *definition* is allowed where listed below, in
the style of the existing `aMax`/`shape` defaults; every existing statement must then elaborate
unchanged). The three committed certificates and all golden files stay byte-identical. The
`mbu` mode is the Phase 1 code path, gate for gate.

---

## 15a — the mode, the adjoint, the synthesizer, Lemma 6.3.2 in mode `coherent`

### A1. Adjoint of measurement-free gate lists (`CQRV/Circuit/IR.lean`, `Semantics.lean`)

- `Gate.adjoint : Gate → Gate`: `s ↔ sdg`, `t ↔ tdg`; `h x z cnot cz` fixed; `measure ifBit
  alloc free` fixed (the function is total; the theorems assume `Gate.isUnitary`, which already
  exists, Semantics.lean:436).
- `List.adjointGates gs := (gs.map Gate.adjoint).reverse` (name as you like, say it).
- `theorem gateU_adjoint (g) (hg : g.isUnitary = true) : gateU n a g.adjoint = star (gateU n a g)`.
  Routes: `star_monoMat` (Semantics.lean:192) for `x`, `cnot` (involutive permutation,
  `cnotPerm_involutive`), `cz`, and the phase gates (`star_sign_mul`, `star_ω_mul_ω`); `hMat` is
  self-adjoint (the `star_` lemmas at :281, :290 — check their names with `#check`).
- `theorem unitaryDenote_adjoint (gs) (h : ∀ g ∈ gs, g.isUnitary = true) :
  unitaryDenote n a (adjointGates gs) = star (unitaryDenote n a gs)` (induction; `star_mul`).
- `#guard`: `adjointGates (TempLogicalAND a b t)` is the explicit 13-gate list
  `[sdg t, h t, cnot t b, cnot t a, tdg t, t b, t a, cnot t b, cnot t a, cnot b t, cnot a t, tdg t, h t]`.

### A2. The mode and the gadget (`CQRV/Synthesis/TempAnd.lean`, `Oracle.lean`)

- `inductive UncomputeMode | mbu | coherent deriving Repr, DecidableEq, Inhabited`; `toString`
  `"mbu"`/`"coherent"` and a parser for the CLI.
- `UncomputeTempLogicalANDCoherent a b t : List Gate := adjointGates (TempLogicalAND a b t)`.
- `Oracle.step` gets the mode; in `step` the AND case builds
  `unc := pre ++ (match mode with | .mbu => UncomputeTempLogicalAND pu pv t 0
                                  | .coherent => UncomputeTempLogicalANDCoherent pu pv t) ++ [.free t] ++ pre.reverse`
  and nothing else differs. `synthesizeOracle (N) (mode : UncomputeMode := .mbu)`.
  The shifted-bit numbering of uncompute blocks (`mapIdx … shiftBits i`) is unchanged; in mode
  `coherent` it is the identity on every block (no bits).
- Thread the default through `synthesizeWithBudget`, `diffusionWith`, `diffusion`,
  `groverIteration`, `groverCircuit` (Diffusion.lean) and `groverCircuitOf` (Grover/Restore.lean:924)
  as the *last* defaulted argument. Bennett (`chainCircuit`) and `mczFew` stay MBU: `synthesizeWithBudget`
  with `aMax = some k` below the straight-line count **and** mode `coherent` fails with
  `unsupportedCombination "Bennett pebbling is MBU-only (Stage 15)"`; the few-ancilla builders do
  not take a mode in this stage.
- CLI: `cqr synthesize … --uncompute mbu|coherent` (also with `--diffusion n` and `--grover`);
  the JSON/`--layers` output unchanged in form. `cqr certify` does **not** take the flag yet
  (15b).
- Harness: `scripts/diff_oracles.sh` and `diff_grover.sh` run every existing case in both modes
  (the harness needs no change: coherent circuits have no `measure`; `free` still asserts |0⟩).

### A3. Lemma 6.3.2, well-formedness and success in mode `coherent` (`CQRV/Circuit/OracleCorrect.lean`)

Proof plan (reviewer; verify every step):
1. `tempLogicalAND_adjoint_basis`: on a basis state with `t = a ∧ b`, the coherent uncompute maps
   `|a, b, a∧b⟩ ↦ |a, b, 0⟩` with amplitude 1. Route: `tempLogicalAND_kraus_basis`
   (OracleBlocks.lean:272) gives `U |a,b,0⟩ = |a,b,a∧b⟩`; `unitaryDenote_adjoint` gives
   `U† U = 1`; apply `U†` to both sides. Via `krausOps_of_unitary` the Kraus operator of the
   coherent block is `U†` in every branch (there is one branch: no bits).
2. `unc_kraus_coherent`: the analogue of `unc_kraus` (:213) with amplitude `1` instead of
   `(√2)⁻¹` and the block `r.uncC j := r.pre ++ UncomputeTempLogicalANDCoherent r.p r.q (anc j)
   ++ [free (anc j)] ++ r.pre.reverse` (no bit argument).
3. `chain_kraus` (:243) hard-codes `(√2)⁻¹ ^ rs.length` and `uncBlocks`. Generalize it to a
   gadget record `{ unc : AndRec → ℕ → ℕ → List Gate, amp : ℂ, unc_kraus : … }` with the MBU
   gadget and the coherent gadget as its two instances, **or** duplicate it as
   `chain_kraus_coherent`; prefer the generalization, fall back to duplication if the
   generalization costs more than one round. Say which in DECISIONS.md.
4. `fold_inv` (:590) records the uncompute blocks of the fold; it must know the mode (the
   invariant's `hunc` equation names `uncBlocks`). Expect a mode parameter on `Inv`/`fold_inv`
   with the MBU case definitionally the old one.
5. `lemma_6_3_2_coherent_of_le (N) (C) (hC : synthesizeOracle N .coherent = .ok C) (hWF : C.WF)
   (a) (ha : C.nAnc ≤ a) : AncRestore C.nData a C (phaseOracle (N.pred C.nData))` by
   `ancRestore_of_kraus` with `λ_c = ε` (|ε| = 1), `C.nBits = 0` (so the sum over branches has one
   term), and the generalized chain lemma; then `lemma_6_3_2_coherent` at `C.nAnc`.
6. `synthesizeOracle_WF` and `synthesizeOracle_succeeds` for mode `coherent`: the qubit invariant
   (`InvQ`, `and_blocks_qubitsOk`) needs the coherent block's qubits (the same three qubits and
   `pre`); `bitsOk` is trivial without `measure`; `succeeds` is mode-independent if the mode only
   selects the gadget (`fold`/`prepare`/`cone` untouched) — state them as
   `synthesizeOracle_WF' (mode)` and `synthesizeOracle_succeeds' (mode)` with the old names as
   the `.mbu` instances, or generalize the old proofs in place with the mode as an argument and the
   old statements as corollaries. Old statements unchanged.

### Acceptance (15a)

- `lake build` green, sorry-free, warning-free; guarded `#print axioms` for
  `lemma_6_3_2_coherent`, `synthesizeOracle_WF'`, `synthesizeOracle_succeeds'`: the standard three.
- `#guard` tests (tests/CQRVTests/Synthesis.lean): the running example's oracle in mode `coherent`
  has `tCount = 16`, `nBits = 0`, no `measure`; its grade and the tree diffusion's grade in both
  modes reported in (e) (expect the same width and ancillae, 8 T per AND, and a depth to be
  measured, not guessed).
- Harness green in both modes; `scripts/ci_local.sh` all PASS; committed certificates and golden
  files byte-identical; `cli_smoke.sh` gains the `--uncompute` cases and the Bennett rejection
  (mind the CRLF note: patch in binary mode).
- DECISIONS.md: dated entries for the mode design (defaulted argument vs. new names, chosen
  option), the chain-lemma route, and the Bennett/few exclusion. PROJECT_STATUS.md: a "Phase 2"
  section pointing to `docs/PHASE2_ROADMAP.md` and `docs/PHASE2_SPEC.md`, with Stage 15a as its
  first row; README status line updated.

### Stop conditions (15a)

- Any existing statement would have to change, or a committed certificate re-certifies
  differently → stop and propose.
- `unc_kraus_coherent` or the chain lemma do not close in 3 rounds → stop; ship nothing of A3
  as a `sorry`: report the open goal and the duplicated-lemma fallback's status.

---

## 15b — certificates in mode `coherent`

### B1. The parametric lemma with an abstract oracle (`CQRV/Grover/Lemma.lean`)

`grover_parametric_lemma_gen`: as `grover_parametric_lemma_diff` (:534) but with the oracle
abstract — `(P : Reg n → Bool) (Oc : Circuit) (hOn : Oc.nData = n) (hOb : Oc.bitsOk = true)
(hOr : ∀ a, Oc.nAnc ≤ a → AncRestore n a Oc (phaseOracle P))` and the Grover data `(M)
(hM_pos) (hM_card)` as explicit hypotheses (or a `GroverData` record without the `OracleCert`),
conclusion as in `_diff` with `groverCircuitOf Oc Dc n r`. Check first that the proof of `_diff`
uses `gp.oracle` only through `P`, `C`, `nData_eq` and `ancRestore`; if it uses `hC`, say where.
Then `_diff` becomes a one-line instance; its statement is unchanged.

### B2. Certificates (`CQRV/Grover/Restore.lean`, `Certify/Specialize.lean`, `Generate.lean`)

- `OracleCert` is **not** modified (the committed certificates construct it). Add
  `OracleCertCoh (n)` with `hC : synthesizeOracle N .coherent = .ok C` and `restore` filled by
  `lemma_6_3_2_coherent_of_le`; `OracleCertCoh.ancRestore` as for `OracleCert`.
- `grover_certificate_coherent` in Specialize.lean, parallel to `grover_certificate_few` (:154):
  hypotheses `hC : groverCircuit O.N n r (mode := .coherent) = .ok C` etc., from
  `grover_parametric_lemma_gen`.
- `CertRequest.uncompute : UncomputeMode := .mbu`; `renderCertCoherent` (or a mode switch inside
  the existing renderers with the `.mbu` text byte-identical — prove it by re-certifying);
  `cqr certify … --uncompute mbu|coherent`; `--uncompute coherent --shape few:log` rejected with
  `unsupportedCombination`.
- JSON: `"uncompute": "mbu"|"coherent"` (schema 1.7.0; 1.6.0 is Stage 14a's `solution_count` envelope; `tests/diff/cert_schema.py`); run report
  row 3 names the mode; `G` of the hardware perturbation bound counts no measurement in mode
  `coherent` (`GateCounts` already distinguishes the kinds). Note from 15a: the coherent Grover
  circuit of the running example has grade (15, 200, 144, 7) and 0 classical bits, so under
  `--profile illustrative_sc` the depth check passes with equality (200 ≤ 200); the run report must
  show the measured depth next to the budget, and the certificate's `hardware` block must come
  out of the same code path as the MBU one (no special case for equality).
- Commit a fourth example certificate `examples/certs/grover_pred_037_coh/` (running example,
  tree diffusion, mode coherent) with its run report, QIR, QASM; `check_certify.sh` and
  `ci_local.sh` step 20 cover it.

### Acceptance (15b)

- Build green and sorry-free; `#print axioms` for `grover_parametric_lemma_gen`,
  `grover_certificate_coherent` and the new `cert`: the standard three.
- The three Phase 1 certificates byte-identical; the fourth re-certifies byte-identically in CI;
  kernel time of the fourth measured by the `bench_kernel.sh` protocol and reported in (e) with
  its grade `(w, d, t, a)` next to the MBU grade `(15, 134, 72, 7)`.
- DECISIONS.md entries: the `_gen` lemma, the `OracleCertCoh` choice, the schema bump.

### Stop conditions (15b)

- The proof of `_diff` depends on `OracleCert.hC` in a way the abstraction cannot absorb → stop,
  report the dependency, propose.
- Re-certification of a Phase 1 example changes → stop.

---

## Closing reply (each task)

CLAUDE.md format, under 40 lines. In (e) for 15a: the chosen mode design and why, the grades in
both modes for the oracle and the tree diffusion, lines added per file. For 15b: the Grover grade
in mode `coherent`, the kernel time, and which Phase 1 lemma became a corollary.
