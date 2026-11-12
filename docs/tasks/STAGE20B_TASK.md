# Stage 20b — The amplitude-estimation parametric lemma (PHASE2_SPEC §A.4)

PHASE2_SPEC.md §A.4 ("Amendments before Stage 20b" — read it first; it replaces the output type,
the decoding POVM and the channel of "Specification and decoding" and of the statement sketch), the
"20a2 done" paragraph and its notes for Stage 20b, §A.2 (`aqft_diamond_le`, `aqft_opNorm_le`, the
Stage 18c notes on vacuity), §A.3 (5) (`U_count`), §A.8 items 1 and 6; report §2.1.2 (Definition
2.2), §2.3.2 (Theorem 3.3b), §8.2; PHASE2_ROADMAP.md row 20b. Three tasks: **20b1** and **20b2** are
specified here, each one commit, each starting after the reviewer accepts the previous one, from
`main`. **20b3** (the certificate) gets its task text after 20b2 is accepted.

Precondition: Stage 20a complete; main = 32dca39 (the 20a2 review commit). `git switch -c
stage-20b1 main` (20b2: `stage-20b2` from `main` after 20b1 is merged). The 20b1 commit includes this
file and the reviewer's edits to `docs/PHASE2_SPEC.md` and `docs/PHASE2_ROADMAP.md`, all unedited.
Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows:
`LEAN_NUM_THREADS=4`. Process as in Stage 20a: `lake build` in the foreground; `scripts/ci_local.sh`
and any Lean run longer than a few minutes are the user's separate terminal, one Lean process at a
time; harness scripts run before CI the way `ci_local.sh` runs them (`.venv/Scripts/python.exe -I`,
stdout redirected to a file, no `-X utf8`); "ready for CI", the reviewer's audit, the user's CI run,
then the commit and the closing reply.

**Invariants of both tasks.** Every measured value is unchanged; no definition a committed
`Cert.lean` evaluates is edited; no certificate is regenerated; every existing theorem statement
is unchanged — `coherent_composition`, `coherent_composition_diamond`, `qpe_success`, `U_count`,
`countingCircuit_ancRestore` included. The `cqr` executable gets no new subcommand or flag and its
import closure stays Lean core + Mathlib (§A.8 item 6). No new CI step: the pass mark stays **18
PASS, 0 FAIL, 4 n/a**; harness checks go into the existing step "Counting circuit". `sorry` is not
part of the acceptance of either task: if a lemma resists after a serious attempt, stop and ask. If
a statement here is false, give the counterexample and the corrected form, as at 19b, and report it
in (e). Use the decidability instance of `qpe_success` (`open Classical in`) and cite
`GroverData.iteration_induction` by that name (the 20a2 notes).

---

## 20b1 — The realization lemma, exact inverse QFT (`CQRV/Grover/AmplitudeEstimation.lean`, new)

Imports `CQRV.Grover.Counting`; not in the `cqr` closure. Throughout `gp : GroverData`,
`a = gp.M / 2 ^ gp.n` (as a real), `m ≥ 1`.

### A1. The output type, the metric, the specification

```
def countEst (m : ℕ) (a : ℝ) : Reg m ⊕ Unit → ℝ
  | .inl y  => Real.sin (π * y.toNat / 2 ^ m) ^ 2
  | .inr () => a
def CountOut (m : ℕ) (a : ℝ) : Type := Reg m ⊕ Unit
-- Fintype, DecidableEq by inferInstanceAs; the pseudo-metric induced by countEst m a
noncomputable instance (m : ℕ) (a : ℝ) : PseudoMetricSpace (CountOut m a) :=
  PseudoMetricSpace.induced (countEst m a) inferInstance
def CountSpec (m : ℕ) (a : ℝ) : Spec Unit (CountOut m a) := fun _ y => y = .inr ()
```

Lemmas: `dist_countOut : dist y y' = |countEst m a y − countEst m a y'|`; `countSpec_relax :
(CountSpec m a).relax ε () y ↔ |countEst m a y − a| ≤ ε`; `countSpec_dom : (CountSpec m a).dom =
Set.univ`. The metric is a pseudo-metric: `y` and its reflection `2^m − y` have the same estimate.
That is intended, and it is why §A.4 (3) of the amendments is needed for 20b2.

### A2. The decoding POVM

```
def countPOVM (n m : ℕ) (a : ℝ) : POVM (CountOut m a) (Reg (n + m))
  -- mats (inl y) = ∑ s : Reg n, (MState.pure (Ket.basis ((splitEquiv n m).symm (s, y)))).M
  -- mats (inr ()) = 0
```

`normalized` by reindexing `∑_y ∑_s` to `∑_x` through `splitEquiv` and the proof of
`basisPOVM`'s `normalized` (Grover/Lemma.lean). Then the measurement on the state the circuit
produces:

```
theorem countPOVM_measure (gp : GroverData) (m : ℕ) (y : Reg m) :
    (countPOVM gp.n m a).measure ((U_count gp.P m none) ◃ ancZero (gp.n + m)) (.inl y) =
      phaseDist gp m y
-- and the value at .inr () is 0
```

Follow `terminal_measurement` (Grover/Lemma.lean:588) for the pure-state computation:
`measure_eq_re_trace` (Realizability/Composition.lean), `pure_basis_m_apply`, the vector
`(U_count …).val *ᵥ basisVec (zeroReg _)`.

### A3. The realization

```
noncomputable def ae_delta : ℝ := 1 - 8 / π ^ 2
theorem ae_realizes (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {C : Circuit}
    (hR : AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
      (ae_eps a m) ae_delta g
```

The grade part is `hg`. For the probability part: `AncRestore.traced` turns the channel output on
`encode ()` into `U_count ◃ ancZero (gp.n + m)`, as in `grover_realizes_of_ancRestore`
(Grover/Lemma.lean:621). `countSpec_relax` turns the event into `|countEst y − a| ≤ ae_eps a m`.
On `inl y` this is the filter of `qpe_success`; `inr ()` has probability 0 (it is in the event,
since `ae_eps ≥ 0`, which does not matter). `countPOVM_measure` and `qpe_success` finish it.

### A4. The parametric lemma

```
theorem ae_parametric_lemma (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network} (hN : N.WF)
    (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N gp.n m none shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
        (ae_eps a m) ae_delta g ∧
      AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)
```

from `countingCircuit_ancRestore` (rewritten by `hP`) and `ae_realizes`. With `g := Synthesis.grade
C` it is the measured statement. Stage 20b3 uses it with the composed bound of 19a.

### A5. Tests

`tests/CQRVTests/AmplitudeEstimation.lean` (new): `example` instances at `n = 2`, `m = 2`
(`countSpec_relax` on both constructors, `ae_parametric_lemma` on the two-qubit AND network of the
19c tests with its `GroverData`), and `#guard_msgs` axiom checks of `countPOVM_measure`,
`ae_realizes` and `ae_parametric_lemma` (the standard three). No harness change in 20b1:
`phaseDist` and the success sets are already checked by part (g).

### 20b1 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (`CountOut` with `Reg m` and a real estimate; the POVM on the whole data
register; the channel `groverChannel (n+m)`); `docs/PROJECT_STATUS.md` one line; no README change.
Reviewer files go in unedited.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; A1–A4 proved, no `sorry`.

Stop and ask: the induced pseudo-metric meets an obstacle in Lean. The fallback of §A.8 item 1, the
specification that carries the tolerance with `RealizesExact`, is a reviewer decision: report the
obstacle and do not switch on your own. Also stop if a statement needs a hypothesis not listed.

---

## 20b2 — The AQFT variant through Theorem 3.3b (after 20b1 is accepted)

**Notes added at the 20b1 review (2026-11-10).** (i) 20b1 is in
`CQRV/Grover/AmplitudeEstimation.lean`; put 20b2's lemmas there too (B1 and the generic norm lemma
of B2 go where B1 and B2 say). (ii) Write the ideal point as `(Sum.inr () : CountOut m a)`, and
apply the lemmas about `CountOut` (`dist_countOut`, `countSpec_relax`) as terms, since `rw` does not
see through the type synonym. (iii) For step 4 of B4, `ae_realizes` gives a `Realizes` for
`groverChannel (gp.n + m) C₀`. Take `.2` on `encode ()` and rewrite the channel by the
factorization of step 3. Do not re-prove the probability.

### B1. Theorem 3.3b on a pseudo-metric (`CQRV/Realizability/Coherent.lean`)

`coherent_composition_pseudo` and `coherent_composition_diamond_pseudo`: the two statements with
`[PseudoMetricSpace Z]` in place of `[MetricSpace Z]`, with the same proofs (they use only what
`Spec.relax` needs). The existing theorems keep their statements; you may re-derive their proofs
from the new ones or leave them as they are.

### B2. The operator norm under reindexing

- `l2_opNorm_submatrix_equiv (A : Matrix d d ℂ) (e : d' ≃ d) : ‖A.submatrix e e‖ = ‖A‖` (look for
  it in Mathlib first; otherwise prove it by conjugation with the permutation matrix, which is
  unitary). It goes into `CQRV/Realizability/Diamond.lean`, section `Unitary`, next to
  `l2_opNorm_kronecker_one_le`.
- `l2_opNorm_liftP_le : ‖liftP B‖ ≤ ‖B‖` (`liftP_eq_submatrix`, the swap of the Kronecker factors by
  `Equiv.prodComm`, `l2_opNorm_kronecker_one_le`).
- `l2_opNorm_kronecker_one_reg0 : ‖A ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)‖ = ‖A‖` (`Reg 0` is one
  point; `Reg m × Reg 0 ≃ Reg m`).

### B3. The inverse block

```
theorem inverse_diamond_le (n m kmax a : ℕ) :
    diamondDist (channelDenote (n + m) a (countingInverse n m none))
      (channelDenote (n + m) a (countingInverse n m (some kmax))) ≤ eta_aqft m kmax
```

Route: `channelDenote_of_unitary` (the inverse block is WF and unitary), `diamondDist_ofUnitary_le`,
`unitaryDenote_dataOnly`, `qftInvU_val` for both, `sub_kronecker_one`, `l2_opNorm_kronecker_one_le`,
the linearity of `liftP` in its argument, `l2_opNorm_liftP_le`, `l2_opNorm_conjTranspose`,
`unitaryDenote_zero_eq` with `l2_opNorm_kronecker_one_reg0`, and `aqft_opNorm_le`:
`2 · 2πm/2^kmax = eta_aqft m kmax`. Then the traced version for `traceRight ∘ …` by
`diamondDist_compose_le`.

### B4. The lemma

```
theorem ae_parametric_lemma_aqft (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network}
    (hN : N.WF) (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} (kmax : ℕ) {C : Circuit}
    (hC : countingCircuit N gp.n m (some kmax) shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
      (ae_eps a m) (ae_delta + eta_aqft m kmax / 2) g
```

Route:
1. `countingCircuit_ok` gives `body`, the same for `none` and `some kmax`. Prove the converse
   constructor (`countingCircuit … kmax = .ok (body.append (countingInverse n m kmax))` from the
   `body` equation and `m ≠ 0`) to obtain the exact circuit `C₀` and its `hC₀`.
2. `C.nAnc = C₀.nAnc = body.nAnc`: the inverse block has no ancilla (`nAnc_append`).
3. `(groverChannel (gp.n+m) C).chan = Ψ_kmax ∘ₘ Φ`, with `Φ = channelDenote body ∘ₘ replacement …`
   and `Ψ_k = traceRight ∘ₘ channelDenote (countingInverse n m k)`, by `channelDenote_append`; the
   same for `C₀` with `Ψ_none`.
4. The ideal composite: `ae_realizes` on `C₀`. Take its probability part, with grade `0` against
   budget `0`. Write `CountSpec` as `S_g.comp S_f` with `S_f : Spec Unit Unit := fun _ _ => True`
   and `S_g = fun _ => CountSpec m a ()` (an equality by `funext`).
5. `coherent_composition_diamond_pseudo` with `η_f = 0` (`diamondDist_self`) and `η_g = eta_aqft m
   kmax` (B3). Take the probability part of the conclusion, and the grade part from `hg`.

### B5. Tests

- Lean: `example` instances at `n = 2`, `m = 2`, `kmax = 1`; `#guard_msgs` axiom checks of
  `coherent_composition_diamond_pseudo`, `inverse_diamond_le` and `ae_parametric_lemma_aqft`.
- `tests/diff/counting_diff.py`, a new part (h): for two of the `n = 4` predicates with `M ≥ 1`, in
  coherent mode, at `m = 5, 6` (§A.8 item 3, moved here at the 19b review), the realized
  probability of `|countEst y − a| ≤ ae_eps a m` against `1 − ae_delta = 8/π²`; and at `m = 6`,
  `kmax = 4, 5`, the AQFT circuit's realized probability, printed next to `8/π² − eta_aqft/2`
  (vacuous for m ≤ 6, as in 18c; state it). Measure the step's time before and after; if part (h)
  adds more than about 60 s, keep `m = 5, 6` for one predicate only and say so.

### 20b2 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the pseudo-metric versions of Theorem 3.3b, and why the existing ones
keep `MetricSpace`; the reindexing lemma; the factorization of the channel; `η_f = 0`);
`docs/PROJECT_STATUS.md`; README status line. Reviewer files untouched.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; B1–B4 proved, no `sorry`, axioms the
standard three; the harness part (h) passes.

Stop and ask: a statement needs a hypothesis not listed; an existing statement would have to
change; the channel factorization of step 3 fails (for instance, if the ancilla registers of `C`
and `C₀` differ).

---

## 20b3 — The counting certificate (written at the 20b2 review, 2026-11-10; after 20b2 is accepted)

PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3" (1)–(6) — read it first. Precondition: main =
af4c813 (the 20b2 review commit). `git switch -c stage-20b3 main`; the 20b3 commit includes the
reviewer's edits to `docs/PHASE2_SPEC.md`, `docs/PHASE2_ROADMAP.md` and this file, unedited.

**Invariants of 20b3** (in addition to the ones above). The Grover pipeline is not touched:
`groverInstance`, `CertRequest`, `renderCert*`, `Certificate`, `Certificate.build`, `RunData`,
`schemaVersion` (it stays `"1.9.0"`) and every committed certificate directory stay byte-identical;
`cqr certify` produces the same files as before. No new `cqr` subcommand or flag. Every new module
in `CQRV/Certify/` and `CQRV/Synthesis/` is Physlib-free. The instance is grover_pred_037,
`n = 8`, `M = 32`, `m = 4`, `kmax = none`, shape tree, mode MBU.

### C1. Library support (Physlib-free; `CQRV/Synthesis/Counting.lean`, `CQRV/Circuit/GradeCompose.lean`)

- `assembleCounting (init : Circuit) (bs : List Circuit) (inv : Circuit) : Circuit` — the fold of
  `Circuit.append` over `bs.zipIdx.flatMap fun (b, j) => List.replicate (2 ^ j) b` from `init`, then
  `.append inv`. Write it so that it is literally the list form of `grade_foldl_append_le`.
- `countingCircuit_of_blocks : m ≠ 0 → bs.length = m → (∀ j (h : j < m), controlledGrover N n m j
  shape mode = .ok (bs.get ⟨j, _⟩)) → countingCircuit N n m kmax shape mode = .ok (assembleCounting
  (countingHLayer n m) bs (countingInverse n m kmax))`, by induction through `countingPowers` (the
  converse direction of `countingCircuit_ok` / `countingCircuit_of_body`).
- `grade_assembleCounting_le` — with every block on the same data register and `liveEnd = 0`:
  `(assembleCounting init bs inv).grade ≤ init.grade + (bs.zipIdx.map fun (b, j) => 2 ^ j • b.grade).sum
  + inv.grade`; and `gradeExt_assembleCounting` — `twoQ`, `rot`, `meas`, `ff` equal to the
  corresponding sums, `tDepth ≤ init.tDepth + ∑ 2^j · tCount b + tCount inv`. From 19a's list forms.
  Shape the right-hand sides so that a `Cert.lean` rewrites them with the block `grade_eq` /
  `gradeExt_eq` and closes the arithmetic by `decide`, with no kernel run of the scheduler on the
  whole circuit.
- Tests in `tests/CQRVTests/Counting.lean` at `n = 4`, `m = 2` (the 19b instance): `#guard` that
  `assembleCounting` of the built blocks equals the built circuit, and examples of the two theorems.

### C2. The generator (`CQRV/Certify/CountCert.lean`, new, Physlib-free)

Its own `CountRequest`, `renderCountCert : CountRequest → String`, `CountCertificate` with `toJson`,
and a counting run report (Markdown and JSON). Reuse the literal printers (`circuitLit`,
`networkLit`, the typed-program printer), SHA3, `predicateHash`, `circuitHash` (of
`emitted.toJson.compress`, the assembled circuit, computed in compiled code), `proofHash`,
`RefConfig`, `detectMachine`, `checkAndAudit`, `emitQIR`, `emitQASM`. Do not change any of them.
`Cert.lean` (namespace `CQRV.Cert.«grover_pred_037_count»`):

1. `net`, `prog`, `prog_scoped`, `net_ok`, `front_end` (as the Grover certificates);
2. the six block literals with `_ok`, `_grade_eq`, `_gradeExt_eq`, `_liveEnd` (the 19b probe form);
3. `emitted := assembleCounting h_layer [cg_0, cg_1, cg_2, cg_3] inverse` and `emitted_ok` from
   `countingCircuit_of_blocks` and the four `cg_j_ok`;
4. `grade_le : Synthesis.grade emitted ≤ ⟨20, 1388, 660, 8⟩` and `gradeExt_bound` (the four equalities
   and the `tDepth` bound) from C1 and the block theorems — the numbers the generator computes, not
   these hard-coded ones;
5. `hN : net.WF`; `cert` universal in `M` as amendment (3), from `ae_parametric_lemma` with
   `gp := ⟨8, M, hpos, Network.pred net 8, hcard⟩`; `hM_count` (the kernel-decided `32`, as the
   Grover certificates) and `cert_count`, the instance at `M = 32`;
6. `#print axioms cert` and `#print axioms cert_count`.

The JSON follows amendments (4) and (5): `schema_version "1.10.0"`, `pattern "Count"`, `instance
{n, M, m, kmax}` (M the kernel-decided count), `spec {epsilon: {expr, approx}, delta: {expr, approx},
estimate: "sin^2(pi*y/2^m)"}`, `grade` with `grade_kind "composed_bound"`, `grade_ext` with its
`t_depth` marked as a bound, `blocks`, `solution_count {value 32, status kernel_decided}`,
`hypotheses` (M ≥ 1, no claim for M = 0; m = 4; exact inverse QFT), `restoration`, `hashes`,
`trust_boundary` (the proved front end; the emitted QIR text; the emitter translation-validated by
re-parse), `hardware_perturbation` (gate counts of the assembled circuit; the QASM measures all
`n + m` data qubits, and `countPOVM` reads only the phase register, which is the same POVM),
`reference_configuration`, `theorem "CQRV.Cert.grover_pred_037_count.cert"`, `axioms`,
`obligations []`, `status "certified"` only after the kernel check and the axiom audit pass. The
run report says in words what the certificate states, including the ±43 in M units and why m = 4
was chosen (amendment (4)).

`CertifyTool count-certify <file.cqr> <m> --out <dir> [--report]` writes `Cert.lean`, runs
`checkAndAudit`, then writes `certificate.json`, `<name>.qir`, `<name>.qasm` and, with `--report`,
`run_report.{md,json}`; on a failed check it writes no JSON and exits 1, as `cqr certify` does.
Commit the output for grover_pred_037 at m = 4 as `examples/certs/grover_pred_037_count/`.

### C3. Schema (`docs/certificate.schema.json`, `tests/diff/cert_schema.py`)

Add `"1.10.0"` to the version enum with a `pattern: "Count"` branch (amendment (5)); under 1.10.0
only `"Count"` is allowed for now. Every committed certificate validates unchanged; every existing
negative test of `cert_schema.py` is still rejected. New negative tests for the branch: missing
`grade_kind`; `grade_kind "measured"` with `pattern "Count"`; `spec.epsilon` as a bare number or a
rational string; an extra key in `instance`; a `blocks` entry without `multiplicity`; the
`Count` pattern under `1.9.0`.

### C4. Checks (`tests/diff/certify_check.py`, `scripts/print_axioms.sh`)

A counting section in `certify_check.py` (inside the existing step, so the pass mark stays 18):
`count-certify` twice — `Cert.lean`, `.qir`, `.qasm` byte-identical, the JSON equal outside the
machine fields — and the comparison with the committed directory (JSON outside
`reference_configuration`); the schema; the predicate hash; the circuit hash recomputed in Python
by **replaying the six block literals of `Cert.lean`** with their multiplicities and bit shifts (as
`counting_diff.py`'s `replay`); `proof_hash`; the QASM re-parsed equal to the assembled circuit, the
QIR equal to it after `decomposeCp` (the `emit_diff.py` path: the inverse QFT has six `cp`); the
JSON's composed grade equal to the sum the Python recomputes from the blocks' grades; the
`theorem`, `axioms`, `status`. Negative tests on temporary copies, through `CertifyTool audit`: a
mutated gate in one block literal (the kernel rejects `_ok`), and `grade_le` with `d` lowered by
one (the kernel rejects it). Add the directory to `scripts/print_axioms.sh`. Report the step's time
before and after.

### 20b3 Docs / Acceptance / Stop

Docs: DECISIONS.md entry; `docs/PROJECT_STATUS.md`; README status line ("Stages 0–20b"); one paragraph
in `examples/certs/README.md` (if it exists) on the counting certificate and what it does not claim.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; `cert` and `cert_count` kernel-checked
with axioms exactly `propext`, `Classical.choice`, `Quot.sound`; every Lean process below 8 GB; the
Grover certificates byte-identical; the new negative tests rejected.

Stop and ask: a block above 600 gates or a `grade_eq` above 30 s; the kernel check of the
certificate above 8 GB or 10 minutes; a change needed anywhere in the Grover pipeline; a statement
of C1 that needs a hypothesis not listed; the composed bound differing from the probe's
`(20, 1388, 660, 8)` (report both, do not adjust).

**Notes added at the 20b3 review (2026-11-13).** 20b3 is accepted as implemented (ba9bb6c). No stop
condition was hit: blocks of 244 gates, `grade_eq` about 1.5 s, the kernel check of `Cert.lean`
18 s at 2.6 GB, the composed bound equal to the probe's. Two deviations are accepted:
- `cert` goes through `ae_parametric_lemma_mk`, which avoids an elaboration cost of the record
  form;
- the C1 lambdas use projections.

Both are recorded in DECISIONS.md. The items Stage 21 inherits are listed in PHASE2_SPEC §A.4
under "20b3 done": the early refusal of `M = 0`, a `--count-limit` policy, the Grover certificates
at 1.10.0, and the wording of the schema's `grade` description.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests — CI summary, the axiom lines, for 20b2 the
harness numbers of part (h), for 20b3 the kernel time and peak memory of the certificate and the
step's time —, (d) SORRIES.md, (e) open questions; for 20b2, what the certificate task 20b3 should
know; for 20b3, what Stage 21 should know about wiring the generator into `cqr certify`.
