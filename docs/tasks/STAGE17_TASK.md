# Stage 17 — IR and grade extension: exact phase gates `p` / `cp`, `GradeExt`, `gradeExt_eq` in every certificate

PHASE2_SPEC.md §A.1 (as amended 2026-10-31 in the Stage 16b review commit), §A.8 item 2; report
§9.1.1 (the IR), §3.1.1 (the grade), §5.3 (trust boundaries), §8.4.3 (emitters);
PHASE2_ROADMAP.md row 17. Two tasks, **two commits**: do **17a**, reply, stop; start **17b** after
the reviewer accepts 17a.

Precondition: Stage 16b accepted; main = the 16b review commit. `git switch -c stage-17a main`
(17b: `stage-17b` from `stage-17a`). The 17a commit includes this file (untracked until then; do
not edit it). Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`.
Windows: `LEAN_NUM_THREADS=4`. Process as in Stage 16: `lake build` in the foreground;
`scripts/ci_local.sh` and any Lean run longer than a few minutes are the user's separate terminal,
one Lean process at a time; when the build is green and the tests you can run yourself pass, stop
and say "ready for CI"; after the user's run, read `.lake/ci_local/*.log`, commit, closing reply.

**Invariants of both tasks.** `Grade`, `Circuit.grade`, the scheduler's placement rule
(`SchedState.step`), `TempLogicalAND`, `MBU`, the synthesizer, the diffusion builders,
`groverCircuit` and **every existing theorem statement are not modified**; no synthesized circuit
contains a `p` or `cp` gate after this stage (the new gates are infrastructure for Stages 18–20).
The committed `cert`, `net`, `prog`, `emitted` literals and the QIR / QASM files stay
byte-identical; `Cert.lean` gains exactly one theorem (`gradeExt_eq`, 17b). If a proof or a
`match` seems to need a change in one of the frozen definitions, stop and propose.

## Why a second record (§A.1, §A.8.2)

`Grade` stays (w, d, t, a) as Table 3.1 defines it. The paper reviews asked for a two-qubit count
and a T-depth, and the counting circuits of Stages 19–20 bring rotation gates whose Clifford+T
cost depends on a synthesis precision that is a hardware matter (§C). So a second record
`GradeExt` is measured by the same scheduler and stated in every certificate as its own theorem;
nothing about `Grade` or the budget order changes. The phase gates are exact: `p a k` is
diag(1, e^{2πi·a/2^k}) with `a : Int`, `k : Nat` — no floating point in the IR or in the kernel;
floating point appears only in the QIR text (17b), which is a declared trust boundary.

---

## 17a — IR, semantics, well-formedness, scheduler, `GradeExt`, `decomposeCp` (library stage; no emitter, CLI, certificate or Python change)

### A1. Gates (`CQRV/Circuit/IR.lean`)

- Two constructors appended to `Gate`, nothing else changes:
  ```
  | p  (a : Int) (k : Nat) (q : Qubit)       -- diag(1, exp(2πi·a/2^k)) on q
  | cp (a : Int) (k : Nat) (c t : Qubit)     -- that phase on the states where c and t both read 1
  ```
  (`deriving Repr, DecidableEq, Inhabited` keep working.)
- Every function on `Gate` gets **explicit equations** for the two constructors wherever a
  catch-all would be wrong: `qubits` (`[q]`, `[c, t]`); `isClifford`: `p a k` iff
  `(2 ^ k : Int) ∣ 4 * a`, `cp a k` iff `(2 ^ k : Int) ∣ 2 * a`; `tCount`: `p a k` is 1 iff
  `(2 ^ k : Int) ∣ 8 * a ∧ ¬ (2 ^ k : Int) ∣ 4 * a` (an odd multiple of π/4: `p 1 3`, `p (-1) 3`,
  `p 3 3`, `p 2 4`, … count exactly as `t` / `tdg`), `cp` contributes 0; `adjoint`: `p (-a) k q`,
  `cp (-a) k c t`; `shiftBits`, `writes`: the catch-all is right; `render`: `P(a/2^k) x[i]`,
  `CP(a/2^k) x[i] x[j]` with `a` and `2^k` printed as integers (fraction of a full turn — say so
  in the doc-comment). New: `Gate.isTPower : Gate → Bool` (the `tCount = 1` condition for `p`,
  `true` for `t` / `tdg`, `false` otherwise; `ifBit` looks inside) and `Gate.isRotation : Gate →
  Bool` (a `p` / `cp` that is neither Clifford nor a T-power; `false` for every other
  constructor; `ifBit` looks inside), with the theorem `tCount_eq_isTPower : g.tCount = if
  g.isTPower then 1 else 0`.
- `Circuit.validate`: `cp` operands distinct (the repeated-qubit check next to `cnot` / `cz`);
  `ifBit` may control a Clifford `p` / `cp` (it falls out of `isClifford`). `gateJson`:
  `{"op":"p","q":[i],"a":a,"k":k}` and `{"op":"cp","q":[c,t],"a":a,"k":k}` (`a` a JSON integer,
  possibly negative; `k` a natural).
- `Gate.qubitsOk` (`CQRV/Circuit/Semantics.lean`): `cp` operands distinct, like `cnot` / `cz`.

### A2. Semantics (`CQRV/Circuit/Semantics.lean`)

- `def phaseOf (a : Int) (k : Nat) : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / 2 ^ k)` (fix
  the exact form you can work with; state it once). Lemmas: `star_phaseOf_mul : star (phaseOf a k)
  * phaseOf a k = 1` (unit modulus — find the Mathlib route with `exact?` / `Complex.exp_conj`,
  `Complex.exp_add`, `Complex.exp_zero`; no invented names), `phaseOf_neg : phaseOf (-a) k = star
  (phaseOf a k)`, `phaseOf_add_self : phaseOf a (k + 1) * phaseOf a (k + 1) = phaseOf a k`.
- `gateU (.p a k q) = phaseMat n a q (phaseOf a k)`; `gateU (.cp a k c t) = monoMat id (fun s =>
  if c.get s && t.get s then phaseOf a k else 1)` (as `cz` with `-1` replaced).
  `gateU_mem_unitaryGroup` extends with no new hypothesis (`phaseMat_mem_unitaryGroup` with
  `star_phaseOf_mul`; the `cp` case like `cz` with `monoMat_mem_unitaryGroup`). `gateU_adjoint`,
  `unitaryDenote_adjoint`: the new cases (`isUnitary` is `true` for both; `star_phaseMat`,
  `phaseOf_neg`). `gateK`: its catch-all (`gateU`) is right. Check that every `match` in
  `Semantics.lean`, `Restoration.lean`, `OracleCorrect*.lean`, `Schedule.lean` is still exhaustive
  and that no proof silently acquired a new goal (adding a case to a proof is fine; changing a
  statement is not).
- The identities, as theorems about `gateU n a`: `gateU_p_one_one : gateU n a (.p 1 1 q) = gateU
  n a (.z q)`, `gateU_p_one_two : … (.p 1 2 q) = … (.s q)`, `gateU_p_neg_one_two : … (.p (-1) 2
  q) = … (.sdg q)`, `gateU_p_one_three : … (.p 1 3 q) = … (.t q)`, `gateU_p_neg_one_three : …
  (.p (-1) 3 q) = … (.tdg q)`, `gateU_cp_one_one : gateU n a (.cp 1 1 c t) = gateU n a (.cz c
  t)` (`Complex.exp_pi_mul_I`; `ω` is `Complex.exp (Real.pi / 4 * Complex.I)` by definition;
  `star_ω`; find the π/2 lemma with `exact?`). Pointwise action: `gateU_p_mulVec`,
  `gateU_cp_mulVec` in the style of `gateU_cz_mulVec`.
- `Circuit.decomposeCp : List Gate → List Gate`: every **top-level** `cp a k c t` replaced by
  `[.p a (k+1) c, .p a (k+1) t, .cnot c t, .p (-a) (k+1) t, .cnot c t]` (θ = 2πa/2^k, so θ/2 is
  `a / 2^(k+1)`); every other gate kept, **including** `ifBit _ (cp …)` (left undecomposed; the
  QIR emitter of 17b refuses it with a diagnostic — say so in the doc-comment). Theorems:
  `decomposeCp_gate (hct : c ≠ t) : unitaryDenote n a [.p a (k+1) c, .p a (k+1) t, .cnot c t,
  .p (-a) (k+1) t, .cnot c t] = gateU n a (.cp a k c t)` (monomial-matrix calculation:
  `monoMat_mul`, case analysis on `c.get s` and `t.get s`, `phaseOf_add_self`, `phaseOf_neg`,
  `star_phaseOf_mul`; the hypothesis `c ≠ t` because `gateU (.cnot c c) = 1`), `decomposeCp_unitary
  (gs) (h : ∀ g ∈ gs, g.isUnitary = true) (hq : every cp in gs has distinct operands — phrase it
  through `Gate.qubitsOk` or a separate predicate) : unitaryDenote n a (decomposeCp gs) =
  unitaryDenote n a gs` (by `unitaryDenote_append`), `decomposeCp_wf : C.wf = true → (⟨C.nData,
  decomposeCp C.gates⟩ : Circuit).wf = true` (17b's QIR path needs it). If `decomposeCp_gate` does
  not close in reasonable time, leave it as a **tracked `sorry`** (SORRIES.md entry, the obligation
  stated) and say so — no certificate depends on it in Stage 17.

### A3. `GradeExt` (new `CQRV/Grades/Ext.lean`; `CQRV/Circuit/Schedule.lean`)

- ```
  structure GradeExt where
    twoQ   : Nat   -- cnot, cz, cp (also under ifBit)
    tDepth : Nat   -- layers of the decision-4 schedule that contain a t / tdg or a T-power p
    rot    : Nat   -- p / cp gates that are neither Clifford nor T-powers (also under ifBit)
    meas   : Nat   -- measure gates
    ff     : Nat   -- ifBit gates
    deriving DecidableEq, Repr
  ```
  No ⊕/⊗ algebra for `GradeExt` in this stage (it is measured, not composed) — doc-comment.
- `Circuit.gradeExt (c : Circuit) : GradeExt` from the **same** `schedule` as `grade`: `twoQ`,
  `rot`, `meas`, `ff` by one fold over the gates (through `ifBit`); `tDepth` = number of layers
  `k ≥ 1` such that some gate placed in layer `k` has `isTPower = true` (read off `schedule c`; no
  second scheduler). `Synthesis.gradeExt` next to `Synthesis.grade` (whichever module exposes
  `grade` to the certificates — follow `grade_eq`).
- Sanity theorems: `gradeExt_meas_eq_nBits : c.gradeExt.meas = c.nBits` (proved);
  `gradeExt_tDepth_le_depth : c.gradeExt.tDepth ≤ c.depth` (proved); `gradeExt_tDepth_le_tCount :
  c.gradeExt.tDepth ≤ c.tCount` (proved or tracked).

### A4. Tests (`tests/CQRVTests/Semantics.lean`, `tests/CQRVTests/Grades.lean`, `tests/CQRVTests/Synthesis.lean`)

- `#guard`s: `isClifford` / `isTPower` / `isRotation` on `p 1 1`, `p 1 2`, `p 1 3`, `p 2 4`,
  `p 3 3`, `p 1 4` (rotation), `p 0 5` (Clifford: the identity), `p (-3) 5` (rotation), `cp 1 1`
  (Clifford), `cp 1 2` (rotation), `cp 2 2` (Clifford); `tCount_eq_isTPower` instances; `adjoint`
  of `p` / `cp`; `Circuit.validate` accepts `cp` on distinct qubits and `ifBit` over `cp 1 1`,
  rejects `cp q q` and `ifBit` over `p 1 3`; `decomposeCp` of a hand-built list (expected list
  written out), `decomposeCp_wf` on it; `Circuit.toJson` of a circuit with `p` / `cp` (`#guard` on
  the compressed text).
- `gradeExt` on hand-built circuits with the five values computed by hand in a comment, and on
  the running example: `okPayload (groverCircuit net 8 2)` (`rot = 0`, `meas = 18`, `ff = 36`,
  `twoQ` and `tDepth` as measured), its coherent variant (`meas = 0`, `ff = 0`), `TempLogicalAND`,
  `okPayload (mczFewK 8 .logDepth)`; `gradeExt_meas_eq_nBits` instances. Record the measured
  `GradeExt` of the four committed circuits (grover, alu, few, coh) in the closing reply — 17b
  writes them into the certificates.
- `#guard_msgs` axiom checks of `decomposeCp_unitary` (the standard three, or the `sorryAx` line
  if tracked) and of `gateU_mem_unitaryGroup`.

### 17a Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the T-power rule as a divisibility condition — not "`k = 3` and `a`
odd" — so that `p 2 4` and `p 1 3` are classified alike; `rot` for `cp` means non-Clifford;
`decomposeCp` leaves `ifBit`-controlled `cp` alone; `GradeExt` has no algebra yet; what was
tracked, if anything), SORRIES.md if anything is tracked, `docs/PROJECT_STATUS.md` one line. No
README change in 17a. Do not edit `docs/PHASE2_SPEC.md` or `docs/PHASE2_ROADMAP.md` (reviewer
files; commit them unedited if the working tree holds reviewer edits).

Acceptance: `lake build` green and warning-free; CI 16 PASS, 0 FAIL, 4 n/a; `Grade` and every
existing theorem statement unchanged (the reviewer checks by script); no synthesized circuit
changed (golden files, CI step 14); the running example's `GradeExt` reported.

Stop and ask: a change to `Grade`, `SchedState.step`, `grade`, or any existing statement seems
necessary; `gateU_mem_unitaryGroup` needs a new hypothesis; a `match` cannot be made exhaustive
without touching a proof whose statement would change.

---

## 17b — emitters, re-parsers, harness, `gradeExt_eq`, schema 1.9.0 (after 17a is accepted)

### B1. JSON, harness, the sample circuit

- `tests/diff/statevector.py`: `p` and `cp` from `{"op","q","a","k"}` (exact
  `cmath.exp(2j*math.pi*a/2**k)`); unit tests: `p 1 2` equals the `s` table, `p 1 3` the `t`
  table, `p (-1) 3` `tdg`, `p 1 1` `z`, `cp 1 1` `cz`, on random states; a circuit with `cp`
  gives the same state as its five-gate decomposition (Python side builds the five gates).
  `oracle_json.py` and the golden files unchanged.
- `CQRV/Emit/Basic.lean`: `Emit.sampleCircuit` — 3 data qubits, 1 ancilla, every gate constructor
  at least once, including `p 1 3`, `p (-3) 5`, `p 2 4`, `p 0 5`, `cp 1 1`, `cp 1 2`,
  `cp (-1) 3`, an `ifBit` over `p 1 1` and one over `p 1 2`, `measure`, `alloc` / `free`;
  `Circuit.validate` passes; **no** `ifBit` over `cp`. `Emit.sampleCircuitIfCp`: the same with one
  `ifBit` over `cp 1 1` (the negative QIR test). `scripts/CertifyTool.lean`: new command
  `emit-sample <json|qasm|qir> [--decompose-cp] [--if-cp]` printing the sample as IR JSON (through
  `decomposeCp` with `--decompose-cp`), OpenQASM 3 or QIR (exit 1 with the diagnostic JSON for
  `qir --if-cp`). This is the test path for gates no synthesized circuit contains.

### B2. Emitters (`CQRV/Emit/QASM.lean`, `CQRV/Emit/QIR.lean`) and re-parsers

- OpenQASM 3: `p(2*pi*{a}/{N}) q;` and `cp(2*pi*{a}/{N}) c, t;` with `N = 2^k` **evaluated** to
  an integer (`^` is XOR in OpenQASM 3) and `a` printed as an integer, in parentheses when
  negative (`p(2*pi*(-3)/32) x[0];`, `cp(2*pi*1/2) x[0], x[1];`); both gates are in
  `stdgates.inc`; `ifBit` over a Clifford `cp` is `if (c[j]) { cp(…) x[0], x[1]; }` as today.
  `tests/diff/reparse_qasm.py`: `RE_GATE` gets an optional argument group
  `\(2\*pi\*(-?\d+|\(-\d+\))/(\d+)\)` and returns `a`, `k` (`N` must be a power of two, `k =
  log2 N`); the comparison in `emit_diff.py` is exact on `(op, qubits, a, k)`.
- QIR: `p a k q` → `call void @__quantum__qis__rz__body(double <θ>, ptr …)` with θ = 2πa/2^k as a
  `Float` printed as an **LLVM hex-float literal** (`0x` followed by the 16 hex digits of
  `Float.toBits` — confirm the name with `#check` first; a decimal literal that is not exactly
  representable is rejected by `llvm-as` and llvmlite); `declare void
  @__quantum__qis__rz__body(double, ptr)`. `rz(θ) = e^{-iθ/2} · p(θ)`: a global phase per gate
  (per branch under `ifBit`), irrelevant to every statement of this project — the module
  doc-comment and run-report row 8 say so. A top-level `cp a k c t` → the five calls of
  `Circuit.decomposeCp` (`rz`, `rz`, `cnot`, `rz`, `cnot`); an `ifBit` over a `cp` → the emitter
  returns `.error` with a diagnostic (stage `emit`, code `unsupported_in_qir`: "classically
  controlled cp has no QIR form in this emitter"; `cqr emit` prints the diagnostic JSON, exit 1,
  nothing written; QASM is unaffected). `emitQIR` therefore returns `Except Diagnostic String` (or
  a sibling `emitQIR?`; keep the existing callers byte-identical in output).
  `tests/diff/reparse_qir.py`: `rz` → `{"op":"p","q":[i],"angle": float}` (parse the hex float
  with `struct`); `emit_diff.py` compares a QIR re-parse against the IR after `decomposeCp` (the
  Lean side: `cqr synthesize --json --decompose-cp`, or `emit-sample --decompose-cp` for the
  sample — the flag exists on `synthesize` only if it is one line; otherwise sample-only,
  documented), with `p` gates matched on qubits and `|angle − 2πa/2^k| ≤ 1e-12·(1 + |angle|)`;
  the `cqrv: alloc|free` deletion test unchanged in kind. `emit_diff.py` runs on the Grover
  circuits as today **and** on the sample (QASM exact; QIR against the decomposed sample; the
  negative `--if-cp` case: exit 1, diagnostic code `unsupported_in_qir`). llvmlite verifies the
  sample's QIR as it verifies every QIR text (CI step 19 / check_emit).

### B3. Certificates (`CQRV/Certify/Generate.lean`, `Certificate.lean`, `RunReport.lean`, `Apps/cqr/Main.lean`)

- Every template, right after `grade_eq`: `theorem gradeExt_eq : Synthesis.gradeExt emitted =
  ⟨{twoQ}, {tDepth}, {rot}, {meas}, {ff}⟩ := by decide +kernel`. `cert` unchanged (it does not
  take `gradeExt_eq`). Everything else in `Cert.lean` byte-identical to the 16b files — extend the
  byte-identity test of `certify_check.py`: the 16b file (git `7f46857`) plus exactly that theorem
  (and its doc-comment) after `grade_eq`.
- `Certificate` gains `gradeExt : GradeExt`; JSON `"grade_ext": {"two_qubit", "t_depth", "rot",
  "meas", "ff"}` (naturals; keys sorted as everywhere), required under schema **1.9.0**;
  `schemaVersion := "1.9.0"`; `docs/certificate.schema.json`: `grade_ext` present iff `1.9.0`; the
  proved `front_end` wording allowed under 1.8.0 and 1.9.0 (adjust the `if` / `else`); `uncompute`
  and `solution_count` required under 1.9.0; legacy envelopes still validate; `cert_schema.py`
  negative tests (`1.9.0` without `grade_ext`, `grade_ext` under `1.8.0`, a negative or missing
  component, an extra key). Consistency asserted in `certify_check.py` for every certificate it
  checks: `grade_ext.meas == hardware_perturbation.counts.mid_circuit_measurements`,
  `grade_ext.ff == counts.classically_controlled`, `grade_ext.two_qubit` equals a Python count of
  `cnot` / `cz` / `cp` (through `if`) over the `emitted` literal it already parses, `rot == 0`;
  `t_depth ≤ grade.d` and `t_depth ≤ grade.t`.
- Run report: row 4 ("QPLP Instant.") resources gain `; ext: 2Q {twoQ}, T-depth {tDepth}, rot
  {rot}, meas {meas}, ff {ff}`; when `rot > 0` the row's note adds "Clifford+T cost of the rotation
  gates depends on the synthesis precision (PHASE2_SPEC §C), not folded into t" (§A.8.2 as
  amended: the note only when `rot > 0`); row 8's note gains one sentence on the QIR `rz` global
  phase. No `hardware` budget on `GradeExt` in this stage (profile schema unchanged).
- Regenerate the four committed certificates with their own flags (as in 16b: `grover_pred_037`
  and `simple_alu_x0_1` without `--profile`, `_few` and `_coh` with `--profile illustrative_sc`;
  all with `--bench 5 --report`); QIR / QASM byte-identical (assert in `certify_check.py`);
  `scripts/print_axioms.sh` unchanged (`cert` and `front_end`; `gradeExt_eq` is a `decide`
  theorem like `grade_eq`).

### 17b Docs / Acceptance / Stop

Docs: DECISIONS.md entry (QASM angle syntax with the evaluated power and the parenthesised
negative; QIR `rz` + hex float + the global-phase note; `cp` decomposed in QIR, refused under
`ifBit`; `grade_ext` keys; schema 1.9.0; the measured `GradeExt` of the four certificates and the
kernel medians old → new), `docs/PROJECT_STATUS.md` (grade line, schema), README status line,
`scripts/check_certify.sh` and `scripts/check_emit.sh` headers.

Acceptance: `lake build` green; CI 16 PASS; four certificates `certified` with `grade_ext`
kernel-decided; `cert` / `net` / `prog` / `emitted` and QIR / QASM byte-identical; emit_diff on the
Grover circuits and on the sample (both emitters, the negative case); statevector `p` / `cp`
tests; the schema negative tests.

Stop and ask: `gradeExt_eq` alone exceeds 30 s in the kernel for any certificate, or a kernel
median exceeds twice its 16b value (14.40 / 16.70 / 12.60 / 25.40 s); `llvm-as` or llvmlite rejects
the hex-float form; `Float.toBits` (or an equivalent) does not exist in this toolchain — then stop
and propose (do not print decimals); `emitQIR`'s new error path would change the output of an
existing certificate's `.qir` by a byte.

## Closing reply (both tasks)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests (17a: the `GradeExt` of the four committed
circuits; 17b: CI summary, kernel-time table old → new, `grade_ext` of each certificate, emit_diff
results including the sample), (d) SORRIES.md, (e) open questions — including, for 17b, whether
the **chunked `emitted` literal** (the 14b/14c ceiling, ~1953 instructions) should be designed at
Stage 18 or Stage 19; and anything learned incidentally about the `Nat m` elaboration slowness
(16b open item; no experiment requested).
