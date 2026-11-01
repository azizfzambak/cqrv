# PHASE2_SPEC — specification addendum (report v4 → v5)

Status: §A drafted 2026-10-29 by the reviewer; approved by the author on 2026-10-29 for
Stages 15–21, including the reviewer's recommendations on the design choices listed in §A.8
(output type `Fin (2^m) ⊕ Unit` with the induced metric as the primary route; exact phase gates
`p`/`cp` with `rot` outside the T-count; AQFT as the Theorem 3.3b client; precision `m = 4` for
the committed counting certificate). §B (restoration theory) and §C (hardware backend) are
written before their first stages.

This document plays, for Phase 2, the role the report plays for Phase 1 (CLAUDE.md rule 5):
task files cite its sections, doc comments cite them (`/-- PHASE2_SPEC §A.3 -/`), and a
disagreement between code and this text is reported, not resolved silently. Where it extends
the report it says which report section it extends; where it departs from the report (the report
plans plain amplitude amplification, §9.3.1, §10.1.1) it says why. Statements written in Lean
syntax are *statement sketches*: the task file of the stage fixes the exact form, and the usual
rule applies — hypotheses the formalization needs are made explicit and recorded.

Conventions: `Reg k := Fin k → Bool`; qubit 0 is the most significant bit of an index
(as in the harness); `ω = e^{iπ/4}`; the ASAP scheduler of Stage 5 decision 4 measures every
grade; nothing below changes `Grade`, `Realizes`, `AncRestore`, or any Phase 1 statement.

---

## §A. Certified amplitude estimation (quantum counting)

### A.0 Why estimation, not amplification (departure from report §9.3.1, §10.1.1)

The report's second pattern is amplitude amplification; its stated purpose is to exercise
Theorem 3.3b. Amplitude estimation (Brassard, Høyer, Mosca, Tapp 2002, Theorem 12) does that and
more: its output is a rational approximation of a = M/2ⁿ, so the specification needs a metric
and ε > 0; its success probability is 8/π², so δ > 0; the Grover iterate is used as an
*unmeasured* controlled subroutine; the approximate QFT gives Theorem 3.3b a client with a real
η > 0; and the solution count M, today a hypothesis on every certificate (§8.2), is produced by the
pattern. The amplification pattern is then a corollary and is not built separately. The report's
qualification in §10.1.1 — a state preparation containing MBU has no adjoint — is met by the
coherent uncomputation mode of §A.0.1, which the hardware track also needs.

#### A.0.1 Coherent uncomputation mode (extends report §6.1.4, §6.2.2, §10.1.1)

`inductive UncomputeMode | mbu | coherent`. In mode `coherent` the uncompute block of an AND is
the adjoint of its compute block: `pre ++ adjoint (TempLogicalAND p q t) ++ [free t] ++ pre.reverse`,
where `adjoint` reverses a measurement-free gate list and swaps `s ↔ sdg`, `t ↔ tdg`
(`h`, `x`, `z`, `cnot`, `cz` are self-adjoint). Cost: 8 T per AND, no classical bit, no
measurement. `mbu` remains the default and is byte-for-byte the Phase 1 synthesizer.

Lemma 6.3.2 holds in both modes (`lemma_6_3_2_xor_of_le` for `mbu`, `lemma_6_3_2_coherent_of_le`
for `coherent`); so do `synthesizeOracle_WF` and `synthesizeOracle_succeeds`. The Grover
parametric lemma is restated with the oracle abstract (`grover_parametric_lemma_gen`): any
circuit on n data qubits that respects the bit discipline and restores its ancillae with
`phaseOracle P` on every register at least as large as its own; the Phase 1 lemmas are instances.
Certificates record the mode (`"uncompute": "mbu" | "coherent"`). Bennett pebbling and the
few-ancilla MCZ keep MBU in this stage; the combination is rejected with a diagnostic, not
silently changed: diagnostic code `unsupported_combination` (`Code.unsupportedCombination`,
added in Stage 15a; it is a new code because no existing one names a legal request whose parts
are individually supported but not together, and Phase 3 needs every terminating diagnostic
classified).

### A.1 IR extension: exact phase gates and the extended grade (extends report §9.1.1, §3.1.1)

**Gates.** Two constructors are added to `Gate`, nothing else changes:

```
| p  (a : Int) (k : Nat) (q : Qubit)          -- diag(1, exp(2πi·a/2^k)) on q
| cp (a : Int) (k : Nat) (c t : Qubit)        -- the same phase on |11⟩ of (c, t)
```

Semantics: `gateU (.p a k q) = phaseMat n a q (exp (2πi a / 2^k))`, a monomial matrix, so
`gateU_mem_unitaryGroup` extends without hypotheses; `cp` is diagonal with that entry on the
states where both qubits read 1 (as `cz` is with −1). Identities, proved as theorems about
`gateU`: `p 1 1 = z`, `p 1 2 = s`, `p (-1) 2 = sdg`, `p 1 3 = t`, `p (-1) 3 = tdg`, `cp 1 1 = cz`
(as matrices; amended 2026-10-31: `p a 1` is `z` only for odd `a`). Adjoint: `p (-a) k`,
`cp (-a) k`.

**Well-formedness.** `qubitsOk`: operands in range, `cp` operands distinct. `isClifford`:
`p a k` iff `2^k ∣ 4a` (angle a multiple of π/2); `cp a k` iff `2^k ∣ 2a` (angle a multiple of
π). `ifBit` may control a Clifford `p`/`cp` and nothing else (the bit discipline is unchanged).

**Grade.** `Grade` is unchanged. `Gate.tCount` of `p a k` is 1 when the angle is an odd multiple
of π/4, i.e. `2^k ∣ 8a` and not `2^k ∣ 4a` (amended 2026-10-31 from "`k = 3` and `a` odd", so that
`p 2 4` is classified as `p 1 3` is; `Gate.isTPower`), else 0; `cp` contributes 0 to `t`. The
non-Clifford phase gates that are not T-powers (`rot`; for `cp`: the non-Clifford ones,
`Gate.isRotation`) are counted in a second record, computed by the same scheduler (no ⊕/⊗ algebra
for it in Stage 17: it is measured, not composed):

```
structure GradeExt where
  twoQ   : Nat   -- cnot, cz, cp (also under ifBit)
  tDepth : Nat   -- layers (k ≥ 1) of the decision-4 (ASAP) schedule that contain a t/tdg or a T-power p
  rot    : Nat   -- p/cp gates that are neither Clifford nor T-powers
  meas   : Nat   -- measure gates
  ff     : Nat   -- ifBit gates
```

Stage 17a (b32b999, accepted 2026-10-31): `CQRV/Grades/Ext.lean`; `Circuit.gradeExt` reads the
record off the same `schedule` as `grade` — `twoQ`, `rot`, `meas`, `ff` by `countP` over the
gates (`Gate.isTwoQubit`, `isRotation`, `isMeasure`, `isIfBit`; `ifBit` looks inside), `tDepth`
as the number of `k < depth` such that some gate placed in layer `k + 1` is a T-power (a `countP`
over `List.range depth`, so depth × gates work for the kernel). Proved: `gradeExt_meas_eq_nBits`,
`gradeExt_tDepth_le_depth`, `gradeExt_tDepth_le_tCount`. Reviewer decision 2026-10-31: if
`gradeExt_eq` alone exceeds 30 s in the kernel for any certificate in 17b, the `tDepth` clause
changes to the deduplicated list of T-layer indices (linear in the T-count) and the three
theorems are re-proved; otherwise the definition stays.

`Synthesis.gradeExt C : GradeExt`; every certificate states `theorem gradeExt_eq :
Synthesis.gradeExt emitted = ⟨…⟩ := by decide +kernel` and records it as `grade_ext` `{two_qubit, t_depth, rot, meas, ff}` in the
JSON (schema 1.9.0, required in every certificate, present iff the version is 1.9.0; the run report
prints the five values in row 4 and, only when `rot > 0`, the note of §A.8.2 — reviewer decision
2026-10-31; 1.6.0 is Stage 14a's `solution_count`, 1.7.0 Stage 15b's `uncompute` on coherent certificates, 1.8.0 Stage 16b's proved front end with `uncompute` explicit in every certificate — renumbered 2026-10-30). The paper's "no two-qubit count, no T-depth" item is answered here; the
Clifford+T cost of `rot` gates is deliberately *not* folded into `t` (it depends on a synthesis
precision that is a hardware matter, §C).

**Emitters.** OpenQASM 3: `p(2*pi*a/N) q;` and `cp(2*pi*a/N) c, t;` with `N = 2^k` evaluated
to an integer (`^` is XOR in OpenQASM 3; amended 2026-10-31) and `a` printed as an integer, in
parentheses when negative (`p(2*pi*(-3)/32) x[0];`); both gates are in `stdgates.inc`; re-parse
validation unchanged in kind, exact on `(a, k)`. QIR: `p` as `__quantum__qis__rz__body(double θ,
ptr)` with θ = 2πa/2^k printed as an LLVM hex-float literal (`Float.toBits`; a decimal literal is
rejected by `llvm-as` unless exactly representable), the re-parse comparing θ with 2πa/2^k to
1e-12 (the global phase e^{−iθ/2} of `rz` against `p` is irrelevant to every statement in this
project — per branch under `ifBit` too — and the run report says so); `cp` has no intrinsic and is
emitted as the standard decomposition `p a (k+1) c; p a (k+1) t; cnot c t; p (-a) (k+1) t;
cnot c t` (θ/2 = 2πa/2^(k+1)), so the QIR re-parse is validated against `Circuit.decomposeCp C`
(top-level `cp` only; a `cp` under `ifBit` is refused by the QIR emitter with a diagnostic, the
Adaptive-Profile branch would need the five gates), with `decomposeCp_unitary (gs) (h : ∀ g ∈ gs,
g.cpOk n a = true) : unitaryDenote n a (decomposeCp gs) = unitaryDenote n a gs` proved once in
17a (this is the first entry of the decomposition table of §C.3). `Gate.cpOk n a`: every
top-level `cp` has distinct operands and its target inside the register `Reg n × Reg a`. The
hypothesis is necessary and was added at 17a (reviewer-accepted 2026-10-31): the semantics reads
a qubit outside the register as 0, so on an out-of-range target the five gates reduce to
`p a (k+1) c` while `cp` is the identity; the task text's `c ≠ t` alone was false, and its
`isUnitary` hypothesis was unnecessary (`unitaryDenote` reads every gate through `gateU`). 17b adds
the circuit-level form the QIR emitter cites, `decomposeCp_unitary_wf (C : Circuit) (h : C.WF) :
unitaryDenote C.nData C.nAnc (decomposeCp C.gates) = unitaryDenote C.nData C.nAnc C.gates`
(`cpOk` holds automatically: `qubitsOk` bounds the data indices and `nAnc` is one more than the
largest ancilla index). Gates no synthesized circuit contains are exercised through a fixed sample
circuit (`CertifyTool emit-sample`, Stage 17b).

**Harness.** `tests/diff/statevector.py` learns `{"op":"p","q":[i],"a":a,"k":k}` and `"cp"`.

**Stages.** 17a: IR, semantics, well-formedness, scheduler, `GradeExt`, `decomposeCp` (library;
no emitter, CLI, certificate or Python change) — **done b32b999, accepted 2026-10-31**, all
theorems proved, nothing tracked, `Grade` and every existing statement unchanged (checked by
script), the measured `GradeExt` (twoQ, tDepth, rot, meas, ff) of the four committed circuits
grover_pred_037 (126, 39, 0, 18, 36), simple_alu_x0_1 (137, 28, 0, 15, 30), grover_pred_037_few
(106, 77, 0, 8, 16), grover_pred_037_coh (216, 74, 0, 0, 0); until 17b the OpenQASM emitter writes
a `// cqrv: unsupported before Stage 17b` comment for `p` / `cp` and the QIR emitter its existing
`; unsupported gate` comment (no synthesized circuit contains them). 17b: emitters, re-parsers,
harness, `gradeExt_eq` in every certificate, schema 1.9.0, the four certificates regenerated, plus
`decomposeCp_unitary_wf` (docs/tasks/STAGE17_TASK.md, 2026-10-31). The coherent certificate's
`tDepth` 74 against the MBU 39 (the adjoint compute block repeats the T layers) is recorded in
the 17b DECISIONS entry, not in the run report. 17b **done 9fc909b, accepted 2026-10-31** (CI
16 PASS): everything above as specified; `decomposeCp` lives in `CQRV/Circuit/IR.lean` since
17b (the emitters do not import the semantics; its theorems stay in `Semantics.lean` and
`OracleCorrect.lean`); `emitQIR : Except Diagnostic String`, diagnostic stage `emit`, code
`unsupported_in_qir`; the `rz` declaration is written only when a `p` gate is emitted, so every
committed `.qir` stayed byte-identical; π enters `qirAngle` as the double `0x400921FB54442D18`
(the bits of `math.pi`), so the emitter and the re-parser compute the same `Float`. Kernel
medians 16b → 17b: 14.40 → 18.10, 16.70 → 16.90, 12.60 → 15.40, 25.40 → 33.50 s; `gradeExt_eq`
alone 9.26 / 7.03 / 7.95 / 17.5 s under the certificate's metric (cumulative kernel type checking
as the run reports state it — the reviewer's reading of the 30 s rule, 2026-10-31; the
profiler's per-declaration figure double-counts the `decide +kernel` evaluation and would show
31.7 s for the coherent file), so the `tDepth` definition stays. The chunked `emitted` literal
(the ~1953-instruction ceiling) is designed and tried at Stage 18 on the QFT / AQFT circuits.

### A.2 QFT and approximate QFT (new; the Theorem 3.3b client)

`qft m : List Gate` on data qubits `0..m−1`, the textbook circuit without the final swaps: for
`j = 0..m−1`: `h j`; for `k = 2..m−j`: `cp 1 k (j+k−1) j`. Theorem:

```
theorem qft_basis (m : Nat) (x : Fin (2^m)) :
    unitaryDenote m 0 (qft m) *ᵥ basisVec x =
      (2^m : ℂ)^(-1/2) • ∑ y : Fin (2^m), exp (2πi · x·y / 2^m) • basisVec (bitRev m y)
```

with `bitRev m` the bit-reversal permutation (the swaps are absorbed into the decoding map of
§A.4). `aqft m kmax` drops every `cp 1 k` with `k > kmax`.

Two bounds, the second being the one Theorem 3.3b consumes:

```
theorem diamondDist_unitary_le (U V : unitary) :
    diamondDist (CPTPMap.ofUnitary U) (CPTPMap.ofUnitary V) ≤ 2 * ‖U − V‖       -- operator norm
theorem aqft_opNorm_le (m kmax : Nat) :
    ‖unitaryDenote (qft m) − unitaryDenote (aqft m kmax)‖ ≤ 2π · m / 2^kmax
```

(`|e^{iφ} − 1| ≤ |φ|` per dropped gate and a telescoping sum over the product). Hence
`diamondDist (ofUnitary (qft m)) (ofUnitary (aqft m kmax)) ≤ 4π m / 2^kmax =: η_aqft m kmax`.
The adjoint circuits (inverse QFT) are `adjoint (qft m)`, `adjoint (aqft m kmax)` from §A.0.1.

**Amendments before Stage 18 (reviewer, 2026-10-31; docs/tasks/STAGE18_TASK.md).** (1)
*Encoding.* The basis index of `Reg m = Fin m → Bool` reads qubit 0 as the **most significant
bit**, as the harness does (`tests/diff/statevector.py`): `Reg.toNat s = ∑_j [s j] 2^(m−1−j)`;
`Reg.toNatLE` is the little-endian reading, `bitRev s = fun j => s (Fin.rev j)` and
`(bitRev s).toNat = s.toNatLE`; `Reg.ofNat m x = fun j => x.testBit (m−1−j)`. `Fin (2^m)` is not
used in the statements; `Reg m` is. (2) *Circuits.* `qftGates m = (List.range m).flatMap (qftBlock
m)` with `qftBlock m j = h (data j) :: [cp 1 (i+2) (data (j+i+1)) (data j) | i < m−j−1]` (the text
above, 0-based); `aqftGates m kmax = (qftGates m).filter (cp 1 k kept iff k ≤ kmax)`;
`qftCircuit m = ⟨m, qftGates m⟩`, `aqftCircuit`; `qftCircuit_WF`, `qftGates_unitary` proved.
Every `cp 1 k` with k ≥ 2 is a rotation of §A.1 (`GradeExt.rot = m(m−1)/2`, `t = 0`). (3) *The
theorem*, pointwise on the circuit's own register `Reg m × Reg 0` (`reg0` the unique element of
`Reg 0`; `basisVec` of `CQRV.Circuit.Restoration`), replaces the vector form above:

```
theorem qft_basis (m : ℕ) (x s : Reg m) :
    (unitaryDenote m 0 (qftGates m) *ᵥ basisVec (x, reg0)) (s, reg0) =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * ((x.toNat * (bitRev s).toNat : ℕ) : ℂ) / 2 ^ m)
```

(the amplitude of output state `s` is `2^{−m/2} e^{2πi · x · bitrev(s) / 2^m}`: the textbook
output without swaps). Proof by the block invariant (after blocks `0..j−1` the state is
`⊗_{i<j} (|0⟩ + e^{2πi φ_i}|1⟩)/√2 ⊗ |x_j … x_{m−1}⟩`, `φ_i = (x.toNat mod 2^{m−i}) / 2^{m−i}`) and
the arithmetic identity `exp_sum_phases` (the exponents differ by an integer); the task text
names the sub-lemmas. (4) *Norm.* `‖·‖` on matrices is the L2 operator norm in the instance
Physlib's `Matrix.traceNorm_mul_le_opNorm_traceNorm` uses (Mathlib `Matrix.l2_opNorm_*`).
`aqft_opNorm_le` is proved from `unitaryDenote_filter_sub_le` (telescoping over a filtered gate
list, unitaries of norm 1) and `gateU_cp_sub_one_le : ‖gateU (.cp 1 k c t) − 1‖ ≤ 2π/2^k`
(`Complex.norm_exp_I_mul_ofReal_sub_one_le`). (5) *Channels.* `channelDenote_of_unitary : C.WF →
C.gates.all isUnitary → channelDenote n a C = CPTPMap.ofUnitary ⟨unitaryDenote n a C.gates, _⟩`
(the bridge Stages 19–20 reuse); `diamondDist_ofUnitary_le (U V : 𝐔[d]) : diamondDist (ofUnitary
U) (ofUnitary V) ≤ 2‖U − V‖` through the two sub-lemmas `prod_id_ofUnitary ((ofUnitary U ⊗ᶜᵖ id)
ρ = ρ.uConj (unitary_kron U 1))` and `l2_opNorm_kronecker_one_le (‖A ⊗ₖ 1‖ ≤ ‖A‖)`, each a
tracked obligation if it resists; `eta_aqft m kmax := 4π m / 2^kmax`; the client statement is
`aqft_diamond_le : diamondDist (channelDenote m 0 (qftCircuit m)) (channelDenote m 0 (aqftCircuit
m kmax)) ≤ eta_aqft m kmax`. (6) *Stages.* 18a: the kernel-evaluation forms — the 14b ceiling is
re-attributed (the single error of `bench/scaling/out/rand_a64_r1_h/lean.log` is at `grade_eq`,
line 449, not `emitted_ok`, which passed on the 1953-gate literal), the scheduler state becomes a
cons list (`placed : List`, `schedule := ⟨placed.reverse⟩`, placement rule and every measured
value unchanged, three Stage 17a lemma statements adapted), a probe (`scripts/kernel_forms.sh`,
`docs/benchmarks/KERNEL_FORMS.md`: rand_a64 at r = 1, 2, 3, per declaration, with a memory
guard) and the `Nat m` diagnosis (report only); 18b: circuits, encodings, `qft_basis`, harness
`tests/diff/qft_diff.py` for m ≤ 6 with both AQFT bounds, CI step "QFT / AQFT" (pass mark 17
PASS); 18c: C1–C4 above. The Stage 19–20 certificate form (flat literal or compositional) is
decided at the 18a review from the probe. **18a done 5058ea4, accepted 2026-11-01** (CI 16 PASS
on the second run; the first hung in step 20 on the machine-detection `powershell` call, see
18b B0): no recursion error at any size after the cons-list state; the flat form is limited by
**memory**, about 750 instructions on the 16 GB machine (6.9 GB at 706, above 8 GB at 838); the
kernel cost is the scheduler's evaluation inside `grade_eq` / `gradeExt_eq` (about 90 %, slope
2.07 in the gate count); `Nat m` is not reproducible through `cqr certify` and is **closed**.
**Decided at the 18a review: the compositional certificate form of §A.3.**

### A.3 The counting circuit (extends report §8.2, §6.1.4)

Registers: `m` phase qubits `data 0..m−1`, `n` search qubits `data m..m+n−1`, ancillae.

**Controlled oracle without new gates.** For a one-output network `N` on `n` inputs and a control
input `c`, `Network.withControl N c` is the network on `m+n` inputs whose output is
`and (input c) (out N)` with `N`'s inputs renumbered to `m..m+n−1`. Its phase oracle is exactly
controlled-`O_P`, and Lemma 6.3.2 applies unchanged (`withControl_pred`). The synthesizer may
realize the final conjunction with an AND node (one more ancilla, 4 or 8 T) or, as an
optimization recorded in the decision log, by a `cz` between the two pivots in `phaseFlip`; either
is covered by the lemma.

**Controlled diffusion.** `H^{⊗n} X^{⊗n}` on the search register, the phase oracle of
`Network.withControl (treeNet n) c` (an MCZ on n+1 qubits), `X^{⊗n} H^{⊗n}`; the data layers are
uncontrolled because they are conjugated away when `c = 0` (`ancRestore_of_dataLayer`).

**Powers and the circuit.**

```
def controlledGrover (N : Network) (n m : Nat) (c : Nat) (mode) : Except Diagnostic Circuit
def countingCircuit (N : Network) (n m : Nat) (kmax : Option Nat) (mode) : Except Diagnostic Circuit
```

`countingCircuit` = `H` on the phase register; for `k = 0..m−1`, `2^k` copies of
`controlledGrover N n m k mode` (bits shifted by `Circuit.append`); `adjoint (qft m)` (or
`adjoint (aqft m kmax)`); the phase register is measured by the decoding POVM, not in the IR
(as the search register is for Grover). Theorem (`countingCircuit_ancRestore`): the circuit
restores its ancillae on every register at least as large as its own and applies
`U_count = (QFT†_m ⊗ I) · (∑_k |k⟩⟨k| ⊗ G^k) · (H^{⊗m} ⊗ I)` to the data register; proved from
`AncRestore.comp`/`ancRestore_foldl` over the controlled iterates, whose own restoration is
Lemma 6.3.2 for `withControl` networks plus the data-layer lemma.

**Certificate form (decided at the 18a review, 2026-11-01; docs/benchmarks/KERNEL_FORMS.md).**
The flat form of Stages 8–18 (`grade_eq` / `gradeExt_eq` by `decide +kernel` on the whole
`emitted` literal) is limited by memory to about 750 instructions on the 16 GB machine (Stage
18a: the kernel's evaluation of the scheduler, quadratic in the gate count; 6.9 GB at 706
instructions, above 8 GB at 838), while the committed counting certificate (`n = 8`, `m = 4`,
§A.8.3) has about 10 000 gates. Every certificate must check on a 16 GB machine with each Lean
process below 8 GB, whatever machine measures it. The counting certificates therefore use the
**compositional form**:

1. *Blocks.* `countingCircuit` is the `Circuit.append` of named blocks: the Hadamard layer, the
   controlled iterates `controlledGrover N n m k mode`, the inverse (A)QFT. Each **distinct**
   block is a literal in `Cert.lean` with its own hash link (`… = .ok block` by `decide +kernel`,
   as `emitted_ok` today) and its own exact `grade_eq` / `gradeExt_eq`. The `2^k` copies of
   iterate `k` are stated once. The generator refuses a block above 600 emitted instructions with
   a diagnostic; there is no flat fallback.
2. *Composition of the grade.* New general theorems (Stage 19a), under the hypotheses the task
   text fixes (the same data register; `C₁` frees every ancilla it allocates, which `WF` gives):
   `Circuit.grade (C₁.append C₂) ≤ Circuit.grade C₁ + Circuit.grade C₂`. This is ⊕ of report
   §3.1.1, Table 3.1: width and ancillae as maxima, depth and T-count added. The T-count is in
   fact additive; the depth is a bound, because the scheduler may overlap two blocks. The
   theorems also give the n-fold form `≤ n • Circuit.grade C` for `n` copies (the `AddCommMonoid
   Grade` instance, §3.1.4) and the `GradeExt` analogue: `twoQ`, `rot`, `meas`, `ff` additive
   (equalities), `tDepth` at most the sum. The whole circuit's grade in the certificate is the
   composed value `g`. It is **an upper bound in the budget order, not the measured grade**, and
   `certificate.json` and the run report say so: a field names the kind of grade, `measured` for
   every certificate before Stage 19 and `composed_bound` here; the schema bump belongs to Stage
   20b. The hardware check (`fits`) is made against `g`.
3. *Realization against the bound.* `Realizes … r` already reads the grade as a budget
   (`Φ.grade ≤ r`, `CQRV/Realizability/Realizes.lean`, report §3.1.2). The lemmas of §A.4 are
   therefore stated with the bound `g`, from `Synthesis.grade C ≤ g` by transitivity; `Realizes`
   does not change and no new realization lemma is needed.
4. *Unchanged.* The four committed certificates and every Phase 1 certificate keep the flat,
   measured form: all are below 600 instructions, and nothing is regenerated for this decision. A
   kernel-friendly evaluator proved equal to `Circuit.grade` (option (a) of KERNEL_FORMS.md) is
   **not scheduled**. It is reconsidered only if a block that must be measured exceeds 600
   instructions, or a block's `grade_eq` exceeds 30 s under the certificate's metric. A layer
   witness from an untrusted scheduler (option (c)) is rejected.

### A.4 The amplitude-estimation parametric lemma (extends report §8.2, §2.2)

**Eigenstructure.** With `ψ_g`, `ψ_b` and `θ` of `GroverParams` (`sin²θ = M/2ⁿ`), the vectors
`ψ_± = (ψ_g ∓ i ψ_b)/√2` satisfy `G ψ_± = e^{±2iθ} ψ_±` (from `reflection_geometry`), and
`ketS = (e^{iθ} ψ_+ + e^{−iθ} ψ_−)/√2` up to the convention fixed in the task file.

**The QPE lemma** (`qpe_two_phase_bound`), pure linear algebra on `Fin (2^m)`: for a unitary `G`
with an eigenvector `ψ` of eigenphase `φ ∈ [0,1)` (`G ψ = e^{2πiφ} ψ`), the measurement
distribution of the phase register after `U_count` on input `|0^m⟩ ⊗ ψ` is
`P_m(y; φ) = |2^{−m} ∑_{j<2^m} e^{2πi j (φ − y/2^m)}|²`, and
`∑_{y : ‖y/2^m − φ‖ ≤ 2^{−m}} P_m(y; φ) ≥ 8/π²` (‖·‖ the distance on the circle). On the
superposition of two eigenvectors the distribution is the equal mixture, and since
`sin²(π y/2^m)` is invariant under `y ↦ 2^m − y` both eigenphases `±θ/π` decode to the same
estimate.

**Specification and decoding.** The POVM outcome type must be finite (Physlib `POVM X d`), while
the ideal output `a = M/2ⁿ` is in general not an outcome. The output type is therefore
`Y_m := Fin (2^m) ⊕ Unit`, with the estimate `ã : Y_m → ℚ`, `ã (inl y) = sin²(π·bitRev y / 2^m)`
represented exactly as a rational by the Chebyshev route of `groverSuccess` where needed, and
`ã (inr ()) = a`; the metric on `Y_m` is the pseudo-metric induced by `ã`
(`PseudoMetricSpace.induced`). The specification is exact: `CountSpec a m : Spec Unit Y_m :=
fun _ y => y = inr ()`; its ε-relaxation is `{y : |ã y − a| ≤ ε}`, which is what the device can
produce. The decoding POVM `countPOVM m : POVM Y_m (Reg m)` is the computational-basis POVM on
`inl` and the zero operator on `inr ()` (allowed: positive semidefinite, sums to the identity).
If the induced-metric route proves awkward in Lean, the fallback is the specification that carries
the tolerance, `fun _ y => |ã y − a| ≤ ε`, with `RealizesExact`; the task file says which was used.

**Statement sketch.**

```
def ae_eps (a : ℝ) (m : Nat) : ℝ := 2π √(a(1−a)) / 2^m + π² / 4^m
def ae_delta : ℝ := 1 − 8/π²

theorem ae_parametric_lemma (gp : GroverParams) (m : Nat) (mode) (C) (hC : countingCircuit … = .ok C)
    (g : Grade) (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec (gp.M / 2^gp.n) m) (countPOVM m) (countingChannel gp.n m C)
      (ae_eps (gp.M/2^gp.n) m) ae_delta g
  ∧ AncRestore (m + gp.n) C.nAnc C U_count

theorem ae_parametric_lemma_aqft … (kmax) … (g) (hg : Synthesis.grade C ≤ g) :
    Realizes … (ae_eps …) (ae_delta + η_aqft m kmax / 2) g
```

(The grade argument is the composed bound of §A.3, as amended at the 18a review, 2026-11-01. With
`g := Synthesis.grade C` the statements are the measured ones.)

The second is `coherent_composition_diamond` applied with `Φ₁ = Φ₂` the controlled-powers block
(η_f = 0) and `Ψ₁, Ψ₂` the exact and approximate inverse QFT (η_g from §A.2): the first
certificate in which the diamond distance of Stage 13b appears. The `GroverParams` hypothesis
`hM_card` is still needed *in the lemma* (it fixes `a`); the point of the pattern is that the
certificate's *output* is an estimate of `M`, see §A.5. The estimate's error in `M` units is
`2ⁿ · ae_eps`, and the stretch goal §A.7 turns it into an exact `M` for `m` large enough.

### A.5 The second library entry, the request, decidability (report §4.1–4.2, §9.3.2, §7.2)

**Request.** `cqr certify f.cqr --problem count --precision m [--aqft kmax] [--uncompute coherent]`;
`--problem search` is the default and the Phase 1 behaviour. The DSL itself does not change (the
predicate is the same object); the problem class is a request parameter, as `--solutions` is.

**Signature and pattern.** The extractor's signature term gains the class constant `Count` and
the precision: `sig(Count, n, P, oracle, m)`. The library entry:

```
φ_Count = ⟨Count, n:F₁, P:Bool^{F₁}→Bool, oracle:PhaseKickback(Multiplicative, F₄), m:F₅⟩, F₅ ≥ 1
library := [groverEntry, countEntry]
```

The QPLP record of report §3.2 (`CQRV/Patterns/Basic.lean`, a placeholder today) is instantiated
for both entries: specification family, circuit family, grade function, precondition, and the
name of the parametric lemma. `groverInstance` (which rejects every entry but "Grover") becomes a
dispatch on the matched entry. Repair hints work across entries: a `Count` request on a program
with an unbounded loop gets the same `iter` hint as a search request.

**Proposition 5.1** (report §4.2.1, a committed Phase III deliverable): for the implemented
fragment — ground signature terms, patterns whose metavariables are applied to distinct bound
variables, AC sets normalized by sorting, side conditions decidable — (i) `millerMatch` is a
decision procedure: it returns `some σ` iff some `σ` with `φσ = t` exists (`millerMatch_complete`,
the converse of `millerMatch_sound`); (ii) the match set over the library is empty or a singleton
because distinct entries have distinct class constants (`library_match_unique`); (iii) a rejection
is therefore a proved non-match within the fragment, and the run report says "no entry matches
(proved)" instead of "no match found".

**Certificate and status.** The counting certificate states the two conjuncts of §A.4 at the
request's literals; its status line reads `certified (ε = …, δ = 1 − 8/π² [+ η/2]; conditional
on: solution_count = M)` — the hypothesis is still there, because the lemma is about the true `a`.
JSON: `"pattern": "Count"`, `"spec": {"epsilon": …, "delta": …, "precision": m, "aqft": kmax?}`.

### A.6 Certified selection under a budget (new; answers review R2.3)

`cqr certify … --budget w,d,t,a --prefer depth|width|t|anc` enumerates the admissible candidate
space — diffusion shape × uncomputation mode (× precision `m` for counting, within a range given
on the command line) — builds each candidate, computes its grade, discards those that do not fit,
and picks the minimum in the lexicographic order starting with the preferred component. The
certificate then contains, for every candidate `cᵢ`, `theorem grade_i : Synthesis.grade cᵢ = gᵢ
:= by decide +kernel`, and `theorem selected : chosen = argmin … := by decide` over the finite
list, so that the claim "no admissible candidate in this space is better in this order" is
kernel-checked. The candidate space is finite and stated in the certificate; the claim is about it
and nothing else.

### A.7 Stretch: measured composition exercised (report Theorem 3.3a)

Counting followed by search with the estimated `M` ("search with an unknown number of
solutions") composes at a measured interface: stage 1 outputs `ã`, stage 2 runs Grover with
`r*(ã)`. In the framework, stage 2 must be a graded channel on the encoding of the intermediate
value; a circuit whose iteration count depends on a classical input is not expressible in the IR
without classically controlled iteration, so the honest options are (a) a channel family indexed
by the intermediate outcome, with Theorem 3.3a generalized to that form, or (b) exercising
Theorem 3.3a on two certified toy stages, as the report's own validation gate did for 3.3b. The
M3 review decides; the obstacle is recorded either way.

### A.8 Design choices (decided 2026-10-29) and what the task files still fix

1. Output type and metric: `Y_m = Fin (2^m) ⊕ Unit` with the metric induced by `ã` (§A.4) is the
   primary route; the tolerance-carrying specification is the fallback, used only if the Stage 20b
   implementer reports the induced metric as an obstacle.
2. `rot` gates carry no T-estimate in the grade or the certificate. The run report prints the
   rotation count and, when it is positive, the note "Clifford+T cost depends on the synthesis
   precision (see §C)" (amended 2026-10-31); a
   Ross–Selinger estimate, if ever given, is a hardware-profile matter.
3. Precision of the committed counting certificate: `n = 8, M = 32`, `m = 4` (15 controlled
   iterates); the harness also runs `m = 6`. The exact `ε` at `m = 4` is
   `2π·√(7/64)/16 + π²/256`, stated as a real in the certificate as `δ` is today.
4. Still fixed in the task files: the convention for `ψ_±` and the sign of the eigenphase
   (Stage 20a); whether the controlled oracle's final conjunction is an AND node or a `cz` on the
   pivots (Stage 19, decision log).
5. Certificate form of the counting certificates: compositional (§A.3), with blocks of at most 600
   instructions measured exactly and the whole grade a ⊕ bound labelled `composed_bound`. Every
   Lean process stays below 8 GB on the 16 GB machine (decided at the 18a review, 2026-11-01).
