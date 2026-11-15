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
(`Real.norm_exp_I_mul_ofReal_sub_one_le`; the name was `Complex.…` here before the 18c review,
which does not exist in the pinned Mathlib). (5) *Channels.* `channelDenote_of_unitary : C.WF →
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
**Decided at the 18a review: the compositional certificate form of §A.3.** **18b done 3ec8377,
accepted 2026-11-01** (CI 17 PASS, 0 FAIL, 4 n/a on the second run; the first failed in
`certify_check.py` on a `→` printed to a cp1252 stdout, after every B0 assertion had passed):
(1)–(3) as stated, `qft_basis` proved with no `sorry` (axioms `propext`, `Classical.choice`,
`Quot.sound`), `gateU_h_mulVec` / `gateU_cp_mulVec` unchanged; measured `qftCircuit m` grade
`(m, 2m−1, 0, 0)` and `GradeExt (m(m−1)/2, 0, m(m−1)/2, 0, 0)` for m = 1..8; the harness for
m ≤ 6 confirms `U_qft = R·F` and both AQFT bounds (m = 6, kmax = 3: `‖U_qft − U_aqft‖₂` = 1.482
≤ Σ_dropped = 1.669 ≤ 2πm/2^kmax = 4.712; the dropped-angle sum is attained to three digits at
kmax = m − 1). `qftCircuit_WF` / `qftGates_unitary` are in `CQRV/Circuit/QFTCorrect.lean`, not in
`CQRV/Synthesis/QFT.lean` (accepted at the 18b review, §A.8 item 6). **18c done 65caea8,
accepted 2026-11-01** (CI 17 PASS, 0 FAIL, 4 n/a): (4)–(5) as stated, everything proved — the two
sub-lemmas `prod_id_ofUnitary` (through Physlib's `MatrixMap.conj_kron`) and
`l2_opNorm_kronecker_one_le` included — with axioms `propext`, `Classical.choice`, `Quot.sound`;
`channelDenote_of_unitary` is in `CQRV/Circuit/UnitaryChannel.lean`; `aqft_adjoint_diamond_le`
gives the same bound for the inverse circuits. Numerically, `η_aqft` is informative (below 2 with
a gate dropped) only from m = 7 on: m = 7, kmax = 6: `2‖U_qft − U_aqft‖₂` = 0.098 ≤ 1.374;
m = 8, kmax = 6 and 7: 0.245 ≤ 1.571 and 0.049 ≤ 0.785 (harness `--m-max 8`, outside CI). **Stage
18 complete.**

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
§A.8.3) has 3 682 gates in MBU mode and 5 167 in coherent mode (measured at Stage 19b; the
estimate here was about 10 000). Every certificate must check on a 16 GB machine with each Lean
process below 8 GB, whatever machine measures it. The counting certificates therefore use the
**compositional form**:

1. *Blocks.* `countingCircuit` is the `Circuit.append` of named blocks: the Hadamard layer, the
   controlled iterates `controlledGrover N n m k mode`, the inverse (A)QFT. Each **distinct**
   block is a literal in `Cert.lean` with its own hash link (`… = .ok block` by `decide +kernel`,
   as `emitted_ok` today) and its own exact `grade_eq` / `gradeExt_eq`. The `2^k` copies of
   iterate `k` are stated once. The generator refuses a block above 600 emitted instructions with
   a diagnostic; there is no flat fallback.
2. *Composition of the grade.* New general theorems (Stage 19a), under the hypotheses the task
   text fixes (the same data register; `C₁` ends with no live ancilla — `WF` does not check
   `alloc` / `free`, so this is a hypothesis of its own; amended before Stage 19, see below):
   `Circuit.grade (C₁.append C₂) ≤ Circuit.grade C₁ + Circuit.grade C₂`. This is ⊕ of report
   §3.1.1, Table 3.1: width and ancillae as maxima, depth and T-count added. The T-count is in
   fact additive; the depth is a bound, because the scheduler may overlap two blocks. The
   theorems also give the n-fold form `≤ n • Circuit.grade C` for `n` copies (the `AddCommMonoid
   Grade` instance, §3.1.4) and the `GradeExt` analogue: `twoQ`, `rot`, `meas`, `ff` additive
   (equalities), `tDepth` at most `tDepth C₁ + tCount C₂` (not the sum of the two T-depths,
   which is false for the ASAP scheduler; amended before Stage 19, see below). The whole
   circuit's grade in the certificate is the
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

**Amendments before Stage 19 (reviewer, 2026-11-01; docs/tasks/STAGE19_TASK.md).** They replace
the register layout, the renumbering and the formula for `U_count` above.

(1) *Register layout.* The search register is `data 0..n−1`, as in every Grover builder
(`Diffusion.onAll`, `treeNet`, `synthesizeOracle`, Lemma 6.3.2, all hard-wired to `data 0..`).
The phase register is `data n..n+m−1`: phase qubit `j` is `data (n+j)`. Only the unitary,
data-only blocks that touch the phase register are shifted, by a new `Gate.shiftData`: the
initial Hadamard layer and the inverse (A)QFT. `Network.withControl N m j` keeps `N`'s input
numbering, has `n + m` inputs, and its output is `and (input (n+j)) (out N)`.

(2) *The phase fix.* The circuit's diffusion is `−U_s`: `diffusion_circuit_matrix`, decision 5,
a global phase in Grover. Under a control the sign becomes a relative phase. The controlled
diffusion applies `ctrl_j(−U_s)`, and without a correction the block would apply `ctrl_j(−G)`:
the eigenphases `±θ/π` move to `1/2 ± θ/π` and the decoding reads `1 − a`. `controlledGrover`
therefore ends with `z (data (n+j))`, so that each block applies exactly `ctrl_j(G)`, with
`G = groverOp P = U_s U_P`. The global-phase lemma `AncRestore.congr` is never used inside a
controlled block.

(3) *Conjunction.* The controlled oracle's final conjunction is the AND node of `withControl`,
which Lemma 6.3.2 covers unchanged. The `cz`-on-pivots optimization is not scheduled (§A.8
item 4 resolved).

(4) *The circuit.* `countingCircuit` consists of three parts, joined by `Circuit.append`:
- `H` on all `n + m` data qubits (`Diffusion.onAll .h (n+m)`), which prepares `|s⟩` on the
  search register as `groverCircuit` does;
- for `j = 0..m−1`, `2^j` copies of `controlledGrover N n m j mode`;
- the inverse (A)QFT `(adjointGates (qftGates m)).map (Gate.shiftData n)`, or the same with
  `aqftGates m kmax`.

Shapes `tree` and `chain` go through `synthesizeOracle`. The few-ancilla MCZ and Bennett budgets
are refused (`unsupported_combination`).

(5) *The unitary.* With `phase x : Reg m` and `search x : Reg n` the restrictions of
`x : Reg (n+m)`, and `k(x) = (phase x).toNatLE`, so that phase qubit `j` has weight `2^j`:
```
countingCircuit_ancRestore : AncRestore (n+m) C.nAnc C U_count,
U_count = liftP (QFT†_m) · ctrlPow G · H^{⊗(n+m)},
(ctrlPow G) x y = [phase x = phase y] · (G ^ k(x)) (search x) (search y).
```
After `QFT† = (R·F)†` the amplitude of phase outcome `y` (read with `data n` as the MSB,
`(phase x).toNat`) on an eigenvector of phase `φ` is `2^{−m} ∑_{j<2^m} e^{2πi j (φ − y/2^m)}`.
The estimate is therefore `y/2^m` directly, with **no `bitRev`**; §A.4 is amended to match. The
Stage 19b harness checks this numerically. If it shows another convention, the stage stops.

(6) *Grade composition.* Two corrections to item 2:
- **Width and ancillae.** `peakAncilla` counts live ancillae in program order, so for
  `C₁.append C₂` it is `max` of the two exactly when `C₁` ends with no live ancilla
  (`liveEnd C₁ = 0`, a new definition).
- **T-depth.** The sum of the two T-depths is **not** a bound. A T gate of `C₂` on a qubit
  that `C₁` keeps busy is delayed, while a T gate on an idle qubit is not, so two T gates in
  one layer of `C₂` can land in two layers. The bound is `tDepth (C₁.append C₂) ≤ tDepth C₁ +
  tCount C₂`.

The depth bound `depth (C₁.append C₂) ≤ depth C₁ + depth C₂` needs no hypothesis.

**19a done 2ec7298, accepted 2026-11-01** (CI 17 PASS, 0 FAIL, 4 n/a). Everything in (6) and
item 2 as amended is proved with no `sorry`, in the Physlib-free `CQRV/Circuit/GradeCompose.lean`:
`liveEnd`, `grade_append_le`, `grade_foldl_append_le`, `grade_replicate_le`, `depth_append_le`
(through the scheduler invariant `SchedState.Dom`), the `GradeExt` equalities and
`tDepth_append_le`. The counterexample is in the tests. On grover_pred_037 the iteration's
measured grade `(15, 68, 36, 7)` equals oracle ⊕ diffusion. At r = 2 the measured grade is
`(15, 134, 72, 7)` and the composed bound is `(15, 137, 72, 7)`: the scheduler overlaps the
blocks by three layers, and width, T-count and ancillae are exact. The `oracle_plus_diffusion`
grade of `cqr synthesize --grover` is now a proved bound.

**19b done 35ea970, accepted 2026-11-05** (CI 18 PASS, 0 FAIL, 4 n/a). The builders are
`CQRV/Synthesis/Counting.lean` (Physlib-free, in the `cqr` closure) and the restoration
`countingCircuit_ancRestore_raw` is in `CQRV/Circuit/CountingCorrect.lean`, in the circuit's own
factors, with no `sorry`. **The convention of (5) is confirmed numerically:** the phase-register
distribution equals `½ (P_m(y; θ/π) + P_m(y; −θ/π))`, read with `data n` as the MSB, to 2·10⁻¹⁴
(six predicates with M = 0, 1, 5, 8, 9, 16; m = 1..4). Without the phase fix of (2) it is the
mixture at `½ ± θ/π` to the same accuracy, and the bit-reversed reading fails whenever M ≠ 0. The
block probe (`docs/benchmarks/COUNTING_BLOCKS.md`) on grover_pred_037, m = 4:

| | MBU | coherent |
|---|---|---|
| gates per controlled iterate | 244 | 343 |
| `grade_eq` per block | 1.4 s | 2.9 s |
| kernel, whole probe file | 14.7 s | 29.5 s |
| peak memory | 2.5 GB | 3.2 GB |
| gates, whole circuit | 3 682 | 5 167 |
| measured depth ≤ composed | 1352 ≤ 1388 | 2040 ≤ 2048 |
| measured `tDepth` ≤ composed | 402 ≤ 660 | 733 ≤ 1320 |

Width, T-count and ancillae of the composed bound are exact in both modes. Item 4's condition for
reopening the kernel-friendly evaluator is not met. In MBU mode the compositional form checks a
circuit about five times the size at which the flat form stops (about 750 instructions), at
under a third of the 8 GB limit.

**19c done 47ab45d, accepted 2026-11-05** (CI 18 PASS, 0 FAIL, 4 n/a). `countingCircuit_ancRestore`
and `U_count` of (5) are proved in `CQRV/Circuit/CountingCorrect.lean`, with no `sorry` and nothing
tracked: the shift lemma `dataMat_shiftData` and the product `powersU_val` are proved too. The
matrices of (5) are functions on matrices, block diagonal along `Reg (n+m) ≃ Reg n × Reg m`
(`blockD`, Mathlib's `Matrix.blockDiagonal`, `blockD_eq_submatrix`), and the control of `ctrlU j`
is a natural number read through `Reg.bit`. The phase fix of (2) is now a theorem:
`cdiffU_val : cdiffU j = ctrlU j (−U_s)` and `cgU_val : cgU j = ctrlU j G`. `raw_eq_U_count` is an
equality of unitaries, so no global-phase argument enters. In the definition of `U_count` the
inverse QFT is written `star (dataMat m (inverseGates m kmax))`, where `inverseGates` is the
forward list (`qftGates m` or `aqftGates m k`). **Stage 19 complete.**

### A.4 The amplitude-estimation parametric lemma (extends report §8.2, §2.2)

**Eigenstructure.** With `ψ_g`, `ψ_b` and `θ` of `GroverParams` (`sin²θ = M/2ⁿ`), the vectors
`ψ_± = (ψ_g ± i ψ_b)/√2` satisfy `G ψ_± = e^{±2iθ} ψ_±` (from `reflection_geometry`), and
`ketS = (−i e^{iθ} ψ_+ + i e^{−iθ} ψ_−)/√2`. (Labels and coefficient corrected before Stage 20a.
This paragraph explains the two phases; the proof does not use the vectors, see the amendments
below.)

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
`Y_m := Fin (2^m) ⊕ Unit`, with the estimate `ã : Y_m → ℚ`, `ã (inl y) = sin²(π y / 2^m)`, where
`y` is the phase register read with `data n` as the MSB. There is no `bitRev`: the inverse QFT
of the circuit undoes the bit reversal of `qftGates` (amended before Stage 19, §A.3 (5)). The value is
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

**Amendments before Stage 20a (reviewer, 2026-11-05; docs/tasks/STAGE20A_TASK.md).** They replace
the statement of "The QPE lemma" above. The rest of this section stands.

(1) *No eigenvectors in the proof.* `iteration_induction` already gives `G^k ketS = sin((2k+1)θ)
ψ_g + cos((2k+1)θ) ψ_b`, and writing sine and cosine as exponentials produces the two phases
`±θ/π` directly. The case `M = 2ⁿ`, where `ψ_b = 0` and `ψ_±` are not unit vectors, needs no
separate eigenstructure. A QPE lemma for an arbitrary unitary and eigenvector is not proved: no
client needs it in Phase 2. It can be added when the library has a second QPE-based pattern.

(2) *The amplitude.* With `U_count` of §A.3 (5), for `x : Reg (n+m)`, `y = (phase x).toNat`:
```
(U_count P m none *ᵥ |0…0⟩) x =
  2^{−m} ∑_{k<2^m} e^{−2πi y k / 2^m} (G^k ketS)(search x).
```

(3) *The distribution.* `qpeAmp m δ = 2^{−m} ∑_{k<2^m} e^{2πi k δ}`, `qpeProb m φ y = |qpeAmp m
(φ − y/2^m)|²`, and `phaseDist gp m y = ∑_{s : Reg n} |(U_count … *ᵥ |0…0⟩) (s, y)|²`. For every
`GroverData` (so `M ≥ 1`, including `M = 2ⁿ`):
```
phaseDist gp m y = ½ (qpeProb m (θ/π) y.toNat + qpeProb m (−θ/π) y.toNat).
```

(4) *The bound.* `CircleNear m φ y := ∃ z : ℤ, |y/2^m − φ − z| ≤ 2^{−m}`, which is `‖y/2^m − φ‖ ≤
2^{−m}` on the circle without a new distance. For `m ≥ 1`:
```
qpe_two_phase_bound : 8/π² ≤ ∑_{y : near θ/π or near −θ/π} phaseDist gp m y,
qpe_success         : 8/π² ≤ ∑_{y : |sin²(π y/2^m) − a| ≤ ae_eps a m} phaseDist gp m y,
```
with `a = M/2ⁿ`. The two neighbours `⌊2^m φ⌋` and `⌊2^m φ⌋ + 1` carry the bound. It reduces to
`8 ≤ sin²(πt) (1/t² + 1/(1−t)²)` for `0 < t < 1`; equality holds at `t = ½`. The `|ã − a|` bound is
`|sin²(θ+Δ) − sin²θ| ≤ |sin 2θ| |Δ| + Δ²` with `|Δ| ≤ π/2^m`, and it is the same for both signs of
`θ`. Stage 20b works from `qpe_success`.

**20a1 done 19b575d, accepted 2026-11-05** (CI 18 PASS, 0 FAIL, 4 n/a). The analysis of (3)–(4) is
proved in `CQRV/Grover/QPEBound.lean` with no `sorry`, and its import closure is Mathlib only. It
contains `two_point_bound` (on `(0, ¼]` by concavity of `sin`; on `[¼, ½]` by the cosine bound
with `π < 3.15` and a polynomial inequality), `qpeProb_two_neighbours`, `CircleNear`,
`qpe_near_sum_ge` and `decode_close`. The outcome is an integer (`y : ℤ`), so periodicity is a
lemma. On the harness grid the minimum of the two-point inequality is exactly 8, at `t = ½`, and
`ae_eps` is almost tight (largest error / `ae_eps` 0.99995).

**20a2 done 6d5d195, accepted 2026-11-10** (CI 18 PASS, 0 FAIL, 4 n/a). (2)–(4) are proved in
`CQRV/Grover/Counting.lean` with no `sorry`: `U_count_zero_apply`, `phaseDist_eq` for every
`GroverData` (at `M = 2ⁿ` through `ampB = 0`, with no hypothesis `M < 2ⁿ`), `qpe_two_phase_bound`
and `qpe_success`. Two expected steps were not needed: the split of the Hadamard layer (the
existing `hadamardMat_mulVec_zero` gives the constant `ketS (n+m)`) and any eigenvector. On the
counting circuits of the harness (n = 4, 6; M = 1, 5, 8, 9, 16; m = 1..4) both sets carry more
than `8/π²`, the smallest margin being +0.049. Notes for Stage 20b:
- `qpe_success` filters `Finset.univ : Finset (Reg m)` under `open Classical in`; the decoding is
  `sin²(π y.toNat / 2^m)`, with no `bitRev`.
- `phaseDist` is defined for `kmax = none` only. The AQFT variant goes through Theorem 3.3b.
- The plane lemma to cite is `GroverData.iteration_induction`.

**Stage 20a complete** (912 lines of library Lean over 20a1 and 20a2).

**Amendments before Stage 20b (reviewer, 2026-11-10; docs/tasks/STAGE20B_TASK.md).** They replace
the output type, the decoding POVM and the channel of "Specification and decoding" and of the
statement sketch above. The induced-metric route of §A.8 item 1 stays the primary one.

(1) *Output type and metric.* `CountOut m a := Reg m ⊕ Unit`, carrying the pseudo-metric induced
by `countEst m a`, where `countEst (inl y) = sin²(π y.toNat / 2^m)` and `countEst (inr ()) = a`.
The estimate is **real-valued**, not rational: `sin²(π y/2^m)` is in general irrational
(`sin²(π/8) = (2 − √2)/4`), so the Chebyshev route of `groverSuccess` does not apply. `Reg m` is used
in place of `Fin (2^m)`: the whole development is indexed by `Reg`. The metric depends on `a`, so
`a` is a parameter of the type. The specification is `CountSpec m a : Spec Unit (CountOut m a) :=
fun _ y => y = inr ()`, and `relax ε` holds exactly when `|countEst y − a| ≤ ε`.

(2) *Decoding and channel.* The POVM acts on the whole data register: `countPOVM n m a : POVM
(CountOut m a) (Reg (n+m))` sends `inl y` to the projector onto "phase = y" (summed over the search
register) and `inr ()` to `0`. The channel is `groverChannel (n+m) C`: prepare `|0…0⟩`, run
`channelDenote`, trace out the ancillae. The search register is never traced, and the probability
of `inl y` is `phaseDist gp m y` (20a2).

(3) *Composition with a pseudo-metric.* `coherent_composition` and `coherent_composition_diamond`
state `[MetricSpace Z]`, but their proofs use only the pseudo-metric that `relax` needs. Stage 20b
adds `coherent_composition_pseudo` and `coherent_composition_diamond_pseudo` with
`[PseudoMetricSpace Z]` and the same proofs. The existing statements stay as they are.

(4) *The AQFT variant.* `countingCircuit` is `body.append (countingInverse n m kmax)` (19b,
`countingCircuit_ok`). `body` does not depend on `kmax`, and the inverse block is data-only, so the
exact and the approximate circuits have the same ancilla register. With `Φ` the channel of
`body` (preparation included) and `Ψ_k = traceRight ∘ channelDenote (countingInverse n m k)`:
- `diamondDist Φ Φ = 0`, so `η_f = 0`;
- `diamondDist Ψ_exact Ψ_aqft ≤ 2 ‖U_exact − U_aqft‖ ≤ η_aqft m kmax`, by
  `diamondDist_compose_le`, `channelDenote_of_unitary`, `diamondDist_ofUnitary_le`, `qftInvU_val`,
  a reindexing-invariance lemma for the L2 operator norm (which gives `‖liftP B‖ ≤ ‖B‖` and
  `‖A ⊗ₖ 1_{Reg 0}‖ = ‖A‖`), and `aqft_opNorm_le`.

Then `δ = ae_delta + η_aqft m kmax / 2`, with `ae_delta = 1 − 8/π²`. For m ≤ 6 the bound is
vacuous (`η_aqft ≥ 2`; Stage 18c notes), but the statement holds for every `m` and `kmax`.

(5) *The certificate* (n = 8, M = 32, m = 4; compositional; grade labelled `composed_bound`; schema
bump) is the third task of Stage 20b. Its task text is written after the realization lemmas are
accepted, because it builds on their final form.

**20b1 done fa95373, accepted 2026-11-10** (CI 18 PASS, 0 FAIL, 4 n/a). (1)–(2) are proved in
`CQRV/Grover/AmplitudeEstimation.lean` with no `sorry`: `CountOut`, `countEst`, `CountSpec`,
`countPOVM` (through `phaseProj`), `countPOVM_measure` (`= phaseDist`), `ae_realizes` and
`ae_parametric_lemma`. The induced pseudo-metric worked in Lean, so the fallback of §A.8 item 1 is
not needed. A point `inr ()` of `CountOut` has to be written `(Sum.inr () : CountOut m a)`: the
lemmas about `CountOut` are applied as terms, because `rw` does not see through the type synonym.

**20b2 done 4300cf2, accepted 2026-11-10** (CI 18 PASS, 0 FAIL, 4 n/a; the step "Counting circuit"
now takes 136 s, accepted). (3)–(4) are proved with no `sorry`:
- `coherent_composition_pseudo` and `coherent_composition_diamond_pseudo` (the existing statements
  are kept);
- `l2_opNorm_submatrix_equiv`, which is not in Mathlib;
- `inverse_diamond_le` (`≤ eta_aqft m kmax`, by the unitary route);
- `ae_parametric_lemma_aqft`, with `η_f = 0`.

The factorization of the channel works because the inverse block has no ancilla
(`countingInverse_nAnc`). This is the first statement in which the diamond distance enters a
realization of the counting pattern.

On the harness (all_four, n = 4, M = 1, coherent mode) the realized probability is 0.876 at m = 5
and 0.974 at m = 6 against `8/π²`. The AQFT variants at m = 6 give 0.955 (kmax = 4) and 0.972
(kmax = 5), at total-variation distance 0.021 and 0.003 from the exact circuit, while the lemma's
bound `8/π² − η_aqft/2` is vacuous there (−1.55 and −0.37). The proved AQFT bound is far from the
measured loss in this range: report it as such, not as a tight bound.

`ae_parametric_lemma_aqft` has no restoration conjunct; `countingCircuit_ancRestore` gives it with
`U_count gp.P m (some kmax)`.

**Amendments before Stage 20b3 (reviewer, 2026-11-10; docs/tasks/STAGE20B_TASK.md, section
20b3).** They fix the counting certificate. Amendment (5) above said its text would come here.

(1) *A separate generator.* The Grover pipeline is Grover-only, and it stays unchanged:
- `groverInstance` refuses every other pattern;
- `Certificate.build` requires `C.nData = n` and a measured grade;
- the schema closes `instance` to `{n, M, r}` and fixes `epsilon = "0"`.

The counting certificate gets its own Physlib-free generator `CQRV/Certify/CountCert.lean` (its
own request record, renderer, JSON record and run report), called by a new `CertifyTool`
subcommand. The `cqr` executable is unchanged; Stage 21 wires the same functions to
`cqr certify --problem count`.

(2) *Cert.lean in the compositional form.* There is no flat literal. It contains:
- the six distinct blocks (`h_layer`, `cg_0`–`cg_3`, `inverse`) as literals, each with its link to
  the builder and its `grade_eq` / `gradeExt_eq` by `decide +kernel` (the Stage 19b probe form);
- `emitted := assembleCounting h_layer [cg_0, …] inverse`, a library definition;
- `emitted_ok : countingCircuit net 8 4 none .tree .mbu = .ok emitted` by the library theorem
  `countingCircuit_of_blocks` and the four block links, so no kernel evaluation of the whole
  circuit;
- the composed grade `grade_le : Synthesis.grade emitted ≤ g` by a library lemma
  (`grade_assembleCounting_le`) over the block grades, with each block's `liveEnd = 0` decided.

(3) *The statement is universal in M.* The circuit does not depend on M, and neither does `g`:
```
cert : ∀ M, (univ.filter (net.pred 8 · = true)).card = M → 1 ≤ M →
  Realizes (CountSpec 4 (M/2^8)) (countPOVM 8 4 (M/2^8)) (groverChannel 12 emitted)
    (ae_eps (M/2^8) 4) ae_delta g ∧ AncRestore 12 emitted.nAnc emitted (U_count (net.pred 8) 4 none)
```
"For whatever the true solution count is, the output estimates it." It needs no count and is the
statement a counting application can use. The kernel-decided instance at M = 32 is a corollary,
`cert_count`, kept for the comparison with the Grover certificate of the same predicate. For
M = 0 the certificate makes no claim (`GroverData.hM_pos`), and it says so.

(4) *ε and δ are real.* `ε = 2π√(7/64)/16 + π²/256 ≈ 0.1684` and `δ = 1 − 8/π² ≈ 0.1894`. The JSON
gives each as an expression string and a decimal marked approximate, never as a rational. In M
units the guarantee at m = 4 is M within about ±43 with probability ≥ 8/π², and the decoding set
`{0, 1, 2, 14, 15}` contains the estimate 0. This is the weak instance §A.8 item 3 chose for
size. The run report states it, and states that the precision grows with m.

(5) *Schema 1.10.0.* A `pattern: "Count"` branch is added to `docs/certificate.schema.json`:
- `instance {n, M, m, kmax}`, `spec.epsilon` / `spec.delta` as `{expr, approx}`;
- `grade_kind: "composed_bound"`, with `grade_ext.t_depth` a bound;
- `blocks` (name, gates, multiplicity, grade, grade_ext, live_end).

The four committed Grover certificates stay at ≤ 1.9.0 and validate unchanged, so none is
regenerated. They move to 1.10.0 with `grade_kind: "measured"` in Stage 21, when the CLI changes.

(6) *No AQFT certificate at m = 4.* `δ + η_aqft/2 ≥ 1` there, so it would certify nothing. The
diamond distance enters a counting realization as the proved lemma `ae_parametric_lemma_aqft`. A
certified AQFT instance waits for a size where `η_aqft < 2`, which needs m ≥ 7.

**20b3 done ba9bb6c, accepted 2026-11-13** (CI 18 PASS, 0 FAIL, 4 n/a; the step "cqr certify" now
takes 632 s, 467 s before, accepted). **Stage 20b is complete, and with it Stage 20.**
(1)–(6) hold as written, with no `sorry`:
- the six blocks are 244 gates or fewer, and each `grade_eq` takes about 1.5 s;
- the composed bound is the probe's (20, 1388, 660, 8), and `grade_ext` is (1161, ≤ 660, 6, 165,
  330);
- the kernel check of `Cert.lean` takes 18 s kernel and 29 s wall, at 2.6 GB;
- the axioms of `front_end`, `cert` and `cert_count` are the standard three;
- the four Grover certificates are byte-identical at 1.9.0;
- the `cqr` closure is still Lean core + Mathlib (48 modules, `CountCert` included).

Two deviations from the task text are accepted:
- `cert` is proved through `ae_parametric_lemma_mk`, the 20b1 lemma stated over the fields
  `n, M, P, hcard` instead of the `GroverData` record. With the record, the elaborator unfolds
  `Network.pred` before it reduces the projection, about 2.5 s per occurrence, which exceeds the
  heartbeat limit of a generated file. No statement changed.
- The C1 lambdas use the projections `p.1`, `p.2` in place of `fun (b, j) =>`. A pattern-matching
  lambda elaborates to its own matcher at each occurrence, and `rw` does not identify them.

*For Stage 21* (wiring `cqr certify --problem count`):
- Call `CountRequest.ofProgram`, `renderCountCert`, `CountCertificate.ofRequest` and
  `CountRunData`, in the order `count-certify` uses them, and `ae_parametric_lemma_mk`.
- Refuse `M = 0` up front with a diagnostic. Today the generator writes `Cert.lean` and fails at
  `cert_count` in the kernel check (exit 1, no JSON). That is safe, but the error comes late.
- Add a `--count-limit` policy. The counting certificate always decides the count in the kernel.
- The hardware object and `--profile` are not written for Count.
- Move the Grover certificates to 1.10.0 with `grade_kind: "measured"` (amendment (5)). Then
  reword the schema's top-level description of `grade` ("Measured grade"), which the Count branch
  uses for a composed bound.

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

**Amendments before Stage 21 (reviewer, 2026-11-13; docs/tasks/STAGE21_TASK.md).** They replace
the parts of this section that they name. Amendment (8), on selection, is in §A.6.

(1) *The split.* The main stage is **21a**, in four commits:
- 21a1: the request and the Count entry;
- 21a2: Proposition 5.1;
- 21a3: the QPLP record and `cqr certify --problem count`;
- 21a4: certified selection.

21a1 and 21a2 are specified in the task text. 21a3 and 21a4 have outlines there and get their
detailed text at the review of the task before them. The stretch **21b** (§A.7) is unchanged.

(2) *The Count signature term has seven fields:* `sig(Count, n, M, P, iter, oracle, m)`. The
search term keeps its six fields `sig(class, n, M, P, iter, oracle)`, so every search output is
unchanged; `sigFields` gains `"m"`. The entry:

```
φ_Count = ⟨Count, n: F₁, M: F₆, P: Bool^F₁ → Bool, iter: bounded(F₃),
           oracle: PhaseKickback(Multiplicative, F₄), m: F₅⟩,   F₅ ≥ 1
```

- **F₆ has sort `any`.** The counting certificate is universal in M (§A.4, amendments before
  Stage 20b3 (3)), so the entry does not constrain the count: `unknown` matches.
- **The `iter` field is part of φ_Count.** The sketch above omitted it, but the cross-entry iter
  hint needs it.
- **The two entries never match the same term.** They differ in the class constant and in the
  argument count.
- **Corrected at the 21a1 stop (2026-11-13).** This draft first said that a search request's
  nearest miss stays Grover and a Count request's stays Count. That was false under Algorithm 2 as
  written. A root clash counts as one gap, so a search term with two gaps had Count as its nearest
  miss: `search_while` without `--solutions`, where Grover's gaps are M and iter. The implementer
  found this.

  **The fix (21a1).** `matchLibrary` takes the nearest miss only among the entries whose
  precondition has the term's root shape: the same head and the same argument count, not the class
  constant. When no entry has it, the choice falls back to all entries. So every six-field term has
  Grover as its only candidate, and the search and decision outputs are those of Stage 4 by
  construction. A Count term has Count as its only candidate. The early exit on a match is
  unchanged, and so is the statement of Proposition 5.1, which is about matched and non-matched,
  not about which miss is reported.

(3) *The class and the precision come from the request.*
- `ProblemClass` gains `count`, and `SigmaIn` gains `precision : Option Nat := none`; the
  extractor ℰ is unchanged.
- `SigmaIn.withProblem (.count m)` sets the class to Count and the precision to m, whatever ℰ
  found. A program that is not a predicate then fails at the `P` field with a hint.
- `--solutions M` keeps its meaning under both problems.
- `--aqft` is not a flag in Stage 21. An AQFT certificate is vacuous for m ≤ 6, so it waits for a
  size where it says something (m ≥ 7, §A.4, amendments before Stage 20b3 (6)).

(4) *The formal statement of Proposition 5.1* (21a2, `CQRV/Matching/Complete.lean`).

**The fragment.** `MillerFragment φ` means that `φ.isMillerPattern` holds and that every
metavariable occurs in φ with one argument count. The second condition is necessary.
Counterexample: φ = `c(λ. F x₀, λλ. F x₀ x₁)` and t = `c(λ. x₀, λλ. x₀)`. The substitution
F ↦ λ. x₀ solves it, because `subst` ignores the binding's arity. `millerMatch` builds the
bindings ⟨1, x₀⟩ and ⟨2, x₀⟩, finds them inconsistent, and fails.

**The substitutions.** Only well-formed substitutions count (`Subst.WFFor φ σ`). For every
metavariable of φ, the binding has:
- the arity of its occurrences;
- a body without metavariables, whose free variables are below that arity;
- a body its sort admits.

**The statements.** For φ in the fragment and t ground:
- (i) `millerMatch_complete`, the converse of `millerMatch_sound`: if a well-formed σ with
  φσ = t exists, `millerMatch φ t` succeeds. `millerMatch_wf`: its result is well formed.
- (i′) `matchers_agree`: two well-formed matchers agree on φ's metavariables, so the match set of
  one entry is a singleton. With side conditions over φ's metavariables, `matchPrecondition`
  is complete as well.
- (ii) `library_match_unique`: two entries of `library` never both match.
- (iii) `matchLibrary_noMatch`: a non-`matched` result means that no entry matches. Collected for
  the library as `matchLibrary_spec`.

On a non-match, `cqr match` and `cqr certify` say "No library entry matches (proved)", and the
JSON hint carries `"non_match":"proved"`.

**What is not formalized.** The report's cost bound (Proposition 5.1 (3)) is not, because Lean
has no cost model here. The implementation is one structural pass per entry, with early exit and
no backtracking; that is documented, not proved.

The statements are on normal forms, as `millerMatch_sound` is. Matching modulo the AC theory is
syntactic matching of normal forms (§4.1.1). A theorem that normalization commutes with
substitution in the fragment is not part of Stage 21.

(5) *Certificate and status of a Count request.* This replaces "Certificate and status" above,
in line with §A.4 (amendments before Stage 20b3 (3)–(5)): the certificate is universal in M,
with no "conditional on". Stage 21a3 adds:
- **n ≤ `--count-limit`:** the count is decided by the kernel, and `cert_count` is stated.
  M = 0 is refused before anything is written (diagnostic, exit 1).
- **n > `--count-limit`:** `cert` only. `solution_count` is `{"value": null, "status":
  "not_decided"}`, and the status line ends "solution count not decided".
- **Refused** with `--problem count` in Stage 21 (usage, exit 2): `--solutions`, `--iterations`,
  `--profile`, and `--shape` other than tree. The hardware check is stated for rational δ, and a
  counting certificate with a profile is later work.

(6) *The QPLP record (Definition 4.1) has two layers,* because the `cqr` closure is
Physlib-free (§A.8 item 6).
- **Syntactic layer.** `CQRV/Patterns/Basic.lean` (Physlib-free) holds `QPLP`: the library
  entry, the names of the specification and of the parametric lemma, the grade kind, and the
  builder dispatch that replaces the Grover-only `groverInstance`. `cqr` uses this layer.
- **Semantic layer.** `CQRV/Patterns/Sound.lean` (Physlib-side) holds `QPLP.Sem`, the dependent
  record ⟨S, φ, C, g, π⟩. Its proof field states the realization and the restoration for every
  instance whose builder succeeds. It is instantiated for Grover from
  `grover_parametric_lemma_gen` and for Count from `ae_parametric_lemma_mk`.
- **The claim is per instance.** The Grover output `Reg n` has no metric, so its claim is
  `RealizesExact`. The Count output is pseudo-metric, so its claim is `Realizes`.

(7) *Schema 1.10.0 for every certificate* (21a3).
- **Grover.** The four Grover certificates are regenerated at 1.10.0 with `grade_kind:
  "measured"`. Only their `certificate.json` changes; `Cert.lean`, `.qir` and `.qasm` are
  byte-identical. The schema's top-level `grade` description is reworded for both kinds.
- **Count.** `CertifyTool count-certify` is removed. `cqr certify --problem count` writes
  `examples/certs/grover_pred_037_count`, with `Cert.lean`, `.qir` and `.qasm` byte-identical to
  20b3's.

**21a1 done 9782199, accepted 2026-11-13** (CI 18 PASS, 0 FAIL, 4 n/a). Amendments (2) and (3)
hold as written, with the correction to (2) above.
- `ProblemClass.count`, `SigmaIn.precision`, `Problem` and `SigmaIn.withProblem` exist.
- The seven-field Count term exists, and `sigFields` includes `"m"`.
- φ_Count has F₆ : any and F₅ ≥ 1; `library := [groverEntry, countEntry]`.
- `cqr extract` and `cqr match` take `--problem` and `--precision`.
- `matchLibrary` takes the nearest miss among the entries with the term's root shape. It finds a
  match with `List.findSome?` over the priority-sorted entries, then runs the old scan on the
  candidates.
- The search path is unchanged: 126 of 126 compared runs are byte-identical, and the Stage 4
  guard `["M", "iter"]` passes unchanged.
- The `cqr` closure is 48 modules, Lean + Mathlib only.

**21a2 done eefe3e0, accepted 2026-11-13** (CI 18 PASS, 0 FAIL, 4 n/a). Amendment (4) holds as
written; no statement was false. `CQRV/Matching/Complete.lean` is 1 183 lines, Physlib-free, and
proves:
- `millerMatch_complete`, through `millerMatch_complete_extends`;
- `millerMatch_wf`;
- `matchers_agree`, as a corollary of the two;
- `matchPrecondition_complete`;
- `matchLibrary_noMatch`, through `List.findSome?_eq_none_iff`, and `matchLibrary_matched`;
- `library_fragment` (decide) and `library_match_unique` (from `not_matches_both`);
- `SigmaIn.toTerm_ground`;
- `matchLibrary_spec`, with axioms `propext`, `Classical.choice`, `Quot.sound`.

The uniform-arity counterexample is a test. "Not matched" is stated as `(matchLibrary lib
t).isMatched = false`. The hypothesis `t.Ground` of `millerMatch_complete` is implied by
well-formedness, but kept as stated. The kernel does not reduce `List.mergeSort`, so concrete
uses of `matchLibrary` in the kernel rewrite with `library_mergeSort` first.

The no-match outputs carry the proved wording: 22 of the 126 compared runs differ, only by it.
The `cqr` closure is 49 modules.

**Refinements at the 21a2 review (2026-11-13), for 21a3.** They make (5) and (6) precise.

(5′) *When the count is not decided*, n > `--count-limit`, the certified statement is still
`cert` for every M ≥ 1, but ε depends on the unknown a = M/2ⁿ. The JSON then gives:
- `spec.epsilon`: `{expr: "max over a in [0,1] of 2*pi*sqrt(a*(1-a))/2^m + pi^2/4^m =
  pi/2^m + pi^2/4^m", approx: π/2^m + π²/4^m}`. This is a sound upper bound, because
  2π√(a(1−a)) ≤ π.
- `instance.M`: `null`.
- `solution_count`: `{"value": null, "status": "not_decided"}`.
- the status line: `certified (ε ≤ π/2^m + π²/4^m ≈ …, δ = 1 − 8/π² ≈ 0.189431; universal in
  M ≥ 1; solution count not decided)`.

Counting is the case where M is unknown, so this path is not an edge case.

(6′) *The claim of `QPLP.Sem` is uniform.* Its proof field states `Realizes` for every
instance. The Grover output gets a discrete metric through a type synonym (`DiscreteOut (Reg n)`,
distance 0 or 1). Its ε = 0 realization then comes from the existing `RealizesExact` by
`realizes_zero_iff`. This replaces "the claim is per instance" in (6). If the synonym route meets
an instance problem in Lean, the fallback is the per-instance claim of (6), reported.

**21a3 done a9f12c2, accepted 2026-11-14** (CI 18 PASS, 0 FAIL, 4 n/a; step 22 701 s, 620 s
at 21a2). The uniform claim of (6′) holds; the per-instance fallback was not needed.
- `QPLP` (Physlib-free) carries the entry, the names of the specification family, the parametric
  lemma and the semantic instance, the grade kind, and the builder dispatch `instantiate`.
  `qplpLibrary_entries` is `rfl`, so `matchLibrary_spec` applies unchanged.
- `QPLP.Sem` (Physlib-side) states `Realizes ∧ AncRestore` for every instance. The Grover output
  is `DiscreteOut (Reg n)` with the discrete metric. Mathlib has no discrete metric to reuse, so
  it is defined here. `groverSem` and `countSem` read `grover_parametric_lemma` and
  `ae_parametric_lemma_mk` through the record without re-proof. Their axioms are the standard
  three. A composed bound is the corollary `QPLP.Sem.realizes_of_le`.
- `cqr certify --problem count --precision m` writes the counting certificate in three forms:
  count decided, count not decided (5′), and coherent. M = 0 is refused with `no_solutions`.
  `CertifyTool count-certify` is removed.
- Every certificate is at 1.10.0; Grover certificates carry `grade_kind "measured"`. The five
  committed directories were regenerated with every `Cert.lean`, `.qir` and `.qasm`
  byte-identical. The `cqr` closure is 50 modules.

Three deviations from the task text are accepted:
- `QPLP` has a `builder` field, so the dispatch is total and does not go by the entry's name.
- `target` lies in the unitary group `𝐔[Reg n]`, which is what `AncRestore` takes. The task
  text's `Matrix … ℂ` was wrong.
- The header line "generated by `CertifyTool count-certify`" stays in the committed counting
  `Cert.lean` and in `renderCountCert`, for byte identity. It is corrected at the next stage that
  may change `Cert.lean` bytes.

The `countSem` test takes `hcard` and `hC` as hypotheses; it shows that the record applies at the
AND network, which is what F5 asked. Step 7 took 230 s in this CI run (124 s at 21a2) with no new
check; 21a4 reports it.

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

**Amendment before Stage 21 (8) (reviewer, 2026-11-13; 21a4).**

**Scope.** Selection in Stage 21 is for search requests. The candidate space is the three
certified pairs (tree, mbu), (tree, coherent) and (few:log, mbu), at the request's r; few:log
with coherent has no certificate path.

**Fit and order.**
- A candidate is admissible when its measured grade is ≤ the budget componentwise (the budget
  order of §3.1).
- The order is lexicographic: first the preferred component, then the others in the order
  (w, d, t, a).
- When no candidate fits, there is a diagnostic listing every candidate's grade, exit 1, and
  nothing is written.

**What the certificate contains.**
- The ordinary certificate of the chosen candidate.
- `cand_grades`: every candidate's grade, by `decide +kernel` on the builder.
- `selected`: the chosen candidate fits the budget, and no admissible candidate is smaller in the
  order (`decide`).

**Count selection is not in Stage 21.** Comparing counting candidates means comparing composed
bounds, not measured grades. The natural criterion there is precision first (the largest
admissible m), which is not the grade order above. It is left open for the M3 review.

**Refinement at the 21a3 review (2026-11-14), for 21a4.** (8′) makes (8) precise.

*The candidates.* There are three, named and listed in this order:
1. `treeMbu`: `groverCircuit N n r`;
2. `treeCoherent`: `groverCircuit N n r none .tree .coherent`;
3. `fewLogMbu`: `groverCircuitFew N n r .logDepth`.

These are the builders whose output the `emitted_ok` theorems of the three committed Grover
certificates check. All three are built at the request's r. The list order breaks ties: among
admissible candidates with equal keys, the first is chosen.

*The order.* `--prefer` names the first component: `width` is w, `depth` d, `t` t, `anc` a.
The key of a grade is that component followed by the other three in the order (w, d, t, a). Keys
are compared lexicographically on ℕ.

*The budget.* `--budget w,d,t,a` gives four naturals; there is no wildcard. A candidate is
admissible when g ≤ budget in the order of §3.1 (`CQRV/Grades/Order.lean`). `--budget` and
`--prefer` must be given together.

*What `Cert.lean` states.* It keeps the ordinary certificate of the chosen candidate and adds:
- `cand_grade_c` for each candidate c: `(c.build net n r).map Synthesis.grade = .ok g_c`, by
  `decide +kernel` (one kernel evaluation of the builder). For the chosen candidate it follows
  from `emitted_ok` and `grade_eq`. If a builder fails at the instance, the certificate states
  the failure instead, and the candidate is not admissible.
- `chosen_fits : Synthesis.grade emitted ≤ budget`.
- `selected : ∀ c ∈ candidates, ∀ C, c.build net n r = .ok C → Synthesis.grade C ≤ budget →
  ¬ lexLt (key pref (Synthesis.grade C)) (key pref (Synthesis.grade emitted))`.

`selected` quantifies over the builders' outputs, not over a list of numbers. So the claim "no
admissible candidate in this space is better in this order" is kernel-checked against the
circuits themselves. The selection function the CLI runs is proved once in the library
(`select_spec`): what it returns is admissible, no admissible candidate lies strictly below it,
and it returns `none` exactly when no candidate fits.

*The JSON.* A certificate written with `--budget` has `schema_version "1.11.0"` and an object
`selection`, present iff the version is 1.11.0 and for Grover only. Its fields:
- `budget` {w, d, t, a};
- `prefer`;
- `order`: the four letters in key order;
- `candidates`: each with `shape`, `uncompute`, `grade` (`null` if the builder failed) and
  `admissible`;
- `selected` {shape, uncompute};
- `theorem`: the name of `selected`.

A certificate written without `--budget` is unchanged and stays at 1.10.0, so the five committed
directories are not touched.

*What the selection cannot see.* For `grover_pred_037` at r = 2 the grades are:
- `treeMbu` (15, 134, 72, 7);
- `treeCoherent` (15, 200, 144, 7);
- `fewLogMbu` (10, 172, 96, 2).

`treeCoherent` is dominated componentwise by `treeMbu`, so no budget and no preference selects
it. Coherent uncomputation adds compute adjoints and saves no qubit, so this is expected in
general, not only for this predicate. Its advantage is that it has no mid-circuit measurement
and no classical feed-forward (`grade_ext` meas = ff = 0), and that is not part of (w, d, t, a).
It stays in the candidate space and in `selected`. A budget on `grade_ext` is a question for the
M3 review, together with Count selection.

**21a4 done ceaf36f, accepted 2026-11-15** (CI 19 PASS, 0 FAIL, 4 n/a; the new step 23
"Certified selection" took 154 s, step 22 688 s). (8′) holds as written; no statement was false.
- **The module.** `CQRV/Patterns/Select.lean` is Physlib-free. It defines `Pref`, `Grade.key`,
  `lexLt` (Mathlib's order on `List ℕ`, decided), the three candidates with their builders, and
  `select`. `select_spec` is proved once, for any list; its axioms are the standard three.
- **The certificate.** `selected` quantifies over the builders' outputs. One kernel run audits
  `cert`, `chosen_fits` and `selected`.
- **A detail the text did not foresee.** The kernel does not evaluate `groverCircuitFew` directly,
  because the MCZ plan sorts. So a non-chosen `fewLogMbu` gets its `cand_grade` through
  `groverCircuitFew_ok_of`, with its own oracle and MCZ literals, as the few:log certificate does.
- **The committed example.** `examples/certs/grover_pred_037_sel` uses budget (12, 200, 100, 8)
  and prefer depth. It selects `fewLogMbu`; one of three candidates is admissible. Kernel 25.4 s.
  Its `.qir` and `.qasm` are byte-identical to `grover_pred_037_few`'s, and removing the selection
  block gives that directory's `Cert.lean` byte for byte.
- **Schema 1.11.0** appears only in certificates written with `--budget`. The five older
  directories are untouched. `order` is written as a string (`"dwta"`), which is accepted.
- **Invariants.** The search outputs are unchanged (the 126 runs as at 21a2). The `cqr` closure is
  51 modules.

With 21a4, Stage 21a is complete, and so is milestone M3: two patterns are certified end to end
(Grover and Count), Proposition 5.1 is proved for the implemented fragment, and selection under a
budget is certified.

### A.7 Stretch: measured composition exercised (report Theorem 3.3a)

Counting followed by search with the estimated `M` ("search with an unknown number of
solutions") composes at a measured interface: stage 1 outputs `ã`, stage 2 runs Grover with
`r*(ã)`. In the framework, stage 2 must be a graded channel on the encoding of the intermediate
value; a circuit whose iteration count depends on a classical input is not expressible in the IR
without classically controlled iteration, so the honest options are (a) a channel family indexed
by the intermediate outcome, with Theorem 3.3a generalized to that form, or (b) exercising
Theorem 3.3a on two certified toy stages, as the report's own validation gate did for 3.3b. The
M3 review decides; the obstacle is recorded either way. Decided at the M3 review: §A.9 (1).

### A.8 Design choices (decided 2026-10-29) and what the task files still fix

1. Output type and metric: `Y_m = Fin (2^m) ⊕ Unit` with the metric induced by `ã` (§A.4) is the
   primary route; the tolerance-carrying specification is the fallback, used only if the Stage 20b
   implementer reports the induced metric as an obstacle. Amended before Stage 20b: `CountOut m a
   = Reg m ⊕ Unit` with a real-valued estimate (§A.4, amendments before Stage 20b (1)).
2. `rot` gates carry no T-estimate in the grade or the certificate. The run report prints the
   rotation count and, when it is positive, the note "Clifford+T cost depends on the synthesis
   precision (see §C)" (amended 2026-10-31); a
   Ross–Selinger estimate, if ever given, is a hardware-profile matter.
3. Precision of the committed counting certificate: `n = 8, M = 32`, `m = 4` (15 controlled
   iterates); the harness of Stage 20b also runs `m = 6` (Stage 19b's runs m ≤ 4). The exact `ε`
   at `m = 4` is
   `2π·√(7/64)/16 + π²/256`, stated as a real in the certificate as `δ` is today.
4. Resolved: the controlled oracle's final conjunction is an AND node (§A.3, amendment (3));
   `ψ_± = (ψ_g ± i ψ_b)/√2`, and the proof does not use them (§A.4, amendment (1)).
5. Certificate form of the counting certificates: compositional (§A.3), with blocks of at most 600
   instructions measured exactly and the whole grade a ⊕ bound labelled `composed_bound`. Every
   Lean process stays below 8 GB on the 16 GB machine (decided at the 18a review, 2026-11-01).
6. Import discipline: the `cqr` executable's import closure (the synthesizer `CQRV/Synthesis/*`,
   the certificate generator, the emitters) is Lean core and Mathlib only, never Physlib.
   Theorems that need the semantics (`Circuit.WF`, `Gate.isUnitary`, `unitaryDenote`,
   `channelDenote`) live in `CQRV/Circuit/Semantics.lean`, a `*Correct.lean` module or a later
   module that the executable does not import. Reason: Physlib's trailing notation
   `p [x₁ ↔ x₂]` (`QuantumInfo/ClassicalInfo/Prob.lean`) changes the parse of a term followed by a
   newline and `[` (the 18b `RunReport.lean` failure), and the executable has had this closure
   since Stage 6. There is no project-wide guard against the notation and no CI check: in a file
   that imports Physlib, such a list is parenthesised where it occurs, and the reviewer checks
   the closure at each audit (at 3ec8377: `Lean`, `Mathlib`, 46 local modules). Decided at the
   18b review, 2026-11-01.

### A.9 The M3 review (2026-11-15)

M3 was reached with 21a4 (ceaf36f). The author approved each of the following decisions.

1. **21b runs in two steps.**
   - **21b1 is a short feasibility probe.** It writes no certificate and changes no committed
     file outside its probe and its notes. It answers two questions:
     - Can stage 2 of "search with an unknown number of solutions" be stated as one
       `GradedChannel` on the encoded estimate? Stage 2 is Grover with `r⋆(ã)` chosen by the
       classical outcome. The IR has no classically controlled iteration, so the question is about
       the channel level, with the grade taken as the maximum over branches.
     - Is there a small instance where the composition by `measured_composition` gives a
       non-vacuous δ? The domain hypothesis needs `S_g`'s domain to be the estimates within ε of
       the true a; δ_g is then the worst Grover failure over that range.
   - **21b2 follows the probe.**
     - If the probe is positive, 21b2 implements route (a) of §A.7 at that instance.
     - If it is negative, 21b2 exercises Theorem 3.3a on two small certified stages (route (b)).
   - The obstacle is recorded either way. 21b1 gets its text at the review of the M3 close task.
2. **23b is decided at M4**, after Stage 23, since its content depends on Stages 22–23.
3. **Stage 29 is not run as a stage.** Stage 30 records why: no Coq / SQIR toolchain, and the
   download and effort it needs. It also gives a comparison with SQIR / VQO from the literature
   only.
4. **Count selection gets no Phase 2 stage.** Its order puts precision first (the largest
   admissible m) and compares composed bounds. Paper 1 lists it as a limitation and future work.
5. **A budget on `grade_ext`** (no mid-circuit measurement, no feed-forward) gets no stage of its
   own. It is an input to Stage 24 (the capability flags of `HardwareTarget`) and Stage 26
   (selection by the physical grade). There, `treeCoherent` is the candidate for a target without
   mid-circuit measurement.
6. **The stale header line** "generated by `CertifyTool count-certify`" of the counting
   certificate is corrected in the M3 close task. This is the one change to a committed
   `Cert.lean` there.
7. **The M3 report.** The M3 close task writes `docs/M3_REPORT.md` from measured data, as
   `docs/M2_REPORT.md` was written at M2. `docs/M2_REPORT.md` stays frozen. The report gives:
   - what is certified, with the axioms;
   - the committed certificates, their grades and kernel times;
   - the scope of Proposition 5.1 and of the selection claim;
   - the CI with its step times;
   - the deviations and open items, with the destinations decided here;
   - the claims Paper 1 may make, each with its evidence and exact scope, and the claims it must
     not make.

   The text of Paper 1 is revised at Stage 30; nothing is published before then. The M3 report is
   written from the repository alone; `docs/paper/` is neither read nor edited for it.

Order after M3: the M3 close task, then 21b1, 21b2, then Track B (Stage 22). §B.1 is written
before Stage 22 starts.

**21m done dbbfe71, accepted 2026-11-15** (CI 19 PASS, 0 FAIL, 4 n/a; step 22 687 s, step 23 154
s).
- The counting certificate's header now names `cqr certify --problem count`. Its `Cert.lean`
  changed in that line only; `.qir` and `.qasm` are byte-identical.
- `docs/M3_REPORT.md` (288 lines) has the eight sections of item (7). Every number names its
  source, and the CI table is the acceptance run of 21m. The errata against report v3 are two
  kernel times.

From here on, the author has delegated the running of the process up to Stage 30 to the reviewer
(2026-11-15). The reviewer's recommendations are taken as decisions, recorded as "reviewer
decisions (delegated)". Downloads, accounts and credentials, anything published, and the final
text of the papers still go to the author.

**Refinement at the 21m review (2026-11-15), for 21b1.** The reviewer read the code for route (a).
The probe checks these points; they are not established.
- `measured_composition` assumes `[MetricSpace Y]`, but the counting output `CountOut m a` is only
  pseudo-metric: an outcome and its reflection have the same estimate. Route (a) therefore needs
  Theorem 3.3a on a pseudo-metric, as 20b1 did for 3.3b. The question is whether the existing
  proof goes through unchanged.
- `GradedChannel` carries a declared grade. So stage 2 can be a measure-and-prepare channel:
  measure y, then prepare the output of Grover with r(y) iterations. Its grade is the maximum over
  the branches.
- Two of the three hypotheses are free:
  - Non-expansiveness holds trivially for `S_g y z := |countEst m a y − a| ≤ ε ∧ P z`: take z = z'.
  - Domain compatibility is `countSpec_relax`.
- The cost is in δ_g. Bounding the stage-2 failure over the domain needs, for every outcome y
  whose r(y) is not the good r, a proof that y lies outside the domain. Each such proof is a
  strict real inequality on sin²(π y/2^m).
- The reviewer's arithmetic, which the probe recomputes, for n = 8 and M = 32:
  - At m = 4 the outcome y = 0 (estimate 0) lies in the domain with a bad r, so the composite is
    vacuous.
  - At m = 5 and m = 6 the domain seems to contain only outcomes with r(y) = 2, which would give
    δ ≈ 1 − 8/π² + 7/128 ≈ 0.244.

**21b1 done, accepted 2026-11-15** (a probe; no CI). Route (a) is feasible at `grover_pred_037`
(n = 8, M = 32) with m = 5. `docs/notes/PROBE_21B1.md` records the findings, and
`scripts/probes/Probe21b1.lean` holds the proofs (outside the build; 12 s; standard axioms):
- **Q1.** `measured_composition` holds on pseudo-metric spaces with its proof unchanged; no lemma
  it uses needs a metric.
- **Q2.** Physlib has no measure-and-prepare constructor. The probe builds one from the
  block-diagonal Choi matrix through `CPTPMap.CPTP_of_choi_PSD_Tr`, in 60 lines, and proves
  `measurePrepare_encode`.
- **Q3.** The numbers confirm the reviewer's arithmetic:
  - m = 4 is vacuous. Both y = 0 and y = 1 lie in the domain with a wrong r.
  - For m = 5 to 7, the domain contains only outcomes with r = 2, giving δ = 1 − 8/π² + 7/128 ≈
    0.2441.
  - `simple_alu_x0_1` is non-vacuous but weak, and is not a candidate.
- **Q4.** At m = 5 there are 15 exclusion inequalities, up to the symmetry y ↔ 32 − y. The
  tightest (y = 2, margin 0.0124) is proved in 16 lines from `Real.pi_lt_d4`, `Real.sin_le` and
  `nlinarith`.
- **Q5.** The counting certificate at m = 5 checks in 22.4 s with 2.6 GB.

**Refinement at the 21b1 review (2026-11-15), for 21b2** (reviewer decisions, delegated).

*(9) The stage-2 grade covers every branch.* Stage 2 runs the Grover circuit at r(y) on every
outcome y, not only on the outcomes in the domain. So its declared grade must bound all of them.
In the theorem this is a hypothesis `∀ y, Synthesis.grade (C y) ≤ g₂`. The probe's composite
grade (21, 2996, 1436, 8) took the maximum over the domain only. At m = 5 the outcome y = 0 has
estimate 0 and gets r = 12. The honest g₂ is therefore the Grover grade at the largest r in the
table; 21b2 states which grade that is, and recomputes the composite grade.

*(10) The post-processing is a parameter.* `rStar` computes in `Float`, which the kernel does not
evaluate. So the theorem takes r, or directly the circuit family `C : CountOut m a → Circuit`, as a
parameter, and assumes the good-domain hypothesis: every y within ε of a gets the circuit `C₀` of
r₀ iterations. The CLI or a probe computes the table with `rStar`; the theorem does not depend on
how the table was found.

*(11) The two stages come through the QPLP records.* Stage 1 is `countSem` and the per-branch
stage 2 is `groverSem`, so the composite is stated over the two records' parameters and proved
from their proof fields. This uses Definition 4.1 rather than restating the lemmas.

*(12) No committed composition certificate.* The domain lemma is real analysis specific to one
instance: strict inequalities on sin²(πy/2^m), which no generator can produce for arbitrary
(n, M, m). The remaining facts at the instance are circuit equalities and grades, which are
decidable and of the kind every committed certificate already checks by kernel. So 21b ends with
21b2: the library theorem, the instance's domain lemma, and the corollary at (8, 32, 5) with only
those decidable facts as hypotheses. Paper 1 may say that Theorem 3.3a is exercised at that
instance in this form, and no more.

**21b2 done, accepted 2026-11-15** (CI 19 PASS, 0 FAIL, 4 n/a; step 22 757 s, step 23 171 s).
Theorem 3.3a is exercised at `grover_pred_037`, (n, M, m) = (8, 32, 5), in the form of
refinement (12). Stage 21 is complete.
- **New library pieces:**
  - `measured_composition_pseudo` (Composition.lean, 20 lines);
  - `CQRV/Realizability/MeasurePrepare.lean`, the measure-and-prepare channel, 96 lines;
  - `CQRV/Grover/SearchUnknownM.lean`, 395 lines: `searchStage`, `SearchAfterCount` and its three
    lemmas, `searchStage_realizes`, `search_unknown_M` over `countSem` and `groverSem`,
    `search_unknown_M_rat`, `domain_8_32_5` (118 lines with its helpers, using `pi_gt_d4` /
    `pi_lt_d4`, `sin_le` and `sin_gt_sub_cube`), and `search_unknown_M_8_32_5`.
  - All have the standard three axioms.
- **The numbers at the instance:**
  - the table r(y) = 12, 8, 3, 2, 2, 1, 1, 1, 0, …, 0, 1, 1, 1, 2, 2, 3, 8;
  - the honest stage-2 grade is the Grover grade at r = 12, (15, 794, 432, 7);
  - the composite grade is (21, 2862, 1364, 8) ⊕ (15, 794, 432, 7) = (21, 3656, 1796, 8);
  - ε ≈ 0.0746, δ = 1 − 8/π² + 7/128 ≈ 0.2441.
- **Accepted forms:**
  - The grade bound of (9) is returned as a conjunct on every branch: `Realizes` reads only the
    declared grade.
  - The decodings and specifications are written out rather than as record projections, because
    projected instances break `rw`.
  - `groverSem.pre` is not needed, since `GroverParams` carries `hM_pos`.
- **The generic theorem does not tie the two predicates.** Stage 1 may count one predicate and
  stage 2 search another; the theorem stays true. The corollary at the instance ties them, since
  both circuits are built on the same network `O.N`. Paper 1 cites the corollary.

## §B. A theory of restoration under measurement (Track B; Paper 2)

Written at the 21b2 review (2026-11-15) by the reviewer, under the author's delegation.
Report: §6.2.1 (`AncRestore`), §6.2.2 (the temporary logical-AND and MBU), §6.2.4 (the three
layers), §6.3.2 (Lemma 6.3.2). PHASE2_ROADMAP rows 22, 23, 23b. Track B is Physlib-side
throughout: no CLI, certificate or CI-step change, and no existing statement changes.

### B.1 The general MBU theorem (Stage 22)

**What exists.** MBU is proved for one gadget. `mbu_channel_correct` (Stage 6b-1) says that
`TempLogicalAND; Z t; H t; measure t; if 1: CZ; if 1: X t` maps ρ ⊗ |0⟩⟨0| to
CZ ρ CZ† ⊗ |0⟩⟨0|. The proof is a case split over the four inputs and the two branches. Nothing
says why CZ is the right correction, and nothing covers any compute block other than the AND.

**The setting.** Fix a data register `Reg n`, an ancilla register `Reg a`, an ancilla qubit `t`
and a classical bit `j`.
- **A compute block** for f : Reg n → Bool with phase φ : Reg n → ℂ (|φ x| = 1 for every x) is
  a list `B` of unitary gates (`Gate.isUnitary`). For every data basis state x, `unitaryDenote
  n a B` maps |x, 0…0⟩ to φ x · |x, e_t(f x)⟩. Here e_t(b) is the ancilla basis state with t = b
  and every other ancilla 0. Other ancillas may be used inside B, but come back to 0.
- **A phase implementation** of f is a list `O` of unitary gates on data qubits only. Its
  `unitaryDenote` is λ · (diag((−1)^{f x}) ⊗ 1) for some λ with |λ| = 1. The global phase λ is
  allowed because it lives in one measurement branch only, and a scalar per branch does not
  disturb restoration (`ancRestore_of_kraus`).
- **The MBU uncompute** is `mbuUncompute t j O := [.h t, .measure t j] ++ O.map (.ifBit j) ++
  [.ifBit j (.x t)]`. The §6.2.2 listing is the instance
  `UncomputeTempLogicalAND a b t m = mbuUncompute t m [.cz a b]`.

**The theorem (`mbu_general`).** Take a well-formed circuit whose gates are
`B ++ mbuUncompute t j O` and whose only measurement is the one of `mbuUncompute`. Then
`AncRestore n a C (diagU φ)`. With `Z t` inserted, that is with gates
`B ++ [.z t] ++ mbuUncompute t j O`, the conclusion is `AncRestore n a C (diagU (φ · (−1)^f))`.
At φ = 1 the two conclusions are the identity and `phaseOracle f`.

In words:
- In the X basis, outcome 1 leaves the phase (−1)^{f(x)} on the data, and O removes it. Outcome
  0 leaves nothing.
- The reset returns the ancilla to |0⟩.
- A compute phase φ is *not* removed: MBU needs a phase-exact compute block, or it leaves diag(φ)
  on the data. The coherent uncompute, the adjoint of B, would remove φ.
- The temporary AND is phase-exact (`tempLogicalAND_correct_lift`). This is the
  "relative-phase convention" of the roadmap row.

**The AND instance re-derived.** With B = `TempLogicalAND a b t`, f = a ∧ b, O = `[.cz a b]` and
φ = 1, the statement of `mbu_channel_correct` follows from `mbu_general`. This is a second proof
of the same statement; the Stage 6b-1 proof stays.

**The Clifford corollary (Stage 22b).** O can be chosen Clifford iff f has degree ≤ 2 over
GF(2).
- (⇐) is constructive. f(x) = c ⊕ ⊕_i a_i x_i ⊕ ⊕_{i<j} b_ij x_i x_j is implemented by Z on x_i
  where a_i = 1, and CZ on (x_i, x_j) where b_ij = 1; c only contributes the global phase −1.
- (⇒) For D = diag((−1)^f), D X_i D† = X_i · diag((−1)^{f(x) ⊕ f(x ⊕ e_i)}). This is a Pauli up
  to phase iff the derivative D_i f is affine, and all derivatives are affine iff f is quadratic.
- "Clifford" for a diagonal unitary means that conjugation maps every X_i to a Pauli up to a
  phase; the Z_i commute with D. The definitions are stated explicitly and both directions are
  proved.

This explains why the MBU of an AND is free (the correction is the Clifford CZ), and why MBU is
costly beyond degree 2: for a three-input AND the correction is CCZ, with 7 T.

**The split.**
- 22a: `mbu_general` in both forms, the AND re-derived, the tests.
- 22b: the Clifford corollary.

**22a done, accepted 2026-11-15** (CI below). `CQRV/Circuit/MBUGeneral.lean` (468 lines) proves:
- `mbu_general` and `mbu_general_phase` for any phase-exact compute block B and any data-only
  phase implementation O;
- the φ = 1 corollaries;
- `mbu_channel_correct_of_general`, the statement of `mbu_channel_correct` word for word, from
  the general theorem. The Stage 6b-1 proof stays.

All have the standard three axioms. `diagU` is new: neither Mathlib nor Physlib has a
diagonal-unitary constructor. The hypothesis C.nBits = j + 1 of the task text was dropped: it is
derivable from the gate list and `C.WF`, so it is redundant, not false. The linear instance
f = x0 ⊕ x1 is a test.

**A fact of the IR that refines §B.1.** `Circuit.WF` admits only Clifford gates under `ifBit`
(`Gate.bitOk`: `g.isClifford`). So the corrections O that `mbu_general` can use in a well-formed
circuit are lists of Clifford gates. The degree-3 example (correction CCZ, 7 T) is therefore not a
well-formed circuit of this IR; the test was not written, for this reason and not for its cost.
The §B.1 sentence "for a three-input AND the correction is CCZ, with 7 T" is true of the matrix,
but in this IR "MBU is costly beyond degree 2" reads "MBU is not expressible beyond degree 2".

**Refinement at the 22a review (2026-11-15), for Stage 22.** The Clifford corollary splits:
- **22b, the mathematics.** The quadratic characterization, the constructive direction, and
  `IsCliffordDiag (phaseDiag f) ↔ IsQuadratic f`.
- **22c, the IR boundary.** A list of IR Clifford gates acting on data only, whose unitary is
  λ · (phaseDiag f ⊗ 1), has f quadratic. Hence a well-formed `mbuUncompute t j O` with
  `PhaseImpl n a O f` forces `IsQuadratic f`, and in this IR `mbu_general` applies exactly to the
  quadratic f. This needs the conjugation of Paulis by each IR Clifford gate.

**22b done, accepted 2026-11-15** (CI below). `CQRV/Circuit/MBUClifford.lean` (540 lines;
𝔽₂ = `ZMod 2`) proves:
- `isQuadratic_iff_deriv_affine`. Its (⇐) half reconstructs the coefficients and goes by
  induction over indicator vectors; the task's statement needed no change.
- `phaseCircuitQuad_phaseImpl`: Z and CZ gates, λ = (−1)^c.
- `mbu_quadratic`: every quadratic f with a compute block has a restoring MBU circuit.
- `conj_pauliX_phaseDiag`, `phaseDiag_eq_smul_pauliZ_iff` and `clifford_iff_quadratic`.

All have the standard three axioms. The tests show by `decide` that x0 ∧ x1 ∧ x2 is not quadratic,
and prove `¬ IsCliffordDiag (phaseDiag (x0 ∧ x1 ∧ x2))`: the CCZ matrix is not Clifford, as a
theorem. `mbu_quadratic` applied to `mbuCircuit` gives the statement of `mbu_channel_correct` a
third time.

**Refinement at the 22b review (2026-11-15), for 22c.** The Clifford notion of 22b is the
diagonal one. 22c needs the general notion on the IR's register `Reg n × Reg a`, and the
restriction from it to the diagonal notion on `Reg n`. The plan is the implementer's (22b (e)):
- **A Pauli** on `Reg n × Reg a` is λ · monoMat (flip the qubits in S) (s ↦ (−1)^{parity of the
  qubits in T at s}), with ‖λ‖ = 1.
- **A unitary is Clifford** when it conjugates every single-qubit X and Z to a Pauli. Closure
  under products goes through "every Pauli is a product of single-qubit ones".
- **Every IR Clifford gate is Clifford:**
  - X, Z, S, Sdg, CNOT and CZ, and `p` / `cp` under the divisibility of `Gate.isClifford`, are
    monomial, so the conjugation is a computation;
  - H is the one non-monomial case, through H X H = Z.
- **The restriction.** If λ · (D ⊗ 1) is Clifford on n + a qubits and D is a diagonal sign
  matrix, then `IsCliffordDiag D`.
- **`mbu_wf_forces_quadratic`.** A well-formed circuit containing `mbuUncompute t j O` with
  `PhaseImpl n a O f` has f quadratic. This holds because `Circuit.bitsOkFrom` demands
  `isClifford` under `ifBit`.
- **`mbu_exactly_quadratic`.** For a compute block B for f: a well-formed MBU circuit
  B ++ [Z t] ++ mbuUncompute t j O with `PhaseImpl n a O f` exists iff f is quadratic.
  - (⇐) uses `phaseCircuitQuad`, whose gates are Clifford, with its well-formedness.

  This is the sentence Paper 2 states: in this IR, MBU applies exactly to the quadratic f.

**22c done, accepted 2026-11-15** (CI below). `CQRV/Circuit/MBUBoundary.lean` (801 lines) builds a
Pauli and Clifford layer on the IR's register `Reg n × Reg a`, in the symplectic representation:
- `pauliMono S T λ` = λ X^S Z^T, where S and T are bit vectors of the register, with the exact
  product rule;
- `IsPauli`, closed under products and adjoints;
- `IsClifford U := ∀ P, IsPauli P → IsPauli (U P Uᴴ)`. This is the standard definition; the
  generator form of the task text is its corollary. Closure under products is one line.

`gateU_isClifford` holds for every IR Clifford gate, with no range hypothesis (H through
H = (Z + X)/√2). From there:
- `isCliffordDiag_of_tensor`;
- `mbu_wf_forces_quadratic`;
- `mbu_exactly_quadratic`.

All have the standard three axioms.

**One statement of the task text was false and is corrected.** "Fix a bit j" fails for j ≥ 1. A
well-formed circuit B ++ [Z t] ++ mbuUncompute t j O has exactly one classical bit, so j = 0. The
counterexample is j = 1 with f = x0 ∧ x1 and B the temporary AND: no well-formed circuit of that
shape exists, so the (⇐) direction fails.

The corrected `mbu_exactly_quadratic` makes j existential. It needs only B's well-formedness
(qubits in range, unitary gates), not that B computes f:
(∃ j O C, C.nData = n ∧ C.WF ∧ C.gates = B ++ [.z t] ++ mbuUncompute t j O ∧ PhaseImpl n a O f)
↔ IsQuadratic f.

**Stage 22 is complete.** Paper 2 may state that in this IR, measurement-based uncomputation
applies exactly to the quadratic f. The cubic case (CCZ) is excluded by `Circuit.WF`, not by
cost.

### B.2 The restoration algebra (Stage 23)

Written at the 22c review (2026-11-15) by the reviewer, under the author's delegation. Report:
§6.2.1, §6.2.3 (the three regimes, Table 4), §6.2.4, §6.3.2. PHASE2_ROADMAP row 23; review R1.7
(the 8n − 24 argument). Stage 22's conventions continue: the symplectic representation, 𝔽₂ =
`ZMod 2`, and statements on `channelDenote` through Kraus operators.

**What exists.**
- `AncRestore n a C U`: clean restoration on density operators.
- `AncRestore.comp`: sequential composition through `Circuit.append`.
- `ancRestore_of_kraus`: every branch acts as a scalar times U ⊗ |0⟩⟨0| on the clean-ancilla
  subspace.
- `ancRestore_foldl`: the iteration in `Grover/Restore.lean`.
- Stage 22: `mbu_general`, and the IR boundary.

**What Stage 23 adds.** Three tasks.

*23a — composition laws for clean restoration.*
- **Block lists.** Local restoration implies global restoration for any list of blocks, not only
  for an iterate.
- **Restoration under measurement with a mixed data action** (`AncRestoreMix`). If branch c of a
  circuit acts on the clean-ancilla subspace as l_c · (U_c ⊗ |0⟩⟨0|), then the ancillas are
  restored and the data undergoes the mixture ρ ↦ ∑_c |l_c|² U_c ρ U_cᴴ. Clean restoration is
  the case where all the U_c are equal. The example is MBU without its correction: the ancilla
  is restored, but the data is dephased in the basis of f, with U_0 = 1, U_1 = O_f and weights
  1/2. This is the precise sense of "restoration under measurement".
- **Widening, or ancilla reuse.** A block certified on a ancillas, touching only those, is
  certified on a + b ancillas with the same unitary. So blocks certified with different ancilla
  counts compose on the larger register.

*23b — the three regimes of §6.2.3.*
- **Dirty.** `AncRestoreDirty n a C U`: for every data state ρ and every ancilla state σ,
  `channelDenote n a C (ρ ⊗ σ) = (U ◃ ρ) ⊗ σ`.
- **Conditionally clean**, after Khattar–Gidney §2. The exact definition is fixed at the 23a
  review, against the invariant the existing `MczFewAll.lean` uses.
- **Laws:**
  - the hierarchy: dirty restoration ⇒ clean restoration;
  - sequential composition in each regime;
  - commutation of blocks on disjoint qubits (a gate-level lemma on the qubits a gate acts on);
  - a dirty instance: a phase gadget that uses a dirty ancilla twice, so that its value cancels.

*23c — the 8n − 24 argument as a theorem.* It formalizes the counting of `docs/MCZ_NOTES.md` on
Khattar–Gidney Problem 1 schedules, under a stated cost model:
- 4 T for a conjunction on a clean target, uncomputed by MBU;
- 8 T for one on a non-clean target, a relative-phase Toffoli pair.

With two clean ancillas, at most two conjunctions target clean qubits, so an MCZ_n needs at least
4·2 + 8(n − 4) = 8n − 24 T (`problem1_T_lower_bound`). Candidate B (`few:log`) attains it. The
theorem is about the cost model and the schedules, not a lower bound on the T-count of all
circuits; Maslov's per-Toffoli 4-T bound is a stated assumption, not proved. 23c gets its text at
the 23b review.

**Gate.** The three regimes with their composition laws, and the M4 milestone: a draft of Paper 2,
written after 23c as `docs/notes/PAPER2_DRAFT.md` (the reviewer's draft; the author owns the
final text).

**23a done, accepted 2026-11-15** (CI below). `CQRV/Circuit/RestoreAlgebra.lean` (593 lines)
proves:
- `ancRestore_list`, local restoration implies global restoration for any list of blocks;
- `ancRestoreMix_of_kraus`, restoration under measurement with a mixed data action, in matrix
  form (Physlib has no mixture API on `MState`);
- `sum_norm_sq_eq_one_of_kraus`;
- `mbu_uncorrected` and `mbu_uncorrected_phase`: MBU without its correction restores the
  ancilla and dephases the data in the basis of f, ½ ρ + ½ O_f ρ O_f;
- `AncRestore.widen` and `AncRestore.comp_widen`: ancilla reuse, through
  `Reg (a + b) ≃ Reg a × Reg b`, transporting the channel equality directly.

All have the standard three axioms. The weight hypothesis ∑ ‖l_c‖² = 1 of the Stage 6b-1
`ancRestore_of_kraus` turns out to be redundant: it follows from Kraus completeness. The
hypothesis-free form is `ancRestore_of_kraus'`, and the old statement stays.

**Refinement at the 23a review (2026-11-15), for 23b.** The meaning of "conditionally clean" is
fixed here.
- **What the code has.** The invariant of `MczFewAll.lean` (Stage 13a, KG §5.1) is a statement
  about computational-basis values in an array model. A marked index t > 0 holding 0 is
  "conditionally clean": its value is determined by the controls below it. It is an internal
  invariant of the MCZ proof, whose block is cleanly restoring as a whole (`AncRestore`).
- **Conditionally clean as a regime of restoration** (report Table 4, "conditional factorization
  under a branch condition"). For a condition cond : Reg n → Bool, the conditionally clean
  subspace V_cond is spanned by the |x, w⟩ with cond x → w = 0. A block is conditionally clean
  restoring with U when it acts as Ad(U ⊗ 1) on every state supported on V_cond.
- **The hierarchy.** Dirty restoration is Ad(U ⊗ 1) on every product state, hence on every state.
  It implies conditionally clean restoration for every cond, which implies clean restoration
  (cond ≡ true gives V = {w = 0}).
- **The KG invariant enters as documentation and one bridge lemma**, not as the definition: in the
  array model, `Inv.cond` says that a marked t > 0 has a value fixed by a condition on the indices
  below it.

**23b done, accepted 2026-11-15** (CI below). `CQRV/Circuit/RestoreRegimes.lean` proves the three
regimes of report §6.2.3 with their laws.

*Dirty.*
- `AncRestoreDirty`, with `ancRestoreDirty_of_kraus`, `ancRestoreDirty_of_unitary`, `toClean` and
  `comp`.
- `AncRestoreDirty.all`: a dirty block acts as Ad(U ⊗ 1) on every state. It rests on the span of
  product states, proved by polarization.
- The phase gadget that uses a dirty ancilla twice is dirty restoring with CZ.

*`reset_not_dirty`.* A circuit that ends by measuring an ancilla, applying a data-only correction
and resetting it, is not dirty restoring for any U. This is the theorem behind "dirty ancillas
cannot use MBU"; `mbuCircuit` is the corollary.

*Conditionally clean.*
- `AncRestoreCond`: Ad(U ⊗ 1) on the states supported on V_cond.
- The hierarchy is exact: dirty = Cond(false) ⇒ Cond(cond) ⇒ Cond(true) ⇒ clean, with
  `toDirty`, `mono`, `toClean` for every cond, and `ancRestoreDirty_iff_cond_false`.
- `AncRestoreCond.comp`, under the matrix form of "U₁ ⊗ 1 maps V_cond into V_cond'".
- The instance `[cz (data 0) (anc 0)]` under cond = x0 shows that both implications are strict.

*The KG bridge.* `Inv.cond_value` lives in `CQRV/Grover/KGRegime.lean`; the layering rule is that
Circuit modules do not import Grover modules. It states that a marked target t > 0 has its value
fixed by the indices below it.

All theorems have the standard three axioms, except the bridge, which uses `propext` only.

*Corrections and skips.*
- The task text's justification of "not dirty" for the instance was wrong: a phase on a basis
  vector is not a witness. The witness is |1⟩ ⊗ |+⟩ ↦ |1⟩ ⊗ |−⟩; the statement stands.
- Skipped as allowed: `AncRestoreDirty.widen` (about 80 lines through the span argument) and the
  commutation on disjoint qubits (a split of the data register, above its guard).
- Not proved: clean ⇒ Cond(true). It needs the data block of a state supported on {w = 0} as an
  `MState`.

**Refinement at the 23b review (2026-11-15), for 23c.** The 8n − 24 theorem is stated in an
abstract schedule model, not over the code's two-array plan, and is then connected to candidate
B.
- **The model.** An array A : Fin L → Bool (true = available as a target, false = holds a live
  value) and a set `Clean` of indices that start available and fresh. An operation (t, x, y)
  needs A t, ¬A x, ¬A y and t, x, y distinct. It sets A t := false and A x, A y := true.
- **The cost model**, the KG family's: 4 T for the first operation that targets a fresh clean
  index (Gidney's AND, uncomputed by MBU), and 8 T for every other operation (a relative-phase
  Toffoli pair, Maslov's 4 T each). The 4 T per relative-phase Toffoli is the stated assumption
  of the model, not a proved lower bound on circuits.
- **The counting.** Every operation lowers the number of live values by one. So a schedule from
  n live values to k has n − k operations, and at most |Clean| of them target a fresh clean
  index.
- **`problem1_T_lower_bound`.** With |Clean| = 2 and k ≤ 2 (the final phase is a CZ, 0 T, or a
  Z), the cost is at least 8n − 24 for n ≥ 4.
- **Candidate B attains it.** Its plan is valid in the model, with `Clean` = {anc 0, anc 1}, and
  costs 8n − 24. The emitted T-count equals the cost: for n = 4…12 by `decide`, and for all n
  only if the induction over the plan stays within a size guard.

**23c done, accepted 2026-11-15** (CI below). `CQRV/Synthesis/Problem1.lean` (362 lines;
Physlib-free, not imported by the CLI) defines the schedule model:
- `P1State` (avail, fresh);
- `P1Op` = (t, x, y), with validity and the step;
- the costs 4 / 8.

It proves:
- `live_step`, `nFresh_le`, `cost_add`, `live_run`;
- the general form `cost_lower_bound`, cost ≥ 8 (n − k) − 4 min(|fresh₀|, n − k);
- `problem1_T_lower_bound`, cost ≥ 8n − 24 for |fresh₀| = 2, k ≤ 2, n ≥ 4.

Candidate B's plan translates into the model with no exception. Each clean index is targeted at
most once, since index 0 of an array is never a control.
- **Validity, end state and emitted T-count** (`planB_valid`, `planB_live`, `planB_tCount`) are
  proved for n = 4 … 12 by kernel evaluation, through a kernel-evaluable copy of the plan
  (`plan_eq`), because `List.mergeSort` does not reduce in the kernel.
- **The T-count 8n − 24** (`planB_cost`) holds for n = 6 … 12.
- **The all-n forms** were not attempted, being over the guard; their route is recorded.
- The three-clean-ancilla example costs 8n − 28, so the bound counts the clean ancillas.

**One statement of the task text was false at two values and is corrected.** "Candidate B costs
8n − 24 for n = 4 … 12" fails at n = 4 and 5, where B costs 8n − 20 (`planB_cost_small`). The
greedy leaves two unmarked qubits after the first array, so `anc 1` is never targeted and B uses
one AND instead of two. The bound 8n − 24 is still attained in the model at n = 4, by a
two-operation schedule in the tests. B attains it from n = 6 on, as
`tests/CQRVTests/MczFew.lean` already said.

**Stage 23 is complete. M4 is reached** with `docs/notes/PAPER2_DRAFT.md`, the reviewer's draft
of Paper 2. Every claim in it names its theorem, and the author owns the final text.

### B.3 The M4 review (2026-11-15; reviewer decisions, delegated)

1. **23b is not run as a stage.** Its three points become remarks in Paper 2's discussion:
   - the relation of the Unqomp / Silq safety conditions to the criterion of Stage 22;
   - graded realizability as a fibration;
   - the obstruction theorem, which exists in its concrete form (`no_cloning_obstruction`).
   None needs new mechanization for the paper's claims.
2. **The M4 housekeeping list goes to Stage 30's cleanup**, not to a task now:
   - the duplicated kernel-evaluable schedule (`Grover.FewSchedule` and Problem1's copy);
   - the layering exception `Circuit/CountingCorrect.lean` → `Grover/Restore.lean`.
   Both are code quality without a claim attached.
3. **Open proof items** are listed as open in Paper 2 §10 and in `docs/M3_REPORT.md`'s successor
   at M5:
   - clean ⇒ Cond(true);
   - the dirty widening;
   - commutation of blocks on disjoint qubits;
   - the all-n forms of 23c.
4. **Track C starts with Stage 24.** It needs Qiskit, Aer and the runtime fake provider: a
   download from PyPI that the author must approve. §C.1 is written after the author's answer.
   If the download is declined, Track C is reconsidered, and the simulator-only path of the
   roadmap is the default.

## §C. Hardware backend, simulator first (Track C; Paper 1)

Written at the M4 review (2026-11-15) by the reviewer, under the author's delegation. Report:
§3.1.3 (hardware profiles as change of base), §5.3 (the emitter and the trust boundary), §2.3.2
and §6.6 (noise). PHASE2_ROADMAP rows 24–28.

The architecture is that of the hardware study (PHASE2_ROADMAP, Track C):
- the Lean certificate is unchanged;
- the backend is a new layer after it;
- untrusted tools (Qiskit, Aer) do the work and produce a witness, and Lean checks the witness;
- the rest becomes named hypotheses.

Two rules apply throughout:
- **Never "verified on hardware".** A simulator run is an emulation; it validates nothing about a
  device.
- **Downloads go to the author.** Qiskit, Aer and the runtime fake provider were approved on
  2026-11-15. They are installed into a separate git-ignored venv `.venv-hw` and pinned in
  `hw/requirements.lock`. The harness venv `.venv` and its lock are untouched. Any further
  download (another package, a newer pin, real calibration data) needs a new approval.

### C.1 Target model and lowering (Stage 24)

**The target model.** A `HardwareTarget` is a JSON file, schema
`docs/hardware_target.schema.json`, with:
- `name`, `source` (the fake backend's class and the package version), and `num_qubits`;
- `basis_gates`, the native gate names, and `coupling_map`, the directed edges;
- `capabilities`: `mid_circuit_measurement`, `feed_forward` (classically conditioned
  operations, Qiskit's `if_else` / `if_test`) and `reset`. Each flag is read from the backend's
  target and says where it was read from;
- `durations`: per gate and qubit tuple, in ns;
- `calibration`, a snapshot:
  - errors per one-qubit gate and qubit, per two-qubit gate and edge;
  - readout error per qubit;
  - the mid-circuit measurement error per qubit, if the source gives it. If it does not, the
    field is null with a note, and the readout error is not silently substituted;
  - T1 and T2 per qubit;
- `snapshot`: the timestamp the source gives, and `hash`, the SHA3-256 of the canonical JSON of
  `calibration`. The canonical form is sorted keys, compact, and numbers as the source gives
  them.

**`cqr hw capabilities <target.json>`.** It reads a target, validates the fields it needs, and
prints:
- the capability flags;
- which uncomputation modes the target supports: `mbu` needs mid-circuit measurement and feed
  forward; `coherent` needs neither;
- the snapshot hash.

Lean reads the JSON, Physlib-free, and checks the hash with the existing SHA3. A target that does
not support `mbu` is an input to Stage 26's selection, which picks `treeCoherent` there (§A.9
(5)).

**Lowering.**
- The canonical circuit JSON of the IR (the JSON `cqr synthesize` and the certificates hash, not
  the QASM text) is lowered to a Qiskit dynamic circuit. Each `ifBit j g` becomes an `if_test` on
  the classical bit, and each `measure q j` a mid-circuit measurement into that bit.
  `alloc` / `free` are bookkeeping.
- An ideal Aer simulation is compared with the in-repo statevector reference, branch by branch:
  for each assignment of the classical bits, the post-measurement state of that branch and its
  probability, up to global phase. The comparison runs on every committed example and generated
  instance with at most 6 data qubits plus ancillas.
- The lowering is an untrusted tool. What validates it is the comparison here; Stage 26 later
  checks witnesses in Lean.

**Per-operation rates.** The hardware bound of Stage 11b, δ_hw ≤ δ + G · p̄, uses one rate p̄ for
all G operations. It is replaced by
δ_hw ≤ δ + Σ_types (count of the type) · (the rate of the type, from the snapshot): one-qubit
gates, two-qubit gates, mid-circuit measurements, final readout.
- Before transpilation the counts are the logical ones (`gateCounts`, `grade_ext`). After
  transpilation (Stage 25) they are the physical ones.
- The bound is still a union bound under a stochastic-noise premise, and it is reported, not
  certified, until Stage 27's theorem.
- The old p̄ form stays available for the committed certificates, whose JSONs are unchanged.

**The split.**
- **24a:** the environment, the `hw/` package skeleton, `HardwareTarget` with its schema, two
  committed targets extracted from fake backends, and `cqr hw capabilities`.
- **24b:** the lowering and the branch-by-branch comparison on Aer, as a new CI step.
- **24c:** the per-operation-type rates and the weighted bound in the run reports.
