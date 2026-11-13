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
