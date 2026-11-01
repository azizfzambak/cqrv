# Stage 18 — QFT and approximate QFT (PHASE2_SPEC §A.2), and the kernel-evaluation forms (the 14b/14c ceiling, the 16b `Nat m` item)

PHASE2_SPEC.md §A.2 (as amended 2026-10-31, "Amendments before Stage 18"), §A.0.1 (adjoint
circuits), §A.4 (the client of `qft_basis` and `η_aqft`); report §9.1.1 (the IR and its
semantics), §2.3.2 (Theorem 3.3b, `dist⋄`), §3.1.1 (the grade), §9.5.1 (kernel check);
PHASE2_ROADMAP.md row 18; `docs/benchmarks/SCALING.md` (Stage 14b/14c). Three tasks, **three
commits**: do **18a**, reply, stop; **18b** and **18c** each start after the reviewer accepts the
previous one, from `main`.

Precondition: Stage 17 complete; main = fb72491 (the 17b review commit). `git switch -c stage-18a
main` (18b: `stage-18b` from `main` after 18a is merged; 18c likewise). The 18a commit includes
this file (untracked until then; do not edit it). Untracked and not yours: `docs/paper/`,
`docs/cqrv_report_revised_v4.docx`. Windows: `LEAN_NUM_THREADS=4`. Process as in Stage 17:
`lake build` in the foreground; `scripts/ci_local.sh`, the probe runs of 18a and any Lean run
longer than a few minutes are the user's separate terminal, one Lean process at a time; when the
build is green and the tests you can run yourself pass, stop and say "ready for CI" (18a has an
extra stop, "ready for the probe run", see A2); after the user's run, read the logs, commit,
closing reply.

**Invariants of all three tasks.** Every measured value is unchanged: `Grade` and `GradeExt` of
every golden circuit (CI step 14) and of the four committed certificates (`grade_eq`,
`gradeExt_eq` literals), the scheduler's **placement rule** (`layer := ready + 1`, the `qReady` /
`cReady` updates, `alloc` / `free` in layer 0), `TempLogicalAND`, `MBU`, the synthesizer, the
diffusion builders, `groverCircuit`. The committed `Cert.lean`, `.qir`, `.qasm` files are
byte-identical in 18a and untouched in 18b / 18c (only `certificate.json` / `run_report.*`
machine fields move when a certificate is regenerated). Every existing theorem **statement** is
unchanged, with one consented exception in 18a (A1: the three Stage 17a lemmas that mention the
type of `SchedState.placed`). If anything else seems to need a statement change, stop and
propose.

---

## 18a — Kernel-evaluation forms: the ceiling re-attributed and lifted, the probe, the `Nat m` diagnosis (infrastructure; no new theory)

### What the record actually says (read first)

`bench/scaling/out/rand_a64_r1_h/lean.log` has exactly one error, at `Cert.lean:449:70`, and
line 449 of that file is

```
theorem grade_eq : Synthesis.grade emitted = ⟨76, 585, 300, 64⟩ := by decide +kernel
```

— **not** `emitted_ok` (line 442, which elaborated and kernel-checked on the 1953-gate literal
without error), and not `nAnc_eq` (line 451). The Stage 14b/14c texts and the roadmap attributed
the "deep recursion detected" to the emitted literal / `emitted_ok`; the correct attribution is
the kernel evaluation of `Synthesis.grade emitted`, i.e. of `schedule`. Working hypothesis
(confirm or refute in A2): `SchedState.placed : Array (Gate × Nat)` is built by 1953
`Array.push`es, and `Array.push a v = ⟨List.concat a.toList v⟩` nests one `List.concat` per gate,
so the first traversal of the finished array (`depth`'s `foldl`) must unfold a 1953-deep chain
of `concat`s — the kernel's recursion guard, which `--tstack` cannot move (14c). `nAnc_eq`
(`List.foldl` over the literal) and `emitted_ok` (`decEq` over the literal) passed at the same
size.

### A0. The `Nat m` diagnosis (time box 30 minutes of your time + one run in the user's terminal; report only)

DECISIONS.md 2026-10-31 (Stage 16b, "Open"): a scratch program with a parameter `k : Nat 3` made
the certificate's front-end block elaborate for more than five minutes where `Vec`-only programs
take seconds. Reproduce it once, measured, and name the slow declaration:

- `bench/forms/nat_m.cqr` (committed, a few lines): a predicate the matcher accepts as Grover
  with parameters `(x : Vec 4) (k : Nat 3)` or similar — the smallest program that exhibits the
  slowness in your 16b notes. `scripts/kernel_forms.sh` (A2) generates its certificate with
  `cqr certify … --count-limit 0 --out bench/forms/out/nat_m` and then runs
  `lake env lean -Dprofiler=true -Dprofiler.threshold=500 bench/forms/out/nat_m/Cert.lean` under a
  900 s timeout, writing `lean.log` next to it (the profiler prints one line per declaration
  above the threshold: elaboration, `decide`, type checking).
- From the log, report: the declaration (`prog` literal, `prog_scoped : … := by decide`,
  `net_ok : … := except_ok_of_check _ _ (by decide +kernel)`, `front_end`, or another), its time,
  and a one-paragraph hypothesis (for instance: `decide` on `scoped` with a `Nat` parameter is
  evaluated by the elaborator's `whnf` at default transparency, where `Nat` arithmetic on
  `Ty.width` / `natOfBits` is slow, and `decide +kernel` would not be). **No fix in 18a**: the
  fix changes every `Cert.lean` and is a reviewer decision (18a review).
- If `cqr certify` itself does not finish within 900 s on that program (its own kernel check is
  the slow step), the script records that outcome and the profile of a `Cert.lean` produced with
  the kernel check disabled is not required: say so and stop A0 there.

### A1. The scheduler state as a cons list (`CQRV/Circuit/Schedule.lean`; Stage 17a lemmas adapted)

- `structure SchedState`: `placed : List (Gate × Nat) := []`, **most recent first**; `step`
  conses `(g, layer)` / `(g, 0)` instead of `push`. `schedule c : Array (Gate × Nat) :=
  ⟨(c.gates.foldl SchedState.step {}).placed.reverse⟩` — the structure constructor `Array.mk`
  on the reversed list (`List.reverse` is `reverseAux`, tail-recursive), **not** `List.toArray`
  (which pushes element by element and would nest again). The type and the value of `schedule`
  are unchanged, so `depth`, `layers`, `layerDump`, `gradeExt`, `grade` need no edit (check
  that none of them relies on `placed` being an `Array`).
- The three Stage 17a lemmas whose statements mention `placed` are **adapted, with the
  reviewer's consent given here**: `SchedState.step_placed : ∃ l, (st.step g).placed = (g, l) ::
  st.placed`; `foldl_step_placed : (gs.foldl SchedState.step st).placed = (gs.map …).reverse ++
  st.placed`-shaped (state it in the form your proof of `schedule_gates` needs);
  `schedule_gates : (schedule c).toList.map Prod.fst = c.gates` **keeps its statement** and is
  re-proved. `gradeExt_tDepth_le_depth`, `gradeExt_meas_eq_nBits`, `gradeExt_tDepth_le_tCount`
  and every other statement are unchanged (their proofs may need one `simp` lemma about
  `Array.toList ⟨l⟩`).
- Agreement with the old definition, by test: copy the Stage 17b `SchedState` / `step` /
  `schedule` verbatim into `tests/CQRVTests/Schedule.lean` (new file; the `.submodules` glob of
  the lakefile picks it up) as `SchedStateOld` / `scheduleOld`, and `#guard scheduleOld c ==
  schedule c` on: every corpus oracle (`oracle s` and `oracleC s` for the seven sources of the
  Stage 17a test), `diffusion n none` and `diffusion n none .tree .coherent` for n = 1..10,
  `mczFew n .logDepth` for n = 3..10, `groverCircuit` of the running example (r = 2, both modes)
  and of `simple_alu_x0_1` (r = 1), `Emit.sampleCircuit`. A general theorem `schedule_eq_old`
  (simulation of the two folds) is welcome if it is short; the `#guard`s are the acceptance.
- Expected effect, measured in A2: `grade_eq` and `gradeExt_eq` of rand_a64 (1953 gates) pass
  in the kernel; the kernel medians of the four committed certificates may drop (the chain was
  also costing time at 700 gates). Record both.

### A2. The probe (`scripts/kernel_forms.sh`, `bench/forms/`, `docs/benchmarks/KERNEL_FORMS.md`)

Measurement only, in the user's terminal (`LEAN_NUM_THREADS=4`; exactly one Lean process at a
time; 900 s timeout per Lean run; peak memory recorded as `scripts/bench_scaling.py` records it —
reuse its `run_timed` / `kernel_run` through a small Python driver if that is simpler than bash;
then the script is `scripts/kernel_forms.py` with a one-line bash wrapper). Probes:

1. `rand_a64` at r = 1 (1953 gates; the 14b failure), r = 2 (~3 900) and r = 3 (~5 850):
   `cqr certify bench/scaling/rand_a64.cqr --solutions 1853 --iterations r --count-limit 0 --out
   bench/forms/out/rand_a64_r{r}` (the hypothesis form, as 14b's `_h` items), each followed by
   `lake env lean -Dprofiler=true -Dprofiler.threshold=1000 Cert.lean` for the per-declaration
   times. **Memory guard**: run r = 3 only if r = 2 finished with a peak below 9 GB and within
   the timeout; otherwise record "skipped (guard)" — this laptop has 16 GB.
2. The `Nat m` scratch of A0.
3. The four committed certificates, `grade_eq` alone and `gradeExt_eq` alone with the
   certificate's metric (the scratch-file method of 17b: `net`, `emitted` and that one theorem),
   before and after A1 (run "before" from `git stash` or a worktree of `main` — or take the
   17b numbers 7.04 / 5.58 / 5.98 / 13.5 s and 9.26 / 7.03 / 7.95 / 17.5 s as "before" and say so).

`docs/benchmarks/KERNEL_FORMS.md` (generated from the logs by the driver, like SCALING.md's
tables; hand-written reading at the end): one row per probe and declaration (`emitted_ok`,
`delta_eq`, `grade_eq`, `gradeExt_eq`, `nAnc_eq`, the oracle / MCZ certificates, `cert`) with
kernel seconds, outcome, peak MB, instruction count; then: the corrected attribution of the 14b
ceiling (quote the log line); whether rand_a64 (1953) now certifies and at what cost; the new
ceiling if one appeared (which declaration, which size); the empirical exponent of `grade_eq`
against gates after A1; and **a recommendation, not a decision**, for the Stage 19–20 certificate
form — a flat literal with `decide +kernel` as today, or a compositional form (the counting
circuit as `countingCircuit n m P` built from certified blocks, the hash link per block) — with
the sizes it would have to cover (the running example at precision m = 4 is about 15 controlled
Grover iterations, i.e. roughly 10 000 gates). The reviewer decides at the 18a review.

Flow of 18a: A1 + the script + tests → `lake build` green, local tests pass → stop: **"ready for
the probe run"** (the user runs `scripts/kernel_forms.sh` in their terminal and tells you) → read
the logs, write KERNEL_FORMS.md and the A0 paragraph → regenerate the four committed certificates
with their own flags (`grover_pred_037` and `simple_alu_x0_1` without `--profile`, `_few` and
`_coh` with `--profile illustrative_sc`, all `--bench 5 --report`; `Cert.lean` / `.qir` / `.qasm`
must come back byte-identical — assert it in `certify_check.py` against the 17b commit 9fc909b)
→ stop: **"ready for CI"** → CI → commit → closing reply.

### 18a Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the re-attribution of the 14b ceiling with the log line; the cons-list
state and why `Array.mk`, not `List.toArray`; the three adapted lemma statements; the probe
results in one table; the A0 finding; the recommendation for Stage 19–20 — marked as a
recommendation); `docs/PROJECT_STATUS.md` (kernel medians, one line on the probe); SCALING.md
**unchanged** (it is generated; the correction lives in KERNEL_FORMS.md and DECISIONS.md);
SORRIES.md untouched (nothing new is proved by `sorry` here). No README change. Do not edit
`docs/PHASE2_SPEC.md` or `docs/PHASE2_ROADMAP.md` (reviewer files; commit them unedited if the
working tree holds reviewer edits).

Acceptance: `lake build` green and warning-free; CI 16 PASS, 0 FAIL, 4 n/a; golden circuits
(step 14) and the four `Cert.lean` / `.qir` / `.qasm` byte-identical; `grade_eq` / `gradeExt_eq`
literals unchanged; the `scheduleOld == schedule` guards; KERNEL_FORMS.md with the probe table;
rand_a64 at 1953 gates kernel-checked (or the report says precisely which declaration still
fails and why).

Stop and ask: the cons-list state changes any measured grade (a guard fails); rand_a64 at 1953
still fails after A1 (report the declaration and the new hypothesis; do not try a third
representation); the r = 2 probe exceeds 900 s or 12 GB (skip r = 3, report); a statement other
than the three named lemmas would have to change.

---

## 18b — QFT and approximate QFT: circuits, encodings, `qft_basis`, harness (after 18a is accepted)

### B1. Circuits (`CQRV/Synthesis/QFT.lean`, new)

```
/-- PHASE2_SPEC.md §A.2 — block j of the textbook QFT without the final swaps: H on data qubit
j, then `cp 1 k` from qubit j+k−1 onto qubit j for k = 2 .. m−j. -/
def qftBlock (m j : ℕ) : List Gate :=
  .h (.data j) :: (List.range (m - j - 1)).map fun i => .cp 1 (i + 2) (.data (j + i + 1)) (.data j)
def qftGates (m : ℕ) : List Gate := (List.range m).flatMap (qftBlock m)
/-- `aqft m kmax` drops every `cp 1 k` with `k > kmax` (a filter of `qftGates`). -/
def aqftGates (m kmax : ℕ) : List Gate :=
  (qftGates m).filter fun g => match g with | .cp _ k _ _ => decide (k ≤ kmax) | _ => true
def qftCircuit (m : ℕ) : Circuit := ⟨m, qftGates m⟩
def aqftCircuit (m kmax : ℕ) : Circuit := ⟨m, aqftGates m kmax⟩
```

Proved (general m): `qftCircuit_WF : (qftCircuit m).WF`, `aqftCircuit_WF` (every gate on a data
qubit `< m`, `cp` operands distinct since `j + i + 1 ≠ j`, no classical bit); `qftGates_unitary :
∀ g ∈ qftGates m, g.isUnitary = true` (and for `aqftGates`, by `List.filter`); `aqftGates_eq_self
(h : m ≤ kmax) : aqftGates m kmax = qftGates m`; `(qftGates m).length = m * (m + 1) / 2`
(`#guard` for m ≤ 8 and the theorem if short). Measured, in `#guard`s with the values written
out: `grade` and `gradeExt` of `qftCircuit m` for m = 1..8 (expected: `t = 0`, `tDepth = 0`,
`rot = m (m − 1) / 2` — every `cp 1 k` with k ≥ 2 is a rotation, `cp 1 1` never occurs; `twoQ =
rot`; `meas = ff = 0`; `d` as measured), and of `aqftCircuit 6 kmax` for kmax = 1..6. The inverse
circuits are `adjointGates (qftGates m)` (§A.0.1): `#guard` that `adjointGates` of `qftGates 3`
is the expected list (`cp (-1) k`).

### B2. Encodings (`CQRV/Circuit/Basis.lean`, new; imported by `Restoration.lean`'s successors or standalone)

Convention fixed here, **identical to the harness** (`tests/diff/statevector.py`: "qubit 0 is the
most significant bit of the basis index"):

```
def Reg.toNat {m : ℕ} (s : Reg m) : ℕ := ∑ j : Fin m, if s j then 2 ^ (m - 1 - j) else 0
def Reg.toNatLE {m : ℕ} (s : Reg m) : ℕ := ∑ j : Fin m, if s j then 2 ^ (j : ℕ) else 0
def Reg.ofNat (m x : ℕ) : Reg m := fun j => x.testBit (m - 1 - j)
def bitRev {m : ℕ} (s : Reg m) : Reg m := fun j => s (Fin.rev j)
def reg0 : Reg 0 := fun i => i.elim0          -- the unique element; `Subsingleton (Reg 0)`
```

Lemmas: `toNat_lt : s.toNat < 2 ^ m`, `ofNat_toNat : Reg.ofNat m s.toNat = s`, `toNat_ofNat (hx :
x < 2 ^ m) : (Reg.ofNat m x).toNat = x`, `toNat_bitRev : (bitRev s).toNat = s.toNatLE`,
`bitRev_bitRev`, `toNat_injective`; `Reg.toNat` restricted to the top bits: `toNat_mod :
s.toNat % 2 ^ (m - j) = ∑ i : Fin m, if j ≤ i ∧ s i then 2 ^ (m - 1 - i) else 0` (the binary
fraction `0.x_j … x_{m−1}` that block j of the QFT writes). `basisVec` stays where it is
(`CQRV.Circuit.Restoration`, `basisVec (s : ι) : ι → ℂ`), with `mulVec_basisVec` there; if the
import layering wants `Basis.lean` below `Restoration.lean`, move `basisVec` and
`mulVec_basisVec` into `Basis.lean` unchanged (same names, same namespace).

### B3. `qft_basis` (`CQRV/Circuit/QFTCorrect.lean`, new)

The statement, pointwise on the circuit's own register `Reg m × Reg 0` (§A.2 as amended):

```
theorem qft_basis (m : ℕ) (x s : Reg m) :
    (unitaryDenote m 0 (qftGates m) *ᵥ basisVec (x, reg0)) (s, reg0) =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * ((x.toNat * (bitRev s).toNat : ℕ) : ℂ) / 2 ^ m)
```

(`(bitRev s).toNat = s.toNatLE`; the swaps of the textbook circuit are absorbed by the decoding
map of §A.4.) Proof route, as sub-lemmas with these names (state them first; prove in order):

1. `unitaryDenote_flatMap`-style decomposition: `qftGates m = ((List.range j).flatMap (qftBlock
   m)) ++ ((List.range' j (m - j)).flatMap (qftBlock m))` and `unitaryDenote_append`.
2. The phase of block j: `φ m j x : ℝ := (x.toNat % 2 ^ (m - j) : ℕ) / 2 ^ (m - j)` (the binary
   fraction `0.x_j x_{j+1} … x_{m−1}`), with `exp_phase_block : (-1 : ℂ) ^ (if x ⟨j, _⟩ then 1
   else 0) * ∏ i < m - j - 1, (if x ⟨j + i + 1, _⟩ then Complex.exp (2πi / 2 ^ (i + 2)) else 1)
   = Complex.exp (2πi · φ m j x)` (`Complex.exp_sum`, `Complex.exp_pi_mul_I`; the sum of the
   selected `2^{-k}` is `φ` by `toNat_mod`).
3. The prefix invariant `qft_prefix (j ≤ m) : unitaryDenote m 0 ((List.range j).flatMap
   (qftBlock m)) *ᵥ basisVec (x, reg0) = fun p => if (∀ i : Fin m, j ≤ i → p.1 i = x i) then
   ((Real.sqrt 2)⁻¹ : ℂ) ^ j * ∏ i : Fin m, (if (i : ℕ) < j ∧ p.1 i then Complex.exp (2πi · φ m
   i x) else 1) else 0`, by induction on j; the step is block j gate by gate with
   `unitaryDenote_cons_mulVec`, `gateU_h_mulVec` (the `inRange` hypothesis holds, `j < m`),
   `gateU_cp_mulVec`, and 2.
4. The assembly at `j = m`: `∏ i, (if p.1 i then exp (2πi φ m i x) else 1) = exp (2πi · ∑ i,
   [p.1 i] φ m i x)` and `exp_sum_phases : Complex.exp (2πi · ∑ i, [s i] · φ m i x) =
   Complex.exp (2πi · (x.toNat * s.toNatLE : ℕ) / 2 ^ m)` — the two exponents differ by the
   integer `∑ i, [s i] · ⌊x.toNat / 2^{m−i}⌋` (`Nat.div_add_mod`, `Complex.exp_int_mul_two_pi_mul_I`
   or the lemma `exact?` finds; no invented names).

If 4 (`exp_sum_phases`) resists after a serious attempt, leave **that lemma alone** as a tracked
`sorry` (SORRIES.md: file:line, the statement, §A.2, "pure arithmetic on binary fractions") and
prove `qft_basis` from it; everything else proved. `#print axioms qft_basis` under `#guard_msgs`
(the standard three, or the `sorryAx` line). Corollaries: `qft_unitary : unitaryDenote m 0
(qftGates m) ∈ Matrix.unitaryGroup _ ℂ` is `unitaryDenote_mem_unitaryGroup`; `aqft_eq_qft_of_le
(h : m ≤ kmax)`.

### B4. Harness and CI (`tests/diff/qft_diff.py`, `scripts/diff_qft.sh`, `scripts/CertifyTool.lean qft-sample`, `scripts/ci_local.sh`)

- `CertifyTool qft-sample <m> [<kmax>]` prints the IR JSON of `qftCircuit m` (or `aqftCircuit m
  kmax`); `qft-sample <m> --adjoint` the inverse (`adjointGates`).
- `tests/diff/qft_diff.py --m-max 6`: for m = 1..6, builds the DFT matrix **in the harness
  convention** `F[y, x] = 2^{-m/2} · exp(2πi · x · y / 2^m)` with x, y read with qubit 0 as the
  most significant bit, and the bit-reversal permutation `R`; checks on random states that the
  simulated `qftCircuit m` equals `R · F` (i.e. the amplitude at basis state s is
  `2^{-m/2} exp(2πi x · bitrev(s) / 2^m)` — the same convention as `qft_basis`, written out in
  the docstring), that the simulated matrix is unitary, that `adjointGates` gives the inverse
  (`U† U = I` numerically), and for kmax = 1..m that `‖U_qft − U_aqft‖₂` (spectral norm,
  `numpy.linalg.norm(·, 2)`) is `≤ 2π m / 2^kmax` **and** `≤` the sum of the dropped angles
  `Σ 2π / 2^k` (the bound of C1, so 18c's theorem is checked numerically before it is proved);
  negative control: the sign of one rotation flipped is detected. The matrices come from
  `statevector.run_ir` on the 2^m basis states (m ≤ 6: 64 columns, fine).
- `scripts/diff_qft.sh` (template `scripts/diff_mcz.sh`); CI: a new step after "Few-ancilla MCZ":
  `step "QFT / AQFT (Stage 18b)" scripts/diff_qft.sh` — the pass mark becomes **17 PASS, 0 FAIL,
  4 n/a**; say so in the DECISIONS entry and in `scripts/ci_local.sh`'s header.

### B5. Tests (`tests/CQRVTests/QFT.lean`, new)

`#guard qftGates 3 == [the six gates written out: H x0, CP(1/4) x1 x0, CP(1/8) x2 x0, H x1,
CP(1/4) x2 x1, H x2]`; `aqftGates 3 1` is the three H's only (`k ≥ 2` always; guard it); the grades of B1; `Reg.toNat` /
`toNatLE` / `bitRev` / `ofNat` on hand-written registers (`![true, false, true]` ↦ 5, LE 5;
`![true, true, false]` ↦ 6, LE 3); `example` instances of every theorem of B2 / B3 at m = 3;
`#guard_msgs` axiom checks of `qft_basis`, `qftCircuit_WF`; `qft_basis` at m = 1 and m = 2 by
`norm_num`-level checks is optional.

### 18b Docs / Acceptance / Stop

Docs: DECISIONS.md entry (conventions: qubit 0 MSB as the harness, the pointwise statement, the
filter form of `aqft`, where `basisVec` lives, the CI pass mark 17); SORRIES.md if 4 is tracked;
`docs/PROJECT_STATUS.md` one line; no README change. Reviewer files untouched.

Acceptance: `lake build` green; CI 17 PASS, 0 FAIL, 4 n/a; `qft_basis` proved (at most
`exp_sum_phases` tracked); WF and unitarity proved; the harness passes for m ≤ 6 with both
AQFT bounds; the measured grades reported in the closing reply.

Stop and ask: `qft_basis` needs a statement other than B3's (for instance a different sign or
bit order — then the harness and the statement disagree: stop, report both conventions, do not
change the harness); `gateU_h_mulVec` or `gateU_cp_mulVec` need a change; more than one tracked
`sorry`.

---

## 18c — The AQFT bounds and the channel bridge: the Theorem 3.3b client (after 18b is accepted)

### C1. Operator-norm bound (`CQRV/Circuit/QFTCorrect.lean`)

Norm: the L2 operator norm on `Matrix (Reg m × Reg 0) (Reg m × Reg 0) ℂ`, **the same instance
Physlib uses** in `Matrix.traceNorm_mul_le_opNorm_traceNorm` (`QuantumInfo/ForMathlib/MatrixNorm/
TraceNorm.lean`; Mathlib's `Matrix.l2_opNorm_*` lemmas in `Mathlib/Analysis/CStarAlgebra/
Matrix.lean`, scoped instances `Matrix.Norms.L2Operator`) — confirm with `#check` which `open
scoped` / local instance that file uses and use the same, so that the 18c lemmas compose with
Physlib's.

- `unitaryDenote_filter_sub_le (gs : List Gate) (keep : Gate → Bool) : ‖unitaryDenote n a gs -
  unitaryDenote n a (gs.filter keep)‖ ≤ ((gs.filter fun g => !keep g).map fun g => ‖gateU n a g -
  1‖).sum` — no unitarity hypothesis should be needed, since `gateU_mem_unitaryGroup` holds for
  every gate; telescoping by induction on `gs`
  (`unitaryDenote (g :: gs) = unitaryDenote gs * gateU g`; `‖U‖ = 1` for a unitary:
  `Matrix.l2_opNorm_conjTranspose_mul_self` with `Uᴴ * U = 1` and `‖(1 : Matrix …)‖ = 1`
  (`l2_opNorm_diagonal` on the constant-one vector, or the `CStarRing` / `NormOneClass` route
  `exact?` finds); `l2_opNorm_mul`).
- `gateU_cp_sub_one_le (k) (hk : 1 ≤ k) : ‖gateU n a (.cp 1 k c t) - 1‖ ≤ 2 * Real.pi / 2 ^ k`:
  `gateU_cp` is `monoMat id φ = Matrix.diagonal φ` (lemma `monoMat_id_eq_diagonal`),
  `l2_opNorm_diagonal`, the sup of `‖φ s − 1‖ ∈ {0, ‖exp(2πi/2^k) − 1‖}`, and
  `Complex.norm_exp_I_mul_ofReal_sub_one_le : ‖exp (I * x) - 1‖ ≤ ‖x‖` (Mathlib
  `Analysis/SpecialFunctions/Trigonometric/Bounds.lean`) with `x = 2π / 2^k`.
- `aqft_opNorm_le (m kmax : ℕ) : ‖unitaryDenote m 0 (qftGates m) - unitaryDenote m 0 (aqftGates
  m kmax)‖ ≤ 2 * Real.pi * m / 2 ^ kmax`: the dropped gates of block j are `cp 1 k` for k =
  kmax+1 .. m−j, `∑ 2π/2^k ≤ 2π/2^kmax` (geometric series), m blocks.

### C2. The channel bridge (`CQRV/Circuit/Semantics.lean` or a new `CQRV/Circuit/UnitaryChannel.lean`)

`channelDenote_of_unitary {C : Circuit} (hWF : C.WF) (hU : C.gates.all Gate.isUnitary = true) :
channelDenote n a C = CPTPMap.ofUnitary ⟨unitaryDenote n a C.gates,
unitaryDenote_mem_unitaryGroup n a C.gates⟩` — `channelDenote_of_WF`, `krausOps_of_unitary`, the
circuit has no `measure` so `C.nBits = 0` and the Kraus sum over `Fin 0 → Bool` has one term;
`CPTPMap.ext` / `MState.ext_m` and `CPTPMap.ofUnitary_eq_conj`, `channelDenote_m_of_bitsOk`. (Stage
19–20 use it for the controlled-powers block too.)

### C3. Diamond distance of unitary channels (`CQRV/Realizability/Diamond.lean`)

```
theorem diamondDist_ofUnitary_le {d : Type} [Fintype d] [DecidableEq d] (U V : 𝐔[d]) :
    diamondDist (CPTPMap.ofUnitary U) (CPTPMap.ofUnitary V) ≤ 2 * ‖(U : Matrix d d ℂ) - V‖
```

Route: `ciSup_le` over `ρ : MState (d × d)`; `2 · TrDistance σ₁ σ₂ = (σ₁.m − σ₂.m).traceNorm`
(the definition of `TrDistance`, ½ of the trace norm — confirm at `QuantumInfo/States/Mixed/
TraceDistance.lean:31`); the two sub-lemmas:

- `prod_id_ofUnitary (U : 𝐔[d]) (ρ : MState (d × d)) : (CPTPMap.ofUnitary U ⊗ᶜᵖ CPTPMap.id) ρ =
  ρ.uConj (unitary_kron U 1)` (Physlib `unitary_kron`, `QuantumInfo/ForMathlib/HermitianMat/
  Unitary.lean:36`; `CPTPMap.prod` is `MatrixMap.kron` of the two linear maps — find the lemma
  that evaluates a `kron` of two `MatrixMap.conj`s, or prove it on matrices by `Matrix.ext`).
- `l2_opNorm_kronecker_one_le (A : Matrix d d ℂ) : ‖A ⊗ₖ (1 : Matrix d d ℂ)‖ ≤ ‖A‖` (via
  `Matrix.l2_opNorm_def` / `l2_opNorm_mulVec` and `Fintype.sum_prod_type`: `‖(A ⊗ₖ 1) x‖² =
  ∑_j ‖A x_{·,j}‖² ≤ ‖A‖² ∑_j ‖x_{·,j}‖²`).

Then `W₁ ρ W₁ᴴ − W₂ ρ W₂ᴴ = (W₁ − W₂) ρ W₁ᴴ + W₂ ρ (W₁ − W₂)ᴴ` with `W_i = U_i ⊗ₖ 1`,
`traceNorm_add_le`, `traceNorm_mul_le_opNorm_traceNorm`, `traceNorm_mul_le_traceNorm_opNorm`,
`MState.traceNorm_eq_one`, `‖W_i‖ = 1`, `l2_opNorm_conjTranspose`, and `(U − V) ⊗ₖ 1 = U ⊗ₖ 1 −
V ⊗ₖ 1` (`Matrix.sub_kronecker`). Each of the two sub-lemmas may be left as a **tracked `sorry`**
(SORRIES.md, the statement, "Physlib / Mathlib obligation") if it resists after a serious
attempt; `diamondDist_ofUnitary_le` itself is proved from them.

### C4. The client (`CQRV/Circuit/QFTCorrect.lean`)

```
def eta_aqft (m kmax : ℕ) : ℝ := 4 * Real.pi * m / 2 ^ kmax
theorem aqft_diamond_le (m kmax : ℕ) :
    diamondDist (channelDenote m 0 (qftCircuit m)) (channelDenote m 0 (aqftCircuit m kmax)) ≤
      eta_aqft m kmax
```

from C2 (both circuits WF and unitary, 18b), C3 and C1 (`2 · (2π m / 2^kmax)`). Also the inverse
circuits: `aqft_adjoint_diamond_le` for `adjointGates`, if it is a corollary of the same shape
(`unitaryDenote_adjoint`, `l2_opNorm_conjTranspose`); otherwise state it and track it.

### 18c Tests / Docs / Acceptance / Stop

Tests: `#guard_msgs` axiom checks of `aqft_diamond_le`, `diamondDist_ofUnitary_le`,
`channelDenote_of_unitary`, `aqft_opNorm_le` (the standard three, or the `sorryAx` line for the
tracked ones — and then the SORRIES entries); `example` instances at m = 3, kmax = 2. The harness
bound of B4 already checks `aqft_opNorm_le` numerically; add the `η_aqft` line to `qft_diff.py`
if it is not there.

Docs: DECISIONS.md entry (the norm instance; the two sub-lemmas and their status; `η_aqft`; the
bridge lemma), SORRIES.md for anything tracked (each with the statement and "depends on"),
`docs/PROJECT_STATUS.md`, README status line ("Stages 0–18c"). Reviewer files untouched.

Acceptance: `lake build` green; CI 17 PASS; the statements exactly as above (§A.2 as amended);
`aqft_diamond_le` proved modulo at most the two named sub-lemmas tracked; axiom checks.

Stop and ask: a statement needs a hypothesis §A.2 does not have; Physlib's `CPTPMap.prod` has no
usable characterization after an hour (then track `prod_id_ofUnitary` and continue); a third
`sorry` would be needed.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests — 18a: CI summary, the probe table (per
declaration), the kernel medians old → new, the A0 finding; 18b: CI summary, the measured grades
of `qftCircuit m` for m = 1..8, the harness output incl. the two AQFT bounds; 18c: CI summary,
the axiom lines, what is tracked —, (d) SORRIES.md, (e) open questions: for 18a the
recommendation for the Stage 19–20 certificate form and the `Nat m` fix proposal (both reviewer
decisions); for 18c anything learned about Physlib's `CPTPMap.prod`.
