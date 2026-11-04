# Stage 19 — The counting circuit (PHASE2_SPEC §A.3), and grade composition (§A.3 item 2)

PHASE2_SPEC.md §A.3 (as amended 2026-11-01, "Amendments before Stage 19" — read it first; it
replaces the register layout, the renumbering and the `U_count` formula of the text above it),
§A.0.1 (coherent mode, adjoint circuits), §A.2 (QFT), §A.8 items 4–6 (item 6: import discipline);
report §3.1.1 Table 3.1 (⊕), §3.1.4, §6.1.4 (the decision-4 scheduler), §6.2.4 and Lemma 6.3.2,
§8.2 (Grover); PHASE2_ROADMAP.md row 19. Three tasks, **three commits**: do **19a**, reply, stop;
**19b** and **19c** each start after the reviewer accepts the previous one, from `main`.

Precondition: Stage 18 complete; main = 3fbe033 (the 18c review commit). `git switch -c stage-19a
main` (19b: `stage-19b` from `main` after 19a is merged; 19c likewise). The 19a commit includes
this file (untracked until then; do not edit it). Untracked and not yours: `docs/paper/`,
`docs/cqrv_report_revised_v4.docx`. Windows: `LEAN_NUM_THREADS=4`. Process as in Stage 18:
`lake build` in the foreground; `scripts/ci_local.sh`, the probe run of 19b (B6) and any Lean run
longer than a few minutes are the user's separate terminal, one Lean process at a time; run the
harness scripts before CI the way `ci_local.sh` does (`.venv/Scripts/python.exe -I`, stdout
redirected to a file, no `-X utf8`); when the build is green and the tests you can run yourself
pass, stop and say "ready for CI" (19b has an extra stop, "ready for the probe run", see B6); the
reviewer audits, the user runs CI, then you commit and give the closing reply.

**Invariants of all three tasks.** Every measured value is unchanged: `Grade` and `GradeExt` of
every golden circuit (CI step 14) and of the four committed certificates; the scheduler (its
definitions and its placement rule), `peakAncilla`, `tCount`, `gradeExt` and every other definition
a committed `Cert.lean` evaluates are **not edited**, not even to an equal form; the synthesizer,
`TempLogicalAND`, `MBU`, the diffusion builders, `groverCircuit`, `qftGates` / `aqftGates`. No
certificate is regenerated. Every existing theorem **statement** is unchanged. The `cqr`
executable gets no new subcommand or flag (the tools are `CertifyTool` subcommands); its import
closure stays Lean core + Mathlib (PHASE2_SPEC §A.8 item 6): the new modules
`CQRV/Circuit/GradeCompose.lean` (19a) and `CQRV/Synthesis/Counting.lean` (19b) import no
Physlib; the semantic theorems go into `CQRV/Circuit/CountingCorrect.lean` (19b, 19c), which the
executable does not import. A definition another module unfolds by `rfl` or evaluates by `decide`
carries `@[expose]` (the synthesis modules keep `@[expose] public section`). In Physlib-importing
files a list that follows a newline is parenthesised. If anything else seems to need a change,
stop and propose.

---

## 19a — Grade composition (report §3.1.1 Table 3.1; PHASE2_SPEC §A.3 item 2 and amendment (6))

New module `CQRV/Circuit/GradeCompose.lean` (imports `CQRV.Circuit.Schedule`; added to the
`CQRV/Circuit/Basic.lean` umbrella). Facts to build on: `Circuit.append C₁ C₂ = ⟨C₁.nData,
C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)⟩` (IR.lean:208; ancillae are **not** shifted,
the register is `C₁`'s); `Circuit.grade c = ⟨c.width, c.depth, c.tCount, c.peakAncilla⟩`
(Schedule.lean:92), `width = nData + peakAncilla`, `peakAncilla` the peak of the live-ancilla
count in program order (`alloc` +1, `free` −1, truncated), `depth` the largest layer of
`schedule` (alloc / free at layer 0); `Grade`'s `+` is ⊕ = `seqComp` (Grades/Basic.lean:39), `≤`
componentwise (Grades/Order.lean:26), `AddCommMonoid Grade` with `nsmulRec` (Basic.lean:85).
`Gate.shiftBits` changes only `measure` / `ifBit` bits (IR.lean:160).

### A1. `liveEnd`

`def Circuit.liveEnd (c : Circuit) : Nat` — the live-ancilla count at the end of the gate list,
the first component of **the same fold** as `peakAncilla` (copy the fold; do not edit
`peakAncilla`). Lemma on the fold pair: starting from `(0, p)` the fold over a gate list `l` ends
at `(live l, max p (peak l))` (generalise over `p`); `shiftBits` leaves `alloc` / `free` alone, so
the fold over `C₂.gates.map (shiftBits k)` equals the fold over `C₂.gates`. `WF` does not check
alloc / free discipline, so `liveEnd C₁ = 0` is a hypothesis of its own (PHASE2_SPEC §A.3 as
amended).

### A2. The components

```
theorem tCount_append (C₁ C₂ : Circuit) : (C₁.append C₂).tCount = C₁.tCount + C₂.tCount
theorem liveEnd_append {C₁ C₂ : Circuit} (h : C₁.liveEnd = 0) :
    (C₁.append C₂).liveEnd = C₂.liveEnd
theorem peakAncilla_append {C₁ C₂ : Circuit} (h : C₁.liveEnd = 0) :
    (C₁.append C₂).peakAncilla = max C₁.peakAncilla C₂.peakAncilla
theorem width_append {C₁ C₂ : Circuit} (hn : C₁.nData = C₂.nData) (h : C₁.liveEnd = 0) :
    (C₁.append C₂).width = max C₁.width C₂.width
theorem depth_append_le (C₁ C₂ : Circuit) : (C₁.append C₂).depth ≤ C₁.depth + C₂.depth
```

`depth_append_le` needs no hypothesis. Route: let `D = C₁.depth`. (i) After the `C₁` part every
entry of `qReady` and `cReady` is a layer of `C₁`'s schedule, hence `≤ D`. (ii) An invariant of
`SchedState.step` along `C₂.gates`: with `st` the state of the appended run and `st₂` that of
`C₂` alone, for every qubit `q`, `(st.qReady.lookup q).getD 0 ≤ D + (st₂.qReady.lookup q).getD
0`, and for every bit `c`, `(st.cReady.lookup (c + C₁.nBits)).getD 0 ≤ D + (st₂.cReady.lookup
c).getD 0` (the shifted bit of an `ifBit c` in the appended run is `c + C₁.nBits`); hence each
gate's appended layer is `≤ D +` its layer in `C₂`. Work through `lookup … getD 0` and the Stage
18a lemmas `step_placed` / `foldl_step_placed` / `schedule_gates` (Schedule.lean:143); no
`bitsOk` hypothesis is needed because every `C₁` entry is `≤ D` anyway.

### A3. The grade theorems

```
theorem grade_append_le {C₁ C₂ : Circuit} (hn : C₁.nData = C₂.nData) (h : C₁.liveEnd = 0) :
    (C₁.append C₂).grade ≤ C₁.grade + C₂.grade
theorem grade_foldl_append_le (init : Circuit) (bs : List Circuit)
    (hn : ∀ b ∈ bs, b.nData = init.nData) (hi : init.liveEnd = 0) (hb : ∀ b ∈ bs, b.liveEnd = 0) :
    (bs.foldl Circuit.append init).grade ≤ init.grade + (bs.map Circuit.grade).sum
theorem grade_replicate_le (init it : Circuit) (r : ℕ) (hn : it.nData = init.nData)
    (hi : init.liveEnd = 0) (ht : it.liveEnd = 0) :
    ((List.replicate r it).foldl Circuit.append init).grade ≤ init.grade + r • it.grade
```

Width, ancillae and T-count are exact (`=` componentwise); depth is the only `≤`. The list form
by induction (`append` keeps `C₁.nData`; `liveEnd_append` keeps the accumulator at 0;
`seqComp_mono`, associativity); the n-fold form from it (`List.sum_replicate` or its name in the
pinned Mathlib — confirm with `#check`).

### A4. The `GradeExt` analogue

`twoQ`, `rot`, `meas`, `ff` of `(C₁.append C₂).gradeExt` are the sums (equalities; `shiftBits`
preserves `isTwoQubit`, `isRotation`, `isMeasure`, `isIfBit`), and

```
theorem tDepth_append_le (C₁ C₂ : Circuit) :
    (C₁.append C₂).gradeExt.tDepth ≤ C₁.gradeExt.tDepth + C₂.tCount
```

(the T-layers of the `C₁` part are those of `C₁`'s schedule; each T-power gate of the `C₂` part
adds at most one layer; `tCount_eq_countP`, Schedule.lean:196). The sum of the two T-depths is
**not** a bound; put the counterexample in the tests: `C₁ = ⟨2, [h (data 0), h (data 0)]⟩`,
`C₂ = ⟨2, [t (data 0), t (data 1)]⟩` — `C₂` alone has `tDepth = 1`, the append has its two `T`
in layers 3 and 1, `tDepth = 2 > 0 + 1`, and the bound `0 + 2` is attained. List forms as in A3
(`tDepth ≤ init.tDepth + (bs.map Circuit.tCount).sum`).

### A5. Tests (`tests/CQRVTests/GradeCompose.lean`, new)

`#guard`s: the counterexample; `liveEnd = 0` for the synthesized oracle and diffusion of
grover_pred_037 (the Grover certificate's network) and for `qftCircuit 4`; `(o.append d).grade ≤
o.grade + d.grade` for that oracle and diffusion, with the measured values printed in the closing
reply; `groverCircuit` at r = 2 against `hLayer.grade + 2 • iteration.grade`; examples
instantiating each theorem; `#guard_msgs` axiom checks of `depth_append_le`, `grade_append_le`,
`grade_foldl_append_le`, `grade_replicate_le`, `tDepth_append_le` (the standard three). Note: the
`oracle_plus_diffusion` grade that `cqr synthesize --grover` prints (Apps/cqr/Main.lean:342,
`o.grade + d.grade`) is now a proved upper bound of the iteration's measured grade — say so in
DECISIONS; no CLI change.

### 19a Docs / Acceptance / Stop

Docs: DECISIONS.md entry (`liveEnd` and why it is not part of `WF`; the depth invariant; the
T-depth counterexample and the `tCount` bound; the exact components); `docs/PROJECT_STATUS.md`
one line; no README change. Reviewer files untouched.

Acceptance: `lake build` green; CI 17 PASS, 0 FAIL, 4 n/a (no new CI step); A2–A4 proved, no
`sorry`; the tests above.

Stop and ask: a component needs a hypothesis beyond `hn` / `liveEnd`; a definition the
certificates evaluate would have to change; the depth invariant fails on an example (report the
example); the proof of `depth_append_le` resists after a serious attempt (then state it, track
the scheduler invariant as the one `sorry`, and ask before going on).

---

## 19b — The counting circuit: builders, restoration in the circuit's own factors, harness, block probe (after 19a is accepted)

Layout (PHASE2_SPEC §A.3 amendment (1)): search register `data 0..n−1`, phase qubit `j` =
`data (n+j)`, data register `n + m`. Facts: `synthesizeOracle N mode` returns `nData :=
N.nInputs`, ancillae `anc 0..` (Oracle.lean:165); `Diffusion.onAll g n` acts on `data 0..n−1`
(Diffusion.lean:44); `diffusionNet shape n` (Diffusion.lean:103); the circuit's diffusion is
`−U_s` (`diffusion_circuit_matrix`, Grover/Reflections.lean).

### B1. `Network.withControl` (`CQRV/Synthesis/Counting.lean`, new, Physlib-free)

`def Network.withControl (N : Network) (m j : Nat) : Network` — `nInputs := N.nInputs + m`,
`nodes := N.nodes ++ #[.input (N.nInputs + j), .and o s]` with `o` N's (single) output and `s`
the index of the new input node, `outputs := [the index of the new AND]`. N's input numbering is
unchanged. Lemmas (Physlib-free): `withControl_WF (hN : N.WF) (h1 : N.outputs.length = 1)
(hj : j < m) : (N.withControl m j).WF` and

```
theorem withControl_pred (hN : N.WF) (h1 : N.outputs.length = 1) (hj : j < m)
    (x : Fin (N.nInputs + m) → Bool) :
    (N.withControl m j).pred (N.nInputs + m) x =
      (x ⟨N.nInputs + j, by omega⟩ && N.pred N.nInputs (fun i => x (Fin.castAdd m i)))
```

(the values of the first `N.nodes.size` nodes do not change when nodes are appended — find or
prove that lemma for `Network.values`). If `Network.WF` requires a node layout `withControl`
cannot meet, stop and ask.

### B2. `Gate.shiftData` (`CQRV/Circuit/IR.lean`, a new definition next to `shiftBits`)

`Qubit.shiftData k : .data i ↦ .data (i + k)`, `.anc i` unchanged; `Gate.shiftData k` applies it
to every qubit operand, recursively under `ifBit`. Lemmas: `isUnitary_shiftData`, and `qubitsOk
m g → qubitsOk (k + m) (g.shiftData k)` for unitary data gates. Used only for the phase register.

### B3. The builders (`CQRV/Synthesis/Counting.lean`)

```
def controlledDiffusion (n m j : Nat) (shape : DiffusionShape := .tree)
    (mode : UncomputeMode := .mbu) : Except Diagnostic Circuit := do
  let mcz ← synthesizeOracle ((Diffusion.diffusionNet shape n).withControl m j) mode
  return ((⟨n + m, onAll .h n ++ onAll .x n⟩ : Circuit).append mcz).append
    ⟨n + m, onAll .x n ++ onAll .h n⟩

def controlledGrover (N : Network) (n m j : Nat) (shape := .tree) (mode := .mbu) :
    Except Diagnostic Circuit := do
  -- refuse with a diagnostic: N.nInputs ≠ n, N.outputs.length ≠ 1, j ≥ m, n = 0
  let o ← synthesizeOracle (N.withControl m j) mode
  let d ← controlledDiffusion n m j shape mode
  return (o.append d).append ⟨n + m, [.z (.data (n + j))]⟩      -- the phase fix, §A.3 (2)

def countingCircuit (N : Network) (n m : Nat) (kmax : Option Nat := none) (shape := .tree)
    (mode := .mbu) : Except Diagnostic Circuit
  -- H on all n + m data qubits; for j = 0..m−1, 2^j copies of controlledGrover N n m j;
  -- then ⟨n + m, (adjointGates (qftGates m or aqftGates m k)).map (Gate.shiftData n)⟩;
  -- refuse m = 0
```

Write `countingCircuit` so that the proof of B4 is direct (for instance a fold over `j` whose step
is `(List.replicate (2^j) b_j).foldl Circuit.append acc`); the gate list must be the one of
§A.3 (4). Diagnostics use the existing `Code`s (record which in DECISIONS); no new `Code`. No
few-ancilla or Bennett variant (no `aMax`).

### B4. Restoration in the circuit's own factors (`CQRV/Circuit/CountingCorrect.lean`, new)

- `unitaryDenote_hUpTo (N a k) (hk : k ≤ N) : unitaryDenote N a ((List.range k).map fun i =>
  Gate.h (.data i)) = hUpTo N k ⊗ₖ 1` — the local `key` of `unitaryDenote_hLayer`
  (Grover/Restore.lean:506) as a lemma of its own; the same for `X` with `flipUpTo` (the `key` of
  `unitaryDenote_xLayer`). The existing lemmas stay as they are.
- `dataMat N gs : Matrix (Reg N) (Reg N) ℂ := fun x y => unitaryDenote N 0 gs (x, reg0) (y, reg0)`
  and `unitaryDenote_dataOnly (gs) (hu : gs.all Gate.isUnitary = true) (hq : gs.all (Gate.qubitsOk
  N) = true) : unitaryDenote N a gs = dataMat N gs ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)` with
  `dataMat_mem_unitaryGroup` — gate by gate (`Qubit.get` / `Qubit.flip` of a `.data` qubit read and
  change only the first component). It covers the `z` fix and the shifted inverse QFT.
- `controlledDiffusion_ancRestore`, `controlledGrover_ancRestore`, and

```
theorem countingCircuit_ancRestore_raw
    (hC : countingCircuit N n m kmax shape mode = .ok C) (hN : N.WF) (hn : N.nInputs = n)
    (h1 : N.outputs.length = 1) :
    C.WF ∧ AncRestore (n + m) C.nAnc C (qftInvU n m kmax * powersU N n m shape mode * hadamardU (n + m))
```

  where `powersU` is the product, in program order, of `cgU j ^ (2^j)`, `cgU j := zU j * cdiffU j *
  phaseOracle ((N.withControl m j).pred (n + m))`, `cdiffU j := post * phaseOracle (((diffusionNet
  shape n).withControl m j).pred (n + m)) * pre` with `pre` / `post` the `hUpTo` / `flipUpTo`
  unitaries, and `zU`, `qftInvU` the `dataMat` unitaries of their layers. The factors are the
  exact matrices; `AncRestore.congr` is not used. Proof: Lemma 6.3.2 for the `withControl`
  networks (the variant the Grover certificates use for `N`, OracleCorrect.lean:1052–1169;
  `withControl` adds one AND node and no XOR), `ancRestore_of_dataLayer`, `ancRestore_hLayer`,
  `AncRestore.comp`, `ancRestore_foldl` (Grover/Restore.lean:825) once per `j`, `Circuit.WF_append`,
  `synthesizeOracle_WF'`, `nAnc_append`.

### B5. Harness and CI (`scripts/CertifyTool.lean counting-sample`, `tests/diff/counting_diff.py`, `scripts/diff_counting.sh`)

`CertifyTool counting-sample <file.cqr> <m> [--kmax k] [--shape tree|chain] [--uncompute
mbu|coherent]` prints one JSON object: the circuit (`Circuit.toJson`), the block table (name,
first gate, length, grade, grade_ext, `liveEnd`; distinct blocks once with their multiplicity),
the measured grade of the whole and the composed bound of 19a. Predicates: a few small DSL files
`tests/diff/counting/*.cqr`, n ≤ 6, with M covering 1, an odd value, 2^{n−1}, and M = 0 and
M = 2ⁿ if the DSL can express them (else say so); M computed in Python independently of the
synthesizer (as grover_diff does: "P is evaluated here"). `counting_diff.py`, for m = 1..4:

- (a) coherent mode, one branch from |0…0⟩: the phase-register distribution `P(y)` (y the phase
  register read with `data n` the MSB, marginal over the search register; the ancillae end in
  |0⟩) equals `½ (P_m(y; θ/π) + P_m(y; −θ/π))` to 1e−9, where `P_m(y; φ) = |2^{−m} ∑_{j<2^m}
  e^{2πi j (φ − y/2^m)}|²` and `sin²θ = M/2ⁿ`;
- (b) MBU mode, sampled branches (`statevector.run_ir_sampled`): each branch's final data state
  equals the coherent one (overlap ≥ 1 − 1e−9), ancillae |0⟩;
- (c) negative controls: every `z (data (n+j))` removed by the harness gives the shifted mixture
  `½ (P_m(y; ½ + θ/π) + P_m(y; ½ − θ/π))` and differs from (a) by more than 0.1 for a predicate
  with M/2ⁿ ≠ ½; the bit-reversed reading of the phase register fails the closed form for some
  m ≥ 2;
- (d) grades: measured ≤ composed componentwise (w, a, t equal; d ≤), `tDepth` within its bound,
  the `GradeExt` equalities; the block table replays to the circuit's gate list (with the bit
  shifts);
- (e) `kmax` (m = 4, kmax = 2, 3): the circuit is the exact one without the dropped shifted `cp`;
  the total-variation distance to the exact distribution is printed, no bound asserted
  (`η_aqft ≥ 2` for m ≤ 4, as in 18c).

If the harness shows a convention other than §A.3 (5) (another bit order, the phases at
`½ ± θ/π` with the fix present), **stop**: report both, change neither the harness nor the
circuit. `scripts/diff_counting.sh`; CI step "Counting circuit (Stage 19b)" after "QFT / AQFT" in
`scripts/ci_local.sh` **and** `.github/workflows/ci.yml`: **the pass mark becomes 18 PASS, 0 FAIL,
4 n/a**. Keep the step under about 3 minutes (fewer sampled branches, never fewer closed-form
checks).

### B6. The block probe (report only; `bench/counting/`, `docs/benchmarks/COUNTING_BLOCKS.md`)

For grover_pred_037 (n = 8, M = 32), m = 4, shape tree, both modes: the block table of
`counting-sample`, and a generated Lean file stating each **distinct** block as a literal with
`… = .ok block` (as `emitted_ok`) and its `grade_eq` / `gradeExt_eq` by `decide +kernel`, measured
per declaration with the 18a machinery (`scripts/kernel_forms.sh`: 900 s timeout, 8 GB kill).
Report: per block the gate count, grade, `GradeExt`, `liveEnd`, kernel time and peak memory; for
the whole circuit the gate count, the measured grade (compiled evaluation, not the kernel) and the
composed bound. Stop with "ready for the probe run"; the user runs it. Afterwards stop and ask if a
block exceeds 600 gates or a `grade_eq` 30 s (PHASE2_SPEC §A.3 item 4). Not in CI; no certificate.

### 19b Docs / Acceptance / Stop

Docs: DECISIONS.md entry (layout, phase fix, conjunction, the diagnostics, the predicates and the
conventions the harness confirmed, the probe table), `docs/PROJECT_STATUS.md` one line, no README
change. Reviewer files untouched.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; B1 and B4 proved (at most
`unitaryDenote_dataOnly` tracked, with its SORRIES entry); the harness passes with the convention
of §A.3 (5); COUNTING_BLOCKS.md written.

Stop and ask: the harness convention differs (above); Lemma 6.3.2 or an existing builder needs a
change; a block above 600 gates; a second `sorry`.

---

## 19c — The tensor form of `U_count` (after 19b is accepted; `CQRV/Circuit/CountingCorrect.lean`)

**Notes added at the 19b review (2026-11-05).** They use the names 19b actually has; where they
differ from the sections below, these notes win.

(i) *The factors to rewrite.* `preU n m = flipUpToU (n+m) n * hUpToU (n+m) n _`, `postU n m =
hUpToU (n+m) n _ * flipUpToU (n+m) n`, `cdiffU n m j shape = postU * phaseOracle (((diffusionNet
shape n).withControl m j).pred (n+m)) * preU`, `zU n m j = dataMatU (n+m) [.z (.data (n+j))]`,
`cgU N n m j shape = zU * cdiffU * phaseOracle ((N.withControl m j).pred (n+m))`, `qftInvU n m
kmax = dataMatU (n+m) (countingInverse n m kmax).gates`, `powersUpTo` and `powersU N n m shape`
(no `mode` argument). `countingCircuit_ancRestore_raw` stays as committed.

(ii) *C2.* The X layer is `flipUpToMat (n+m) n`. Prove the entry formula of `zU` as a lemma about
`dataMat`. The shift lemma may take `gs.all Gate.dataOnly = true` in addition to, or instead of,
`qubitsOk m`, whichever the proof needs: the 19b correction to `unitaryDenote_dataOnly` showed
that `qubitsOk` admits ancilla operands. Its client, `inverseGates`, satisfies both.

(iii) *C4.* Prove the `ctrlPow` product through `powersUpTo` in a partial form: for `j ≤ m`,
`powersUpTo … j = ` the matrix with `[phase x = phase y] · (G ^ (∑_{i<j} [phase x i] 2^i)) (search
x) (search y)`; `j = m` is `ctrlPow G` by `toNatLE_eq_sum_range`.

(iv) *C5.* `dataMat m (adjointGates gs) = star (dataMat m gs)` for a unitary `gs` is a small lemma
from `unitaryDenote_adjoint` at `a = 0`. `kmax = none` is `qftGates m` and `kmax = some k` is
`aqftGates m k`; `inverseGates m kmax` is already that case split.

(v) *Types.* State every intermediate result in the form `Fin (n + m)` with `subst` of `N.nInputs =
n` done first: the 19b tests found that an `example` writing `Fin 6` for `Fin (n4.nInputs + 2)`
times out at `whnf`. Lemmas must not mention `Fin.cast` where `subst` avoids it.

### C1. Coordinates and matrices

`search x : Reg n := fun i => x (Fin.castAdd m i)`, `phase x : Reg m := fun j => x (Fin.natAdd n
j)` for `x : Reg (n + m)`; entrywise, with `[·]` the indicator:

```
liftS A x y    = [phase x = phase y] · A (search x) (search y)
liftP B x y    = [search x = search y] · B (phase x) (phase y)
ctrlU j V x y  = [phase x = phase y] · (if phase x j then V else 1) (search x) (search y)
ctrlPow V x y  = [phase x = phase y] · (V ^ (phase x).toNatLE) (search x) (search y)
```

with unitary-group membership for unitary arguments.

### C2. The layers

`hUpTo (n+m) n = liftS (hadamardMat n)`; the `flipUpTo` layer `= liftS (xAllMat n)`; `dataMat
(n+m) [z (data (n+j))] = zU j` (diagonal, `−1` where `phase x j`); the shift lemma `dataMat (n+m)
(gs.map (Gate.shiftData n)) = liftP (dataMat m gs)` for unitary `gs` with `qubitsOk m` (gate by
gate; the inverse (A)QFT is the client).

### C3. The oracles

`phaseOracle ((N.withControl m j).pred (n+m)) = ctrlU j (phaseOracle (N.pred n))` from
`withControl_pred` (`subst` `N.nInputs = n` first); the same for `diffusionNet shape n` with its
`pred` lemma (`treeNet_pred` for `tree`).

### C4. The algebra

`ctrlU j A * ctrlU j B = ctrlU j (A * B)`; `liftS A * ctrlU j B * liftS A' = ctrlU j (A * B * A')`
when `A * A' = 1`; `zU j * ctrlU j (−V) = ctrlU j V`; `(ctrlU j V) ^ r = ctrlU j (V ^ r)`; the
product in program order of `(ctrlU j G) ^ (2^j)` over `j < m` is `ctrlPow G` (induction on the
number of factors with `toNatLE_eq_sum_range`, Basis.lean). Hence `cdiffU j = ctrlU j (−diffU n)`
(`diffusion_circuit_matrix`) and `cgU j = ctrlU j (groverOp (N.pred n))`.

### C5. The theorem

```
def U_count (P : Reg n → Bool) (m : ℕ) (kmax : Option ℕ) : 𝐔[Reg (n + m)]
  -- liftP (star (dataMat m (qftGates m))) * ctrlPow (groverOp P) * hadamardMat (n + m), resp. aqftGates
theorem countingCircuit_ancRestore
    (hC : countingCircuit N n m kmax shape mode = .ok C) (hN : N.WF) (hn : N.nInputs = n)
    (h1 : N.outputs.length = 1) :
    C.WF ∧ AncRestore (n + m) C.nAnc C (U_count (N.pred n) m kmax)
```

from `countingCircuit_ancRestore_raw` by rewriting the factors with C2–C4 (equalities of unitaries,
not `AncRestore.congr`). This is the form Stage 20a starts from.

### 19c Tests / Docs / Acceptance / Stop

Tests: `example` instances at n = 2, m = 2; `#guard_msgs` axiom checks of `countingCircuit_ancRestore`
and the C4 product lemma. Docs: DECISIONS.md entry, SORRIES.md for anything tracked,
`docs/PROJECT_STATUS.md`, README status line ("Stages 0–19c"). Reviewer files untouched.

Acceptance: `lake build` green; CI 18 PASS; `countingCircuit_ancRestore` proved modulo at most
two tracked sub-lemmas, named in advance: the shift lemma of C2 and the `ctrlPow` product of C4;
the 19b raw theorem and every other statement unchanged.

Stop and ask: a statement needs a hypothesis not listed here; a third `sorry`; the raw theorem of
19b would have to change.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests — 19a: CI summary, the axiom lines, the
counterexample, grover_pred_037's iteration measured vs composed; 19b: CI summary, the harness's
largest closed-form error and the negative controls, the probe table; 19c: CI summary, the axiom
lines, what is tracked —, (d) SORRIES.md, (e) open questions.
