# Stage 26 — The witness in Lean and the physical grade (PHASE2_SPEC §C.3; Track C, Paper 1)

PHASE2_SPEC.md §C.3. Report: §5.3, §3.1.3, §9.1.1. PHASE2_ROADMAP row 26. Written at the 25b review
(2026-11-15) by the reviewer, under the author's delegation.

Stage 26 has three tasks, one commit each:
- **26a**, the embedding and the translation, is specified here;
- **26b**, routing and `applyWitness_sound`, is specified below (written at the 26a review);
- **26c**, the per-instance checks, the physical grade and the physical certificate, is outlined and
  gets its detailed text at the 26b review.

Precondition: main = the 25b review commit. Start with `git switch -c stage-26a main`.

**Invariants of Stage 26:**
- No existing theorem statement changes; `Circuit.WF`, `channelDenote` and `Gate.isClifford` are
  unchanged.
- No committed certificate is regenerated before 26c, and in 26c none of the existing ones is
  regenerated (the physical certificate is new).
- The outputs of the existing `cqr` subcommands are byte-identical.
- The `cqr` closure stays Lean core + Mathlib: the data parts (the table, the translation, the
  witness reader) are Physlib-free, and the proofs are Physlib-side.
- No `sorry`.
- No new download.
- If a statement here is false, give the counterexample and the corrected form.
- CLAUDE.md rule 2.

---

## 26a — The embedding, the Lean table, `decomp_sound`, `translate_sound`

### W1. Data (`CQRV/Hardware/Decomp.lean`, Physlib-free)

- **`BasisGate`.**
  - `rz (a : Int) (k : Nat) q` (angle 2πa/2^k), `sx q`, `x q`, `cz a b`, `cx c t`;
  - `measure q j`, `ifBit j BasisGate`.
- **`TargetBasis`** (cz or cx), reused from 24c.
- **`expand : BasisGate → List Gate`.** `sx` ↦ [h, s, h]; `rz a k` ↦ [p a k]; `x`, `cz` ↦
  themselves; `cx` ↦ cnot; `measure` and `ifBit` map structurally (an `ifBit` over a multi-gate
  expansion becomes the list of `ifBit`s).
  - The expansion of a conditioned basis gate is a list of conditioned IR gates. Every IR gate
    under `ifBit` must be Clifford for `Circuit.WF`: h, s and the Clifford `p` are, but
    `p a k` for a non-Clifford angle is not. So a conditioned `rz` with a non-Clifford angle is
    not expressible in a well-formed IR circuit, exactly as in the IR itself. State what the
    table does for such gates (they do not occur under `ifBit` in the IR, by `Circuit.WF`).
- **`decompTable : TargetBasis → Gate → List BasisGate × (ℤ × ℕ)`.** The table of
  `hw/decomp.py`, entry for entry, with the phase φ as a dyadic fraction of a turn (−1/8, ±1/16,
  −a/2^(k+1), …).
- **`translate : TargetBasis → Circuit → List BasisGate`**, gate by gate, keeping conditions.
- **`cqr hw table --basis cz|cx`** prints the Lean table as JSON in `hw/decomp.py`'s format.

### W2. Proofs (`CQRV/Hardware/DecompSound.lean`, Physlib-side)

- **`decomp_sound`.** For every IR gate g that the table covers, and every basis b:
  `unitaryDenote n a ((decompTable b g).1.flatMap expand) = exp(2πiφ) • gateU n a g`.
  - Prove it per entry, on in-range qubits, through the existing gate lemmas (`monoMat`, `hMat`,
    and the phase lemmas of `Semantics.lean`).
  - For `p` and `cp` it holds for every a, k, as a parametric statement, not per angle.
- **`translate_sound`.** For a well-formed IR circuit C, the IR circuit
  `⟨C.nData, (translate b C).flatMap expand⟩` is well formed and has the same `channelDenote`.
  - Per-branch global phases cancel in K_c ρ K_cᴴ.
  - State the needed lemma: a unit scalar on a gate scales every Kraus operator it belongs to by
    a unit scalar, and leaves the channel unchanged.
- **Corollaries.** `AncRestore` and `Realizes` (through `groverChannel`) transfer from C to its
  translation.

### W3. Checks

- **`tests/CQRVTests/HardwareDecomp.lean`:** the axioms of `decomp_sound` and `translate_sound`
  (`#guard_msgs`); `translate` on the MBU gadget; the transfer of `mbu_channel_correct` to the
  translated gadget, as an example.
- **The two tables agree.** `tests/diff/hw_transpile_check.py` (or a new `hw_table_check.py`)
  compares `cqr hw table --basis cz` and `--basis cx` with `hw/decomp.py`'s table: the entries
  and the phases, exactly. They then agree by construction, and 25a's reconstruction uses the
  table Lean proves.
- **CI.** The table comparison joins an existing hardware step; the pass mark stays 23.

### 26a Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 23 PASS, 0 FAIL, 4 n/a;
- the axioms the standard three;
- the tables identical.

Stop and ask in any of these cases:
- a table entry's phase in Lean differs from Python's; report the entry;
- the global-phase lemma does not hold for conditioned gates as stated;
- a single proof above about 400 lines.

---

## 26b — Routing and `applyWitness_sound` (written at the 26a review, 2026-11-15)

PHASE2_SPEC §C.3 (step 2, routing, and step 3, assembly), and the "26a done" paragraph.
Precondition: main = the 26a review commit. Start with `git switch -c stage-26b main`. The
invariants of Stage 26 hold.

**The physical register** is the compact register of the used qubits, N = |used qubits|, 3–17 for
the committed artifacts. Everything is stated on `Reg N` with no ancilla part: the physical
circuit is an IR circuit with nData = N and nAnc = 0. The logical register `Reg n × Reg a` enters
through an injection.

### X1. Relabeling, SWAP, embedding (`CQRV/Hardware/Route.lean`, Physlib-side; data parts Physlib-free)

- **`permMat σ`.** For a permutation σ of the qubit positions of a register, `permMat σ` is
  `monoMat` of the induced permutation of basis states.
- **`Gate.relabel σ` and `Circuit.relabel σ`** rename the qubits.
- **`channelDenote_relabel`.** The relabeled circuit's channel is Ad(permMat σ) ∘ channel ∘
  Ad(permMat σ⁻¹). It goes through `gateU_relabel`: `permMat σ * gateU g * (permMat σ)ᴴ =
  gateU (g.relabel σ)`, per gate type.
- **`ud_swapEntry`.** The expansion of the table's SWAP entry is irPhase • permMat (p q), the
  transposition, in both bases.
- **`embed`.** For an injection ι from the logical qubits (data, then ancillas) into Fin N, a
  logical state ρ on `Reg n × Reg a` becomes a state on `Reg N`: ρ at the positions ι(…), |0⟩ at
  the other positions, as a permuted tensor with |0…0⟩. This generalizes 23a's widening.
- **`channelDenote_embed`.** A logical circuit relabeled by ι and run on `Reg N` has the channel
  "embed after the logical channel" on embedded inputs.
- **`translateCircuit_nAnc`.** `(translateCircuit b C).nAnc = C.nAnc` in general (the 26a open
  item).

### X2. Commutation and reordering

- **`gateK_comm_of_disjoint`.** Two gates whose qubit sets are disjoint, and that share no
  classical bit (a `measure` writing j and an `ifBit` reading j share j), have commuting `gateK`
  in every branch.
- **`krausOps_reorder`.** If a list `gs'` is a reordering of `gs` in which every element, when
  taken, is at the head of every dependency queue it touches (the queues per qubit and per
  classical bit, as the Python matcher accepts them), then the Kraus operators are equal in every
  branch, hence the channels.
  - State the queue condition as a Boolean function that the kernel can evaluate per instance
    (`validReorder`).
  - Prove that `validReorder gs gs' = true` implies the equality: an induction that moves each
    taken element to the front through commuting neighbours.

### X3. The witness and the assembly (`CQRV/Hardware/Witness.lean`, data Physlib-free; proofs Physlib-side)

- **`Witness`.** It has the fields of `docs/hw_witness.schema.json`, as far as the reconstruction
  needs them:
  - the initial layout (logical → compact physical);
  - `order`, with gate entries and SWAP entries, and `blocks` for `if_test` bodies;
  - the final layout;
  - the classical-bit map;
  - the table basis.

  `Witness.ofJson` reads it, with the compact remapping of the manifest's `layout.used_qubits`.
- **`applyWitness b C w : Except String (List BasisGate)`.** The reconstruction of 25a in Lean: a
  fold over `order` with the current layout, relabeled basis gates, SWAPs expanded by the table,
  blocks processed recursively, and `validReorder` checked. Any mismatch is an error naming the
  entry.
- **`applyWitness_sound`.** If C is well formed and `applyWitness b C w = .ok G`, then for every
  logical state ρ:
  `channelDenote N 0 ⟨N, G.flatMap expand⟩ (embed ι ρ) = Ad(permMat π_final) (embed ι
  (channelDenote n a C ρ))`.
  Here ι is the initial layout and π_final the permutation from the initial to the final layout.
  The proof is `translate_sound`, then the relabeling, then moving each SWAP to the end through
  `channelDenote_relabel` (G · SWAP = SWAP · G relabeled), then `krausOps_reorder`.
- **The transfer theorems:**
  - `AncRestore.phys`: if `AncRestore n a C U`, the physical circuit on embedded clean inputs
    outputs Ad(permMat π_final)(embed ι ((U ρ Uᴴ) ⊗ |0…0⟩)).
  - `realizes_phys`: for a Grover certificate's `RealizesExact`, the same with the decoding POVM
    permuted by π_final.

### X4. Tests

**`tests/CQRVTests/HardwareRoute.lean`:**
- the axioms of `channelDenote_relabel`, `ud_swapEntry`, `krausOps_reorder` and
  `applyWitness_sound`;
- `applyWitness` on the MBU gadget artifact's witness (inline, small), equal to its physical
  circuit by `decide`;
- the transfer of `mbu_channel_correct` to that physical circuit.

The per-instance kernel checks on all 12 artifacts are 26c.

### 26b Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 23 PASS, 0 FAIL, 4 n/a;
- the axioms the standard three.

Stop and ask in any of these cases:
- the module set passes about 1 200 lines (propose the split: 26b1 X1, 26b2 X2–X3);
- `validReorder` as the matcher defines it does not suffice for `krausOps_reorder` (report the
  missing condition);
- a statement of mine is false (give the counterexample and the corrected form);
- a single proof above about 400 lines.

### 26b2 — X2–X3 (note added at the 26b1 review, 2026-11-16)

26b was split at its guard: 26b1 = X1 (accepted), 26b2 = X2 (commutation and reordering) and X3
(the witness, `applyWitness`, `applyWitness_sound`, the transfers), with X4's remaining tests.
They are specified above, unchanged. Use 26b1's names: `channelDenote_relabel`, `ud_swapEntry`,
`channelDenote_embed`, `physOf`, `embed`, and the compact register `Reg (n + (a + b)) × Reg 0`.
- The reconstruction's Kraus operators are unit scalars times the relabeled ones: the −i of each
  cz-basis SWAP is cancelled by 26a's `channelDenote_eq_of_kraus_smul`.
- Discharge `nAnc_translate`'s hypothesis by `decide` on `ancCovered`.
- The precondition is main = the 26b1 review commit, on the same branch name `stage-26b` or a new
  `stage-26b2`; say which.

### 26b3 — `applyWitness_sound` and the transfers (note added at the 26b2 review, 2026-11-16)

26b2 stopped at its guard; 26b3 completes X3 and X4 of the 26b text. Precondition: main = the 26b2
review commit; start with `git switch -c stage-26b3 main`.
- **`krausOps_swap_migrate_ifBit`**, the conditioned form, and the composition of the
  layout-tracked relabelings: `swapLay` against `swapPerm`, from the initial layout to the final
  one.
- **`applyWitness_sound`**, by the five steps of PHASE2_SPEC "26b2 done": for a well-formed C
  with `ancCovered` and `applyWitness b C w N = .ok G`,
  `channelDenote N 0 (physCircuit N G) (embed b σ₀ ρ) = embed b σ_f (channelDenote n a C ρ)`.
- **The transfers.** `AncRestore.phys`, `realizes_phys`, and `gadgetPhys_correct`:
  `mbu_channel_correct` transferred to the artifact's physical circuit through
  `applyWitness_sound`, not through 26b1's hand placement.
- **The guards.** The same guards: a single proof above about 500 lines (this is the one proof
  allowed to approach it), or a missing hypothesis, means stop and report.

## 26c — Per-instance checks, the physical grade, the physical certificate (outline)

- The kernel check of the reconstruction against the exported physical circuit, and of the
  coupling edges.
- `PhysGrade` with the ASAP timing model and a named feed-forward latency.
- The physical certificate generator and the committed physical certificate of grover_pred_037
  (tree mbu) on FakeTorino.
- The status words.
- Selection by the physical grade.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
