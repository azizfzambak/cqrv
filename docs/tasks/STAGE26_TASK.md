# Stage 26 — The witness in Lean and the physical grade (PHASE2_SPEC §C.3; Track C, Paper 1)

PHASE2_SPEC.md §C.3. Report: §5.3, §3.1.3, §9.1.1. PHASE2_ROADMAP row 26. Written at the 25b review
(2026-11-15) by the reviewer, under the author's delegation.

Stage 26 has three tasks, one commit each:
- **26a**, the embedding and the translation, is specified here;
- **26b**, routing and `applyWitness_sound`, and **26c**, the per-instance checks, the physical
  grade and the physical certificate, are outlined and detailed at the review of the task before.

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

## 26b — Routing and `applyWitness_sound` (outline)

- Qubit relabeling and its channel lemma; SWAP as a permutation.
- `gateK_comm_of_disjoint` and the reordering lemma for a topological order over qubits and
  classical bits.
- The witness reader (Physlib-free), `applyWitness`, and `applyWitness_sound`.
- The transfer theorems for `Realizes` and `AncRestore` under the final-layout permutation.

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
