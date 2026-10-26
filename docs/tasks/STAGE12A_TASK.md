# Stage 12a (improvement 3, part 1) — balanced-tree diffusion: cut the depth, keep the proof

Report sections: §8.2 (`U_s = H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}`), §6.1.4 (diffusion), §3.3.3 / Table 3.5
(Kyiv depth budget ~200), §6.3.2 (Lemma 6.3.2 covers every xor-free network).
Precondition: Stage 11b accepted (main = 11b review commit). `git switch -c stage-12a main`; one
commit; include this file (untracked); leave `docs/tasks/STAGE12B_TASK.md` untracked.
Windows: `LEAN_NUM_THREADS=4`. Repository stays sorry-free.

## Why this first (reviewer)

The Grover slice misses the Kyiv depth budget (230 > 200) because the V1 diffusion's MCZ is the
phase oracle of a **chain** `((y₀ ∧ y₁) ∧ y₂) ∧ … ∧ y₇` — 7 ANDs strictly in sequence (depth 89).
The same predicate as a **balanced tree** `((y₀∧y₁)∧(y₂∧y₃))∧((y₄∧y₅)∧(y₆∧y₇))` has the same 7 ANDs
(T = 28, a = 7, w = 15 unchanged) but only 3 AND levels, and the ASAP scheduler runs ANDs on
disjoint qubits in parallel. Expected: diffusion depth well below 89 and Grover depth under 200 —
**to be measured, not assumed**. Correctness needs **no new restoration proof**: Lemma 6.3.2 holds
for every xor-free network the synthesizer accepts (`lemma_6_3_2_xor`, `synthesizeOracle_WF`); only
the fact "the tree computes y₀ ∧ … ∧ y₇" is new.

## Reviewer decisions (record in DECISIONS.md)

1. `treeNet n` (Synthesis/Diffusion.lean): AND nodes pairing inputs level by level (odd leftover
   carried up), one output; `treeNet_pred : (treeNet n).pred n = P_all` — prove (structural, by
   induction on levels or by an explicit evaluation lemma), and `treeNet_WF : n ≠ 0 → (treeNet n).WF`.
2. **Generalize `DiffusionCert` backward-compatibly**: today `hN : mcz.N = allNet n`. Add a second
   constructor path — e.g. a field `hPred : mcz.N.pred n = P_all` (with `allNet` and `treeNet` both
   providing it) — so every existing caller and the committed `Cert.lean` files keep building
   unchanged. If that cannot be done without editing the generated files, stop and propose.
3. **Default diffusion becomes the tree** (`diffusion n none` = tree V1; keep the chain as
   `--diffusion chain`). This changes the Grover circuit, its grade, hash and certificate:
   regenerate both committed example certificates **deliberately**, record old → new grade and
   hashes in DECISIONS.md, and update `docs/M2_REPORT.md` only by a dated post-M2 line.
4. Measure, do not tune: the decision-4 scheduler of Stage 5 unchanged.

## Tasks

1. `treeNet`, `treeNet_pred`, `treeNet_WF` (decision 1); `#guard` that the tree has n − 1 AND nodes.
2. `DiffusionCert` generalization (decision 2) and the generator path for the tree.
3. CLI: `cqr synthesize --diffusion n [--shape tree|chain]`, `--grover` uses the tree by default.
4. Harness: tree diffusion and the full Grover circuit through `diff_grover` (all branches for one
   iteration; success probability exactly 121/128 for grover_pred_037, 1215/2048 for the ALU).
5. Regenerate both example certificates (decision 3); `cqr certify … --profile ibm_kyiv` for both.

## What to report (measured)

| Object | V1 chain (today) | V1 tree (measure) |
|---|---|---|
| D₈ | (15, 89, 28, 7) | ? |
| Grover iteration | (15, 116, 36, 7) | ? |
| Grover r⋆ = 2 | (15, 230, 72, 7) | ? |
| Kyiv depth check | exceeds (230 > 200) | ? |
| ALU r⋆ = 1 | (16, 145, 60, 10) | ? |

## Acceptance

- `lake build` green, sorry-free; `#print axioms` (guarded) for `treeNet_pred`, `treeNet_WF` and
  the regenerated certificates: standard three only.
- `scripts/ci_local.sh` all PASS (if step 19 runs out of memory, run `scripts/check_certify.sh`
  alone and paste it); both certificates `certified (conditional on: …)`.
- The table above filled; Kyiv line for Grover pasted.

## Stop conditions

- The measured tree depth is not lower than the chain's → stop and report (then 12a is not worth
  the certificate churn).
- Any existing statement would have to change → stop and propose.
- Do not start the 2-ancilla relative-phase MCZ (12b).

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the filled table, the Kyiv line, and the old → new hashes.
