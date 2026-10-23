# Stage 6b-3 — Lemma 6.3.2 for xor-free networks: induction over the synthesizer

Report sections: §6.3.2 (Lemma 6.3.2), §6.2.4 (Layers 1–3), §6.1.1/§6.1.4 (Z on the ancilla
holding P(x)), §6.2.2 (MBU). Precondition: 6b-2 accepted (main = a3586f4).
`git switch -c stage-6b3 main`; include this file (untracked) in the commit. Put the closing hash
of `tempLogicalAND_correct_lift` (a3586f4) into SORRIES.md in this commit.
Windows: `LEAN_NUM_THREADS=4`. Module system. **Proof stage.** This is the largest proof so far:
work item by item, build after each, 3 build–fix rounds per item. If an item is stuck, leave it
as a tracked `sorry` **with its own SORRIES.md row** (goal verbatim) and continue with the next
item that does not depend on it — `lemma_6_3_2` may then close modulo named sub-lemmas, which is
progress the reviewer can audit.

## What the synthesizer does on an xor-free network (read `CQRV/Synthesis/Oracle.lean`)

With `N.xorFree`, every `Aff` in `st.vals` has `lin` of length ≤ 1 (an input bit, an AND
ancilla, or empty = constant), so `gather` emits nothing and `prepare` emits only the polarity
`X` gates. Each non-folded AND k gets the fresh ancilla `t_k = anc k`, the compute block
`pre_k ++ [alloc t_k] ++ TempLogicalAND pu pv t_k ++ pre_kᴿ` and the uncompute block
`pre_k ++ Uncompute… pu pv t_k 0 ++ [free t_k] ++ pre_kᴿ` (shifted to its bit). `phaseFlip` is
`[X q]? ++ [Z q] ++ [X q]?` on the single atom `q` of P (nothing for a constant P).

## Reviewer decisions (record in DECISIONS.md)

1. **Proof-only bookkeeping is allowed in `St`** (e.g. an array of `(pu, pv, t, u, v)` per
   non-folded AND) **if the emitted circuit is unchanged**: before and after, the JSON of
   `cqr synthesize --json` on the three corpus files and on 20 random predicates from
   `oracle_diff.py`'s generator must be byte-identical (script it, keep the script), and
   `diff_oracles.sh` stays 101/101. Rejected: changing the gate sequence to ease the proof.
2. **Monadic fold.** Reason about `foldlM` over `Except` with an invariant lemma
   (`List.foldlM` induction); if `synthesizeOracle N = .ok C`, every `step` returned `.ok`.
   Prefer a lemma `step_ok_inv : step … st k = .ok st' → Inv k st → Inv (k+1) st'`.

## Tasks (`CQRV/Circuit/OracleCorrect.lean`; doc-comment each with its §)

1. **Atom semantics.** For a data basis input `x : Reg n`, `atomState x : Reg n × Reg m` = data
   `x`, ancilla `k` = the value of the k-th non-folded AND on `x`. `Aff.eval` of an `Aff` on a
   register state. `N.pred` / node evaluation as already defined in `Network.lean`.
2. **Invariant `Inv k st`** (xor-free): for every node `i < k` in the cone, `st.vals[i] = some u`
   with `u.lin.length ≤ 1` and `u.eval (atomState x) = node value of i on x`; `st.nextAnc` =
   number of non-folded ANDs among nodes `< k`; each recorded `(pu, pv, t)` has `t = anc j` for
   its index `j`, `pu ≠ pv`, `pu, pv ≠ t`, and `pu, pv` are data qubits or ancillas `< j`.
   Prove `step_ok_inv` and conclude `Inv` for the final state. (Folding identities: prove that
   `fold u v = some r → r.eval = u.eval && v.eval` on every state.)
3. **Compute part.** All compute blocks together are unitary (no measurement) and map
   `basisVec (x, 0)` to `basisVec (atomState x)` — induction over the blocks with
   `tempLogicalAND_kraus_basis` (6b-2), the X-polarity lemma (the `pre`/`preᴿ` X gates cancel
   and make the controls hold `u`, `v`), and the 6b-2 chaining lemma.
4. **Phase.** `phaseFlip p` maps `basisVec (atomState x)` to `(−1)^{P(x)} • basisVec (atomState x)`
   (`z_basis`, `x_basis`; constant P: no gate, and P is constant on all x — check the global phase
   is then `±1` and fits `ancRestore_of_kraus`, or state the constant case separately).
5. **Uncompute part.** For every branch `c`, the uncompute blocks (reverse order, shifted bits)
   map `basisVec (atomState x)` to `(√2)⁻¹ ^ K • basisVec (x, 0)` (K = number of non-folded ANDs):
   induction from the last AND down, using `mbu_branch_basis` (its hypothesis
   `t = u ∧ v` holds because ancillas `> j` are already reset and atoms `< j` are intact).
6. **Assembly — `lemma_6_3_2`.** From 3–5: `krausOps … c * ancProj = l c • (phaseOracle P ⊗ₖ
   ancZero.m)` with `l c = (√2)⁻¹ ^ K` (check on basis vectors `(x, y)`: `y ≠ 0` is killed by the
   projector), `Σ_c ‖l c‖² = 2^K · 2^{-K} = 1`, and `ancRestore_of_kraus`. Also needs
   `C.nAnc = K` (or whatever the circuit's ancilla count is) — prove it from `Inv`.
   **Remove the `sorry`** of `lemma_6_3_2`; `grover_pred_037_ancRestore` and
   `lemma_6_3_2_traced` then become sorry-free automatically.

## Tests

- `#print axioms lemma_6_3_2`, `grover_pred_037_ancRestore`, `lemma_6_3_2_traced`: if all items
  closed, only `propext`, `Classical.choice`, `Quot.sound` — paste the lines. Otherwise paste
  them anyway (they will show `sorryAx`) and list which sub-lemma rows remain.
- The byte-identical JSON script of decision 1, run in CI next to `diff_oracles.sh`.

## Acceptance

- `lake build` green, check scripts pass, `diff_oracles.sh` 101/101, JSON identical.
- `lemma_6_3_2` proved, **or** reduced to named sub-lemmas each with its own SORRIES.md row.
- SORRIES.md: lift closed with a3586f4; `lemma_6_3_2` closed (this commit's hash in a follow-up)
  or its row rewritten to point at the remaining sub-lemma rows.

## Stop conditions

- The invariant turns out false for some synthesized circuit (e.g. an operand qubit equal to the
  target, or `pu = pv` after folding) → stop and report the network; it would be a synthesizer
  bug the harness missed.
- Do not touch `lemma_6_3_2_xor`, the diffusion operator, or Stage 7/8.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which of items 1–6 closed, the remaining sub-lemma rows
(if any), and whether the bookkeeping of decision 1 was needed.
