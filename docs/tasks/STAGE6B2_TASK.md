# Stage 6b-2 — Basis-vector lemmas for the oracle blocks (compute lift, MBU branch, Z phase)

Report sections: §6.2.2 (TempLogicalAND / MBU), §6.2.4 (Layer 1: per-AND lemmas; Layer 3:
factorization), §6.1.4 (Z on the ancilla holding P(x)), §6.3.2 (Lemma 6.3.2).
Precondition: 6b-1 closed (main = 801b310). `git switch -c stage-6b2 main`; one commit; include
this file (untracked) in it. Windows: `LEAN_NUM_THREADS=4`. Module system. **Proof stage**, 3
build–fix rounds per item; a stuck item becomes a tracked `sorry` with the goal verbatim.

## The proof route for `lemma_6_3_2` (reviewer's plan — 6b-2 builds the parts, 6b-3 assembles)

`ancRestore_of_kraus` (6b-1) reduces Lemma 6.3.2 to one fact about **every** Kraus branch `c`
on basis inputs: `K_c |x, 0…0⟩ = 2^{-k/2} · (−1)^{P(x)} · |x, 0…0⟩` (k = number of ANDs).
That fact follows block by block on basis vectors, with no superpositions to track:
- **compute** (TempLogicalAND a b t, t = 0): `|s⟩ ↦ |s[t ↦ s a && s b]⟩` (phase 1);
- **Z t**: `|s⟩ ↦ (−1)^{s t} |s⟩`;
- **MBU branch** (H t; measure t; if m: CZ a b; if m: X t), when `s t = s a && s b`: in **both**
  branches `|s⟩ ↦ (1/√2) |s[t ↦ false]⟩` — no sign. Check: after H the |1⟩ coefficient is
  `(−1)^{s t}/√2`; the fix-up CZ multiplies by `(−1)^{s a · s b} = (−1)^{s t}`, so it is `+1/√2`;
  `X t` resets. Branch 0 is `+1/√2` directly.
- X gates on data (NOT polarity) are permutations of basis states.
The phase therefore appears exactly once (at Z), every MBU contributes a branch-independent
`1/√2`, and `Σ_c ‖2^{-k/2}‖² = 2^k · 2^{-k} = 1`. (Channel composition from 6b-1 is not needed
on this route; keep it — it is proved and will serve Stage 7.)

## Tasks (`CQRV/Circuit/OracleBlocks.lean`; doc-comment each with its §)

0. **`Circuit.WF_append`** (6b-1 open question 2): `C₁.nData = C₂.nData → C₁.WF → C₂.WF →
   (C₁.append C₂).WF` — prove (qubit ranges are preserved; bits via `bitsOk_append`).
1. **Kraus on a gate list, basis form.** A lemma that `krausOps` of a concatenation applied to a
   vector is the product of the parts' Kraus operators for the matching slices of the branch
   assignment (you have `krausOps_append` for one gate; extend to lists with the shifted-bit
   convention of 6b-1). State it so blocks can be chained with `mulVec`.
2. **`tempLogicalAND_correct_lift` — prove** (closes its tracked `sorry`): distinct, in-range
   `a b t`, basis state `s` with `t.get s = false` ⇒ `unitaryDenote n m (TempLogicalAND a b t)
   *ᵥ basisVec s = basisVec (t.set (a.get s && b.get s) s)`. Go gate by gate with the
   `get/set/flip` lemmas and `gateU_*_mulVec`; the two H gates on `t` create a two-term sum —
   track it as `α • basisVec s₀ + β • basisVec s₁`. Do **not** enumerate registers. If the
   generic proof is stuck after 3 rounds, prove a locality lemma instead (a gate list touching
   only `{a, b, t}` acts on `basisVec s` through the 3-qubit action with the other bits fixed)
   and derive the lift from the proved 3-qubit `tempLogicalAND_correct`.
3. **`mbu_branch_basis` — prove:** for the uncompute block with its classical bit `j` and any
   branch assignment `c`, if `t.get s = (a.get s && b.get s)` then
   `K_c *ᵥ basisVec s = (1/√2 : ℂ) • basisVec (t.set false s)`.
4. **`z_basis` — prove:** `gateU (.z t) *ᵥ basisVec s = (if t.get s then -1 else 1) • basisVec s`;
   and the X-gate (NOT polarity) basis lemma if not already present.
5. **SORRIES.md**: close `tempLogicalAND_correct_lift` (hash in a follow-up line or next
   commit, as before); update the `lemma_6_3_2` row's "Depends on" to the route above
   (6b-3: induction over the synthesizer's AND list using items 1–4 + `ancRestore_of_kraus`).

## Tests

`tests/CQRVTests/Semantics.lean`: `#print axioms` for every new theorem (only the three standard
axioms). One concrete `example`: on the 3-qubit register, `mbu_branch_basis` instantiated at
`s = |1,1,1⟩` for both branches (by the lemma, not by recomputation).

## Acceptance

- `lake build` green, check scripts pass, `diff_oracles.sh` still 101/101 (nothing in the
  synthesizer should change).
- Proved: items 0, 2, 3, 4 (and 1 in whatever form 6b-3 needs). SORRIES.md: lift closed.
- DECISIONS.md: the basis-vector route for Lemma 6.3.2 (rejected: induction via channel
  composition — nested compute/uncompute brackets do not split into independent restoring blocks).

## Stop conditions

- `mbu_branch_basis` is false for some branch (it would contradict the hand check above and the
  harness) → stop and report the computed vector.
- Do not start the induction over the AND list (6b-3) and do not touch `lemma_6_3_2`'s proof.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the exact statement shape of item 1 that 6b-3 will
chain, and whether the lift went generic or through the locality lemma.
