# Stage 13a — KG Theorem 5.1 for all n: the few-ancilla MCZ restores for every n

Report sections: §6.2 (restoration co-equal), §6.3.2, §8.2, §9.5.2. Source: Khattar–Gidney,
Quantum 9, 1752 (2025), §5.1–5.3, Theorem 5.1. Closes the planned SORRIES.md row "KG Theorem 5.1
for all n, candidate B".
Precondition: main = 7f6ef5f (report v3 commit). `git switch -c stage-13a main`; one commit;
include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix rounds
per layer; the repository stays sorry-free — a stuck layer is reported (see Fallback), never left
as a `sorry`.
**Scope: Lean only.** No change to `mczFew`, `plan`, emitted circuits, the certificate generator,
the committed certificates (byte-identical) or any existing statement. New names only.

## Target

```
theorem mczFew_logDepth_ancRestore {n : ℕ} {C : Circuit} (hC : mczFew n .logDepth = .ok C) :
    AncRestore n 2 C (phaseOracle allOnes)
theorem mczFew_logDepth_ok {n : ℕ} (hn : n ≠ 0) : ∃ C, mczFew n .logDepth = .ok C
theorem diffusionFew_logDepth_ancRestore {n : ℕ} {D : Circuit}
    (hD : diffusionFew n .logDepth = .ok D) : ∀ a, D.nAnc ≤ a → AncRestore n a D (diffU n)
```
No `C.WF`, `nBits`, `stepOk` or classical hypothesis: all are proved for every `n`.
Via `mczFew_ancRestore_of_classical` (12d) this needs, for every `n`: `C.WF`,
`C.nBits = nAnd (plan n .logDepth).1`, `(plan n .logDepth).1.all (stepOk n 2)`,
`(plan n .logDepth).2.all (·.inRange n 2)`, and ∀ x, `stepsPre … ∧ phaseBit 2 n .logDepth x = allOnes x`.

## Proof plan (reviewer; verify every step, do not trust it)

**L1 — schedule-independent invariant (KG §5.1).** Index model: an array of marks `A` and values
`q` (index 0 = the clean ancilla, `A[0] = true`, `q 0 = false`; `F` = product of the initial
unmarked values). An op `(t, x, y)` is *valid* if `t < x < y`, `A[t]`, `¬A[x]`, `¬A[y]` (the
test-file `valid`, move it to `CQRV/`); it writes `q t := q x ∧ q y` if `t = 0`, else
`q t := ¬(q t ⊕ (q x ∧ q y))`. Hand-derived invariant, preserved by every valid op:
 (a) ∏ unmarked `q i` = `F`;
 (b) ∀ marked `t > 0`, `q t = false → ∏_{i < t, unmarked} q i = false` (conditionally clean);
 (c) `A[0] → q 0 = false` (index 0 is never re-marked: `x > t ≥ 0`), which gives `stepsPre`.
Reviewer's check of (a): if `q t = 0` and `t > 0`, (b) makes the unmarked product left of `t` zero,
so both sides are 0. (b) for the new marks `x`, `y`: if `q x ∧ q y = 0` the new `q t` is `¬q t`
(rtof) or `0` (AND), and `q t = 0` falls back to (b) at `t`; for an older mark `t' > t`, the same
case split. Then a **simulation lemma**: for `qs` `Nodup`, `runSteps (stepsOf qs ops)` and
`stepsPre` agree with the index model.

**L2 — validity of the schedule for every n.** `greedy`: valid by construction (`greedyStep`).
`doubling n`: valid from `true :: replicate n false`, with the closed form after timestep `i`
(`0^{i+1} 1^{2^{i+1}} 0…`, the `#guard` at n = 36); prove per timestep through `substepsK` /
`FewSchedule.substeps_eq` (no `mergeSort` reasoning if `sortNat` suffices). **Hardest layer.**
`accumulate`: L1 again on the fresh array `anc 1 :: us`, whose `F` is (a) of phase 1; its qubits
are disjoint from the phase-1 marks, which it never touches.

**L3 — side conditions for every n.** `stepOk n 2` (from `Nodup` and indices in range),
`inRange` of `us`, `C.WF`, `C.nBits = nAnd` (bits numbered by `uncomputeAll`).

**L4 — success.** `accumulate` / `greedy` from `[true, false^k]` ends with 1 or 2 unmarked (KG §5.2;
each op removes one unmarked; find the invariant that rules out ≥ 3 with no valid op), plus
`n ≤ 2`. Only `mczFew_logDepth_ok` needs L4.

## Fallback (if L2-doubling or L4 does not close in 3 rounds)

Keep L1, L3 and the simulation lemma; state the stuck part as a Bool check polynomial in `n`
(`valid (true :: replicate n false) (doubling n)`, O(n²), no `2ⁿ` enumeration), prove the target
conditional on it, measure its `decide +kernel` time at n = 12, 64, 256, and keep the SORRIES row
planned with the remaining obligation narrowed to that check. Report; do not switch the generator.

## Acceptance

- `lake build` green, sorry-free; guarded `#print axioms` for the three targets: standard three.
- SORRIES.md row closed with hash (or narrowed per Fallback); DECISIONS.md: proof route, invariant.
- `scripts/ci_local.sh` all PASS (or `check_certify.sh` alone if step 19 runs out of memory);
  certificates byte-identical.

## Stop conditions

- The invariant (a)–(c) fails for some valid op (give the counterexample) → stop.
- Any existing statement or definition would have to change → stop and propose.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which layers closed, the invariant as proved, line
counts, and whether the generator's `2ⁿ` `fewCheck` can now be dropped (a 13a-follow-up decision,
not done here).
