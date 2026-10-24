# Stage 5b — Diffusion operator and the measured Grover grade (engineering; no new proofs)

Report sections: §3.1.4 / Table 3.3 (diffusion "10, 16, 28, 2 (reused)"), §6.1.4 / Table 3
("4n − 4 T-gates, 28 for n = 8, via the relative-phase multi-controlled-Z decomposition, 16
layers, reusing the two ancillae"), §8.2 (`U_s = 2|s⟩⟨s| − I = H^{⊗n}(2|0⟩⟨0| − I)H^{⊗n}`),
§3.2.4 (circuit family: H^{⊗n} then r⋆ iterations, then measure).
Precondition: 6b-3 accepted (main = 518b698). `git switch -c stage-5b main`;
one commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`; Python
`.venv/Scripts/python.exe -I`. Module system.

## The reviewer's reading of the report's diffusion claim (to be measured, not trusted)

`2|0⟩⟨0| − I = −X^{⊗n} · MCZ · X^{⊗n}`, and `MCZ` is exactly the **phase oracle of
P_all(y) = y₀ ∧ … ∧ y_{n−1}**. Our synthesizer already builds that oracle and **Lemma 6.3.2
already proves it** (xor-free AND chain): n − 1 = 7 ANDs, `t = 4(n − 1) = 28` — the report's
"4n − 4" — but with **a = n − 1 = 7** ancillae, not the 2 the report claims. With 2 clean
ancillae a 7-node chain is infeasible under our pebbling (Stage 5: p pebbles reach node
2^p − 1, so a_max = 3 is the minimum). So the report's "(16, 28, a = 2 reused)" looks
internally inconsistent; this stage measures what is actually achievable.

## Reviewer decisions (record in DECISIONS.md)

1. **Primary construction (V1):** `diffusion n := H^{⊗n} ; X^{⊗n} ; synthesizeOracle(P_all) ;
   X^{⊗n} ; H^{⊗n}`. Its correctness (up to the global phase −1, irrelevant for the channel) is
   then Lemma 6.3.2 plus H/X wrappers — **no new restoration proof**. Rejected for now: a
   relative-phase / dirty-ancilla MCZ with a = 2 (would need its own restoration proof).
2. **Also measure (V2):** the same with the Stage 5 Bennett schedule at `a_max = 3` (the minimum
   feasible) — grade only, plus harness; not used for the headline unless the reviewer decides so.
3. **Ancilla reuse:** diffusion uses `anc[0..)` starting at 0, so the oracle's two restored
   ancillae are reused (§3.1.4); the iteration's `a` is `max(a_oracle, a_diffusion)` under ⊕.

## Tasks

1. `CQRV/Synthesis/Diffusion.lean`: `diffusion (n) (aMax : Option Nat) : Except Diagnostic Circuit`
   (V1 when `none`, V2 with Bennett), built from the existing synthesizer on the network of
   `P_all`; `groverIteration P n` = oracle ++ diffusion (shifted append of 6b-1);
   `groverCircuit P n r` = `H^{⊗n}` then `r` iterations (no final measurement in the IR; the
   harness measures).
2. CLI: `cqr synthesize --diffusion n [--amax k]`, `cqr synthesize <file> --grover [--iterations r]`
   (default r = r⋆ = ⌊π/(4θ)⌋ from n and M; print r⋆). Print each grade.
3. Python (`tests/diff/`): (a) diffusion check — for random complex `|ψ⟩` on n ≤ 10 data qubits,
   **every measurement branch** ends in `(2|s⟩⟨s| − I)|ψ⟩ ⊗ |0…0⟩` up to a global phase;
   (b) one Grover iteration of `grover_pred_037` = `U_s U_P` on random `|ψ⟩`, all branches;
   (c) full Grover for `grover_pred_037` at r = r⋆ = 2 from `|0…0⟩`: sample **one random branch
   per measurement** (restoration makes every branch identical, which (a)/(b) check), then
   compute the success probability `Σ_{P(x)=1} |amp|²` and compare with `sin²((2r⋆+1)θ)`,
   sin²θ = 32/256 (≈ 0.945) to 1e-9. Add to `diff_oracles.sh` (or a sibling script) and CI.
4. Lean tests: `#guard` the grades printed below once measured (they become regression values).

## What to report (measured, not adjusted)

| Object | Report claims | Measure |
|---|---|---|
| Diffusion D₈ (V1) | (10, 16, 28, 2 reused) | (w, d, t, a) |
| Diffusion D₈ (V2, a_max = 3) | — | (w, d, t, a) |
| One iteration (oracle ⊕ D₈, V1) | (10, 37, 36, 2) | measured, and ⊕ of the two measured grades |
| Full Grover, r⋆ = 2 (V1) | (10, 74, 72, 2) | measured |
| Success probability | sin²(5θ) ≈ 0.945 | simulated |

Check that the measured iteration grade equals `oracle ⊕ diffusion` from Stage 1 (it may not:
the scheduler can overlap layers across the boundary — report either way).

## Acceptance

- `lake build` green; harness (a), (b), (c) pass; the table above filled in DECISIONS.md and the
  closing reply; every deviation from the report recorded as an erratum candidate.
- No new `sorry`. `oracle_diff` / JSON byte-identity still pass (the oracle must not change).

## Stop conditions

- (a) or (b) fails in some branch → stop and report (it would contradict Lemma 6.3.2 or the
  wrapper reasoning).
- The simulated success probability differs from sin²(5θ) by more than 1e-9 → stop and report.
- Do not attempt a relative-phase MCZ, do not write Lean proofs about the diffusion (Stage 7),
  do not start Stage 7/8.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the filled table, whether ⊕ of measured parts equals
the measured whole, and a recommendation (V1 vs V2) for the headline grade with its trade-off.
