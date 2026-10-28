# Stage 13c — `synthesizeOracle_succeeds`: synthesis never fails on a well-formed predicate

Report sections: §6.1.2, §6.1.4, §6.3.2, §9.1.1. Closes the planned SORRIES.md row
`synthesizeOracle_succeeds` (CQRV/Circuit/OracleCorrect.lean, next to `synthesizeOracle_WF`).
Precondition: Stage 13b accepted; main = 13b commit (fast-forward first, see below).
`git switch -c stage-13c main`; one commit; include this file (untracked). Windows:
`LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix rounds per item; repository stays sorry-free.
**No change** to `synthesizeOracle`, `step`, `prepare`, `fold`, `symDiff`, `cone`, emitted
circuits (golden files byte-identical), the generator or any existing statement. New names only.

## Target (statement as in the SORRIES row)

```
theorem synthesizeOracle_succeeds {N : Network} (hN : N.WF) (h1 : N.outputs.length = 1) :
    ∃ C, synthesizeOracle N = .ok C
```

## Proof plan (reviewer; verify every step)

The failure points of `synthesizeOracle` (CQRV/Synthesis/Oracle.lean) and why each is unreachable:
1. `outputs` not a singleton — excluded by `h1`.
2. `step`: `N.nodes[k]? = none` — `k < N.nodes.size` (the fold runs over `List.range`).
3. `get`: "operand outside the cone" — **cone closure**: if `mark[k]` and node `k` has operand
   `i`, then `mark[i]` (`cone` scans `k` downward and marks operands, which are `< k` by
   `N.WF`, before they are scanned; prove it as an invariant of the `foldl` over the reversed
   range). With the fold invariant "`vals.size = k` and `vals[i] = some _` for every marked
   `i < k`", `get` always meets `some`.
4. The final "output outside the cone" — `cone` marks `out` itself, and `out` is a node (`N.WF`).
5. `prepare`, first `fail` (`u.lin = []`) — `fold` returned `none`, so `u.lin ≠ []`.
6. `prepare`, second `fail` (`Sv.filter (· != pu) = []`) — **sortedness**: every `lin` reachable
   by `step` is strictly sorted by `Qubit.key` with no repeats (`[.data i]`, `[t]`, `symDiff`
   through `insertBy`, and `fold`'s results preserve it); `Qubit.key` is injective. Then: if
   `pu ∉ v.lin`, `Sv = v.lin ≠ []` has no `pu`; if `pu ∈ v.lin`, an empty filter means
   `u.lin.erase pu` and `v.lin.erase pu` have the same elements, hence `u.lin`, `v.lin` have the
   same elements, hence (strictly sorted) `u.lin = v.lin`, which `fold` already caught.
   Reuse the 6b-3 / 11a lemmas about `symDiff` and `fold_inv` / `Inv` where they apply; if the
   needed sortedness fact is already part of `Inv`, say so.

## Corollaries (new names; existing ones unchanged)

- `OracleCert.ofWF (N) (hN : N.WF) (h1 : N.outputs.length = 1) : OracleCert N.nInputs`
  (noncomputable via `Classical.choose`, or computable by matching on `synthesizeOracle N` —
  your choice, say which).
- `DiffusionCert.ofN (n) (hn : n ≠ 0) : DiffusionCert n` — no `hC` argument (with `allNet_WF`).
- Where `grover_parametric_lemma'` takes an `hC` that is now derivable, add a primed-again
  corollary only if it is short; otherwise list it in (e).

## Acceptance

- `lake build` green, sorry-free; guarded `#print axioms` for the target and the corollaries:
  standard three.
- SORRIES.md: row closed with hash (follow-up line); DECISIONS.md entry (proof route, which
  invariants were new, which were reused). PROJECT_STATUS.md §4: remove the row.
- A negative `example`: `⟨1, #[.input 0], []⟩` fails (no outputs) — the hypothesis `h1` is needed.
- `scripts/ci_local.sh` all PASS (or `check_certify.sh` alone if step 20 runs out of memory);
  certificates and golden files byte-identical.

## Stop conditions

- A reachable failure is found (some WF one-output network on which `synthesizeOracle` fails):
  stop, give the network, add it as a `#guard` counterexample; do not change the synthesizer.
- Any existing statement would have to change → stop and propose.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which of 1–6 needed new invariants, line counts, and
which `hC` arguments can now be dropped downstream.
