# Stage 9a — `lemma_6_3_2_xor`: Lemma 6.3.2 for networks with XOR (and `if`) nodes

Report sections: §6.3.2 (Lemma 6.3.2), §6.1.2 (XOR nodes cost no T and no ancilla; in-place XOR),
§6.2.4 (Layers 1–3), §7.3.2 (`if` via the mux rule `b ⊕ (c ∧ (a ⊕ b))`), §9.2 Table 9.2
(the second predicate of M2 contains XOR and `if`).
Precondition: Stage 8b accepted (main = 8b review commit). `git switch -c stage-9a main`; one
commit; include this file (untracked); leave `docs/tasks/STAGE9B_TASK.md` untracked.
Windows: `LEAN_NUM_THREADS=4`. Module system. **Proof stage**, 3 build–fix rounds per item;
a stuck item becomes a tracked `sorry` with its goal verbatim (own SORRIES.md row).
**CI stays local** (reviewer decision 2026-10-25): every check you would rely on CI for must be
run locally and reported.

## Why this is the next proof

The M2 acceptance (PLAN.md Stage 9) needs a second certified predicate with an XOR chain and an
`if`. `cqr certify` currently reports `tracked obligations: lemma_6_3_2_xor` for any network with
XOR nodes — honestly, but it blocks M2. 6b-3 proved the xor-free case by an invariant over the
synthesizer's fold with `lin.length ≤ 1`; this stage lifts that restriction.

## What changes when XOR nodes are present (read `CQRV/Synthesis/Oracle.lean`)

`Aff` values have `lin` of any length. `prepare u v` emits `gather u.lin pu` (CNOTs from the
other atoms of `u` onto the pivot `pu`), then `gather Sv pv` for `v` (with the symmetric-difference
trick when `pu ∈ v.lin`), then the polarity `X` gates; the compute block is
`pre ++ alloc t ++ TempLogicalAND pu pv t ++ preᴿ`, the uncompute block replays `pre` around the
MBU. On basis vectors CNOTs are permutations, so the proof stays on basis vectors (6b-3 route):
after `pre`, qubit `pu` holds `Aff.eval u`, `pv` holds `Aff.eval v`, every other qubit holds its
atom; `preᴿ` restores the atoms exactly (the gather CNOTs are self-inverse and commute as used —
prove it, do not assume it).

## Tasks (`CQRV/Circuit/OracleCorrectXor.lean` or an extension of `OracleCorrect.lean`)

1. **`gather` on basis vectors — prove:** for distinct in-range atoms `S` with pivot `p ∈ S`,
   `gather S p` maps `basisVec s` to `basisVec (p.set (⊕_{q∈S} q.get s) s)`, and
   `(gather S p)ᴿ` undoes it on that image.
2. **`prepare` on basis vectors — prove:** after `pre`, `pu` holds `u.eval s`, `pv` holds
   `v.eval s` (including the `pu ∈ v.lin` symmetric-difference case and the `X` polarity), all
   other qubits unchanged; `preᴿ ∘ pre = id` on basis vectors.
3. **Generalized invariant** — extend 6b-3's `Inv` to arbitrary `lin` (drop `lin.length ≤ 1`),
   with `symDiff` semantics `Aff.eval (xor) = Aff.eval a ⊕ Aff.eval b` proved for the
   insertion-sort `symDiff` of 8b, and the `fold` identities as before.
4. **Compute / phase / uncompute** — redo 6b-3 items 3–5 with items 1–2 in place of the bare `X`
   lemma; `phaseFlip` now gathers `p.lin` onto `q` before `Z` — same lemmas.
5. **`lemma_6_3_2_xor` — prove** (statement exactly as its SORRIES.md row: `lemma_6_3_2` without
   `N.xorFree`). Then make `lemma_6_3_2` a corollary of it (keep the name and statement — do not
   break Stage 7/8 callers), and remove the `hXor` field from `OracleCert` / the generated
   `Cert.lean` **only if** every caller still builds; otherwise keep the field and record why.
6. **`cqr certify` on an XOR predicate**: with the lemma closed, the Stage 5 xor/`if` corpus
   predicate that 8b used as negative test (a) must now be certified (conditional on its
   solution count). Replace negative test (a) by: a network that fails `C.WF` or does not match
   → no "certified". Keep (b) injected `sorry` and (c) `search_while`.
7. **Optional, only if items 1–6 closed with rounds to spare:** `synthesizeOracle_WF`
   (planned row). Otherwise leave it planned.

## Tests

- `#print axioms` (guarded with `#guard_msgs`) for `lemma_6_3_2_xor`, `lemma_6_3_2`, and the
  regenerated Grover example certificate: only `propext`, `Classical.choice`, `Quot.sound`.
- `diff_oracles.sh` (incl. xor-if 30/30), oracle JSON byte-identical, `check_emit.sh`,
  `check_certify.sh`, `cli_smoke.sh`, `print_axioms.sh` — all run **locally**, outputs pasted.

## Acceptance

- `lemma_6_3_2_xor` proved (or reduced to named sub-lemma rows); SORRIES.md row closed with the
  hash (follow-up line as before).
- An XOR/`if` predicate from the corpus certifies with the honest conditional status line.
- No synthesizer output changes (golden JSON byte-identical).

## Stop conditions

- The invariant is false for some XOR network the synthesizer accepts (e.g. a gather CNOT whose
  control equals its target, or `pu = pv` after `symDiff`) → stop and report the network: it
  would be a synthesizer bug the harness missed.
- Do not start 9b (second RevLib/EPFL predicate, front-end validation, run report, M2 report).

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which items closed, whether `hXor` was removed, the
certify status line for the XOR predicate, and whether `synthesizeOracle_WF` was attempted.
