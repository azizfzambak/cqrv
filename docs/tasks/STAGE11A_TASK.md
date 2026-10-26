# Stage 11a (improvement 1) — `synthesizeOracle_WF`: well-formedness of every synthesized oracle

Report sections: §6.3.2 (Lemma 6.3.2's side condition `C.WF`), §8.3.4 (Figure 8.1, restoration
side), §9.1.1 (gate-level AST). Precondition: Stage 10b accepted (main = 10b review commit; the
repository has **no** `sorry`). `git switch -c stage-11a main`; one commit; include this file
(untracked). Windows: `LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix rounds per item; a stuck
item becomes a tracked `sorry` with its own row — but the goal of the stage is to keep the
repository sorry-free, so prefer stopping and reporting over leaving a sorry.

## Why

Today every certificate discharges `C.WF` per instance by `decide +kernel`, and the general Grover
lemma needs `OracleCert.hWF` and a `DiffusionCert n` argument because `WF` is not known for
general networks. The planned SORRIES.md row states the fix:
`synthesizeOracle_WF : N.WF → synthesizeOracle N = .ok C → C.WF` (the hypothesis `N.WF` was added
in the 9a review after the counterexample `⟨0, #[.input 5], [0]⟩`).

## Tasks

1. **Prove `synthesizeOracle_WF`** in `CQRV/Circuit/OracleCorrect.lean` (next to `lemma_6_3_2_xor`).
   `C.WF` = every gate's data qubits `< C.nData`, CNOT/CZ operands distinct (also under `ifBit`),
   and the classical-bit discipline `bitsOk`. Reuse the 6b-3/9a invariant (`synthesizeOracle_ok`,
   `fold_inv`/`Inv`, records `p ≠ q`, operand atoms below their target) and `bitsOkFrom_shift`;
   new pieces: data atoms come from `input k` nodes with `k < N.nInputs` (from `N.WF`), and the
   `gather`/`prepare` CNOTs have distinct operands (from the sorted, duplicate-free `lin` lists).
2. **Diffusion corollary**: `allNet_WF : (allNet n).WF` and hence `(diffusion n none = .ok C) → C.WF`
   for every n — so `DiffusionCert n` can be **constructed** for every n.
3. **Simplify the Grover API** only where it stays backwards compatible: add
   `OracleCert.ofNetwork (N) (hN : N.WF) (hC : synthesizeOracle N = .ok C)` filling `hWF` from item 1,
   and `DiffusionCert.mk' n` from item 2; add a variant `grover_parametric_lemma'` without the
   `DiffusionCert` argument. Keep the existing names and statements (Stage 7/8 callers, the generated
   `Cert.lean` files) unchanged. Do **not** change the certificate generator in this stage — the
   per-instance `decide +kernel` checks stay as an independent second check.
4. **`toNetwork` produces well-formed networks**: either prove `toNetwork tp = N → N.WF` (if the
   front-end code is total and the proof is short) or keep the existing `#guard` on the corpus and
   record why; do not attempt a long front-end proof here.

## Acceptance

- `lake build` green; repository still sorry-free; `#print axioms` (guarded) for
  `synthesizeOracle_WF`, `allNet_WF`, `grover_parametric_lemma'`: only the standard three.
- SORRIES.md: the planned row closed with this stage's hash (follow-up line).
- `scripts/ci_local.sh` all PASS; both example certificates unchanged (byte-identical
  `Cert.lean`, hashes unchanged).

## Stop conditions

- The statement is false for some network accepted by `N.WF` (another counterexample) → stop and
  report it with the network; do not weaken the conclusion silently.
- Do not touch the emitter, the certificate generator, or Theorem 3.3a/3.3b files.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): whether item 4 was proved, the size of the WF proof, and
the `#print axioms` lines.
