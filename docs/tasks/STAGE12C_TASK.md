# Stage 12c — Restoration proof for the few-ancilla MCZ (candidate B, Khattar–Gidney §5.3)

Report sections: §6.2 (restoration is a co-equal obligation), §6.2.4 (Layers 1–3), §6.3.2
(Lemma 6.3.2 on density operators), §8.2 (diffusion), §9.5.2 (loose-but-proved).
Sources: Khattar–Gidney, Quantum 9, 1752 (2025), §5.1–5.3, Theorem 5.1; Maslov, PRA 93, 022311
(2016), relative-phase Toffoli. Implementation: `CQRV/Synthesis/MczFew.lean` (Stage 12b).
Precondition: Stage 12b accepted (main = fc3de52 or later). `git switch -c stage-12c main`; one
commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`. **Proof stage**, 3 build–fix
rounds per item; the repository must stay sorry-free at the end — a stuck item is reported, not
left as a `sorry` (if unavoidable, its own SORRIES.md row, and stop).
**Scope: proofs only.** `cqr certify` and the certificate generator are not changed here; wiring B
into certificates is a later stage (12d), after this proof exists.

## Proof plan (reviewer; verify every step, do not trust it)

Stay on the 6b-2/6b-3 **basis-vector route**: every gate of `mczFew` maps a basis state to a phase
times a basis state, except the MBU branches, which give `(√2)⁻¹` times a basis state.

1. **`rtof_basis`** — `rtof a b t` (distinct, in range) maps `basisVec s` to
   `d(a, b, t') • basisVec (t.set t' s)` with `t' = t.get s ⊕ (a.get s ∧ b.get s)` and `d` the
   diagonal of `D = diag(1,1,1,1,1,−1,−i,i)` (as checked by `tests/diff/mcz_diff.py` (0); state
   the index order explicitly and check it against the harness). Gate by gate as in
   `tempLogicalAND_correct_lift` (two H gates → a two-term sum).
2. **Pair cancellation** — for every value `t₀` of the target: the phase of the compute
   `rtof; X t` times the phase of the matching uncompute `X t; rtof` is 1, *provided the block in
   between returns `a, b, t` to the values they had after the compute*. Reviewer's hand check:
   the product is `d(a,b,t₀ ⊕ ab) · d(a,b,t₀)`; for `ab = 0` it is `d(a,b,t₀)² = 1` (entries
   1, 1, 1, 1, 1, −1 square to 1); for `ab = 1` it is `d(1,1,¬t₀) · d(1,1,t₀) = (−i)(i) = 1`. So the
   cancellation needs **no** "conditionally clean" assumption on `t₀` — confirm this in Lean.
3. **Classical skeleton** — define `mczFew.mid n v : (Reg n → Bool) → (Reg n × Reg a)`, the basis
   state reached after the compute steps (pure bit evaluation of the steps: AND writes `x ∧ y` on
   a clean target; `rtof; X` writes `¬(t ⊕ x ∧ y)`), and `phaseBit` = the product of the unmarked
   qubits `us` at `mid`. Prove the **inductive restoration claim**: for every branch `c`, the Kraus
   operator of `mczFew n v` maps `basisVec (x, 0)` to `(√2)⁻¹ ^ (#AND steps) · (−1)^{phaseBit x} •
   basisVec (x, 0)` — compute steps (items 1, `tempLogicalAND_kraus_basis`), phase (`z_basis`,
   CZ basis lemma), uncompute in reverse (item 2 for rtof pairs, `mbu_branch_basis` for AND pairs,
   whose hypothesis `t = x ∧ y` holds because everything after it has been undone).
4. **KG correctness, classical** — `phaseBit x = x₀ ∧ … ∧ x_{n−1}` for all `x`. Prove it for the
   instance **n = 8, `logDepth`** by `decide` over the 256 inputs (kernel-evaluable; no
   `native_decide`); optionally also for `ladder`. A proof for all n (KG Theorem 5.1) is **not**
   required in this stage — record it as a planned row if not done.
5. **Assemble** — with `ancRestore_of_kraus` (6b-1): `AncRestore 8 2 (mczFew 8 .logDepth) (phaseOracle P_all)`;
   then the diffusion `H X · MCZ · X H` with `AncRestore … (2|s⟩⟨s| − I)` (reuse the 7a/12a wrapper
   lemmas and the global-sign lemma). Name: `diffusionFew_ancRestore_8`.
6. Well-formedness: `(mczFew 8 .logDepth).WF` by `decide +kernel`.

## Acceptance

- `lake build` green, **no `sorry`**; `#print axioms` (guarded) for `rtof_basis`, the pair lemma,
  the restoration claim, `diffusionFew_ancRestore_8`: only `propext`, `Classical.choice`, `Quot.sound`.
- SORRIES.md: the planned 12c row closed (hash in a follow-up line); a planned row for the all-n
  version (item 4) if not proved.
- `scripts/ci_local.sh` all PASS (or `check_certify.sh` alone if step 19 runs out of memory);
  certificates unchanged (no generator change).
- DECISIONS.md: the proof route, and that B is now **proved for n = 8** but still not used by
  `cqr certify` (12d).

## Stop conditions

- `rtof_basis` contradicts the harness's `D` (index order or sign) → stop and report the computed
  phases; do not edit `rtof` to fit.
- The pair cancellation fails for some `t₀` (contradicting the hand check) → stop and report.
- `decide` over 256 inputs does not finish in reasonable time → stop and report (do not switch to
  `native_decide`).
- Do not change `mczFew`, the emitted circuits (golden JSON byte-identical), the certificate
  generator, or any existing statement.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): which items closed, the exact `D` index order used,
whether item 4 holds for `ladder` too, and what 12d would need to certify `--shape few:log`.
