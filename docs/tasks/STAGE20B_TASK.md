# Stage 20b — The amplitude-estimation parametric lemma (PHASE2_SPEC §A.4)

PHASE2_SPEC.md §A.4 ("Amendments before Stage 20b" — read it first; it replaces the output type,
the decoding POVM and the channel of "Specification and decoding" and of the statement sketch), the
"20a2 done" paragraph and its notes for Stage 20b, §A.2 (`aqft_diamond_le`, `aqft_opNorm_le`, the
Stage 18c notes on vacuity), §A.3 (5) (`U_count`), §A.8 items 1 and 6; report §2.1.2 (Definition
2.2), §2.3.2 (Theorem 3.3b), §8.2; PHASE2_ROADMAP.md row 20b. Three tasks: **20b1** and **20b2** are
specified here, each one commit, each starting after the reviewer accepts the previous one, from
`main`. **20b3** (the certificate) gets its task text after 20b2 is accepted.

Precondition: Stage 20a complete; main = 32dca39 (the 20a2 review commit). `git switch -c
stage-20b1 main` (20b2: `stage-20b2` from `main` after 20b1 is merged). The 20b1 commit includes this
file and the reviewer's edits to `docs/PHASE2_SPEC.md` and `docs/PHASE2_ROADMAP.md`, all unedited.
Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows:
`LEAN_NUM_THREADS=4`. Process as in Stage 20a: `lake build` in the foreground; `scripts/ci_local.sh`
and any Lean run longer than a few minutes are the user's separate terminal, one Lean process at a
time; harness scripts run before CI the way `ci_local.sh` runs them (`.venv/Scripts/python.exe -I`,
stdout redirected to a file, no `-X utf8`); "ready for CI", the reviewer's audit, the user's CI run,
then the commit and the closing reply.

**Invariants of both tasks.** Every measured value is unchanged; no definition a committed
`Cert.lean` evaluates is edited; no certificate is regenerated; every existing theorem statement
is unchanged — `coherent_composition`, `coherent_composition_diamond`, `qpe_success`, `U_count`,
`countingCircuit_ancRestore` included. The `cqr` executable gets no new subcommand or flag and its
import closure stays Lean core + Mathlib (§A.8 item 6). No new CI step: the pass mark stays **18
PASS, 0 FAIL, 4 n/a**; harness checks go into the existing step "Counting circuit". `sorry` is not
part of the acceptance of either task: if a lemma resists after a serious attempt, stop and ask. If
a statement here is false, give the counterexample and the corrected form, as at 19b, and report it
in (e). Use the decidability instance of `qpe_success` (`open Classical in`) and cite
`GroverData.iteration_induction` by that name (the 20a2 notes).

---

## 20b1 — The realization lemma, exact inverse QFT (`CQRV/Grover/AmplitudeEstimation.lean`, new)

Imports `CQRV.Grover.Counting`; not in the `cqr` closure. Throughout `gp : GroverData`,
`a = gp.M / 2 ^ gp.n` (as a real), `m ≥ 1`.

### A1. The output type, the metric, the specification

```
def countEst (m : ℕ) (a : ℝ) : Reg m ⊕ Unit → ℝ
  | .inl y  => Real.sin (π * y.toNat / 2 ^ m) ^ 2
  | .inr () => a
def CountOut (m : ℕ) (a : ℝ) : Type := Reg m ⊕ Unit
-- Fintype, DecidableEq by inferInstanceAs; the pseudo-metric induced by countEst m a
noncomputable instance (m : ℕ) (a : ℝ) : PseudoMetricSpace (CountOut m a) :=
  PseudoMetricSpace.induced (countEst m a) inferInstance
def CountSpec (m : ℕ) (a : ℝ) : Spec Unit (CountOut m a) := fun _ y => y = .inr ()
```

Lemmas: `dist_countOut : dist y y' = |countEst m a y − countEst m a y'|`; `countSpec_relax :
(CountSpec m a).relax ε () y ↔ |countEst m a y − a| ≤ ε`; `countSpec_dom : (CountSpec m a).dom =
Set.univ`. The metric is a pseudo-metric: `y` and its reflection `2^m − y` have the same estimate.
That is intended, and it is why §A.4 (3) of the amendments is needed for 20b2.

### A2. The decoding POVM

```
def countPOVM (n m : ℕ) (a : ℝ) : POVM (CountOut m a) (Reg (n + m))
  -- mats (inl y) = ∑ s : Reg n, (MState.pure (Ket.basis ((splitEquiv n m).symm (s, y)))).M
  -- mats (inr ()) = 0
```

`normalized` by reindexing `∑_y ∑_s` to `∑_x` through `splitEquiv` and the proof of
`basisPOVM`'s `normalized` (Grover/Lemma.lean). Then the measurement on the state the circuit
produces:

```
theorem countPOVM_measure (gp : GroverData) (m : ℕ) (y : Reg m) :
    (countPOVM gp.n m a).measure ((U_count gp.P m none) ◃ ancZero (gp.n + m)) (.inl y) =
      phaseDist gp m y
-- and the value at .inr () is 0
```

Follow `terminal_measurement` (Grover/Lemma.lean:588) for the pure-state computation:
`measure_eq_re_trace` (Realizability/Composition.lean), `pure_basis_m_apply`, the vector
`(U_count …).val *ᵥ basisVec (zeroReg _)`.

### A3. The realization

```
noncomputable def ae_delta : ℝ := 1 - 8 / π ^ 2
theorem ae_realizes (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {C : Circuit}
    (hR : AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
      (ae_eps a m) ae_delta g
```

The grade part is `hg`. For the probability part: `AncRestore.traced` turns the channel output on
`encode ()` into `U_count ◃ ancZero (gp.n + m)`, as in `grover_realizes_of_ancRestore`
(Grover/Lemma.lean:621). `countSpec_relax` turns the event into `|countEst y − a| ≤ ae_eps a m`.
On `inl y` this is the filter of `qpe_success`; `inr ()` has probability 0 (it is in the event,
since `ae_eps ≥ 0`, which does not matter). `countPOVM_measure` and `qpe_success` finish it.

### A4. The parametric lemma

```
theorem ae_parametric_lemma (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network} (hN : N.WF)
    (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N gp.n m none shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
        (ae_eps a m) ae_delta g ∧
      AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)
```

from `countingCircuit_ancRestore` (rewritten by `hP`) and `ae_realizes`. With `g := Synthesis.grade
C` it is the measured statement. Stage 20b3 uses it with the composed bound of 19a.

### A5. Tests

`tests/CQRVTests/AmplitudeEstimation.lean` (new): `example` instances at `n = 2`, `m = 2`
(`countSpec_relax` on both constructors, `ae_parametric_lemma` on the two-qubit AND network of the
19c tests with its `GroverData`), and `#guard_msgs` axiom checks of `countPOVM_measure`,
`ae_realizes` and `ae_parametric_lemma` (the standard three). No harness change in 20b1:
`phaseDist` and the success sets are already checked by part (g).

### 20b1 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (`CountOut` with `Reg m` and a real estimate; the POVM on the whole data
register; the channel `groverChannel (n+m)`); `docs/PROJECT_STATUS.md` one line; no README change.
Reviewer files go in unedited.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; A1–A4 proved, no `sorry`.

Stop and ask: the induced pseudo-metric meets an obstacle in Lean. The fallback of §A.8 item 1, the
specification that carries the tolerance with `RealizesExact`, is a reviewer decision: report the
obstacle and do not switch on your own. Also stop if a statement needs a hypothesis not listed.

---

## 20b2 — The AQFT variant through Theorem 3.3b (after 20b1 is accepted)

### B1. Theorem 3.3b on a pseudo-metric (`CQRV/Realizability/Coherent.lean`)

`coherent_composition_pseudo` and `coherent_composition_diamond_pseudo`: the two statements with
`[PseudoMetricSpace Z]` in place of `[MetricSpace Z]`, with the same proofs (they use only what
`Spec.relax` needs). The existing theorems keep their statements; you may re-derive their proofs
from the new ones or leave them as they are.

### B2. The operator norm under reindexing

- `l2_opNorm_submatrix_equiv (A : Matrix d d ℂ) (e : d' ≃ d) : ‖A.submatrix e e‖ = ‖A‖` (look for
  it in Mathlib first; otherwise prove it by conjugation with the permutation matrix, which is
  unitary). It goes into `CQRV/Realizability/Diamond.lean`, section `Unitary`, next to
  `l2_opNorm_kronecker_one_le`.
- `l2_opNorm_liftP_le : ‖liftP B‖ ≤ ‖B‖` (`liftP_eq_submatrix`, the swap of the Kronecker factors by
  `Equiv.prodComm`, `l2_opNorm_kronecker_one_le`).
- `l2_opNorm_kronecker_one_reg0 : ‖A ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)‖ = ‖A‖` (`Reg 0` is one
  point; `Reg m × Reg 0 ≃ Reg m`).

### B3. The inverse block

```
theorem inverse_diamond_le (n m kmax a : ℕ) :
    diamondDist (channelDenote (n + m) a (countingInverse n m none))
      (channelDenote (n + m) a (countingInverse n m (some kmax))) ≤ eta_aqft m kmax
```

Route: `channelDenote_of_unitary` (the inverse block is WF and unitary), `diamondDist_ofUnitary_le`,
`unitaryDenote_dataOnly`, `qftInvU_val` for both, `sub_kronecker_one`, `l2_opNorm_kronecker_one_le`,
the linearity of `liftP` in its argument, `l2_opNorm_liftP_le`, `l2_opNorm_conjTranspose`,
`unitaryDenote_zero_eq` with `l2_opNorm_kronecker_one_reg0`, and `aqft_opNorm_le`:
`2 · 2πm/2^kmax = eta_aqft m kmax`. Then the traced version for `traceRight ∘ …` by
`diamondDist_compose_le`.

### B4. The lemma

```
theorem ae_parametric_lemma_aqft (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network}
    (hN : N.WF) (hn : N.nInputs = gp.n) (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    {shape : DiffusionShape} {mode : UncomputeMode} (kmax : ℕ) {C : Circuit}
    (hC : countingCircuit N gp.n m (some kmax) shape mode = .ok C) (g : Grade)
    (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m a) (countPOVM gp.n m a) (groverChannel (gp.n + m) C)
      (ae_eps a m) (ae_delta + eta_aqft m kmax / 2) g
```

Route:
1. `countingCircuit_ok` gives `body`, the same for `none` and `some kmax`. Prove the converse
   constructor (`countingCircuit … kmax = .ok (body.append (countingInverse n m kmax))` from the
   `body` equation and `m ≠ 0`) to obtain the exact circuit `C₀` and its `hC₀`.
2. `C.nAnc = C₀.nAnc = body.nAnc`: the inverse block has no ancilla (`nAnc_append`).
3. `(groverChannel (gp.n+m) C).chan = Ψ_kmax ∘ₘ Φ`, with `Φ = channelDenote body ∘ₘ replacement …`
   and `Ψ_k = traceRight ∘ₘ channelDenote (countingInverse n m k)`, by `channelDenote_append`; the
   same for `C₀` with `Ψ_none`.
4. The ideal composite: `ae_realizes` on `C₀`. Take its probability part, with grade `0` against
   budget `0`. Write `CountSpec` as `S_g.comp S_f` with `S_f : Spec Unit Unit := fun _ _ => True`
   and `S_g = fun _ => CountSpec m a ()` (an equality by `funext`).
5. `coherent_composition_diamond_pseudo` with `η_f = 0` (`diamondDist_self`) and `η_g = eta_aqft m
   kmax` (B3). Take the probability part of the conclusion, and the grade part from `hg`.

### B5. Tests

- Lean: `example` instances at `n = 2`, `m = 2`, `kmax = 1`; `#guard_msgs` axiom checks of
  `coherent_composition_diamond_pseudo`, `inverse_diamond_le` and `ae_parametric_lemma_aqft`.
- `tests/diff/counting_diff.py`, a new part (h): for two of the `n = 4` predicates with `M ≥ 1`, in
  coherent mode, at `m = 5, 6` (§A.8 item 3, moved here at the 19b review), the realized
  probability of `|countEst y − a| ≤ ae_eps a m` against `1 − ae_delta = 8/π²`; and at `m = 6`,
  `kmax = 4, 5`, the AQFT circuit's realized probability, printed next to `8/π² − eta_aqft/2`
  (vacuous for m ≤ 6, as in 18c; state it). Measure the step's time before and after; if part (h)
  adds more than about 60 s, keep `m = 5, 6` for one predicate only and say so.

### 20b2 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the pseudo-metric versions of Theorem 3.3b, and why the existing ones
keep `MetricSpace`; the reindexing lemma; the factorization of the channel; `η_f = 0`);
`docs/PROJECT_STATUS.md`; README status line. Reviewer files untouched.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; B1–B4 proved, no `sorry`, axioms the
standard three; the harness part (h) passes.

Stop and ask: a statement needs a hypothesis not listed; an existing statement would have to
change; the channel factorization of step 3 fails (for instance, if the ancilla registers of `C`
and `C₀` differ).

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests — CI summary, the axiom lines, for 20b2 the
harness numbers of part (h) —, (d) SORRIES.md, (e) open questions; for 20b2, what the certificate
task 20b3 should know.
