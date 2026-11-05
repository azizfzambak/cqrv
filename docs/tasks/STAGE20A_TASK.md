# Stage 20a — The QPE bound for the counting circuit (PHASE2_SPEC §A.4)

PHASE2_SPEC.md §A.4 ("Amendments before Stage 20a" — read it first; it replaces the statement of
"The QPE lemma" above it), §A.3 (5) (`U_count`), §A.8 item 6 (import discipline); report §2.2
(realization), §8.2, §8.3.2 (the plane of `ψ_g`, `ψ_b`); PHASE2_ROADMAP.md row 20a. Two tasks, **two
commits**: do **20a1**, reply, stop; **20a2** starts after the reviewer accepts 20a1, from `main`.
Stage 20b (the realization lemma and the certificate) has its own task text, written after 20a.

Precondition: Stage 19 complete; main = d1aad62 (the 19c review commit). `git switch -c stage-20a1
main` (20a2: `stage-20a2` from `main` after 20a1 is merged). The 20a1 commit includes this file and
the reviewer's edits to `docs/PHASE2_SPEC.md` and `docs/PHASE2_ROADMAP.md`, all unedited. Untracked
and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows: `LEAN_NUM_THREADS=4`.
Process as in Stage 19: `lake build` in the foreground; `scripts/ci_local.sh` and any Lean run
longer than a few minutes are the user's separate terminal, one Lean process at a time; run the
harness scripts before CI the way `ci_local.sh` does (`.venv/Scripts/python.exe -I`, stdout
redirected to a file, no `-X utf8`); when the build is green and the tests you can run yourself
pass, stop and say "ready for CI"; the reviewer audits, the user runs CI, then you commit and give
the closing reply.

**Invariants of both tasks.** Every measured value is unchanged; no definition a committed
`Cert.lean` evaluates is edited; no certificate is regenerated; every existing theorem statement
is unchanged, `countingCircuit_ancRestore` and `U_count` included. The `cqr` executable gets no new
subcommand or flag and its import closure stays Lean core + Mathlib (§A.8 item 6). There is no new
CI step: the pass mark stays **18 PASS, 0 FAIL, 4 n/a**; the harness checks go into the existing
step "Counting circuit". `sorry` is not part of the acceptance of either task: if a lemma resists
after a serious attempt, stop and ask. If a statement here is false, give the counterexample and
the corrected form, as at 19b, and report it in (e).

---

## 20a1 — The analysis (`CQRV/Grover/QPEBound.lean`, new; imports Mathlib only, no Physlib)

Real and complex analysis only: no register, no circuit. Sums are over `Finset.range (2 ^ m)`, and
the outcome `y` is an integer, so that periodicity is a statement and not a case split. Confirm
every Mathlib name with `#check` (CLAUDE.md rule 2); the names below are the expected ones, not
promises.

### A1. The amplitude and the probability

```
noncomputable def qpeAmp (m : ℕ) (δ : ℝ) : ℂ :=
  ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m), Complex.exp (2 * π * Complex.I * k * δ)
noncomputable def qpeProb (m : ℕ) (φ : ℝ) (y : ℤ) : ℝ := ‖qpeAmp m (φ - y / 2 ^ m)‖ ^ 2
```

Lemmas: `qpeAmp_add_int` (`qpeAmp m (δ + z) = qpeAmp m δ` for `z : ℤ`), hence `qpeProb_add_two_pow`
(`qpeProb m φ (y + 2 ^ m) = qpeProb m φ y`) and `qpeProb` depends on `y` only through `y % 2 ^ m`;
`qpeAmp_zero` (`qpeAmp m 0 = 1`); and the closed form, for `sin (π δ) ≠ 0`,

```
theorem qpeProb_closed (m) (δ) (h : Real.sin (π * δ) ≠ 0) :
    ‖qpeAmp m δ‖ ^ 2 = Real.sin (π * 2 ^ m * δ) ^ 2 / ((2 ^ m) ^ 2 * Real.sin (π * δ) ^ 2)
```

by `geom_sum_eq` and `‖e^{ix} − 1‖ = 2 |sin (x/2)|` (`Complex.norm_exp_I_mul_ofReal_sub_one`, or
whatever Stage 18c found next to `Real.norm_exp_I_mul_ofReal_sub_one_le`).

### A2. The inequality

```
theorem two_point_bound {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2)
```

Equality holds at `t = ½`. Route, with `t ≤ ½` wlog (both factors are symmetric under `t ↦ 1 − t`):

- **`0 < t ≤ ¼`.** Concavity of `sin` on `[0, π/2]` (`strictConcaveOn_sin_Icc`) at `0` and `π/4`
  gives `sin (π t) ≥ 4 t · sin (π/4) = 2√2 t`, so `sin²(πt) / t² ≥ 8`, and the other term is
  non-negative.
- **`¼ ≤ t ≤ ½`.** Put `s = ½ − t`, `q = s² ∈ [0, 1/16]`. Then `sin (π t) = cos (π s)`,
  `1/t² + 1/(1−t)² = (½ + 2q) / (¼ − q)²`, and the claim is `cos²(π s) (1 + 4q) ≥ (1 − 4q)²`. Use
  `Real.one_sub_sq_div_two_le_cos`: `cos (π s) ≥ 1 − c q` with `c = π²/2`, and `π < 3.15`
  (`Real.pi_lt_d2`) gives `c < 4.97`, so `cos (π s) ≥ 1 − 4.97 q > 0`. The polynomial inequality
  `(1 − 4.97 q)² (1 + 4q) ≥ (1 − 4q)²` on `[0, 1/16]` holds: the difference divided by `q` is at
  least `2.06 − 31.06 q ≥ 0.11`. `nlinarith` should close it.

The first idea one tries is false: `sin (π t) ≥ 4 t (1 − t)` fails at `t = ¼` (the true direction is
`≤`), and so does `sinc t + sinc (1−t) ≥ 4/π`. Do not spend time there.

### A3. The two neighbours and the near set

```
theorem qpeProb_two_neighbours (m : ℕ) (φ : ℝ) :
    8 / π ^ 2 ≤ qpeProb m φ ⌊2 ^ m * φ⌋ + qpeProb m φ (⌊2 ^ m * φ⌋ + 1)
```

With `t = 2^m φ − ⌊2^m φ⌋ ∈ [0, 1)`. If `t = 0` the first term is `qpeProb = 1 ≥ 8/π²`
(`qpeAmp_zero`; `π > 3.14`). If `0 < t < 1`: the two arguments are `δ₁ = t/2^m`, `δ₂ = (t−1)/2^m`,
`sin (π 2^m δ_i)² = sin²(π t)`, and `2^m |sin (π δ_i)| ≤ π |2^m δ_i|` (`Real.sin_le`, `|sin x| ≤ |x|`)
gives `qpeProb ≥ sin²(π t) / (π t)²` and `≥ sin²(π t) / (π (1−t))²`; then A2. Check
`sin (π δ_i) ≠ 0` from `0 < |δ_i| < 1` before using A1.

```
def CircleNear (m : ℕ) (φ : ℝ) (y : ℤ) : Prop := ∃ z : ℤ, |(y : ℝ) / 2 ^ m - φ - z| ≤ (2 ^ m : ℝ)⁻¹
theorem qpe_near_sum_ge {m : ℕ} (hm : 1 ≤ m) (φ : ℝ) :
    8 / π ^ 2 ≤ ∑ y ∈ (Finset.range (2 ^ m)).filter (fun y : ℕ => CircleNear m φ y), qpeProb m φ y
```

(decidability by `Classical`). The two elements are `⌊2^m φ⌋ % 2^m` and `(⌊2^m φ⌋ + 1) % 2^m`;
they are distinct because `2^m ≥ 2` (`hm`, the only use of it), both are `CircleNear`, and
`qpeProb_add_two_pow` moves the bound to them. `qpeProb_nonneg` drops the other terms.

### A4. The decoding

```
noncomputable def ae_eps (a : ℝ) (m : ℕ) : ℝ :=
  2 * π * Real.sqrt (a * (1 - a)) / 2 ^ m + π ^ 2 / 4 ^ m
theorem sin_sq_sub_le (θ Δ : ℝ) :
    |Real.sin (θ + Δ) ^ 2 - Real.sin θ ^ 2| ≤ |Real.sin (2 * θ)| * |Δ| + Δ ^ 2
theorem decode_close {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ π / 2) {m : ℕ} {y : ℤ}
    (h : CircleNear m (θ / π) y ∨ CircleNear m (-θ / π) y) :
    |Real.sin (π * y / 2 ^ m) ^ 2 - Real.sin θ ^ 2| ≤ ae_eps (Real.sin θ ^ 2) m
```

`sin²(θ+Δ) − sin²θ = sin(2θ+Δ) sin Δ`; `sin²` has period `π` and is even, so both signs reduce to
`sin_sq_sub_le` with `|Δ| ≤ π/2^m`; on `[0, π/2]`, `sin 2θ = 2 √(a(1−a))` with `a = sin²θ`.

### A5. Tests

- `tests/CQRVTests/QPEBound.lean` (new): `example` instances at `m = 1, 2` and `#guard_msgs` axiom
  checks of `two_point_bound`, `qpeProb_two_neighbours`, `qpe_near_sum_ge`, `decode_close` (the
  standard three). No real number can be `#guard`ed.
- `tests/diff/counting_diff.py`, a new part (f), pure numbers, no circuit: on a grid of `t` the
  inequality of A2, attained at `t = ½`; for `m = 1..8` and a grid of `φ` the closed form of A1
  against the sum, `∑_y qpeProb = 1`, and the bound of A3; the two false ideas above are shown to
  fail at `t = ¼` as negative controls.

### 20a1 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the route of A2 and why the two simpler bounds fail; `y : ℤ`; `CircleNear`
in place of a circle distance); `docs/PROJECT_STATUS.md` one line; no README change. Reviewer files
go in unedited.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; A1–A4 proved, no `sorry`; the module's
import closure has no Physlib.

Stop and ask: a statement needs a hypothesis not listed; `two_point_bound` resists the route above.

---

## 20a2 — The distribution of the counting circuit (`CQRV/Grover/Counting.lean`, new; after 20a1 is accepted)

Imports `CQRV.Circuit.CountingCorrect`, `CQRV.Grover.Lemma`, `CQRV.Grover.QPEBound`; not in the
`cqr` closure. Throughout `gp : GroverData`, `G = groverOp gp.P`, `θ = gp.θ`.

### B1. The amplitude of `U_count` on |0…0⟩

```
theorem U_count_zero_apply (gp : GroverData) (m : ℕ) (x : Reg (gp.n + m)) :
    ((U_count gp.P m none).val *ᵥ basisVec (zeroReg _)) x =
      ((2 ^ m : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ m),
        Complex.exp (-(2 * π * Complex.I * (phase x).toNat * k / 2 ^ m)) *
          ((G ^ k).val *ᵥ ketS gp.n) (search x)
```

Three steps, right to left. (i) `hadamardMat (n+m) *ᵥ basisVec (zeroReg _)` is the constant
`(√2)⁻¹ ^ (n+m)` (`mulVec_basisVec`, `hEntry _ false`). The split `hadamardMat (n+m) = liftS … *
liftP …` that the 19c review expected is not needed; record that. (ii) `ctrlPow` on a constant is
`(√2)⁻¹ ^ m · (G ^ (phase x).toNatLE *ᵥ ketS) (search x)`: `ctrlPow_apply`, reindex the sum by
`splitEquiv`, and `ketS` is the constant `(√2)⁻¹ ^ n`. (iii) `liftP (star (dataMat m (qftGates m)))`:
`liftP_apply`, `splitEquiv`, `dataMat_apply`, `qft_basis` (with `mulVec_basisVec`), `Reg.toNat_bitRev`,
so the entry is `(√2)⁻¹ ^ m · e^{−2πi (phase x).toNat · p.toNatLE / 2^m}`. Finally reindex
`∑ p : Reg m` to `∑ k ∈ range (2^m)` through `p ↦ p.toNatLE`, a bijection (`Reg.toNat_lt`,
`Reg.toNat_injective`, `bitRev_bitRev`); make this a lemma of its own in `CQRV/Circuit/Basis.lean` or
here, whichever keeps Physlib out of nothing that had none. `U_count … none` unfolds to `qftGates m`
by `rfl` (the 19c test).

### B2. The two phases

With `iteration_induction`, and `y = (phase x).toNat`:

```
A y = 2^{−m} ∑_k e^{−2πi y k/2^m} sin((2k+1)θ),   B y = the same with cos,
amplitude at x = A y · ψ_g (search x) + B y · ψ_b (search x),
A y = (e^{iθ} D₊ − e^{−iθ} D₋) / (2i),   B y = (e^{iθ} D₊ + e^{−iθ} D₋) / 2,
D₊ = qpeAmp m (θ/π − y/2^m),   D₋ = qpeAmp m (−θ/π − y/2^m).
```

Hence `‖A y‖² + ‖B y‖² = ½ (‖D₊‖² + ‖D₋‖²)`, because `|e^{±iθ}| = 1` (parallelogram identity).

### B3. The distribution

```
noncomputable def phaseDist (gp : GroverData) (m : ℕ) (y : Reg m) : ℝ :=
  ∑ s : Reg gp.n, ‖((U_count gp.P m none).val *ᵥ basisVec (zeroReg _))
    ((splitEquiv gp.n m).symm (s, y))‖ ^ 2
theorem phaseDist_eq (gp : GroverData) (m : ℕ) (y : Reg m) :
    phaseDist gp m y = (qpeProb m (gp.θ / π) y.toNat + qpeProb m (-gp.θ / π) y.toNat) / 2
```

`∑_s ‖A ψ_g s + B ψ_b s‖² = ‖A‖² + ‖B‖²` from `psiGood_dot_self`, `psiGood_dot_psiBad` and
`psiBad_dot_self`. That last lemma is a disjunction: **`ψ_b = 0` happens, at `M = 2ⁿ`**. Then
`cos θ = 0` (`cos_θ_eq`), `θ = π/2` (`θ_mem`), `cos ((2k+1) π/2) = 0`, so `B y = 0` and the identity
still holds. Do not add a hypothesis `M < 2ⁿ`.

### B4. The bound

```
theorem qpe_two_phase_bound (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        CircleNear m (gp.θ / π) y.toNat ∨ CircleNear m (-gp.θ / π) y.toNat), phaseDist gp m y
theorem qpe_success (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        |Real.sin (π * y.toNat / 2 ^ m) ^ 2 - gp.M / 2 ^ gp.n| ≤ ae_eps (gp.M / 2 ^ gp.n) m),
      phaseDist gp m y
```

`phaseDist_eq`, `qpe_near_sum_ge` once for each sign (reindexed from `range (2^m)` to `Reg m` through
`y ↦ y.toNat`, a bijection), and the union contains each near set, so the half-sum of two bounds
of `8/π²` is `8/π²`. `qpe_success` from `decode_close` and `sin_θ_eq` (the filter of `qpe_two_phase_bound`
is contained in this one, and `phaseDist ≥ 0`).

### B5. Tests

- `tests/CQRVTests/Counting.lean` or a new file: `example` instances at `n = 2`, `m = 2`; `#guard_msgs`
  axiom checks of `U_count_zero_apply`, `phaseDist_eq`, `qpe_two_phase_bound`, `qpe_success`.
- `tests/diff/counting_diff.py`, a new part (g), on the coherent circuits of part (a) for every
  predicate with `M ≥ 1`: the sum over the near set is at least `8/π²`, the sum over the decoding
  set of `qpe_success` is at least `8/π²`, and both are printed with the margin. `M = 0` is outside
  `GroverData` (`hM_pos`): it stays in part (a) and is skipped here, with a note.

### 20a2 Docs / Acceptance / Stop

Docs: DECISIONS.md entry (the direct route without eigenvectors; the case `M = 2ⁿ`; the Hadamard
split not needed); `docs/PROJECT_STATUS.md`; README status line ("Stages 0–20a"). Reviewer files
untouched.

Acceptance: `lake build` green; CI 18 PASS, 0 FAIL, 4 n/a; B1–B4 proved, no `sorry`, axioms the
standard three; the harness part (g) passes.

Stop and ask: a statement needs a hypothesis not listed (in particular `M < 2ⁿ`); `U_count` or
`countingCircuit_ancRestore` would have to change; the harness disagrees with `phaseDist_eq`.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests — 20a1: CI summary, the axiom lines, the grid
minimum of A2; 20a2: CI summary, the axiom lines, the harness margins per predicate —, (d)
SORRIES.md, (e) open questions; for 20a2, what Stage 20b should know about the form of `qpe_success`.
