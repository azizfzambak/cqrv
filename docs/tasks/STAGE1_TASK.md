# Stage 1 — Resource grades and the fibration

Report sections: §3.1.1 (Table 3.1, revised ⊕ = max/+/+/max), §3.1.2 (Table 3.2),
§3.1.3 (hardware profile = monotone map), §3.1.4 (Table 3.3), §3.3.2–3.3.3 (ρNISQ, Table 3.5),
§2.3.3 (three-stage pipeline table).
Precondition: Stage 0 accepted 2026-10-22 (commits 57d34aa, 2301b0f; Lean v4.35.0, Mathlib
v4.35.0 @ 56a0058, Physlib @ 96a6bc5). The repo has no `main` yet: create it at the tip of
`stage-0` (`git branch main stage-0`), then `git switch -c stage-1 main`; one commit. Windows builds: `LEAN_NUM_THREADS=4` (README). Do not import Physlib
in this stage.
Read `CLAUDE.md` and `docs/DECISIONS.md` first. No `sorry` is expected in this stage.

## Corrections to the PLAN.md wording (follow these, not the PLAN text)

- PLAN writes `structure Grade (w d t a : Nat)`; that makes the components type parameters.
  The grade is a value: `structure Grade where (w d t a : Nat)` with `@[ext]`,
  `deriving DecidableEq, Repr`.
- PLAN asks for `CommMonoid Grade` for ⊕. Use **`AddCommMonoid Grade`** instead:
  `+` is ⊕, `0` is (0,0,0,0), and `n • r` is the n-fold ⊕ that Stage 3 needs for `for` loops
  and that gives the r⋆-fold Grover iteration. Keep `seqComp` as the named definition
  (`instance : Add Grade := ⟨seqComp⟩`) so the report's name is still in the code.
  Record this in DECISIONS.md (Rejected: multiplicative `CommMonoid` — `r ^ k` for k-fold
  sequential composition reads wrong; a custom `⊕` notation — clashes with Lean's `Sum` type
  notation `α ⊕ β`). If you add notation, make it `scoped` and different from `⊕`.

## Tasks (all in `CQRV/Grades/`, doc-comment every definition with its report §)

1. **`Grade`** as above. Doc-comment: w = width, d = depth (critical-path layers),
   t = T-count, a = peak simultaneous ancillae (§3.1.1).

2. **`seqComp` (⊕)** = `⟨max w₁ w₂, d₁ + d₂, t₁ + t₂, max a₁ a₂⟩`, exactly Table 3.1.
   Doc-comment: valid because every stage restores its ancillae (§6.2), so registers are reused.
   **`parComp` (⊗)** = `⟨w₁ + w₂, max d₁ d₂, t₁ + t₂, a₁ + a₂⟩`. Doc-comment must say ⊗ is
   only for circuits on **disjoint** registers. Do not make ⊗ an instance (one `+` only);
   prove its laws as named theorems: `parComp_comm`, `parComp_assoc`, `parComp_zero`.

3. **`AddCommMonoid Grade`** with all laws proved (`ext` + `simp` / `omega`; for `max`
   use the Mathlib order lemmas). Rule 2 applies: confirm every lemma name with `#check`
   before use; if `omega` closes a goal, prefer it over named lemmas. Also prove the
   simp lemmas `seqComp_w/_d/_t/_a`.
   **Do not define `nsmul` by hand** — leave the structure's default (repeated addition),
   so no `nsmul_zero`/`nsmul_succ` proofs are needed. Since `max` is idempotent and 0 is the
   identity, `2 • iteration` reduces to `iteration + iteration` and the Table 3.3 test closes
   by `decide`/`rfl`. Do not add general `nsmul_*` component lemmas in this stage.

4. **Order (§3.1.2).** Component-wise `PartialOrder Grade` (not lexicographic, not via
   `Prod`), `DecidableRel (· ≤ · : Grade → Grade → Prop)`, and
   `def fits (r b : Grade) : Bool := decide (r ≤ b)` with `theorem fits_iff : fits r b = true ↔ r ≤ b`.
   Monotonicity: `seqComp_mono` and `parComp_mono` (r ≤ r' → s ≤ s' → r ⊕ s ≤ r' ⊕ s').
   Fibre: `def Fibre (b : Grade) := {r : Grade // r ≤ b}` and the reindexing inclusion
   `Fibre.relax (h : b ≤ b') : Fibre b → Fibre b'` (Table 3.2, "budget relaxation").
   Doc-comment that the base category is (R, ≤)ᵒᵖ and fibre membership is decidable.
   Do not build the category-theoretic fibration in Mathlib's `CategoryTheory`; out of scope.

5. **Hardware profiles (§3.1.3).**
   `structure HardwareProfile (P : Type) [Preorder P] where map : Grade → P; mono : Monotone map`.
   (PLAN says Grade → Grade; the report's ρ lands in R_phys, so the target is a parameter.)
   `def ρNISQ (tgate tT : Nat) : HardwareProfile Grade` with
   `map r = ⟨r.w, r.d * tgate, r.t * tT, r.a⟩` (§3.3.3), monotonicity proved.
   Durations are in nanoseconds; do not hard-code a value for `tT` — the report gives none.

6. **Tests** in `tests/Grades.lean` (wired into `CQRVTests`), using `#guard` for Bool
   facts and `example … := by decide` / `rfl` for equalities:
   - §2.3.3: r₁ = (10,50,100,5), r₂ = (12,200,800,8), r₃ = (8,30,0,0);
     r₁ + r₂ = (12,250,900,8) and (r₁ + r₂) + r₃ = (12,280,900,8).
   - Table 3.3: oracle (10,21,8,2) + diffusion (10,16,28,2) = iteration (10,37,36,2);
     `2 • iteration = (10,74,72,2)` (r⋆ = 2).
   - ⊗ sanity: (10,21,8,2) ⊗ (10,16,28,2) = (20,21,36,4) — and a comment that this is the
     wrong law for Grover (shared registers), which is exactly why both laws exist.
   - Budget (§3.3.3): `fits (10,74,72,2) ⟨127,200,72,127⟩ = true`;
     `fits (10,74,72,2) ⟨127,73,72,127⟩ = false` (depth over budget).
     Comment: the t-budget is set to the requirement because on NISQ T is native (Table 3.5);
     no Kyiv T-budget number is invented.
   - ρNISQ: `(ρNISQ 500 tT).map (10,74,72,2)` has depth 37 000 ns ≤ 100 000 ns (T1 ≈ 100 μs,
     §3.3.3), for a symbolic or any concrete `tT`.

## Acceptance

- `lake build` and `lake build CQRVTests` green, warning-free, **zero `sorry`**,
  SORRIES.md unchanged; CI scripts from Stage 0 pass.
- All tests above pass; `#print axioms` on `fits_iff`, `seqComp_mono` and one monoid law
  shows only `propext`, `Classical.choice`, `Quot.sound` (paste the output).
- DECISIONS.md: the `AddCommMonoid` choice and the `HardwareProfile` target-type choice.

## Stop conditions

- A monoid law that `omega`/`simp` will not close after 3 rounds → stop and report the goal state.
- Any number in the tests not reproducing the report → stop and report; do not adjust the
  test or the definition to make it pass.
- Do not touch modules outside `CQRV/Grades` and `tests/` (except the root import). Do not start Stage 2.

## Closing reply

CLAUDE.md format, under 40 lines: (a) files, (b) `lake build` tail, (c) test output and the
`#print axioms` lines, (d) SORRIES.md (expected: unchanged), (e) open questions.
