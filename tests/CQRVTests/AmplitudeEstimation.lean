module

import CQRV.Grover.AmplitudeEstimation

/-!
# The amplitude-estimation realization lemma (Stage 20b1, PHASE2_SPEC.md §A.4 "Amendments before
Stage 20b" (1)–(2); docs/tasks/STAGE20B_TASK.md 20b1 A1–A5)

`example` instances at `n = 2`, `m = 2`: the estimate and the induced distance on both
constructors of `CountOut`, `countSpec_relax` on `inl y` and on `inr ()`, `countSpec_dom`, the
decoding POVM on the state of `U_count` (`countPOVM_measure`, the value `0` at `inr ()`),
`ae_realizes` on the Grover data of `x₀ ∧ x₁`, and `ae_parametric_lemma` on the two-qubit AND
network of the 19c tests with its `GroverData` — and the axiom lines of `countPOVM_measure`,
`ae_realizes` and `ae_parametric_lemma`. No harness change in 20b1: `phaseDist` and the success
sets are checked by part (g) of `tests/diff/counting_diff.py`.
-/

namespace CQRV.Tests.AmplitudeEstimation

open CQRV CQRV.Synthesis CQRV.Counting CQRV.Grover Matrix Real
open scoped MState

/-- The Grover data of `x₀ ∧ x₁` on two qubits: `M = 1`, `a = 1/4`. -/
def gp22 : GroverData := ⟨2, 1, le_rfl, fun x => x 0 && x 1, by decide⟩

/-! ## A1 — the output type, the metric, the specification -/

example (y : Reg 2) : countEst 2 (1 / 4) (Sum.inl y) = Real.sin (π * y.toNat / 2 ^ 2) ^ 2 := rfl
example : countEst 2 (1 / 4) (Sum.inr ()) = 1 / 4 := rfl
example (y y' : CountOut 2 (1 / 4)) :
    dist y y' = |countEst 2 (1 / 4) y - countEst 2 (1 / 4) y'| :=
  dist_countOut 2 (1 / 4) y y'
-- the pseudo-metric: `y = 1` and its reflection `y = 3` are at distance `0` at `m = 2`
example : @dist (CountOut 2 (1 / 4)) _ (Sum.inl (Reg.ofNat 2 1)) (Sum.inl (Reg.ofNat 2 3)) = 0 := by
  refine (dist_countOut 2 (1 / 4) (Sum.inl (Reg.ofNat 2 1)) (Sum.inl (Reg.ofNat 2 3))).trans ?_
  change |Real.sin (π * ((Reg.ofNat 2 1).toNat : ℝ) / 2 ^ 2) ^ 2 -
    Real.sin (π * ((Reg.ofNat 2 3).toNat : ℝ) / 2 ^ 2) ^ 2| = 0
  rw [Reg.toNat_ofNat (by norm_num), Reg.toNat_ofNat (by norm_num)]
  have h : Real.sin (π * (3 : ℕ) / 2 ^ 2) = Real.sin (π * (1 : ℕ) / 2 ^ 2) := by
    rw [← Real.sin_pi_sub]; congr 1; push_cast; ring
  rw [h, sub_self, abs_zero]
-- `countSpec_relax` on both constructors
example (ε : ℝ) (y : Reg 2) :
    (CountSpec 2 (1 / 4)).relax ε () (Sum.inl y) ↔
      |Real.sin (π * y.toNat / 2 ^ 2) ^ 2 - 1 / 4| ≤ ε :=
  countSpec_relax 2 (1 / 4) ε (Sum.inl y)
example (ε : ℝ) :
    (CountSpec 2 (1 / 4)).relax ε () (Sum.inr ()) ↔ |(1 / 4 : ℝ) - 1 / 4| ≤ ε :=
  countSpec_relax 2 (1 / 4) ε (Sum.inr ())
example (ε : ℝ) (hε : 0 ≤ ε) : (CountSpec 2 (1 / 4)).relax ε () (Sum.inr ()) :=
  (countSpec_relax 2 (1 / 4) ε (Sum.inr ())).mpr (by
    change |(1 / 4 : ℝ) - 1 / 4| ≤ ε
    simpa using hε)
example : (CountSpec 2 (1 / 4)).dom = Set.univ := countSpec_dom 2 (1 / 4)
example : () ∈ (CountSpec 2 (1 / 4)).dom := ⟨(Sum.inr () : CountOut 2 (1 / 4)), rfl⟩

/-! ## A2 — the decoding POVM -/

example (y : Reg 2) :
    ((countPOVM gp22.n 2 (gp22.M / 2 ^ gp22.n : ℝ)).measure
      ((U_count gp22.P 2 none) ◃ ancZero (gp22.n + 2)) (Sum.inl y) : ℝ) = phaseDist gp22 2 y :=
  countPOVM_measure gp22 2 y
example (ρ : MState (Reg (2 + 2))) : ((countPOVM 2 2 (1 / 4)).measure ρ (Sum.inr ()) : ℝ) = 0 :=
  countPOVM_measure_inr 2 2 (1 / 4) ρ
example : ∑ y : Reg 2, phaseProj 2 2 y = 1 := sum_phaseProj 2 2

/-! ## A3 — the realization -/

example : ae_delta = 1 - 8 / π ^ 2 := rfl
example {C : Circuit} (hR : AncRestore (gp22.n + 2) C.nAnc C (U_count gp22.P 2 none)) :
    Realizes (CountSpec 2 (gp22.M / 2 ^ gp22.n : ℝ)) (countPOVM gp22.n 2 (gp22.M / 2 ^ gp22.n : ℝ))
      (groverChannel (gp22.n + 2) C) (ae_eps (gp22.M / 2 ^ gp22.n : ℝ) 2) ae_delta
      (Synthesis.grade C) :=
  ae_realizes gp22 (by norm_num) hR _ le_rfl

/-! ## A4 — the parametric lemma on the two-qubit AND network of the 19c tests -/

/-- `x₀ ∧ x₁` on two inputs (`M = 1`), the network of the 19c tests. -/
def n2 : Network := ⟨2, #[.input 0, .input 1, .and 0 1], [2]⟩

def cc2 : Circuit := (countingCircuit n2 2 2).toOption.getD default

/-- The Grover data of the network: its own predicate, `M = 1`. -/
def gpN2 : GroverData := ⟨2, 1, le_rfl, n2.pred 2, by decide +kernel⟩

example (h : countingCircuit n2 2 2 = .ok cc2) :
    Realizes (CountSpec 2 (gpN2.M / 2 ^ gpN2.n : ℝ)) (countPOVM gpN2.n 2 (gpN2.M / 2 ^ gpN2.n : ℝ))
        (groverChannel (gpN2.n + 2) cc2) (ae_eps (gpN2.M / 2 ^ gpN2.n : ℝ) 2) ae_delta
        (Synthesis.grade cc2) ∧
      AncRestore (gpN2.n + 2) cc2.nAnc cc2 (U_count gpN2.P 2 none) :=
  ae_parametric_lemma gpN2 (by norm_num) (by decide +kernel) rfl rfl rfl h _ le_rfl

-- the same with the data of `x₀ ∧ x₁` written directly (`hP` by evaluation)
example (h : countingCircuit n2 2 2 = .ok cc2) :
    Realizes (CountSpec 2 (gp22.M / 2 ^ gp22.n : ℝ)) (countPOVM gp22.n 2 (gp22.M / 2 ^ gp22.n : ℝ))
        (groverChannel (gp22.n + 2) cc2) (ae_eps (gp22.M / 2 ^ gp22.n : ℝ) 2) ae_delta
        (Synthesis.grade cc2) ∧
      AncRestore (gp22.n + 2) cc2.nAnc cc2 (U_count gp22.P 2 none) :=
  ae_parametric_lemma gp22 (by norm_num) (by decide +kernel) rfl rfl (by decide +kernel) h _ le_rfl

/-! ## Axioms (CLAUDE.md rule 10) -/

/-- info: 'CQRV.Grover.countPOVM_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countPOVM_measure

/-- info: 'CQRV.Grover.ae_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ae_realizes

/-- info: 'CQRV.Grover.ae_parametric_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ae_parametric_lemma

end CQRV.Tests.AmplitudeEstimation
