module

import CQRV.Grover.SearchUnknownM

/-!
# Tests for `CQRV.Grover.SearchUnknownM` (Stage 21b2; PHASE2_SPEC §A.7, §A.9 (9)–(12); report §2.3.2)

The axiom lines of `measured_composition_pseudo`, `measurePrepare_encode`, `search_unknown_M`,
`domain_8_32_5` and `search_unknown_M_8_32_5` (the standard three), `searchStage_encode` as an
`example`, and the corollary at `(8, 32, 5)` applied with its hypotheses as hypotheses (as the
`countSem` test does).
-/

namespace CQRV.Tests.SearchUnknownM

open CQRV CQRV.Patterns CQRV.Grover CQRV.Synthesis CQRV.Certify

/-- info: 'CQRV.measured_composition_pseudo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms measured_composition_pseudo

/-- info: 'CQRV.measurePrepare_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms measurePrepare_encode

/-- info: 'CQRV.Grover.search_unknown_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms search_unknown_M

/-- info: 'CQRV.Grover.domain_8_32_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms domain_8_32_5

/-- info: 'CQRV.Grover.search_unknown_M_8_32_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms search_unknown_M_8_32_5

/-- Stage 2 on an encoded outcome is the Grover channel of that outcome's circuit. -/
example (C : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ) → Circuit) (g : Grade)
    (y : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ)) :
    (searchStage 8 C g).chan (encode y) = (groverChannel 8 (C y)).chan (encode ()) :=
  searchStage_encode 8 C g y

/-- The domain lemma at the ideal point and at an outcome in the domain. -/
example : (Sum.inr () : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ)) = Sum.inr () ∨
    ∃ k : Reg 5, (Sum.inr () : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ)) = Sum.inl k ∧
      (k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 28 ∨ k.toNat = 29) :=
  domain_8_32_5 _ (by
    change |((32 : ℕ) / 2 ^ 8 : ℝ) - ((32 : ℕ) / 2 ^ 8 : ℝ)| ≤ _
    rw [sub_self, abs_zero]
    unfold ae_eps
    positivity)

/-- The corollary at `grover_pred_037`, `(n, M, m) = (8, 32, 5)`, shape tree, mode MBU, with its
hypotheses as hypotheses: the composite realizes "a solution of `P`, after an estimate within
`ae_eps (1/8) 5` of `1/8`" with ε = `ae_eps (1/8) 5`, δ = `ae_delta + groverDelta 2 8 32` and
grade `grade C₁ ⊕ g₂`. -/
example (O : OracleCert 8) (D : DiffusionCert 8) (hWF : O.N.WF) (h1 : O.N.outputs.length = 1)
    (hcard : (Finset.univ.filter fun x => O.P x = true).card = 32) {C₁ C₀ : Circuit}
    (hC₁ : countingCircuit O.N 8 5 none .tree .mbu = .ok C₁) (hC₀ : groverCircuit O.N 8 2 = .ok C₀)
    (C : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ) → Circuit)
    (htab : ∀ k : Reg 5, (k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 28 ∨ k.toNat = 29) →
      C (Sum.inl k) = C₀)
    (hideal : C (Sum.inr ()) = C₀) (g₂ : Grade) (hg₂ : ∀ y, Synthesis.grade (C y) ≤ g₂) :
    Realizes ((SearchAfterCount 5 ((32 : ℕ) / 2 ^ 8 : ℝ) O.P (ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5)).comp
          (CountSpec 5 ((32 : ℕ) / 2 ^ 8 : ℝ)))
        (basisPOVM 8)
        (measuredComp (groverChannel (8 + 5) C₁) (countPOVM 8 5 ((32 : ℕ) / 2 ^ 8 : ℝ))
          (searchStage 8 C g₂))
        (ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5) (ae_delta + ((groverDelta 2 8 32 : ℚ) : ℝ))
        (Synthesis.grade C₁ + g₂) ∧
      ∀ y, (groverChannel 8 (C y)).grade ≤ (searchStage 8 C g₂).grade :=
  search_unknown_M_8_32_5 O D hWF h1 hcard .tree .mbu hC₁ hC₀ C htab hideal g₂ hg₂

end CQRV.Tests.SearchUnknownM
