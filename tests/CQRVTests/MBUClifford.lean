module

import CQRV.Circuit.MBUClifford
meta import CQRV.Circuit.MBUClifford

/-!
# Tests for `CQRV.Circuit.MBUClifford` (Stage 22b; PHASE2_SPEC §B.1; report §6.2.2)

The axiom lines of `isQuadratic_iff_deriv_affine`, `phaseCircuitQuad_phaseImpl`, `mbu_quadratic`
and `clifford_iff_quadratic` (the standard three); `decide`-level checks through the derivative
criterion that `x0 ∧ x1` and `x0 ⊕ x1 ⊕ (x1 ∧ x2)` are quadratic and that `x0 ∧ x1 ∧ x2` is not;
`phaseCircuitQuad` of `x0 ∧ x1` is `[CZ x0 x1]`; the `AncRestore` conclusion of `mbu_quadratic` on
the AND gadget.
-/

namespace CQRV.Tests.MBUClifford

open CQRV CQRV.Synthesis
open scoped MState

/-- info: 'CQRV.isQuadratic_iff_deriv_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isQuadratic_iff_deriv_affine

/-- info: 'CQRV.phaseCircuitQuad_phaseImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phaseCircuitQuad_phaseImpl

/-- info: 'CQRV.mbu_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_quadratic

/-- info: 'CQRV.clifford_iff_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clifford_iff_quadratic

/-! ## The derivative criterion at small `n` -/

/-- `x0 ∧ x1` is quadratic. -/
example : IsQuadratic (fun x : Reg 2 => x 0 && x 1) :=
  (isQuadratic_iff_deriv_affine _).2 (by decide)

/-- `x0 ⊕ x1 ⊕ (x1 ∧ x2)` is quadratic. -/
example : IsQuadratic (fun x : Reg 3 => xor (xor (x 0) (x 1)) (x 1 && x 2)) :=
  (isQuadratic_iff_deriv_affine _).2 (by decide)

/-- `x0 ∧ x1 ∧ x2` is not quadratic: its derivative in `x0` is `x1 ∧ x2`, not affine. -/
example : ¬ IsQuadratic (fun x : Reg 3 => x 0 && x 1 && x 2) := fun h =>
  absurd ((isQuadratic_iff_deriv_affine _).1 h) (by decide)

/-- Hence its sign diagonal (the CCZ matrix) is not Clifford. -/
example : ¬ IsCliffordDiag (phaseDiag fun x : Reg 3 => x 0 && x 1 && x 2) := fun h =>
  absurd ((clifford_iff_quadratic _).1 h)
    (fun h' => absurd ((isQuadratic_iff_deriv_affine _).1 h') (by decide))

/-! ## The constructive direction on the AND -/

/-- The coefficients of `x0 ∧ x1`: no linear term, `b 0 1 = 1`. -/
def bAnd : Fin 2 → Fin 2 → ZMod 2 := fun i j => if i = 0 ∧ j = 1 then 1 else 0

-- `phaseCircuitQuad` of `x0 ∧ x1` is `[CZ x0 x1]`.
#guard phaseCircuitQuad (fun _ : Fin 2 => (0 : ZMod 2)) bAnd == [.cz (.data 0) (.data 1)]

/-- `x0 ∧ x1 = quadForm 0 0 bAnd`. -/
theorem and_quadForm : ∀ x : Reg 2, toZ2 (x 0 && x 1) = quadForm 0 (fun _ => 0) bAnd x := by
  decide

/-- `phaseCircuitQuad` of the AND is a phase implementation of the AND on the MBU register. -/
example : PhaseImpl 2 1 (phaseCircuitQuad (fun _ : Fin 2 => (0 : ZMod 2)) bAnd) (fun x => x 0 && x 1) :=
  phaseCircuitQuad_phaseImpl and_quadForm

/-- `mbu_quadratic` on the AND gadget: `mbuCircuit`'s statement, since `phaseCircuitQuad` of the AND
is `[CZ x0 x1]` and `czU = phaseOracle (x0 ∧ x1)`. -/
example (ρ : MState (Reg 2)) :
    channelDenote 2 1 mbuCircuit (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 :=
  mbu_quadratic (C := mbuCircuit) mbuCircuit_WF
    (B := TempLogicalAND (.data 0) (.data 1) (.anc 0)) (t := .anc 0) (j := 0)
    (a := fun _ => 0) (b := bAnd) (by decide) ⟨0, by norm_num, rfl⟩ and_quadForm
    tempLogicalAND_computesInto ρ

end CQRV.Tests.MBUClifford
