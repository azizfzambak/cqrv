module

import CQRV.Circuit.MBUBoundary
meta import CQRV.Circuit.MBUBoundary

/-!
# Tests for `CQRV.Circuit.MBUBoundary` (Stage 22c; PHASE2_SPEC §B.1; report §6.2.2, §9.1.1)

The axiom lines of `gateU_isClifford`, `isCliffordDiag_of_tensor`, `mbu_wf_forces_quadratic` and
`mbu_exactly_quadratic` (the standard three); `H`, `S`, `CNOT` and `CZ` Clifford at a small
register; the Pauli product rule at a small register; `mbu_wf_forces_quadratic` on `mbuCircuit`
gives `IsQuadratic (x0 ∧ x1)`; and no well-formed MBU circuit of this IR has a phase implementation
of `x0 ∧ x1 ∧ x2` (CCZ is not a correction the IR can express).
-/

namespace CQRV.Tests.MBUBoundary

open CQRV CQRV.Synthesis Matrix

/-- info: 'CQRV.gateU_isClifford' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gateU_isClifford

/-- info: 'CQRV.isCliffordDiag_of_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isCliffordDiag_of_tensor

/-- info: 'CQRV.mbu_wf_forces_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_wf_forces_quadratic

/-- info: 'CQRV.mbu_exactly_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mbu_exactly_quadratic

/-! ## The IR Clifford gates at a small register -/

example : IsClifford (gateU 2 1 (.h (.data 0))) := gateU_isClifford _ rfl
example : IsClifford (gateU 2 1 (.s (.data 1))) := gateU_isClifford _ rfl
example : IsClifford (gateU 2 1 (.cnot (.data 0) (.anc 0))) := gateU_isClifford _ rfl
example : IsClifford (gateU 2 1 (.cz (.data 0) (.data 1))) := gateU_isClifford _ rfl
example : IsClifford (gateU 2 1 (.p 1 2 (.data 0))) := gateU_isClifford _ (by decide)

-- `T` is not an IR Clifford gate.
#guard (Gate.t (.data 0)).isClifford == false

/-- The product rule at a one-qubit register: `X · Z = −Z · X` as Paulis (`Z X = (−1)^{⟨e, e⟩} X Z`). -/
example : pauliMono (n := 1) (a := 0) zeroV (unitV (.data 0)) 1 * pauliMono (unitV (.data 0)) zeroV 1 =
    pauliMono (xorV zeroV (unitV (.data 0))) (xorV (unitV (.data 0)) zeroV) (1 * 1 * sgnZ 1) := by
  rw [pauliMono_mul, ip_unitV, get_unitV_self (by decide), toZ2]
  rfl

/-- The generator form of the task text follows from the definition. -/
example (U : Matrix (Reg 2 × Reg 1) (Reg 2 × Reg 1) ℂ) (hU : IsClifford U) (q : Qubit) :
    IsPauli (U * gateU 2 1 (.x q) * Uᴴ) ∧ IsPauli (U * gateU 2 1 (.z q) * Uᴴ) :=
  ⟨hU.conj_X q, hU.conj_Z q⟩

/-! ## The boundary on the AND gadget and on the three-input AND -/

/-- `mbu_wf_forces_quadratic` on `mbuCircuit`: `x0 ∧ x1` is quadratic. -/
example : IsQuadratic (fun x : Reg 2 => x 0 && x 1) :=
  mbu_wf_forces_quadratic (C := mbuCircuit) mbuCircuit_WF
    (B := TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)]) (t := .anc 0) (j := 0)
    (O := [.cz (.data 0) (.data 1)]) rfl cz_phaseImpl

/-- No well-formed MBU circuit of this IR corrects a three-input AND: with any measurement-free
block `B` on three data qubits, no `O` with `PhaseImpl 3 2 O (x0 ∧ x1 ∧ x2)` fits a well-formed
`B; Z t; mbuUncompute t j O` — `x0 ∧ x1 ∧ x2` is not quadratic. -/
example (B : List Gate) (hB : ∀ g ∈ B, g.qubitsOk 3 = true ∧ g.isUnitary = true) :
    ¬ ∃ (j : ℕ) (O : List Gate) (C : Circuit), C.nData = 3 ∧ C.WF ∧
        C.gates = B ++ [.z (.anc 0)] ++ mbuUncompute (.anc 0) j O ∧
        PhaseImpl 3 2 O (fun x : Reg 3 => x 0 && x 1 && x 2) := fun h =>
  absurd ((mbu_exactly_quadratic hB ⟨0, by norm_num, rfl⟩ _).1 h)
    (fun h' => absurd ((isQuadratic_iff_deriv_affine _).1 h') (by decide))

/-- And such a circuit exists for the parity `x0 ⊕ x1` with the empty block. -/
example : ∃ (j : ℕ) (O : List Gate) (C : Circuit), C.nData = 2 ∧ C.WF ∧
    C.gates = [] ++ [.z (.anc 0)] ++ mbuUncompute (.anc 0) j O ∧
    PhaseImpl 2 1 O (fun x : Reg 2 => xor (x 0) (x 1)) :=
  (mbu_exactly_quadratic (B := []) (by simp) ⟨0, by norm_num, rfl⟩ _).2
    ((isQuadratic_iff_deriv_affine _).2 (by decide))

end CQRV.Tests.MBUBoundary
