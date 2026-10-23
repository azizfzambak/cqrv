module

import CQRV.Circuit.Basic
import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
meta import CQRV.Circuit.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic

/-!
# Tests for `CQRV.Circuit.Semantics` and `CQRV.Circuit.Restoration` (report §6.2, §6.3.2, §9.1.1)

`Circuit.WF` on the Stage 5 Grover oracle and on ill-formed circuits; the hand-written
`groverNet` / `groverOracle` of the Grover instance against the DSL front end and the
synthesizer; `#print axioms` for every proved theorem of Stage 6a, 6b-1, 6b-2 and 6b-3; the Grover
oracle as the shifted `Circuit.append` of its two pieces at the MBU cut; `mbu_branch_basis` on
`|1,1,1⟩` in both branches.
-/

namespace CQRV.Tests.Semantics

open CQRV CQRV.DSL CQRV.Synthesis

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"

/-- Front end + network + oracle. -/
def oracle (src : String) : Except Diagnostic Circuit :=
  parse src >>= check >>= toNetwork >>= synthesizeOracle

/-! ## Decision 3 — `Circuit.WF` -/

-- The Stage 5 Grover oracle (from the source) is well formed and is `groverOracle`.
#guard (oracle groverSrc).toOption == some groverOracle
#guard groverOracle.wf
#guard groverOracle.nBits == 2 && groverOracle.nAnc == 2
#guard mbuCircuit.wf
-- A classical bit read before it is written.
#guard !(Circuit.mk 2 [.ifBit 0 (.x (.data 0)), .measure (.data 1) 0]).wf
-- A classical bit written twice; a bit index beyond the measurements.
#guard !(Circuit.mk 2 [.measure (.data 0) 0, .measure (.data 1) 0]).wf
#guard !(Circuit.mk 2 [.measure (.data 0) 1]).wf
-- A data qubit out of range; a repeated operand (also under `ifBit`).
#guard !(Circuit.mk 2 [.x (.data 2)]).wf
#guard !(Circuit.mk 2 [.cnot (.data 0) (.data 0)]).wf
#guard !(Circuit.mk 2 [.measure (.data 0) 0, .ifBit 0 (.cz (.data 1) (.data 1))]).wf

/-! ## The Grover instance: `groverNet` is the predicate of the source -/

-- Same oracle as the network `toNetwork` builds from the source.
#guard (synthesizeOracle groverNet).toOption == some groverOracle
#guard groverNet.xorFree
-- Truth table of `groverNet` = `x0 ∧ x3 ∧ x7`, against the front end.
#guard (List.range 256).all fun k =>
  let x : Nat → Bool := fun i => (k >>> i) % 2 == 1
  ((parse groverSrc >>= check >>= toNetwork).map (·.eval x)).toOption ==
    some (groverNet.eval x) &&
  groverNet.eval x == [x 0 && x 3 && x 7]

/-! ## DSL bridge (Stage 6a review): `toNetwork` of the source is `groverNet` -/

/-- Field-by-field equality of networks (`Network` derives no `BEq`). -/
def netEq (N M : Network) : Bool :=
  N.nInputs == M.nInputs && N.nodes.toList == M.nodes.toList && N.outputs == M.outputs

#guard match parse groverSrc >>= check >>= toNetwork with
  | .ok N => netEq N groverNet
  | .error _ => false
-- `groverPred` (on `Reg 8`) is `x0 ∧ x3 ∧ x7` on all 256 inputs.
#guard (List.range 256).all fun k =>
  let x : Reg 8 := fun i => (k >>> i.val) % 2 == 1
  groverPred x == (x 0 && x 3 && x 7) &&
    groverPred x == ((k % 2 == 1) && ((k >>> 3) % 2 == 1) && ((k >>> 7) % 2 == 1))

/-! ## Stage 6b-1 review: the Grover oracle is a shifted append at the MBU cut

With bits numbered in measurement order, the oracle up to `free anc1` (bit 0) and the last MBU
block written with bit 0 are both well formed, and `Circuit.append` (shift by 1) gives back the
oracle exactly. -/

/-- The oracle through `free anc[1]`: compute, `Z`, MBU of anc[1] (bit 0). -/
def groverPiece₁ : Circuit := ⟨8, groverOracle.gates.take 34⟩

/-- The MBU of anc[0], written with bit 0. -/
def groverPiece₂ : Circuit :=
  ⟨8, UncomputeTempLogicalAND (.data 0) (.data 3) (.anc 0) 0 ++ [.free (.anc 0)]⟩

#guard groverPiece₁.wf && groverPiece₂.wf
#guard groverPiece₁.append groverPiece₂ == groverOracle
#guard (groverPiece₁.append groverPiece₂).nBits == groverPiece₁.nBits + groverPiece₂.nBits

/-! ## Stage 6b-2: `mbu_branch_basis` on the 3-qubit register

At `s = |1,1,1⟩` (a = b = 1, target t = anc[0] holding `1 ∧ 1`), both branches of the uncompute
block give `(1/√2) |1,1,0⟩`, by the lemma (no recomputation). -/

open Matrix in
example : krausOps 2 1 1 (UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0) ![false] *ᵥ
      basisVec ((![true, true], ![true]) : Reg 2 × Reg 1) =
    ((Real.sqrt 2)⁻¹ : ℂ) •
      basisVec ((Qubit.anc 0).set false ((![true, true], ![true]) : Reg 2 × Reg 1)) :=
  mbu_branch_basis _ _ _ 0 (by decide) (by decide) (by decide) _ _ (by decide)

open Matrix in
example : krausOps 2 1 1 (UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0) ![true] *ᵥ
      basisVec ((![true, true], ![true]) : Reg 2 × Reg 1) =
    ((Real.sqrt 2)⁻¹ : ℂ) •
      basisVec ((Qubit.anc 0).set false ((![true, true], ![true]) : Reg 2 × Reg 1)) :=
  mbu_branch_basis _ _ _ 0 (by decide) (by decide) (by decide) _ _ (by decide)

-- `Circuit.WF_append` on the Grover pieces (the `#guard` above checks the same by evaluation).
example : (groverPiece₁.append groverPiece₂).WF :=
  Circuit.WF_append rfl (by decide) (by decide)

/-! ## Stage 6b-3 — the synthesized oracle as AND records (`CQRV.Circuit.OracleCorrect`) -/

def searchOrSrc : String := include_str "../../examples/search_or.cqr"

-- The Grover oracle is `cmpBlocks ++ phaseFlip ++ uncBlocks` of its two AND records.
#guard groverOracle.gates ==
  cmpBlocks [⟨.data 0, false, .data 3, false⟩, ⟨.anc 0, false, .data 7, false⟩] 0 ++
    Oracle.phaseFlip ⟨[.anc 1], false⟩ ++
    uncBlocks [⟨.data 0, false, .data 3, false⟩, ⟨.anc 0, false, .data 7, false⟩] 0

-- `search_or` (`x0 ∨ x1 = ¬(¬x0 ∧ ¬x1)`): one AND record with both polarities negative, and a
-- negated output (`X Z X` on its ancilla).
#guard ((oracle searchOrSrc).toOption.map (·.gates)) ==
  some (cmpBlocks [⟨.data 0, true, .data 1, true⟩] 0 ++ Oracle.phaseFlip ⟨[.anc 0], true⟩ ++
    uncBlocks [⟨.data 0, true, .data 1, true⟩] 0)

-- `prepare` on single atoms emits only the polarity gates (`prepare_single`).
#guard Oracle.prepare ⟨[.data 2], true⟩ ⟨[.anc 0], false⟩ ==
  .ok ((⟨.data 2, true, .anc 0, false⟩ : AndRec).pre, .data 2, .anc 0)

-- The folding identities (`fold_eval`): `u ∧ ¬u = 0`, `u ∧ u = u`, `1 ∧ v = v`, `0 ∧ v = 0`.
#guard Oracle.fold ⟨[.data 0], false⟩ ⟨[.data 0], true⟩ == some ⟨[], false⟩
#guard Oracle.fold ⟨[.data 0], true⟩ ⟨[.data 0], true⟩ == some ⟨[.data 0], true⟩
#guard Oracle.fold ⟨[], true⟩ ⟨[.anc 1], false⟩ == some ⟨[.anc 1], false⟩
#guard Oracle.fold ⟨[], false⟩ ⟨[.anc 1], false⟩ == some ⟨[], false⟩
#guard Oracle.fold ⟨[.data 0], false⟩ ⟨[.data 1], false⟩ == none

-- `Aff.eval` on a basis state of `Reg 2 × Reg 1`: `x1 ⊕ 1` and the constant 1.
#guard (Aff.mk [.data 1] true).eval ((![true, false], ![false]) : Reg 2 × Reg 1) == true
#guard (Aff.mk [] true).eval ((![true, false], ![false]) : Reg 2 × Reg 1) == true

/-! ## Axiom audit (CLAUDE.md rule 10) -/

-- Proved, expected axioms only `propext`, `Classical.choice`, `Quot.sound`:
#print axioms gateU_mem_unitaryGroup
#print axioms unitaryDenote_mem_unitaryGroup
#print axioms krausOps_complete
#print axioms phaseDiag_mem_unitaryGroup
#print axioms tempLogicalAND_correct
#print axioms AncRestore.traced
#print axioms Circuit.WF.bitsOk
#print axioms channelDenote_of_WF
-- Stage 6b-1:
#print axioms ancRestore_of_kraus
#print axioms mbu_channel_correct
#print axioms channelDenote_append
#print axioms AncRestore.comp
-- Stage 6b-2 (`CQRV.Circuit.OracleBlocks`):
#print axioms Circuit.WF_append
#print axioms krausOps_append_mulVec
#print axioms krausOps_append_shift_mulVec
#print axioms tempLogicalAND_correct_lift
#print axioms tempLogicalAND_kraus_basis
#print axioms mbu_branch_basis
#print axioms z_basis
#print axioms x_basis
#print axioms h_basis
#print axioms cnot_basis
#print axioms cz_basis
#print axioms Qubit.set_comm
-- Stage 6b-3 (`CQRV.Circuit.OracleCorrect`): Lemma 6.3.2 for xor-free networks and its parts.
#print axioms fold_eval
#print axioms step_ok_inv
#print axioms fold_inv
#print axioms cmp_kraus
#print axioms unc_kraus
#print axioms chain_kraus
#print axioms phaseFlip_kraus
#print axioms Circuit.WF.gatesOk
#print axioms kraus_mul_ancProj
#print axioms lemma_6_3_2
#print axioms lemma_6_3_2_traced
#print axioms grover_pred_037_ancRestore

end CQRV.Tests.Semantics
