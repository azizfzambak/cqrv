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
synthesizer; `#print axioms` for every proved theorem of Stage 6a and Stage 6b-1; the Grover
oracle as the shifted `Circuit.append` of its two pieces at the MBU cut.
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
-- Proved from `lemma_6_3_2`, which is a tracked `sorry`: these show `sorryAx` until 6b.
#print axioms lemma_6_3_2_traced
#print axioms grover_pred_037_ancRestore

end CQRV.Tests.Semantics
