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
synthesizer; `#print axioms` for every proved theorem of Stage 6a, 6b-1, 6b-2, 6b-3 and 9a
(`lemma_6_3_2_xor`, `lemma_6_3_2` guarded by `#guard_msgs`); XOR / `if` networks; the Grover
oracle as the shifted `Circuit.append` of its two pieces at the MBU cut; `mbu_branch_basis` on
`|1,1,1⟩` in both branches. Stage 17a (PHASE2_SPEC.md §A.1): the phase gates `p` / `cp` — the
classifiers, `tCount_eq_isTPower`, adjoint, `validate`, JSON, `Circuit.decomposeCp` with
`decomposeCp_wf` and `decomposeCp_unitary` on a hand-built list, the `gateU` identities.
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

/-- The two AND records of the Grover oracle (no `prepare` gate: single positive atoms). -/
def groverRecs : List AndRec :=
  [⟨[], .data 0, .data 3, ⟨[.data 0], false⟩, ⟨[.data 3], false⟩⟩,
   ⟨[], .anc 0, .data 7, ⟨[.anc 0], false⟩, ⟨[.data 7], false⟩⟩]

-- The Grover oracle is `cmpBlocks ++ phaseFlip ++ uncBlocks` of its two AND records.
#guard groverOracle.gates ==
  cmpBlocks groverRecs 0 ++ Oracle.phaseFlip ⟨[.anc 1], false⟩ ++ uncBlocks groverRecs 0

-- `search_or` (`x0 ∨ x1 = ¬(¬x0 ∧ ¬x1)`): one AND record with both polarities negative, and a
-- negated output (`X Z X` on its ancilla).
#guard ((oracle searchOrSrc).toOption.map (·.gates)) ==
  some (cmpBlocks [⟨[.x (.data 0), .x (.data 1)], .data 0, .data 1, ⟨[.data 0], true⟩,
      ⟨[.data 1], true⟩⟩] 0 ++ Oracle.phaseFlip ⟨[.anc 0], true⟩ ++
    uncBlocks [⟨[.x (.data 0), .x (.data 1)], .data 0, .data 1, ⟨[.data 0], true⟩,
      ⟨[.data 1], true⟩⟩] 0)

-- `prepare` on single atoms emits only the polarity gates.
#guard Oracle.prepare ⟨[.data 2], true⟩ ⟨[.anc 0], false⟩ == .ok ([.x (.data 2)], .data 2, .anc 0)

-- The folding identities (`fold_eval`): `u ∧ ¬u = 0`, `u ∧ u = u`, `1 ∧ v = v`, `0 ∧ v = 0`.
#guard Oracle.fold ⟨[.data 0], false⟩ ⟨[.data 0], true⟩ == some ⟨[], false⟩
#guard Oracle.fold ⟨[.data 0], true⟩ ⟨[.data 0], true⟩ == some ⟨[.data 0], true⟩
#guard Oracle.fold ⟨[], true⟩ ⟨[.anc 1], false⟩ == some ⟨[.anc 1], false⟩
#guard Oracle.fold ⟨[], false⟩ ⟨[.anc 1], false⟩ == some ⟨[], false⟩
#guard Oracle.fold ⟨[.data 0], false⟩ ⟨[.data 1], false⟩ == none

-- `Aff.eval` on a basis state of `Reg 2 × Reg 1`: `x1 ⊕ 1` and the constant 1.
#guard (Aff.mk [.data 1] true).eval ((![true, false], ![false]) : Reg 2 × Reg 1) == true
#guard (Aff.mk [] true).eval ((![true, false], ![false]) : Reg 2 × Reg 1) == true

/-! ## Stage 9a — XOR networks (`CQRV.Circuit.OracleCorrectXor`, `lemma_6_3_2_xor`) -/

-- `prepare` with `pu ∈ v.lin` (u = x0 ⊕ x1, v = ¬(x0 ⊕ x2)): `Sv = x0 :: symDiff [x1] [x2]`,
-- pivot `x1`; and with `pu ∉ v.lin` (u = ¬(x0 ⊕ x1), v = x2 ⊕ anc0).
#guard Oracle.prepare ⟨[.data 0, .data 1], false⟩ ⟨[.data 0, .data 2], true⟩ ==
  .ok ([.cnot (.data 1) (.data 0), .cnot (.data 0) (.data 1), .cnot (.data 2) (.data 1),
    .x (.data 1)], .data 0, .data 1)
#guard Oracle.prepare ⟨[.data 0, .data 1], true⟩ ⟨[.data 2, .anc 0], false⟩ ==
  .ok ([.cnot (.data 1) (.data 0), .cnot (.anc 0) (.data 2), .x (.data 0)], .data 0, .data 2)

-- `prepare_ok` on every basis state of `Reg 3 × Reg 0` (the symmetric-difference case): after
-- `pre`, `x0` holds `x0 ⊕ x1` and `x1` holds `¬(x0 ⊕ x2)`; `preᴿ` undoes `pre`.
def symPre : List Gate :=
  [.cnot (.data 1) (.data 0), .cnot (.data 0) (.data 1), .cnot (.data 2) (.data 1), .x (.data 1)]

example : ∀ s : Reg 3 × Reg 0,
    (Qubit.data 0).get (permRun symPre s) = (Aff.mk [.data 0, .data 1] false).eval s ∧
      (Qubit.data 1).get (permRun symPre s) = (Aff.mk [.data 0, .data 2] true).eval s ∧
      permRun symPre.reverse (permRun symPre s) = s := by
  decide

-- `gather` on a basis state: the pivot gets the XOR of the set (`permRun_gather`).
example : ∀ s : Reg 3 × Reg 0,
    permRun (Oracle.gather [.data 1, .data 0, .data 2] (.data 1)) s =
      (Qubit.data 1).set (xorL [.data 1, .data 0, .data 2] s) s := by
  decide

-- `symDiff` = XOR of the linear parts (`xorL_symDiff`).
example : ∀ s : Reg 3 × Reg 1,
    xorL (symDiff [.data 0, .data 1, .anc 0] [.data 1, .data 2]) s =
      (xorL [.data 0, .data 1, .anc 0] s ^^ xorL [.data 1, .data 2] s) := by
  decide

/-- `if x0 then x1 ⊕ x3 else x2 ⊕ x1` as `toNetwork` builds it (Stage 3 mux
`b ⊕ (c ∧ (a ⊕ b))`): an XOR chain, one AND, a three-atom output. -/
def muxXorNet : Network :=
  ⟨4, #[.input 0, .input 1, .input 2, .input 3, .xor 1 3, .xor 2 1, .xor 4 5, .and 0 6, .xor 5 7],
    [8]⟩

def muxXorSrc : String :=
  "fn mux_xor(x: Vec Bool 4) -> Bool {
" ++
  "  if idx(x, 0) then (idx(x, 1) xor idx(x, 3)) else (idx(x, 2) xor idx(x, 1))
}
"

-- the DSL front end produces `muxXorNet` and the same oracle
#guard ((parse muxXorSrc >>= check >>= toNetwork).toOption.map fun N =>
  (N.nInputs, N.nodes.toList, N.outputs)) ==
    some (muxXorNet.nInputs, muxXorNet.nodes.toList, muxXorNet.outputs)

/-- `(x0 ⊕ x1) ∧ ¬(x0 ⊕ x2)`: the AND of two XORs sharing their pivot (`pu ∈ v.lin`). -/
def symNet : Network :=
  ⟨3, #[.input 0, .input 1, .input 2, .xor 0 1, .xor 0 2, .not 4, .and 3 5], [6]⟩

def muxXorOracle : Circuit :=
  match synthesizeOracle muxXorNet with
  | .ok c => c
  | .error _ => default

def symOracle : Circuit :=
  match synthesizeOracle symNet with
  | .ok c => c
  | .error _ => default

#guard (oracle muxXorSrc).toOption == some muxXorOracle
#guard (Network.pred muxXorNet 4 = fun x => if x 0 then x 1 ^^ x 3 else x 2 ^^ x 1 : Bool)
#guard symOracle.gates.take 4 == symPre

-- Lemma 6.3.2 for both XOR networks (side conditions by `rfl` / `decide`).
example : AncRestore 4 muxXorOracle.nAnc muxXorOracle (phaseOracle (muxXorNet.pred 4)) :=
  lemma_6_3_2_xor muxXorNet muxXorOracle (by rfl) (by decide)

example : AncRestore 3 symOracle.nAnc symOracle (phaseOracle (symNet.pred 3)) :=
  lemma_6_3_2_xor symNet symOracle (by rfl) (by decide)

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
#print axioms lemma_6_3_2_traced
#print axioms grover_pred_037_ancRestore
-- Stage 9a (`CQRV.Circuit.OracleCorrectXor`, `OracleCorrect`): Lemma 6.3.2 with XOR nodes.
#print axioms permRun_reverse
#print axioms perm_kraus
#print axioms permRun_gather
#print axioms xorL_symDiff
#print axioms prepare_ok

/-- info: 'CQRV.lemma_6_3_2_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_6_3_2_xor

/-- info: 'CQRV.lemma_6_3_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_6_3_2

/-! ## Stage 17a — exact phase gates `p` / `cp` (PHASE2_SPEC.md §A.1) -/

def q0 : Qubit := .data 0
def q1 : Qubit := .data 1

/-- `(isClifford, isTPower, isRotation)` of a gate. -/
def cls (g : Gate) : Bool × Bool × Bool := (g.isClifford, g.isTPower, g.isRotation)

-- `p a k`: Clifford iff 2^k ∣ 4a; T-power iff 2^k ∣ 8a and 2^k ∤ 4a (a divisibility condition, so
-- `p 2 4` is classified as `p 1 3`); rotation otherwise. `p 0 5` is the identity (Clifford).
#guard cls (.p 1 1 q0) == (true, false, false)
#guard cls (.p 1 2 q0) == (true, false, false)
#guard cls (.p 1 3 q0) == (false, true, false)
#guard cls (.p (-1) 3 q0) == (false, true, false)
#guard cls (.p 2 4 q0) == (false, true, false)
#guard cls (.p 3 3 q0) == (false, true, false)
#guard cls (.p 1 4 q0) == (false, false, true)
#guard cls (.p 0 5 q0) == (true, false, false)
#guard cls (.p (-3) 5 q0) == (false, false, true)
-- `cp a k`: Clifford iff 2^k ∣ 2a, never a T-power, otherwise a rotation.
#guard cls (.cp 1 1 q0 q1) == (true, false, false)
#guard cls (.cp 1 2 q0 q1) == (false, false, true)
#guard cls (.cp 2 2 q0 q1) == (true, false, false)
#guard cls (.cp (-1) 3 q0 q1) == (false, false, true)
-- `ifBit` looks inside for the classifiers (`isClifford` does not: the bit discipline is unchanged).
#guard (Gate.ifBit 0 (.p 1 3 q0)).isTPower && (Gate.ifBit 0 (.p 1 4 q0)).isRotation &&
  (Gate.ifBit 0 (.cp 1 1 q0 q1)).isTwoQubit && (Gate.ifBit 0 (.cz q0 q1)).isTwoQubit
-- `tCount` is the indicator of `isTPower`: 1 for the T-powers, 0 for Clifford, rotations, `cp`.
#guard [Gate.p 1 3 q0, .p 2 4 q0, .p 3 3 q0, .p (-1) 3 q0, .t q0, .tdg q0].map (·.tCount) ==
  [1, 1, 1, 1, 1, 1]
#guard [Gate.p 1 1 q0, .p 1 4 q0, .p 0 5 q0, .cp 1 2 q0 q1, .cp 1 1 q0 q1].map (·.tCount) ==
  [0, 0, 0, 0, 0]
example (g : Gate) : g.tCount = if g.isTPower then 1 else 0 := Gate.tCount_eq_isTPower g
example : (Gate.p 2 4 q0).tCount = 1 := by decide
-- Adjoint: `p (-a) k`, `cp (-a) k`; `adjointGates` reverses.
#guard (Gate.p 3 5 q0).adjoint == .p (-3) 5 q0 && (Gate.cp (-1) 2 q0 q1).adjoint == .cp 1 2 q0 q1
#guard adjointGates [.p 1 3 q0, .cp 1 2 q0 q1] == [.cp (-1) 2 q0 q1, .p (-1) 3 q0]
-- `render`: the angle as the fraction `a/2^k` of a full turn.
#guard (Gate.p 1 3 q0).render == "P(1/8) x[0]" &&
  (Gate.cp (-3) 5 q0 q1).render == "CP(-3/32) x[0] x[1]"
-- `Circuit.validate` / `wf`: `cp` on distinct qubits and `ifBit` over a Clifford `cp` / `p` pass;
-- `cp q q` and `ifBit` over a non-Clifford `p` / `cp` are rejected.
#guard (Circuit.mk 2 [.cp 1 2 q0 q1, .p 1 3 q1]).validate.isOk
#guard (Circuit.mk 2 [.measure q0 0, .ifBit 0 (.cp 1 1 q0 q1), .ifBit 0 (.p 1 2 q1)]).validate.isOk
#guard !(Circuit.mk 2 [.cp 1 2 q0 q0]).validate.isOk
#guard !(Circuit.mk 2 [.measure q0 0, .ifBit 0 (.p 1 3 q1)]).validate.isOk
#guard !(Circuit.mk 2 [.measure q0 0, .ifBit 0 (.cp 1 2 q0 q1)]).validate.isOk
#guard (Circuit.mk 2 [.cp 1 2 q0 q1]).wf && !(Circuit.mk 2 [.cp 1 2 q0 q0]).wf
#guard (Circuit.mk 2 [.measure q0 0, .ifBit 0 (.cp 1 1 q0 q1)]).wf &&
  !(Circuit.mk 2 [.measure q0 0, .ifBit 0 (.cp 1 2 q0 q1)]).wf
-- JSON export (`tests/diff/statevector.py` learns it in Stage 17b): `a` (possibly negative), `k`.
#guard (Circuit.mk 2 [.p (-3) 5 q0, .cp 1 2 q0 q1, .ifBit 0 (.p 1 1 q1)]).toJson.compress ==
  "{\"gates\":[{\"a\":-3,\"k\":5,\"op\":\"p\",\"q\":[0]},{\"a\":1,\"k\":2,\"op\":\"cp\",\"q\":[0,1]},\
  {\"a\":1,\"if\":0,\"k\":1,\"op\":\"p\",\"q\":[1]}],\"n_anc\":0,\"n_data\":2}"

/-! ### `Circuit.decomposeCp` (PHASE2_SPEC.md §A.1, §C.3) -/

/-- A `cp` to decompose (θ/2 = 1/8 of a turn), a controlled `cp` to leave alone, a `cp` with a
negative angle. -/
def cpList : List Gate :=
  [.h q0, .cp 1 2 q0 q1, .measure q1 0, .ifBit 0 (.cp 1 1 q0 q1), .cp (-3) 5 q1 q0]

#guard Circuit.decomposeCp cpList ==
  [.h q0, .p 1 3 q0, .p 1 3 q1, .cnot q0 q1, .p (-1) 3 q1, .cnot q0 q1,
   .measure q1 0, .ifBit 0 (.cp 1 1 q0 q1),
   .p (-3) 6 q1, .p (-3) 6 q0, .cnot q1 q0, .p 3 6 q0, .cnot q1 q0]
#guard (Circuit.mk 2 cpList).wf && (Circuit.mk 2 (Circuit.decomposeCp cpList)).wf
example : (⟨2, Circuit.decomposeCp cpList⟩ : Circuit).wf = true :=
  Circuit.decomposeCp_wf (C := ⟨2, cpList⟩) (by decide)
-- Every top-level `cp` of `cpList` has distinct operands and its target in `Reg 2 × Reg 0`, so the
-- decomposition has the same unitary semantics.
example : unitaryDenote 2 0 (Circuit.decomposeCp cpList) = unitaryDenote 2 0 cpList :=
  decomposeCp_unitary 2 0 cpList (by decide)
-- The identities as theorems about `gateU`, at the 2-qubit register.
example (q : Qubit) : gateU 2 0 (.p 1 1 q) = gateU 2 0 (.z q) := gateU_p_one_one 2 0 q
example (q : Qubit) : gateU 2 0 (.p 1 2 q) = gateU 2 0 (.s q) := gateU_p_one_two 2 0 q
example (q : Qubit) : gateU 2 0 (.p (-1) 2 q) = gateU 2 0 (.sdg q) := gateU_p_neg_one_two 2 0 q
example (q : Qubit) : gateU 2 0 (.p 1 3 q) = gateU 2 0 (.t q) := gateU_p_one_three 2 0 q
example (q : Qubit) : gateU 2 0 (.p (-1) 3 q) = gateU 2 0 (.tdg q) := gateU_p_neg_one_three 2 0 q
example (c t : Qubit) : gateU 2 0 (.cp 1 1 c t) = gateU 2 0 (.cz c t) := gateU_cp_one_one 2 0 c t

/-- info: 'CQRV.decomposeCp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomposeCp_unitary

/-- info: 'CQRV.gateU_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gateU_mem_unitaryGroup

#print axioms decomposeCp_gate

-- Stage 17b (Stage 17a review, decision 4): the circuit-level corollary the QIR emitter cites
/-- info: 'CQRV.decomposeCp_unitary_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomposeCp_unitary_wf
#print axioms Circuit.decomposeCp_wf
#print axioms gateU_adjoint
#print axioms phaseOf_add_self

end CQRV.Tests.Semantics
