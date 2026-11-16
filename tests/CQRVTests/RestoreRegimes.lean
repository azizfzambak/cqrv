module

import CQRV.Circuit.RestoreRegimes
meta import CQRV.Circuit.RestoreRegimes

/-!
# Tests for `CQRV.Circuit.RestoreRegimes` (Stage 23b; PHASE2_SPEC §B.2; report §6.2.3)

The axiom lines of `ancRestoreDirty_of_kraus`, `AncRestoreDirty.toClean`, `AncRestoreDirty.comp`,
`reset_not_dirty`, `AncRestoreDirty.toCond`, `AncRestoreCond.toClean` and `AncRestoreCond.comp`
(the standard three), and of the R2 theorems `supportFactor`, `AncRestore.toCond_true`,
`ancRestoreCond_true_iff` with the iff used on the MBU gadget and the CZ instance; the dirty phase gadget is dirty restoring (and hence conditionally clean and
clean); `mbuCircuit` is not dirty restoring; the conditionally clean instance `CZ(x0, anc 0)` with
both strictness facts; the composition laws on the instances. The KG bridge is tested in
`CQRVTests.KGRegime`.
-/

namespace CQRV.Tests.RestoreRegimes

open CQRV CQRV.Synthesis Matrix
open scoped MState Kronecker

/-- info: 'CQRV.ancRestoreDirty_of_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ancRestoreDirty_of_kraus

/-- info: 'CQRV.AncRestoreDirty.toClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestoreDirty.toClean

/-- info: 'CQRV.AncRestoreDirty.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestoreDirty.comp

/-- info: 'CQRV.reset_not_dirty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reset_not_dirty

/-- info: 'CQRV.AncRestoreDirty.toCond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestoreDirty.toCond

/-- info: 'CQRV.AncRestoreCond.toClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestoreCond.toClean

/-- info: 'CQRV.AncRestoreCond.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestoreCond.comp

/-! ## R2 (REVIEW_RESPONSE_1 row 2) — Clean ⇔ Cond(true) -/

/-- info: 'CQRV.supportFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supportFactor

/-- info: 'CQRV.AncRestore.toCond_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AncRestore.toCond_true

/-- info: 'CQRV.ancRestoreCond_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ancRestoreCond_true_iff

/-- The MBU gadget is clean (`mbu_channel_correct`), hence conditionally clean under `true`. -/
example : AncRestoreCond 2 1 mbuCircuit czU (fun _ => true) :=
  ancRestoreCond_true_iff.mpr mbu_channel_correct

/-- And back: the CZ instance's conditional statement under `true` is its clean statement. -/
example : AncRestore 1 1 czCondCircuit 1 :=
  ancRestoreCond_true_iff.mp (czCond_cond.mono fun _ _ => rfl)

/-! ## The dirty phase gadget -/

#guard dirtyGadget.wf
#guard dirtyGadget.gates.all Gate.isUnitary

/-- The gadget is dirty restoring with `CZ`. -/
example : AncRestoreDirty 2 1 dirtyGadget czU := dirtyGadget_dirty

/-- The hierarchy on the gadget: dirty ⇒ conditionally clean (any condition) ⇒ clean. -/
example : AncRestoreCond 2 1 dirtyGadget czU (fun x => x 0) :=
  dirtyGadget_dirty.toCond (by decide) _

example : AncRestore 2 1 dirtyGadget czU := dirtyGadget_dirty.toClean

example : AncRestore 2 1 dirtyGadget czU :=
  (dirtyGadget_dirty.toCond (by decide) (fun x => x 0)).toClean

/-- Two gadgets in sequence are dirty restoring with `CZ · CZ`. -/
example : AncRestoreDirty 2 1 (dirtyGadget.append dirtyGadget) (czU * czU) :=
  dirtyGadget_dirty.comp (by decide) (by decide) dirtyGadget_dirty

/-- The gadget acts as `CZ ⊗ 1` on every state of the register, not only on products. -/
example (ω : MState (Reg 2 × Reg 1)) :
    (channelDenote 2 1 dirtyGadget ω).m =
      (czU.val ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ)) * ω.m * (czU.val ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ))ᴴ :=
  dirtyGadget_dirty.all (by decide)  ω

/-! ## The reset is never dirty -/

/-- `mbuCircuit` is not dirty restoring, for any `U`. -/
example (U : 𝐔[Reg 2]) : ¬ AncRestoreDirty 2 1 mbuCircuit U := mbuCircuit_not_dirty U

/-- Nor is MBU without its correction (the 23a `mbuNoCorr'`): `measure; ifBit (X t)` ends it. -/
example (U : 𝐔[Reg 2]) :
    ¬ AncRestoreDirty 2 1 ⟨2, TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ mbuUncompute (.anc 0) 0 []⟩ U :=
  reset_not_dirty' (by decide) (B := TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.h (.anc 0)])
    rfl ⟨0, by norm_num, rfl⟩ U

/-! ## The conditionally clean instance `CZ(x0, anc 0)` -/

#guard czCondCircuit.wf

/-- Conditionally clean with `U = 1` under `x0`. -/
example : AncRestoreCond 1 1 czCondCircuit 1 (fun x => x 0) := czCond_cond

/-- Clean. -/
example : AncRestore 1 1 czCondCircuit 1 := czCond_clean

/-- Strictness (i): conditionally clean but not dirty. -/
example (U : 𝐔[Reg 1]) : ¬ AncRestoreDirty 1 1 czCondCircuit U := czCond_not_dirty U

/-- Strictness (ii): clean but not conditionally clean under `cond ≡ false`. -/
example (U : 𝐔[Reg 1]) : ¬ AncRestoreCond 1 1 czCondCircuit U (fun _ => false) :=
  czCond_not_cond_false U

/-- Dirty ⇔ conditionally clean under `false`. -/
example (U : 𝐔[Reg 1]) : AncRestoreDirty 1 1 czCondCircuit U ↔ AncRestoreCond 1 1 czCondCircuit U (fun _ => false) :=
  ancRestoreDirty_iff_cond_false (by decide)

/-- Monotonicity: conditionally clean under `x0` is conditionally clean under `true`. -/
example : AncRestoreCond 1 1 czCondCircuit 1 (fun _ => true) :=
  czCond_cond.mono (fun _ _ => rfl)

/-- Composition with a diagonal first block: two `CZ(x0, anc 0)` under `x0`. -/
example : AncRestoreCond 1 1 (czCondCircuit.append czCondCircuit) (1 * 1) (fun x => x 0) :=
  AncRestoreCond.comp_diag (φ := fun _ => 1) (Matrix.diagonal_one).symm (by decide) (by decide)
    czCond_cond czCond_cond

/-- The composite of the two is clean. -/
example : AncRestore 1 1 (czCondCircuit.append czCondCircuit) (1 * 1) :=
  (AncRestoreCond.comp_diag (φ := fun _ => 1) (Matrix.diagonal_one).symm (by decide) (by decide)
    czCond_cond czCond_cond).toClean

end CQRV.Tests.RestoreRegimes
