module

import CQRV.Grover.Basic
meta import CQRV.Grover.Basic

/-!
# Tests for `CQRV.Grover.MczFew` (report §6.2, §6.2.4, §8.2, §9.5.2; Stage 12c)

The restoration proof of the few-ancilla MCZ, candidate B (`mczFew 8 .logDepth`), and of the
diffusion around it. Every Stage 12c theorem is pinned to (a subset of) the standard three axioms with
`#guard_msgs` (§9.5.1): the test build fails if one acquires `sorryAx` or another axiom.
-/

namespace CQRV.Tests.MczFewCorrect

open CQRV CQRV.Grover CQRV.Synthesis CQRV.Synthesis.MczFew

/-! ## The schedule the proof is about -/

-- The kernel-evaluable copy of the schedule agrees with the compiled one (`plan_8_logDepth`
-- is the kernel's evaluation; this is the compiler's).
#guard plan 8 .logDepth == (steps8, us8)
#guard (mczFew 8 .logDepth).toOption == some mczFew8
-- Two AND (MBU) steps, four relative-phase Toffoli pairs, two classical bits.
#guard nAnd steps8 == 2
#guard (steps8.filter (!·.2.2.2)).length == 4
#guard mczFew8.nBits == 2
#guard mczFew8.nAnc == 2

/-! ## Axioms (items 1–6) -/

/-- info: 'CQRV.Grover.rtof_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rtof_basis

/-- info: 'CQRV.Grover.rtofPhase_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rtofPhase_pair

/-- info: 'CQRV.Grover.rtof_pair_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rtof_pair_kraus

/-- info: 'CQRV.Grover.steps_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms steps_kraus

/-- info: 'CQRV.Grover.mczFew_kraus_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mczFew_kraus_basis

/--
info: 'CQRV.Grover.mczFew_logDepth_8_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mczFew_logDepth_8_classical

/--
info: 'CQRV.Grover.mczFew_ladder_8_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mczFew_ladder_8_classical

/-- info: 'CQRV.Grover.mczFew_ancRestore_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mczFew_ancRestore_8

/--
info: 'CQRV.Grover.diffusionFew_ancRestore_8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diffusionFew_ancRestore_8

/-- info: 'CQRV.Grover.mczFew8_WF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mczFew8_WF

/-- info: 'CQRV.Grover.diffusionFew8_WF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms diffusionFew8_WF


/-! ## Stage 12d — per-instance certification (report §5.1.3, §8.2)

`fewCheck` (the classical KG step of one `n`) evaluated by the compiler for n = 1..12 (the
front-end limit) at the register `a₀ = 2` the certificates use; the kernel evaluates it for the
certificate's own `n` (`decide +kernel`, below for n = 8). A register without `anc[1]` fails the
qubit check for n ≥ 6 (candidate B uses two ancillae there). -/

#guard (List.range 12).all fun k => fewCheck (k + 1) 2 (FewSchedule.planK (k + 1) .logDepth)
#guard (List.range 12).all fun k => plan (k + 1) .logDepth == FewSchedule.planK (k + 1) .logDepth
#guard (List.range 12).all fun k =>
  (mczFew (k + 1) .logDepth).toOption == (mczFewK (k + 1) .logDepth).toOption
#guard !fewCheck 8 1 (FewSchedule.planK 8 .logDepth)
#guard (mczFewK 8 .logDepth).toOption == some mczFew8

example : fewCheck 8 2 (plan 8 .logDepth) = true := by
  rw [FewSchedule.plan_eq_planK]
  decide +kernel

/-! ## Axioms (Stage 12d) -/

/--
info: 'CQRV.Grover.FewSchedule.plan_eq_planK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FewSchedule.plan_eq_planK

/-- info: 'CQRV.Grover.mczFew_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mczFew_eq_K

/--
info: 'CQRV.Grover.fewCheck_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fewCheck_sound

/--
info: 'CQRV.Grover.mczFew_ancRestore_of_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mczFew_ancRestore_of_classical

/--
info: 'CQRV.Grover.diffusionFew_ancRestore_of_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diffusionFew_ancRestore_of_classical

/--
info: 'CQRV.Grover.groverCircuitFew_ok_of' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms groverCircuitFew_ok_of

/--
info: 'CQRV.Grover.grover_ancRestore_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grover_ancRestore_diff

/--
info: 'CQRV.Grover.grover_realizes_of_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grover_realizes_of_ancRestore

/--
info: 'CQRV.Grover.grover_parametric_lemma_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms grover_parametric_lemma_diff

end CQRV.Tests.MczFewCorrect
