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

end CQRV.Tests.MczFewCorrect
