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

/-! ## Stage 13a — KG Theorem 5.1 for every n (`CQRV.Grover.MczFewAll`)

The index-model pieces on small values, then the all-n theorems used at sizes no per-instance
check reaches (`fewCheck` enumerates `2ⁿ` inputs). -/

-- One sub-step of timestep `i` is `subOps (i + 2^i) (2^{i−1})` (`substeps_succ_interval`).
#guard KG.subOps 4 2 == [(3, 5, 6), (2, 7, 8)]
#guard timestep 1 == KG.subOps 3 1 ++ [(1, 2, 3)]
#guard timestep 2 == KG.subOps 6 2 ++ KG.subOps 4 1 ++ [(2, 3, 4)]
-- The greedy shapes `F(j, r) = 0 (10)^j 1 1 0^r`, `B(j, r) = 0 (10)^j 0 1^r` (L4).
#guard KG.arr 7 (KG.fF 2) == [false, true, false, true, false, true, true]
#guard KG.arr 7 (KG.fB 1) == [false, true, false, false, true, true, true]
#guard (greedy 9 (true :: List.replicate 8 false)).2 == KG.arr 9 (KG.fB 0)
#guard (List.range 40).all fun k =>
  ((List.range (k + 4)).filter fun i => !(greedy (k + 4) (true :: List.replicate (k + 3) false)).2.getD i true).length == 2

example : ∃ C, mczFew 12 .logDepth = .ok C := mczFew_logDepth_ok (by decide)

example {C : Circuit} (h : mczFew 1000 .logDepth = .ok C) : AncRestore 1000 2 C (phaseOracle allOnes) :=
  mczFew_logDepth_ancRestore h

example {D : Circuit} (h : diffusionFew 64 .logDepth = .ok D) : AncRestore 64 D.nAnc D (diffU 64) :=
  diffusionFew_logDepth_ancRestore h D.nAnc le_rfl

/-! ## Axioms (Stage 13a) -/

/-- info: 'CQRV.Grover.KG.inv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KG.inv_step

/-- info: 'CQRV.Grover.KG.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KG.sim

/--
info: 'CQRV.Grover.KG.substeps_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KG.substeps_spec

/--
info: 'CQRV.Grover.KG.doubling_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KG.doubling_spec

/-- info: 'CQRV.Grover.KG.greedy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KG.greedy_spec

/--
info: 'CQRV.Grover.KG.logDepth_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KG.logDepth_classical

/--
info: 'CQRV.Grover.KG.mczFew_logDepth_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KG.mczFew_logDepth_WF

/--
info: 'CQRV.Grover.KG.greedy_init_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KG.greedy_init_two

/--
info: 'CQRV.Grover.mczFew_logDepth_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mczFew_logDepth_ancRestore

/--
info: 'CQRV.Grover.mczFew_logDepth_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mczFew_logDepth_ok

/--
info: 'CQRV.Grover.diffusionFew_logDepth_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diffusionFew_logDepth_ancRestore

end CQRV.Tests.MczFewCorrect
