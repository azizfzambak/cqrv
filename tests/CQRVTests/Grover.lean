module

import CQRV.Grover.Basic
meta import CQRV.Grover.Basic

/-!
# Tests for `CQRV.Grover` (report §8.2–8.4, Figure 8.1; Stages 7a, 7b)

* The computed grade of the synthesized Grover circuit of `grover_pred_037` (`r = 2`, V1) is
  `(15, 230, 72, 7)` (Stage 7a decision 1: the certificate's grade is this computed value).
* `#print axioms` for every proved theorem of Stage 7a: only `propext`, `Classical.choice`,
  `Quot.sound`.
* Stage 7b: the Figure 8.1 statements, the parametric lemma and the `grover_pred_037` instance
  are sorry-free; their axioms are pinned with `#guard_msgs`.
-/

namespace CQRV.Tests.Grover

open CQRV CQRV.Grover CQRV.Synthesis

/-! ## Computed grade and circuit facts -/

#guard Synthesis.grade grover037Circuit == ⟨15, 134, 72, 7⟩
#guard (groverCircuit groverNet 8 2).toOption == some grover037Circuit
-- Stage 12a: the chain construction keeps its report-v3 grade.
#guard Synthesis.grade grover037Circuit_chain == ⟨15, 230, 72, 7⟩
#guard (groverCircuit groverNet 8 2 none .chain).toOption == some grover037Circuit_chain
#guard (synthesizeOracle (treeNet 8)).toOption == some mcz8TreeCircuit
#guard grover037Circuit.nAnc == 7 && grover037Circuit.nData == 8
#guard (synthesizeOracle (allNet 8)).toOption == some mcz8Circuit
#guard mcz8Circuit.nAnc == 7
-- The MCZ predicate `P_all` on 8 bits (cf. `allNet_pred`).
#guard (List.range 256).all fun k =>
  (allNet 8).pred 8 (fun i => (k >>> i.val) % 2 == 1) == (k == 255)

-- `allNet` builds its inputs from `List.range` (DECISIONS.md, Stage 7a interpretation 3): the
-- node array is the former `(Array.range n).map Node.input` for every `n`.
example (n : ℕ) : ((List.range n).map Node.input).toArray = (Array.range n).map Node.input := by
  apply Array.ext'
  simp

/-! ## Axioms of the proved theorems (standard three only) -/

-- Item 3 (linear algebra on `Matrix (Reg n) (Reg n) ℂ`).
#print axioms hadamardMat_mul_self
#print axioms hadamardMat_apply
#print axioms oracle_reflection
#print axioms diffusion_reflection
#print axioms diffusion_circuit_matrix
#print axioms uConj_neg
-- Item 4 (restoration; `lemma_6_3_2_of_le` is the 6b-3 proof at a larger register).
#print axioms lemma_6_3_2_of_le
#print axioms lemma_6_3_2
#print axioms allNet_pred
#print axioms unitaryDenote_hLayer
#print axioms unitaryDenote_xLayer
#print axioms ancRestore_of_dataLayer
#print axioms diffusion_ancRestore
#print axioms iteration_ancRestore
#print axioms grover_ancRestore
-- Item 5 and the instance's computed facts.
#print axioms sin_sq_five_mul
#print axioms searchSpec_dom_iff
#print axioms basisPOVM
#print axioms grover037Circuit_ok
#print axioms grover037_grade
#print axioms grover037_sin_sq

/-! ## Figure 8.1, proved in Stage 7b: pinned to the standard three axioms

`#guard_msgs` fails the test build if any of these acquires `sorryAx` or another axiom
(§9.5.1). The plane facts and the measurement lemmas are printed below. -/

/-- info: 'CQRV.Grover.reflection_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflection_geometry

/-- info: 'CQRV.Grover.iteration_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iteration_induction

/-- info: 'CQRV.Grover.terminal_measurement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms terminal_measurement

/-- info: 'CQRV.Grover.grover_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_realizes

/-- info: 'CQRV.Grover.grover_parametric_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_parametric_lemma

/-- info: 'CQRV.Grover.grover_pred_037_certified_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_pred_037_certified_statement

-- Item 1 (plane facts, §8.3.2) and item 4 (pure state, basis POVM, §8.2.3).
#print axioms GroverParams.ketS_eq
#print axioms GroverParams.psiGood_dot_self
#print axioms GroverParams.psiBad_dot_self
#print axioms GroverParams.psiGood_dot_psiBad
#print axioms GroverParams.sin_θ_eq
#print axioms GroverParams.cos_θ_eq
#print axioms GroverParams.θ_mem
#print axioms GroverParams.ketS_dot_psiGood
#print axioms GroverParams.ketS_dot_psiBad
#print axioms GroverParams.phaseOracle_psiGood
#print axioms GroverParams.phaseOracle_psiBad
#print axioms diffU_mulVec
#print axioms uConj_ancZero_m
#print axioms basisPOVM_measure

/-! ## Stage 11a — `synthesizeOracle_WF`, `allNet_WF`, constructors without `decide` -/

/-- info: 'CQRV.synthesizeOracle_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms synthesizeOracle_WF

/-- info: 'CQRV.Grover.allNet_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allNet_WF

/-- info: 'CQRV.Grover.grover_parametric_lemma'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_parametric_lemma'

#print axioms diffusion_WF
#print axioms OracleCert.ofNetwork
#print axioms DiffusionCert.mk'

-- `allNet n` is well formed exactly for `n ≥ 1` (the hypothesis of `allNet_WF`).
#guard !(allNet 0).wf
#guard (List.range 12).all fun n => (allNet (n + 1)).wf
example : ¬ (allNet 0).WF := by decide

-- The constructors give the same circuits as the per-instance certificates (`decide` there).
example : (OracleCert.ofNetwork groverNet (by decide) (by rfl)).C = grover037Oracle.C := rfl
example : (DiffusionCert.mk' 8 mcz8Circuit_ok).mcz.C = mczCert8.mcz.C := rfl

/-! ## Stage 12a — the balanced AND tree `treeNet n` -/

/-- info: 'CQRV.Grover.treeNet_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeNet_pred

/-- info: 'CQRV.Grover.treeNet_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeNet_WF

-- Option (A) with preservation: the chain statements under `_chain`, the tree under the original
-- names, the shape-general lemmas they are instances of.
/-- info: 'CQRV.Grover.diffusion_ok_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms diffusion_ok_chain

/-- info: 'CQRV.Grover.grover037_grade_chain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms grover037_grade_chain

/-- info: 'CQRV.Grover.grover_pred_037_certified_statement_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_pred_037_certified_statement_chain

/-- info: 'CQRV.Grover.grover_parametric_lemma_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_parametric_lemma_shape

/-- info: 'CQRV.Grover.grover_ancRestore_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grover_ancRestore_shape

#print axioms diffusion_ok
#print axioms DiffusionCert.ofShape
#print axioms diffusion_WF_shape

-- The generalized `DiffusionCert` (decision 2): the Stage 7a chain certificate is unchanged
-- (`net` defaults to `allNet 8`), the tree certificate sets `net := treeNet 8`.
example : mczCert8.net = allNet 8 := rfl
example : mczTreeCert8.net = treeNet 8 := rfl
-- Both certificates are accepted by the (unchanged) parametric lemma.
example (hM : (Finset.univ.filter (fun x => grover037Oracle.P x = true)).card = 32) :=
  grover_parametric_lemma (grover037Params hM) mczCert8 2 grover037Circuit_ok
example (hM : (Finset.univ.filter (fun x => grover037Oracle.P x = true)).card = 32) :=
  grover_parametric_lemma (grover037Params hM) mczTreeCert8 2 grover037Circuit_ok

-- The instance through the variant without `DiffusionCert`.
example (hM : (Finset.univ.filter (fun x => grover037Oracle.P x = true)).card = 32) :=
  grover_parametric_lemma' (grover037Params hM) 2 grover037Circuit_ok

end CQRV.Tests.Grover
