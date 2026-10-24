module

import CQRV.Grover.Basic
meta import CQRV.Grover.Basic

/-!
# Tests for `CQRV.Grover` (report §8.2–8.4, Figure 8.1; Stage 7a)

* The computed grade of the synthesized Grover circuit of `grover_pred_037` (`r = 2`, V1) is
  `(15, 230, 72, 7)` (Stage 7a decision 1: the certificate's grade is this computed value).
* `#print axioms` for every proved theorem of Stage 7a: only `propext`, `Classical.choice`,
  `Quot.sound`. The open statements and everything built on them show `sorryAx` (SORRIES.md).
-/

namespace CQRV.Tests.Grover

open CQRV CQRV.Grover CQRV.Synthesis

/-! ## Computed grade and circuit facts -/

#guard Synthesis.grade grover037Circuit == ⟨15, 230, 72, 7⟩
#guard (groverCircuit groverNet 8 2).toOption == some grover037Circuit
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

/-! ## Open statements (Stage 7b/7c): these show `sorryAx` -/

#print axioms reflection_geometry
#print axioms iteration_induction
#print axioms terminal_measurement
#print axioms grover_realizes
-- `sorryAx` only through `grover_realizes`, the realization conjunct:
#print axioms grover_parametric_lemma
#print axioms grover_pred_037_certified_statement

end CQRV.Tests.Grover
