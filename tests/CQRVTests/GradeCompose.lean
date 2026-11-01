module

import CQRV.Circuit.GradeCompose
import CQRV.Synthesis.Diffusion
import CQRV.Synthesis.QFT
meta import CQRV.Circuit.GradeCompose
meta import CQRV.Synthesis.Diffusion
meta import CQRV.Synthesis.QFT

/-!
# Grade composition (Stage 19a, PHASE2_SPEC.md §A.3 item 2 and amendment (6);
docs/tasks/STAGE19_TASK.md A5)

* The T-depth counterexample: `C₁ = ⟨2, [h x0, h x0]⟩`, `C₂ = ⟨2, [t x0, t x1]⟩` — `C₂` alone has
  `tDepth = 1`, the append places its two `T` in layers 3 and 1, `tDepth = 2 > 0 + 1`; the bound
  `tDepth C₁ + tCount C₂ = 0 + 2` is attained.
* `liveEnd = 0` for the synthesized oracle and the diffusion of `grover_pred_037` (the network
  of the Grover certificate, `CQRV.Circuit.Restoration.groverNet`, written out here so that this
  file stays Physlib-free), for the Hadamard layer and for `qftCircuit 4`.
* The measured grades of `grover_pred_037`: oracle `(10, 27, 8, 2)`, diffusion `(15, 41, 28, 7)`,
  the iteration `oracle.append diffusion` `(15, 68, 36, 7)` = oracle ⊕ diffusion (the
  `oracle_plus_diffusion` value `cqr synthesize --grover` prints, attained here); `groverCircuit`
  at `r = 2`: measured `(15, 134, 72, 7)` (the certificate's) ≤ `hLayer ⊕ 2 • iteration` =
  `(15, 137, 72, 7)` — the scheduler overlaps the blocks by three layers.
* `example` instances of every theorem of A2–A4 and the axiom lines of the five theorems the
  task names.
-/

namespace CQRV.Tests.GradeCompose

open CQRV CQRV.Synthesis

/-! ## The T-depth counterexample (PHASE2_SPEC §A.3 amendment (6)) -/

def c1 : Circuit := ⟨2, [.h (.data 0), .h (.data 0)]⟩
def c2 : Circuit := ⟨2, [.t (.data 0), .t (.data 1)]⟩

#guard c1.gradeExt.tDepth == 0
#guard c2.gradeExt.tDepth == 1
#guard c2.tCount == 2
-- the sum of the two T-depths, 0 + 1, is exceeded
#guard (c1.append c2).gradeExt.tDepth == 2
-- the two `T` of the `C₂` part land in layers 3 and 1
#guard (schedule (c1.append c2)).toList ==
  [(.h (.data 0), 1), (.h (.data 0), 2), (.t (.data 0), 3), (.t (.data 1), 1)]
-- the bound `tDepth C₁ + tCount C₂` is attained
#guard (c1.append c2).gradeExt.tDepth == c1.gradeExt.tDepth + c2.tCount
#guard ((c1.append c2).depth, c1.depth, c2.depth) == (3, 2, 1)
#guard (c1.append c2).grade == ⟨2, 3, 2, 0⟩
#guard c1.grade + c2.grade == ⟨2, 3, 2, 0⟩
#guard (c1.append c2).grade ≤ c1.grade + c2.grade
#guard c1.liveEnd == 0 && c2.liveEnd == 0

/-! ## `grover_pred_037`: oracle, diffusion, iteration, `groverCircuit` at `r = 2` -/

/-- The network of `grover_pred_037` (`x0 ∧ x3 ∧ x7`), the literal of
`CQRV.Circuit.Restoration.groverNet` (report §8, §6.1.4). -/
def groverNet037 : Network :=
  ⟨8, #[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7,
        .and 0 3, .and 8 7], [9]⟩

def oracle037 : Circuit := (synthesizeOracle groverNet037).toOption.getD default
def diffusion8 : Circuit := (diffusion 8 none).toOption.getD default
def iteration037 : Circuit := oracle037.append diffusion8
def hLayer8 : Circuit := ⟨8, Diffusion.onAll .h 8⟩
def grover037r2 : Circuit := (groverCircuit groverNet037 8 2).toOption.getD default

#guard (synthesizeOracle groverNet037).toBool && (diffusion 8 none).toBool &&
  (groverCircuit groverNet037 8 2).toBool
#guard (groverIteration groverNet037 8).toOption == some iteration037
#guard (groverCircuit groverNet037 8 2).toOption ==
  some ((List.replicate 2 iteration037).foldl Circuit.append hLayer8)

-- `liveEnd = 0`: every block ends with its ancillae freed
#guard oracle037.liveEnd == 0
#guard diffusion8.liveEnd == 0
#guard iteration037.liveEnd == 0
#guard hLayer8.liveEnd == 0
#guard (qftCircuit 4).liveEnd == 0

-- the measured grades and the composed bound (attained for the iteration)
#guard oracle037.grade == ⟨10, 27, 8, 2⟩
#guard diffusion8.grade == ⟨15, 41, 28, 7⟩
#guard iteration037.grade == ⟨15, 68, 36, 7⟩
#guard oracle037.grade + diffusion8.grade == ⟨15, 68, 36, 7⟩
#guard iteration037.grade ≤ oracle037.grade + diffusion8.grade

-- `GradeExt`: the sums and the T-depth bound (17 ≤ 5 + 28)
#guard oracle037.gradeExt == ⟨14, 5, 0, 2, 4⟩
#guard diffusion8.gradeExt == ⟨49, 7, 0, 7, 14⟩
#guard iteration037.gradeExt == ⟨63, 17, 0, 9, 18⟩
#guard iteration037.gradeExt.tDepth ≤ oracle037.gradeExt.tDepth + diffusion8.tCount

-- `groverCircuit` at `r = 2`: the certificate's grade against `hLayer ⊕ 2 • iteration`
#guard grover037r2.grade == ⟨15, 134, 72, 7⟩
#guard hLayer8.grade == ⟨8, 1, 0, 0⟩
#guard hLayer8.grade + 2 • iteration037.grade == ⟨15, 137, 72, 7⟩
#guard grover037r2.grade ≤ hLayer8.grade + 2 • iteration037.grade
#guard grover037r2.gradeExt == ⟨126, 39, 0, 18, 36⟩
#guard grover037r2.gradeExt.tDepth ≤ hLayer8.gradeExt.tDepth + 2 * iteration037.tCount

/-! ## Instances of the theorems -/

-- A1 / A2 on the counterexample circuits (hypotheses decided)
example : (c1.append c2).tCount = c1.tCount + c2.tCount := Circuit.tCount_append c1 c2
example : (c1.append c2).liveEnd = c2.liveEnd := Circuit.liveEnd_append (by decide)
example : (c1.append c2).peakAncilla = max c1.peakAncilla c2.peakAncilla :=
  Circuit.peakAncilla_append (by decide)
example : (c1.append c2).width = max c1.width c2.width := Circuit.width_append rfl (by decide)
example : (c1.append c2).depth ≤ c1.depth + c2.depth := Circuit.depth_append_le c1 c2

-- A3 on the Grover blocks (the hypotheses as stated; `liveEnd = 0` is the `#guard` above)
example (h : oracle037.liveEnd = 0) (hn : oracle037.nData = diffusion8.nData) :
    (oracle037.append diffusion8).grade ≤ oracle037.grade + diffusion8.grade :=
  Circuit.grade_append_le hn h
example (hn : ∀ b ∈ [oracle037, diffusion8], b.nData = hLayer8.nData)
    (hb : ∀ b ∈ [oracle037, diffusion8], b.liveEnd = 0) :
    ([oracle037, diffusion8].foldl Circuit.append hLayer8).grade ≤
      hLayer8.grade + ([oracle037, diffusion8].map Circuit.grade).sum :=
  Circuit.grade_foldl_append_le hLayer8 _ hn rfl hb
example (hn : iteration037.nData = hLayer8.nData) (ht : iteration037.liveEnd = 0) :
    ((List.replicate 2 iteration037).foldl Circuit.append hLayer8).grade ≤
      hLayer8.grade + 2 • iteration037.grade :=
  Circuit.grade_replicate_le hLayer8 iteration037 2 hn rfl ht

-- A4
example : (c1.append c2).gradeExt.tDepth ≤ c1.gradeExt.tDepth + c2.tCount :=
  Circuit.tDepth_append_le c1 c2
example : (oracle037.append diffusion8).gradeExt.twoQ =
    oracle037.gradeExt.twoQ + diffusion8.gradeExt.twoQ :=
  Circuit.gradeExt_twoQ_append _ _
example : (oracle037.append diffusion8).gradeExt.rot =
    oracle037.gradeExt.rot + diffusion8.gradeExt.rot :=
  Circuit.gradeExt_rot_append _ _
example : (oracle037.append diffusion8).gradeExt.meas =
    oracle037.gradeExt.meas + diffusion8.gradeExt.meas :=
  Circuit.gradeExt_meas_append _ _
example : (oracle037.append diffusion8).gradeExt.ff =
    oracle037.gradeExt.ff + diffusion8.gradeExt.ff :=
  Circuit.gradeExt_ff_append _ _
example : ((List.replicate 2 iteration037).foldl Circuit.append hLayer8).gradeExt.tDepth ≤
    hLayer8.gradeExt.tDepth + 2 * iteration037.tCount :=
  Circuit.gradeExt_tDepth_replicate_le hLayer8 iteration037 2

/-! ## Axioms (CLAUDE.md rule 10) -/

/-- info: 'CQRV.Circuit.depth_append_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.depth_append_le

/-- info: 'CQRV.Circuit.grade_append_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.grade_append_le

/-- info: 'CQRV.Circuit.grade_foldl_append_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.grade_foldl_append_le

/-- info: 'CQRV.Circuit.grade_replicate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.grade_replicate_le

/-- info: 'CQRV.Circuit.tDepth_append_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.tDepth_append_le

end CQRV.Tests.GradeCompose
