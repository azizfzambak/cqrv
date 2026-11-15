module

import CQRV.Grover.KGRegime
meta import CQRV.Grover.KGRegime

/-!
# Tests for `CQRV.Grover.KGRegime` (Stage 23b; PHASE2_SPEC §B.2)

The axiom line of the KG bridge `Grover.KG.Inv.cond_value`, and the bridge applied to the initial
invariant of one array (`inv_init`): index 0 is the only marked index, so nothing above it is
constrained, and the hypothesis `M t = true` with `0 < t` is contradictory.
-/

namespace CQRV.Tests.KGRegime

open CQRV CQRV.Grover CQRV.Grover.KG

/-- info: 'CQRV.Grover.KG.Inv.cond_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inv.cond_value

/-- The bridge in use: from an invariant, a marked `t > 0` with the lower product 1 reads 1. -/
example {L : ℕ} {M v : ℕ → Bool} {F : Bool} (h : KG.Inv L M v F) {t : ℕ} (ht : t < L) (h0 : 0 < t)
    (hM : M t = true) (hc : ∀ i < t, M i = true ∨ v i = true) : v t = true :=
  h.cond_value ht h0 hM hc

end CQRV.Tests.KGRegime
