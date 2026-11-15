module

public import CQRV.Circuit.RestoreRegimes
public import CQRV.Grover.MczFewAll

/-!
# CQRV.Grover.KGRegime

Stage 23b (PHASE2_SPEC §B.2; report §6.1.4, §6.2.3) — **the KG bridge**: the invariant of
`CQRV.Grover.MczFewAll` (Stage 13a, Khattar–Gidney §5.1) read in the terms of the conditionally
clean regime of `CQRV.Circuit.RestoreRegimes`. In the array model, a marked index `t > 0` is
conditionally clean in the sense that its value is fixed (to 1) whenever the unmarked values below
it are all 1 — the regime's `cond x → w = value` shape on computational-basis values, with the
clean value 1 rather than 0 (the targets of `rtof; X t`). It is a statement about basis values
inside the MCZ proof, not the density-operator regime `AncRestoreCond`; the MCZ block as a whole is
cleanly restoring (`mczFew_ancRestore_of_classical`).

Layering: this module sits in `Grover` and imports `Circuit`; no `Circuit` module imports `Grover`.
-/

@[expose] public section

namespace CQRV

/-! ## The KG invariant in the regime's terms -/

namespace Grover.KG

/-- PHASE2_SPEC §B.2 (23b), report §6.1.4 — **the KG bridge**: in the array model of
`MczFewAll.lean` (Stage 13a), a marked index `t > 0` is conditionally clean in the sense of the
regime — its value is fixed by the indices below it: whenever the unmarked values below `t` are
all 1 (`Clear M v t`), `t` reads 1. This is `Inv.cond` read contrapositively; it is a statement
on computational-basis values inside the MCZ proof, with the clean value 1 (the targets of
`rtof; X t`), not the density-operator regime `AncRestoreCond`. -/
theorem Inv.cond_value {L : ℕ} {M v : ℕ → Bool} {F : Bool} (h : Inv L M v F) {t : ℕ} (ht : t < L)
    (h0 : 0 < t) (hM : M t = true) (hc : Clear M v t) : v t = true := by
  by_contra hv
  exact h.cond t ht h0 hM (by simpa using hv) hc

end Grover.KG

end CQRV

end
