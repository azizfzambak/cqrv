module

public import Mathlib.Order.Basic
public import CQRV.Grades.Basic

/-!
# CQRV.Grades.Order

Report §3.1.2 (Table 3.2) — the component-wise order on grades, the decidable budget test
`fits`, monotonicity of ⊕ and ⊗, and fibres over a budget with budget-relaxation reindexing.

The resource fibration is `p : QR → (R, ≤)ᵒᵖ`: its base category is the grade poset with the
opposite order, and the fibre over a budget `b` contains the channels with grade `r ≤ b`.
Fibre membership is decidable (`fits`). Only the order-theoretic content is formalized here;
the category-theoretic fibration is out of scope.
-/

@[expose] public section

namespace CQRV

namespace Grade

/-- Report §3.1.2 — the component-wise order on `ℕ⁴` (not lexicographic). The base category
of the resource fibration is `(Grade, ≤)ᵒᵖ`. -/
instance : PartialOrder Grade where
  le r s := r.w ≤ s.w ∧ r.d ≤ s.d ∧ r.t ≤ s.t ∧ r.a ≤ s.a
  le_refl r := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨by omega, by omega, by omega, by omega⟩
  le_antisymm r s h₁ h₂ := by
    obtain ⟨_, _, _, _⟩ := h₁
    obtain ⟨_, _, _, _⟩ := h₂
    ext <;> omega

/-- Report §3.1.2 — unfolding of the component-wise order. -/
theorem le_def {r s : Grade} : r ≤ s ↔ r.w ≤ s.w ∧ r.d ≤ s.d ∧ r.t ≤ s.t ∧ r.a ≤ s.a :=
  Iff.rfl

/-- Report §3.1.2 — budget feasibility `r ≤ b` is a decidable inequality on `ℕ⁴`. -/
instance : DecidableRel (· ≤ · : Grade → Grade → Prop) := fun r s =>
  inferInstanceAs (Decidable (r.w ≤ s.w ∧ r.d ≤ s.d ∧ r.t ≤ s.t ∧ r.a ≤ s.a))

/-- Report §3.1.2, §3.3.2 — the fibre-membership test: does grade `r` fit budget `b`? -/
def fits (r b : Grade) : Bool := decide (r ≤ b)

/-- Report §3.1.2 — `fits` decides the component-wise order. -/
theorem fits_iff {r b : Grade} : fits r b = true ↔ r ≤ b := by
  simp [fits]

/-- Report §3.1.1–3.1.2 — ⊕ is monotone in both arguments. -/
theorem seqComp_mono {r r' s s' : Grade} (hr : r ≤ r') (hs : s ≤ s') : r + s ≤ r' + s' := by
  obtain ⟨_, _, _, _⟩ := hr
  obtain ⟨_, _, _, _⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [seqComp_w, seqComp_d, seqComp_t, seqComp_a] <;> omega

/-- Report §3.1.1–3.1.2 — ⊗ is monotone in both arguments. -/
theorem parComp_mono {r r' s s' : Grade} (hr : r ≤ r') (hs : s ≤ s') :
    parComp r s ≤ parComp r' s' := by
  obtain ⟨_, _, _, _⟩ := hr
  obtain ⟨_, _, _, _⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [parComp_w, parComp_d, parComp_t, parComp_a] <;> omega

end Grade

/-- Report §3.1.2, Table 3.2, row "Fibre over b" — the grades affordable within budget `b`
(the grade-level shadow of `{Φ | grade Φ ≤ b}`). Membership is decidable (`Grade.fits`). -/
def Fibre (b : Grade) := {r : Grade // r ≤ b}

/-- Report §3.1.2, Table 3.2, row "Reindexing" — budget relaxation `b ≤ b'` is the fibre
inclusion `Fibre b ↪ Fibre b'` (reindexing along the base arrow `b' → b` of `(R, ≤)ᵒᵖ`). -/
def Fibre.relax {b b' : Grade} (h : b ≤ b') : Fibre b → Fibre b' :=
  fun r => ⟨r.1, le_trans r.2 h⟩

end CQRV

end
