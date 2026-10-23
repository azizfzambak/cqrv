module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Card

/-!
# CQRV.Realizability.Obstruction

Report §2.2.2 — Theorem 3.1 (revised: `Cl_det`, non-degeneracy), statement only, in the
report's concrete "equivalently" form.

Neither Mathlib nor Physlib has the category U, so the categorical packaging (no monoidal
functor `Cl_det → U` preserving the copy/discard structure (Δ, !)) is deferred
(docs/DECISIONS.md, 2026-10-23). What is stated here is its linear-algebra core: on a
non-degenerate space (`dim F(Bool) ≥ 2`) no linear map copies every vector.
-/

@[expose] public section

namespace CQRV

/-- Report §2.2.2, Theorem 3.1 (concrete form) — for a finite basis type `d` with
`2 ≤ |d|` (non-degeneracy), there is no linear map `C : ℂ^d → ℂ^(d×d)` with `C ψ = ψ ⊗ ψ`
for **all** vectors `ψ` (naturality with respect to all states, not only basis states, which
the classical copy `|x⟩ ↦ |x⟩|x⟩` does satisfy). Tracked `sorry` (docs/SORRIES.md); not to be
attempted until the reviewer decides. -/
theorem no_cloning_obstruction {d : Type} [Fintype d] (hd : 2 ≤ Fintype.card d) :
    ¬ ∃ C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ), ∀ ψ : d → ℂ, C ψ = fun ij => ψ ij.1 * ψ ij.2 := by
  sorry

end CQRV

end
