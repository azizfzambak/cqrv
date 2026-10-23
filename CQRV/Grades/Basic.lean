module

public import Mathlib.Algebra.Group.Defs

/-!
# CQRV.Grades.Basic

Report §3.1.1 (Table 3.1) — the resource grade (w, d, t, a), sequential composition ⊕
(`seqComp`, the `AddCommMonoid` structure) and the parallel product ⊗ (`parComp`).

`+` on `Grade` is ⊕ and `n • r` is the n-fold ⊕ (docs/DECISIONS.md, 2026-10-23).
-/

@[expose] public section

namespace CQRV

/-- Report §3.1.1 — a resource grade `R = (w, d, t, a) ∈ ℕ⁴`:
`w` = width (number of logical qubits), `d` = depth (time steps / layers on the critical path),
`t` = T-count, `a` = peak number of ancillae allocated simultaneously. -/
@[ext]
structure Grade where
  /-- Width: number of logical qubits (§3.1.1). -/
  w : Nat
  /-- Depth: critical-path layers (§3.1.1). -/
  d : Nat
  /-- T-count (§3.1.1). -/
  t : Nat
  /-- Peak simultaneous ancillae (§3.1.1). -/
  a : Nat
  deriving DecidableEq, Repr

namespace Grade

/-- Report §3.1.1, Table 3.1, row "Sequential (⊕)":
`r₁ ⊕ r₂ = (max w₁ w₂, d₁ + d₂, t₁ + t₂, max a₁ a₂)`. Depth and T-count add; width and
ancilla are peaks. Valid because every stage restores its ancillae to |0⋯0⟩ (§6.2), so the
registers are reused by the next stage rather than allocated afresh. -/
def seqComp (r₁ r₂ : Grade) : Grade :=
  ⟨max r₁.w r₂.w, r₁.d + r₂.d, r₁.t + r₂.t, max r₁.a r₂.a⟩

/-- Report §3.1.1, Table 3.1, row "Parallel (⊗)":
`r₁ ⊗ r₂ = (w₁ + w₂, max d₁ d₂, t₁ + t₂, a₁ + a₂)`. Only for circuits on **disjoint**
registers; for circuits sharing registers (e.g. a Grover oracle and diffusion) use `seqComp`.
Deliberately not an instance: `+` on `Grade` is ⊕ only. -/
def parComp (r₁ r₂ : Grade) : Grade :=
  ⟨r₁.w + r₂.w, max r₁.d r₂.d, r₁.t + r₂.t, r₁.a + r₂.a⟩

/-- Report §3.1.1, Table 3.1, row "Identity": the empty circuit `(0, 0, 0, 0)`. -/
instance : Zero Grade := ⟨⟨0, 0, 0, 0⟩⟩

/-- Report §3.1.1 — `+` on `Grade` is sequential composition ⊕ (`seqComp`). -/
instance : Add Grade := ⟨seqComp⟩

/-- Report §3.1.1 — components of the identity grade. -/
@[simp] theorem zero_w : (0 : Grade).w = 0 := rfl
/-- Report §3.1.1 — components of the identity grade. -/
@[simp] theorem zero_d : (0 : Grade).d = 0 := rfl
/-- Report §3.1.1 — components of the identity grade. -/
@[simp] theorem zero_t : (0 : Grade).t = 0 := rfl
/-- Report §3.1.1 — components of the identity grade. -/
@[simp] theorem zero_a : (0 : Grade).a = 0 := rfl

/-- Report §3.1.1, Table 3.1 — width of `r₁ ⊕ r₂`. -/
@[simp] theorem seqComp_w (r₁ r₂ : Grade) : (r₁ + r₂).w = max r₁.w r₂.w := rfl
/-- Report §3.1.1, Table 3.1 — depth of `r₁ ⊕ r₂`. -/
@[simp] theorem seqComp_d (r₁ r₂ : Grade) : (r₁ + r₂).d = r₁.d + r₂.d := rfl
/-- Report §3.1.1, Table 3.1 — T-count of `r₁ ⊕ r₂`. -/
@[simp] theorem seqComp_t (r₁ r₂ : Grade) : (r₁ + r₂).t = r₁.t + r₂.t := rfl
/-- Report §3.1.1, Table 3.1 — ancilla of `r₁ ⊕ r₂`. -/
@[simp] theorem seqComp_a (r₁ r₂ : Grade) : (r₁ + r₂).a = max r₁.a r₂.a := rfl

/-- Report §3.1.1, Table 3.1 — components of `r₁ ⊗ r₂`. -/
@[simp] theorem parComp_w (r₁ r₂ : Grade) : (parComp r₁ r₂).w = r₁.w + r₂.w := rfl
/-- Report §3.1.1, Table 3.1 — components of `r₁ ⊗ r₂`. -/
@[simp] theorem parComp_d (r₁ r₂ : Grade) : (parComp r₁ r₂).d = max r₁.d r₂.d := rfl
/-- Report §3.1.1, Table 3.1 — components of `r₁ ⊗ r₂`. -/
@[simp] theorem parComp_t (r₁ r₂ : Grade) : (parComp r₁ r₂).t = r₁.t + r₂.t := rfl
/-- Report §3.1.1, Table 3.1 — components of `r₁ ⊗ r₂`. -/
@[simp] theorem parComp_a (r₁ r₂ : Grade) : (parComp r₁ r₂).a = r₁.a + r₂.a := rfl

/-- Report §3.1.1 — `(ℕ⁴, ⊕, 0)` is a commutative monoid. `n • r` is the n-fold ⊕
(`nsmul := nsmulRec`, i.e. repeated addition; `nsmul_zero`/`nsmul_succ` hold by the structure's
default `rfl` proofs), used for `for` loops (§7.3.2) and the r⋆-fold Grover iteration (§3.1.4). -/
instance : AddCommMonoid Grade where
  nsmul := nsmulRec
  add_assoc r₁ r₂ r₃ := by ext <;> simp <;> omega
  zero_add r := by ext <;> simp
  add_zero r := by ext <;> simp
  add_comm r₁ r₂ := by ext <;> simp <;> omega

/-- Report §3.1.1, Table 3.1 — ⊗ is commutative. -/
theorem parComp_comm (r₁ r₂ : Grade) : parComp r₁ r₂ = parComp r₂ r₁ := by
  ext <;> simp <;> omega

/-- Report §3.1.1, Table 3.1 — ⊗ is associative. -/
theorem parComp_assoc (r₁ r₂ r₃ : Grade) :
    parComp (parComp r₁ r₂) r₃ = parComp r₁ (parComp r₂ r₃) := by
  ext <;> simp <;> omega

/-- Report §3.1.1, Table 3.1 — `(0, 0, 0, 0)` is the identity of ⊗. -/
theorem parComp_zero (r : Grade) : parComp r 0 = r := by
  ext <;> simp

end Grade

end CQRV

end
