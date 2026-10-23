module

public import Mathlib.Order.Monotone.Basic
public import CQRV.Grades.Order

/-!
# CQRV.Grades.Hardware

Report §3.1.3 (hardware profiles as change-of-base) and §3.3.3 (the simplified NISQ profile
ρNISQ, Table 3.5).
-/

@[expose] public section

namespace CQRV

/-- Report §3.1.3 — a hardware profile is a monotone map `ρ : R → R_phys` from logical grades
to a preordered physical cost space `P` (change-of-base of the resource fibration). The target
is a parameter because the report's ρ lands in `R_phys`, not in `R` (docs/DECISIONS.md,
2026-10-23). -/
structure HardwareProfile (P : Type) [Preorder P] where
  /-- The cost map `ρ : R → R_phys` (§3.1.3). -/
  map : Grade → P
  /-- ρ is monotone (§3.1.3). -/
  mono : Monotone map

/-- Report §3.3.3 — the simplified NISQ profile
`ρNISQ (w, d, t, a) = (w, d · t_gate, t · t_T, a)`, with `tgate` the typical two-qubit gate
duration and `tT` the T-gate duration, both in nanoseconds. No value of `tT` is fixed here:
the report gives none. -/
def ρNISQ (tgate tT : Nat) : HardwareProfile Grade where
  map r := ⟨r.w, r.d * tgate, r.t * tT, r.a⟩
  mono r s h := by
    obtain ⟨hw, hd, ht, ha⟩ := h
    exact ⟨hw, Nat.mul_le_mul_right tgate hd, Nat.mul_le_mul_right tT ht, ha⟩

end CQRV

end
