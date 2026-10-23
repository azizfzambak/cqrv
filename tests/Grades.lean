import CQRV.Grades.Hardware

/-!
# Tests for `CQRV.Grades` (report §2.3.3, §3.1.1–3.1.4, §3.3.3)

Every number below is copied from the report; none is adjusted to fit the code.
-/

namespace CQRV.Tests.Grades

open CQRV CQRV.Grade

/-! ## §2.3.3, Table 3 — three-stage measured pipeline under ⊕ -/

/-- Stage 1 grade, report §2.3.3. -/
def r₁ : Grade := ⟨10, 50, 100, 5⟩
/-- Stage 2 grade, report §2.3.3. -/
def r₂ : Grade := ⟨12, 200, 800, 8⟩
/-- Stage 3 grade, report §2.3.3. -/
def r₃ : Grade := ⟨8, 30, 0, 0⟩

example : r₁ + r₂ = ⟨12, 250, 900, 8⟩ := by decide
example : (r₁ + r₂) + r₃ = ⟨12, 280, 900, 8⟩ := by decide

/-! ## §3.1.4, Table 3.3 — Grover at n = 8, M = 32 -/

/-- Oracle U_P per call, Table 3.3. -/
def oracle : Grade := ⟨10, 21, 8, 2⟩
/-- Diffusion D₈ per call, Table 3.3. -/
def diffusion : Grade := ⟨10, 16, 28, 2⟩
/-- One Grover iteration, Table 3.3. -/
def iteration : Grade := ⟨10, 37, 36, 2⟩

example : oracle + diffusion = iteration := by decide
-- r⋆ = 2 iterations: the total Grover grade of Table 3.3.
example : (2 : Nat) • iteration = ⟨10, 74, 72, 2⟩ := by decide
#guard (2 : Nat) • iteration == ⟨10, 74, 72, 2⟩

/-! ## ⊗ sanity check (Table 3.1, parallel row)

This is the wrong law for Grover: oracle and diffusion share the data register and the two
ancillae, so they compose sequentially (⊕). ⊗ would double-count width and ancilla — which is
exactly why both laws exist. -/
example : parComp oracle diffusion = ⟨20, 21, 36, 4⟩ := by decide

/-! ## §3.3.3, Table 3.5 — budget check against IBM Kyiv

The t-budget is set to the requirement (72) because on NISQ hardware T is a native RZ(π/4)
gate (Table 3.5: "native"); no Kyiv T-budget number is invented. Depth budget ~200 layers. -/
#guard fits ⟨10, 74, 72, 2⟩ ⟨127, 200, 72, 127⟩ = true
-- Depth 74 over a depth budget of 73.
#guard fits ⟨10, 74, 72, 2⟩ ⟨127, 73, 72, 127⟩ = false

example : (⟨10, 74, 72, 2⟩ : Grade) ≤ ⟨127, 200, 72, 127⟩ :=
  fits_iff.mp (by decide)

/-! ## §3.3.3 — ρNISQ with t_gate = 500 ns

Depth 74 × 500 ns = 37 000 ns ≤ 100 000 ns (T1 ≈ 100 μs), for any T-gate duration `tT`. -/
example (tT : Nat) : ((ρNISQ 500 tT).map ⟨10, 74, 72, 2⟩).d = 37000 := rfl
example (tT : Nat) : ((ρNISQ 500 tT).map ⟨10, 74, 72, 2⟩).d ≤ 100000 :=
  show 74 * 500 ≤ 100000 by decide
#guard ((ρNISQ 500 0).map ⟨10, 74, 72, 2⟩).d ≤ 100000

/-! ## Axiom audit (CLAUDE.md rule 10) -/

#print axioms fits_iff
#print axioms seqComp_mono
-- The monoid laws (add_assoc, zero_add, add_zero, add_comm) are fields of this instance.
#print axioms CQRV.Grade.instAddCommMonoid

end CQRV.Tests.Grades
