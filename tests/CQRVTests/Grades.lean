import CQRV.Grades.Hardware
import CQRV.Grades.Profile

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

-- Report v3, erratum 10: the measured MVP grade (15, 230, 72, 7) does NOT fit Kyiv —
-- depth 230 exceeds the ~200-layer budget. The Table 3.3 checks above stay as the report's
-- arithmetic; this records the measured value against the same budget.
#guard fits ⟨15, 230, 72, 7⟩ ⟨127, 200, 72, 127⟩ = false

/-! ## §3.3.3 — ρNISQ with t_gate = 500 ns

Depth 74 × 500 ns = 37 000 ns ≤ 100 000 ns (T1 ≈ 100 μs), for any T-gate duration `tT`. -/
example (tT : Nat) : ((ρNISQ 500 tT).map ⟨10, 74, 72, 2⟩).d = 37000 := rfl
example (tT : Nat) : ((ρNISQ 500 tT).map ⟨10, 74, 72, 2⟩).d ≤ 100000 :=
  show 74 * 500 ≤ 100000 by decide
#guard ((ρNISQ 500 0).map ⟨10, 74, 72, 2⟩).d ≤ 100000

/-! ## §3.3.2–3.3.3 — declared profiles, `fitsPartial`, `δ_hw` (Stage 11b)

`kyiv` has the figures of `profiles/ibm_kyiv.json` (report Table 3.5, §3.3.3): budget
(127, 200, —, 127), t_gate = 500 ns, no t_T, T1 = 100 μs, p̄ = 1/100. -/

/-- The IBM Kyiv profile of report Table 3.5 / §3.3.3 (T-count not limiting). -/
def kyiv : Profile :=
  { name := "ibm_kyiv", budget := ⟨some 127, some 200, none, some 127⟩, tGateNs := some 500,
    tTNs := none, t1Ns := some 100000, pBar := some (1 / 100) }

/-- The measured grades of the two worked examples (examples/certs/). -/
def groverGrade : Grade := ⟨15, 230, 72, 7⟩
/-- simple_alu_x0_1, measured. -/
def aluGrade : Grade := ⟨16, 145, 60, 10⟩

-- grover_pred_037 exceeds the depth budget only (Table 3.5, v3 erratum 10)
#guard groverGrade.fitsPartial kyiv.budget = false
#guard (groverGrade.checkComponents kyiv.budget).map (·.fits) == [true, false, true, true]
#guard (groverGrade.checkComponents kyiv.budget).filter (!·.fits) ==
  [⟨"d", "depth", 230, some 200⟩]
-- simple_alu_x0_1 fits every component
#guard aluGrade.fitsPartial kyiv.budget = true
#guard (aluGrade.checkComponents kyiv.budget).all (·.fits)
-- a `none` component is never compared, however large the requirement
#guard (⟨1, 1, 10 ^ 9, 1⟩ : Grade).fitsPartial kyiv.budget = true
#guard (⟨1, 201, 0, 1⟩ : Grade).fitsPartial kyiv.budget = false

-- agreement with `Grade.fits` when every component is given: the theorem (Stage 11b review) …
example (r b : Grade) : r.fitsPartial (.ofGrade b) = fits r b := fitsPartial_ofGrade r b

/-- info: 'CQRV.Grade.fitsPartial_ofGrade' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fitsPartial_ofGrade

-- … and its instances (each component on both sides of its bound)
#guard [groverGrade, aluGrade, ⟨10, 74, 72, 2⟩, 0, ⟨127, 200, 72, 127⟩, ⟨128, 200, 72, 127⟩,
    ⟨127, 201, 72, 127⟩, ⟨127, 200, 73, 127⟩, ⟨127, 200, 72, 128⟩].all fun r =>
  [⟨127, 200, 72, 127⟩, ⟨127, 73, 72, 127⟩, 0, ⟨15, 230, 72, 7⟩].all fun b =>
    r.fitsPartial (.ofGrade b) == fits r b

-- ρNISQ consistency of the Kyiv figures: d · t_gate ≤ T1 (200 · 500 ns = 100 μs) …
#guard kyiv.coherenceOk == some true
-- … and the measured Grover depth does not: 230 · 500 ns = 115 μs > T1
#guard ((ρNISQ 500 0).map groverGrade).d == 115000
#guard ((ρNISQ 500 0).map aluGrade).d ≤ 100000
#guard ({ kyiv with t1Ns := none } : Profile).coherenceOk == none

-- δ_hw = δ + G·p̄, exact (§3.3.3): Grover G = 390, ALU G = 345 (Stage 8a counts); both vacuous
#guard deltaHw (7 / 128) 390 (1 / 100) == 2531 / 640
#guard (HardwareCheck.of kyiv "" groverGrade (7 / 128) 390).vacuous == some true
#guard deltaHw (833 / 2048) 345 (1 / 100) == 39493 / 10240
#guard (HardwareCheck.of kyiv "" aluGrade (833 / 2048) 345).vacuous == some true
-- informative when G·p̄ ≪ 1, e.g. p̄ = 10⁻⁴ (the fault-tolerant p_phy of §3.3.3)
#guard (HardwareCheck.of { kyiv with pBar := some (1 / 10000) } "" groverGrade (7 / 128)
  390).vacuous == some false
#guard (HardwareCheck.of { kyiv with pBar := none } "" groverGrade (7 / 128) 390).deltaHw == none

-- the second status line (Stage 11b, decision 4)
#guard (HardwareCheck.of kyiv "" groverGrade (7 / 128) 390).statusLine ==
  "hardware profile ibm_kyiv: exceeds depth budget (230 > 200); δ_hw ≤ 7/128 + 390·1/100 = \
    2531/640 (vacuous)"
#guard (HardwareCheck.of kyiv "" aluGrade (833 / 2048) 345).statusLine ==
  "hardware profile ibm_kyiv: fits all budgets; δ_hw ≤ 833/2048 + 345·1/100 = 39493/10240 \
    (vacuous)"

-- exact decimals
#guard parseDecimal "0.01" == some (1 / 100)
#guard parseDecimal "1" == some 1
#guard parseDecimal "0.0001" == some (1 / 10000)
#guard parseDecimal "2.50" == some (5 / 2)
#guard [".5", "1.", "", "1e-2", "-0.1", "0.1.2", "1_0", "0x1"].all (parseDecimal · == none)

/-! ## Axiom audit (CLAUDE.md rule 10) -/

#print axioms fits_iff
#print axioms seqComp_mono
-- The monoid laws (add_assoc, zero_add, add_zero, add_comm) are fields of this instance.
#print axioms CQRV.Grade.instAddCommMonoid

end CQRV.Tests.Grades
