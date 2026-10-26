module

public import CQRV.Grades.Order
public import CQRV.Grades.Hardware

/-!
# CQRV.Grades.Profile

Report §3.1.3 (hardware profile as change of base), §3.3.2–3.3.3 (budget feasibility as fibre
membership, ρNISQ, Table 3.5 against IBM Kyiv, the hardware-perturbation corollary
`δ_hw ≤ δ + G·p̄`) — the declared hardware profile of `cqr certify --profile` (Stage 11b;
DECISIONS.md 2026-10-26).

* `PartialBudget`: a budget `(w, d, t, a)` whose components may be absent (`none` = "not
  limiting", e.g. Table 3.5's "native" T-count). `Grade.fitsPartial` compares only the given
  components; with all four given it is `Grade.fits` (`PartialBudget.ofGrade`, tested).
* `Profile`: the data of a profile file `profiles/<name>.json` (`docs/profile.schema.json`).
  Reading the JSON is in `CQRV.Certify.Profile`.
* `HardwareCheck`: the per-component check and the exact perturbation bound
  `δ_hw = δ + G·p̄`, vacuous when `δ_hw ≥ 1` (§3.3.3: "the bound is vacuous (Gp ≳ 1)").

This is a check against **declared** figures, not a proof about hardware: routing, native-gate
translation and calibration noise are backend matters outside the trust boundary (§5.3.1).
-/

@[expose] public section

namespace CQRV

/-- Report §3.3.2, Table 3.5 — a hardware budget `(w, d, t, a)` with optional components;
`none` means the component is not limiting (Table 3.5: T gates are native on NISQ). -/
structure PartialBudget where
  w : Option Nat
  d : Option Nat
  t : Option Nat
  a : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- A full budget as a partial budget (every component given). -/
def PartialBudget.ofGrade (b : Grade) : PartialBudget := ⟨some b.w, some b.d, some b.t, some b.a⟩

/-- Report §3.3.2 — `required ≤ budget`, or no budget. -/
def fitsComponent (required : Nat) (budget : Option Nat) : Bool := budget.all (required ≤ ·)

/-- Report §3.1.2, §3.3.2 — fibre membership against a partial budget: every given component
bounds the grade's component; absent components are not compared. -/
def Grade.fitsPartial (r : Grade) (b : PartialBudget) : Bool :=
  fitsComponent r.w b.w && fitsComponent r.d b.d && fitsComponent r.t b.t &&
    fitsComponent r.a b.a

/-- Report §3.3.2, Table 3.5 — one row of the budget check: the grade field and its name, the grade's
value, the budget (`none` = not limiting). -/
structure ComponentCheck where
  /-- the grade field: `w`, `d`, `t` or `a` -/
  key : String
  name : String
  required : Nat
  budget : Option Nat
  deriving Repr, DecidableEq

/-- Does the component fit its budget? -/
def ComponentCheck.fits (c : ComponentCheck) : Bool := fitsComponent c.required c.budget

/-- Report §3.3.3, Table 3.5 — the rows width, depth, T-count, ancilla. -/
def Grade.checkComponents (r : Grade) (b : PartialBudget) : List ComponentCheck :=
  [⟨"w", "width", r.w, b.w⟩, ⟨"d", "depth", r.d, b.d⟩, ⟨"t", "T-count", r.t, b.t⟩,
    ⟨"a", "ancilla", r.a, b.a⟩]

/-- Report §3.3.3 — a declared hardware profile (`docs/profile.schema.json` v1.0.0). Durations
in nanoseconds; `pBar` is the mean per-operation error p̄, exact. `none` = the source gives no
figure (never invented). -/
structure Profile where
  name : String
  budget : PartialBudget
  /-- typical two-qubit gate duration `t_gate` of ρNISQ -/
  tGateNs : Option Nat
  /-- T-gate duration `t_T` of ρNISQ -/
  tTNs : Option Nat
  /-- coherence time `T1` from which the depth budget is derived (`d ≈ T1 / t_gate`) -/
  t1Ns : Option Nat
  /-- mean per-operation error p̄ of `δ_hw ≤ δ + G·p̄` -/
  pBar : Option Rat
  deriving Repr, Inhabited

/-- Report §3.3.3 — ρNISQ consistency of a profile: the depth budget, run at `t_gate` per
layer, stays within `T1` (`d · t_gate ≤ T1`). `none` if a figure is missing. -/
def Profile.coherenceOk (p : Profile) : Option Bool := do
  let d ← p.budget.d
  let tg ← p.tGateNs
  let t1 ← p.t1Ns
  return decide (d * tg ≤ t1)

/-- Report §3.3.3 — the hardware-perturbation bound `δ_hw = δ + G·p̄`, exact. -/
def deltaHw (δ : Rat) (G : Nat) (pBar : Rat) : Rat := δ + G * pBar

/-- Report §3.3.2–3.3.3 — the outcome of checking a certificate's grade, `δ` and `G` against a
profile. -/
structure HardwareCheck where
  profile : String
  /-- SHA3-256 of the profile file (LF line endings) -/
  profileHash : String
  components : List ComponentCheck
  delta : Rat
  G : Nat
  pBar : Option Rat
  deriving Repr

/-- Report §3.3.2–3.3.3 — check grade `r`, failure bound `δ` and noisy-operation count `G`
against profile `p` (file hash `h`). -/
def HardwareCheck.of (p : Profile) (h : String) (r : Grade) (δ : Rat) (G : Nat) :
    HardwareCheck :=
  { profile := p.name, profileHash := h, components := r.checkComponents p.budget, delta := δ,
    G, pBar := p.pBar }

/-- Every component fits. -/
def HardwareCheck.fits (c : HardwareCheck) : Bool := c.components.all (·.fits)

/-- `δ_hw = δ + G·p̄` (`none` if the profile gives no p̄). -/
def HardwareCheck.deltaHw (c : HardwareCheck) : Option Rat :=
  c.pBar.map (CQRV.deltaHw c.delta c.G)

/-- §3.3.3 — the bound says nothing when `δ_hw ≥ 1` (`none` without p̄). -/
def HardwareCheck.vacuous (c : HardwareCheck) : Option Bool := c.deltaHw.map (1 ≤ ·)

/-- Report §3.3.3, Decision 4 of Stage 11b — the second status line, e.g.
`hardware profile ibm_kyiv: exceeds depth budget (230 > 200); δ_hw ≤ 7/128 + 390·1/100 =
2531/640 (vacuous)`. -/
def HardwareCheck.statusLine (c : HardwareCheck) : String :=
  let over := c.components.filter (!·.fits)
  let budgets := if over.isEmpty then "fits all budgets" else
    "exceeds " ++ ", ".intercalate (over.map fun k =>
      s!"{k.name} budget ({k.required} > {k.budget.getD 0})")
  let bound := match c.pBar, c.deltaHw with
    | some p, some h =>
      s!"δ_hw ≤ {c.delta} + {c.G}·{p} = {h}{if 1 ≤ h then " (vacuous)" else ""}"
    | _, _ => "δ_hw not computed (the profile gives no p̄)"
  s!"hardware profile {c.profile}: {budgets}; {bound}"

/-- Parse an unsigned decimal `"0.01"`, `"2"`, `"1.5"` exactly (`[0-9]+(\.[0-9]+)?`). -/
def parseDecimal (s : String) : Option Rat :=
  let digits (t : String) : Option Nat :=
    if t.isEmpty || !t.all Char.isDigit then none else t.toNat?
  match s.splitOn "." with
  | [i] => (digits i).map fun n => (n : Rat)
  | [i, f] => do
    let n ← digits i
    let m ← digits f
    return (n : Rat) + (m : Rat) / ((10 ^ f.length : Nat) : Rat)
  | _ => none

end CQRV

end
