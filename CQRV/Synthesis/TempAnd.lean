module

public import CQRV.Circuit.IR

/-!
# CQRV.Synthesis.TempAnd

Report §6.2.2 — Gidney's temporary logical-AND (arXiv:1709.06648, Fig. 3) and its
measurement-based uncomputation (MBU), gate for gate as the §6.2.2 listing, with one addition
recorded as a report erratum (DECISIONS.md 2026-10-23, Stage 5): the listing's uncompute
claims the target is "restored to |0⟩ (reset)" but contains no reset. After the X-basis
measurement (`H; measure`) the target is |m⟩, so `ifBit m (X t)` is appended. It is Clifford
(0 T) and shares the layer of the CZ fix-up under the decision-4 scheduler.
-/

@[expose] public section

namespace CQRV.Synthesis

/-- Report §6.2.2, compute phase, gate for gate (4 T): on |a, b, 0⟩ the target ends in
|a ∧ b⟩, controls unchanged. -/
def TempLogicalAND (a b t : Qubit) : List Gate :=
  [.h t, .t t,
   .cnot a t, .cnot b t,
   .cnot t a, .cnot t b,
   .tdg a, .tdg b, .t t,
   .cnot t a, .cnot t b,
   .h t, .s t]

/-- Report §6.2.2, uncompute phase (0 T), MBU: `H t; measure t → m; if m: CZ a b`, plus the
erratum fix `if m: X t` that returns the target to |0⟩. -/
def UncomputeTempLogicalAND (a b t : Qubit) (m : Nat) : List Gate :=
  [.h t, .measure t m, .ifBit m (.cz a b), .ifBit m (.x t)]

/-- PHASE2_SPEC.md §A.0.1 (extends report §6.1.4, §6.2.2, §10.1.1; Stage 15a) — how the ancilla
of an AND is uncomputed: `mbu` (measurement-based, the §6.2.2 listing; the Phase 1 code path,
gate for gate, and the default) or `coherent` (the adjoint of the compute block: 4 more T per
AND, no measurement, no classical bit). -/
inductive UncomputeMode where
  | mbu
  | coherent
  deriving Repr, DecidableEq, Inhabited

namespace UncomputeMode

/-- The CLI / JSON name of a mode. -/
def toString : UncomputeMode → String
  | .mbu => "mbu"
  | .coherent => "coherent"

instance : ToString UncomputeMode := ⟨UncomputeMode.toString⟩

/-- Parse a `--uncompute` value. -/
def parse? : String → Option UncomputeMode
  | "mbu" => some .mbu
  | "coherent" => some .coherent
  | _ => none

end UncomputeMode

/-- PHASE2_SPEC.md §A.0.1 — the coherent uncompute (4 T, 13 gates): the adjoint of the compute
listing, `S† t; H t; CNOT t b; CNOT t a; T† t; T b; T a; CNOT t b; CNOT t a; CNOT b t;
CNOT a t; T† t; H t`. On |a, b, a ∧ b⟩ it returns the target to |0⟩ with amplitude 1
(`tempLogicalAND_adjoint_basis`). -/
def UncomputeTempLogicalANDCoherent (a b t : Qubit) : List Gate :=
  adjointGates (TempLogicalAND a b t)

end CQRV.Synthesis

end
