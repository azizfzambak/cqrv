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

end CQRV.Synthesis

end
