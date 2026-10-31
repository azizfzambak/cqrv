module

/-!
# CQRV.Grades.Ext

PHASE2_SPEC.md §A.1, §A.8 item 2 (Stage 17a); report §3.1.1 — the second resource record
`GradeExt`: two-qubit gate count, T-depth, rotation count, measurement count and feed-forward
count, measured by the same decision-4 scheduler as `Grade` (`Circuit.gradeExt` in
`CQRV.Circuit.Schedule`) and, from Stage 17b, stated in every certificate as its own theorem
`gradeExt_eq`. `Grade` (w, d, t, a) and the budget order are unchanged.

There is **no ⊕ / ⊗ algebra** for `GradeExt` in Stage 17: it is measured, not composed (the
T-depth of a sequential composition is not the sum of the T-depths in general).
-/

@[expose] public section

namespace CQRV

/-- PHASE2_SPEC.md §A.1 — the second resource record, measured on the decision-4 schedule. -/
structure GradeExt where
  /-- Two-qubit gates: `cnot`, `cz`, `cp` (also under `ifBit`). -/
  twoQ : Nat
  /-- Layers of the decision-4 schedule that contain a `t` / `tdg` or a T-power `p`. -/
  tDepth : Nat
  /-- `p` / `cp` gates that are neither Clifford nor T-powers (also under `ifBit`); their
  Clifford+T cost depends on a synthesis precision (PHASE2_SPEC.md §C) and is not folded into
  `Grade.t`. -/
  rot : Nat
  /-- `measure` gates. -/
  meas : Nat
  /-- `ifBit` gates (feed-forward). -/
  ff : Nat
  deriving DecidableEq, Repr

end CQRV

end
