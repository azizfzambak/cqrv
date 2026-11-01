module

public import CQRV.Circuit.IR
public import CQRV.Circuit.Schedule

/-!
# CQRV.Synthesis.QFT

PHASE2_SPEC.md §A.2 (Stage 18b, docs/tasks/STAGE18_TASK.md B1) — the quantum Fourier transform
on `m` data qubits as a gate list of the IR, and its approximate form.

* `qftBlock m j` is block `j` of the textbook circuit without the final swaps: `H` on data
  qubit `j`, then `cp 1 k` from qubit `j + k − 1` onto qubit `j` for `k = 2 .. m − j` (0-based:
  `i < m − j − 1`, `k = i + 2`, control `j + i + 1`); `qftGates m` is the concatenation of the
  blocks `j = 0 .. m − 1` and `qftCircuit m = ⟨m, qftGates m⟩`.
* `aqftGates m kmax` drops every `cp 1 k` with `k > kmax` (a `List.filter` of `qftGates m`; the
  `H` gates always stay); `aqftGates_eq_self : m ≤ kmax → aqftGates m kmax = qftGates m`.
* Proved for every `m` here (Lean core only): the membership lemmas, `qftGates_cp_le : cp a k c t
  ∈ qftGates m → k ≤ m`, `aqftGates_eq_self` and `qftBlock_length`. Well-formedness and
  unitarity (`qftCircuit_WF`, `aqftCircuit_WF`, `qftGates_unitary`), the gate count
  `qftGates_length : (qftGates m).length = m (m + 1) / 2` and the semantics (`qft_basis`) are
  `CQRV.Circuit.QFTCorrect`: `Circuit.WF` and `Gate.isUnitary` live in `CQRV.Circuit.Semantics`,
  which imports Physlib (and Mathlib), and this module stays in the Physlib-free closure of the
  synthesizer and the `cqr` executable (Physlib's trailing notation `p [x ↔ y]` would otherwise
  change the parsing of `CQRV.Certify.RunReport`).
* Every `cp 1 k` with `k ≥ 2` is a rotation of §A.1 (`GradeExt.rot = m (m − 1) / 2`, `t = 0`);
  the measured grades are `#guard`s in `tests/CQRVTests/QFT.lean`. The inverse circuits are
  `adjointGates (qftGates m)` (§A.0.1).
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV

/-- PHASE2_SPEC.md §A.2 — block `j` of the textbook QFT without the final swaps: `H` on data
qubit `j`, then `cp 1 k` from qubit `j + k − 1` onto qubit `j` for `k = 2 .. m − j`. -/
def qftBlock (m j : ℕ) : List Gate :=
  .h (.data j) :: (List.range (m - j - 1)).map fun i => .cp 1 (i + 2) (.data (j + i + 1)) (.data j)

/-- PHASE2_SPEC.md §A.2 — the QFT on `m` data qubits: the blocks `j = 0 .. m − 1`. -/
def qftGates (m : ℕ) : List Gate := (List.range m).flatMap (qftBlock m)

/-- PHASE2_SPEC.md §A.2 — `aqft m kmax` drops every `cp 1 k` with `k > kmax` (a filter of
`qftGates`). -/
def aqftGates (m kmax : ℕ) : List Gate :=
  (qftGates m).filter fun g => match g with | .cp _ k _ _ => decide (k ≤ kmax) | _ => true

/-- PHASE2_SPEC.md §A.2 — the QFT circuit on `m` data qubits (no ancilla). -/
def qftCircuit (m : ℕ) : Circuit := ⟨m, qftGates m⟩

/-- PHASE2_SPEC.md §A.2 — the approximate QFT circuit on `m` data qubits. -/
def aqftCircuit (m kmax : ℕ) : Circuit := ⟨m, aqftGates m kmax⟩

/-! ## Membership -/

theorem mem_qftBlock {m j : ℕ} {g : Gate} (hg : g ∈ qftBlock m j) :
    g = .h (.data j) ∨ ∃ i, i < m - j - 1 ∧ g = .cp 1 (i + 2) (.data (j + i + 1)) (.data j) := by
  simp only [qftBlock, List.mem_cons, List.mem_map, List.mem_range] at hg
  rcases hg with h | ⟨i, hi, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, rfl⟩

theorem mem_qftGates {m : ℕ} {g : Gate} (hg : g ∈ qftGates m) :
    ∃ j, j < m ∧ g ∈ qftBlock m j := by
  simpa [qftGates, List.mem_flatMap, List.mem_range] using hg

theorem mem_aqftGates {m kmax : ℕ} {g : Gate} (hg : g ∈ aqftGates m kmax) : g ∈ qftGates m :=
  (List.mem_filter.mp hg).1

/-- PHASE2_SPEC.md §A.2 — every rotation of the QFT has `k ≤ m`. -/
theorem qftGates_cp_le {m : ℕ} {a : ℤ} {k : ℕ} {c t : Qubit}
    (hg : Gate.cp a k c t ∈ qftGates m) : k ≤ m := by
  obtain ⟨j, _, hgj⟩ := mem_qftGates hg
  rcases mem_qftBlock hgj with h | ⟨i, hi, h⟩
  · cases h
  · cases h
    omega

/-- PHASE2_SPEC.md §A.2 — with `kmax ≥ m` nothing is dropped. -/
theorem aqftGates_eq_self {m kmax : ℕ} (h : m ≤ kmax) : aqftGates m kmax = qftGates m := by
  rw [aqftGates, List.filter_eq_self]
  intro g hg
  cases g with
  | cp a k c t => exact decide_eq_true (Nat.le_trans (qftGates_cp_le hg) h)
  | _ => rfl

/-- Block `j` has `m − j` gates (one `H` and `m − j − 1` rotations). -/
theorem qftBlock_length {m j : ℕ} (hj : j < m) : (qftBlock m j).length = m - j := by
  simp only [qftBlock, List.length_cons, List.length_map, List.length_range]
  omega

end CQRV.Synthesis

end
