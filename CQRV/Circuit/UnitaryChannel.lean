module

public import CQRV.Circuit.Semantics

/-!
# CQRV.Circuit.UnitaryChannel

PHASE2_SPEC.md §A.2 (5) (Stage 18c, docs/tasks/STAGE18_TASK.md C2) — the channel bridge: on a
well-formed, measurement-free circuit the density-matrix semantics `channelDenote` is the unitary
channel `CPTPMap.ofUnitary` of the unitary semantics `unitaryDenote`:

```
channelDenote_of_unitary : C.WF → C.gates.all Gate.isUnitary = true →
  channelDenote n a C = CPTPMap.ofUnitary ⟨unitaryDenote n a C.gates, _⟩
```

Proof: `channelDenote_of_WF` gives the Kraus channel; the circuit has no `measure`, so
`C.nBits = 0` (`nBits_eq_zero_of_unitary`) and the Kraus sum over `Fin 0 → Bool` has the single
term `unitaryDenote n a C.gates` (`krausOps_of_unitary`); `CPTPMap.ext` on the `MatrixMap`s
(`MatrixMap.of_kraus_eq_sum_conj`, `Finset.sum_const`). Stages 19–20 reuse it for the
controlled-powers block.

Import discipline (PHASE2_SPEC.md §A.8 item 6): this module imports Physlib through
`CQRV.Circuit.Semantics` and is never in the import closure of the `cqr` executable.
-/

public section

namespace CQRV

open Matrix

variable (n a : ℕ)

/-- A measurement-free gate list writes no classical bit. -/
theorem Circuit.written_eq_nil_of_unitary {gs : List Gate} (h : gs.all Gate.isUnitary = true) :
    Circuit.written gs = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [Circuit.written, List.flatMap_cons, ← Circuit.written, ih h.2, List.append_nil]
    cases g <;> simp_all [Gate.writes, Gate.isUnitary]

/-- Report §9.1.1 — a measurement-free circuit has no classical bits. -/
theorem Circuit.nBits_eq_zero_of_unitary {C : Circuit} (hU : C.gates.all Gate.isUnitary = true) :
    C.nBits = 0 := by
  simp [Circuit.nBits, Circuit.written_eq_nil_of_unitary hU]

/-- PHASE2_SPEC.md §A.2 (5), report §9.1.1 — **the channel bridge**: on a well-formed,
measurement-free circuit `channelDenote` is the unitary channel of `unitaryDenote`. -/
theorem channelDenote_of_unitary {C : Circuit} (hWF : C.WF)
    (hU : C.gates.all Gate.isUnitary = true) :
    channelDenote n a C =
      CPTPMap.ofUnitary ⟨unitaryDenote n a C.gates, unitaryDenote_mem_unitaryGroup n a C.gates⟩ := by
  rw [channelDenote_of_WF n a hWF]
  apply CPTPMap.ext
  change MatrixMap.of_kraus (krausOps n a C.nBits C.gates) (krausOps n a C.nBits C.gates) =
    MatrixMap.conj (unitaryDenote n a C.gates)
  rw [MatrixMap.of_kraus_eq_sum_conj]
  simp_rw [krausOps_of_unitary n a C.nBits C.gates hU]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Circuit.nBits_eq_zero_of_unitary hU, pow_zero, one_smul]

end CQRV

end
