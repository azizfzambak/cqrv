module

public import CQRV.Emit.QIR
public import CQRV.Emit.QASM

/-!
# CQRV.Emit

Report §5.3, §8.4.3 — QIR (Adaptive Profile, static addressing) and OpenQASM 3 emitters
(Stage 8a). Both are unverified and translation-validated by re-parse (`tests/diff/`).

Stage 17b (PHASE2_SPEC.md §A.1): `sampleCircuit`, a fixed circuit with every gate constructor,
the phase gates included, which no synthesized circuit contains; `scripts/CertifyTool.lean
emit-sample` prints it as IR JSON, OpenQASM 3 or QIR and `tests/diff/emit_diff.py` re-parses the
texts. `sampleCircuitIfCp` adds a classically controlled `cp`, the negative QIR case.
-/

@[expose] public section

namespace CQRV.Emit

/-- PHASE2_SPEC.md §A.1 (Stage 17b) — the sample circuit of the emitter tests: 3 data qubits, one
ancilla, every gate constructor at least once (`p 1 3`, `p (-3) 5`, `p 2 4`, `p 0 5`, `cp 1 1`,
`cp 1 2`, `cp (-1) 3`, an `ifBit` over `p 1 1` and one over `p 1 2`, `measure`, `alloc` / `free`);
`Circuit.validate` passes; no `ifBit` over a `cp`. -/
def sampleCircuit : Circuit := ⟨3, [
  .alloc (.anc 0), .h (.data 0), .h (.data 1), .h (.data 2), .h (.anc 0),
  .s (.data 0), .sdg (.data 1), .t (.data 2), .tdg (.anc 0), .x (.data 1), .z (.data 2),
  .cnot (.data 0) (.anc 0), .cz (.data 1) (.data 2),
  .p 1 3 (.data 0), .p (-3) 5 (.data 1), .p 2 4 (.data 2), .p 0 5 (.anc 0),
  .cp 1 1 (.data 0) (.data 1), .cp 1 2 (.data 1) (.data 2), .cp (-1) 3 (.data 2) (.anc 0),
  .h (.anc 0), .measure (.anc 0) 0,
  .ifBit 0 (.p 1 1 (.data 0)), .ifBit 0 (.p 1 2 (.data 1)), .ifBit 0 (.cz (.data 1) (.data 2)),
  .ifBit 0 (.x (.anc 0)), .free (.anc 0)]⟩

/-- PHASE2_SPEC.md §A.1 (Stage 17b) — `sampleCircuit` with one `ifBit` over `cp 1 1` (a Clifford
gate, so `validate` passes): OpenQASM 3 emits it, the QIR emitter refuses it
(`unsupported_in_qir`). -/
def sampleCircuitIfCp : Circuit :=
  ⟨3, sampleCircuit.gates.dropLast ++ [.ifBit 0 (.cp 1 1 (.data 1) (.data 2)), .free (.anc 0)]⟩

end CQRV.Emit

end
