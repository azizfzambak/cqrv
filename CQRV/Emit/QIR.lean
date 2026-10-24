module

public import CQRV.Circuit.IR

/-!
# CQRV.Emit.QIR

Report §5.3.1–5.3.4 (the emitted IR is an explicit trust boundary), §8.4.3 (QIR export, Adaptive
Profile) — LLVM IR text (opaque pointers) for the QIR Adaptive Profile with static addressing
(DECISIONS.md 2026-10-24, Stage 8a reviewer decision 4):

* qubit `k` is `inttoptr (i64 k to ptr)`: data `x[i] ↦ i`, ancilla `anc[i] ↦ nData + i`
  (`Circuit.qIndex`, as in the IR JSON); result `j` likewise;
* the gate list is emitted flat, one `__quantum__qis__*__body` call per gate (Stage 8a
  interpretation: no project-level callees);
* `measure q → c` is `__quantum__qis__mz__body(q, result c)`; `ifBit c g` reads result `c` with
  `__quantum__qis__read_result__body` and branches (`br i1`) to a block holding `g`;
* `alloc` / `free` have no counterpart in static addressing; they are kept as the structured
  comments `; cqrv: alloc <k>` / `; cqrv: free <k>`, so that the re-parser recovers the IR;
* one terminal measurement block (`measurements:`) over the data register into results
  `nBits .. nBits + nData − 1`, recorded as the output array `out` (`output:` block).

The emitter is unverified; `tests/diff/reparse_qir.py` translation-validates it.
-/

@[expose] public section

namespace CQRV.Emit

/-- `ptr inttoptr (i64 k to ptr)`: the static address `k` of a qubit or a result. -/
def qirPtr (k : Nat) : String := s!"ptr inttoptr (i64 {k} to ptr)"

/-- Report §8.4.3 — the QIS callee of a unitary gate and its qubits (`none` for `measure`,
`ifBit`, `alloc`, `free`). -/
def qirCallee : Gate → Option (String × List Qubit)
  | .h q => some ("h", [q])
  | .s q => some ("s", [q])
  | .sdg q => some ("s__adj", [q])
  | .t q => some ("t", [q])
  | .tdg q => some ("t__adj", [q])
  | .x q => some ("x", [q])
  | .z q => some ("z", [q])
  | .cnot a b => some ("cnot", [a, b])
  | .cz a b => some ("cz", [a, b])
  | _ => none

/-- One `call` line of a unitary gate. -/
def qirCall (C : Circuit) (g : Gate) : String :=
  match qirCallee g with
  | some (f, qs) =>
    s!"  call void @__quantum__qis__{f}__body({", ".intercalate (qs.map (qirPtr ∘ C.qIndex))})"
  | none => s!"  ; unsupported gate {g.render}"

/-- Report §8.4.3 — the lines of gate number `k` (`k` makes block and value names unique). -/
def qirGate (C : Circuit) (k : Nat) : Gate → List String
  | .measure q c =>
    [s!"  call void @__quantum__qis__mz__body({qirPtr (C.qIndex q)}, {qirPtr c})"]
  | .ifBit c g =>
    [s!"  %c{k} = call i1 @__quantum__qis__read_result__body({qirPtr c})",
     s!"  br i1 %c{k}, label %then{k}, label %cont{k}",
     s!"then{k}:", qirCall C g, s!"  br label %cont{k}",
     s!"cont{k}:"]
  | .alloc q => [s!"  ; cqrv: alloc {C.qIndex q}"]
  | .free q => [s!"  ; cqrv: free {C.qIndex q}"]
  | g => [qirCall C g]

/-- A NUL-terminated string constant `@name = internal constant [len x i8] c"s\00"`. -/
def qirLabel (name s : String) : String :=
  s!"@{name} = internal constant [{s.utf8ByteSize + 1} x i8] c\"{s}\\00\""

/-- Report §8.4.3 — the QIR Adaptive Profile module of a circuit with entry point `@name`: the
gates, then one terminal measurement of the data register, recorded as the array `out`. -/
def emitQIR (name : String) (C : Circuit) : String :=
  let n := C.nData
  let m := C.nBits
  let labels := qirLabel "out" "out" :: (List.range n).map fun i => qirLabel s!"out{i}" s!"out[{i}]"
  let body := (C.gates.zipIdx.map fun (g, k) => qirGate C k g).flatten
  let measure := (List.range n).map fun i =>
    s!"  call void @__quantum__qis__mz__body({qirPtr i}, {qirPtr (m + i)})"
  let record :=
    s!"  call void @__quantum__rt__array_record_output(i64 {n}, ptr @out)" ::
    (List.range n).map fun i =>
      s!"  call void @__quantum__rt__result_record_output({qirPtr (m + i)}, ptr @out{i})"
  let decls := ["h", "s", "s__adj", "t", "t__adj", "x", "z"].map
      (fun f => s!"declare void @__quantum__qis__{f}__body(ptr)") ++
    ["declare void @__quantum__qis__cnot__body(ptr, ptr)",
     "declare void @__quantum__qis__cz__body(ptr, ptr)",
     "declare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1",
     "declare i1 @__quantum__qis__read_result__body(ptr)",
     "declare void @__quantum__rt__initialize(ptr)",
     "declare void @__quantum__rt__array_record_output(i64, ptr)",
     "declare void @__quantum__rt__result_record_output(ptr, ptr)"]
  let lines :=
    [s!"; QIR Adaptive Profile — {name} (CQRV, report §8.4.3); unverified emitter (§5.3)",
     s!"; data qubits 0..{n}, ancillae {n}..{n + C.nAnc}; mid-circuit results 0..{m}, \
       terminal results {m}..{m + n}", ""] ++
    labels ++ ["", s!"define i64 @{name}() #0 \{", "entry:",
      "  call void @__quantum__rt__initialize(ptr null)"] ++
    body ++ ["  br label %measurements", "measurements:"] ++ measure ++
    ["  br label %output", "output:"] ++ record ++ ["  ret i64 0", "}", ""] ++ decls ++
    ["", s!"attributes #0 = \{ \"entry_point\" \"output_labeling_schema\" \
        \"qir_profiles\"=\"adaptive_profile\" \"required_num_qubits\"=\"{n + C.nAnc}\" \
        \"required_num_results\"=\"{m + n}\" }",
     "attributes #1 = { \"irreversible\" }", "",
     "!llvm.module.flags = !{!0, !1, !2, !3}",
     "!0 = !{i32 1, !\"qir_major_version\", i32 1}",
     "!1 = !{i32 7, !\"qir_minor_version\", i32 0}",
     "!2 = !{i32 1, !\"dynamic_qubit_management\", i1 false}",
     "!3 = !{i32 1, !\"dynamic_result_management\", i1 false}"]
  "\n".intercalate lines ++ "\n"

end CQRV.Emit

end
