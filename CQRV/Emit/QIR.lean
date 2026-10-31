module

public import CQRV.Circuit.IR
public import CQRV.DSL.Diagnostic

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
  `nBits .. nBits + nData − 1`, recorded as the output array `out` (`output:` block);
* Stage 17b (PHASE2_SPEC.md §A.1): the gate list is first passed through `Circuit.decomposeCp`
  (`decomposeCp_unitary_wf`: the same unitary on the circuit's own register), so a top-level
  `cp a k c t` becomes the five calls `rz, rz, cnot, rz, cnot`; `p a k q` is
  `__quantum__qis__rz__body(double θ, ptr q)` with `θ = 2πa/2^k` as a `Float` printed as the
  **LLVM hex-float literal** of its bits (`qirAngle`; a decimal that is not exactly representable
  is rejected by `llvm-as`). `rz(θ) = e^{-iθ/2} · p(θ)`: a global phase per gate (per branch under
  `ifBit`), irrelevant to every statement of this project (the run report says so, row 8). The
  `rz` declaration is written only when the text uses it, so circuits without phase gates are
  emitted byte for byte as before. A `cp` under `ifBit` has **no QIR form in this emitter**
  (`decomposeCp` leaves it alone; the Adaptive-Profile branch would need the five gates):
  `emitQIR` returns the diagnostic `unsupported_in_qir` (stage `emit`) and `cqr emit` /
  `cqr certify` write nothing. OpenQASM 3 is unaffected.

The emitter is unverified; `tests/diff/reparse_qir.py` translation-validates it.
-/

@[expose] public section

namespace CQRV.Emit

open CQRV.DSL in
/-- PHASE2_SPEC.md §A.1 (Stage 17b) — the diagnostic of a classically controlled `cp` (gate
number `k` of the circuit). -/
def unsupportedInQir (k : Nat) (g : Gate) : CQRV.DSL.Diagnostic :=
  Diagnostic.at .emit .unsupportedInQir ⟨1, 1⟩
    s!"classically controlled cp has no QIR form in this emitter (gate {k}: `{g.render}`)"

/-- `ptr inttoptr (i64 k to ptr)`: the static address `k` of a qubit or a result. -/
def qirPtr (k : Nat) : String := s!"ptr inttoptr (i64 {k} to ptr)"

/-- π as the double `0x400921FB54442D18` (the bits of `math.pi`), so that the angle below is
computed exactly as the re-parser's reference `2*math.pi*a/2**k`. -/
def qirPi : Float := Float.ofBits 0x400921FB54442D18

/-- The 16 upper-case hex digits of a 64-bit word. -/
def hex16 (w : UInt64) : String :=
  let s := String.ofList ((Nat.toDigits 16 w.toNat).map Char.toUpper)
  "".pushn '0' (16 - s.length) ++ s

/-- PHASE2_SPEC.md §A.1 (Stage 17b) — the angle `θ = 2πa/2^k` of `p a k` as an LLVM hex-float
literal: `0x` and the 16 hex digits of `Float.toBits` (the only `double` syntax `llvm-as` accepts
for a value that is not exactly representable in decimal). -/
def qirAngle (a : Int) (k : Nat) : String :=
  let θ : Float := 2 * qirPi * Float.ofInt a / Float.ofNat (2 ^ k)
  "0x" ++ hex16 θ.toBits

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

/-- One `call` line of a unitary gate; `p a k q` is `rz` with its hex-float angle (Stage 17b). A
`cp` never reaches this function: `emitQIR` decomposes the top-level ones and refuses the
classically controlled ones. -/
def qirCall (C : Circuit) (g : Gate) : String :=
  match g with
  | .p a k q =>
    s!"  call void @__quantum__qis__rz__body(double {qirAngle a k}, {qirPtr (C.qIndex q)})"
  | g =>
    match qirCallee g with
    | some (f, qs) =>
      s!"  call void @__quantum__qis__{f}__body({", ".intercalate (qs.map (qirPtr ∘ C.qIndex))})"
    | none => s!"  ; unsupported gate {g.render}"

/-- Whether a gate is emitted as `rz` (a `p`, also under `ifBit`): the `rz` declaration is
written iff some gate is. -/
def usesRz : Gate → Bool
  | .p .. => true
  | .ifBit _ g => usesRz g
  | _ => false

/-- The first classically controlled `cp` of a gate list, with its index. -/
def findIfCp (gs : List Gate) : Option (Nat × Gate) :=
  (gs.zipIdx.find? fun (g, _) => match g with | .ifBit _ (.cp ..) => true | _ => false).map
    fun (g, k) => (k, g)

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
gates (after `Circuit.decomposeCp`, Stage 17b), then one terminal measurement of the data
register, recorded as the array `out`. `.error` (stage `emit`, code `unsupported_in_qir`) iff the
circuit has a `cp` under `ifBit`. -/
def emitQIR (name : String) (C : Circuit) : Except CQRV.DSL.Diagnostic String := do
  if let some (k, g) := findIfCp C.gates then throw (unsupportedInQir k g)
  let gates := Circuit.decomposeCp C.gates
  let n := C.nData
  let m := C.nBits
  let labels := qirLabel "out" "out" :: (List.range n).map fun i => qirLabel s!"out{i}" s!"out[{i}]"
  let body := (gates.zipIdx.map fun (g, k) => qirGate C k g).flatten
  let measure := (List.range n).map fun i =>
    s!"  call void @__quantum__qis__mz__body({qirPtr i}, {qirPtr (m + i)})"
  let record :=
    s!"  call void @__quantum__rt__array_record_output(i64 {n}, ptr @out)" ::
    (List.range n).map fun i =>
      s!"  call void @__quantum__rt__result_record_output({qirPtr (m + i)}, ptr @out{i})"
  let decls := ["h", "s", "s__adj", "t", "t__adj", "x", "z"].map
      (fun f => s!"declare void @__quantum__qis__{f}__body(ptr)") ++
    ["declare void @__quantum__qis__cnot__body(ptr, ptr)",
     "declare void @__quantum__qis__cz__body(ptr, ptr)"] ++
    (if gates.any usesRz then ["declare void @__quantum__qis__rz__body(double, ptr)"] else []) ++
    ["declare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1",
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
  return "\n".intercalate lines ++ "\n"

end CQRV.Emit

end
