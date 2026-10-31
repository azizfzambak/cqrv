module

public import CQRV.Circuit.IR

/-!
# CQRV.Emit.QASM

Report §5.3 (the emitted program is an explicit trust boundary), §8.4.3 — OpenQASM 3 text of a
circuit (DECISIONS.md 2026-10-24, Stage 8a reviewer decision 5):
`OPENQASM 3.0; include "stdgates.inc"; qubit[n] x; qubit[a] anc; bit[m] c; bit[n] out;`, gates
by their `stdgates.inc` names (`cx` for CNOT), `c[j] = measure q;`, `if (c[j]) { g }`, and the
final `out = measure x;`. `alloc` / `free` are the structured comments `// cqrv: alloc q` /
`// cqrv: free q` (OpenQASM 3 qubits are declared statically). Declarations of size 0 are
omitted. Unverified; `tests/diff/reparse_qasm.py` translation-validates it.
-/

@[expose] public section

namespace CQRV.Emit

/-- The OpenQASM 3 operand of a qubit (`x[i]`, `anc[i]`). -/
def qasmQubit : Qubit → String
  | .data i => s!"x[{i}]"
  | .anc i => s!"anc[{i}]"

/-- One statement of a gate (without indentation). -/
def qasmGate : Gate → String
  | .h q => s!"h {qasmQubit q};"
  | .s q => s!"s {qasmQubit q};"
  | .sdg q => s!"sdg {qasmQubit q};"
  | .t q => s!"t {qasmQubit q};"
  | .tdg q => s!"tdg {qasmQubit q};"
  | .x q => s!"x {qasmQubit q};"
  | .z q => s!"z {qasmQubit q};"
  | .cnot a b => s!"cx {qasmQubit a}, {qasmQubit b};"
  | .cz a b => s!"cz {qasmQubit a}, {qasmQubit b};"
  | .measure q c => s!"c[{c}] = measure {qasmQubit q};"
  | .ifBit c g => s!"if (c[{c}]) \{ {qasmGate g} }"
  | .alloc q => s!"// cqrv: alloc {qasmQubit q}"
  | .free q => s!"// cqrv: free {qasmQubit q}"
  -- Stage 17a: the phase gates exist in the IR but no synthesized circuit contains them; their
  -- OpenQASM 3 form (`p(2*pi*a/N)`, PHASE2_SPEC.md §A.1) is Stage 17b. Until then a comment.
  | .p a k q => s!"// cqrv: unsupported before Stage 17b: {(Gate.p a k q).render}"
  | .cp a k c t => s!"// cqrv: unsupported before Stage 17b: {(Gate.cp a k c t).render}"

/-- Report §8.4.3 — the OpenQASM 3 program of a circuit, with the terminal measurement of the
data register into `out`. -/
def emitQASM (name : String) (C : Circuit) : String :=
  let decl (ty reg : String) (k : Nat) : List String := if k == 0 then [] else [s!"{ty}[{k}] {reg};"]
  let lines :=
    [s!"// OpenQASM 3 — {name} (CQRV, report §8.4.3); unverified emitter (§5.3)",
     "OPENQASM 3.0;", "include \"stdgates.inc\";"] ++
    decl "qubit" "x" C.nData ++ decl "qubit" "anc" C.nAnc ++ decl "bit" "c" C.nBits ++
    decl "bit" "out" C.nData ++ C.gates.map qasmGate ++ ["out = measure x;"]
  "\n".intercalate lines ++ "\n"

end CQRV.Emit

end
