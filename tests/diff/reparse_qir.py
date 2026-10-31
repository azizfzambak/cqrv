"""Re-parser for the QIR emitted by `cqr emit --format qir` (report §5.3, §8.4.3; Stage 8a,
reviewer decision 6: the emitter is a trust boundary, translation-validated by re-parse).

Reads the LLVM IR text back into the IR JSON format of `cqr synthesize --json`
(`{n_data, n_anc, gates: [{op, q, c?, if?}]}`) plus the terminal measurement, and checks the
static shape on the way: Adaptive Profile attributes, module flags, static qubit/result
addresses, `read_result` + `br i1` into a block with exactly one gate, one `measurements:`
block, the `output:` record. Any line it does not understand is an error, never skipped.
Stage 17b (PHASE2_SPEC.md §A.1): `__quantum__qis__rz__body(double <hex float>, ptr q)` gives
`{"op":"p","q":[i],"angle": float}` (the hex-float literal `0x…` decoded with `struct`); the
emitter writes `rz` for `p a k` with angle 2πa/2^k and a top-level `cp` as its five-gate
decomposition, so `emit_diff.py` compares such a re-parse against the Lean IR after
`Circuit.decomposeCp`, with the angles to 1e-12.

Usage as a module: `parse(text) -> (circuit_dict, terminal)` with `terminal` the list of
`(qubit, result)` pairs of the `measurements:` block.
"""

import re
import struct

GATES = {"h": "h", "s": "s", "s__adj": "sdg", "t": "t", "t__adj": "tdg", "x": "x", "z": "z",
         "cnot": "cnot", "cz": "cz"}
PTR = r"ptr (?:inttoptr \(i64 (\d+) to ptr\)|null)"
RE_HEX_FLOAT = re.compile(r"^double 0x([0-9A-Fa-f]{16})$")
RE_GATE = re.compile(r"^  call void @__quantum__qis__(\w+?)__body\((.*)\)$")
RE_ARG = re.compile(r"^" + PTR + r"$")
RE_READ = re.compile(r"^  %(c\d+) = call i1 @__quantum__qis__read_result__body\((.*)\)$")
RE_BR_COND = re.compile(r"^  br i1 %(c\d+), label %(then\d+), label %(cont\d+)$")
RE_BR = re.compile(r"^  br label %(\w+)$")
RE_LABEL = re.compile(r"^(\w+):$")
RE_ANNOT = re.compile(r"^  ; cqrv: (alloc|free) (\d+)$")
RE_ATTR0 = re.compile(r'^attributes #0 = \{ "entry_point" "output_labeling_schema" '
                      r'"qir_profiles"="adaptive_profile" "required_num_qubits"="(\d+)" '
                      r'"required_num_results"="(\d+)" \}$')
RE_ARRAY_OUT = re.compile(r"^  call void @__quantum__rt__array_record_output\(i64 (\d+), ptr @out\)$")
RE_RES_OUT = re.compile(r"^  call void @__quantum__rt__result_record_output\((.*), ptr @out(\d+)\)$")
FLAGS = [
    '!0 = !{i32 1, !"qir_major_version", i32 1}',
    '!1 = !{i32 7, !"qir_minor_version", i32 0}',
    '!2 = !{i32 1, !"dynamic_qubit_management", i1 false}',
    '!3 = !{i32 1, !"dynamic_result_management", i1 false}',
]


class ParseError(ValueError):
    pass


def _args(s):
    out = []
    for a in s.split(", "):
        m = RE_ARG.match(a)
        if not m:
            raise ParseError(f"not a static address: {a!r}")
        out.append(int(m.group(1)) if m.group(1) is not None else 0)
    return out


def _gate(line):
    """A unitary QIS call -> (op, qubits) or, for `rz` (Stage 17b), (op, qubits, angle); None
    otherwise."""
    m = RE_GATE.match(line)
    if not m or m.group(1) == "mz":
        return None
    if m.group(1) == "rz":
        parts = m.group(2).split(", ")
        mh = RE_HEX_FLOAT.match(parts[0]) if len(parts) == 2 else None
        if not mh:
            raise ParseError(f"rz needs one hex-float double and one qubit: {line!r}")
        (angle,) = struct.unpack(">d", bytes.fromhex(mh.group(1)))
        return "p", _args(parts[1]), angle
    if m.group(1) not in GATES:
        raise ParseError(f"unknown QIS callee: {line!r}")
    op = GATES[m.group(1)]
    q = _args(m.group(2))
    if len(q) != (2 if op in ("cnot", "cz") else 1):
        raise ParseError(f"wrong arity: {line!r}")
    return op, q


def _gate_dict(g):
    d = {"op": g[0], "q": g[1]}
    if len(g) == 3:
        d["angle"] = g[2]
    return d


def parse(text):
    lines = text.replace("\r\n", "\n").split("\n")
    attrs = [RE_ATTR0.match(ln) for ln in lines if ln.startswith("attributes #0")]
    if len(attrs) != 1 or not attrs[0]:
        raise ParseError("missing or malformed Adaptive Profile entry-point attributes")
    num_qubits, num_results = int(attrs[0].group(1)), int(attrs[0].group(2))
    for f in FLAGS + ["!llvm.module.flags = !{!0, !1, !2, !3}"]:
        if f not in lines:
            raise ParseError(f"missing module flag {f!r}")
    try:
        start = next(i for i, ln in enumerate(lines) if re.match(r"^define i64 @\w+\(\) #0 \{$", ln))
    except StopIteration:
        raise ParseError("no entry point definition")
    end = lines.index("}", start)
    body = lines[start + 1:end]
    if body[:2] != ["entry:", "  call void @__quantum__rt__initialize(ptr null)"]:
        raise ParseError("entry block must start with __quantum__rt__initialize(ptr null)")
    i = 2
    gates, results_written = [], []
    terminal, recorded, n_out = [], [], None
    block = "entry"
    while i < len(body):
        ln = body[i]
        if block == "entry" or block.startswith("cont"):
            m = RE_ANNOT.match(ln)
            if m:
                gates.append({"op": m.group(1), "q": [int(m.group(2))]})
                i += 1
                continue
            g = _gate(ln)
            if g:
                gates.append(_gate_dict(g))
                i += 1
                continue
            m = RE_GATE.match(ln)
            if m and m.group(1) == "mz":
                q, r = _args(m.group(2))
                gates.append({"op": "measure", "q": [q], "c": r})
                results_written.append(r)
                i += 1
                continue
            m = RE_READ.match(ln)
            if m:
                (r,) = _args(m.group(2))
                if r not in results_written:
                    raise ParseError(f"result {r} read before it is written: {ln!r}")
                # %cK = read; br i1 %cK, then, cont; then: <gate>; br cont; cont:
                mb = RE_BR_COND.match(body[i + 1]) if i + 1 < len(body) else None
                if not mb or mb.group(1) != m.group(1):
                    raise ParseError(f"read_result not followed by its br i1: {ln!r}")
                then, cont = mb.group(2), mb.group(3)
                if body[i + 2] != f"{then}:":
                    raise ParseError(f"block {then} does not follow its branch")
                g = _gate(body[i + 3])
                if not g:
                    raise ParseError(f"block {then} must hold exactly one unitary gate")
                if body[i + 4] != f"  br label %{cont}" or body[i + 5] != f"{cont}:":
                    raise ParseError(f"block {then} must branch to {cont}, which follows it")
                gates.append({**_gate_dict(g), "if": r})
                block = cont
                i += 6
                continue
            if ln == "  br label %measurements" and body[i + 1] == "measurements:":
                block = "measurements"
                i += 2
                continue
            raise ParseError(f"unexpected line in the gate section: {ln!r}")
        elif block == "measurements":
            m = RE_GATE.match(ln)
            if m and m.group(1) == "mz":
                terminal.append(tuple(_args(m.group(2))))
                i += 1
                continue
            if ln == "  br label %output" and body[i + 1] == "output:":
                block = "output"
                i += 2
                continue
            raise ParseError(f"unexpected line in the measurements block: {ln!r}")
        elif block == "output":
            m = RE_ARRAY_OUT.match(ln)
            if m and n_out is None:
                n_out = int(m.group(1))
                i += 1
                continue
            m = RE_RES_OUT.match(ln)
            if m:
                (r,) = _args(m.group(1))
                recorded.append((r, int(m.group(2))))
                i += 1
                continue
            if ln == "  ret i64 0" and i == len(body) - 1:
                i += 1
                continue
            raise ParseError(f"unexpected line in the output block: {ln!r}")
    if block != "output":
        raise ParseError("no measurements/output blocks")
    n_data = len(terminal)
    if n_out != n_data or recorded != [(r, k) for k, (_, r) in enumerate(terminal)]:
        raise ParseError("output record does not match the terminal measurement")
    if [q for q, _ in terminal] != list(range(n_data)):
        raise ParseError("terminal measurement must cover the data qubits 0..n-1 in order")
    m_bits = len(results_written)
    if sorted(results_written) != list(range(m_bits)):
        raise ParseError("mid-circuit results must be 0..m-1, each written once")
    if [r for _, r in terminal] != list(range(m_bits, m_bits + n_data)):
        raise ParseError("terminal results must follow the mid-circuit results")
    if num_results != m_bits + n_data:
        raise ParseError(f"required_num_results = {num_results}, expected {m_bits + n_data}")
    n_anc = num_qubits - n_data
    for g in gates:
        if any(q >= num_qubits for q in g["q"]):
            raise ParseError(f"qubit out of range in {g}")
    return {"n_data": n_data, "n_anc": n_anc, "gates": gates}, terminal
