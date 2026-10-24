"""Re-parser for the OpenQASM 3 emitted by `cqr emit --format qasm` (report §5.3, §8.4.3;
Stage 8a, reviewer decision 6).

Reads the program back into the IR JSON format of `cqr synthesize --json`
(`{n_data, n_anc, gates: [{op, q, c?, if?}]}`, data qubits `x[i] -> i`, ancillae
`anc[i] -> n_data + i`) and the terminal measurement. Accepts exactly the subset the emitter
writes (declarations `qubit[n] x; qubit[a] anc; bit[m] c; bit[n] out;`, stdgates names,
`c[j] = measure q;`, `if (c[j]) { g; }`, `out = measure x;`, `// cqrv: alloc|free q`); any other
line is an error.

Usage as a module: `parse(text) -> (circuit_dict, terminal)`; `terminal` is the list of
`(qubit, out index)` pairs of `out = measure x;`.
"""

import re

GATES = {"h": "h", "s": "s", "sdg": "sdg", "t": "t", "tdg": "tdg", "x": "x", "z": "z",
         "cx": "cnot", "cz": "cz"}
QUBIT = r"(x|anc)\[(\d+)\]"
RE_DECL = re.compile(r"^(qubit|bit)\[(\d+)\] (x|anc|c|out);$")
RE_GATE = re.compile(r"^(\w+) " + QUBIT + r"(?:, " + QUBIT + r")?;$")
RE_MEASURE = re.compile(r"^c\[(\d+)\] = measure " + QUBIT + r";$")
RE_IF = re.compile(r"^if \(c\[(\d+)\]\) \{ (.*) \}$")
RE_ANNOT = re.compile(r"^// cqrv: (alloc|free) " + QUBIT + r"$")


class ParseError(ValueError):
    pass


def parse(text):
    lines = [ln for ln in text.replace("\r\n", "\n").split("\n") if ln != ""]
    if not lines or not lines[0].startswith("// "):
        raise ParseError("missing header comment")
    if lines[1:3] != ["OPENQASM 3.0;", 'include "stdgates.inc";']:
        raise ParseError("missing OPENQASM 3.0 header or stdgates include")
    sizes = {}
    i = 3
    while i < len(lines) and RE_DECL.match(lines[i]):
        m = RE_DECL.match(lines[i])
        kind, k, reg = m.group(1), int(m.group(2)), m.group(3)
        if (kind == "qubit") != (reg in ("x", "anc")) or reg in sizes:
            raise ParseError(f"bad declaration {lines[i]!r}")
        sizes[reg] = k
        i += 1
    n_data, n_anc = sizes.get("x", 0), sizes.get("anc", 0)
    n_bits = sizes.get("c", 0)
    if sizes.get("out") != n_data:
        raise ParseError("bit[n] out must have the size of the data register")

    def qubit(reg, idx):
        idx = int(idx)
        if idx >= (n_data if reg == "x" else n_anc):
            raise ParseError(f"{reg}[{idx}] out of range")
        return idx if reg == "x" else n_data + idx

    def gate(s):
        m = RE_GATE.match(s)
        if not m or m.group(1) not in GATES:
            return None
        op = GATES[m.group(1)]
        q = [qubit(m.group(2), m.group(3))]
        if m.group(4) is not None:
            q.append(qubit(m.group(4), m.group(5)))
        if len(q) != (2 if op in ("cnot", "cz") else 1):
            raise ParseError(f"wrong arity: {s!r}")
        return {"op": op, "q": q}

    gates, written, terminal = [], [], None
    for ln in lines[i:]:
        if terminal is not None:
            raise ParseError(f"statement after the terminal measurement: {ln!r}")
        if ln == "out = measure x;":
            terminal = [(k, k) for k in range(n_data)]
            continue
        m = RE_ANNOT.match(ln)
        if m:
            gates.append({"op": m.group(1), "q": [qubit(m.group(2), m.group(3))]})
            continue
        m = RE_MEASURE.match(ln)
        if m:
            c = int(m.group(1))
            if c >= n_bits:
                raise ParseError(f"c[{c}] out of range")
            gates.append({"op": "measure", "q": [qubit(m.group(2), m.group(3))], "c": c})
            written.append(c)
            continue
        m = RE_IF.match(ln)
        if m:
            c = int(m.group(1))
            if c not in written:
                raise ParseError(f"c[{c}] read before it is measured: {ln!r}")
            g = gate(m.group(2))
            if g is None:
                raise ParseError(f"if-body is not one gate: {ln!r}")
            gates.append({**g, "if": c})
            continue
        g = gate(ln)
        if g is None:
            raise ParseError(f"unexpected line: {ln!r}")
        gates.append(g)
    if terminal is None:
        raise ParseError("no terminal measurement `out = measure x;`")
    if sorted(written) != list(range(n_bits)):
        raise ParseError("classical bits must be 0..m-1, each written once")
    return {"n_data": n_data, "n_anc": n_anc, "gates": gates}, terminal
