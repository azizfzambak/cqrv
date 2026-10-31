"""Re-parser for the OpenQASM 3 emitted by `cqr emit --format qasm` (report §5.3, §8.4.3;
Stage 8a, reviewer decision 6).

Reads the program back into the IR JSON format of `cqr synthesize --json`
(`{n_data, n_anc, gates: [{op, q, c?, if?}]}`, data qubits `x[i] -> i`, ancillae
`anc[i] -> n_data + i`) and the terminal measurement. Accepts exactly the subset the emitter
writes (declarations `qubit[n] x; qubit[a] anc; bit[m] c; bit[n] out;`, stdgates names,
`c[j] = measure q;`, `if (c[j]) { g; }`, `out = measure x;`, `// cqrv: alloc|free q`); any other
line is an error. Stage 17b (PHASE2_SPEC.md §A.1): `p(2*pi*a/N) q;` and `cp(2*pi*a/N) c, t;`
with `a` an integer (in parentheses when negative) and `N` a power of two give
`{"op":"p"|"cp", "q": …, "a": a, "k": log2 N}`, exactly the Lean IR JSON; an argument on any
other gate, a missing argument on `p` / `cp`, or an `N` that is not a power of two is an error.

Usage as a module: `parse(text) -> (circuit_dict, terminal)`; `terminal` is the list of
`(qubit, out index)` pairs of `out = measure x;`.
"""

import re

GATES = {"h": "h", "s": "s", "sdg": "sdg", "t": "t", "tdg": "tdg", "x": "x", "z": "z",
         "cx": "cnot", "cz": "cz", "p": "p", "cp": "cp"}
TWO_QUBIT = ("cnot", "cz", "cp")
QUBIT = r"(x|anc)\[(\d+)\]"
RE_DECL = re.compile(r"^(qubit|bit)\[(\d+)\] (x|anc|c|out);$")
# Stage 17b: the optional angle `(2*pi*a/N)` of `p` / `cp`, `a` an integer, `(-a)` when negative
RE_GATE = re.compile(r"^(\w+)(?:\(2\*pi\*(-?\d+|\(-\d+\))/(\d+)\))? " + QUBIT +
                     r"(?:, " + QUBIT + r")?;$")
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
        q = [qubit(m.group(4), m.group(5))]
        if m.group(6) is not None:
            q.append(qubit(m.group(6), m.group(7)))
        if len(q) != (2 if op in TWO_QUBIT else 1):
            raise ParseError(f"wrong arity: {s!r}")
        g = {"op": op, "q": q}
        if (m.group(2) is not None) != (op in ("p", "cp")):
            raise ParseError(f"angle argument on the wrong gate: {s!r}")
        if m.group(2) is not None:
            a, n = int(m.group(2).strip("()")), int(m.group(3))
            if n < 1 or n & (n - 1):
                raise ParseError(f"the denominator {n} is not a power of two: {s!r}")
            g.update(a=a, k=n.bit_length() - 1)
        return g

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
