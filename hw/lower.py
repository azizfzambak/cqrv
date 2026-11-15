"""Lower the canonical circuit JSON of the CQRV IR to a Qiskit dynamic circuit — Stage 24b
(PHASE2_SPEC §C.1 "Lowering", Track C; report §5.3, §6.2.2).

Untrusted tool. The input is `Circuit.toJson` (CQRV/Circuit/IR.lean; the JSON that `cqr
synthesize --json` prints and the certificates hash): `{n_data, n_anc, gates: [{op, q, c?, a?,
k?, if?}]}` with flat qubit indices (data qubits `0 .. n_data-1`, ancilla `i` at `n_data + i`).
The lowered circuit has `n_data + n_anc` qubits in the JSON's flat order (IR qubit `i` is Qiskit
qubit `i`) and one classical register of `n_bits` bits (IR bit `c` is clbit `c`). The mapping:

    h s sdg t tdg x z   the same gates           cnot            cx
    cz                  cz                       p a k           p(2π a / 2^k)
    cp a k              cp(2π a / 2^k)           measure q -> c  measure(q, c)
    if: k  (ifBit k g)  with qc.if_test((clbit k, 1)): g
    alloc, free         nothing (bookkeeping; the harness checks them)

The phase convention is the IR's: `p a k` multiplies |1> by exp(2πi a / 2^k) — Qiskit's phase
gate with θ = 2π a / 2^k (`check_phase_convention` verifies it numerically on Aer).

Note on bit order: Qiskit's statevector index has qubit 0 as its least significant bit, the
harness (tests/diff/statevector.py) has qubit 0 as the most significant bit; `to_harness_order`
converts an Aer statevector to the harness's order.

Usage: python -I hw/lower.py <circuit.json> [--qasm-out f]   (the QASM 3 export is for inspection
only; the comparison of tests/diff/hw_lower_check.py is on the circuit object). Nothing here
touches the network.
"""

import argparse
import json
import math
import sys

import numpy as np
from qiskit import ClassicalRegister, QuantumCircuit, QuantumRegister

ONE_QUBIT = {"h": "h", "s": "s", "sdg": "sdg", "t": "t", "tdg": "tdg", "x": "x", "z": "z"}


def theta(a, k):
    """The angle 2π a / 2^k of `p a k` / `cp a k`."""
    return 2.0 * math.pi * a / 2 ** k


def n_bits_of(circ):
    """The number of classical bits the circuit uses (at least one register bit)."""
    bits = [g["c"] for g in circ["gates"] if g["op"] == "measure"]
    bits += [g["if"] for g in circ["gates"] if "if" in g]
    return (max(bits) + 1) if bits else 1


def _apply(qc, g, cr):
    op, q = g["op"], g["q"]
    if op in ONE_QUBIT:
        getattr(qc, ONE_QUBIT[op])(q[0])
    elif op == "cnot":
        qc.cx(q[0], q[1])
    elif op == "cz":
        qc.cz(q[0], q[1])
    elif op == "p":
        qc.p(theta(g["a"], g["k"]), q[0])
    elif op == "cp":
        qc.cp(theta(g["a"], g["k"]), q[0], q[1])
    elif op == "measure":
        qc.measure(q[0], cr[g["c"]])
    elif op in ("alloc", "free"):
        pass
    else:
        raise ValueError(f"lower: unknown op {op!r}")


def lower(circ, x_prefix=(), hooks=None):
    """The Qiskit circuit of an IR circuit dict. `x_prefix`: data qubits to start in |1> (X gates
    prepended, for the basis-input sweep). `hooks`: an optional callable `hooks(qc, k, g)` run
    before gate `k` (the check inserts Aer save instructions through it)."""
    n = circ["n_data"] + circ["n_anc"]
    qr, cr = QuantumRegister(n, "q"), ClassicalRegister(n_bits_of(circ), "c")
    qc = QuantumCircuit(qr, cr)
    for i in x_prefix:
        qc.x(i)
    for k, g in enumerate(circ["gates"]):
        if hooks is not None:
            hooks(qc, k, g)
        if "if" in g:
            inner = {kk: v for kk, v in g.items() if kk != "if"}
            if inner["op"] == "measure":
                raise ValueError("lower: a conditioned measurement is not in the IR")
            with qc.if_test((cr[g["if"]], 1)):
                _apply(qc, inner, cr)
        else:
            _apply(qc, g, cr)
    return qc


def to_harness_order(vec, n):
    """An Aer statevector (qubit 0 = least significant index bit) in the harness's order
    (qubit 0 = most significant index bit)."""
    v = np.asarray(vec, dtype=complex).reshape([2] * n)
    return v.transpose(list(range(n))[::-1]).reshape(-1)


def check_phase_convention():
    """`p 1 3` on |1> gives e^{iπ/4}; `cp 1 2` on |11> gives i; both against Aer, exactly."""
    from qiskit_aer import AerSimulator
    sim = AerSimulator(method="statevector")
    qc = lower({"n_data": 1, "n_anc": 0, "gates": [{"op": "x", "q": [0]}, {"op": "p", "q": [0], "a": 1, "k": 3}]})
    qc.save_statevector(label="s")
    v = np.asarray(sim.run(qc, shots=1).result().data(0)["s"])
    want = np.array([0, np.exp(1j * np.pi / 4)])
    qc2 = lower({"n_data": 2, "n_anc": 0, "gates": [{"op": "x", "q": [0]}, {"op": "x", "q": [1]},
                                                     {"op": "cp", "q": [0, 1], "a": 1, "k": 2}]})
    qc2.save_statevector(label="s")
    v2 = to_harness_order(sim.run(qc2, shots=1).result().data(0)["s"], 2)
    want2 = np.array([0, 0, 0, 1j])
    return np.linalg.norm(v - want) < 1e-12 and np.linalg.norm(v2 - want2) < 1e-12


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("circuit", help="a canonical circuit JSON file ({n_data, n_anc, gates}) or a "
                                    "`cqr synthesize --json` output (its `circuit` field is used)")
    ap.add_argument("--qasm-out", help="write the OpenQASM 3 text of the lowered circuit (inspection only)")
    a = ap.parse_args(argv)
    obj = json.load(open(a.circuit, encoding="utf-8"))
    circ = obj["circuit"] if "circuit" in obj else obj
    qc = lower(circ)
    print(f"{a.circuit}: {qc.num_qubits} qubits, {qc.num_clbits} clbits, {len(qc.data)} instructions, "
          f"depth {qc.depth()}")
    if a.qasm_out:
        from qiskit import qasm3
        with open(a.qasm_out, "w", encoding="utf-8", newline="\n") as f:
            f.write(qasm3.dumps(qc))
        print(f"wrote {a.qasm_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
