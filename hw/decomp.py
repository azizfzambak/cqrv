"""Our basis translation of the CQRV IR — Stage 25a U1 (PHASE2_SPEC §C.2; report §5.3).

Untrusted tool, with every entry checked numerically. The decomposition table maps each IR gate
(`h s sdg t tdg x z p cnot cz cp`) and the routing `swap` to a sequence of basis gates of the
target — `rz` with an exact angle, `sx`, `x`, and the two-qubit basis gate `cz` (FakeTorino) or
`cx` (FakeWashingtonV2) — **exact up to one global phase per entry**, which the entry records: the product of the basis
matrices equals e^{2πi·phase} times the IR gate's matrix.
Angles and phases are exact fractions of a full turn: `rz(f)` means `rz(2π f)`, and the phase
`e^{2πi f}`. `check_table(basis)` verifies, for every entry and (for `p` / `cp`) several `a / 2^k`,
that the product of the basis matrices equals the IR gate's matrix times the recorded phase, to
1e-12. Stage 26 proves the entries in Lean (`decomp_sound`).

`translate(circ, basis)` returns the translated circuit as a flat list of basis gates — dicts
`{op, q, angle?, c?, if?, ir, entry, pos}` where `ir` is the index of the IR gate the basis gate
came from, `entry` its table entry and `pos` its position in that entry (the provenance) — and
`to_qiskit(gates, n, n_bits)` builds the Qiskit circuit (a conditioned IR gate becomes one
`if_test` block holding its basis sequence). Nothing here touches the network.
"""

import cmath
import math
from fractions import Fraction

import numpy as np

HALF = Fraction(1, 2)
QUARTER = Fraction(1, 4)
EIGHTH = Fraction(1, 8)
SIXTEENTH = Fraction(1, 16)

# --- the matrices (for the numerical check only)

def rz_mat(f):
    th = 2 * math.pi * float(f)
    return np.diag([cmath.exp(-1j * th / 2), cmath.exp(1j * th / 2)])


SX = np.array([[1 + 1j, 1 - 1j], [1 - 1j, 1 + 1j]]) / 2
X = np.array([[0, 1], [1, 0]], dtype=complex)
H = np.array([[1, 1], [1, -1]]) / math.sqrt(2)
CZ = np.diag([1, 1, 1, -1]).astype(complex)
# qubit order in 2-qubit matrices: (q0, q1) with q0 the most significant index bit (control first)
CX = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex)
SWAP = np.array([[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]], dtype=complex)


def p_mat(f):
    return np.diag([1, cmath.exp(2j * math.pi * float(f))])


def cp_mat(f):
    return np.diag([1, 1, 1, cmath.exp(2j * math.pi * float(f))])


def ir_matrix(op, f=None):
    return {"h": H, "s": p_mat(QUARTER), "sdg": p_mat(-QUARTER), "t": p_mat(EIGHTH), "tdg": p_mat(-EIGHTH),
            "x": X, "z": p_mat(HALF), "cnot": CX, "cz": CZ, "swap": SWAP,
            "p": p_mat(f) if f is not None else None, "cp": cp_mat(f) if f is not None else None}[op]


# --- the table: each entry is (gates, phase); a gate is (name, roles, angle) with roles a tuple
#     of 0 (the gate's first qubit / control) and 1 (its second qubit / target)

def rz(role, f):
    return ("rz", (role,), Fraction(f))


def one(name, role):
    return (name, (role,), None)


def two(basis, c, t):
    return (basis, (c, t), None)


H_SEQ = [rz(0, QUARTER), one("sx", 0), rz(0, QUARTER)]   # h = e^{-iπ/4}·(rz(π/2) sx rz(π/2)) — checked
H_PHASE = Fraction(-1, 8)                               # recorded phase e^{2πi·(-1/8)} = e^{-iπ/4}


def shift(seq, role):
    """A one-qubit sequence written for role 0, moved to `role`."""
    return [(n, (role,), f) for (n, _, f) in seq]


def table(basis):
    """The entries of the table for `basis` ∈ {cz, cx} as `name -> (gates, phase)`; `p` and `cp`
    are given by `p_entry(f)` / `cp_entry(basis, f)` because they depend on the angle."""
    cnot = [two("cx", 0, 1)] if basis == "cx" else shift(H_SEQ, 1) + [two("cz", 0, 1)] + shift(H_SEQ, 1)
    cnot_phase = Fraction(0) if basis == "cx" else 2 * H_PHASE
    czg = [two("cz", 0, 1)] if basis == "cz" else shift(H_SEQ, 1) + [two("cx", 0, 1)] + shift(H_SEQ, 1)
    cz_phase = Fraction(0) if basis == "cz" else 2 * H_PHASE
    swap = cnot + [(n, tuple(1 - r for r in roles), f) for (n, roles, f) in cnot] + cnot
    return {
        "h": (H_SEQ, H_PHASE),
        "s": ([rz(0, QUARTER)], -EIGHTH),         # rz(φ) = e^{-iφ/2} p(φ): φ = π/2 → phase −1/8 turn
        "sdg": ([rz(0, -QUARTER)], EIGHTH),
        "t": ([rz(0, EIGHTH)], -SIXTEENTH),
        "tdg": ([rz(0, -EIGHTH)], SIXTEENTH),
        "z": ([rz(0, HALF)], -QUARTER),
        "x": ([one("x", 0)], Fraction(0)),
        "cnot": (cnot, cnot_phase),
        "cz": (czg, cz_phase),
        "swap": (swap, 3 * cnot_phase),
    }


def p_entry(f):
    """`p a k` = diag(1, e^{2πi f}), f = a / 2^k: `rz(2π f)` = e^{-2πi f/2} · p, so the recorded phase
    (basis product = phase · IR) is −f/2."""
    f = Fraction(f)
    return [rz(0, f)], -f / 2


def cp_entry(basis, f):
    """`cp a k` by the five-gate decomposition `p a (k+1) c; p a (k+1) t; cnot; p (−a) (k+1) t; cnot`
    (CQRV `Circuit.decomposeCp`), each piece by its entry; the phase is the sum of the pieces'."""
    f = Fraction(f)
    g = f / 2
    cnot, cnot_phase = table(basis)["cnot"]
    gates = [rz(0, g), rz(1, g)] + cnot + [rz(1, -g)] + cnot
    phase = -g / 2 - g / 2 + cnot_phase + g / 2 + cnot_phase
    return gates, phase


def turn_of(g):
    """The angle fraction of an IR `p` / `cp` gate: a / 2^k."""
    return Fraction(int(g["a"]), 2 ** int(g["k"]))


# --- the numerical check

def _kron_on(mat, roles, n):
    """`mat` on the qubits `roles` of an n-qubit system (qubit 0 = most significant index bit)."""
    if n == 1:
        return mat
    if len(roles) == 1:
        return np.kron(mat, np.eye(2)) if roles[0] == 0 else np.kron(np.eye(2), mat)
    if roles == (0, 1):
        return mat
    # two-qubit gate with swapped roles: conjugate by SWAP
    return SWAP @ mat @ SWAP


def seq_matrix(gates, n):
    m = np.eye(2 ** n, dtype=complex)
    for name, roles, f in gates:
        g = {"rz": rz_mat(f) if f is not None else None, "sx": SX, "x": X, "cz": CZ, "cx": CX}[name]
        m = _kron_on(g, roles, n) @ m
    return m


def check_entry(op, gates, phase, f=None):
    n = 2 if op in ("cnot", "cz", "cp", "swap") else 1
    want = cmath.exp(2j * math.pi * float(phase)) * ir_matrix(op, f)
    return float(np.max(np.abs(seq_matrix(gates, n) - want)))


def check_table(basis, tol=1e-12):
    """Every entry (and `p` / `cp` at several a / 2^k) against its IR matrix: the maximum
    deviation, which must be below `tol`. Returns (ok, max deviation, worst entry)."""
    worst, worst_name = 0.0, ""
    for name, (gates, phase) in table(basis).items():
        d = check_entry(name, gates, phase)
        if d > worst:
            worst, worst_name = d, name
    for a, k in ((1, 1), (1, 2), (-1, 3), (3, 3), (5, 4), (-7, 5), (1, 8), (0, 1)):
        f = Fraction(a, 2 ** k)
        d = check_entry("p", *p_entry(f), f=f)
        if d > worst:
            worst, worst_name = d, f"p {a} {k}"
        d = check_entry("cp", *cp_entry(basis, f), f=f)
        if d > worst:
            worst, worst_name = d, f"cp {a} {k}"
    return worst < tol, worst, worst_name


# --- translation

def frac_str(f):
    f = Fraction(f)
    return f"{f.numerator}/{f.denominator}" if f.denominator != 1 else str(f.numerator)


def entry_for(basis, g):
    op = g["op"]
    if op == "p":
        return f"p {g['a']} {g['k']}", p_entry(turn_of(g))
    if op == "cp":
        return f"cp {g['a']} {g['k']}", cp_entry(basis, turn_of(g))
    return op, table(basis)[op]


def translate(circ, basis):
    """The flat basis-gate list of an IR circuit dict, with provenance; `alloc` / `free` vanish,
    `measure` stays, a conditioned gate's basis gates all carry its `if` bit."""
    out = []
    for k, g in enumerate(circ["gates"]):
        op = g["op"]
        if op in ("alloc", "free"):
            continue
        if op == "measure":
            out.append({"op": "measure", "q": [g["q"][0]], "c": g["c"], "ir": k, "entry": "measure", "pos": 0})
            continue
        name, (gates, _phase) = entry_for(basis, g)
        for j, (bname, roles, f) in enumerate(gates):
            bg = {"op": bname, "q": [g["q"][r] for r in roles], "ir": k, "entry": name, "pos": j}
            if f is not None:
                bg["angle"] = frac_str(f)
            if "if" in g:
                bg["if"] = g["if"]
            out.append(bg)
    return out


def phase_of(circ, basis):
    """The total recorded global phase of the translation, as a fraction of a turn mod 1."""
    tot = Fraction(0)
    for g in circ["gates"]:
        if g["op"] in ("alloc", "free", "measure"):
            continue
        tot += entry_for(basis, g)[1][1]
    return tot % 1


def apply_basis_gate(qc, bg, qmap=None):
    """One basis gate on a Qiskit circuit; `qmap` maps the gate's qubit indices (default identity)."""
    q = [qmap[i] if qmap is not None else i for i in bg["q"]]
    op = bg["op"]
    if op == "rz":
        qc.rz(2 * math.pi * float(Fraction(bg["angle"])), q[0])
    elif op == "sx":
        qc.sx(q[0])
    elif op == "x":
        qc.x(q[0])
    elif op == "cz":
        qc.cz(q[0], q[1])
    elif op == "cx":
        qc.cx(q[0], q[1])
    elif op == "swap":
        qc.swap(q[0], q[1])
    elif op == "measure":
        qc.measure(q[0], bg["c"])
    else:
        raise ValueError(op)


def to_qiskit(gates, n, n_bits, qmap=None):
    """The Qiskit circuit of a basis-gate list on `n` qubits and `n_bits` classical bits; consecutive
    gates with the same `if` bit and the same `ir` index form one `if_test` block."""
    from qiskit import ClassicalRegister, QuantumCircuit, QuantumRegister
    qc = QuantumCircuit(QuantumRegister(n, "q"), ClassicalRegister(max(1, n_bits), "c"))
    i = 0
    while i < len(gates):
        bg = gates[i]
        if "if" in bg:
            j = i
            while j < len(gates) and gates[j].get("if") == bg["if"] and gates[j].get("ir") == bg.get("ir"):
                j += 1
            with qc.if_test((qc.clbits[bg["if"]], 1)):
                for h in gates[i:j]:
                    apply_basis_gate(qc, h, qmap)
            i = j
        else:
            apply_basis_gate(qc, bg, qmap)
            i += 1
    return qc


def n_bits_of(circ):
    bits = [g["c"] for g in circ["gates"] if g["op"] == "measure"] + [g["if"] for g in circ["gates"] if "if" in g]
    return (max(bits) + 1) if bits else 1


SAMPLE_ANGLES = [(1, 1), (1, 2), (-1, 3), (3, 3), (5, 4), (-7, 5), (1, 8), (0, 1)]


def gate_json(name, roles, f):
    g = {"op": name, "q": list(roles)}
    if f is not None:
        g["angle"] = frac_str(f)
    return g


def entry_json(gates, phase):
    return {"gates": [gate_json(*g) for g in gates], "phase": frac_str(phase)}


def table_json(basis):
    """The table as canonical JSON, the format `cqr hw table --basis` prints (Stage 26a): the
    fixed entries on roles 0 / 1, `p a k` and `cp a k` at SAMPLE_ANGLES, and `swap`."""
    entries = {}
    for name, (gates, phase) in table(basis).items():
        if name != "swap":
            entries[name] = entry_json(gates, phase)
    for a, k in SAMPLE_ANGLES:
        f = Fraction(a, 2 ** k)
        entries[f"p {a} {k}"] = entry_json(*p_entry(f))
        entries[f"cp {a} {k}"] = entry_json(*cp_entry(basis, f))
    entries["swap"] = entry_json(*table(basis)["swap"])
    return {"basis": basis, "entries": entries}


if __name__ == "__main__":
    import json
    import sys as _sys
    if len(_sys.argv) == 3 and _sys.argv[1] == "--json":
        print(json.dumps(table_json(_sys.argv[2]), sort_keys=True, separators=(",", ":")))
    else:
        for b in ("cz", "cx"):
            print(b, check_table(b))
