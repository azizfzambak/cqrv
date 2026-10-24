"""Statevector simulator for the differential harness (CLAUDE.md rule 9).

Report §6.1.4, §6.2.2, §6.2.4, §9.5.1. Pure states on at most MAX_QUBITS qubits; qubit 0 is
the most significant bit of the basis index. Stage 5 adds the executor for the CQRV gate-level
IR as exported by `cqr synthesize --json` (flat format: data qubits 0..n_data, ancillae after):

  * gates H, S, S†, T, T†, X, Z, CNOT, CZ;
  * `measure q -> c` in the computational basis: **both outcomes are enumerated** (a branch
    tree); branches of probability < PROB_EPS are dropped;
  * `if c: g` applies the Clifford gate g in the branches where bit c is 1;
  * `alloc q` / `free q` assert, in every branch, that q is |0> (restoration check).

Usage (from the repository root):  python -I tests/diff/statevector.py --selftest
"""

import sys

import numpy as np

MAX_QUBITS = 20
PROB_EPS = 1e-12
ZERO_EPS = 1e-10

H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)
S = np.diag([1, 1j])
SDG = np.diag([1, -1j])
T = np.diag([1, np.exp(1j * np.pi / 4)])
TDG = np.diag([1, np.exp(-1j * np.pi / 4)])
ONE_QUBIT = {"h": H, "x": X, "z": Z, "s": S, "sdg": SDG, "t": T, "tdg": TDG}


class StateVector:
    def __init__(self, n):
        if not 1 <= n <= MAX_QUBITS:
            raise ValueError(f"n must be in 1..{MAX_QUBITS}, got {n}")
        self.n = n
        self.amp = np.zeros(2**n, dtype=complex)
        self.amp[0] = 1.0

    def copy(self):
        sv = StateVector.__new__(StateVector)
        sv.n, sv.amp = self.n, self.amp.copy()
        return sv

    def _apply_1q(self, gate, q):
        psi = self.amp.reshape((2,) * self.n)
        psi = np.moveaxis(np.tensordot(gate, psi, axes=([1], [q])), 0, q)
        self.amp = psi.reshape(-1)

    def gate1(self, name, q):
        self._apply_1q(ONE_QUBIT[name], q)
        return self

    def h(self, q):
        return self.gate1("h", q)

    def x(self, q):
        return self.gate1("x", q)

    def cnot(self, c, t):
        if c == t:
            raise ValueError("control and target must differ")
        psi = self.amp.reshape((2,) * self.n).copy()
        idx = [slice(None)] * self.n
        idx[c] = 1
        sub = psi[tuple(idx)]  # control = 1 subspace; target axis shifts if t > c
        sub[:] = np.flip(sub, axis=t if t < c else t - 1)
        psi[tuple(idx)] = sub
        self.amp = psi.reshape(-1)
        return self

    def cz(self, a, b):
        if a == b:
            raise ValueError("CZ qubits must differ")
        psi = self.amp.reshape((2,) * self.n).copy()
        idx = [slice(None)] * self.n
        idx[a] = 1
        idx[b] = 1
        psi[tuple(idx)] *= -1
        self.amp = psi.reshape(-1)
        return self

    def prob_one(self, q):
        """Squared norm of the q = 1 part (the state is not renormalized)."""
        psi = self.amp.reshape((2,) * self.n)
        return float(np.sum(np.abs(np.take(psi, 1, axis=q)) ** 2))

    def project(self, q, bit):
        """Unnormalized projection onto q = bit."""
        psi = self.amp.reshape((2,) * self.n).copy()
        idx = [slice(None)] * self.n
        idx[q] = 1 - bit
        psi[tuple(idx)] = 0
        self.amp = psi.reshape(-1)
        return self

    def norm2(self):
        return float(np.vdot(self.amp, self.amp).real)


def apply_unitary(sv, g):
    op, q = g["op"], g["q"]
    if op in ONE_QUBIT:
        sv.gate1(op, q[0])
    elif op == "cnot":
        sv.cnot(q[0], q[1])
    elif op == "cz":
        sv.cz(q[0], q[1])
    else:
        raise ValueError(f"not a unitary gate: {g}")


class RestorationError(AssertionError):
    pass


def run_ir(circ, data_state):
    """Execute an IR circuit (dict from `cqr synthesize --json`) on `data_state` (a vector on
    the n_data data qubits) tensored with |0...0> on the ancillae. Returns the list of
    branches `(bits, state)` with unnormalized final states, one per sequence of measurement
    outcomes of non-negligible probability."""
    n_data, n_anc = circ["n_data"], circ["n_anc"]
    n = n_data + n_anc
    init = StateVector(n)
    full = np.zeros(2**n, dtype=complex)
    full[:: 2**n_anc] = data_state  # data qubits are the most significant ones
    init.amp = full
    branches = [({}, init)]
    for k, g in enumerate(circ["gates"]):
        op = g["op"]
        nxt = []
        for bits, sv in branches:
            if op in ("alloc", "free"):
                p1 = sv.prob_one(g["q"][0])
                if p1 > ZERO_EPS * max(sv.norm2(), PROB_EPS):
                    raise RestorationError(
                        f"gate {k} ({op} q{g['q'][0]}): qubit is not |0> in branch {bits} "
                        f"(P(1) = {p1 / sv.norm2():.3g})")
                nxt.append((bits, sv))
            elif op == "measure":
                for b in (0, 1):
                    s2 = sv.copy().project(g["q"][0], b)
                    if s2.norm2() > PROB_EPS:
                        nxt.append(({**bits, g["c"]: b}, s2))
            elif "if" in g:
                if g["if"] not in bits:
                    raise ValueError(f"gate {k}: bit c{g['if']} read before measurement")
                if bits[g["if"]] == 1:
                    apply_unitary(sv, g)
                nxt.append((bits, sv))
            else:
                apply_unitary(sv, g)
                nxt.append((bits, sv))
        branches = nxt
    return branches


def _embed(circ, data_state):
    n_data, n_anc = circ["n_data"], circ["n_anc"]
    sv = StateVector(n_data + n_anc)
    full = np.zeros(2 ** sv.n, dtype=complex)
    full[:: 2**n_anc] = data_state  # data qubits are the most significant ones
    sv.amp = full
    return sv


def _step(k, g, bits, sv):
    """One non-measurement gate of `run_ir` (same checks), in place."""
    op = g["op"]
    if op in ("alloc", "free"):
        p1 = sv.prob_one(g["q"][0])
        if p1 > ZERO_EPS * max(sv.norm2(), PROB_EPS):
            raise RestorationError(
                f"gate {k} ({op} q{g['q'][0]}): qubit is not |0> in branch {bits} "
                f"(P(1) = {p1 / sv.norm2():.3g})")
    elif "if" in g:
        if g["if"] not in bits:
            raise ValueError(f"gate {k}: bit c{g['if']} read before measurement")
        if bits[g["if"]] == 1:
            apply_unitary(sv, g)
    else:
        apply_unitary(sv, g)


def iter_ir_branches(circ, data_state):
    """Stage 5b: the branches of `run_ir`, enumerated depth first (a generator; memory is one
    state per pending measurement instead of one per branch). Same checks as `run_ir`."""
    gates = circ["gates"]

    def go(k, bits, sv):
        while k < len(gates):
            g = gates[k]
            if g["op"] == "measure":
                for b in (0, 1):
                    s2 = sv.copy().project(g["q"][0], b)
                    if s2.norm2() > PROB_EPS:
                        yield from go(k + 1, {**bits, g["c"]: b}, s2)
                return
            _step(k, g, bits, sv)
            k += 1
        yield bits, sv

    yield from go(0, {}, _embed(circ, data_state))


def run_ir_sampled(circ, data_state, rng):
    """Stage 5b: one branch of `run_ir`, each measurement outcome drawn with its Born
    probability and the state renormalized. Returns `(bits, state)` (norm 1)."""
    sv, bits = _embed(circ, data_state), {}
    sv.amp = sv.amp / np.sqrt(sv.norm2())
    for k, g in enumerate(circ["gates"]):
        if g["op"] == "measure":
            p1 = sv.prob_one(g["q"][0])
            b = int(rng.random() < p1)
            sv.project(g["q"][0], b)
            sv.amp = sv.amp / np.sqrt(sv.norm2())
            bits = {**bits, g["c"]: b}
        else:
            _step(k, g, bits, sv)
    return bits, sv


def check_phase_oracle(circ, pred, rng, trials=1):
    """Report §6.2.4: for a random complex superposition |psi> on the data register, every
    branch must end in U_P|psi> (x) |0...0>_anc up to a global phase of that branch, with
    U_P|x> = (-1)^P(x)|x>. `pred(x)` takes the data index (qubit 0 = MSB = input bit 0).
    Returns the number of branches checked; raises AssertionError on failure."""
    n_data, n_anc = circ["n_data"], circ["n_anc"]
    signs = np.array([-1.0 if pred(x) else 1.0 for x in range(2**n_data)])
    checked = 0
    for _ in range(trials):
        psi = _random_state(n_data, rng)
        want = np.zeros(2 ** (n_data + n_anc), dtype=complex)
        want[:: 2**n_anc] = signs * psi
        total = 0.0
        for bits, sv in run_ir(circ, psi):
            nrm = sv.norm2()
            total += nrm
            overlap = abs(np.vdot(want, sv.amp)) / np.sqrt(nrm)
            if overlap < 1 - 1e-9:
                raise AssertionError(
                    f"branch {bits}: |<U_P psi (x) 0|out>| = {overlap:.12f} != 1 "
                    f"(wrong phase or ancilla not factored out)")
            checked += 1
        if abs(total - 1) > 1e-9:
            raise AssertionError(f"branch probabilities sum to {total}")
    return checked


def _random_state(n, rng):
    v = rng.normal(size=2**n) + 1j * rng.normal(size=2**n)
    return v / np.linalg.norm(v)


# --- the §6.2.2 listing, independently of the Lean synthesizer (qubits a, b, t) ------------

def temp_and(a, b, t):
    seq = [("h", t), ("t", t), ("cnot", a, t), ("cnot", b, t), ("cnot", t, a), ("cnot", t, b),
           ("tdg", a), ("tdg", b), ("t", t), ("cnot", t, a), ("cnot", t, b), ("h", t), ("s", t)]
    return [{"op": g[0], "q": list(g[1:])} for g in seq]


def uncompute_temp_and(a, b, t, m, reset=True):
    gs = [{"op": "h", "q": [t]}, {"op": "measure", "q": [t], "c": m},
          {"op": "cz", "q": [a, b], "if": m}]
    return gs + ([{"op": "x", "q": [t], "if": m}] if reset else [])


def selftest():
    rng = np.random.default_rng(0)
    # H·H = I on every qubit of a random 4-qubit state.
    for q in range(4):
        sv = StateVector(4)
        sv.amp = _random_state(4, rng)
        before = sv.amp.copy()
        sv.h(q).h(q)
        assert np.allclose(sv.amp, before), f"H*H != I on qubit {q}"
    # X flips |000> to |010> (qubit 1 set; qubit 0 is the MSB).
    sv = StateVector(3).x(1)
    assert np.isclose(abs(sv.amp[0b010]), 1.0), "X on qubit 1"
    # Bell state: H(0); CNOT(0,1) -> (|00> + |11>)/sqrt 2.
    sv = StateVector(2).h(0).cnot(0, 1)
    bell = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)
    assert np.allclose(sv.amp, bell), f"Bell state wrong: {sv.amp}"
    # CNOT with control below target on 3 qubits: |100> -> CNOT(0,2) -> |101>.
    sv = StateVector(3).x(0).cnot(0, 2)
    assert np.isclose(abs(sv.amp[0b101]), 1.0), "CNOT(0,2)"
    # CNOT with control above target: |001> -> CNOT(2,0) -> |101>.
    sv = StateVector(3).x(2).cnot(2, 0)
    assert np.isclose(abs(sv.amp[0b101]), 1.0), "CNOT(2,0)"
    # S·S = Z, T·T = S, T·T† = I, CZ = H_b CNOT H_b.
    for a, b in ((S @ S, Z), (T @ T, S), (T @ TDG, np.eye(2))):
        assert np.allclose(a, b), "phase gate identities"
    sv1, sv2 = StateVector(2), StateVector(2)
    sv1.amp = sv2.amp = _random_state(2, rng)
    sv1.cz(0, 1)
    sv2.h(1).cnot(0, 1).h(1)
    assert np.allclose(sv1.amp, sv2.amp), "CZ != (I x H) CNOT (I x H)"
    # Size limit is enforced and n = MAX_QUBITS works.
    StateVector(MAX_QUBITS).h(MAX_QUBITS - 1)
    try:
        StateVector(MAX_QUBITS + 1)
        raise AssertionError(f"n > {MAX_QUBITS} accepted")
    except ValueError:
        pass
    # §6.2.2 TempLogicalAND, gate for gate: |a, b, 0> -> |a, b, a AND b> exactly (no phase).
    for a in (0, 1):
        for b in (0, 1):
            data = np.zeros(4, dtype=complex)
            data[2 * a + b] = 1
            circ = {"n_data": 2, "n_anc": 1,
                    "gates": [{"op": "alloc", "q": [2]}] + temp_and(0, 1, 2)}
            [(_, sv)] = run_ir(circ, data)
            want = np.zeros(8, dtype=complex)
            want[4 * a + 2 * b + (a & b)] = 1
            assert np.allclose(sv.amp, want), f"TempLogicalAND on |{a}{b}0>: {sv.amp}"
    # Compute; Z on the target; MBU uncompute (with the reset fix) = CZ(a, b) on superpositions.
    gates = ([{"op": "alloc", "q": [2]}] + temp_and(0, 1, 2) + [{"op": "z", "q": [2]}]
             + uncompute_temp_and(0, 1, 2, 0) + [{"op": "free", "q": [2]}])
    n = check_phase_oracle({"n_data": 2, "n_anc": 1, "gates": gates},
                           lambda x: x == 0b11, rng, trials=3)
    assert n == 6, n
    # Erratum (DECISIONS.md, Stage 5): the listing's uncompute *without* `if m: X t` leaves the
    # target in |1> in the m = 1 branch; `free` must catch it.
    gates_listed = ([{"op": "alloc", "q": [2]}] + temp_and(0, 1, 2) + [{"op": "z", "q": [2]}]
                    + uncompute_temp_and(0, 1, 2, 0, reset=False) + [{"op": "free", "q": [2]}])
    try:
        check_phase_oracle({"n_data": 2, "n_anc": 1, "gates": gates_listed},
                           lambda x: x == 0b11, rng)
        raise AssertionError("uncompute without reset was accepted")
    except RestorationError:
        pass
    # A wrong phase is caught on a superposition (and would not be on a basis state).
    try:
        check_phase_oracle({"n_data": 2, "n_anc": 1, "gates": [{"op": "z", "q": [0]}]},
                           lambda x: x == 0b11, rng)
        raise AssertionError("wrong oracle accepted")
    except AssertionError as e:
        assert "branch" in str(e), e
    print("statevector selftest: OK (H*H = I, X, Bell, CNOT both directions, phase gates, CZ, "
          f"n <= {MAX_QUBITS}; TempLogicalAND exact; compute+Z+MBU = CZ in every branch; "
          "MBU without reset caught; wrong phase caught)")


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        selftest()
    else:
        print(__doc__)
        sys.exit(2)
