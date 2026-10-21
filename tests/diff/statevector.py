"""Minimal statevector simulator for the differential harness (CLAUDE.md rule 9).

Stage 0 placeholder (report §9.5.1, §9.5.3): applies H, X and CNOT to an n-qubit pure
state, n <= 12. Qubit 0 is the most significant bit of the basis index. The executor for
the CQRV gate-level IR (measurement, TempLogicalAND, MBU) arrives in Stage 5.

Usage (from the repository root):  python -I tests/diff/statevector.py --selftest
"""

import sys

import numpy as np

MAX_QUBITS = 12

H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)


class StateVector:
    def __init__(self, n):
        if not 1 <= n <= MAX_QUBITS:
            raise ValueError(f"n must be in 1..{MAX_QUBITS}, got {n}")
        self.n = n
        self.amp = np.zeros(2**n, dtype=complex)
        self.amp[0] = 1.0

    def _apply_1q(self, gate, q):
        psi = self.amp.reshape((2,) * self.n)
        psi = np.moveaxis(np.tensordot(gate, psi, axes=([1], [q])), 0, q)
        self.amp = psi.reshape(-1)

    def h(self, q):
        self._apply_1q(H, q)
        return self

    def x(self, q):
        self._apply_1q(X, q)
        return self

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


def _random_state(n, rng):
    v = rng.normal(size=2**n) + 1j * rng.normal(size=2**n)
    return v / np.linalg.norm(v)


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
    # Size limit is enforced and n = 12 works.
    StateVector(MAX_QUBITS).h(MAX_QUBITS - 1)
    try:
        StateVector(MAX_QUBITS + 1)
        raise AssertionError("n > 12 accepted")
    except ValueError:
        pass
    print("statevector selftest: OK (H*H = I, X, Bell state, CNOT both directions, n <= 12)")


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        selftest()
    else:
        print(__doc__)
        sys.exit(2)
