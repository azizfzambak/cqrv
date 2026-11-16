"""Revision R12 (REVIEW_RESPONSE_1 §4; docs/tasks/REVC_TASK.md) — the combinational benchmarks cmp4, addchk3,
wt8_3: reference semantics, the statevector harness, and the re-certification check of the committed
certificates (CLAUDE.md rule 9; report §8.5.3).

  python -I tests/diff/r12_predicates.py --cqr <cqr> [--sample K] [--exhaustive E] [--only name] [--seed S]
                                         [--no-certify]

The references are integer arithmetic on the input layout of each file header (bit 0 = LSB), never the
DSL text or the synthesizer's network:
  * cmp4:    x - y >= 5 for 4-bit x = x[0..3], y = x[4..7]                     (n = 8, M = 66, r* = 1);
  * addchk3: x + y = z (mod 8) for 3-bit x = x[0..2], y = x[3..5], z = x[6..8]  (n = 9, M = 64, r* = 2);
  * wt8_3:   exactly three of the eight bits are set                            (n = 8, M = 56, r* = 1).
cmp4 is harness evidence only (its kernel check peaks above the 8 GB guard; DECISIONS.md 2026-11-17);
addchk3 and wt8_3 are certified (CERTIFIED), wt8_3 also as a counting certificate (COUNT_BENCH).

For each benchmark:
  (0) the DSL program against the definition on ALL 2^n inputs: `cqr check --truth-table` (the reference
      evaluator on the typed term, and the network) equals the Python reference's table; M is the number
      of ones (the test oracle; the certificate decides M by the kernel, hM_count); `cqr extract
      --solutions M` (arity, c_and); `cqr match` -> Grover with F2 |-> M;
  (1) the oracle U_P on a random complex |psi>: every measurement branch ends in U_P|psi> (x) |0...0>_anc
      up to a phase — exhaustively when the circuit has k measurements with 2^k <= 2^E (--exhaustive,
      default 8), else on K distinct sampled branches (`benchmark_diff.sampled_branches`; the
      restoration theorem makes every branch identical; Stage 12a review). Each check prints k, 2^k and
      the branches checked;
  (2) for the tree and the few:log shape: one Grover iteration = U_s U_P, and the full circuit at r*
      from |0...0>: the ancillae end in |0...0> and the success probability equals the exact rational
      1 - delta (Chebyshev form, `benchmark_diff.grover_success`) to 1e-9 — the same exhaustive / sampled
      rule;
  (3) unless --no-certify, for the CERTIFIED benchmarks: `cqr certify <file> --solutions M --report` into a
      temporary directory is `certified` (M kernel-decided, standard three axioms;
      `certify_check.check_dir`) and reproduces the committed examples/certs/<name>/ byte for byte
      (Cert.lean, .qasm, .qir; the JSON modulo the machine fields and hashes.library); for COUNT_BENCH also
      `--problem count --precision 4` against examples/certs/<name>_count/ (`certify_check.check_count_dir`).
The CI step (scripts/diff_benchmark.sh) runs K = 4; the R12 evidence run used K = 32 and E = 13
(DECISIONS.md 2026-11-17).
"""
import argparse
import json
import os
import sys
import tempfile
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402
import benchmark_diff as bd  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOL = 1e-9


def num(bits, lo, w):
    return sum(bits[lo + k] << k for k in range(w))


def cmp4_ref(b):
    return num(b, 0, 4) - num(b, 4, 4) >= 5


def addchk3_ref(b):
    return (num(b, 0, 3) + num(b, 3, 3)) % 8 == num(b, 6, 3)


def wt8_3_ref(b):
    return sum(b) == 3


# name: (n, reference, M, r*, c_and)
BENCH = {"cmp4": (8, cmp4_ref, 66, 1, 11), "addchk3": (9, addchk3_ref, 64, 2, 5), "wt8_3": (8, wt8_3_ref, 56, 1, 12)}
CERTIFIED = ("addchk3", "wt8_3")
COUNT_BENCH = "wt8_3"


def input_bits(x, n):
    return [(x >> k) & 1 for k in range(n)]


def data_bits(x, n):
    """Data-register index -> input bits (qubit 0 = MSB = input bit 0; statevector.py)."""
    return [(x >> (n - 1 - k)) & 1 for k in range(n)]


def n_measure(circ):
    return sum(1 for g in circ["gates"] if g["op"] == "measure")


def branches(circ, psi, k, exhaustive, rng):
    """(branches of `circ` on `psi`, label): every branch when 2^measurements <= 2^exhaustive (the
    probabilities must then sum to 1), else k distinct sampled branches (each renormalized)."""
    m = n_measure(circ)
    if m <= exhaustive:
        out, total = [], 0.0
        for bits, s in sv.iter_ir_branches(circ, psi):
            nrm = s.norm2()
            total += nrm
            s.amp = s.amp / np.sqrt(nrm)
            out.append((bits, s))
        assert abs(total - 1) <= TOL, f"branch probabilities sum to {total}"
        return out, f"every branch ({m} measurements, 2^{m} = {2**m} branches)"
    return list(bd.sampled_branches(circ, psi, k, rng)), f"sampled distinct branches ({m} measurements, 2^{m} branches)"


def check_state(circ, psi, want_data, k, exhaustive, rng, label):
    n_anc = circ["n_anc"]
    want = np.zeros(2 ** (circ["n_data"] + n_anc), dtype=complex)
    want[:: 2**n_anc] = want_data
    brs, how = branches(circ, psi, k, exhaustive, rng)
    for bits, s in brs:
        overlap = abs(np.vdot(want, s.amp))
        assert overlap >= 1 - TOL, f"{label}: branch {bits}: overlap {overlap:.12f} != 1"
    return f"{len(brs)} of {how}"


def check_bench(exe, name, k, exhaustive, rng):
    n, ref, M, r_want, cand = BENCH[name]
    src = os.path.join("examples", f"{name}.cqr")
    N = 2**n
    table = "".join("1" if ref(input_bits(x, n)) else "0" for x in range(N))
    assert table.count("1") == M, (name, table.count("1"), M)
    tt = bd.cqr_json(exe, "check", src, "--truth-table")
    assert tt["n"] == n and tt["evaluator"] == table and tt["network"] == table, name
    sig = bd.cqr_json(exe, "extract", src, "--solutions", str(M))
    assert (sig["arity"], sig["and_complexity"], sig["solution_count"]) == (n, cand, M), sig
    mt = bd.cqr_json(exe, "match", src, "--solutions", str(M))
    assert mt["pattern"] == "Grover" and mt["subst"]["F₂"] == M, mt
    print(f"(0) {name}: program = definition on all {N} inputs (evaluator and network); M = {M}; "
          f"extract (n = {n}, c_and = {cand}); match Grover F2 -> {M}")
    signs = np.array([-1.0 if ref(data_bits(x, n)) else 1.0 for x in range(N)])
    oracle = bd.cqr_json(exe, "synthesize", src, "--json")["circuit"]
    psi = sv._random_state(n, rng)
    how = check_state(oracle, psi, signs * psi, k, exhaustive, rng, f"{name} oracle")
    print(f"(1) {name}: oracle U_P ({oracle['n_data'] + oracle['n_anc']} qubits): {how}")
    s_exact = Fraction(M, N)
    p_exact = bd.grover_success(r_want, s_exact)
    e0 = np.zeros(N, dtype=complex)
    e0[0] = 1
    good = [x for x in range(N) if ref(data_bits(x, n))]
    for shape in ("tree", "few:log"):
        res = bd.cqr_json(exe, "synthesize", src, "--grover", "--solutions", str(M), "--shape", shape, "--json")
        assert res["r_star"] == r_want and res["iterations"] == r_want, (name, shape, res["r_star"])
        psi = sv._random_state(n, rng)
        how1 = check_state(res["iteration_circuit"], psi, bd.u_s(n) @ (signs * psi), k, exhaustive, rng,
                           f"{name} {shape} iteration")
        circ = res["circuit"]
        brs, how2 = branches(circ, e0, k, exhaustive, rng)
        for bits, s in brs:
            data = s.amp.reshape(N, 2 ** circ["n_anc"])
            anc_rest = float(np.sum(np.abs(data[:, 1:]) ** 2))
            assert anc_rest < TOL, f"{name} {shape}: branch {bits}: ancilla not |0...0> (weight {anc_rest})"
            p = float(sum(abs(data[x, 0]) ** 2 for x in good))
            assert abs(p - float(p_exact)) <= TOL, f"{name} {shape}: branch {bits}: success {p!r} != {p_exact}"
        g = res["grades"]["circuit"]
        print(f"(2) {name} {shape}: r* = {r_want}; iteration U_s U_P: {how1}; full circuit: {len(brs)} of {how2}: "
              f"ancillae |0...0>, success = {p_exact} = {float(p_exact):.9f}; grade "
              f"({g['w']}, {g['d']}, {g['t']}, {g['a']}), {len(circ['gates'])} gates")
    return p_exact


def certify_bench(exe, name, tmp, cc, validator):
    """(3) re-certification against the committed directory (and the counting one for COUNT_BENCH)."""
    n, _, M, r_want, _ = BENCH[name]
    src = os.path.join("examples", f"{name}.cqr")
    out = os.path.join(tmp, name)
    rc, so, se = cc.certify(exe, src, out, "--solutions", str(M), "--report")
    last = so.rstrip("\n").split("\n")[-1]
    assert rc == 0 and last == "certified", (name, rc, so, se)
    cert, text = cc.check_dir(out, validator)
    assert cert["status"] == "certified" and cert["axioms"] == cc.STANDARD and cert["obligations"] == []
    assert cert["solution_count"] == {"value": M, "status": "kernel_decided"} and "hM_card" not in text
    assert cert["instance"] == {"n": n, "M": M, "r": r_want}, cert["instance"]
    exa = os.path.join(ROOT, "examples", "certs", name)
    ex, _ = cc.check_dir(exa, validator)
    for f in ("Cert.lean", f"{name}.qir", f"{name}.qasm"):
        assert cc.read(os.path.join(out, f), "rb") == cc.read(os.path.join(exa, f), "rb"), f"{name}: committed {f} differs"
    assert cc.without(cert, cc.MACHINE) == cc.without(ex, cc.MACHINE), f"{name}: committed certificate.json"
    assert cc.masked(cc.read(os.path.join(out, "certificate.json"))) == \
        cc.masked(cc.read(os.path.join(exa, "certificate.json"))), f"{name}: certificate.json bytes"
    cc.check_report(exa, ex)
    print(f"(3) {name}: `certified` (exit 0), M = {M} kernel-decided, standard axioms; committed "
          f"examples/certs/{name} reproduced (Cert.lean, .qasm, .qir bytes; JSON modulo machine fields and "
          f"hashes.library; run report agrees)")
    if name == COUNT_BENCH:
        outc = os.path.join(tmp, name + "_count")
        rc, so, se = cc.certify(exe, src, outc, "--problem", "count", "--precision", "4", "--report")
        assert rc == 0 and so.rstrip("\n").split("\n")[-1].startswith("certified"), (rc, so, se)
        cnt, _, _ = cc.check_count_dir(outc, validator, name=name)
        exc = os.path.join(ROOT, "examples", "certs", name + "_count")
        exn, _, _ = cc.check_count_dir(exc, validator, name=name)
        for f in ("Cert.lean", f"{name}.qir", f"{name}.qasm"):
            assert cc.read(os.path.join(outc, f), "rb") == cc.read(os.path.join(exc, f), "rb"), f"{name}_count: {f}"
        assert cc.without(cnt, cc.MACHINE) == cc.without(exn, cc.MACHINE), f"{name}_count: certificate.json"
        assert cc.masked(cc.read(os.path.join(outc, "certificate.json"))) == \
            cc.masked(cc.read(os.path.join(exc, "certificate.json"))), f"{name}_count: certificate.json bytes"
        print(f"(3) {name}_count: `--problem count --precision 4` certified; committed examples/certs/{name}_count "
              f"reproduced (bytes; JSON modulo machine fields and hashes.library); composed grade "
              f"({cnt['grade']['w']}, {cnt['grade']['d']}, {cnt['grade']['t']}, {cnt['grade']['a']})")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261117)
    ap.add_argument("--sample", type=int, default=8, help="distinct sampled branches per check")
    ap.add_argument("--exhaustive", type=int, default=8, help="every branch when 2^measurements <= 2^E")
    ap.add_argument("--only", choices=sorted(BENCH), action="append")
    ap.add_argument("--no-certify", action="store_true")
    a = ap.parse_args()
    exe = os.path.abspath(a.cqr)
    os.chdir(ROOT)
    rng = np.random.default_rng(a.seed)
    names = a.only or list(BENCH)
    for name in names:
        check_bench(exe, name, a.sample, a.exhaustive, rng)
    if not a.no_certify:
        import jsonschema
        import certify_check as cc
        validator = jsonschema.Draft202012Validator(json.load(open(cc.SCHEMA, encoding="utf-8")))
        with tempfile.TemporaryDirectory() as tmp:
            for name in names:
                if name in CERTIFIED:
                    certify_bench(exe, name, tmp, cc, validator)
    print(f"r12_predicates: {len(names)} benchmarks pass ({a.sample} sampled branches per check, every branch "
          f"up to 2^{a.exhaustive})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
