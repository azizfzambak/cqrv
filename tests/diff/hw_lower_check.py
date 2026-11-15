"""Hardware lowering check (Stage 24b; PHASE2_SPEC §C.1 "Lowering"; report §5.3, §6.2.2). Run with
the .venv-hw Python (qiskit 2.6.2, qiskit-aer 0.18.2).

`hw/lower.py` lowers the canonical circuit JSON of the IR to a Qiskit dynamic circuit (`if_test`
on the classical bit for `ifBit`, mid-circuit `measure`). This check compares, branch by branch,
Aer's own execution of the lowered circuit with the in-repo statevector harness
(tests/diff/statevector.py), which enumerates the measurement branches exactly:

  * **The Aer mechanism.** The statevector method runs the dynamic circuit shot by shot. Before
    every `measure` the lowering inserts `save_probabilities_dict(qubits=[q], pershot=True)`, so
    each shot records the exact Born probability of the outcome it then takes; the product along
    the shot is the exact branch probability p_c. At the end `save_statevector(pershot=True)`
    records the (normalized) post-measurement state of the shot's branch, and `memory=True` its
    classical assignment c. No hand evolution with Qiskit operators is involved; the only
    sampling is which branch a shot takes.
  * **The reference** for a branch c is the harness: the enumeration `iter_ir_branches` when the
    instance has at most FULL_MAX branches (then every reference branch must be reached by some
    shot: full coverage), or the trajectory following c (`branch_for`) when it has more (then
    every branch Aer produced is compared, and the number of distinct branches is reported).
  * **Compared per branch:** |p_c(Aer) − p_c(ref)| ≤ TOL and 1 − |<ref|aer>|² ≤ TOL, TOL = 1e-9.
  * **Instances** (data register ≤ 6 qubits): the MBU gadget `mbuCircuit` and its uncorrected
    variants `mbuNoCorr`, `mbuNoCorr'` (CQRV/Circuit/Restoration.lean, tests/CQRVTests/
    RestoreAlgebra.lean), the parity instance `parityCircuit` (22a/23a) and the dirty phase
    gadget `dirtyGadget` (23b, with the ancilla in |0> and in |1>), transcribed gate for gate
    from their Lean definitions; the oracles of examples/search_or.cqr (n = 4) and
    examples/simple_alu_x0_1.cqr (n = 6) in both uncomputation modes, on every computational-basis
    data input; their Grover circuits with one iteration (tree in both modes, few:log in mbu);
    the counting circuit of search_or with m = 2 (CertifyTool counting-sample, `p` / `cp`) in both
    modes. The phase convention of `p` / `cp` is checked numerically on Aer first.

Usage: python -I tests/diff/hw_lower_check.py --cqr <path to cqr> [--shots N] [--seed s]
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
import warnings

import numpy as np

warnings.simplefilter("ignore")
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lower  # noqa: E402
import statevector as svh  # noqa: E402
from lean_tool import certify_tool  # noqa: E402

TOL = 1e-9
FULL_MAX = 64      # at most this many reference branches: enumerate them all and require coverage
BATCH = 64         # Aer shots per run (pershot statevectors are kept in memory per run)
fails = 0
stats = []         # (instance, inputs, branches compared, full coverage?, max dp, max 1-F)


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


# --- the gadgets, transcribed from their Lean definitions (flat indices: data 0, 1; ancilla 2)

def TL(a, b, t):
    """`TempLogicalAND a b t` (CQRV/Synthesis/TempAnd.lean): h t; t t; cnot a t; cnot b t; cnot t a;
    cnot t b; tdg a; tdg b; t t; cnot t a; cnot t b; h t; s t."""
    return [{"op": "h", "q": [t]}, {"op": "t", "q": [t]}, {"op": "cnot", "q": [a, t]},
            {"op": "cnot", "q": [b, t]}, {"op": "cnot", "q": [t, a]}, {"op": "cnot", "q": [t, b]},
            {"op": "tdg", "q": [a]}, {"op": "tdg", "q": [b]}, {"op": "t", "q": [t]},
            {"op": "cnot", "q": [t, a]}, {"op": "cnot", "q": [t, b]}, {"op": "h", "q": [t]},
            {"op": "s", "q": [t]}]


def mbu_uncompute(t, j, O):
    """`mbuUncompute t j O` (CQRV/Circuit/MBUGeneral.lean): h t; measure t j; O under `if j`; if j: x t."""
    return ([{"op": "h", "q": [t]}, {"op": "measure", "q": [t], "c": j}]
            + [{**g, "if": j} for g in O] + [{"op": "x", "q": [t], "if": j}])


def gadget(gates):
    return {"n_data": 2, "n_anc": 1, "gates": gates}


GADGETS = {
    # `mbuCircuit := ⟨2, TempLogicalAND x0 x1 a0 ++ [z a0] ++ UncomputeTempLogicalAND x0 x1 a0 0⟩`,
    # `UncomputeTempLogicalAND a b t m = mbuUncompute t m [cz a b]`
    "mbuCircuit": gadget(TL(0, 1, 2) + [{"op": "z", "q": [2]}] + mbu_uncompute(2, 0, [{"op": "cz", "q": [0, 1]}])),
    # `mbuNoCorr := ⟨2, TempLogicalAND x0 x1 a0 ++ [z a0] ++ mbuUncompute a0 0 []⟩`
    "mbuNoCorr": gadget(TL(0, 1, 2) + [{"op": "z", "q": [2]}] + mbu_uncompute(2, 0, [])),
    # `mbuNoCorr' := ⟨2, TempLogicalAND x0 x1 a0 ++ mbuUncompute a0 0 []⟩`
    "mbuNoCorr'": gadget(TL(0, 1, 2) + mbu_uncompute(2, 0, [])),
    # `parityCircuit := ⟨2, [cnot x0 a0, cnot x1 a0] ++ [z a0] ++ mbuUncompute a0 0 [z x0, z x1]⟩`
    "parityCircuit": gadget([{"op": "cnot", "q": [0, 2]}, {"op": "cnot", "q": [1, 2]}, {"op": "z", "q": [2]}]
                            + mbu_uncompute(2, 0, [{"op": "z", "q": [0]}, {"op": "z", "q": [1]}])),
    # `dirtyGadget := ⟨2, [cnot x0 a0, cz a0 x1, cnot x0 a0, cz a0 x1]⟩`
    "dirtyGadget": gadget([{"op": "cnot", "q": [0, 2]}, {"op": "cz", "q": [2, 1]},
                           {"op": "cnot", "q": [0, 2]}, {"op": "cz", "q": [2, 1]}]),
}
# the dirty gadget with the ancilla prepared in |1> (an X on the ancilla before the gadget)
GADGETS["dirtyGadget_anc1"] = gadget([{"op": "x", "q": [2]}] + GADGETS["dirtyGadget"]["gates"])


# --- circuits from cqr and CertifyTool

def cqr_circuit(cqr, args):
    p = subprocess.run([cqr, "synthesize", *args, "--json"], capture_output=True, text=True, encoding="utf-8")
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if p.returncode != 0 or not lines:
        raise SystemExit(f"cqr synthesize {' '.join(args)} failed ({p.returncode}): {p.stderr.strip()[:200]}")
    return json.loads(lines[-1])["circuit"]


def counting_circuit(src, m, mode):
    out = certify_tool(["counting-sample", src, str(m), "--uncompute", mode])
    return json.loads([l for l in out.splitlines() if l.startswith("{")][-1])["circuit"]


# --- the reference

def basis_state(n_data, x_prefix):
    d = np.zeros(2 ** n_data, dtype=complex)
    idx = 0
    for i in x_prefix:          # harness order: qubit 0 is the most significant bit
        idx |= 1 << (n_data - 1 - i)
    d[idx] = 1.0
    return d


CACHE_DEPTH = 4    # trajectory prefixes (outcome sequences) of at most this length are cached


def branch_for(circ, data_state, bits, cache=None):
    """The harness's branch with the given measurement outcomes (trajectory following):
    (p_c, normalized state) or None if that branch has probability < PROB_EPS. `cache` (a dict
    owned by the caller) keeps the state after each measurement for short outcome prefixes, so
    that the shared beginning of the trajectories is computed once."""
    gates = circ["gates"]
    measures = [k for k, g in enumerate(gates) if g["op"] == "measure"]
    outcomes = []
    for k in measures:
        b = bits.get(gates[k]["c"])
        if b is None:
            return None
        outcomes.append(b)
    # the longest cached prefix
    start, sv = 0, None
    if cache is not None:
        for d in range(min(len(outcomes), CACHE_DEPTH), 0, -1):
            hit = cache.get(tuple(outcomes[:d]))
            if hit is not None:
                start, sv = measures[d - 1] + 1, hit.copy()
                break
    if sv is None:
        sv = svh._embed(circ, data_state)
    depth = sum(1 for k in measures if k < start)
    for k in range(start, len(gates)):
        g = gates[k]
        if g["op"] == "measure":
            sv.project(g["q"][0], bits[g["c"]])
            if sv.norm2() < svh.PROB_EPS:
                return None
            depth += 1
            if cache is not None and depth <= CACHE_DEPTH:
                cache.setdefault(tuple(outcomes[:depth]), sv.copy())
        else:
            svh._step(k, g, bits, sv)
    p = sv.norm2()
    return p, sv.amp / np.sqrt(p)


def key_of(bits):
    return tuple(sorted(bits.items()))


# --- the Aer side

def aer_batches(circ, x_prefix, shots, seed):
    """Run the lowered circuit on Aer in batches; yields (bits, p_c, state in harness order)."""
    from qiskit_aer import AerSimulator
    n = circ["n_data"] + circ["n_anc"]
    n_bits = lower.n_bits_of(circ)
    measures = [k for k, g in enumerate(circ["gates"]) if g["op"] == "measure"]

    def hooks(qc, k, g):
        if g["op"] == "measure":
            qc.save_probabilities_dict(qubits=[g["q"][0]], label=f"m{k}", pershot=True)

    qc = lower.lower(circ, x_prefix=x_prefix, hooks=hooks)
    qc.save_statevector(label="sv", pershot=True)
    sim = AerSimulator(method="statevector")
    done = 0
    while done < shots:
        b = min(BATCH, shots - done)
        res = sim.run(qc, shots=b, seed_simulator=seed + done, memory=True).result()
        data = res.data(0)
        mem = res.get_memory(0) if measures else ["0" * n_bits] * b
        states = data["sv"] if measures or b > 1 else [data["sv"]] if not isinstance(data["sv"], list) else data["sv"]
        for s in range(b):
            m = mem[s]
            bits = {c: int(m[len(m) - 1 - c]) for c in range(n_bits)} if measures else {}
            # only the bits the circuit writes
            written = {g["c"] for g in circ["gates"] if g["op"] == "measure"}
            bits = {c: v for c, v in bits.items() if c in written}
            p = 1.0
            for k in measures:
                probs = data[f"m{k}"][s]
                probs = {(int(kk, 0) if isinstance(kk, str) else int(kk)): float(v) for kk, v in probs.items()}
                p *= probs.get(bits[circ["gates"][k]["c"]], 0.0)
            yield bits, p, lower.to_harness_order(states[s], n)
        done += b


def compare_instance(name, circ, x_prefix, shots, seed):
    """Compare one instance on one data input. Returns (branches compared, full?, max dp, max 1-F)."""
    data_state = basis_state(circ["n_data"], x_prefix)
    n_meas = sum(g["op"] == "measure" for g in circ["gates"])
    full = 2 ** n_meas <= FULL_MAX
    ref = {}
    if full:
        for bits, sv in svh.iter_ir_branches(circ, data_state):
            p = sv.norm2()
            ref[key_of(bits)] = (p, sv.amp / np.sqrt(p))
        shots = max(shots, 16 * len(ref))
    seen, max_dp, max_df, cache = {}, 0.0, 0.0, {}
    for bits, p_aer, st_aer in aer_batches(circ, x_prefix, shots, seed):
        k = key_of(bits)
        if k in seen:
            continue
        r = ref.get(k) if full else branch_for(circ, data_state, bits, cache)
        if r is None:
            check(False, f"{name} input {x_prefix}: Aer branch {dict(k)} has zero probability in the reference")
            seen[k] = True
            continue
        p_ref, st_ref = r
        dp = abs(p_aer - p_ref)
        df = abs(1.0 - abs(np.vdot(st_ref, st_aer)) ** 2)
        max_dp, max_df = max(max_dp, dp), max(max_df, df)
        if dp > TOL or df > TOL:
            check(False, f"{name} input {x_prefix} branch {dict(k)}: p Aer {p_aer:.12g} ref {p_ref:.12g} "
                         f"(dp {dp:.3g}); 1-F {df:.3g}")
        seen[k] = True
        if full and len(seen) == len(ref):
            break
    if full and set(seen) != set(ref):
        check(False, f"{name} input {x_prefix}: {len(seen)} of {len(ref)} reference branches reached by Aer")
    return len(seen), full, max_dp, max_df


def run_instance(name, circ, inputs, shots, seed, sweep_shots=None):
    """`shots` for the first input (the all-zero one), `sweep_shots` (default `shots`) for the others."""
    t0 = time.time()
    tot, full_all, mdp, mdf = 0, True, 0.0, 0.0
    for i, x in enumerate(inputs):
        n, full, dp, df = compare_instance(name, circ, x, shots if i == 0 or sweep_shots is None else sweep_shots, seed)
        tot += n
        full_all &= full
        mdp, mdf = max(mdp, dp), max(mdf, df)
    n_meas = sum(g["op"] == "measure" for g in circ["gates"])
    cov = "all branches" if full_all else "sampled"
    stats.append((name, len(inputs), tot, cov, mdp, mdf))
    check(mdp <= TOL and mdf <= TOL,
          f"{name}: {circ['n_data']}+{circ['n_anc']} qubits, {len(circ['gates'])} gates, {n_meas} measurements; "
          f"{len(inputs)} input(s), {tot} branches compared ({cov}); max |dp| {mdp:.2e}, max 1-F {mdf:.2e} "
          f"({time.time() - t0:.1f} s)")


def all_inputs(n):
    return [tuple(i for i in range(n) if (x >> (n - 1 - i)) & 1) for x in range(2 ** n)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--shots", type=int, default=64, help="Aer shots per input for sampled instances")
    ap.add_argument("--sweep-shots", type=int, default=16,
                    help="Aer shots per non-zero basis input in the oracle sweeps of sampled instances")
    ap.add_argument("--seed", type=int, default=24)
    a = ap.parse_args()
    t_all = time.time()
    check(lower.check_phase_convention(), "phase convention: p 1 3 on |1> = e^{i pi/4}, cp 1 2 on |11> = i (Aer)")

    # the gadgets, every basis input
    for name, circ in GADGETS.items():
        run_instance(name, circ, all_inputs(2), a.shots, a.seed)

    # the oracles, every basis input
    for src, n in (("search_or", 4), ("simple_alu_x0_1", 6)):
        path = os.path.join(ROOT, "examples", f"{src}.cqr")
        for mode in ("mbu", "coherent"):
            circ = cqr_circuit(a.cqr, [path] + (["--uncompute", mode] if mode != "mbu" else []))
            assert circ["n_data"] == n, circ["n_data"]
            run_instance(f"{src} oracle {mode}", circ, all_inputs(n), a.shots, a.seed, a.sweep_shots)

    # the Grover circuits with one iteration, the all-zero input
    for src in ("search_or", "simple_alu_x0_1"):
        path = os.path.join(ROOT, "examples", f"{src}.cqr")
        for label, extra in (("tree mbu", []), ("tree coherent", ["--uncompute", "coherent"]),
                             ("few:log mbu", ["--shape", "few:log"])):
            circ = cqr_circuit(a.cqr, [path, "--grover", "--iterations", "1"] + extra)
            run_instance(f"{src} grover r=1 {label}", circ, [()], 4 * a.shots, a.seed)

    # the counting circuit of search_or, n = 4, m = 2 (p / cp), both modes
    for mode in ("mbu", "coherent"):
        circ = counting_circuit(os.path.join("examples", "search_or.cqr"), 2, mode)
        assert any(g["op"] in ("p", "cp") for g in circ["gates"]), "no p / cp in the counting circuit"
        run_instance(f"counting search_or m=2 {mode}", circ, [()], 4 * a.shots, a.seed)

    # the CLI and the QASM 3 export of one circuit (inspection only)
    with tempfile.TemporaryDirectory() as d:
        cj = os.path.join(d, "mbu.json")
        json.dump(GADGETS["mbuCircuit"], open(cj, "w", encoding="utf-8"))
        out = os.path.join(d, "mbu.qasm")
        p = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "hw", "lower.py"), cj, "--qasm-out", out],
                           capture_output=True, text=True, encoding="utf-8")
        text = open(out, encoding="utf-8").read() if os.path.exists(out) else ""
        check(p.returncode == 0 and text.startswith("OPENQASM 3.0;") and "if (" in text and "measure" in text,
              "hw/lower.py CLI: QASM 3 export of mbuCircuit has an if statement and a measurement")

    print("\ninstance | inputs | branches | coverage | max |dp| | max 1-F")
    for name, ni, nb, cov, dp, df in stats:
        print(f"{name} | {ni} | {nb} | {cov} | {dp:.1e} | {df:.1e}")
    print(f"total branches compared: {sum(s[2] for s in stats)}; max |dp| {max(s[4] for s in stats):.2e}; "
          f"max 1-F {max(s[5] for s in stats):.2e}; {time.time() - t_all:.1f} s")
    print(f"hw_lower_check: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
