"""Hardware transpile check (Stage 25a U5; PHASE2_SPEC §C.2; report §5.3). Two modes:

  python -I tests/diff/hw_transpile_check.py --schema-only            (.venv: jsonschema 4.26.0)
      every committed witness.json and manifest.json validates against docs/hw_witness.schema.json
      and docs/hw_artifact.schema.json (draft 2020-12), and the schemas themselves are valid;

  python -I tests/diff/hw_transpile_check.py --cqr <path to cqr>     (.venv-hw)
    * the decomposition table of hw/decomp.py numerically, both bases, to 1e-12, and (Stage 26a)
      the Lean table `cqr hw table --basis` equal to it entry for entry, phases included;
    * for every instance and target of hw/artifact.py: the pipeline rerun with the same seed list
      reproduces the committed witness.json, physical.qasm and manifest.json byte for byte (so the
      seed search is deterministic, and the committed artifact is the pipeline's output); the
      reconstruction equality, the coupling edges, the layout restoration of every block and the
      agreement of the final layout with Qiskit's are asserted inside the pipeline (a WitnessError
      is a failure); the seed search run twice makes the same choice;
    * the manifest hashes recomputed from the files (certificate JSON, canonical logical circuit —
      equal to the committed certificate's `hashes.circuit` where there is one — target snapshot,
      witness, QASM 3);
    * the bound recomputed independently from the committed physical.qasm (parsed back with
      qiskit.qasm3) and the target JSON, as exact fractions;
    * the ideal-equivalence check for every instance (all use at most 17 physical qubits): Aer's
      execution of the committed physical.qasm (parsed back and reduced to its used qubits by the
      shared helper `transpile.compact_from_qiskit`) agrees branch by branch with the statevector
      harness on the logical circuit after the final layout is undone (the per-shot mechanism of
      Stage 24b), with the unused physical qubits back in |0⟩.
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import time
import warnings
from fractions import Fraction

import numpy as np

warnings.simplefilter("ignore")
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

fails = 0
rows = []


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


def read(p, mode="r"):
    with open(p, mode, encoding=None if "b" in mode else "utf-8", newline=None if "b" in mode else "") as f:
        return f.read()


# --- the schema mode

def schema_mode(art_dir):
    import jsonschema
    for name, files in (("hw_witness", "witness.json"), ("hw_artifact", "manifest.json")):
        schema = json.load(open(os.path.join(ROOT, "docs", f"{name}.schema.json"), encoding="utf-8"))
        jsonschema.Draft202012Validator.check_schema(schema)
        check(True, f"docs/{name}.schema.json is a valid draft 2020-12 schema")
        paths = sorted(glob.glob(os.path.join(art_dir, "*", files)))
        check(len(paths) >= 11, f"{len(paths)} committed {files} files")
        for p in paths:
            try:
                jsonschema.validate(json.load(open(p, encoding="utf-8")), schema, cls=jsonschema.Draft202012Validator)
                check(True, f"{os.path.relpath(p, ROOT)}: schema")
            except jsonschema.ValidationError as e:
                check(False, f"{os.path.relpath(p, ROOT)}: schema: {e.message[:160]}")


# --- the independent bound from the committed QASM

def bound_from_qasm(qasm_text, target, basis, data_physical, delta):
    from qiskit import qasm3
    from qiskit.circuit import IfElseOp
    qc = qasm3.loads(qasm_text)
    cal = target["calibration"]
    one, two, ro = cal["one_qubit_gate_error"], cal["two_qubit_gate_error"], cal["readout_error"]
    total, counts = Fraction(0), {}

    def visit(instrs, qmap):
        nonlocal total
        for ins in instrs:
            name = ins.operation.name
            qs = [qmap[b] for b in ins.qubits]
            if isinstance(ins.operation, IfElseOp):
                blk = ins.operation.blocks[0]
                visit(blk.data, {blk.qubits[i]: qs[i] for i in range(len(qs))})
                continue
            counts[name] = counts.get(name, 0) + 1
            if name in ("rz", "sx", "x"):
                total += Fraction(one[name][str(qs[0])])
            elif name in ("cz", "cx"):
                k = f"{qs[0]},{qs[1]}"
                total += Fraction(two[name][k] if k in two[name] else two[name][f"{qs[1]},{qs[0]}"])
            elif name == "measure":
                total += Fraction(ro[str(qs[0])])
            else:
                raise ValueError(name)
    visit(qc.data, {b: qc.find_bit(b).index for b in qc.qubits})
    for p in data_physical:
        total += Fraction(ro[str(p)])
    return Fraction(delta) + total, counts


# --- the ideal-equivalence check (Stage 24b's mechanism on the physical circuit)

def equivalence(circ, qasm_text, final_layout, used, n_bits, shots, seed):
    """Aer on the committed physical circuit (`qasm_text`, parsed back) restricted to `used`
    (compact indices, through the shared helper `transpile.compact_from_qiskit`), per shot: exact
    branch probability and state; the reference is the harness on the logical circuit; the final
    layout is undone and the unused physical qubits must be |0>. Returns (branches, max dp,
    max 1-F, max leak, full coverage?)."""
    import hw_lower_check as hl
    from qiskit import qasm3
    from qiskit_aer import AerSimulator
    from transpile import compact_from_qiskit
    m = len(used)
    compact = {p: i for i, p in enumerate(used)}
    n_logical = circ["n_data"] + circ["n_anc"]
    measures = []

    def hook(target, cq, k):
        target.save_probabilities_dict(qubits=[cq], label=f"m{k}", pershot=True)
    qc_full = qasm3.loads(qasm_text)
    qc, comp2 = compact_from_qiskit(qc_full, used, before_measure=hook)
    assert comp2 == compact
    # the clbit of the k-th measurement, in order
    from qiskit.circuit import IfElseOp
    for ins in qc_full.data:
        if not isinstance(ins.operation, IfElseOp) and ins.operation.name == "measure":
            measures.append((len(measures), qc_full.find_bit(ins.clbits[0]).index))
    qc.save_statevector(label="sv", pershot=True)
    sim = AerSimulator(method="statevector")
    data_state = hl.basis_state(circ["n_data"], ())
    n_meas = sum(g["op"] == "measure" for g in circ["gates"])
    full = 2 ** n_meas <= hl.FULL_MAX
    ref = {}
    if full:
        import statevector as svh
        for bits, sv in svh.iter_ir_branches(circ, data_state):
            p = sv.norm2()
            ref[hl.key_of(bits)] = (p, sv.amp / np.sqrt(p))
        shots = max(shots, 16 * len(ref))
    # axes: compact index i holds logical l where final_layout[l] = used[i]; Aer index bit for
    # compact qubit i is bit i (little-endian); the harness wants logical 0 as the most significant.
    log_of_compact = {compact[final_layout[l]]: l for l in range(n_logical)}
    extra = [i for i in range(m) if i not in log_of_compact]
    seen, max_dp, max_df, max_leak, cache = {}, 0.0, 0.0, 0.0, {}
    written = {g["c"] for g in circ["gates"] if g["op"] == "measure"}
    done = 0
    batch = 16 if m >= 15 else 64
    while done < shots:
        b = min(batch, shots - done)
        res = sim.run(qc, shots=b, seed_simulator=seed + done, memory=True).result()
        data = res.data(0)
        mem = res.get_memory(0) if measures else ["0" * max(1, n_bits)] * b
        states = data["sv"] if isinstance(data["sv"], list) else [data["sv"]]
        for s in range(b):
            mm = mem[s]
            bits = {c: int(mm[len(mm) - 1 - c]) for c in range(len(mm)) if c in written}
            key = hl.key_of(bits)
            if key in seen:
                continue
            p = 1.0
            for kk, c in measures:
                probs = {(int(x, 0) if isinstance(x, str) else int(x)): float(v) for x, v in data[f"m{kk}"][s].items()}
                p *= probs.get(bits[c], 0.0)
            v = np.asarray(states[s], dtype=complex).reshape([2] * m)
            # numpy axis j corresponds to Aer qubit m-1-j; bring logical l (compact c_l) to axis l,
            # then the extra qubits
            axes = [m - 1 - compact[final_layout[l]] for l in range(n_logical)] + [m - 1 - i for i in extra]
            v = v.transpose(axes).reshape(2 ** n_logical, -1)
            leak = float(np.sum(np.abs(v[:, 1:]) ** 2)) if v.shape[1] > 1 else 0.0
            st = v[:, 0]
            r = ref.get(key) if full else hl.branch_for(circ, data_state, bits, cache)
            if r is None:
                check(False, f"      branch {dict(key)} has zero probability in the reference")
                seen[key] = True
                continue
            p_ref, st_ref = r
            dp = abs(p - p_ref)
            df = abs(1.0 - abs(np.vdot(st_ref, st)) ** 2)
            max_dp, max_df, max_leak = max(max_dp, dp), max(max_df, df), max(max_leak, leak)
            seen[key] = True
            if full and len(seen) == len(ref):
                break
        done += b
        if full and len(seen) == len(ref):
            break
    if full and set(seen) != set(ref):
        check(False, f"      {len(seen)} of {len(ref)} reference branches reached by Aer")
    return len(seen), max_dp, max_df, max_leak, full


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr")
    ap.add_argument("--schema-only", action="store_true")
    ap.add_argument("--artifacts", default=os.path.join(ROOT, "hw", "artifacts"))
    ap.add_argument("--shots", type=int, default=64)
    ap.add_argument("--no-equivalence", action="store_true")
    a = ap.parse_args()
    if a.schema_only:
        schema_mode(a.artifacts)
        print(f"hw_transpile_check --schema-only: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
        return 1 if fails else 0
    if not a.cqr:
        ap.error("--cqr is required without --schema-only")
    t_all = time.time()
    import artifact as art
    import decomp
    import transpile as tp
    for basis in ("cz", "cx"):
        ok, dev, worst = decomp.check_table(basis)
        check(ok, f"table {basis}: every entry equals its IR gate up to the recorded phase; max deviation {dev:.2e} ({worst})")
        # Stage 26a: the Lean table (`cqr hw table`, CQRV.Hardware.decompTable, the one decomp_sound proves)
        # equals this table entry for entry, phases included
        p = subprocess.run([a.cqr, "hw", "table", "--basis", basis], capture_output=True, text=True, encoding="utf-8")
        lean_tab = json.loads(p.stdout.strip().splitlines()[-1]) if p.returncode == 0 and p.stdout.strip() else None
        py_tab = decomp.table_json(basis)
        same = lean_tab == py_tab
        if not same and lean_tab is not None:
            for k in sorted(set(lean_tab["entries"]) | set(py_tab["entries"])):
                if lean_tab["entries"].get(k) != py_tab["entries"].get(k):
                    print(f"      entry {k}: lean {lean_tab['entries'].get(k)} vs python {py_tab['entries'].get(k)}")
        check(same, f"table {basis}: Lean's decompTable (cqr hw table) = hw/decomp.py's table, "
                    f"{len(py_tab['entries'])} entries incl. p/cp at 8 angles and swap, phases exact")
    for inst in art.INSTANCES:
        name = inst[0]
        for tname in inst[4]:
            t0 = time.time()
            label = f"{name}__{tname}"
            d = art.artifact_dir(a.artifacts, name, tname)
            try:
                manifest, w, qasm, best = art.build(a.cqr, inst, tname)
            except tp.WitnessError as e:
                check(False, f"{label}: pipeline: {e}")
                continue
            check(True, f"{label}: reconstruction = physical circuit, two-qubit ops on coupling edges, blocks restore the layout, final layout = Qiskit's (seed {w['seed']})")
            # determinism: the same choice twice
            _, w2, qasm2, _ = art.build(a.cqr, inst, tname)
            check(w2 == w and qasm2 == qasm, f"{label}: seed search deterministic (same witness and QASM twice)")
            # the committed files
            cm, cw, cq = (read(os.path.join(d, f)) for f in ("manifest.json", "witness.json", "physical.qasm"))
            # R5 (DECISIONS.md 2026-11-16): hashes.certificate_json is the full SHA3 of the certificate.json the artifact
            # was transpiled from (a historical record, null before the certificate); the re-transpile records the
            # current one, so the manifest is compared modulo that field
            def sans_cert_hash(m):
                m = json.loads(json.dumps(m)); m["hashes"].pop("certificate_json", None); return art.canonical(m)
            check(sans_cert_hash(json.loads(cm)) == sans_cert_hash(manifest) and cw == art.canonical(w) + "\n" and cq == qasm,
                  f"{label}: committed manifest.json (modulo hashes.certificate_json), witness.json, physical.qasm "
                  "reproduced byte for byte")
            # hashes
            M = json.loads(cm)
            H = M["hashes"]
            target = art.load_target(tname)
            circ, _ = art.logical_circuit(a.cqr, inst)
            hok = (H["witness"] == art.sha3(cw.rstrip("\n")) and H["physical_qasm3"] == art.sha3(cq)
                   and H["logical_circuit"] == art.sha3(art.canonical(circ)) and H["target_snapshot"] == target["snapshot"]["hash"])
            hok = hok and (H["certificate_json"] is None or re.fullmatch(r"[0-9a-f]{64}", H["certificate_json"]) is not None)
            if inst[5] is not None:
                cert = json.loads(read(os.path.join(ROOT, inst[5], "certificate.json")))
                hok = hok and cert["hashes"]["circuit"] == H["logical_circuit"]
                extra = (f"; logical circuit hash = the committed certificate's hashes.circuit ({inst[5]}); "
                         "certificate_json well-formed (the transpile-time hash, not compared, R5)")
            else:
                extra = ""
            check(hok, f"{label}: manifest hashes recomputed from the files{extra}")
            # the bound from the committed QASM
            bq, counts_q = bound_from_qasm(cq, target, M["basis"], M["layout"]["data_physical"], Fraction(M["bound"]["delta"]))
            check(bq == Fraction(M["bound"]["bound"]) and (bq >= 1) == M["bound"]["vacuous"]
                  and counts_q.get(M["basis"], 0) == M["counts"]["physical"][M["basis"]]
                  and counts_q.get("measure", 0) == M["counts"]["physical"]["measure"],
                  f"{label}: bound recomputed from physical.qasm = {float(bq):.4g}{' (vacuous)' if bq >= 1 else ''}; "
                  f"{M['basis']} {counts_q.get(M['basis'], 0)}, measure {counts_q.get('measure', 0)}, "
                  f"error-1.0 edge used: {M['bound']['uses_error_1_edge']}")
            # ideal equivalence
            eq = ""
            if not a.no_equivalence:
                nb, dp, df, leak, full = equivalence(circ, cq, w["final_layout"], M["layout"]["used_qubits"],
                                                     best["n_bits"], a.shots, 25)
                check(dp <= hl_tol() and df <= hl_tol() and leak <= hl_tol(),
                      f"{label}: ideal equivalence on {len(M['layout']['used_qubits'])} physical qubits: {nb} branches "
                      f"({'all' if full else 'sampled'}), max |dp| {dp:.1e}, max 1-F {df:.1e}, leak into unused qubits {leak:.1e}")
                eq = f"{nb} br{'/all' if full else '/sampled'}"
            rows.append((label, w["seed"], M["bound"]["uses_error_1_edge"], len(M["layout"]["used_qubits"]), w["swaps"],
                         M["counts"]["physical"][M["basis"]], M["counts"]["physical"]["measure"], float(bq), bq >= 1, eq,
                         time.time() - t0))
    print("\ninstance__target | seed | error-1.0 edge | used qubits | swaps | 2q | meas | δ_hw | vacuous | equivalence | s")
    for r in rows:
        print(" | ".join(str(x) if not isinstance(x, float) else f"{x:.4g}" for x in r))
    total = sum(os.path.getsize(p) for p in glob.glob(os.path.join(a.artifacts, "*", "*")))
    print(f"artifacts: {len(rows)} directories, {total} bytes; {time.time() - t_all:.1f} s")
    print(f"hw_transpile_check: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
    return 1 if fails else 0


def hl_tol():
    return 1e-9


if __name__ == "__main__":
    sys.exit(main())
