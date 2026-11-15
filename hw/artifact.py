"""The physical artifact — Stage 25a U4/U5 (PHASE2_SPEC §C.2 "The physical artifact"; report §5.3).

Untrusted tool. For every instance of `INSTANCES` and each of its targets, `build` runs the
pipeline of hw/transpile.py with the seed search over `SEEDS` and produces the artifact of
`hw/artifacts/<instance>__<target>/`:

  * `witness.json`   the witness (docs/hw_witness.schema.json 1.0.0), canonical JSON;
  * `physical.qasm`  the final physical circuit (swaps decomposed by the table) as OpenQASM 3;
  * `manifest.json`  the `PhysicalArtifact` (docs/hw_artifact.schema.json 1.0.0): the SHA3-256
                     hashes of the committed certificate JSON (when the instance comes from one),
                     of the canonical logical circuit JSON (the form Lean hashes as
                     `circuit_hash`), of the target snapshot, of the witness and of the QASM 3
                     text; the versions and the seed chosen; every seed tried with its figure;
                     the physical counts and the bound figures (exact fractions; vacuity marked).

δ comes from the Grover parameters of `cqr synthesize --grover --json` (`iterations`,
`solutions`, `n`) by the exact recurrence of tests/diff/hw_bound_check.py (the gadget has δ = 0 and
is not a Grover instance). Nothing is certified: every manifest says so.

Usage: python -I hw/artifact.py --cqr <path to cqr> [--out hw/artifacts] [--only <instance>]
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys
import warnings
from fractions import Fraction

warnings.simplefilter("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
import decomp  # noqa: E402
import transpile as tp  # noqa: E402

SEEDS = list(range(20))
TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}

# name, source (None = the MBU gadget), synthesize flags, uncompute mode, targets, committed certificate dir
INSTANCES = [
    ("mbu_gadget", None, [], "mbu", ["fake_torino"], None),
    ("mbu_gadget_wrapped", None, [], "mbu", ["fake_torino"], None),
    ("hw_n2_tree_mbu", "examples/hw_n2.cqr", [], "mbu", ["fake_torino"], None),
    ("hw_n3_tree_mbu", "examples/hw_n3.cqr", [], "mbu", ["fake_torino"], None),
    ("grover_pred_037_tree_mbu", "examples/grover_pred_037.cqr", [], "mbu", ["fake_torino"], "examples/certs/grover_pred_037"),
    ("grover_pred_037_tree_coherent", "examples/grover_pred_037.cqr", ["--uncompute", "coherent"], "coherent",
     ["fake_torino", "fake_washington"], "examples/certs/grover_pred_037_coh"),
    ("grover_pred_037_fewlog_mbu", "examples/grover_pred_037.cqr", ["--shape", "few:log"], "mbu", ["fake_torino"],
     "examples/certs/grover_pred_037_few"),
    ("simple_alu_x0_1_tree_mbu", "examples/simple_alu_x0_1.cqr", ["--solutions", "30"], "mbu", ["fake_torino"],
     "examples/certs/simple_alu_x0_1"),
    ("simple_alu_x0_1_tree_coherent", "examples/simple_alu_x0_1.cqr", ["--solutions", "30", "--uncompute", "coherent"],
     "coherent", ["fake_torino", "fake_washington"], None),
    ("simple_alu_x0_1_fewlog_mbu", "examples/simple_alu_x0_1.cqr", ["--solutions", "30", "--shape", "few:log"], "mbu",
     ["fake_torino"], None),
]


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha3(data):
    return hashlib.sha3_256(data if isinstance(data, bytes) else data.encode("utf-8")).hexdigest()


def load_target(name):
    return json.load(open(os.path.join(ROOT, TARGET_FILES[name]), encoding="utf-8"))


def backend_of(target):
    import qiskit_ibm_runtime.fake_provider as fp
    return getattr(fp, target["source"]["class"].rsplit(".", 1)[1])()


def logical_circuit(cqr, inst):
    """(circuit dict, Grover parameters or None) of an instance."""
    name, src, flags, mode, _, _ = inst
    if src is None:
        from hw_lower_check import GADGETS
        if name == "mbu_gadget_wrapped":
            return wrapped_gadget(GADGETS["mbuCircuit"]), None
        return GADGETS["mbuCircuit"], None
    p = subprocess.run([cqr, "synthesize", os.path.join(ROOT, src), "--grover", *flags, "--json"],
                       capture_output=True, text=True, encoding="utf-8")
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if p.returncode != 0 or not lines:
        raise SystemExit(f"cqr synthesize {src} {' '.join(flags)} failed ({p.returncode}): {p.stderr.strip()[:200]}")
    r = json.loads(lines[-1])
    return r["circuit"], {"n": r["n"], "r": r["iterations"], "M": r["solutions"], "shape": r["shape"]}


def wrapped_gadget(mbu):
    """Stage 25b V1 — the MBU gadget wrapped for a computational-basis readout: prepare |++> on the
    data (H x0, H x1), the gadget (its ideal output is CZ|++> = (I⊗H)·CNOT(x0→x1)·(H⊗I)|00>),
    then the inverse of that preparation — H x1, CNOT x0→x1, H x0 — so that the ideal output is
    |00> with the ancilla back in |0>; success is the all-zero readout of the three qubits. The
    wrapper is part of the logical circuit, so its two-qubit gate is routed with the rest."""
    pre = [{"op": "h", "q": [0]}, {"op": "h", "q": [1]}]
    post = [{"op": "h", "q": [1]}, {"op": "cnot", "q": [0, 1]}, {"op": "h", "q": [0]}]
    return {"n_data": mbu["n_data"], "n_anc": mbu["n_anc"], "gates": pre + mbu["gates"] + post}


def delta_of(params):
    if params is None:
        return Fraction(0)
    from hw_bound_check import grover_delta
    return grover_delta(params["r"], params["n"], params["M"])


def build(cqr, inst, target_name, seeds=SEEDS):
    """The artifact of one instance on one target: (manifest, witness, qasm text, best result)."""
    name, src, flags, mode, _, cert_dir = inst
    target = load_target(target_name)
    basis = "cz" if "cz" in target["basis_gates"] else "cx"
    if mode == "mbu" and not target["capabilities"]["feed_forward"]["value"]:
        raise SystemExit(f"{name} on {target_name}: mbu needs feed-forward")
    circ, params = logical_circuit(cqr, inst)
    delta = delta_of(params)
    backend = backend_of(target)
    best, trials = tp.seed_search(circ, basis, backend, target, seeds, delta)
    w, b = best["witness"], best["bound"]
    from qiskit import qasm3
    qasm = qasm3.dumps(tp.to_qiskit_physical(best["final_phys"], best["device_width"], best["n_bits"]))
    cert_hash = None
    if cert_dir is not None:
        cert_hash = sha3(open(os.path.join(ROOT, cert_dir, "certificate.json"), "rb").read())
    manifest = {
        "schema_version": "1.0.0",
        "instance": name,
        "source": src,
        "synthesize_flags": flags,
        "uncompute": mode,
        "grover": params,
        "target": target_name,
        "target_class": target["source"]["class"],
        "basis": basis,
        "n_logical": best["n"],
        "device_width": best["device_width"],
        "seed": w["seed"],
        "seeds_tried": trials,
        "versions": w["versions"],
        "hashes": {
            "certificate_json": cert_hash,
            "certificate_dir": cert_dir,
            "logical_circuit": sha3(canonical(circ)),
            "target_snapshot": target["snapshot"]["hash"],
            "witness": sha3(canonical(w)),
            "physical_qasm3": sha3(qasm),
        },
        "layout": {"initial": w["initial_layout"], "final": w["final_layout"], "data_physical": b["data_physical"],
                   "used_qubits": b["used_qubits"], "swaps": w["swaps"]},
        "counts": {"logical_gates": len(circ["gates"]), "translated_basis_gates": len(best["gates"]),
                   "physical": b["counts"]},
        "bound": {"delta": decomp.frac_str(b["delta"]), "sum": decomp.frac_str(b["sum"]),
                  "bound": decomp.frac_str(b["bound"]), "bound_float": float(b["bound"]), "vacuous": b["vacuous"],
                  "uses_error_1_edge": b["uses_error_1_edge"], "error_1_edges": [list(e) for e in b["error_1_edges"]],
                  "terms": {k: decomp.frac_str(v) for k, v in b["terms"].items()},
                  "mid_circuit_assumption": "mid-circuit measurements take the readout rate of their physical qubit "
                                            "(the snapshot gives no mid-circuit error)"},
        "status": "reported, not certified (Stage 27); the transpiler is untrusted, the witness is checked",
    }
    return manifest, w, qasm, best


def artifact_dir(out, name, target_name):
    return os.path.join(out, f"{name}__{target_name}")


def write_artifact(d, manifest, witness, qasm):
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "witness.json"), "w", encoding="utf-8", newline="\n") as f:
        f.write(canonical(witness) + "\n")
    with open(os.path.join(d, "physical.qasm"), "w", encoding="utf-8", newline="\n") as f:
        f.write(qasm)
    with open(os.path.join(d, "manifest.json"), "w", encoding="utf-8", newline="\n") as f:
        f.write(canonical(manifest) + "\n")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--out", default=os.path.join(ROOT, "hw", "artifacts"))
    ap.add_argument("--only")
    a = ap.parse_args(argv)
    total = 0
    for inst in INSTANCES:
        if a.only and inst[0] != a.only:
            continue
        for tname in inst[4]:
            manifest, w, qasm, _ = build(a.cqr, inst, tname)
            d = artifact_dir(a.out, inst[0], tname)
            write_artifact(d, manifest, w, qasm)
            size = sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d))
            total += size
            b = manifest["bound"]
            print(f"{inst[0]}__{tname}: seed {manifest['seed']}, swaps {w['swaps']}, used qubits "
                  f"{len(manifest['layout']['used_qubits'])}, {manifest['basis']} {manifest['counts']['physical'][manifest['basis']]}, "
                  f"bound {b['bound_float']:.4g}{' VACUOUS' if b['vacuous'] else ''}"
                  f"{' error-1.0 edge' if b['uses_error_1_edge'] else ''}; {size} bytes")
    print(f"total {total} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
