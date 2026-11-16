"""Stage 26c2 — the committed physical certificate is the artifact's, and its QASM 3 parses back
(PHASE2_SPEC §C.3; report §5.3, §8.4, §9.1.1).

  python -I tests/diff/hw_physcert_check.py --cqr <cqr> [--cert examples/certs/grover_pred_037_torino]   (.venv-hw)

For the certificate directory:
  * `manifest.json`: the hashes it records are those of the artifact's canonical `logical.json`,
    `witness.json`, `physical.json`, of the logical certificate's `certificate.json` bytes, of the
    target's snapshot and of the target file's bytes; the status words are among the four of P3 and
    `emulator_validated` is present iff the artifact's run report passed;
  * `PhysCert.lean`, `physical.qasm` and `manifest.json` are byte-identical to what `cqr hw certify`
    regenerates (the literals are the artifact's; the logical body is the committed `Cert.lean`'s);
  * the `PhysGrade` values of the manifest equal `hw/physgrade.py`'s at each latency;
  * `physical.qasm` parses back (`qiskit.qasm3.loads`) to the artifact's `physical.json` gate list:
    the same ops on the same device qubits, angles equal to 1e-12, the same measured bits, the same
    conditions.
The kernel check of `PhysCert.lean` (`lake env lean`) is the bash step's.
"""
import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import tempfile
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import physgrade  # noqa: E402

TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}
WORDS = ["logical_certified", "hardware_compatible", "physical_translation_validated", "emulator_validated"]


def sha3(data):
    return hashlib.sha3_256(data if isinstance(data, bytes) else data.encode("utf-8")).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def qasm_ops(text):
    """The ops of a QASM 3 text as physical.json's flat ops: {op, q, angle?, c?} with the condition."""
    from qiskit import qasm3
    qc = qasm3.loads(text)
    out = []

    def emit(inst, cond):
        name = inst.operation.name
        qs = [qc.find_bit(q).index for q in inst.qubits]
        op = {"op": name, "q": qs}
        if name == "rz":
            op["angle"] = float(inst.operation.params[0])
        if name == "measure":
            op["c"] = qc.find_bit(inst.clbits[0]).index
        if cond is not None:
            op["if"] = cond
        out.append(op)

    for inst in qc.data:
        if inst.operation.name == "if_else":
            cond_bit = inst.operation.condition[0]
            bit = qc.find_bit(cond_bit).index if not isinstance(cond_bit, int) else cond_bit
            body = inst.operation.blocks[0]
            for sub in body.data:
                sname = sub.operation.name
                sqs = [qc.find_bit(inst.qubits[body.find_bit(q).index]).index for q in sub.qubits]
                op = {"op": sname, "q": sqs, "if": bit}
                if sname == "rz":
                    op["angle"] = float(sub.operation.params[0])
                out.append(op)
        else:
            emit(inst, None)
    return out


def flat_json_ops(ops):
    out = []
    for pop in ops:
        if "if" in pop:
            for b in pop["body"]:
                o = dict(b); o["if"] = pop["if"]; out.append(o)
        else:
            out.append(dict(pop))
    return out


def same_op(a, b):
    if a["op"] != b["op"] or list(a["q"]) != list(b["q"]) or a.get("if") != b.get("if"):
        return False
    if a["op"] == "measure" and a.get("c") != b.get("c"):
        return False
    if a["op"] == "rz":
        want = 2 * math.pi * float(Fraction(b["angle"]))
        return abs(a["angle"] - want) <= 1e-12 * max(1.0, abs(want))
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--cert", default=os.path.join("examples", "certs", "grover_pred_037_torino"))
    a = ap.parse_args()
    cdir = os.path.join(ROOT, a.cert)
    errors = []
    man = json.load(open(os.path.join(cdir, "manifest.json"), encoding="utf-8"))
    adir = os.path.join(ROOT, man["artifact"]["dir"])
    ldir = os.path.join(ROOT, "examples", "certs", man["certificate"].rsplit("_", 1)[0])
    amanifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
    tpath = os.path.join(ROOT, TARGET_FILES[amanifest["target"]])
    want = {
        "logical_circuit": sha3(canonical(json.load(open(os.path.join(adir, "logical.json"), encoding="utf-8")))),
        "witness": sha3(canonical(json.load(open(os.path.join(adir, "witness.json"), encoding="utf-8")))),
        "physical_json": sha3(canonical(json.load(open(os.path.join(adir, "physical.json"), encoding="utf-8")))),
        "certificate_json": sha3(open(os.path.join(ldir, "certificate.json"), "rb").read()),
        "target_snapshot": json.load(open(tpath, encoding="utf-8"))["snapshot"]["hash"],
        "target_file_sha3": sha3(open(tpath, "rb").read()),
    }
    for k, v in want.items():
        if man["hashes"].get(k) != v:
            errors.append(f"manifest hash {k}: {man['hashes'].get(k)} differs from {v}")
    words = man["status"]
    if any(w not in WORDS for w in words) or words != [w for w in WORDS if w in words]:
        errors.append(f"status words {words} are not an ordered subset of {WORDS}")
    run_path = os.path.join(ROOT, "docs", "hw_runs", f"{amanifest['instance']}__{amanifest['target']}.json")
    passed = os.path.exists(run_path) and json.load(open(run_path, encoding="utf-8"))["check"]["result"] == "passes"
    if ("emulator_validated" in words) != passed:
        errors.append(f"emulator_validated present={('emulator_validated' in words)} but the run report passed={passed}")
    for L, g in man["phys_grade"].items():
        py = physgrade.grade_of_artifact(adir, tpath, L)
        if canonical(py) != canonical(g):
            errors.append(f"phys_grade at L={L}: manifest {canonical(g)[:160]} differs from Python {canonical(py)[:160]}")
    # regeneration
    lat = [L for L in man["ff_latency_ns"] if L != "0"]
    lat = lat[0] if lat else "0"
    with tempfile.TemporaryDirectory() as tmp:
        p = subprocess.run([a.cqr, "hw", "certify", "--cert", ldir, "--artifact", adir, "--target", tpath,
                            "--ff-latency", lat, "--out", tmp], capture_output=True, text=True, encoding="utf-8")
        if p.returncode != 0:
            errors.append(f"cqr hw certify failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
        else:
            for f in ("PhysCert.lean", "physical.qasm", "manifest.json"):
                if open(os.path.join(tmp, f), "rb").read() != open(os.path.join(cdir, f), "rb").read():
                    errors.append(f"{f} differs from the regenerated file")
    # parse back
    try:
        got = qasm_ops(open(os.path.join(cdir, "physical.qasm"), encoding="utf-8").read())
        exp = flat_json_ops(json.load(open(os.path.join(adir, "physical.json"), encoding="utf-8")))
        if len(got) != len(exp):
            errors.append(f"physical.qasm parses to {len(got)} ops, the artifact has {len(exp)}")
        else:
            bad = [i for i, (x, y) in enumerate(zip(got, exp)) if not same_op(x, y)]
            if bad:
                errors.append(f"physical.qasm differs from physical.json at ops {bad[:5]}: {got[bad[0]]} vs {exp[bad[0]]}")
    except Exception as e:  # noqa: BLE001
        errors.append(f"physical.qasm does not parse: {e}")
    for e in errors:
        print("hw_physcert_check: " + e)
    if errors:
        return 1
    print(f"hw_physcert_check: {man['certificate']}: hashes, status words, grades, regeneration and QASM parse-back ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
