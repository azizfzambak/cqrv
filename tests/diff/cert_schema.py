"""Certificate JSON schema v1.1.0 (report §8.4.2, §8.4.4, §9.5.3; Stage 8a, reviewer
decisions 2 and 3; Stage 8b: theorem, obligations, machine fields).

Builds the Stage 8a certificate of examples/grover_pred_037.cqr in Lean (scripts/CertifyTool.lean
`sample`: no kernel check, no axiom audit) and checks that
  * it validates against docs/certificate.schema.json (JSON Schema draft 2020-12);
  * delta = "7/128", success_probability = "121/128", grade = (15, 230, 72, 7),
    status = "not yet audited", proof hash null, axioms empty;
  * the predicate hash is SHA3-256 of the source with LF line endings, and the circuit hash is
    SHA3-256 of the compact sorted-key JSON of the circuit of `cqr synthesize --grover
    --iterations 2 --json` (hashlib as the test oracle);
  * mutated envelopes (wrong status, float delta, missing field, extra field, a status other
    than "not yet audited" without the Stage 8b fields) are rejected;
  * Stage 8b status rules: a filled-in "certified" envelope validates; "certified" with an
    obligation or with sorryAx, "certificate with tracked obligations" without obligations, and
    "not yet audited" with a theorem or a kernel_check are rejected. (The certificates written by
    `cqr certify` are checked by tests/diff/certify_check.py.)

Usage: python -I tests/diff/cert_schema.py --cqr <path to cqr>   (after `lake build`)
"""

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys

import jsonschema

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import ROOT, certify_tool  # noqa: E402

SRC = os.path.join("examples", "grover_pred_037.cqr")
SCHEMA = os.path.join(ROOT, "docs", "certificate.schema.json")


def sha3(b):
    return hashlib.sha3_256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    args = ap.parse_args()
    with open(SCHEMA, encoding="utf-8") as f:
        schema = json.load(f)
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)

    cert = json.loads(certify_tool(["sample", SRC]))
    validator.validate(cert)
    print("ok:   sample certificate validates against docs/certificate.schema.json")

    assert cert["spec"] == {"epsilon": "0", "delta": "7/128", "success_probability": "121/128"}
    assert cert["grade"] == {"w": 15, "d": 230, "t": 72, "a": 7}, cert["grade"]
    assert cert["instance"] == {"n": 8, "M": 32, "r": 2}, cert["instance"]
    assert cert["status"] == "not yet audited" and cert["axioms"] == []
    assert cert["hashes"]["proof"] is None
    assert cert["theorem"] is None and cert["obligations"] == []
    assert cert["reference_configuration"]["kernel_check"] is None
    print("ok:   delta 7/128, grade (15, 230, 72, 7), status 'not yet audited'")

    with open(os.path.join(ROOT, SRC), "rb") as f:
        src = f.read().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    assert cert["hashes"]["predicate"] == sha3(src), "predicate hash"
    p = subprocess.run([args.cqr, "synthesize", os.path.join(ROOT, SRC), "--grover",
                        "--iterations", "2", "--json"], capture_output=True, text=True,
                       encoding="utf-8", check=True)
    circ = json.loads(p.stdout)["circuit"]
    canon = json.dumps(circ, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    assert cert["hashes"]["circuit"] == sha3(canon.encode("utf-8")), "circuit hash"
    gates = circ["gates"]
    counts = {
        "unitary": sum(1 for g in gates
                       if g["op"] not in ("alloc", "free", "measure") and "if" not in g),
        "mid_circuit_measurements": sum(1 for g in gates if g["op"] == "measure"),
        "classically_controlled": sum(1 for g in gates if "if" in g),
        "terminal_measurements": circ["n_data"],
    }
    hp = cert["hardware_perturbation"]
    assert hp["counts"] == counts, (hp["counts"], counts)
    assert hp["G"] == sum(counts.values()), hp
    print(f"ok:   predicate and circuit hashes agree with hashlib; G = {hp['G']} = "
          f"{counts['unitary']} unitary + {counts['mid_circuit_measurements']} mid-circuit "
          f"measurements + {counts['classically_controlled']} classically controlled + "
          f"{counts['terminal_measurements']} terminal measurements")

    def mutated(f):
        c = copy.deepcopy(cert)
        f(c)
        return c

    bad = {
        "unknown status": mutated(lambda c: c.update(status="bogus")),
        "float delta": mutated(lambda c: c["spec"].update(delta="0.0546875")),
        "missing grade": mutated(lambda c: c.pop("grade")),
        "extra field": mutated(lambda c: c.update(note="x")),
        "audited status without proof hash": mutated(lambda c: c.update(status="certificate with tracked obligations")),
        "short hash": mutated(lambda c: c["hashes"].update(circuit="abc")),
        "missing counts": mutated(lambda c: c["hardware_perturbation"].pop("counts")),
        "incomplete counts": mutated(lambda c: c["hardware_perturbation"]["counts"].pop("terminal_measurements")),
    }
    def audited(c, status="certified"):
        c.update(status=status, theorem="CQRV.Cert.grover_pred_037.cert",
                 axioms=["propext", "Classical.choice", "Quot.sound"])
        c["hashes"]["proof"] = "0" * 64
        c["reference_configuration"].update(
            cpu="test cpu", kernel_check={"wall_ms": 1, "kernel_ms": 1, "runs": 1,
                                          "statistic": "single run"})

    certified = mutated(audited)
    validator.validate(certified)
    with_obl = mutated(lambda c: (audited(c, "certificate with tracked obligations"),
                                  c.update(obligations=["lemma_6_3_2_xor"],
                                           axioms=["propext", "sorryAx"])))
    validator.validate(with_obl)
    print("ok:   filled-in 'certified' and 'certificate with tracked obligations' envelopes validate")
    bad.update({
        "certified with an obligation":
            mutated(lambda c: (audited(c), c.update(obligations=["lemma_6_3_2_xor"]))),
        "certified with sorryAx":
            mutated(lambda c: (audited(c), c.update(axioms=["propext", "sorryAx"]))),
        "certified without theorem": mutated(lambda c: (audited(c), c.update(theorem=None))),
        "certified without kernel_check":
            mutated(lambda c: (audited(c), c["reference_configuration"].update(kernel_check=None))),
        "tracked obligations without obligations":
            mutated(lambda c: audited(c, "certificate with tracked obligations")),
        "not yet audited with theorem": mutated(lambda c: c.update(theorem="x")),
        "not yet audited with obligations": mutated(lambda c: c.update(obligations=["x"])),
        "old schema version": mutated(lambda c: c.update(schema_version="1.0.0")),
    })
    for label, c in bad.items():
        if validator.is_valid(c):
            raise AssertionError(f"schema accepts a bad envelope: {label}")
    print(f"ok:   {len(bad)} mutated envelopes rejected")
    print("cert_schema: all checks passed")


if __name__ == "__main__":
    main()
