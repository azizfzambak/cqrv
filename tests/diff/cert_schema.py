"""Certificate JSON schema v1.0.0 (report §8.4.2, §8.4.4, §9.5.3; Stage 8a, reviewer
decisions 2 and 3).

Builds the Stage 8a certificate of examples/grover_pred_037.cqr in Lean (scripts/CertifyTool.lean
`sample`: no kernel check, no axiom audit) and checks that
  * it validates against docs/certificate.schema.json (JSON Schema draft 2020-12);
  * delta = "7/128", success_probability = "121/128", grade = (15, 230, 72, 7),
    status = "not yet audited", proof hash null, axioms empty;
  * the predicate hash is SHA3-256 of the source with LF line endings, and the circuit hash is
    SHA3-256 of the compact sorted-key JSON of the circuit of `cqr synthesize --grover
    --iterations 2 --json` (hashlib as the test oracle);
  * mutated envelopes (wrong status, float delta, missing field, extra field, a status other
    than "not yet audited" without the Stage 8b fields) are rejected.

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
    G = sum(1 for g in circ["gates"] if g["op"] not in ("alloc", "free"))
    assert cert["hardware_perturbation"]["G"] == G, (cert["hardware_perturbation"], G)
    print(f"ok:   predicate and circuit hashes agree with hashlib; G = {G}")

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
    }
    for label, c in bad.items():
        if validator.is_valid(c):
            raise AssertionError(f"schema accepts a bad envelope: {label}")
    print(f"ok:   {len(bad)} mutated envelopes rejected")
    print("cert_schema: all checks passed")


if __name__ == "__main__":
    main()
