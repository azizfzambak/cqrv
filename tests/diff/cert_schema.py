"""Certificate JSON schema v1.6.0 (report §8.4.2, §8.4.4, §9.5.3; Stage 8a, reviewer
decisions 2 and 3; Stage 8b: theorem, obligations, machine fields; Stage 8b review:
trust_boundary.front_end; Stage 9b: front_end after the exhaustive front-end validation;
Stage 11b: the optional object `hardware`, present iff schema_version is "1.4.0"; Stage 12d:
the optional field `diffusion_shape`, present iff schema_version is "1.5.0"; Stage 14a: the
required object `solution_count` {value, status}, present iff schema_version is "1.6.0", under
which `hardware` and `diffusion_shape` are optional).

Builds the Stage 8a certificate of examples/grover_pred_037.cqr in Lean (scripts/CertifyTool.lean
`sample`: no kernel check, no axiom audit) and checks that
  * it validates against docs/certificate.schema.json (JSON Schema draft 2020-12);
  * delta = "7/128", success_probability = "121/128", grade = (15, 134, 72, 7) (tree diffusion, Stage 12a),
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
  * Stage 11b: the sample with a `hardware` object and schema_version "1.4.0" validates (also
    with p_bar null); `hardware` under "1.3.0", "1.4.0" without `hardware`, and malformed
    `hardware` objects are rejected.
  * Stage 12d: diffusion_shape "few:log" with schema_version "1.5.0" validates, with and
    without `hardware`; diffusion_shape under "1.3.0" / "1.4.0", "1.5.0" without it, and
    diffusion_shape "tree" or free text are rejected.
  * Stage 14a: the sample says schema_version "1.6.0" with solution_count {32, hypothesis};
    a kernel_decided audited envelope validates; "1.6.0" without solution_count, solution_count
    under "1.5.0", kernel_decided while "not yet audited", an unknown status word and a
    malformed object are rejected; legacy envelopes (1.3.0 / 1.4.0 + hardware / 1.5.0 +
    diffusion_shape, without solution_count) still validate.

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
    assert cert["grade"] == {"w": 15, "d": 134, "t": 72, "a": 7}, cert["grade"]
    assert cert["instance"] == {"n": 8, "M": 32, "r": 2}, cert["instance"]
    assert cert["status"] == "not yet audited" and cert["axioms"] == []
    assert cert["hashes"]["proof"] is None
    assert cert["trust_boundary"]["front_end"] == ("DSL → network: exhaustively validated "
        "(2^8 inputs) by the unverified evaluator; not kernel-checked")
    assert cert["theorem"] is None and cert["obligations"] == []
    assert cert["reference_configuration"]["kernel_check"] is None
    assert cert["schema_version"] == "1.6.0", cert["schema_version"]
    assert cert["solution_count"] == {"value": 32, "status": "hypothesis"}, cert["solution_count"]
    assert cert["hypotheses"][0] == "solution_count = 32 (hM_card, supplied, not decided)"
    print("ok:   delta 7/128, grade (15, 134, 72, 7), status 'not yet audited'")

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
    # Stage 14a: an audited envelope whose solution count the kernel decided
    validator.validate(mutated(lambda c: (audited(c), c["solution_count"].update(
        status="kernel_decided"), c.update(hypotheses=c["hypotheses"][1:]))))
    # legacy: a Stage 9b certificate (1.3.0, no solution_count) still validates
    validator.validate(mutated(lambda c: (c.update(schema_version="1.3.0"),
                                          c.pop("solution_count"))))
    with_obl = mutated(lambda c: (audited(c, "certificate with tracked obligations"),
                                  c.update(obligations=["lemma_6_3_2_xor"],
                                           axioms=["propext", "sorryAx"])))
    validator.validate(with_obl)
    validator.validate(mutated(lambda c: c["trust_boundary"].update(
        front_end="DSL → network (toNetwork) unverified; predicate_hash binds the source")))
    print("ok:   filled-in 'certified' and 'certificate with tracked obligations' envelopes "
          "validate; the Stage 8b front_end wording (n > 16) validates")
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
        "old schema version": mutated(lambda c: c.update(schema_version="1.2.0")),
        "front_end with n = 17 validated": mutated(lambda c: c["trust_boundary"].update(
            front_end="DSL → network: exhaustively validated (2^17 inputs) by the unverified "
                      "evaluator; not kernel-checked")),
        "front_end free text": mutated(lambda c: c["trust_boundary"].update(front_end="verified")),
        "missing front_end": mutated(lambda c: c["trust_boundary"].pop("front_end")),
        # Stage 14a
        "1.6.0 without solution_count": mutated(lambda c: c.pop("solution_count")),
        "solution_count under 1.3.0": mutated(lambda c: c.update(schema_version="1.3.0")),
        "kernel_decided while not yet audited":
            mutated(lambda c: c["solution_count"].update(status="kernel_decided")),
        "solution_count unknown status":
            mutated(lambda c: c["solution_count"].update(status="decided")),
        "solution_count without value": mutated(lambda c: c["solution_count"].pop("value")),
        "solution_count negative value": mutated(lambda c: c["solution_count"].update(value=-1)),
        "solution_count extra key": mutated(lambda c: c["solution_count"].update(by="kernel")),
    })
    hw = {"profile": "illustrative_sc", "profile_hash": "0" * 64,
          "components": {"w": {"required": 15, "budget": 127, "fits": True},
                         "d": {"required": 230, "budget": 200, "fits": False},
                         "t": {"required": 72, "budget": None, "fits": True},
                         "a": {"required": 7, "budget": 127, "fits": True}},
          "fits": False, "G": 390, "p_bar": "1/100", "delta_hw": "2531/640", "vacuous": True,
          "note": "routing, native gates and calibration are outside the trust boundary"}

    def with_hw(f=lambda h: None, version="1.6.0", legacy=False):
        def g(c):
            h = copy.deepcopy(hw)
            f(h)
            c.update(schema_version=version, hardware=h)
            if legacy:
                c.pop("solution_count")
        return mutated(g)

    validator.validate(with_hw())
    validator.validate(with_hw(lambda h: h.update(p_bar=None, delta_hw=None, vacuous=None)))
    validator.validate(with_hw(version="1.4.0", legacy=True))
    print("ok:   schema v1.6.0: an envelope with `hardware` validates (also without p_bar); "
          "a legacy v1.4.0 one too")
    bad.update({
        "hardware under 1.3.0": with_hw(version="1.3.0", legacy=True),
        "1.4.0 without hardware": mutated(lambda c: (c.update(schema_version="1.4.0"),
                                                     c.pop("solution_count"))),
        "hardware under 1.4.0 with solution_count": with_hw(version="1.4.0"),
        "hardware without note": with_hw(lambda h: h.pop("note")),
        "hardware note free text": with_hw(lambda h: h.update(note="calibrated")),
        "hardware float delta_hw": with_hw(lambda h: h.update(delta_hw="3.95")),
        "hardware component without budget": with_hw(lambda h: h["components"]["d"].pop("budget")),
        "hardware extra component": with_hw(lambda h: h["components"].update(
            x={"required": 1, "budget": 1, "fits": True})),
        "hardware short profile hash": with_hw(lambda h: h.update(profile_hash="abc")),
    })

    def with_shape(shape="few:log", version="1.6.0", hardware=False, legacy=False):
        def g(c):
            if hardware:
                c.update(hardware=copy.deepcopy(hw))
            c.update(schema_version=version, diffusion_shape=shape)
            if legacy:
                c.pop("solution_count")
        return mutated(g)

    validator.validate(with_shape())
    validator.validate(with_shape(hardware=True))
    validator.validate(with_shape(version="1.5.0", legacy=True))
    print("ok:   schema v1.6.0: diffusion_shape few:log validates (with and without hardware); "
          "a legacy v1.5.0 one too")
    bad.update({
        "diffusion_shape under 1.3.0": with_shape(version="1.3.0", legacy=True),
        "diffusion_shape under 1.4.0": with_shape(version="1.4.0", hardware=True, legacy=True),
        "1.5.0 without diffusion_shape": mutated(lambda c: (c.update(schema_version="1.5.0"),
                                                            c.pop("solution_count"))),
        "diffusion_shape under 1.5.0 with solution_count": with_shape(version="1.5.0"),
        "diffusion_shape tree": with_shape(shape="tree"),
        "diffusion_shape free text": with_shape(shape="few:ladder"),
    })
    for label, c in bad.items():
        if validator.is_valid(c):
            raise AssertionError(f"schema accepts a bad envelope: {label}")
    print(f"ok:   {len(bad)} mutated envelopes rejected")
    print("cert_schema: all checks passed")


if __name__ == "__main__":
    main()
