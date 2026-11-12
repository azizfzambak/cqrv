"""Certificate JSON schema v1.9.0 (report §8.4.2, §8.4.4, §9.5.3; Stage 8a, reviewer
decisions 2 and 3; Stage 8b: theorem, obligations, machine fields; Stage 8b review:
trust_boundary.front_end; Stage 9b: front_end after the exhaustive front-end validation;
Stage 11b: the optional object `hardware`, present iff schema_version is "1.4.0"; Stage 12d:
the optional field `diffusion_shape`, present iff schema_version is "1.5.0"; Stage 14a: the
required object `solution_count` {value, status}, present iff schema_version is "1.6.0", under
which `hardware` and `diffusion_shape` are optional; Stage 15b: `uncompute` on coherent
certificates only, "1.7.0"; Stage 16b: "1.8.0" — `uncompute` required in every certificate and
trust_boundary.front_end the proved wording, tied to the version; Stage 17b: "1.9.0" — the
required object `grade_ext` {two_qubit, t_depth, rot, meas, ff}, present iff "1.9.0").

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
  * Stage 11b: an envelope with a `hardware` object validates (also with p_bar null); a legacy
    "1.4.0" one too; `hardware` under "1.3.0", "1.4.0" without `hardware`, and malformed
    `hardware` objects are rejected.
  * Stage 12d: diffusion_shape "few:log" validates, with and without `hardware`; a legacy "1.5.0"
    one too; diffusion_shape under "1.3.0" / "1.4.0", "1.5.0" without it, and diffusion_shape
    "tree" or free text are rejected.
  * Stage 14a: solution_count {32, hypothesis}; a kernel_decided audited envelope validates;
    "1.6.0" without solution_count, solution_count under "1.5.0", kernel_decided while "not yet
    audited", an unknown status word and a malformed object are rejected; legacy envelopes
    (1.3.0 / 1.4.0 + hardware / 1.5.0 + diffusion_shape, without solution_count) still validate.
  * Stage 15b: a "1.7.0" envelope with uncompute "coherent" (the Stage 9b wording) validates, with
    and without hardware, audited; uncompute under "1.6.0" / "1.5.0", "1.7.0" without uncompute or
    without solution_count, and a free-text mode are rejected.
  * Stage 16b: "1.8.0" (now legacy: the sample without grade_ext) with uncompute "coherent",
    audited, with hardware and diffusion_shape validates; "1.8.0" with the Stage 9b or Stage 8b
    front_end wording, and the proved wording under "1.7.0" / "1.6.0" are rejected; the 1.6.0 and
    1.7.0 envelopes above (old wording, uncompute as before) still validate.
  * Stage 17b: the sample says schema_version "1.9.0" with grade_ext {126, 39, 0, 18, 36}
    (two_qubit, t_depth, rot, meas, ff of the running example), uncompute "mbu" and the proved
    front_end wording; "1.9.0" with uncompute "coherent", audited, with hardware and
    diffusion_shape validates; "1.9.0" without grade_ext or without uncompute, grade_ext under
    "1.8.0", a negative, missing or non-integer component and an extra key are rejected
    (39.0 is an integer to JSON Schema).
  * Stage 20b3 (schema v1.10.0, PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3" (5)): the
    committed counting certificate examples/certs/grover_pred_037_count/certificate.json
    (pattern "Count", instance {n, M, m, kmax}, spec.epsilon / delta as {expr, approx}, grade_kind
    "composed_bound", grade_ext with t_depth_kind "bound", blocks) validates; the sample and every
    legacy Grover envelope still validate; rejected: a Count envelope without grade_kind, with
    grade_kind "measured", with spec.epsilon a bare number or a rational string, with an extra key
    in instance, with a blocks entry without multiplicity, under "1.9.0", without blocks, with
    solution_count.status "hypothesis"; and a Grover envelope with grade_kind, with blocks, or
    under "1.10.0".

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
COUNT_CERT = os.path.join(ROOT, "examples", "certs", "grover_pred_037_count", "certificate.json")

# the three front_end wordings (Stage 8b for n > 16; Stage 9b after the exhaustive validation;
# Stage 16b, the proved front end)
TRUST_8B = "DSL → network (toNetwork) unverified; predicate_hash binds the source"
VALIDATED_8 = ("DSL → network: exhaustively validated (2^8 inputs) by the unverified evaluator; "
               "not kernel-checked")
PROVED = ("DSL typed term → network: proved (toNetwork_pred; kernel-checked net_ok and front_end in "
          "Cert.lean); parser, surface checker and the typed-term printer unverified; "
          "predicate_hash binds the source")


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
    assert cert["trust_boundary"]["front_end"] == PROVED, cert["trust_boundary"]
    assert cert["theorem"] is None and cert["obligations"] == []
    assert cert["reference_configuration"]["kernel_check"] is None
    assert cert["schema_version"] == "1.9.0", cert["schema_version"]
    assert cert["uncompute"] == "mbu", cert.get("uncompute")
    assert cert["solution_count"] == {"value": 32, "status": "hypothesis"}, cert["solution_count"]
    assert cert["hypotheses"][0] == "solution_count = 32 (hM_card, supplied, not decided)"
    # Stage 17b: the second record of the running example (Stage 17a measurement)
    assert cert["grade_ext"] == {"two_qubit": 126, "t_depth": 39, "rot": 0, "meas": 18, "ff": 36}, \
        cert["grade_ext"]
    print("ok:   delta 7/128, grade (15, 134, 72, 7), grade_ext (2Q 126, T-depth 39, rot 0, meas 18, "
          "ff 36), status 'not yet audited'; schema_version 1.9.0, uncompute mbu, front_end = the "
          "proved wording")

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

    def legacy(c, version):
        """The sample as a certificate of a version before 1.9.0 (Stage 17b): no `grade_ext`; before
        1.8.0 (Stage 16b) also no `uncompute` (1.7.0 adds it back for coherent ones) and the
        Stage 9b front_end wording."""
        c.update(schema_version=version)
        c.pop("grade_ext", None)
        if version != "1.8.0":
            c.pop("uncompute", None)
            c["trust_boundary"]["front_end"] = VALIDATED_8

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
    validator.validate(mutated(lambda c: (legacy(c, "1.3.0"), c.pop("solution_count"))))
    with_obl = mutated(lambda c: (audited(c, "certificate with tracked obligations"),
                                  c.update(obligations=["lemma_6_3_2_xor"],
                                           axioms=["propext", "sorryAx"])))
    validator.validate(with_obl)
    # the Stage 8b wording (n > 16) under a pre-16b version
    validator.validate(mutated(lambda c: (legacy(c, "1.6.0"),
                                          c["trust_boundary"].update(front_end=TRUST_8B))))
    print("ok:   filled-in 'certified' and 'certificate with tracked obligations' envelopes "
          "validate; the Stage 8b front_end wording (n > 16) validates under 1.6.0")
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
        "old schema version": mutated(lambda c: legacy(c, "1.2.0")),
        "front_end with n = 17 validated": mutated(lambda c: (legacy(c, "1.6.0"),
            c["trust_boundary"].update(
            front_end="DSL → network: exhaustively validated (2^17 inputs) by the unverified "
                      "evaluator; not kernel-checked"))),
        "front_end free text": mutated(lambda c: c["trust_boundary"].update(front_end="verified")),
        "missing front_end": mutated(lambda c: c["trust_boundary"].pop("front_end")),
        # Stage 14a
        "1.6.0 without solution_count": mutated(lambda c: (legacy(c, "1.6.0"),
                                                           c.pop("solution_count"))),
        "solution_count under 1.3.0": mutated(lambda c: legacy(c, "1.3.0")),
        "kernel_decided while not yet audited":
            mutated(lambda c: c["solution_count"].update(status="kernel_decided")),
        "solution_count unknown status":
            mutated(lambda c: c["solution_count"].update(status="decided")),
        "solution_count without value": mutated(lambda c: c["solution_count"].pop("value")),
        "solution_count negative value": mutated(lambda c: c["solution_count"].update(value=-1)),
        "solution_count extra key": mutated(lambda c: c["solution_count"].update(by="kernel")),
        # Stage 16b (1.8.0 legacy) and Stage 17b (1.9.0)
        "1.9.0 without uncompute": mutated(lambda c: c.pop("uncompute")),
        "1.8.0 without uncompute": mutated(lambda c: (legacy(c, "1.8.0"), c.pop("uncompute"))),
        "1.9.0 with the Stage 9b front_end wording":
            mutated(lambda c: c["trust_boundary"].update(front_end=VALIDATED_8)),
        "1.8.0 with the Stage 9b front_end wording":
            mutated(lambda c: (legacy(c, "1.8.0"), c["trust_boundary"].update(front_end=VALIDATED_8))),
        "1.9.0 with the Stage 8b front_end wording":
            mutated(lambda c: c["trust_boundary"].update(front_end=TRUST_8B)),
        "the proved wording under 1.7.0":
            mutated(lambda c: (c.update(schema_version="1.7.0", uncompute="coherent"),
                               c.pop("grade_ext"))),
        "the proved wording under 1.6.0":
            mutated(lambda c: (c.update(schema_version="1.6.0"), c.pop("uncompute"),
                               c.pop("grade_ext"))),
        # Stage 17b: grade_ext present iff 1.9.0, five natural components, nothing else
        "1.9.0 without grade_ext": mutated(lambda c: c.pop("grade_ext")),
        "grade_ext under 1.8.0":
            mutated(lambda c: (legacy(c, "1.8.0"), c.update(grade_ext=copy.deepcopy(cert["grade_ext"])))),
        "grade_ext under 1.7.0":
            mutated(lambda c: (legacy(c, "1.7.0"), c.update(uncompute="coherent",
                                                            grade_ext=copy.deepcopy(cert["grade_ext"])))),
        "grade_ext negative component": mutated(lambda c: c["grade_ext"].update(rot=-1)),
        "grade_ext missing component": mutated(lambda c: c["grade_ext"].pop("t_depth")),
        "grade_ext non-integer component": mutated(lambda c: c["grade_ext"].update(t_depth=39.5)),
        "grade_ext string component": mutated(lambda c: c["grade_ext"].update(meas="18")),
        "grade_ext extra key": mutated(lambda c: c["grade_ext"].update(t_count=72)),
        "grade_ext not an object": mutated(lambda c: c.update(grade_ext=[126, 39, 0, 18, 36])),
    })
    # Stage 17b: 1.8.0 envelopes (no grade_ext) still validate, audited and coherent too
    validator.validate(mutated(lambda c: legacy(c, "1.8.0")))
    validator.validate(mutated(lambda c: (audited(c), legacy(c, "1.8.0"), c.update(uncompute="coherent"))))
    print("ok:   schema v1.8.0 (legacy, no grade_ext): the sample and an audited coherent envelope "
          "validate")
    hw = {"profile": "illustrative_sc", "profile_hash": "0" * 64,
          "components": {"w": {"required": 15, "budget": 127, "fits": True},
                         "d": {"required": 230, "budget": 200, "fits": False},
                         "t": {"required": 72, "budget": None, "fits": True},
                         "a": {"required": 7, "budget": 127, "fits": True}},
          "fits": False, "G": 390, "p_bar": "1/100", "delta_hw": "2531/640", "vacuous": True,
          "note": "routing, native gates and calibration are outside the trust boundary"}

    def with_hw(f=lambda h: None, version="1.9.0", no_count=False):
        def g(c):
            h = copy.deepcopy(hw)
            f(h)
            if version != "1.9.0":
                legacy(c, version)
            if no_count:
                c.pop("solution_count")
            c["hardware"] = h
        return mutated(g)

    validator.validate(with_hw())
    validator.validate(with_hw(lambda h: h.update(p_bar=None, delta_hw=None, vacuous=None)))
    validator.validate(with_hw(version="1.8.0"))
    validator.validate(with_hw(version="1.6.0"))
    validator.validate(with_hw(version="1.4.0", no_count=True))
    print("ok:   schema v1.9.0: an envelope with `hardware` validates (also without p_bar); "
          "legacy v1.8.0, v1.6.0 and v1.4.0 ones too")
    bad.update({
        "hardware under 1.3.0": with_hw(version="1.3.0", no_count=True),
        "1.4.0 without hardware": mutated(lambda c: (legacy(c, "1.4.0"), c.pop("solution_count"))),
        "hardware under 1.4.0 with solution_count": with_hw(version="1.4.0"),
        "hardware without note": with_hw(lambda h: h.pop("note")),
        "hardware note free text": with_hw(lambda h: h.update(note="calibrated")),
        "hardware float delta_hw": with_hw(lambda h: h.update(delta_hw="3.95")),
        "hardware component without budget": with_hw(lambda h: h["components"]["d"].pop("budget")),
        "hardware extra component": with_hw(lambda h: h["components"].update(
            x={"required": 1, "budget": 1, "fits": True})),
        "hardware short profile hash": with_hw(lambda h: h.update(profile_hash="abc")),
    })

    def with_shape(shape="few:log", version="1.9.0", hardware=False, no_count=False):
        def g(c):
            if version != "1.9.0":
                legacy(c, version)
            if hardware:
                c.update(hardware=copy.deepcopy(hw))
            c.update(diffusion_shape=shape)
            if no_count:
                c.pop("solution_count")
        return mutated(g)

    validator.validate(with_shape())
    validator.validate(with_shape(hardware=True))
    validator.validate(with_shape(version="1.8.0"))
    validator.validate(with_shape(version="1.6.0"))
    validator.validate(with_shape(version="1.5.0", no_count=True))
    print("ok:   schema v1.9.0: diffusion_shape few:log validates (with and without hardware); "
          "legacy v1.8.0, v1.6.0 and v1.5.0 ones too")
    bad.update({
        "diffusion_shape under 1.3.0": with_shape(version="1.3.0", no_count=True),
        "diffusion_shape under 1.4.0": with_shape(version="1.4.0", hardware=True, no_count=True),
        "1.5.0 without diffusion_shape": mutated(lambda c: (legacy(c, "1.5.0"),
                                                            c.pop("solution_count"))),
        "diffusion_shape under 1.5.0 with solution_count": with_shape(version="1.5.0"),
        "diffusion_shape tree": with_shape(shape="tree"),
        "diffusion_shape free text": with_shape(shape="few:ladder"),
    })
    # Stage 15b: a 1.7.0 envelope — `uncompute` on coherent certificates only, the Stage 9b wording
    def with_unc(mode="coherent", version="1.7.0", hardware=False):
        def g(c):
            if version != "1.9.0":
                legacy(c, version)
            c.update(uncompute=mode)
            if hardware:
                c["hardware"] = copy.deepcopy(hw)
        return mutated(g)
    validator.validate(with_unc())
    validator.validate(with_unc(hardware=True))
    validator.validate(with_unc(mode="mbu"))
    validator.validate(mutated(lambda c: (audited(c), legacy(c, "1.7.0"),
                                          c.update(uncompute="coherent"))))
    print("ok:   schema v1.7.0 (legacy): uncompute coherent validates (with and without hardware, "
          "audited)")
    bad.update({
        "uncompute under 1.6.0": with_unc(version="1.6.0"),
        "uncompute under 1.5.0 (with diffusion_shape)": mutated(lambda c: (legacy(c, "1.5.0"),
            c.update(diffusion_shape="few:log", uncompute="coherent"))),
        "1.7.0 without uncompute": mutated(lambda c: legacy(c, "1.7.0")),
        "1.7.0 without solution_count": mutated(lambda c: (legacy(c, "1.7.0"),
            c.update(uncompute="coherent"), c.pop("solution_count"))),
        "uncompute free text under 1.7.0": with_unc(mode="adjoint"),
        "uncompute free text under 1.8.0": with_unc(mode="adjoint", version="1.8.0"),
        "uncompute free text under 1.9.0": with_unc(mode="adjoint", version="1.9.0"),
    })
    # Stage 16b / 17b: 1.8.0 and 1.9.0 with uncompute coherent, audited, with hardware and
    # diffusion_shape
    validator.validate(with_unc(version="1.8.0"))
    validator.validate(with_unc(version="1.9.0"))
    validator.validate(mutated(lambda c: (audited(c), c.update(uncompute="coherent"))))
    validator.validate(mutated(lambda c: c.update(hardware=copy.deepcopy(hw),
                                                  diffusion_shape="few:log")))
    print("ok:   schema v1.9.0: uncompute coherent validates (audited too); hardware and "
          "diffusion_shape under 1.9.0 validate")
    # Stage 20b3: the Count branch of 1.10.0 on the committed counting certificate
    with open(COUNT_CERT, encoding="utf-8") as f:
        count = json.load(f)
    validator.validate(count)
    assert count["schema_version"] == "1.10.0" and count["pattern"] == "Count", count["pattern"]
    assert count["grade_kind"] == "composed_bound" and count["grade_ext"]["t_depth_kind"] == "bound"
    assert set(count["instance"]) == {"n", "M", "m", "kmax"} and count["instance"]["kmax"] is None
    assert set(count["spec"]) == {"epsilon", "delta", "estimate"}
    assert all(set(count["spec"][k]) == {"expr", "approx"} and isinstance(count["spec"][k]["approx"], float)
               for k in ("epsilon", "delta")), count["spec"]
    assert [b["name"] for b in count["blocks"]] == ["h_layer", "cg_0", "cg_1", "cg_2", "cg_3", "inverse"]
    print("ok:   schema v1.10.0: the committed counting certificate (pattern Count, instance {n, M, m, "
          "kmax}, real epsilon / delta as {expr, approx}, grade_kind composed_bound, t_depth a bound, "
          "6 blocks) validates")

    def mutated_count(f):
        c = copy.deepcopy(count)
        f(c)
        return c

    bad.update({
        "Count without grade_kind": mutated_count(lambda c: c.pop("grade_kind")),
        "Count with grade_kind measured": mutated_count(lambda c: c.update(grade_kind="measured")),
        "Count epsilon a bare number": mutated_count(lambda c: c["spec"].update(epsilon=0.168426)),
        "Count epsilon a rational string": mutated_count(lambda c: c["spec"].update(epsilon="7/128")),
        "Count extra key in instance": mutated_count(lambda c: c["instance"].update(r=2)),
        "Count block without multiplicity": mutated_count(lambda c: c["blocks"][1].pop("multiplicity")),
        "Count under 1.9.0": mutated_count(lambda c: c.update(schema_version="1.9.0")),
        "Count without blocks": mutated_count(lambda c: c.pop("blocks")),
        "Count with solution_count hypothesis":
            mutated_count(lambda c: c["solution_count"].update(status="hypothesis")),
        "Count without t_depth_kind": mutated_count(lambda c: c["grade_ext"].pop("t_depth_kind")),
        "Count delta as rational string": mutated_count(lambda c: c["spec"].update(delta="7/128")),
        "Grover with grade_kind": mutated(lambda c: c.update(grade_kind="measured")),
        "Grover with blocks": mutated(lambda c: c.update(blocks=[])),
        "Grover under 1.10.0": mutated(lambda c: c.update(schema_version="1.10.0")),
        "Grover 1.10.0 with the Count fields but pattern Grover":
            mutated_count(lambda c: c.update(pattern="Grover")),
    })
    for label, c in bad.items():
        if validator.is_valid(c):
            raise AssertionError(f"schema accepts a bad envelope: {label}")
    print(f"ok:   {len(bad)} mutated envelopes rejected (15 of them the Count branch of Stage 20b3)")
    print("cert_schema: all checks passed")


if __name__ == "__main__":
    main()
