"""Hardware profile schema v1.0.0 (report §3.1.3, §3.3.2–3.3.3, Table 3.5; Stage 11b, reviewer
decision 1).

Checks that
  * docs/profile.schema.json is a valid JSON Schema (draft 2020-12) and every file
    profiles/*.json validates against it;
  * profiles/ibm_kyiv.json has exactly the figures of report Table 3.5 / §3.3.3: budget
    (w, d, t, a) = (127, 200, null, 127), t_gate_ns = 500, t_T_ns = null (the report gives
    none), t1_ns = 100000 (T1 ≈ 100 μs), p_bar = "0.01"; its depth budget is the ρNISQ
    coherence bound T1 / t_gate; every source entry names the report;
  * mutated profiles (a missing source entry, an empty source, an unknown key, p_bar > 1,
    p_bar as a JSON number, a negative or fractional budget, a missing budget component, a
    wrong schema_version) are rejected by the schema AND by the Lean reader
    (`cqr certify … --profile <temp file>` exits 2 before writing anything, so no kernel check
    runs), as is a profile name without a file. The accepted path (`--profile ibm_kyiv`) is
    tested by tests/diff/certify_check.py.

Usage: python -I tests/diff/profile_schema.py --cqr <path to cqr>   (after `lake build`)
"""

import argparse
import copy
import glob
import json
import os
import shutil
import subprocess
import sys
import tempfile

import jsonschema

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import ROOT  # noqa: E402

SCHEMA = os.path.join(ROOT, "docs", "profile.schema.json")
KYIV = os.path.join(ROOT, "profiles", "ibm_kyiv.json")
SRC = os.path.join("examples", "grover_pred_037.cqr")


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    args = ap.parse_args()
    cqr = os.path.abspath(args.cqr)
    schema = load(SCHEMA)
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    files = sorted(glob.glob(os.path.join(ROOT, "profiles", "*.json")))
    assert files, "no profiles/*.json"
    for f in files:
        validator.validate(load(f))
        assert load(f)["name"] == os.path.basename(f)[:-len(".json")], f
    print(f"ok:   {len(files)} profile(s) validate against docs/profile.schema.json")

    kyiv = load(KYIV)
    assert kyiv["budget"] == {"w": 127, "d": 200, "t": None, "a": 127}, kyiv["budget"]
    assert (kyiv["t_gate_ns"], kyiv["t_T_ns"], kyiv["t1_ns"], kyiv["p_bar"]) == \
        (500, None, 100000, "0.01"), kyiv
    assert kyiv["budget"]["d"] == kyiv["t1_ns"] // kyiv["t_gate_ns"], "d = T1 / t_gate"
    assert all("report" in s for s in kyiv["source"].values()), kyiv["source"]
    assert "not calibration data" in kyiv["note"]
    print("ok:   ibm_kyiv = report Table 3.5 / section 3.3.3: budget (127, 200, null, 127), "
          "t_gate 500 ns, t_T null, T1 100 us (d = T1 / t_gate), p_bar 0.01")

    def mutated(f):
        c = copy.deepcopy(kyiv)
        f(c)
        return c

    bad = {
        "missing source entry": mutated(lambda c: c["source"].pop("p_bar")),
        "empty source": mutated(lambda c: c["source"].update(d="")),
        "unknown key": mutated(lambda c: c.update(t2_ns=1)),
        "unknown budget key": mutated(lambda c: c["budget"].update(q=1)),
        "p_bar > 1": mutated(lambda c: c.update(p_bar="1.5")),
        "p_bar number": mutated(lambda c: c.update(p_bar=0.01)),
        "p_bar exponent": mutated(lambda c: c.update(p_bar="1e-2")),
        "negative budget": mutated(lambda c: c["budget"].update(d=-1)),
        "fractional budget": mutated(lambda c: c["budget"].update(d=200.5)),
        "missing budget component": mutated(lambda c: c["budget"].pop("t")),
        "wrong schema_version": mutated(lambda c: c.update(schema_version="2.0.0")),
        "missing t1_ns": mutated(lambda c: c.pop("t1_ns")),
    }
    for label, c in bad.items():
        if validator.is_valid(c):
            raise AssertionError(f"schema accepts a bad profile: {label}")
    print(f"ok:   {len(bad)} mutated profiles rejected by the schema")

    tmp = tempfile.mkdtemp(prefix="cqrv-profile-")
    try:
        for label, c in bad.items():
            path = os.path.join(tmp, "p.json")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(c, f, ensure_ascii=False)
            out = os.path.join(tmp, "out")
            p = subprocess.run([cqr, "certify", SRC, "--out", out, "--profile", path],
                               cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
            assert p.returncode == 2 and "profile" in p.stderr, (label, p.returncode, p.stderr)
            assert not os.path.exists(out), f"{label}: output written for a rejected profile"
        p = subprocess.run([cqr, "certify", SRC, "--out", os.path.join(tmp, "out"),
                            "--profile", "no_such_profile"], cwd=ROOT, capture_output=True,
                           text=True, encoding="utf-8")
        assert p.returncode == 2 and "profiles/no_such_profile.json not found" in p.stderr, \
            (p.returncode, p.stderr)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print(f"ok:   the Lean reader (cqr certify --profile) rejects the same {len(bad)} profiles "
          "and a missing profile file (exit 2, nothing written)")
    print("profile_schema: all checks passed")


if __name__ == "__main__":
    main()
