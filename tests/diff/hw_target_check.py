"""Hardware target check (Stage 24a; PHASE2_SPEC §C.1; report §3.1.3, §5.3). Run with the
.venv-hw Python (qiskit, qiskit-aer, qiskit-ibm-runtime pinned by hw/requirements.lock).

  * every committed target in hw/targets/ validates against docs/hardware_target.schema.json
    (a built-in validator for the subset of JSON Schema the file uses; `jsonschema` too when it
    is importable);
  * re-extracting each target from its fake backend (`source.class`, with `source.variant`)
    gives byte-identical JSON — the fake data is fixed in the package version;
  * `snapshot.hash` equals hashlib's SHA3-256 of the canonical `calibration`;
  * `cqr hw capabilities` on each target prints the expected `uncompute modes` line and
    `snapshot hash ok` and exits 0 — Lean's canonical form and SHA3 agree with Python's;
  * a copy with one calibration digit changed: exit 1 and `snapshot hash mismatch`;
    a missing file: exit 2; `cqr hw` alone: exit 2.

Usage: python -I tests/diff/hw_target_check.py --cqr <path to cqr> [--targets hw/targets]
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import target as hwt  # noqa: E402

fails = 0


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


# --- a small JSON Schema validator (draft 2020-12 subset used by hardware_target.schema.json)

def validate(schema, inst, root, path="$"):
    """Returns the list of violations."""
    errs = []
    if "$ref" in schema:
        ref = schema["$ref"]
        assert ref.startswith("#/$defs/"), ref
        return validate(root["$defs"][ref[len("#/$defs/"):]], inst, root, path)
    if "const" in schema and inst != schema["const"]:
        errs.append(f"{path}: expected {schema['const']!r}")
    if "enum" in schema and inst not in schema["enum"]:
        errs.append(f"{path}: not in {schema['enum']}")
    if "oneOf" in schema:
        n = sum(1 for s in schema["oneOf"] if not validate(s, inst, root, path))
        if n != 1:
            errs.append(f"{path}: oneOf matched {n} alternatives")
    t = schema.get("type")
    if t is not None:
        ok = {"object": lambda v: isinstance(v, dict), "array": lambda v: isinstance(v, list),
              "string": lambda v: isinstance(v, str), "null": lambda v: v is None,
              "boolean": lambda v: isinstance(v, bool),
              "integer": lambda v: isinstance(v, int) and not isinstance(v, bool),
              "number": lambda v: isinstance(v, (int, float)) and not isinstance(v, bool)}[t](inst)
        if not ok:
            return errs + [f"{path}: not of type {t}"]
    if isinstance(inst, str):
        if "minLength" in schema and len(inst) < schema["minLength"]:
            errs.append(f"{path}: shorter than {schema['minLength']}")
        if "pattern" in schema and not re.search(schema["pattern"], inst):
            errs.append(f"{path}: {inst!r} does not match {schema['pattern']}")
    if isinstance(inst, (int, float)) and not isinstance(inst, bool):
        if "minimum" in schema and inst < schema["minimum"]:
            errs.append(f"{path}: below {schema['minimum']}")
    if isinstance(inst, list):
        if "minItems" in schema and len(inst) < schema["minItems"]:
            errs.append(f"{path}: fewer than {schema['minItems']} items")
        if "maxItems" in schema and len(inst) > schema["maxItems"]:
            errs.append(f"{path}: more than {schema['maxItems']} items")
        if schema.get("uniqueItems") and len({json.dumps(x, sort_keys=True) for x in inst}) != len(inst):
            errs.append(f"{path}: items not unique")
        if "items" in schema:
            for i, x in enumerate(inst):
                errs += validate(schema["items"], x, root, f"{path}[{i}]")
    if isinstance(inst, dict):
        for k in schema.get("required", []):
            if k not in inst:
                errs.append(f"{path}: missing {k}")
        props = schema.get("properties", {})
        pats = schema.get("patternProperties", {})
        for k, v in inst.items():
            matched = False
            if k in props:
                matched = True
                errs += validate(props[k], v, root, f"{path}.{k}")
            for pat, sub in pats.items():
                if re.search(pat, k):
                    matched = True
                    errs += validate(sub, v, root, f"{path}.{k}")
            if not matched:
                ap = schema.get("additionalProperties", True)
                if ap is False:
                    errs.append(f"{path}: unexpected key {k}")
                elif isinstance(ap, dict):
                    errs += validate(ap, v, root, f"{path}.{k}")
    return errs


def run_cqr(cqr, *args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True)
    return p.returncode, p.stdout.replace("\r", ""), p.stderr.replace("\r", "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--targets", default=os.path.join(ROOT, "hw", "targets"))
    a = ap.parse_args()
    schema = json.load(open(os.path.join(ROOT, "docs", "hardware_target.schema.json"), encoding="utf-8"))
    try:
        import jsonschema
    except ImportError:
        jsonschema = None
        print("note  jsonschema not importable here; the built-in validator only")
    files = sorted(glob.glob(os.path.join(a.targets, "*.json")))
    check(len(files) >= 2, f"{len(files)} committed targets in {a.targets}")
    for f in files:
        base = os.path.basename(f)
        raw = open(f, "rb").read()
        t = json.loads(raw.decode("utf-8"))
        errs = validate(schema, t, schema)
        check(not errs, f"{base}: schema (built-in validator){'; ' + '; '.join(errs[:3]) if errs else ''}")
        if jsonschema is not None:
            try:
                jsonschema.validate(t, schema)
                check(True, f"{base}: schema (jsonschema)")
            except jsonschema.ValidationError as e:
                check(False, f"{base}: schema (jsonschema): {e.message}")
        check(raw == hwt.render(t).encode("utf-8"), f"{base}: file is in the canonical form")
        check(t["snapshot"]["hash"] == hwt.calibration_hash(t["calibration"]),
              f"{base}: snapshot.hash = sha3_256(canonical calibration)")
        cls = t["source"]["class"].rsplit(".", 1)[1]
        again = hwt.render(hwt.extract(hwt.fake_backend(cls),
                                       feed_forward_off=t["source"].get("variant") == "feed_forward_off"))
        check(again.encode("utf-8") == raw, f"{base}: re-extraction from {cls} byte-identical")
        caps = t["capabilities"]
        modes = "mbu, coherent" if caps["mid_circuit_measurement"]["value"] and caps["feed_forward"]["value"] else "coherent"
        rc, out, err = run_cqr(a.cqr, "hw", "capabilities", f)
        check(rc == 0 and "snapshot hash ok" in out and f"uncompute modes: {modes}" in out
              and f"name: {t['name']}" in out,
              f"{base}: cqr hw capabilities exit {rc}, modes `{modes}`, hash ok (Lean = Python)")
        for k in ("mid_circuit_measurement", "feed_forward", "reset"):
            check(f"{k}: {str(caps[k]['value']).lower()} (source: {caps[k]['source']})" in out,
                  f"{base}: flag {k} with its source printed")
        # a corrupted calibration number
        cal = hwt.canonical(t["calibration"])
        m = re.search(r'"(\d\.\d+|\d(?:\.\d+)?e-\d+)"', cal)
        check(m is not None, f"{base}: a calibration number to corrupt")
        if m:
            num = m.group(1)
            bad = num[:-1] + ("1" if num[-1] != "1" else "2")
            text = raw.decode("utf-8").replace(f'"{num}"', f'"{bad}"', 1)
            with tempfile.TemporaryDirectory() as d:
                bp = os.path.join(d, base)
                open(bp, "w", encoding="utf-8", newline="\n").write(text)
                rc, out, err = run_cqr(a.cqr, "hw", "capabilities", bp)
                check(rc == 1 and "snapshot hash mismatch" in out,
                      f"{base}: corrupted {num} -> {bad}: exit {rc}, mismatch reported")
    rc, out, err = run_cqr(a.cqr, "hw", "capabilities", os.path.join(a.targets, "no_such_target.json"))
    check(rc == 2 and "cqr hw capabilities:" in err, f"missing file: exit {rc}")
    rc, out, err = run_cqr(a.cqr, "hw")
    check(rc == 2 and "hw capabilities <target.json>" in err, f"`cqr hw` alone: exit {rc}, usage lists hw capabilities")
    print(f"hw_target_check: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
