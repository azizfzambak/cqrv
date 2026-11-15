"""Hardware target check (Stage 24a; PHASE2_SPEC §C.1; report §3.1.3, §5.3). Run with the
.venv-hw Python (qiskit, qiskit-aer, qiskit-ibm-runtime pinned by hw/requirements.lock).

  * every committed target in hw/targets/ validates against docs/hardware_target.schema.json — `--schema-only`,
    run with the harness venv `.venv` (jsonschema 4.26.0; Stage 24b moved the validation there,
    so `.venv-hw` needs no extra package);
  * re-extracting each target from its fake backend (`source.class`, with `source.variant`)
    gives byte-identical JSON — the fake data is fixed in the package version;
  * `snapshot.hash` equals hashlib's SHA3-256 of the canonical `calibration`;
  * `cqr hw capabilities` on each target prints the expected `uncompute modes` line and
    `snapshot hash ok` and exits 0 — Lean's canonical form and SHA3 agree with Python's;
  * a copy with one calibration digit changed: exit 1 and `snapshot hash mismatch`;
    a missing file: exit 2; `cqr hw` alone: exit 2.

Usage: python -I tests/diff/hw_target_check.py --cqr <path to cqr> [--targets hw/targets]   (.venv-hw)
       python -I tests/diff/hw_target_check.py --schema-only [--targets hw/targets]       (.venv)
"""

import argparse
import glob
import importlib.metadata
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import target as hwt  # noqa: E402  (no qiskit import at module level)

fails = 0


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


def run_cqr(cqr, *args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True)
    return p.returncode, p.stdout.replace("\r", ""), p.stderr.replace("\r", "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", help="the built cqr (the .venv-hw part of the check)")
    ap.add_argument("--schema-only", action="store_true",
                    help="only validate the targets against the schema with jsonschema (the .venv part)")
    ap.add_argument("--targets", default=os.path.join(ROOT, "hw", "targets"))
    a = ap.parse_args()
    files = sorted(glob.glob(os.path.join(a.targets, "*.json")))
    check(len(files) >= 2, f"{len(files)} committed targets in {a.targets}")
    if a.schema_only:
        import jsonschema
        schema = json.load(open(os.path.join(ROOT, "docs", "hardware_target.schema.json"), encoding="utf-8"))
        jsonschema.Draft202012Validator.check_schema(schema)
        check(True, "docs/hardware_target.schema.json is a valid draft 2020-12 schema")
        for f in files:
            t = json.load(open(f, encoding="utf-8"))
            try:
                jsonschema.validate(t, schema, cls=jsonschema.Draft202012Validator)
                check(True, f"{os.path.basename(f)}: schema (jsonschema {importlib.metadata.version('jsonschema')})")
            except jsonschema.ValidationError as e:
                check(False, f"{os.path.basename(f)}: schema: {e.message}")
        print(f"hw_target_check --schema-only: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
        return 1 if fails else 0
    if not a.cqr:
        ap.error("--cqr is required without --schema-only")
    for f in files:
        base = os.path.basename(f)
        raw = open(f, "rb").read()
        t = json.loads(raw.decode("utf-8"))
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
