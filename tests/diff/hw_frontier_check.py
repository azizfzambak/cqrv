"""Stage 27c (F4) — the frontier table's committed rows match the tools, and its frontier rows match the
certificates (PHASE2_SPEC §C.4; report §2.3.2, §6.6).

  python -I tests/diff/hw_frontier_check.py --cqr <cqr>   (.venv; no Qiskit)

From docs/hw_frontier/frontier.json (written by scripts/frontier.py; the Qiskit regeneration of the
rows is by hand, not in CI):
  * every row whose artifact is committed (`hw/artifacts/<name>__<target>/`) has `noise_bound`,
    `clamped`, `noise_vacuous` and `p_eq_r` equal to `cqr hw noise --json` and `two_qubit`,
    `depth_ns_L0`, `depth_ns_L1000` equal to `cqr hw grade --json` on the committed artifact;
  * `FRONTIER.md` is byte-identical to `scripts/frontier.py --render`'s output of frontier.json
    (checked by re-rendering into a temporary copy);
  * every committed conditional certificate `examples/certs/fr_*_<target>/manifest.json` belongs to a
    frontier row (the largest non-vacuous n of its series) and its `noise.noise_bound` is that row's.
Conditional on the premises; nothing here is a fact about a device or "verified on hardware".
"""
import argparse
import json
import os
import subprocess
import sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}


def cqr_json(cqr, args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit(f"cqr {' '.join(args)} failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
    return json.loads(p.stdout.strip().splitlines()[-1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    data = json.load(open(os.path.join(ROOT, "docs", "hw_frontier", "frontier.json"), encoding="utf-8"))
    errors = []
    checked = 0
    for r in data["rows"]:
        adir = os.path.join(ROOT, "hw", "artifacts", f"{r['name']}__{r['target']}")
        if not os.path.isdir(adir):
            continue
        tpath = os.path.join(ROOT, TARGET_FILES[r["target"]])
        nz = cqr_json(a.cqr, ["hw", "noise", "--artifact", adir, "--target", tpath, "--json"])
        for k, kk in (("noise_bound", "noise_bound"), ("clamped", "clamped"), ("noise_vacuous", "noise_vacuous"),
                      ("physical_bound_p_eq_r", "p_eq_r")):
            if nz[k] != r[kk]:
                errors.append(f"{r['name']}: {kk} {r[kk]} differs from cqr hw noise {nz[k]}")
        for L, key in (("0", "depth_ns_L0"), ("1000", "depth_ns_L1000")):
            g = cqr_json(a.cqr, ["hw", "grade", "--artifact", adir, "--target", tpath, "--ff-latency", L, "--json"])
            if g["depth_ns"] != r[key] or g["two_qubit"] != r["two_qubit"]:
                errors.append(f"{r['name']}: grade at L={L} ({g['two_qubit']}, {g['depth_ns']}) differs from the row ({r['two_qubit']}, {r[key]})")
        checked += 1
    # the frontier rows against the certificates
    frontier = {}
    for key in data["series"]:
        ok = [r for r in data["rows"] if r["series"] == key and not r["noise_vacuous"]]
        if ok:
            frontier[key] = max(ok, key=lambda r: r["n"])
    certs = sorted(d for d in os.listdir(os.path.join(ROOT, "examples", "certs"))
                   if d.startswith("fr_") and os.path.isfile(os.path.join(ROOT, "examples", "certs", d, "manifest.json")))
    for c in certs:
        man = json.load(open(os.path.join(ROOT, "examples", "certs", c, "manifest.json"), encoding="utf-8"))
        inst, target = man["artifact"]["instance"], man["artifact"]["target"]
        rows = [r for r in frontier.values() if r["name"] == inst and r["target"] == target]
        if not rows:
            errors.append(f"{c}: its artifact {inst}__{target} is not a frontier row")
            continue
        if man["noise"]["noise_bound"] != rows[0]["noise_bound"]:
            errors.append(f"{c}: noise_bound {man['noise']['noise_bound']} differs from the frontier row's {rows[0]['noise_bound']}")
        if "noise_conditional" not in man["status"]:
            errors.append(f"{c}: status {man['status']} lacks noise_conditional")
    # the table is the render of the rows
    import tempfile
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    import frontier as fr
    committed = open(fr.TABLE, "rb").read()
    with tempfile.TemporaryDirectory() as tmp:
        fr.TABLE = os.path.join(tmp, "FRONTIER.md")
        import io, contextlib
        with contextlib.redirect_stdout(io.StringIO()):
            fr.render(data)
        if open(fr.TABLE, "rb").read() != committed:
            errors.append("FRONTIER.md differs from the render of frontier.json")
    for e in errors:
        print("hw_frontier_check: " + e)
    if errors:
        return 1
    print(f"hw_frontier_check: {checked} committed rows match cqr hw noise/grade; {len(certs)} frontier certificates match their rows; FRONTIER.md is the render")
    return 0


if __name__ == "__main__":
    sys.exit(main())
