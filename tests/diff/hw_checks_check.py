"""Stage 26c1b — the committed per-instance hardware checks are the artifacts' (PHASE2_SPEC §C.3 "26c1b";
report §5.3, §9.1.1).

  python -I tests/diff/hw_checks_check.py --cqr <path to cqr>   (.venv; no Qiskit)

For every `examples/hw_checks/<artifact>/Check.lean`:
  * the artifact directory `hw/artifacts/<artifact>/` exists with `logical.json`, `witness.json`,
    `physical.json` and `manifest.json`;
  * the SHA3-256 hex digests in the file's header are those of the canonical `logical.json`,
    `witness.json` and `physical.json` (`json.dumps(sort_keys=True, separators=(",", ":"))`, the form the
    files are written in) and of the target's `snapshot.hash`, and `logical.json`'s digest is the
    manifest's `hashes.logical_circuit`;
  * `cqr hw check --artifact <dir> --target <target file> --out <tmp>` regenerates the file
    byte-identically (the literals are the artifact's; the generator is deterministic).
Every artifact directory must have a check file (twelve of each). The kernel check of the files
(`lake env lean`) is the bash step's; this script does not run Lean.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha3(data):
    return hashlib.sha3_256(data if isinstance(data, bytes) else data.encode("utf-8")).hexdigest()


def hashes_in_header(text):
    """The four digests the header names, in order: logical, witness, physical, snapshot."""
    return re.findall(r"`([0-9a-f]{64})`", text.split("-/", 1)[0])


def check_one(cqr, name, errors):
    cdir = os.path.join(ROOT, "examples", "hw_checks", name)
    adir = os.path.join(ROOT, "hw", "artifacts", name)
    for f in ("logical.json", "witness.json", "physical.json", "manifest.json"):
        if not os.path.exists(os.path.join(adir, f)):
            errors.append(f"{name}: {f} missing in the artifact")
            return
    text = open(os.path.join(cdir, "Check.lean"), encoding="utf-8").read()
    manifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
    target = json.load(open(os.path.join(ROOT, TARGET_FILES[manifest["target"]]), encoding="utf-8"))
    want = []
    for f in ("logical.json", "witness.json", "physical.json"):
        obj = json.load(open(os.path.join(adir, f), encoding="utf-8"))
        want.append(sha3(canonical(obj)))
    want.append(target["snapshot"]["hash"])
    got = hashes_in_header(text)
    if got != want:
        errors.append(f"{name}: header digests {got} differ from the artifact's {want}")
    if want[0] != manifest["hashes"]["logical_circuit"]:
        errors.append(f"{name}: logical.json digest is not the manifest's logical_circuit")
    if want[1] != manifest["hashes"]["witness"]:
        errors.append(f"{name}: witness.json digest is not the manifest's witness")
    with tempfile.TemporaryDirectory() as tmp:
        p = subprocess.run([cqr, "hw", "check", "--artifact", adir, "--target",
                            os.path.join(ROOT, TARGET_FILES[manifest["target"]]), "--out", tmp],
                           capture_output=True, text=True, encoding="utf-8")
        if p.returncode != 0:
            errors.append(f"{name}: cqr hw check failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
            return
        regenerated = open(os.path.join(tmp, name, "Check.lean"), "rb").read()
    committed = open(os.path.join(cdir, "Check.lean"), "rb").read()
    if regenerated != committed:
        errors.append(f"{name}: Check.lean differs from the regenerated file ({len(committed)} vs {len(regenerated)} bytes)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    checks = sorted(d for d in os.listdir(os.path.join(ROOT, "examples", "hw_checks"))
                    if os.path.isdir(os.path.join(ROOT, "examples", "hw_checks", d)))
    artifacts = sorted(d for d in os.listdir(os.path.join(ROOT, "hw", "artifacts"))
                       if os.path.isdir(os.path.join(ROOT, "hw", "artifacts", d)))
    errors = []
    if checks != artifacts:
        errors.append(f"check files {checks} and artifacts {artifacts} differ")
    for name in checks:
        if name in artifacts:
            check_one(a.cqr, name, errors)
    for e in errors:
        print("hw_checks_check: " + e)
    if errors:
        return 1
    print(f"hw_checks_check: {len(checks)} check files, headers and regeneration ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
