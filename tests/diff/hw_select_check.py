"""Stage 26c2b — the committed selections are the artifacts', and the budget test (PHASE2_SPEC §C.3;
report §3.1.3, §5.3).

  python -I tests/diff/hw_select_check.py --cqr <cqr>   (.venv; no Qiskit)

For every `examples/hw_select/<request>__<target>/Select.lean`:
  * each candidate's `physical.json` SHA3-256 in the file's candidate docstrings is the digest in the
    header of `examples/hw_checks/<artifact>/Check.lean` (the link to the checked reconstruction);
  * `cqr hw select --request … --target … --prefer bound --out <tmp>` regenerates the file byte for
    byte;
  * the candidates are exactly the request's artifacts on the target.
The budget test: on FakeTorino, `--prefer bound --budget 1` returns `none` for both requests (every
bound there is vacuous): the honest answer, not an error (exit 0, the word `none` in the output).
The kernel check of the files (`lake env lean`) is the bash step's.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}
REQUESTS = ("grover_pred_037", "simple_alu_x0_1")


def check_dir(cqr, name, errors):
    request, target = name.rsplit("__", 1)
    sdir = os.path.join(ROOT, "examples", "hw_select", name)
    text = open(os.path.join(sdir, "Select.lean"), encoding="utf-8").read()
    cands = re.findall(r"Candidate \d+: `([^`]+)` \((?:mbu|coherent)\); `physical.json` SHA3-256 `([0-9a-f]{64})`", text)
    arts = sorted(d for d in os.listdir(os.path.join(ROOT, "hw", "artifacts"))
                  if d.startswith(request + "_") and d.endswith("__" + target))
    if sorted(c for c, _ in cands) != arts:
        errors.append(f"{name}: candidates {[c for c, _ in cands]} are not the artifacts {arts}")
    for cand, digest in cands:
        cpath = os.path.join(ROOT, "examples", "hw_checks", cand, "Check.lean")
        if not os.path.exists(cpath):
            errors.append(f"{name}: candidate {cand} has no Check.lean")
            continue
        header = open(cpath, encoding="utf-8").read().split("-/", 1)[0]
        digests = re.findall(r"`([0-9a-f]{64})`", header)
        if len(digests) < 3 or digests[2] != digest:
            errors.append(f"{name}: candidate {cand}: physical.json digest {digest} is not its Check.lean's {digests[2:3]}")
    with tempfile.TemporaryDirectory() as tmp:
        p = subprocess.run([cqr, "hw", "select", "--request", request, "--target", os.path.join(ROOT, TARGET_FILES[target]),
                            "--prefer", "bound", "--out", tmp], capture_output=True, text=True, encoding="utf-8")
        if p.returncode != 0:
            errors.append(f"{name}: cqr hw select failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
        elif open(os.path.join(tmp, name, "Select.lean"), "rb").read() != open(os.path.join(sdir, "Select.lean"), "rb").read():
            errors.append(f"{name}: Select.lean differs from the regenerated file")


def budget_test(cqr, errors):
    for request in REQUESTS:
        with tempfile.TemporaryDirectory() as tmp:
            p = subprocess.run([cqr, "hw", "select", "--request", request, "--target", os.path.join(ROOT, TARGET_FILES["fake_torino"]),
                                "--prefer", "bound", "--budget", "1", "--out", tmp], capture_output=True, text=True, encoding="utf-8")
            if p.returncode != 0 or "none" not in p.stdout:
                errors.append(f"budget test {request}: expected exit 0 and `none`, got {p.returncode}: {(p.stdout + p.stderr).strip()[:200]}")
            else:
                print(f"hw_select_check: budget 1 on FakeTorino, {request}: none (every bound vacuous): the honest answer, not an error")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    names = sorted(d for d in os.listdir(os.path.join(ROOT, "examples", "hw_select"))
                   if os.path.isdir(os.path.join(ROOT, "examples", "hw_select", d)))
    errors = []
    expected = sorted(f"{r}__{t}" for r in REQUESTS for t in TARGET_FILES)
    if names != expected:
        errors.append(f"selection dirs {names} are not {expected}")
    for name in names:
        check_dir(a.cqr, name, errors)
    budget_test(a.cqr, errors)
    for e in errors:
        print("hw_select_check: " + e)
    if errors:
        return 1
    print(f"hw_select_check: {len(names)} selections, hash links and regeneration ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
