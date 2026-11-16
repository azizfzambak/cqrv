"""Stage 27b (B2) — Lean = Python for the conditional noise bound on all artifacts (PHASE2_SPEC §C.4 (4);
report §2.3.2, §6.6).

  python -I tests/diff/hw_noise_check.py --cqr <cqr>   (.venv; no Qiskit)

For every `hw/artifacts/<instance>__<target>/`: `cqr hw noise --artifact … --target … --json` equals
`hw/noisebound.py … --json` byte for byte (the exact bound, the clamp flag, the vacuity, 25a's p = r
figure). Prints the table of the twelve artifacts: 25a's figure, `noiseBound`, `clamped`, vacuous.
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    arts = sorted(d for d in os.listdir(os.path.join(ROOT, "hw", "artifacts"))
                  if os.path.isdir(os.path.join(ROOT, "hw", "artifacts", d)))
    errors = []
    rows = []
    for d in arts:
        adir = os.path.join(ROOT, "hw", "artifacts", d)
        target = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))["target"]
        tpath = os.path.join(ROOT, TARGET_FILES[target])
        lean = subprocess.run([a.cqr, "hw", "noise", "--artifact", adir, "--target", tpath, "--json"],
                              capture_output=True, text=True, encoding="utf-8")
        py = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "hw", "noisebound.py"), adir, tpath, "--json"],
                            capture_output=True, text=True, encoding="utf-8")
        if lean.returncode != 0 or py.returncode != 0:
            errors.append(f"{d}: cqr {lean.returncode} / python {py.returncode}: {(lean.stderr + py.stderr).strip()[:200]}")
            continue
        if lean.stdout.strip() != py.stdout.strip():
            errors.append(f"{d}: Lean {lean.stdout.strip()[:160]} differs from Python {py.stdout.strip()[:160]}")
            continue
        r = json.loads(lean.stdout)
        rows.append((d, float(Fraction(r["physical_bound_p_eq_r"])), float(Fraction(r["noise_bound"])),
                     r["clamped"], r["noise_vacuous"]))
    for d, pr, nb, cl, vac in rows:
        print(f"hw_noise_check: {d}: p=r {pr:.4f}  noiseBound {nb:.4f}  clamped {str(cl).lower()}  vacuous {str(vac).lower()}")
    for e in errors:
        print("hw_noise_check: " + e)
    if errors:
        return 1
    print(f"hw_noise_check: Lean = Python on {len(rows)} artifacts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
