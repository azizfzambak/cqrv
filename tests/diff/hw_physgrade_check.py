"""Stage 26c2 (P1) — `cqr hw grade --json` equals `hw/physgrade.py` byte for byte on every artifact, at
L = 0 and L = 1000 ns (PHASE2_SPEC §C.3; report §3.1, §9.1.1).

  python -I tests/diff/hw_physgrade_check.py --cqr <path to cqr>   (.venv; no Qiskit)

Prints the table (artifact, L, qubits, two-qubit, mid-circuit measurements, feed-forward, depth ns,
bound, vacuous) and exits 1 on any difference.
"""
import argparse
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import physgrade  # noqa: E402

TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}
LATENCIES = ("0", "1000")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    arts = sorted(d for d in os.listdir(os.path.join(ROOT, "hw", "artifacts"))
                  if os.path.isdir(os.path.join(ROOT, "hw", "artifacts", d)))
    errors = 0
    print(f"{'artifact':50} {'L':>5} {'q':>3} {'2q':>5} {'mid':>4} {'ff':>4} {'depth ns':>14} {'bound':>12} vac")
    for name in arts:
        adir = os.path.join(ROOT, "hw", "artifacts", name)
        manifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
        tpath = os.path.join(ROOT, TARGET_FILES[manifest["target"]])
        for L in LATENCIES:
            py = physgrade.canonical(physgrade.grade_of_artifact(adir, tpath, L))
            p = subprocess.run([a.cqr, "hw", "grade", "--artifact", adir, "--target", tpath, "--ff-latency", L, "--json"],
                               capture_output=True, text=True, encoding="utf-8")
            lean = p.stdout.strip()
            if p.returncode != 0 or lean != py:
                errors += 1
                print(f"hw_physgrade_check: {name} L={L}: Lean {lean[:200]!r} ({p.returncode}, {p.stderr.strip()[:200]}) "
                      f"differs from Python {py[:200]!r}")
                continue
            g = json.loads(lean)
            depth = g["depth_ns"]
            try:
                from fractions import Fraction
                depth_f = float(Fraction(depth)); bound_f = float(Fraction(g["bound"]))
            except Exception:
                depth_f = bound_f = float("nan")
            print(f"{name:50} {L:>5} {g['qubits']:>3} {g['two_qubit']:>5} {g['mid_measurements']:>4} {g['feed_forward']:>4} "
                  f"{depth_f:>14.3f} {bound_f:>12.4f} {'yes' if g['vacuous'] else 'no'}")
    if errors:
        print(f"hw_physgrade_check: {errors} differences")
        return 1
    print(f"hw_physgrade_check: Lean = Python on {len(arts)} artifacts × {len(LATENCIES)} latencies")
    return 0


if __name__ == "__main__":
    sys.exit(main())
