"""Differential test of the Lean SHA3-256 (CQRV.Certify.SHA3) against Python's hashlib, which
is used only as a test oracle (report §9.5.3; Stage 8a, reviewer decision 1).

Checks the two reviewer vectors ("" and "abc"), 200 random byte strings of lengths 0..600
(fixed seed; they cross the 136-byte block boundary several times) and the lengths around the
block boundary (135, 136, 137, 271, 272, 273).

Usage: python -I tests/diff/sha3_diff.py [--seed S]   (after `lake build`)
"""

import argparse
import hashlib
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import certify_tool  # noqa: E402

VECTORS = {
    b"": "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
    b"abc": "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261024)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    msgs = list(VECTORS)
    msgs += [rng.integers(0, 256, size=int(rng.integers(0, 601)), dtype=np.uint8).tobytes()
             for _ in range(200)]
    msgs += [bytes(rng.integers(0, 256, size=k, dtype=np.uint8)) for k in
             (135, 136, 137, 271, 272, 273)]
    out = certify_tool(["sha3"], stdin="".join(m.hex() + "\n" for m in msgs)).split()
    if len(out) != len(msgs):
        raise SystemExit(f"sha3_diff: {len(out)} digests for {len(msgs)} messages")
    for m, want in VECTORS.items():
        assert hashlib.sha3_256(m).hexdigest() == want, "the test oracle disagrees with the vector"
    bad = [(len(m), d) for m, d in zip(msgs, out) if d != hashlib.sha3_256(m).hexdigest()]
    if bad:
        raise SystemExit(f"sha3_diff: {len(bad)} mismatches, first at length {bad[0][0]}")
    lens = [len(m) for m in msgs[2:202]]
    print("ok:   SHA3-256 vectors \"\" and \"abc\"")
    print(f"ok:   200 random strings (lengths {min(lens)}..{max(lens)}, "
          f"{sum(1 for k in lens if k >= 136)} of them >= one block) + 6 boundary lengths")
    print("sha3_diff: all checks passed")


if __name__ == "__main__":
    main()
