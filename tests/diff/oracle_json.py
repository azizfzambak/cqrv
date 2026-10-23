"""Byte-identity check of the synthesized oracles — Stage 6b-3, reviewer decision 1.

Proof-only changes to the synthesizer (`CQRV/Synthesis/Oracle.lean`) must not change the
emitted circuit. This script runs `cqr synthesize <file> --json` on the three corpus files
(grover_pred_037, search_or, and_chain_8) and on 20 random predicates from the generator of
`oracle_diff.py` (fixed seed; 10 AND/NOT/OR, 10 with XOR and `if`) and compares the output
line by line, byte for byte, with the golden file `oracle_json_golden.txt`.

Usage: python -I tests/diff/oracle_json.py --cqr <path to cqr> [--write]
  --write   regenerate the golden file (only from a commit whose circuits are accepted).
"""
import argparse
import os
import subprocess
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oracle_diff import MAX_DATA, gen_tree, render, write_src  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
GOLDEN = os.path.join(HERE, "oracle_json_golden.txt")
CORPUS = ["grover_pred_037", "search_or", "and_chain_8"]
SEED = 20261024


def cases(tmp):
    """(name, path) for the corpus files and the 20 random predicates."""
    out = [(c, os.path.join(ROOT, "examples", f"{c}.cqr")) for c in CORPUS]
    rng = np.random.default_rng(SEED)
    for i in range(20):
        ops = ["and", "or"] if i < 10 else ["and", "or", "xor", "if"]
        n = int(rng.integers(2, MAX_DATA + 1))
        t = gen_tree(rng, n, int(rng.integers(2, 7)), ops)
        out.append((f"rand_{i:02d}", write_src(tmp, f"rand_{i:02d}", n, render(t))))
    return out


def synth(cqr, path):
    res = subprocess.run([cqr, "synthesize", path, "--json"], capture_output=True)
    if res.returncode != 0:
        raise RuntimeError(f"cqr synthesize {path} exited {res.returncode}: {res.stderr!r}")
    return res.stdout.replace(b"\r\n", b"\n").rstrip(b"\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        lines = [name.encode() + b"\t" + synth(os.path.abspath(args.cqr), path)
                 for name, path in cases(tmp)]
    blob = b"\n".join(lines) + b"\n"
    if args.write:
        with open(GOLDEN, "wb") as f:
            f.write(blob)
        print(f"oracle_json: wrote {len(lines)} circuits to {GOLDEN}")
        return
    with open(GOLDEN, "rb") as f:
        golden = f.read().replace(b"\r\n", b"\n")
    if blob == golden:
        print(f"oracle_json: PASS — {len(lines)} circuits byte-identical to the golden file")
        sys.exit(0)
    old = golden.split(b"\n")
    for k, line in enumerate(lines):
        if k >= len(old) or old[k] != line:
            name = line.split(b"\t")[0].decode()
            print(f"oracle_json: FAIL — first difference at {name}")
            break
    else:
        print("oracle_json: FAIL — golden file has extra lines")
    sys.exit(1)


if __name__ == "__main__":
    main()
