"""Front-end validation: DSL evaluator vs network vs a Python reference (report §5.3.3, §7.2,
§9.5.1; Stage 9b, reviewer decision 1, task 1).

For every predicate, `cqr check <file> --truth-table` prints the truth table of the Lean DSL
evaluator (`evalProgram`) and of `Network.pred (toNetwork …)`; both must equal the truth table
computed here, independently of Lean:

  * the corpus: examples/grover_pred_037, and_chain_8, search_or, simple_alu_x0_1 (reference:
    the SyReC integer semantics of RevLib simple_alu, tests/diff/benchmark_diff.py) and
    tests/certify/xor_pred, if_pred; examples/search_while (`loop … while`) must be refused
    (exit 2) and examples/allocate_tree must fail the surface check (exit 1);
  * 100 random predicates from the harness generator (tests/diff/oracle_diff.py `gen_tree`,
    operators and/or/xor/if and negation, n <= 12, fixed seed), evaluated from the tree.

Character x of a table is the value on input x, bit k of x = input bit k.

Usage: python -I tests/diff/frontend_diff.py --cqr <path to cqr executable> [--seed S]
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import benchmark_diff  # noqa: E402
import oracle_diff  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MAX_DATA = 12

CORPUS = [
    ("examples/grover_pred_037.cqr", 8, lambda x: x[0] and x[3] and x[7]),
    ("examples/and_chain_8.cqr", 9, all),
    ("examples/search_or.cqr", 4, lambda x: x[0] or x[1]),
    ("examples/simple_alu_x0_1.cqr", 6, benchmark_diff.reference),
    ("tests/certify/xor_pred.cqr", 4, lambda x: (x[0] != x[1]) and x[2]),
    ("tests/certify/if_pred.cqr", 6,
     lambda x: (x[1] if x[0] else (x[2] != x[3])) and x[4] and x[5]),
]


def table_of(f, n):
    return "".join("1" if f([bool((x >> k) & 1) for k in range(n)]) else "0"
                   for x in range(2**n))


def truth_tables(exe, path):
    p = subprocess.run([exe, "check", path, "--truth-table"], capture_output=True, text=True,
                       encoding="utf-8")
    return p.returncode, p.stdout


def compare(exe, label, path, n, f):
    rc, out = truth_tables(exe, path)
    if rc != 0:
        return f"exit {rc}: {out.strip()}"
    tt = json.loads(out)
    want = table_of(f, n)
    if tt["n"] != n:
        return f"n = {tt['n']}, expected {n}"
    for side in ("evaluator", "network"):
        if tt[side] != want:
            x = next(i for i, (a, b) in enumerate(zip(tt[side], want)) if a != b)
            return f"{side} differs from the reference at input {x} ({tt[side][x]} vs {want[x]})"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=int, default=100)
    args = ap.parse_args()
    exe = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    ok = True

    inputs = 0
    for rel, n, f in CORPUS:
        err = compare(exe, rel, os.path.join(ROOT, rel), n, f)
        if err:
            ok = False
            print(f"FAIL corpus {rel}: {err}")
        else:
            inputs += 2**n
    print(f"corpus: {len(CORPUS)} files, evaluator = network = reference on all {inputs} inputs"
          if ok else "corpus: FAIL")
    rc, _ = truth_tables(exe, os.path.join(ROOT, "examples", "search_while.cqr"))
    if rc != 2:
        ok = False
        print(f"FAIL search_while: `loop … while` not refused (exit {rc})")
    rc, out = truth_tables(exe, os.path.join(ROOT, "examples", "allocate_tree.cqr"))
    if rc != 1 or json.loads(out)["code"] != "non_structural_recursion":
        ok = False
        print(f"FAIL allocate_tree: exit {rc}, {out.strip()}")
    print("corpus: search_while refused (loop … while, exit 2); allocate_tree rejected "
          "(non_structural_recursion, exit 1)")

    rng = np.random.default_rng(args.seed)
    passed, inputs = 0, 0
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(args.count):
            n = int(rng.integers(1, MAX_DATA + 1))
            leaves = 1 if n == 1 else int(rng.integers(1, 8))
            t = oracle_diff.gen_tree(rng, n, leaves, ["and", "or", "xor", "if"])
            path = oracle_diff.write_src(tmp, f"fe_{i:03d}", n, oracle_diff.render(t))
            err = compare(exe, f"fe_{i:03d}", path, n,
                          (lambda t: lambda x: oracle_diff.evaluate(t, x))(t))
            if err:
                ok = False
                print(f"FAIL fe_{i:03d}: {oracle_diff.render(t)}: {err}")
            else:
                passed += 1
                inputs += 2**n
    print(f"random: {passed}/{args.count} predicates, evaluator = network = reference on all "
          f"{inputs} inputs")
    print(f"frontend_diff: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
