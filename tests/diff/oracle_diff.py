"""Differential test of the oracle synthesizer (report §6.1.4, §6.2.2, §6.2.4; CLAUDE.md rule 9).

For each predicate P: write it as a DSL source, run `cqr synthesize <file> --json [--amax k]
[--uncompute mbu|coherent]` (Stage 15a: `--uncompute` selects the mode of every call; in mode
coherent the circuits are measurement-free and the Bennett budgets below the straight-line
count must be rejected),
execute the IR with `statevector.run_ir` (every measurement outcome enumerated), and check in
every branch, on random complex superpositions of the data register, that the final state is
U_P|psi> (x) |0...0>_anc up to a global phase per branch; `alloc`/`free` check that every
ancilla is |0> at both ends of its life. P is evaluated here from the generated tree, never
from the synthesizer's network.

Sets (fixed seed):
  * `random`  — 100 AND/NOT/OR trees over random literals, n <= 12 data qubits;
  * `grover`  — examples/grover_pred_037.cqr, P(x) = x0 AND x3 AND x7 (§6.1.4);
  * `xor-if`  — 30 trees that also use `xor` and `if` (in-place XOR, Stage 5 decision 2);
  * `bennett` — AND chains under Bennett budgets (§6.1.3, decision 3).

Usage: python -I tests/diff/oracle_diff.py --cqr <path to cqr executable> [--seed S]
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import statevector as sv  # noqa: E402

MAX_DATA = 12


# --- predicate trees: ("lit", k, positive) | ("not", t) | (op, t1, t2) | ("if", c, a, b) ----

def evaluate(t, x):
    """x: list of input bits."""
    tag = t[0]
    if tag == "lit":
        return x[t[1]] if t[2] else not x[t[1]]
    if tag == "not":
        return not evaluate(t[1], x)
    if tag == "and":
        return evaluate(t[1], x) and evaluate(t[2], x)
    if tag == "or":
        return evaluate(t[1], x) or evaluate(t[2], x)
    if tag == "xor":
        return evaluate(t[1], x) != evaluate(t[2], x)
    if tag == "if":
        return evaluate(t[2], x) if evaluate(t[1], x) else evaluate(t[3], x)
    raise ValueError(t)


def render(t):
    tag = t[0]
    if tag == "lit":
        return f"idx(x, {t[1]})" if t[2] else f"(not idx(x, {t[1]}))"
    if tag == "not":
        return f"(not {render(t[1])})"
    if tag == "if":
        return f"(if {render(t[1])} then {render(t[2])} else {render(t[3])})"
    return f"({render(t[1])} {tag} {render(t[2])})"


def gen_tree(rng, n, leaves, ops):
    """A random tree with `leaves` literals over random variables (repeats allowed: x AND x,
    x AND NOT x and constant operands are folded by the synthesizer and checked like the rest)."""
    if leaves == 1:
        return ("lit", int(rng.integers(n)), bool(rng.integers(2)))
    k = int(rng.integers(1, leaves))
    op = ops[int(rng.integers(len(ops)))]
    if op == "if" and leaves >= 3:
        k2 = int(rng.integers(1, leaves - k)) if leaves - k > 1 else 1
        if k + k2 < leaves:
            c, a, b = (gen_tree(rng, n, k, ops), gen_tree(rng, n, k2, ops),
                       gen_tree(rng, n, leaves - k - k2, ops))
            return ("if", c, a, b)
    if op == "if":
        op = "and"
    left, right = gen_tree(rng, n, k, ops), gen_tree(rng, n, leaves - k, ops)
    t = (op, left, right)
    return ("not", t) if rng.random() < 0.25 else t


def bits_of(x, n):
    """Data index -> input bits (qubit 0 = MSB = input bit 0)."""
    return [(x >> (n - 1 - k)) & 1 == 1 for k in range(n)]


# --- running cqr -----------------------------------------------------------------------------

MODE = "mbu"  # --uncompute mode of every `cqr synthesize` call (Stage 15a)


def synthesize(cqr, path, amax=None):
    cmd = ([cqr, "synthesize", path, "--json"] + (["--amax", str(amax)] if amax is not None else [])
           + (["--uncompute", MODE] if MODE != "mbu" else []))
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    line = out.stdout.strip().splitlines()[0] if out.stdout.strip() else ""
    if out.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} exited {out.returncode}: {line or out.stderr}")
    return json.loads(line)


def write_src(dirname, name, n, body):
    path = os.path.join(dirname, f"{name}.cqr")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(f"fn {name}(x: Vec Bool {n}) -> Bool {{\n  {body}\n}}\n")
    return path


def check(cqr, path, n, pred, rng, amax=None, trials=2):
    res = synthesize(cqr, path, amax)
    circ = res["circuit"]
    assert circ["n_data"] == n, (circ["n_data"], n)
    branches = sv.check_phase_oracle(circ, lambda x: pred(bits_of(x, n)), rng, trials)
    g = res["grade"]
    # Grade sanity (Eq. 2, Eq. 5): t <= 4 c_and in the straight-line schedule (8 c_and in mode
    # coherent: 4 more T per AND, PHASE2_SPEC.md §A.0.1), w = n + a; coherent circuits have no
    # measurement and no classical bit.
    if amax is None:
        t_per_and = 8 if MODE == "coherent" else 4
        assert g["t"] <= t_per_and * res["and_complexity"] and g["a"] <= res["and_complexity"], res
    if MODE == "coherent":
        assert all(gt["op"] != "measure" and "if" not in gt for gt in circ["gates"]), "coherent: measure"
    assert g["w"] == n + g["a"], g
    return res, branches


def run_set(label, cases, cqr, rng):
    """cases: (name, path, n, pred, amax). Returns (all passed, number passed)."""
    ok, branches = 0, 0
    for name, path, n, pred, amax in cases:
        try:
            _, b = check(cqr, path, n, pred, rng, amax)
            ok += 1
            branches += b
        except (AssertionError, RuntimeError) as e:
            print(f"FAIL [{label}] {name}: {e}")
    print(f"[{label}] {ok}/{len(cases)} predicates pass, {branches} measurement branches checked")
    return ok == len(cases), ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261023)
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--uncompute", choices=["mbu", "coherent"], default="mbu",
                    help="the --uncompute mode of every synthesize call (Stage 15a)")
    args = ap.parse_args()
    global MODE
    MODE = args.uncompute
    args.cqr = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    rng = np.random.default_rng(args.seed)
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    all_ok, total = True, 0
    with tempfile.TemporaryDirectory() as tmp:
        cases = []
        for i in range(args.count):
            n = int(rng.integers(1, MAX_DATA + 1))
            leaves = 1 if n == 1 else int(rng.integers(1, 7))
            t = gen_tree(rng, n, leaves, ["and", "or"])
            path = write_src(tmp, f"rand_{i:03d}", n, render(t))
            cases.append((f"rand_{i:03d}: {render(t)}", path, n,
                          (lambda t: lambda x: evaluate(t, x))(t), None))
        good, k = run_set("random", cases, args.cqr, rng)
        all_ok &= good
        total += k

        grover = os.path.join(root, "examples", "grover_pred_037.cqr")
        good, k = run_set("grover", [("grover_pred_037", grover, 8,
                                      lambda x: x[0] and x[3] and x[7], None)], args.cqr, rng)
        all_ok &= good
        total += k

        xcases = []
        for i in range(30):
            n = int(rng.integers(2, 9))
            t = gen_tree(rng, n, int(rng.integers(2, 6)), ["and", "or", "xor", "if"])
            path = write_src(tmp, f"xor_{i:03d}", n, render(t))
            xcases.append((f"xor_{i:03d}: {render(t)}", path, n,
                           (lambda t: lambda x: evaluate(t, x))(t), None))
        all_ok &= run_set("xor-if", xcases, args.cqr, rng)[0]

        bcases = []
        for L, budgets in ((4, [4, 3]), (5, [3]), (8, [8, 4])):
            body = " and ".join(f"idx(x, {k})" for k in range(L + 1))
            path = write_src(tmp, f"chain_{L}", L + 1, body)
            for a in budgets:
                bcases.append((f"chain_{L} --amax {a}", path, L + 1, lambda x: all(x), a))
        if MODE == "mbu":
            all_ok &= run_set("bennett", bcases, args.cqr, rng)[0]
        else:
            # Bennett pebbling is MBU-only (Stage 15a): a budget below the straight-line count is
            # rejected with unsupported_combination; a budget that covers it is the coherent
            # straight-line oracle (checked like the rest).
            rej, cov = [], []
            for name, path, n, pred, a in bcases:
                L = n - 1
                (cov if a >= L else rej).append((name, path, n, pred, a))
            all_ok &= run_set("bennett (budget covers: straight-line coherent)", cov, args.cqr,
                              rng)[0]
            for name, path, n, pred, a in rej:
                try:
                    synthesize(args.cqr, path, a)
                    all_ok = False
                    print(f"FAIL [bennett coherent] {name}: accepted, expected unsupported_combination")
                except RuntimeError as e:
                    if "unsupported_combination" not in str(e):
                        all_ok = False
                        print(f"FAIL [bennett coherent] {name}: {e}")
            print(f"[bennett coherent] {len(rej)} budgets below the straight-line count rejected "
                  f"with unsupported_combination")

    print(f"oracle_diff ({MODE}): {'PASS' if all_ok else 'FAIL'} — {total}/{args.count + 1} predicates "
          f"(100 random AND/NOT/OR + grover_pred_037) pass in every measurement branch")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
