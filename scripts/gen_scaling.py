"""Stage 14b (docs/tasks/STAGE14_TASK.md B1; report §9.5.1) — generate the scaling families.

Writes `bench/scaling/<name>.cqr` (committed DSL sources) and `bench/scaling/manifest.json`
(instance, family, n, M, r⋆, the iteration counts to certify, and the reference needed by the
harness). Fixed seeds; the DSL sources are deterministic given the seed and the `cqr` build.

Families
  * carry_k  — carry-out of a k-bit ripple-carry adder, n = 2k, k = 1..8 (n ≤ 16). Inputs
               x[0..k-1] = a (LSB first), x[k..2k-1] = b. Carry recurrence in the XOR form of the
               majority, c_i = (a_i ∧ b_i) ⊕ (c_{i-1} ∧ (a_i ⊕ b_i)) (the two terms are
               exclusive, so ⊕ = ∨): 2k − 1 AND nodes. M = 2^(2k-1) − 2^(k-1) (a + b ≥ 2^k).
  * rand_a   — random one-output predicates with AND, XOR, NOT and `if` from the harness
               generator `oracle_diff.gen_tree` (ops ["and", "xor", "if"]; it adds `not` with
               probability 1/4; no `or`), n = 12 (n = 6 for the a = 16 target, so that the
               statevector harness with n + a qubits stays feasible), chosen by rejection
               sampling (seed 20261029 + target) so that the synthesized oracle has exactly
               a = 4, 8, 16, 32, 64 AND nodes (`cqr synthesize --json`, grade.a).
  * alu_bits — the other output bits of RevLib "Simple ALU" (simple_alu_234.src, see
               examples/simple_alu_x0_1.cqr) that the Stage 9b transcription covers without new
               constructs: bit 0 (cone op.0, op.1, x1.0, x2.0: n = 4) and bit 2 (cone op.0,
               op.1, x1.0..2, x2.0..2: n = 8); checked here against the SyReC integer semantics
               (`benchmark_diff.alu_bit`, w = 16 and w = 3) on every input before writing.
               Bits ≥ 3 are skipped: bit 3 of x1 · x2 needs the two-bit carry of a column sum
               (a0b2 + a1b1 + a2b0 + c1 ∈ 0..4), a multi-bit adder that is no longer a reading
               of the SyReC source (DECISIONS.md 2026-10-29, Stage 14b).

M is counted from `cqr check --truth-table` (the network, n ≤ 16) and cross-checked against the
reference evaluation on every input (so the reference used by the harness agrees with the
network). r⋆ = ⌊π/(4θ)⌋, sin²θ = M/2ⁿ (as `rStar`, cross-checked with `cqr synthesize --grover`).
Iteration counts to certify: r = 1, and r⋆ when 1 < r⋆ ≤ 4.

Usage: python -I scripts/gen_scaling.py --cqr .lake/build/bin/cqr.exe
"""

import argparse
import json
import math
import os
import subprocess
import sys
import tempfile

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
import oracle_diff as od  # noqa: E402  (gen_tree, render, evaluate: the harness generator)
import benchmark_diff as bd  # noqa: E402  (alu_bit: the SyReC semantics)

OUT = os.path.join(ROOT, "bench", "scaling")
SEED = 20261029
RAND_TARGETS = (4, 8, 16, 32, 64)


# --- carry_k ---------------------------------------------------------------------------------

def carry_source(k):
    n = 2 * k
    lines = [f"fn carry_{k}(x: Vec Bool {n}) -> Bool {{"]
    lines.append(f"  let c0 = idx(x, 0) and idx(x, {k}) in")
    for i in range(1, k):
        a, b = f"idx(x, {i})", f"idx(x, {k + i})"
        lines.append(f"  let c{i} = ({a} and {b}) xor (c{i - 1} and ({a} xor {b})) in")
    lines.append(f"  c{k - 1}")
    lines.append("}")
    return n, "\n".join(lines) + "\n"


def carry_ref(k, bits):
    a = sum(int(bits[i]) << i for i in range(k))
    b = sum(int(bits[k + i]) << i for i in range(k))
    return ((a + b) >> k) & 1 == 1


# --- alu_bits --------------------------------------------------------------------------------

def alu_layout(bit):
    """Input layout for output bit `bit`: x[0] = op.0, x[1] = op.1, then x1.0..bit, x2.0..bit."""
    return 2 + 2 * (bit + 1)


def alu_source(bit):
    n = alu_layout(bit)
    B = bit + 1
    a = [f"a{i}" for i in range(B)]
    b = [f"b{i}" for i in range(B)]
    lets = ["  let op0 = idx(x, 0) in", "  let op1 = idx(x, 1) in"]
    lets += [f"  let a{i} = idx(x, {2 + i}) in" for i in range(B)]
    lets += [f"  let b{i} = idx(x, {2 + B + i}) in" for i in range(B)]
    if bit == 0:
        add, sub, mul, xor = "a0 xor b0", "a0 xor b0", "a0 and b0", "a0 xor b0"
    elif bit == 2:
        # ripple carry c0 = a0 b0, c1 = a1 b1 ⊕ c0 (a1 ⊕ b1); borrow w0 = ¬a0 b0,
        # w1 = ¬a1 b1 ⊕ w0 ¬(a1 ⊕ b1); product bit 2 = a0 b2 ⊕ a1 b1 ⊕ a2 b0 ⊕ (a0 b1 ∧ a1 b0)
        add = "a2 xor b2 xor ((a1 and b1) xor ((a0 and b0) and (a1 xor b1)))"
        sub = ("a2 xor b2 xor (((not a1) and b1) xor (((not a0) and b0) and "
               "(not (a1 xor b1))))")
        mul = "(a0 and b2) xor (a1 and b1) xor (a2 and b0) xor ((a0 and b1) and (a1 and b0))"
        xor = "a2 xor b2"
    else:
        raise ValueError(bit)
    body = (f"  if (not op1) and (not op0) then {add}\n"
            f"  else if (not op1) and op0 then {sub}\n"
            f"  else if op1 and (not op0) then {mul}\n"
            f"  else {xor}")
    src = (f"-- Stage 14b, family alu_bits: RevLib Simple ALU (simple_alu_234.src), bit {bit} of x0;\n"
           f"-- transcription rules of examples/simple_alu_x0_1.cqr (DECISIONS.md 2026-10-25).\n"
           f"-- Input layout: x[0] = op.0, x[1] = op.1, x[2..{1 + B}] = x1.0..{bit}, "
           f"x[{2 + B}..{n - 1}] = x2.0..{bit}.\n"
           f"fn simple_alu_x0_{bit}(x: Vec Bool {n}) -> Bool {{\n" + "\n".join(lets) + "\n" +
           body + "\n}\n")
    return n, src


def alu_ref(bit, bits):
    B = bit + 1
    op = int(bits[0]) | int(bits[1]) << 1
    x1 = sum(int(bits[2 + i]) << i for i in range(B))
    x2 = sum(int(bits[2 + B + i]) << i for i in range(B))
    return bd.alu_bit(op, x1, x2, 16, bit)


def alu_python_check(bit):
    """The transcription's Boolean formulas, evaluated in Python, equal the SyReC semantics at
    w = 16 and w = bit + 1 on every input (independent of the DSL)."""
    n = alu_layout(bit)
    B = bit + 1
    for x in range(2 ** n):
        bits = [(x >> k) & 1 == 1 for k in range(n)]
        op = int(bits[0]) | int(bits[1]) << 1
        a = bits[2:2 + B]
        b = bits[2 + B:2 + 2 * B]
        if bit == 0:
            add = sub = xor = a[0] != b[0]
            mul = a[0] and b[0]
        else:
            c0 = a[0] and b[0]
            c1 = (a[1] and b[1]) != (c0 and (a[1] != b[1]))
            add = (a[2] != b[2]) != c1
            w0 = (not a[0]) and b[0]
            w1 = ((not a[1]) and b[1]) != (w0 and not (a[1] != b[1]))
            sub = (a[2] != b[2]) != w1
            mul = ((a[0] and b[2]) != (a[1] and b[1])) != ((a[2] and b[0]) !=
                                                           ((a[0] and b[1]) and (a[1] and b[0])))
            xor = a[2] != b[2]
        val = [add, sub, mul, xor][op]
        x1 = sum(int(a[i]) << i for i in range(B))
        x2 = sum(int(b[i]) << i for i in range(B))
        assert val == bd.alu_bit(op, x1, x2, 16, bit) == bd.alu_bit(op, x1, x2, B, bit), \
            (bit, x, op, x1, x2)


# --- references (used by scripts/bench_scaling.py) -------------------------------------------

def reference(inst, bits):
    """The reference value of an instance on input bits (bits[k] = input bit k), computed
    without the DSL or the network."""
    fam = inst["family"]
    if fam == "carry_k":
        return carry_ref(inst["k"], bits)
    if fam == "alu_bits":
        return alu_ref(inst["bit"], bits)
    if fam == "rand_a":
        return bool(od.evaluate(inst["tree"], bits))
    raise ValueError(fam)


# --- cqr helpers -----------------------------------------------------------------------------

def run(cmd):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    return p.returncode, p.stdout.replace("\r\n", "\n"), p.stderr


def truth_table(cqr, path):
    rc, so, se = run([cqr, "check", path, "--truth-table"])
    if rc != 0:
        raise RuntimeError(f"check --truth-table {path}: {so or se}")
    d = json.loads(so.strip())
    assert d["evaluator"] == d["network"], f"{path}: evaluator != network"
    return d["n"], d["network"]


def synth(cqr, path):
    rc, so, se = run([cqr, "synthesize", path, "--json"])
    if rc != 0:
        raise RuntimeError(f"synthesize {path}: {so or se}")
    return json.loads(so.strip().splitlines()[0])


def r_star(n, M):
    theta = math.asin(math.sqrt(M / 2 ** n))
    return math.floor(math.pi / (4 * theta))


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def finish(cqr, inst, path):
    """M from the truth table, cross-checked with the reference; r⋆ (cross-checked with cqr)."""
    n, table = truth_table(cqr, path)
    assert n == inst["n"], (n, inst)
    ref = "".join("1" if reference(inst, [(x >> k) & 1 == 1 for k in range(n)]) else "0"
                  for x in range(2 ** n))
    assert ref == table, f"{inst['name']}: reference != network truth table"
    M = table.count("1")
    assert 0 < M < 2 ** n, (inst["name"], M)
    rs = r_star(n, M)
    rc, so, se = run([cqr, "synthesize", path, "--grover", "--solutions", str(M), "--json"])
    assert rc == 0, (inst["name"], so, se)
    g = json.loads(so.strip().splitlines()[0])
    assert g["r_star"] == rs, (inst["name"], g["r_star"], rs)
    o = synth(cqr, path)
    inst.update(M=M, r_star=rs, iterations=[1] + ([rs] if 1 < rs <= 4 else []),
                oracle_a=o["grade"]["a"], and_complexity=o["and_complexity"],
                path=os.path.relpath(path, ROOT).replace("\\", "/"))
    return inst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--attempts", type=int, default=4000)
    args = ap.parse_args()
    cqr = os.path.abspath(args.cqr)
    os.makedirs(OUT, exist_ok=True)
    insts = []

    for k in range(1, 9):
        n, src = carry_source(k)
        path = os.path.join(OUT, f"carry_{k}.cqr")
        write(path, src)
        inst = {"name": f"carry_{k}", "family": "carry_k", "n": n, "k": k}
        finish(cqr, inst, path)
        assert inst["M"] == 2 ** (2 * k - 1) - 2 ** (k - 1), inst
        insts.append(inst)
        print(f"carry_{k}: n = {n}, M = {inst['M']}, r* = {inst['r_star']}, a = {inst['oracle_a']}")

    with tempfile.TemporaryDirectory() as tmp:
        for target in RAND_TARGETS:
            n = 6 if target == 16 else 12
            rng = np.random.default_rng(SEED + target)
            found = None
            for attempt in range(args.attempts):
                leaves = int(rng.integers(target + 1, 3 * target + 2))
                t = od.gen_tree(rng, n, leaves, ["and", "xor", "if"])
                path = od.write_src(tmp, "cand", n, od.render(t))
                try:
                    o = synth(cqr, path)
                except RuntimeError:
                    continue
                if o["grade"]["a"] != target:
                    continue
                tab = truth_table(cqr, path)[1]
                if tab.count("1") in (0, 2 ** n):
                    continue
                found = (attempt, t)
                break
            assert found is not None, f"rand_a: no predicate with a = {target} in {args.attempts} attempts"
            attempt, t = found
            name = f"rand_a{target}"
            path = os.path.join(OUT, f"{name}.cqr")
            write(path, f"-- Stage 14b, family rand_a: oracle_diff.gen_tree(rng, {n}, leaves, "
                        f"[\"and\", \"xor\", \"if\"]), seed {SEED + target}, attempt {attempt}, "
                        f"target a = {target} AND nodes after synthesis.\n"
                        f"fn {name}(x: Vec Bool {n}) -> Bool {{\n  {od.render(t)}\n}}\n")
            inst = {"name": name, "family": "rand_a", "n": n, "target_a": target,
                    "seed": SEED + target, "attempt": attempt, "tree": t}
            finish(cqr, inst, path)
            assert inst["oracle_a"] == target
            insts.append(inst)
            print(f"{name}: n = {n}, leaves {leaves}, attempt {attempt}, M = {inst['M']}, "
                  f"r* = {inst['r_star']}, a = {inst['oracle_a']}")

    for bit in (0, 2):
        alu_python_check(bit)
        n, src = alu_source(bit)
        path = os.path.join(OUT, f"simple_alu_x0_{bit}.cqr")
        write(path, src)
        inst = {"name": f"simple_alu_x0_{bit}", "family": "alu_bits", "n": n, "bit": bit}
        finish(cqr, inst, path)
        insts.append(inst)
        print(f"simple_alu_x0_{bit}: n = {n}, M = {inst['M']}, r* = {inst['r_star']}, "
              f"a = {inst['oracle_a']}")

    def default(o):
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, (np.bool_,)):
            return bool(o)
        raise TypeError(type(o))

    with open(os.path.join(OUT, "manifest.json"), "w", encoding="utf-8", newline="\n") as f:
        json.dump({"seed": SEED, "instances": insts}, f, indent=1, ensure_ascii=False,
                  default=default)
        f.write("\n")
    print(f"gen_scaling: {len(insts)} instances written to bench/scaling/")


if __name__ == "__main__":
    main()
