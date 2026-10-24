"""Translation validation of the QIR / OpenQASM 3 emitters (report §5.3, §8.4.3; Stage 8a,
reviewer decision 6).

For examples/grover_pred_037.cqr:
  1. the Grover circuit at r = 2 (default r*, and --iterations 2) and the phase oracle
     (--oracle) are emitted as QIR and as QASM by `cqr emit`; each text is re-parsed
     (reparse_qir.py / reparse_qasm.py) and must equal the Lean IR of `cqr synthesize --json`
     exactly (n_data, n_anc, every gate: op, qubits, bit, condition); the first differing gate
     is reported otherwise. The terminal measurement must be one block over the data register.
  2. the same with the `cqrv: alloc|free` annotations deleted from the text: the re-parse
     must equal the Lean IR without alloc/free (the annotations carry no gates);
  3. QIR shape: "qir_profiles"="adaptive_profile", required_num_qubits = 15, exactly one
     `measurements:` block with 8 `mz` on the data qubits;
  4. the re-parsed QASM oracle is executed by the Stage 5 harness (statevector.run_ir, every
     measurement branch) on random complex superpositions: U_P|psi> (x) |0..0> in every branch;
  5. `llvm-as` assembles every QIR text when it is on PATH (CI); otherwise the check is
     skipped with a message.

Usage: python -I tests/diff/emit_diff.py --cqr <path to cqr> [--seed S] [--require-llvm-as]
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import reparse_qasm  # noqa: E402
import reparse_qir  # noqa: E402
import statevector as sv  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "examples", "grover_pred_037.cqr")
N_DATA, N_QUBITS = 8, 15


def run(cqr, args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit(f"cqr {' '.join(args)} failed ({p.returncode}): {p.stdout}{p.stderr}")
    return p.stdout


def first_difference(got, want):
    for key in ("n_data", "n_anc"):
        if got[key] != want[key]:
            return f"{key}: re-parsed {got[key]}, Lean {want[key]}"
    for k, (g, w) in enumerate(zip(got["gates"], want["gates"])):
        if g != w:
            return f"gate {k}: re-parsed {g}, Lean {w}"
    if len(got["gates"]) != len(want["gates"]):
        return f"gate count: re-parsed {len(got['gates'])}, Lean {len(want['gates'])}"
    return None


def strip_annotations(text, fmt):
    mark = "  ; cqrv: " if fmt == "qir" else "// cqrv: "
    return "".join(ln for ln in text.splitlines(keepends=True) if not ln.startswith(mark))


def check_roundtrip(label, fmt, text, lean):
    parse = reparse_qir.parse if fmt == "qir" else reparse_qasm.parse
    got, terminal = parse(text)
    diff = first_difference(got, lean)
    if diff:
        raise AssertionError(f"{label} [{fmt}]: re-parsed IR differs from the Lean IR — {diff}")
    if [q for q, _ in terminal] != list(range(lean["n_data"])):
        raise AssertionError(f"{label} [{fmt}]: terminal measurement is not over x[0..n)")
    bare, _ = parse(strip_annotations(text, fmt))
    want = {**lean, "gates": [g for g in lean["gates"] if g["op"] not in ("alloc", "free")]}
    diff = first_difference(bare, want)
    if diff:
        raise AssertionError(f"{label} [{fmt}] without annotations: {diff}")
    print(f"ok:   {label} [{fmt}] re-parses to the Lean IR ({len(lean['gates'])} gates, "
          f"{len(terminal)} terminal measurements)")
    return got


def check_qir_shape(label, text):
    assert '"qir_profiles"="adaptive_profile"' in text, "no adaptive_profile attribute"
    assert f'"required_num_qubits"="{N_QUBITS}"' in text, "required_num_qubits != 15"
    lines = text.splitlines()
    assert lines.count("measurements:") == 1, "not exactly one measurements block"
    k = lines.index("measurements:")
    block = []
    for ln in lines[k + 1:]:
        if not ln.startswith("  call void @__quantum__qis__mz__body"):
            break
        block.append(ln)
    want = [f"  call void @__quantum__qis__mz__body(ptr inttoptr (i64 {q} to ptr), "
            for q in range(N_DATA)]
    assert len(block) == N_DATA and all(b.startswith(w) for b, w in zip(block, want)), \
        "the measurements block is not one mz per data qubit"
    print(f"ok:   {label} [qir] adaptive_profile, required_num_qubits = 15, one terminal "
          f"block of {N_DATA} mz")


def llvm_as(label, text, required):
    tool = shutil.which("llvm-as")
    if tool is None:
        msg = f"llvm-as not on PATH: QIR assembly check of {label} SKIPPED"
        if required:
            raise AssertionError(msg)
        print(f"skip: {msg}")
        return
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "m.ll")
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        p = subprocess.run([tool, path, "-o", os.devnull], capture_output=True, text=True)
        if p.returncode != 0:
            raise AssertionError(f"llvm-as rejects {label}: {p.stderr}")
    print(f"ok:   {label} [qir] assembles with {tool}")


def grover_pred(x):
    """P(x) = x0 AND x3 AND x7 on the data index (qubit 0 = most significant = x0)."""
    return bool((x >> 7) & 1 and (x >> 4) & 1 and x & 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--seed", type=int, default=20261024)
    ap.add_argument("--require-llvm-as", action="store_true")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    grover = json.loads(run(args.cqr, ["synthesize", SRC, "--grover", "--iterations", "2",
                                       "--json"]))
    assert grover["r_star"] == 2, grover["r_star"]
    oracle = json.loads(run(args.cqr, ["synthesize", SRC, "--json"]))["circuit"]
    cases = [("grover_pred_037 (r = r* = 2)", [], grover["circuit"]),
             ("grover_pred_037 (--iterations 2)", ["--iterations", "2"], grover["circuit"]),
             ("grover_pred_037 oracle", ["--oracle"], oracle)]
    for label, extra, lean in cases:
        for fmt in ("qir", "qasm"):
            text = run(args.cqr, ["emit", SRC, "--format", fmt, *extra])
            got = check_roundtrip(label, fmt, text, lean)
            if fmt == "qir":
                if "oracle" not in label:
                    check_qir_shape(label, text)
                llvm_as(label, text, args.require_llvm_as)
            elif "oracle" in label:
                # the re-parsed QASM oracle, executed by the Stage 5 harness, every branch
                n = sv.check_phase_oracle(got, grover_pred, rng, trials=4)
                print(f"ok:   {label} [qasm] re-parsed oracle = U_P in all {n} branches "
                      f"(4 random superpositions)")
    # negative control: one changed gate must be reported as the first difference
    text = run(args.cqr, ["emit", SRC, "--format", "qasm", "--oracle"])
    bad = text.replace("t anc[0];", "tdg anc[0];", 1)
    try:
        check_roundtrip("negative control", "qasm", bad, oracle)
    except AssertionError as e:
        print(f"ok:   negative control rejected ({str(e).split(' — ')[-1]})")
    else:
        raise AssertionError("negative control: a changed gate was not detected")
    print("emit_diff: all checks passed")


if __name__ == "__main__":
    main()
