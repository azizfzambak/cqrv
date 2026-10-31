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
  5. every QIR text is parsed and verified by LLVM through llvmlite (pinned in
     requirements.txt; mandatory, never skipped — Stage 8a review); in addition `llvm-as`
     assembles it when it is on PATH (CI, where --require-llvm-as makes it mandatory too),
     otherwise that second check is skipped with a message.

Stage 17b (PHASE2_SPEC.md §A.1), the sample circuit `CQRV.Emit.sampleCircuit` (every gate
constructor, the exact phase gates `p` / `cp` included, which no synthesized circuit contains;
`scripts/CertifyTool.lean emit-sample`):
  6. its OpenQASM 3 text re-parses exactly to its IR JSON (`p(2*pi*a/N)` with the evaluated
     power, `(-a)` for a negative numerator, `cp` under `if` as well), also without the
     alloc/free annotations; a changed denominator is caught (negative control);
  7. its QIR text re-parses to the IR after `Circuit.decomposeCp` (`emit-sample json
     --decompose-cp`): a top-level `cp` is the five calls rz, rz, cnot, rz, cnot, `p a k` is `rz`
     with the hex-float angle 2πa/2^k matched to 1e-12·(1 + |angle|) on the same qubits, the `rz`
     declaration present exactly once; LLVM verifies it (llvmlite, and llvm-as as above);
  8. the negative case `--if-cp` (one `ifBit` over `cp 1 1`): the QASM text re-parses to its IR
     (QASM is unaffected), the QIR emitter exits 1 with the diagnostic `unsupported_in_qir`
     (stage `emit`) and prints no module;
  9. the Grover texts carry no `rz` and no `rz` declaration (the committed .qir files are
     byte-identical to Stage 16b; certify_check.py asserts it).

Usage: python -I tests/diff/emit_diff.py --cqr <path to cqr> [--seed S] [--require-llvm-as]
"""

import argparse
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

import llvmlite
import llvmlite.binding as llvm
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import reparse_qasm  # noqa: E402
import reparse_qir  # noqa: E402
import statevector as sv  # noqa: E402
from lean_tool import certify_tool, certify_tool_run  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "examples", "grover_pred_037.cqr")
N_DATA, N_QUBITS = 8, 15


def run(cqr, args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit(f"cqr {' '.join(args)} failed ({p.returncode}): {p.stdout}{p.stderr}")
    return p.stdout


ANGLE_TOL = 1e-12


def gate_equal(g, w):
    """Re-parsed gate `g` = Lean gate `w`; a QIR `rz` (op p with `angle`) matches a Lean `p a k`
    on the same qubits (and `if`) when |angle − 2πa/2^k| ≤ 1e-12·(1 + |angle|) (Stage 17b)."""
    if "angle" in g:
        if w.get("op") != "p" or g["q"] != w["q"] or g.get("if") != w.get("if"):
            return False
        want = 2 * math.pi * w["a"] / 2 ** w["k"]
        return abs(g["angle"] - want) <= ANGLE_TOL * (1 + abs(g["angle"]))
    return g == w


def first_difference(got, want):
    for key in ("n_data", "n_anc"):
        if got[key] != want[key]:
            return f"{key}: re-parsed {got[key]}, Lean {want[key]}"
    for k, (g, w) in enumerate(zip(got["gates"], want["gates"])):
        if not gate_equal(g, w):
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


def llvm_verify(label, text):
    """Mandatory: LLVM's parser and module verifier (llvmlite), every platform."""
    try:
        mod = llvm.parse_assembly(text)
        mod.verify()
    except RuntimeError as e:
        raise AssertionError(f"LLVM rejects {label}: {e}")
    print(f"ok:   {label} [qir] parsed and verified by LLVM "
          f"{'.'.join(map(str, llvm.llvm_version_info))} (llvmlite {llvmlite.__version__})")


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


def check_sample(require_llvm_as):
    """Stage 17b: the sample circuit through both emitters (items 6–8 of the module doc)."""
    ir = json.loads(certify_tool(["emit-sample", "json"]))
    ops = [g["op"] for g in ir["gates"]]
    for op in ("h", "s", "sdg", "t", "tdg", "x", "z", "cnot", "cz", "p", "cp", "measure", "alloc",
               "free"):
        assert op in ops, f"sample circuit lacks {op}"
    assert any(g["op"] == "p" and "if" in g for g in ir["gates"]), "sample: no if over p"
    assert not any(g["op"] == "cp" and "if" in g for g in ir["gates"]), "sample: if over cp"
    assert {(g["a"], g["k"]) for g in ir["gates"] if g["op"] == "p"} >= {(1, 3), (-3, 5), (2, 4), (0, 5)}
    assert {(g["a"], g["k"]) for g in ir["gates"] if g["op"] == "cp"} == {(1, 1), (1, 2), (-1, 3)}
    # QASM: exact round trip, with and without the annotations
    qasm = certify_tool(["emit-sample", "qasm"])
    for frag in ("p(2*pi*(-3)/32) x[1];", "cp(2*pi*1/2) x[0], x[1];", "if (c[0]) { p(2*pi*1/4) x[1]; }"):
        assert frag in qasm, frag
    check_roundtrip("sample circuit", "qasm", qasm, ir)
    bad = qasm.replace("p(2*pi*1/8) x[0];", "p(2*pi*1/16) x[0];", 1)
    try:
        check_roundtrip("negative control (sample)", "qasm", bad, ir)
    except AssertionError as e:
        print(f"ok:   negative control (sample, k of a p gate) rejected ({str(e).split(' — ')[-1]})")
    else:
        raise AssertionError("negative control: a changed phase denominator was not detected")
    # QIR: against the IR after decomposeCp, angles to 1e-12; rz declared once; LLVM verifies
    dec = json.loads(certify_tool(["emit-sample", "json", "--decompose-cp"]))
    n_cp = sum(1 for g in ir["gates"] if g["op"] == "cp")
    assert n_cp == 3 and len(dec["gates"]) == len(ir["gates"]) + 4 * n_cp, "decomposeCp size"
    assert not any(g["op"] == "cp" for g in dec["gates"]), "a top-level cp survived decomposeCp"
    qir = certify_tool(["emit-sample", "qir"])
    got = check_roundtrip("sample circuit (decomposeCp)", "qir", qir, dec)
    n_rz = sum(1 for g in got["gates"] if "angle" in g)
    assert n_rz == sum(1 for g in dec["gates"] if g["op"] == "p") == 4 + 3 * n_cp + 2, n_rz
    assert qir.count("declare void @__quantum__qis__rz__body(double, ptr)\n") == 1, "rz declaration"
    assert '"required_num_qubits"="4"' in qir, "sample: 3 data + 1 ancilla"
    llvm_verify("sample circuit", qir)
    llvm_as("sample circuit", qir, require_llvm_as)
    print(f"ok:   sample circuit [qir] {n_rz} rz calls with hex-float angles = the Lean p gates "
          f"after decomposeCp (3 cp -> 15 calls), angles within {ANGLE_TOL:g}, rz declared once")
    # the negative case: ifBit over cp — QASM fine, QIR refused with the diagnostic
    ir_if = json.loads(certify_tool(["emit-sample", "json", "--if-cp"]))
    assert any(g["op"] == "cp" and g.get("if") == 0 for g in ir_if["gates"]), "if-cp sample"
    check_roundtrip("sample circuit (--if-cp)", "qasm", certify_tool(["emit-sample", "qasm", "--if-cp"]), ir_if)
    p = certify_tool_run(["emit-sample", "qir", "--if-cp"])
    assert p.returncode == 1, (p.returncode, p.stdout, p.stderr)
    d = json.loads(p.stdout.strip().split("\n")[-1])
    assert d["code"] == "unsupported_in_qir" and d["stage"] == "emit", d
    assert "classically controlled cp has no QIR form" in d["message"], d
    assert "define i64" not in p.stdout, "a QIR module was printed with the diagnostic"
    print(f"ok:   sample circuit with an ifBit over cp: QASM re-parses; QIR refused (exit 1, "
          f"{d['stage']} / {d['code']}: {d['message']})")


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
            assert "rz" not in text, f"{label} [{fmt}]: a synthesized circuit has no phase gate"
            if fmt == "qir":
                if "oracle" not in label:
                    check_qir_shape(label, text)
                llvm_verify(label, text)
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
    # negative control for the LLVM check: a branch to an undefined block must be rejected
    text = run(args.cqr, ["emit", SRC, "--format", "qir", "--oracle"])
    try:
        llvm_verify("negative control", text.replace("\nmeasurements:\n", "\n", 1))
    except AssertionError:
        print("ok:   negative control rejected by LLVM (undefined block `measurements`)")
    else:
        raise AssertionError("negative control: LLVM accepted a module with an undefined block")
    # Stage 17b: the sample circuit (p / cp) through both emitters, and the negative --if-cp case
    check_sample(args.require_llvm_as)
    print("emit_diff: all checks passed")


if __name__ == "__main__":
    main()
