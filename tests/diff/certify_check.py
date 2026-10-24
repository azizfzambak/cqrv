"""`cqr certify` checks (report §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3; Stage 8b acceptance).

Runs the built `cqr` from the project root and checks

  * grover_pred_037: exit 0, status line `certified (conditional on: solution_count = 32)`,
    certificate.json valid against docs/certificate.schema.json (v1.2.0), grade (15, 230, 72, 7),
    delta "7/128", axioms exactly propext, Classical.choice, Quot.sound, no obligations;
  * the hash link, independently of the CLI: the `emitted` IR literal of Cert.lean (the circuit
    the kernel-checked theorem is about) is parsed here, its canonical JSON hashed with hashlib
    and compared with hashes.circuit; the .qasm / .qir files re-parse to exactly that literal;
    hashes.proof is recomputed from Cert.lean and the pinned configuration;
  * reproducibility: a second run gives byte-identical Cert.lean / .qir / .qasm and the same JSON
    except the timing field reference_configuration.kernel_check; the committed example
    examples/certs/grover_pred_037/ agrees with the run (JSON modulo the machine fields);
  * negative tests (must not say "certified"): (a) the XOR predicate tests/certify/xor_pred.cqr
    (--solutions 4) → exit 3, `certificate with tracked obligations: lemma_6_3_2_xor`, sorryAx
    in the axioms; (b) the committed Cert.lean with the proof of `cert` replaced by `sorry` (temp
    copy) → audit fails with sorryAx; (b') with one side condition by `native_decide` → audit
    fails with its auxiliary axiom (`nAnc_eq._native.native_decide.ax_1_1` in Lean 4.35;
    `Lean.ofReduceBool` in older versions); (c) examples/search_while.cqr --solutions 64 → the
    Stage 4 repair hint (no_matching_pattern), exit 1.

Usage: python -I tests/diff/certify_check.py --cqr <path to cqr>   (after `lake build`)
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

import jsonschema

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import ROOT  # noqa: E402
import reparse_qasm  # noqa: E402
import reparse_qir  # noqa: E402

SCHEMA = os.path.join(ROOT, "docs", "certificate.schema.json")
EXAMPLE = os.path.join(ROOT, "examples", "certs", "grover_pred_037")
NAME = "grover_pred_037"
THEOREM = "CQRV.Cert.grover_pred_037.cert"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
MACHINE = ("cpu", "logical_cpus", "clock", "lean_threads", "kernel_check")


def sha3(b):
    return hashlib.sha3_256(b).hexdigest()


def read(path, mode="r"):
    with open(path, mode, **({} if "b" in mode else {"encoding": "utf-8", "newline": ""})) as f:
        return f.read()


def run(cmd):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    return p.returncode, p.stdout.replace("\r\n", "\n"), p.stderr.replace("\r\n", "\n")


def certify(cqr, src, out, *extra):
    return run([cqr, "certify", src, "--out", out, *extra])


# --- the IR literal of Cert.lean -------------------------------------------------------------

def split_top(s):
    """Split at commas outside parentheses."""
    items, depth, cur = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            items.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        items.append("".join(cur).strip())
    return items


RE_Q = re.compile(r"\(\.(data|anc) (\d+)\)")


def parse_gate(s, n_data):
    m = re.fullmatch(r"\.ifBit (\d+) \((.*)\)", s)
    if m:
        g = parse_gate(m.group(2), n_data)
        g["if"] = int(m.group(1))
        return g
    m = re.fullmatch(r"\.(\w+)((?: \(\.(?:data|anc) \d+\))+)(?: (\d+))?", s)
    if not m:
        raise ValueError(f"bad gate literal: {s}")
    qs = [int(i) if k == "data" else n_data + int(i) for k, i in RE_Q.findall(m.group(2))]
    g = {"op": m.group(1), "q": qs}
    if m.group(3) is not None:
        g["c"] = int(m.group(3))
    return g


def emitted_circuit(cert_text):
    m = re.search(r"def emitted : Circuit := ⟨(\d+), \[(.*?)\]⟩", cert_text, re.S)
    if not m:
        raise AssertionError("no `def emitted : Circuit := ⟨n, [...]⟩` in Cert.lean")
    n = int(m.group(1))
    gates = [parse_gate(item, n) for item in split_top(m.group(2))]
    anc = [q - n for g in gates for q in g["q"] if q >= n]
    return {"n_data": n, "n_anc": max(anc) + 1 if anc else 0, "gates": gates}


def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def proof_hash(cert_text):
    manifest = json.loads(read(os.path.join(ROOT, "lake-manifest.json")))
    revs = {p["name"]: p["rev"] for p in manifest["packages"]}
    toolchain = read(os.path.join(ROOT, "lean-toolchain")).strip()
    parts = [cert_text.replace("\r\n", "\n"), "lean-toolchain=" + toolchain,
             "mathlib=" + revs["mathlib"], "physlib=" + revs["Physlib"]]
    return sha3(b"\x00".join(p.encode("utf-8") for p in parts))


def check_dir(d, validator):
    """Schema, hash link, proof hash and emitted files of one certify output directory."""
    cert = json.loads(read(os.path.join(d, "certificate.json")))
    validator.validate(cert)
    text = read(os.path.join(d, "Cert.lean"))
    circ = emitted_circuit(text)
    assert cert["hashes"]["circuit"] == sha3(canon(circ).encode("utf-8")), "circuit hash"
    assert cert["hashes"]["proof"] == proof_hash(text), "proof hash"
    name = cert["theorem"].split(".")[-2]
    for fmt, mod in (("qasm", reparse_qasm), ("qir", reparse_qir)):
        parsed, terminal = mod.parse(read(os.path.join(d, f"{name}.{fmt}")))
        assert parsed == circ, f"{fmt} re-parse differs from the IR literal of Cert.lean"
        assert len(terminal) == circ["n_data"], f"{fmt} terminal measurement"
    return cert, text


def without(cert, keys):
    c = json.loads(json.dumps(cert))
    for k in keys:
        c["reference_configuration"].pop(k)
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    args = ap.parse_args()
    validator = jsonschema.Draft202012Validator(json.loads(read(SCHEMA)))
    tmp = tempfile.mkdtemp(prefix="cqrv-certify-")
    try:
        src = os.path.join("examples", f"{NAME}.cqr")
        runs = []
        for i in (1, 2):
            out = os.path.join(tmp, f"run{i}")
            rc, so, se = certify(args.cqr, src, out)
            assert rc == 0, (rc, so, se)
            assert so.rstrip("\n").split("\n")[-1] == \
                "certified (conditional on: solution_count = 32)", so
            runs.append(out)
        print("ok:   status line `certified (conditional on: solution_count = 32)` (exit 0)")
        cert, text = check_dir(runs[0], validator)
        assert cert["status"] == "certified" and cert["obligations"] == []
        assert cert["grade"] == {"w": 15, "d": 230, "t": 72, "a": 7}, cert["grade"]
        assert cert["spec"]["delta"] == "7/128", cert["spec"]
        assert cert["axioms"] == STANDARD, cert["axioms"]
        assert cert["theorem"] == THEOREM
        print("ok:   JSON valid (schema v1.2.0); grade (15, 230, 72, 7), delta 7/128, "
              "axioms exactly propext, Classical.choice, Quot.sound")
        print("ok:   circuit hash = SHA3 of the IR literal of Cert.lean (hashlib); "
              ".qasm / .qir re-parse to that literal; proof hash recomputed")
        cert2, _ = check_dir(runs[1], validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(runs[0], f), "rb") == read(os.path.join(runs[1], f), "rb"), f
        assert without(cert, ["kernel_check"]) == without(cert2, ["kernel_check"])
        print("ok:   second run byte-identical (Cert.lean, .qir, .qasm; JSON except kernel_check)")
        ex, _ = check_dir(EXAMPLE, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(runs[0], f), "rb") == read(os.path.join(EXAMPLE, f), "rb"), \
                f"committed example differs: {f}"
        assert without(cert, MACHINE) == without(ex, MACHINE), "committed certificate.json"
        assert ex["reference_configuration"]["kernel_check"]["runs"] == 5
        print("ok:   committed examples/certs/grover_pred_037 agrees (JSON modulo machine fields)")

        # (a) XOR predicate: Lemma 6.3.2 for XOR is the tracked obligation lemma_6_3_2_xor
        out = os.path.join(tmp, "xor")
        rc, so, se = certify(args.cqr, os.path.join("tests", "certify", "xor_pred.cqr"), out,
                             "--solutions", "4")
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 3 and last == "certificate with tracked obligations: lemma_6_3_2_xor", \
            (rc, so, se)
        assert "certified (" not in so
        xc, _ = check_dir(out, validator)
        assert xc["status"] == "certificate with tracked obligations"
        assert xc["obligations"] == ["lemma_6_3_2_xor"] and "sorryAx" in xc["axioms"]
        print(f"ok:   (a) XOR predicate: `{last}` (exit 3; sorryAx in the axioms)")

        # (b) injected sorry, (b') native_decide, in temp copies of the committed certificate
        base = read(os.path.join(EXAMPLE, "Cert.lean"))
        proof = ("  grover_certificate oracle mcz (by decide) emitted_ok delta_eq grade_eq nAnc_eq "
                 "hM_card\n")
        nd = "theorem nAnc_eq : emitted.nAnc = 7 := by decide +kernel\n"
        assert base.count(proof) == 1 and base.count(nd) == 1
        for label, mutated, expect in (
                ("(b) injected sorry", base.replace(proof, "  sorry\n"), "sorryAx"),
                ("(b') native_decide",
                 base.replace(nd, nd.replace("decide +kernel", "native_decide")), "native_decide")):
            d = os.path.join(tmp, "mut")
            os.makedirs(d, exist_ok=True)
            path = os.path.join(d, "Cert.lean")
            with open(path, "w", encoding="utf-8", newline="\n") as f:
                f.write(mutated)
            rc, so, se = run(["lake", "env", "lean", "--run",
                              os.path.join("scripts", "CertifyTool.lean"), "audit", path, THEOREM])
            line = [ln for ln in so.split("\n") if ln.startswith("axiom audit:")]
            assert rc == 3 and line and "FAILED" in line[0] and expect in line[0], (rc, so, se)
            assert "certified (" not in so
            print(f"ok:   {label}: {line[0].replace(path, 'Cert.lean (temp copy)')}")

        # (c) search_while: outside the fragment, the Stage 4 hint
        rc, so, se = certify(args.cqr, os.path.join("examples", "search_while.cqr"),
                             os.path.join(tmp, "sw"), "--solutions", "64")
        hint = json.loads(so.strip().split("\n")[-1])
        assert rc == 1 and hint["code"] == "no_matching_pattern" and "certified (" not in so, \
            (rc, so, se)
        assert not os.path.exists(os.path.join(tmp, "sw")), "no certificate for a non-match"
        print(f"ok:   (c) search_while: hint {hint['code']} at {hint['location']} (exit 1)")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("certify_check: all checks passed")


if __name__ == "__main__":
    main()
