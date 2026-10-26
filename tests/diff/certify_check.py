"""`cqr certify` checks (report §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3; Stage 8b acceptance).

Runs the built `cqr` from the project root and checks

  * grover_pred_037: exit 0, status line `certified (conditional on: solution_count = 32)`,
    certificate.json valid against docs/certificate.schema.json (v1.3.0), grade (15, 134, 72, 7),
    delta "7/128", axioms exactly propext, Classical.choice, Quot.sound, no obligations,
    trust_boundary.front_end = the exhaustive-validation wording for 2^8 inputs (Stage 9b);
  * the hash link, independently of the CLI: the `emitted` IR literal of Cert.lean (the circuit
    the kernel-checked theorem is about) is parsed here, its canonical JSON hashed with hashlib
    and compared with hashes.circuit; the .qasm / .qir files re-parse to exactly that literal;
    hashes.proof is recomputed from Cert.lean and the pinned configuration;
  * reproducibility: a second run gives byte-identical Cert.lean / .qir / .qasm and the same JSON
    except the timing field reference_configuration.kernel_check; the committed example
    examples/certs/grover_pred_037/ agrees with the run (JSON modulo the machine fields);
  * the second worked predicate examples/simple_alu_x0_1.cqr (RevLib Simple ALU, bit 1 of x0;
    Stage 9b): M = 30 recounted here from the SyReC semantics (benchmark_diff.reference),
    --solutions 30 → exit 0, `certified (conditional on: solution_count = 30)`, r = 1, delta
    833/2048, grade (16, 121, 60, 10), front end validated on 2^6 inputs; the committed
    examples/certs/simple_alu_x0_1/ agrees with the run;
  * the committed run reports (run_report.md / run_report.json, Stage 9b decision 4) of both
    examples: 9 rows in the order of Table 8.5.2 (stage 1 as 1a parser / surface checker and 1b
    typed AST → network, Stage 9b review), each verification one of the four words, the
    measured grade, delta, kernel time and axioms equal to those of the committed
    certificate.json;
  * the XOR predicate tests/certify/xor_pred.cqr (--solutions 4; Stage 9a, `lemma_6_3_2_xor`
    proved): exit 0, `certified (conditional on: solution_count = 4)`, schema, hash link, axioms
    exactly the standard three, no obligations;
  * the `if` predicate tests/certify/if_pred.cqr (`(if x0 then x1 else x2 ⊕ x3) ∧ x4 ∧ x5`;
    Stage 9a review): M = 8 recounted here by brute force over the 64 inputs, then
    --solutions 8 → exit 0, `certified (conditional on: solution_count = 8)`, r = 2, delta 7/128,
    axioms exactly the standard three, no obligations;
  * negative tests (must not say "certified"): (a) a network that fails `C.WF`: the committed
    Cert.lean with the input node `.input 7` of `net` replaced by `.input 8` (a data qubit outside
    the 8-qubit register; temp copy) → the kernel check fails (exit 1); (b) the committed Cert.lean with the proof of `cert` replaced by `sorry` (temp
    copy) → audit fails with sorryAx; (b') with one side condition by `native_decide` → audit
    fails with its auxiliary axiom (`nAnc_eq._native.native_decide.ax_1_1` in Lean 4.35;
    `Lean.ofReduceBool` in older versions); (c) examples/search_while.cqr --solutions 64 → the
    Stage 4 repair hint (no_matching_pattern), exit 1;
  * without --profile (Stage 11b): the certificate.json of each example run is byte-identical
    to the committed one outside the object reference_configuration (machine and timing
    fields), schema_version "1.3.0", no `hardware`;
  * --profile ibm_kyiv (Stage 11b; profiles/ibm_kyiv.json, report Table 3.5 / §3.3.3):
    grover_pred_037 → exit 0, the status line unchanged, then
    `hardware profile ibm_kyiv: fits all budgets; δ_hw ≤ 7/128 + 390·1/100 = 2531/640
    (vacuous)` (since Stage 12a: tree diffusion, d = 134 ≤ 200; the chain's 230 exceeded it);
    simple_alu_x0_1 → fits all budgets, δ_hw vacuous as well (G·p̄ = 3.45).
    Every field of `hardware` is recomputed here (components against the profile file, G,
    δ_hw = δ + G·p̄ with fractions, vacuous, profile_hash = SHA3 of the file with LF); the rest of
    the certificate equals the run without --profile (except schema_version "1.4.0"); Cert.lean,
    .qir, .qasm are byte-identical to the committed ones; the run report has the extra row
    "Hardware profile" with status "checked against declared profile (not a proof about
    hardware)".

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
from fractions import Fraction

import jsonschema

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import ROOT  # noqa: E402
import benchmark_diff  # noqa: E402
import reparse_qasm  # noqa: E402
import reparse_qir  # noqa: E402

SCHEMA = os.path.join(ROOT, "docs", "certificate.schema.json")
EXAMPLE = os.path.join(ROOT, "examples", "certs", "grover_pred_037")
NAME = "grover_pred_037"
THEOREM = "CQRV.Cert.grover_pred_037.cert"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
MACHINE = ("cpu", "logical_cpus", "clock", "lean_threads", "kernel_check")
STAGES = ["1a. DSL Input: parser, surface checker", "1b. DSL Input: typed AST → network",
          "2. Spec Extraction", "3. Pattern Matching", "4. QPLP Instant.",
          "5. Oracle Synthesis", "6. Ancilla Restore", "7. Certificate Gen", "8. QIR Export"]
VERIFICATION = {"kernel-checked", "exhaustively validated", "declared trust boundary",
                "unverified"}


def validated(n):
    return (f"DSL → network: exhaustively validated (2^{n} inputs) by the unverified evaluator; "
            "not kernel-checked")


def secs(ms):
    c = (ms + 5) // 10
    return f"{c // 100}.{c % 100:02d} s"


def check_report(d, cert):
    """The committed run report of a certificate directory agrees with its certificate.json."""
    rep = json.loads(read(os.path.join(d, "run_report.json")))
    md = read(os.path.join(d, "run_report.md"))
    assert [r["stage"] for r in rep["rows"]] == STAGES, [r["stage"] for r in rep["rows"]]
    assert all(r["verification"] in VERIFICATION for r in rep["rows"]), rep["rows"]
    status = "certified (conditional on: solution_count = {})".format(cert["instance"]["M"])
    assert rep["status"] == status and rep["certified"] is True, rep["status"]
    rows = {r["stage"]: r for r in rep["rows"]}
    g = cert["grade"]
    assert f"({g['w']}, {g['d']}, {g['t']}, {g['a']})" in rows["4. QPLP Instant."]["resources"]
    assert f"δ = {cert['spec']['delta']} exact" in rows["4. QPLP Instant."]["resources"]
    kc = cert["reference_configuration"]["kernel_check"]
    res7 = rows["7. Certificate Gen"]["resources"]
    assert f"kernel {secs(kc['kernel_ms'])}" in res7 and f"wall {secs(kc['wall_ms'])}" in res7, \
        (res7, kc)
    assert ", ".join(cert["axioms"]) in res7
    assert f"G = {cert['hardware_perturbation']['G']} " in rows["8. QIR Export"]["resources"]
    assert rows[STAGES[0]]["verification"] == "declared trust boundary"
    assert "shared by both sides of the comparison" in rows[STAGES[0]]["note"]
    assert rows[STAGES[1]]["verification"] == "exhaustively validated"
    assert cert["trust_boundary"]["front_end"] in rows[STAGES[1]]["note"]
    assert [r["verification"] for r in rep["rows"][4:8]] == ["kernel-checked"] * 4
    assert rows["8. QIR Export"]["verification"] == "declared trust boundary"
    assert md.count("\n| ") == 10 and all(st in md for st in STAGES), "run_report.md table"
    return rep


def sha3(b):
    return hashlib.sha3_256(b).hexdigest()


KYIV = os.path.join(ROOT, "profiles", "ibm_kyiv.json")
HW_STATUS = "checked against declared profile (not a proof about hardware)"
HW_NOTE = "routing, native gates and calibration are outside the trust boundary"
RE_REFCONF = re.compile(r'"reference_configuration":\{[^{}]*(?:\{[^{}]*\}|null)[^{}]*\}')


def rat(q):
    """Lean's `toString` of a `Rat`."""
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def masked(text):
    """certificate.json text with the object reference_configuration (machine and timing
    fields) masked; everything else byte for byte."""
    out, k = RE_REFCONF.subn('"reference_configuration":<masked>', text)
    assert k == 1, "reference_configuration not found exactly once"
    return out


def check_hardware(d, cert, plain, last_two, fits):
    """The `hardware` object of a --profile run, recomputed; the rest equals `plain`."""
    prof = json.loads(read(KYIV))
    h = cert["hardware"]
    assert cert["schema_version"] == "1.4.0", cert["schema_version"]
    assert h["profile"] == "ibm_kyiv" and h["note"] == HW_NOTE, h
    assert h["profile_hash"] == sha3(read(KYIV, "rb").replace(b"\r\n", b"\n")), "profile hash"
    names = {"w": "width", "d": "depth", "t": "T-count", "a": "ancilla"}
    over = []
    for k in "wdta":
        req, bud = cert["grade"][k], prof["budget"][k]
        ok = bud is None or req <= bud
        assert h["components"][k] == {"required": req, "budget": bud, "fits": ok}, (k, h)
        if not ok:
            over.append(f"{names[k]} budget ({req} > {bud})")
    assert h["fits"] == (not over) == fits, h
    G = cert["hardware_perturbation"]["G"]
    pbar = Fraction(prof["p_bar"])
    delta = Fraction(cert["spec"]["delta"])
    dhw = delta + G * pbar
    assert (h["G"], h["p_bar"], h["delta_hw"], h["vacuous"]) == (G, rat(pbar), rat(dhw), dhw >= 1), h
    line = (f"hardware profile ibm_kyiv: {'exceeds ' + ', '.join(over) if over else 'fits all budgets'}; "
            f"δ_hw ≤ {rat(delta)} + {G}·{rat(pbar)} = {rat(dhw)}{' (vacuous)' if dhw >= 1 else ''}")
    status = "certified (conditional on: solution_count = {})".format(cert["instance"]["M"])
    assert last_two == [status, line], (last_two, line)
    rest = {k: v for k, v in cert.items() if k not in ("hardware", "schema_version")}
    base = {k: v for k, v in plain.items() if k != "schema_version"}
    assert without(rest, ["kernel_check"]) == without(base, ["kernel_check"]), "rest of the JSON"
    rep = json.loads(read(os.path.join(d, "run_report.json")))
    assert [r["stage"] for r in rep["rows"]] == STAGES + ["Hardware profile"], rep["rows"]
    row = rep["rows"][-1]
    assert row["verification"] == HW_STATUS and row["output"] == line, row
    assert HW_NOTE in row["note"] and f"G = {G}" in row["resources"], row
    md = read(os.path.join(d, "run_report.md"))
    assert md.count("\n| ") == 11 and HW_STATUS in md, "run_report.md table"
    return line


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
        assert cert["grade"] == {"w": 15, "d": 134, "t": 72, "a": 7}, cert["grade"]
        assert cert["spec"]["delta"] == "7/128", cert["spec"]
        assert cert["axioms"] == STANDARD, cert["axioms"]
        assert cert["theorem"] == THEOREM
        assert cert["trust_boundary"]["front_end"] == validated(8), cert["trust_boundary"]
        print("ok:   JSON valid (schema v1.3.0); grade (15, 134, 72, 7), delta 7/128, "
              "axioms exactly propext, Classical.choice, Quot.sound; front end validated "
              "on 2^8 inputs")
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
        assert masked(read(os.path.join(runs[0], "certificate.json"))) == \
            masked(read(os.path.join(EXAMPLE, "certificate.json"))), "certificate.json bytes"
        assert cert["schema_version"] == "1.3.0" and "hardware" not in cert
        print("ok:   without --profile: certificate.json byte-identical to the committed one "
              "outside reference_configuration (schema_version 1.3.0, no hardware)")

        # --profile ibm_kyiv (Stage 11b)
        out = os.path.join(tmp, "kyiv")
        rc, so, se = certify(args.cqr, src, out, "--profile", "ibm_kyiv", "--report")
        assert rc == 0, (rc, so, se)
        kc, _ = check_dir(out, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(out, f), "rb") == read(os.path.join(EXAMPLE, f), "rb"), f
        line = check_hardware(out, kc, cert, so.rstrip("\n").split("\n")[-2:], fits=True)
        assert line == ("hardware profile ibm_kyiv: fits all budgets; "
                        "δ_hw ≤ 7/128 + 390·1/100 = 2531/640 (vacuous)"), line
        print("ok:   --profile ibm_kyiv: status line unchanged (exit 0); fits all budgets "
              "(d = 134 <= 200, tree diffusion), delta_hw = 7/128 + 390*1/100 = 2531/640 "
              "(vacuous); hardware recomputed; run report row 'Hardware profile'; "
              "Cert.lean / .qir / .qasm = committed")

        # The second worked predicate (Stage 9b): RevLib Simple ALU, bit 1 of x0
        m = sum(1 for x in range(64)
                if benchmark_diff.reference(benchmark_diff.input_bits(x)))
        assert m == 30, m
        alu = "simple_alu_x0_1"
        out = os.path.join(tmp, alu)
        rc, so, se = certify(args.cqr, os.path.join("examples", f"{alu}.cqr"), out,
                             "--solutions", str(m))
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 0 and last == "certified (conditional on: solution_count = 30)", (rc, so, se)
        ac, atext = check_dir(out, validator)
        assert ac["status"] == "certified" and ac["obligations"] == []
        assert ac["axioms"] == STANDARD, ac["axioms"]
        assert ac["instance"] == {"n": 6, "M": 30, "r": 1}, ac["instance"]
        assert ac["spec"]["delta"] == "833/2048", ac["spec"]
        assert ac["grade"] == {"w": 16, "d": 121, "t": 60, "a": 10}, ac["grade"]
        assert ac["trust_boundary"]["front_end"] == validated(6)
        assert "sorry" not in atext and ".xor " in atext
        exa = os.path.join(ROOT, "examples", "certs", alu)
        ea, _ = check_dir(exa, validator)
        for f in ("Cert.lean", f"{alu}.qir", f"{alu}.qasm"):
            assert read(os.path.join(out, f), "rb") == read(os.path.join(exa, f), "rb"), \
                f"committed example differs: {f}"
        assert without(ac, MACHINE) == without(ea, MACHINE), "committed certificate.json"
        assert ea["reference_configuration"]["kernel_check"]["runs"] == 5
        assert masked(read(os.path.join(out, "certificate.json"))) == \
            masked(read(os.path.join(exa, "certificate.json"))), "certificate.json bytes"
        out_k = os.path.join(tmp, alu + "_kyiv")
        rc, so, se = certify(args.cqr, os.path.join("examples", f"{alu}.cqr"), out_k,
                             "--solutions", str(m), "--profile", "ibm_kyiv", "--report")
        assert rc == 0, (rc, so, se)
        akc, _ = check_dir(out_k, validator)
        line = check_hardware(out_k, akc, ac, so.rstrip("\n").split("\n")[-2:], fits=True)
        assert line == ("hardware profile ibm_kyiv: fits all budgets; "
                        "δ_hw ≤ 833/2048 + 345·1/100 = 39493/10240 (vacuous)"), line
        print("ok:   simple_alu_x0_1: certificate.json byte-identical to the committed one outside "
              "reference_configuration; --profile ibm_kyiv: fits all budgets, delta_hw = "
              "833/2048 + 345*1/100 = 39493/10240 (vacuous: G*p_bar = 3.45 >= 1)")
        print(f"ok:   second predicate {alu} (M = 30 from the SyReC semantics): `{last}` (exit 0; "
              "r = 1, delta 833/2048, grade (16, 121, 60, 10), front end validated on 2^6 "
              "inputs); committed examples/certs/simple_alu_x0_1 agrees")
        for d, c in ((EXAMPLE, ex), (exa, ea)):
            check_report(d, c)
        print("ok:   committed run reports (both examples): 9 rows of Table 8.5.2 (1a / 1b), "
              "statuses, "
              "measured grade / delta / kernel time / axioms / G = certificate.json")

        # XOR predicate: certified since Stage 9a (Lemma 6.3.2 for XOR, `lemma_6_3_2_xor`)
        out = os.path.join(tmp, "xor")
        rc, so, se = certify(args.cqr, os.path.join("tests", "certify", "xor_pred.cqr"), out,
                             "--solutions", "4")
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 0 and last == "certified (conditional on: solution_count = 4)", (rc, so, se)
        xc, xtext = check_dir(out, validator)
        assert xc["status"] == "certified" and xc["obligations"] == []
        assert xc["axioms"] == STANDARD, xc["axioms"]
        assert "sorry" not in xtext and ".xor " in xtext
        print(f"ok:   XOR predicate xor_pred: `{last}` (exit 0; axioms exactly propext, "
              "Classical.choice, Quot.sound; no obligations)")

        # `if` predicate: the mux `b ⊕ (c ∧ (a ⊕ b))` of toNetwork (Stage 9a review)
        m = sum(1 for v in range(64)
                if ((v >> 1 & 1) if v & 1 else ((v >> 2 & 1) ^ (v >> 3 & 1))) and v >> 4 & 1
                and v >> 5 & 1)
        assert m == 8, m
        out = os.path.join(tmp, "if")
        rc, so, se = certify(args.cqr, os.path.join("tests", "certify", "if_pred.cqr"), out,
                             "--solutions", str(m))
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 0 and last == "certified (conditional on: solution_count = 8)", (rc, so, se)
        ic, itext = check_dir(out, validator)
        assert ic["status"] == "certified" and ic["obligations"] == []
        assert ic["axioms"] == STANDARD, ic["axioms"]
        assert ic["spec"]["delta"] == "7/128" and "r = 2." in itext, (ic["spec"], itext[:400])
        assert "sorry" not in itext and ".xor " in itext
        print(f"ok:   if predicate if_pred (M = 8 by brute force): `{last}` (exit 0; r = 2, "
              "delta 7/128; axioms exactly propext, Classical.choice, Quot.sound)")

        base = read(os.path.join(EXAMPLE, "Cert.lean"))

        # (a) a network that fails C.WF (input outside the register): the kernel check fails
        inp = "    .input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7,\n"
        assert base.count(inp) == 1
        d = os.path.join(tmp, "wf")
        os.makedirs(d, exist_ok=True)
        path = os.path.join(d, "Cert.lean")
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(base.replace(inp, inp.replace(".input 7", ".input 8")))
        rc, so, se = run(["lake", "env", "lean", "--run",
                          os.path.join("scripts", "CertifyTool.lean"), "audit", path, THEOREM])
        assert rc == 1 and "certified (" not in so and ": pass" not in so, (rc, so, se)
        print("ok:   (a) network failing C.WF (`.input 8` on 8 qubits): kernel check fails (exit 1)")

        # (b) injected sorry, (b') native_decide, in temp copies of the committed certificate
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
