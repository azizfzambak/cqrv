"""`cqr certify` checks (report §5.1.3, §8.4.1, §8.4.4, §9.5.1, §9.5.3; Stage 8b acceptance).

Runs the built `cqr` from the project root and checks

  * grover_pred_037: exit 0, status line `certified` (Stage 14a: n = 8 ≤ --count-limit 10, the
    default since Stage 14c (12 in 14a–14b), so
    Cert.lean proves hM_count and `cert` has no hypothesis; solution_count.status kernel_decided),
    certificate.json valid against docs/certificate.schema.json (v1.8.0), grade (15, 134, 72, 7),
    delta "7/128", axioms exactly propext, Classical.choice, Quot.sound, no obligations,
    trust_boundary.front_end = the proved wording and uncompute "mbu" (Stage 16b);
  * the hash link, independently of the CLI: the `emitted` IR literal of Cert.lean (the circuit
    the kernel-checked theorem is about) is parsed here, its canonical JSON hashed with hashlib
    and compared with hashes.circuit; the .qasm / .qir files re-parse to exactly that literal;
    hashes.proof is recomputed from Cert.lean and the pinned configuration;
  * reproducibility: a second run gives byte-identical Cert.lean / .qir / .qasm and the same JSON
    except the machine fields of reference_configuration (MACHINE, Stage 13a′ review; every hash
    stays compared); the committed example
    examples/certs/grover_pred_037/ agrees with the run (JSON modulo the machine fields);
  * the second worked predicate examples/simple_alu_x0_1.cqr (RevLib Simple ALU, bit 1 of x0;
    Stage 9b): M = 30 recounted here from the SyReC semantics (benchmark_diff.reference),
    --solutions 30 → exit 0, `certified (conditional on: solution_count = 30)`, r = 1, delta
    833/2048, grade (16, 121, 60, 10), the proved front-end wording; the committed
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
  * --profile illustrative_sc (Stage 11b; profiles/illustrative_sc.json, report Table 3.5 / §3.3.3):
    grover_pred_037 → exit 0, the status line unchanged, then
    `hardware profile illustrative_sc: fits all budgets; δ_hw ≤ 7/128 + 390·1/100 = 2531/640
    (vacuous)` (since Stage 12a: tree diffusion, d = 134 ≤ 200; the chain's 230 exceeded it);
    simple_alu_x0_1 → fits all budgets, δ_hw vacuous as well (G·p̄ = 3.45).
    Every field of `hardware` is recomputed here (components against the profile file, G,
    δ_hw = δ + G·p̄ with fractions, vacuous, profile_hash = SHA3 of the file with LF); the rest of
    the certificate equals the run without --profile (except schema_version "1.4.0"); Cert.lean,
    .qir, .qasm are byte-identical to the committed ones; the run report has the extra row
    "Hardware profile" with status "checked against declared profile (not a proof about
    hardware)";
  * --shape few:log (Stage 12d; few-ancilla diffusion, candidate B): grover_pred_037 without and
    with --profile illustrative_sc → exit 0, `certified (conditional on: solution_count = 32)`, schema
    v1.5.0 with diffusion_shape "few:log" (hardware only with --profile), grade (10, 172, 96, 2),
    delta 7/128, axioms exactly the standard three; the profile: `hardware profile illustrative_sc: fits all
    budgets; δ_hw ≤ 7/128 + 380·1/100 = 2467/640 (vacuous)` (d = 172 <= 200), every field of
    `hardware` recomputed; Cert.lean applies `grover_certificate_few_all` (Stage 13a′: KG
    Theorem 5.1 for every n, no per-instance classical check: no `fewCheck`, `classical_step`,
    `mcz_WF`, `diff_WF`), no native_decide / sorry / treeNet; the committed
    examples/certs/grover_pred_037_few agrees (Cert.lean, .qir, .qasm bytes; certificate.json
    outside reference_configuration; run report); negative test (d): the committed few Cert.lean
    with `mcz_ok` stated for n = 7 → the kernel check fails;
  * the tree certificates are unchanged by Stage 12d: the byte-identity checks above.
  * Stage 14a: every certificate carries solution_count {value, status} (schema v1.6.0); value =
    instance.M; the status line is `certified` iff status is kernel_decided, and then Cert.lean
    has hM_count and no hM_card (every n ≤ 10 case below is unconditional); negative tests:
    (e) grover_pred_037 --solutions 31 (ℰ's count) and simple_alu_x0_1 --solutions 29
    (Network.countSat's count) → solution_count_mismatch, exit 1, nothing written; (f)
    --count-limit 4 and --count-limit 0 → the conditional form (`certified (conditional on:
    solution_count = 32)`, hM_card, status hypothesis); (g) --profile illustrative_sc (renamed to
    illustrative_sc, no alias) → exit 2, the unknown-profile diagnostic lists the available
    profiles.
  * Stage 15b: `--uncompute coherent` (PHASE2_SPEC.md §A.0.1) → `certified`, schema v1.7.0 with
    uncompute "coherent", grade (15, 200, 144, 7), no measurement / classical bit, Cert.lean with
    OracleCertCoh and grover_certificate_coherent; with --profile illustrative_sc the depth fits
    with equality (200 ≤ 200) and the run report shows the measured depth next to the budget; the
    committed examples/certs/grover_pred_037_coh agrees; `--uncompute mbu` is the Phase 1 output
    byte for byte; few:log + coherent → unsupported_combination; an unknown mode → usage.
  * Stage 14c (f′): the default --count-limit is 10 — an n = 11 predicate `x0 ∧ x10`, written by
    the test to a temporary file, certified without the flag → the conditional form (`certified
    (conditional on: solution_count = 512)`, hM_card, status hypothesis); the kernel-decided
    form at n = 11 is not run (its cost is what Stage 14b measured). Budget: under 60 s.
  * Stage 16b: every Cert.lean (all templates, every run below) carries, between `net` and
    `emitted`, `prog` (the typed-term literal), `prog_scoped`, `net_ok : toNetwork prog = .ok net`
    and `front_end : ∀ x : Fin n → Bool, DSL.evalProgram prog x = Network.pred net n x` with
    `#print axioms front_end`; the four committed Cert.lean files are byte-identical to the
    Stage 16a files (git 52ad73b) outside that block; certificate.json says schema_version
    "1.8.0" with uncompute "mbu" / "coherent" and the proved front_end wording; run report row 1b
    is kernel-checked and names net_ok / front_end, row 1a names the typed-term printer; `cqr
    certify` no longer runs the exhaustive validation (cqr check --truth-table keeps it).

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
import time
from fractions import Fraction

import jsonschema

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_tool import ROOT  # noqa: E402
import benchmark_diff  # noqa: E402
import reparse_qasm  # noqa: E402
import reparse_qir  # noqa: E402

SCHEMA = os.path.join(ROOT, "docs", "certificate.schema.json")
EXAMPLE = os.path.join(ROOT, "examples", "certs", "grover_pred_037")
EXAMPLE_FEW = os.path.join(ROOT, "examples", "certs", "grover_pred_037_few")
EXAMPLE_COH = os.path.join(ROOT, "examples", "certs", "grover_pred_037_coh")
NAME = "grover_pred_037"
THEOREM = "CQRV.Cert.grover_pred_037.cert"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
MACHINE = ("cpu", "logical_cpus", "clock", "lean_threads", "kernel_check")
STAGES = ["1a. DSL Input: parser, surface checker", "1b. DSL Input: typed AST → network",
          "2. Spec Extraction", "3. Pattern Matching", "4. QPLP Instant.",
          "5. Oracle Synthesis", "6. Ancilla Restore", "7. Certificate Gen", "8. QIR Export"]
VERIFICATION = {"kernel-checked", "exhaustively validated", "declared trust boundary",
                "unverified"}


PROVED = ("DSL typed term → network: proved (toNetwork_pred; kernel-checked net_ok and front_end in "
          "Cert.lean); parser, surface checker and the typed-term printer unverified; "
          "predicate_hash binds the source")
STAGE16A = "52ad73b"  # the Stage 16a commit: its Cert.lean files have no front-end block
RE_FRONT_END = re.compile(r"/-- The typed term of the request.*?#print axioms front_end\n\n", re.S)


def check_front_end(text, n, name):
    """Cert.lean states the front end at its instance (Stage 16b): the four declarations between
    `net` and `emitted`, the theorem at the arity n of the request."""
    frags = (f"def prog : DSL.TypedProgram :=\n  {{ name := \"{name}\", params := [",
             "theorem prog_scoped : prog.scoped = true := by decide\n",
             "theorem net_ok : toNetwork prog = .ok net := except_ok_of_check _ _ (by decide +kernel)\n",
             f"theorem front_end : ∀ x : Fin {n} → Bool, DSL.evalProgram prog x = "
             f"Network.pred net {n} x :=\n  fun x => (toNetwork_pred prog net net_ok prog_scoped x).symm\n",
             "#print axioms front_end\n\n/-- The emitted circuit")
    for f in frags:
        assert text.count(f) == 1, f
    assert text.index("def net : Network") < text.index("def prog :") < text.index("def emitted :")
    assert len(RE_FRONT_END.findall(text)) == 1, "front-end block"


def stage16a_text(rel):
    """The committed Cert.lean of the Stage 16a commit (before the front-end block)."""
    p = subprocess.run(["git", "show", f"{STAGE16A}:{rel}"], cwd=ROOT, capture_output=True)
    assert p.returncode == 0, p.stderr.decode("utf-8", "replace")
    return p.stdout.decode("utf-8")  # the blob's bytes, no line-ending translation


def secs(ms):
    c = (ms + 5) // 10
    return f"{c // 100}.{c % 100:02d} s"


def status_line(cert):
    """The status line of a certificate (Stage 14a): unconditional iff M is kernel-decided;
    solution_count.value = instance.M; the hypothesis list names M iff it is a hypothesis."""
    sc = cert["solution_count"]
    assert sc["value"] == cert["instance"]["M"], sc
    named = [h for h in cert["hypotheses"] if h.startswith("solution_count")]
    if sc["status"] == "kernel_decided":
        assert named == [], cert["hypotheses"]
        return "certified"
    assert sc["status"] == "hypothesis", sc
    assert named == [f"solution_count = {sc['value']} (hM_card, supplied, not decided)"], named
    return "certified (conditional on: solution_count = {})".format(sc["value"])


def check_report(d, cert):
    """The committed run report of a certificate directory agrees with its certificate.json."""
    rep = json.loads(read(os.path.join(d, "run_report.json")))
    md = read(os.path.join(d, "run_report.md"))
    hw_rows = ["Hardware profile"] if "hardware" in cert else []
    assert [r["stage"] for r in rep["rows"]] == STAGES + hw_rows, [r["stage"] for r in rep["rows"]]
    assert all(r["verification"] in VERIFICATION for r in rep["rows"][:len(STAGES)]), rep["rows"]
    assert all(r["verification"] == HW_STATUS for r in rep["rows"][len(STAGES):]), rep["rows"]
    status = status_line(cert)
    assert rep["status"] == status and rep["certified"] is True, rep["status"]
    rows = {r["stage"]: r for r in rep["rows"]}
    # Stage 14a: the trust-boundary note for M follows the two cases
    decided = cert["solution_count"]["status"] == "kernel_decided"
    note2 = rows["2. Spec Extraction"]["note"]
    assert ("M is decided by the kernel (hM_count" in note2) == decided, note2
    assert ("M is the hypothesis hM_card, never decided" in note2) == (not decided), note2
    assert (f"M = {cert['instance']['M']} (kernel-decided)" in md) == decided, md[:400]
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
    assert "typed-term printer" in rows[STAGES[0]]["note"]
    # Stage 16b: row 1b is the theorem `front_end` of Cert.lean, kernel-checked
    assert rows[STAGES[1]]["verification"] == "kernel-checked"
    assert cert["trust_boundary"]["front_end"] == PROVED
    assert cert["trust_boundary"]["front_end"] in rows[STAGES[1]]["note"]
    assert "net_ok : toNetwork prog = .ok net" in rows[STAGES[1]]["note"], rows[STAGES[1]]
    assert "front_end" in rows[STAGES[1]]["note"] and "toNetwork_pred" in rows[STAGES[1]]["note"]
    assert f"2^{cert['instance']['n']} = {2 ** cert['instance']['n']} inputs" in rows[STAGES[1]]["resources"]
    assert [r["verification"] for r in rep["rows"][4:8]] == ["kernel-checked"] * 4
    assert rows["8. QIR Export"]["verification"] == "declared trust boundary"
    assert md.count("\n| ") == 10 + len(hw_rows) and all(st in md for st in STAGES), \
        "run_report.md table"
    return rep


def sha3(b):
    return hashlib.sha3_256(b).hexdigest()


PROFILE_NAME = "illustrative_sc"  # Stage 14a: renamed from ibm_kyiv (no alias)
PROFILE = os.path.join(ROOT, "profiles", f"{PROFILE_NAME}.json")
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


def check_hardware(d, cert, plain, last_two, fits, version="1.8.0"):
    """The `hardware` object of a --profile run, recomputed; the rest equals `plain`."""
    prof = json.loads(read(PROFILE))
    h = cert["hardware"]
    assert cert["schema_version"] == version, cert["schema_version"]
    assert h["profile"] == PROFILE_NAME and h["note"] == HW_NOTE, h
    assert h["profile_hash"] == sha3(read(PROFILE, "rb").replace(b"\r\n", b"\n")), "profile hash"
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
    line = (f"hardware profile {PROFILE_NAME}: {'exceeds ' + ', '.join(over) if over else 'fits all budgets'}; "
            f"δ_hw ≤ {rat(delta)} + {G}·{rat(pbar)} = {rat(dhw)}{' (vacuous)' if dhw >= 1 else ''}")
    status = status_line(cert)
    assert last_two == [status, line], (last_two, line)
    rest = {k: v for k, v in cert.items() if k not in ("hardware", "schema_version")}
    base = {k: v for k, v in plain.items() if k != "schema_version"}
    # Run vs run: every machine field differs between runs (Stage 13a′ review), hashes do not.
    assert without(rest, MACHINE) == without(base, MACHINE), "rest of the JSON"
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
            assert so.rstrip("\n").split("\n")[-1] == "certified", so
            runs.append(out)
        print("ok:   status line `certified` (exit 0; Stage 14a: M decided by the kernel)")
        cert, text = check_dir(runs[0], validator)
        assert cert["status"] == "certified" and cert["obligations"] == []
        assert cert["grade"] == {"w": 15, "d": 134, "t": 72, "a": 7}, cert["grade"]
        assert cert["spec"]["delta"] == "7/128", cert["spec"]
        assert cert["axioms"] == STANDARD, cert["axioms"]
        assert cert["theorem"] == THEOREM
        assert cert["trust_boundary"]["front_end"] == PROVED, cert["trust_boundary"]
        assert cert["uncompute"] == "mbu", cert.get("uncompute")
        check_front_end(text, 8, NAME)
        assert cert["solution_count"] == {"value": 32, "status": "kernel_decided"}, cert
        assert status_line(cert) == "certified"
        assert text.count("theorem hM_count : (Finset.univ.filter fun x => Network.pred net 8 x "
                          "= true).card = 32 := by\n  rw [← Network.countSat_eq_card]\n"
                          "  decide +kernel\n") == 1, "hM_count"
        assert "theorem cert :\n    RealizesExact" in text and "hM_card" not in text, "cert"
        assert text.count("nAnc_eq hM_count\n") == 1 and "native_decide" not in text
        print("ok:   Cert.lean: hM_count by Network.countSat_eq_card and decide +kernel; "
              "theorem cert without hypothesis; solution_count kernel_decided")
        print("ok:   JSON valid (schema v1.8.0, uncompute mbu); grade (15, 134, 72, 7), delta 7/128, "
              "axioms exactly propext, Classical.choice, Quot.sound; front end: the proved wording, "
              "Cert.lean states prog / prog_scoped / net_ok / front_end (Stage 16b)")
        print("ok:   circuit hash = SHA3 of the IR literal of Cert.lean (hashlib); "
              ".qasm / .qir re-parse to that literal; proof hash recomputed")
        cert2, _ = check_dir(runs[1], validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(runs[0], f), "rb") == read(os.path.join(runs[1], f), "rb"), f
        assert without(cert, MACHINE) == without(cert2, MACHINE)
        print("ok:   second run byte-identical (Cert.lean, .qir, .qasm; JSON except machine fields)")
        ex, _ = check_dir(EXAMPLE, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(runs[0], f), "rb") == read(os.path.join(EXAMPLE, f), "rb"), \
                f"committed example differs: {f}"
        assert without(cert, MACHINE) == without(ex, MACHINE), "committed certificate.json"
        assert ex["reference_configuration"]["kernel_check"]["runs"] == 5
        print("ok:   committed examples/certs/grover_pred_037 agrees (JSON modulo machine fields)")
        assert masked(read(os.path.join(runs[0], "certificate.json"))) == \
            masked(read(os.path.join(EXAMPLE, "certificate.json"))), "certificate.json bytes"
        assert cert["schema_version"] == "1.8.0" and "hardware" not in cert
        print("ok:   without --profile: certificate.json byte-identical to the committed one "
              "outside reference_configuration (schema_version 1.8.0, no hardware)")

        # --profile illustrative_sc (Stage 11b; renamed from ibm_kyiv in Stage 14a)
        out = os.path.join(tmp, "prof")
        rc, so, se = certify(args.cqr, src, out, "--profile", PROFILE_NAME, "--report")
        assert rc == 0, (rc, so, se)
        kc, _ = check_dir(out, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(out, f), "rb") == read(os.path.join(EXAMPLE, f), "rb"), f
        line = check_hardware(out, kc, cert, so.rstrip("\n").split("\n")[-2:], fits=True)
        assert line == ("hardware profile illustrative_sc: fits all budgets; "
                        "δ_hw ≤ 7/128 + 390·1/100 = 2531/640 (vacuous)"), line
        print("ok:   --profile illustrative_sc: status line unchanged (exit 0); fits all budgets "
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
        assert rc == 0 and last == "certified", (rc, so, se)
        ac, atext = check_dir(out, validator)
        assert ac["status"] == "certified" and ac["obligations"] == []
        assert ac["solution_count"] == {"value": 30, "status": "kernel_decided"}, ac
        assert "theorem hM_count" in atext and "hM_card" not in atext
        assert ac["axioms"] == STANDARD, ac["axioms"]
        assert ac["instance"] == {"n": 6, "M": 30, "r": 1}, ac["instance"]
        assert ac["spec"]["delta"] == "833/2048", ac["spec"]
        assert ac["grade"] == {"w": 16, "d": 121, "t": 60, "a": 10}, ac["grade"]
        assert ac["trust_boundary"]["front_end"] == PROVED and ac["uncompute"] == "mbu"
        check_front_end(atext, 6, alu)
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
                             "--solutions", str(m), "--profile", PROFILE_NAME, "--report")
        assert rc == 0, (rc, so, se)
        akc, _ = check_dir(out_k, validator)
        line = check_hardware(out_k, akc, ac, so.rstrip("\n").split("\n")[-2:], fits=True)
        assert line == ("hardware profile illustrative_sc: fits all budgets; "
                        "δ_hw ≤ 833/2048 + 345·1/100 = 39493/10240 (vacuous)"), line
        print("ok:   simple_alu_x0_1: certificate.json byte-identical to the committed one outside "
              "reference_configuration; --profile illustrative_sc: fits all budgets, delta_hw = "
              "833/2048 + 345*1/100 = 39493/10240 (vacuous: G*p_bar = 3.45 >= 1)")
        print(f"ok:   second predicate {alu} (M = 30 from the SyReC semantics, and decided by the "
              f"kernel): `{last}` (exit 0; "
              "r = 1, delta 833/2048, grade (16, 121, 60, 10), the proved front-end wording, "
              "front_end at n = 6); committed examples/certs/simple_alu_x0_1 agrees")
        for d, c in ((EXAMPLE, ex), (exa, ea)):
            check_report(d, c)
        print("ok:   committed run reports (both examples): 9 rows of Table 8.5.2 (1a / 1b), "
              "statuses, "
              "measured grade / delta / kernel time / axioms / G = certificate.json")

        # --shape few:log (Stage 12d): the few-ancilla diffusion, candidate B
        runs_few = {}
        for label, extra in (("plain", []), ("kyiv", ["--profile", PROFILE_NAME, "--report"])):
            out = os.path.join(tmp, "few_" + label)
            rc, so, se = certify(args.cqr, src, out, "--shape", "few:log", *extra)
            assert rc == 0, (rc, so, se)
            runs_few[label] = (out, so)
        out_p, so_p = runs_few["plain"]
        assert so_p.rstrip("\n").split("\n")[-1] == "certified", so_p
        fc, ftext = check_dir(out_p, validator)
        check_front_end(ftext, 8, NAME)
        assert fc["schema_version"] == "1.8.0" and fc["diffusion_shape"] == "few:log", fc
        assert fc["uncompute"] == "mbu" and fc["trust_boundary"]["front_end"] == PROVED, fc
        assert fc["solution_count"] == {"value": 32, "status": "kernel_decided"}, fc
        assert "hardware" not in fc
        assert fc["status"] == "certified" and fc["obligations"] == [] and fc["axioms"] == STANDARD
        assert fc["grade"] == {"w": 10, "d": 172, "t": 96, "a": 2}, fc["grade"]
        assert fc["spec"]["delta"] == "7/128" and fc["instance"] == {"n": 8, "M": 32, "r": 2}
        assert fc["theorem"] == THEOREM
        for frag in ("  grover_certificate_few_all oracle (by decide) diff_ok emitted_ok",
                     "theorem emitted_ok : groverCircuitFew net 8 2 .logDepth = .ok emitted",
                     "theorem mcz_ok : mczFew 8 .logDepth = .ok mczCircuit",
                     "theorem diff_ok : diffusionFew 8 .logDepth = .ok diffCircuit",
                     "no per-instance classical check", "theorem hM_count :",
                     "nAnc_eq\n    hM_count\n", "theorem cert :\n    RealizesExact"):
            assert ftext.count(frag) == 1, frag
        for bad_frag in ("native_decide", "sorry", "treeNet", "fewCheck", "classical_step",
                         "mcz_WF", "mcz_nBits", "mcz_nAnc", "diff_WF",
                         "grover_certificate_few oracle", "hM_card"):
            assert bad_frag not in ftext, bad_frag
        out_k, so_k = runs_few["kyiv"]
        fk, _ = check_dir(out_k, validator)
        line = check_hardware(out_k, fk, fc, so_k.rstrip("\n").split("\n")[-2:], fits=True)
        assert line == ("hardware profile illustrative_sc: fits all budgets; "
                        "δ_hw ≤ 7/128 + 380·1/100 = 2467/640 (vacuous)"), line
        assert fk["hardware"]["components"]["d"] == {"required": 172, "budget": 200, "fits": True}
        exf, _ = check_dir(EXAMPLE_FEW, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(out_k, f), "rb") == read(os.path.join(EXAMPLE_FEW, f), "rb"), \
                f"committed few example differs: {f}"
            assert read(os.path.join(out_p, f), "rb") == read(os.path.join(out_k, f), "rb"), f
        assert without(fk, MACHINE) == without(exf, MACHINE), "committed few certificate.json"
        assert masked(read(os.path.join(out_k, "certificate.json"))) == \
            masked(read(os.path.join(EXAMPLE_FEW, "certificate.json"))), "few certificate.json"
        assert exf["reference_configuration"]["kernel_check"]["runs"] == 5
        check_report(EXAMPLE_FEW, exf)
        print("ok:   --shape few:log: `certified` (exit 0); "
              "schema v1.8.0, diffusion_shape few:log, grade (10, 172, 96, 2), delta 7/128, "
              "axioms exactly the standard three; grover_certificate_few_all, no fewCheck")
        print("ok:   --shape few:log --profile illustrative_sc: fits all budgets (d = 172 <= 200), "
              "delta_hw = 7/128 + 380*1/100 = 2467/640 (vacuous); hardware recomputed; "
              "committed examples/certs/grover_pred_037_few agrees (bytes, JSON, run report)")

        # --uncompute coherent (Stage 15b, PHASE2_SPEC.md §A.0.1): the adjoint uncompute, no
        # measurement, no classical bit; schema v1.7.0 with `uncompute`; the fourth committed
        # example; the depth 200 equals the illustrative_sc budget (fits with equality)
        runs_coh = {}
        for label, extra in (("plain", []), ("prof", ["--profile", PROFILE_NAME, "--report"])):
            out = os.path.join(tmp, "coh_" + label)
            rc, so, se = certify(args.cqr, src, out, "--uncompute", "coherent", *extra)
            assert rc == 0, (rc, so, se)
            runs_coh[label] = (out, so)
        out_p, so_p = runs_coh["plain"]
        assert so_p.rstrip("\n").split("\n")[-1] == "certified", so_p
        cc, ctext = check_dir(out_p, validator)
        check_front_end(ctext, 8, NAME)
        assert cc["schema_version"] == "1.8.0" and cc["uncompute"] == "coherent", cc
        assert cc["trust_boundary"]["front_end"] == PROVED, cc
        assert "diffusion_shape" not in cc and "hardware" not in cc
        assert cc["solution_count"] == {"value": 32, "status": "kernel_decided"}, cc
        assert cc["status"] == "certified" and cc["obligations"] == [] and cc["axioms"] == STANDARD
        assert cc["grade"] == {"w": 15, "d": 200, "t": 144, "a": 7}, cc["grade"]
        assert cc["spec"]["delta"] == "7/128" and cc["instance"] == {"n": 8, "M": 32, "r": 2}
        assert cc["theorem"] == THEOREM
        counts_c = cc["hardware_perturbation"]["counts"]
        assert counts_c["mid_circuit_measurements"] == 0 and counts_c["classically_controlled"] == 0
        assert cc["hashes"]["circuit"] != cert["hashes"]["circuit"]
        for frag in ("theorem emitted_ok : groverCircuit net 8 2 none .tree .coherent = .ok emitted",
                     "def oracle : OracleCertCoh 8 where",
                     "def oracleCircuit : Circuit := okPayload (synthesizeOracle net .coherent)",
                     "  grover_certificate_coherent oracle (by decide) emitted_ok delta_eq grade_eq "
                     "nAnc_eq hM_count",
                     "theorem hM_count :", "theorem cert :\n    RealizesExact", "uncompute = coherent"):
            assert ctext.count(frag) == 1, frag
        for bad_frag in ("native_decide", "sorry", "DiffusionCert", "treeNet", ".measure ", ".ifBit ",
                         "hM_card", "grover_certificate oracle"):
            assert bad_frag not in ctext, bad_frag
        out_k, so_k = runs_coh["prof"]
        ck, _ = check_dir(out_k, validator)
        line = check_hardware(out_k, ck, cc, so_k.rstrip("\n").split("\n")[-2:], fits=True)
        g_coh = cc["hardware_perturbation"]["G"]
        dhw_coh = Fraction(7, 128) + Fraction(g_coh, 100)
        assert line == ("hardware profile illustrative_sc: fits all budgets; "
                        f"δ_hw ≤ 7/128 + {g_coh}·1/100 = {rat(dhw_coh)} (vacuous)"), line
        assert ck["hardware"]["components"]["d"] == {"required": 200, "budget": 200, "fits": True}
        md_k = read(os.path.join(out_k, "run_report.md"))
        assert "depth 200 / 200: fits" in md_k and "uncompute = coherent" in md_k, md_k[:600]
        exc, _ = check_dir(EXAMPLE_COH, validator)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(out_k, f), "rb") == read(os.path.join(EXAMPLE_COH, f), "rb"), \
                f"committed coherent example differs: {f}"
            assert read(os.path.join(out_p, f), "rb") == read(os.path.join(out_k, f), "rb"), f
        assert without(ck, MACHINE) == without(exc, MACHINE), "committed coherent certificate.json"
        assert masked(read(os.path.join(out_k, "certificate.json"))) == \
            masked(read(os.path.join(EXAMPLE_COH, "certificate.json"))), "coherent certificate.json"
        assert exc["reference_configuration"]["kernel_check"]["runs"] == 5
        check_report(EXAMPLE_COH, exc)
        # the MBU certificate is untouched by the mode: `--uncompute mbu` = no flag, byte for byte
        out_m = os.path.join(tmp, "mbu_explicit")
        rc, so, se = certify(args.cqr, src, out_m, "--uncompute", "mbu")
        assert rc == 0, (rc, so, se)
        for f in ("Cert.lean", f"{NAME}.qir", f"{NAME}.qasm"):
            assert read(os.path.join(out_m, f), "rb") == read(os.path.join(EXAMPLE, f), "rb"), f
        assert masked(read(os.path.join(out_m, "certificate.json"))) == \
            masked(read(os.path.join(EXAMPLE, "certificate.json"))), "mbu certificate.json"
        # rejections: few:log with coherent, an unknown mode
        out = os.path.join(tmp, "few_coh")
        rc, so, se = certify(args.cqr, src, out, "--uncompute", "coherent", "--shape", "few:log")
        dfc = json.loads(so.strip().split("\n")[-1])
        assert rc == 1 and dfc["code"] == "unsupported_combination", (rc, so, se)
        assert not os.path.exists(out), "a certificate was written for few:log + coherent"
        rc, so, se = certify(args.cqr, src, os.path.join(tmp, "bogus"), "--uncompute", "bogus")
        assert rc == 2 and not os.path.exists(os.path.join(tmp, "bogus")), (rc, so, se)
        print("ok:   --uncompute coherent: `certified` (exit 0); schema v1.8.0, uncompute coherent, "
              "grade (15, 200, 144, 7), 0 measurements, 0 classical bits, delta 7/128, axioms exactly "
              "the standard three; grover_certificate_coherent, OracleCertCoh, no DiffusionCert")
        print(f"ok:   --uncompute coherent --profile illustrative_sc: fits all budgets with d = 200 = "
              f"200 (equality), delta_hw = 7/128 + {g_coh}*1/100 = {rat(dhw_coh)} (vacuous); hardware "
              "recomputed; run report shows 'depth 200 / 200: fits'; committed "
              "examples/certs/grover_pred_037_coh agrees (bytes, JSON, run report)")
        print("ok:   --uncompute mbu = the Phase 1 certificate byte for byte; few:log + coherent -> "
              "unsupported_combination (exit 1, nothing written); --uncompute bogus -> usage (exit 2)")

        # Stage 16b: outside the front-end block, the four committed Cert.lean files are the
        # Stage 16a files byte for byte (cert, net, emitted and every other declaration unchanged)
        for dname in ("grover_pred_037", "simple_alu_x0_1", "grover_pred_037_few",
                      "grover_pred_037_coh"):
            new = read(os.path.join(ROOT, "examples", "certs", dname, "Cert.lean"))
            old = stage16a_text(f"examples/certs/{dname}/Cert.lean")
            assert RE_FRONT_END.sub("", new) == old, \
                f"{dname}: Cert.lean differs from the Stage 16a file outside the front-end block"
        print("ok:   the four committed Cert.lean files = the Stage 16a files (git 52ad73b) + the "
              "front-end block (prog, prog_scoped, net_ok, front_end); byte-identical elsewhere")

        # XOR predicate: certified since Stage 9a (Lemma 6.3.2 for XOR, `lemma_6_3_2_xor`)
        out = os.path.join(tmp, "xor")
        rc, so, se = certify(args.cqr, os.path.join("tests", "certify", "xor_pred.cqr"), out,
                             "--solutions", "4")
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 0 and last == "certified", (rc, so, se)
        xc, xtext = check_dir(out, validator)
        assert xc["solution_count"] == {"value": 4, "status": "kernel_decided"}, xc
        assert xc["status"] == "certified" and xc["obligations"] == []
        assert xc["axioms"] == STANDARD, xc["axioms"]
        check_front_end(xtext, xc["instance"]["n"], "xor_pred")
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
        assert rc == 0 and last == "certified", (rc, so, se)
        ic, itext = check_dir(out, validator)
        assert ic["solution_count"] == {"value": 8, "status": "kernel_decided"}, ic
        assert ic["status"] == "certified" and ic["obligations"] == []
        assert ic["axioms"] == STANDARD, ic["axioms"]
        assert ic["spec"]["delta"] == "7/128" and "r = 2." in itext, (ic["spec"], itext[:400])
        check_front_end(itext, ic["instance"]["n"], "if_pred")
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
                 "hM_count\n")
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

        # (d) few:log: `mcz_ok` stated for a wrong n → the kernel check fails (Stage 13a′; the
        # Stage 12d test mutated the classical step, which the certificate no longer has)
        fbase = read(os.path.join(EXAMPLE_FEW, "Cert.lean"))
        step = "theorem mcz_ok : mczFew 8 .logDepth = .ok mczCircuit"
        assert fbase.count(step) == 1
        d = os.path.join(tmp, "few_wrong_n")
        os.makedirs(d, exist_ok=True)
        path = os.path.join(d, "Cert.lean")
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(fbase.replace(step, step.replace("8", "7")))
        rc, so, se = run(["lake", "env", "lean", "--run",
                          os.path.join("scripts", "CertifyTool.lean"), "audit", path, THEOREM])
        assert rc == 1 and "certified (" not in so and ": pass" not in so, (rc, so, se)
        print("ok:   (d) few:log Cert.lean with mcz_ok stated for n = 7: kernel check fails "
              "(exit 1)")

        # (c) search_while: outside the fragment, the Stage 4 hint
        rc, so, se = certify(args.cqr, os.path.join("examples", "search_while.cqr"),
                             os.path.join(tmp, "sw"), "--solutions", "64")
        hint = json.loads(so.strip().split("\n")[-1])
        assert rc == 1 and hint["code"] == "no_matching_pattern" and "certified (" not in so, \
            (rc, so, se)
        assert not os.path.exists(os.path.join(tmp, "sw")), "no certificate for a non-match"
        print(f"ok:   (c) search_while: hint {hint['code']} at {hint['location']} (exit 1)")

        # Stage 14a: the solution count decided by the kernel — negative and conditional cases
        # (e) --solutions 31 contradicts ℰ's M = 32 (the Stage 3 diagnostic): nothing written
        out = os.path.join(tmp, "m31")
        rc, so, se = certify(args.cqr, src, out, "--solutions", "31")
        d31 = json.loads(so.strip().split("\n")[-1])
        assert rc == 1 and d31["code"] == "solution_count_mismatch" and \
            d31["stage"] == "hypothesis", (rc, so, se)
        assert not os.path.exists(out), "a certificate was written on a count mismatch"
        # (e') --solutions 29 for simple_alu_x0_1 (ℰ has no count): Network.countSat says 30
        out = os.path.join(tmp, "m29")
        rc, so, se = certify(args.cqr, os.path.join("examples", f"{alu}.cqr"), out,
                             "--solutions", "29")
        d29 = json.loads(so.strip().split("\n")[-1])
        assert rc == 1 and d29["code"] == "solution_count_mismatch" and \
            d29["stage"] == "hypothesis", (rc, so, se)
        assert "Network.countSat" in d29["message"] and "M = 29" in d29["message"] and \
            "count 30" in d29["message"], d29
        assert not os.path.exists(out), "a certificate was written on a count mismatch"
        print("ok:   (e) --solutions 31 (grover_pred_037, the extractor counts 32) and --solutions 29 "
              "(simple_alu_x0_1, Network.countSat counts 30): solution_count_mismatch, exit 1, "
              "nothing written")
        # (f) --count-limit 4 and --count-limit 0 (disabled): n = 8 → the conditional form
        for lim in ("4", "0"):
            out = os.path.join(tmp, "lim" + lim)
            rc, so, se = certify(args.cqr, src, out, "--count-limit", lim)
            last = so.rstrip("\n").split("\n")[-1]
            assert rc == 0 and last == "certified (conditional on: solution_count = 32)", \
                (rc, so, se)
            lc, ltext = check_dir(out, validator)
            assert lc["solution_count"] == {"value": 32, "status": "hypothesis"}, lc["solution_count"]
            assert lc["hypotheses"][0] == "solution_count = 32 (hM_card, supplied, not decided)"
            assert "(hM_card :" in ltext and "hM_count" not in ltext and "nAnc_eq hM_card\n" in ltext
            assert lc["status"] == "certified" and lc["axioms"] == STANDARD and lc["obligations"] == []
            assert lc["hashes"]["circuit"] == cert["hashes"]["circuit"] and lc["grade"] == cert["grade"]
            assert lc["hashes"]["proof"] != cert["hashes"]["proof"]
        print("ok:   (f) --count-limit 4 / 0: `certified (conditional on: solution_count = 32)`, "
              "Cert.lean with hM_card, solution_count.status hypothesis (exit 0)")
        # (f′) Stage 14c: the default --count-limit is 10 — n = 11 without the flag is the
        # conditional form (the kernel-decided form at n = 11 is not run: Stage 14b measured it)
        src11 = os.path.join(tmp, "tiny11.cqr")
        with open(src11, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("fn tiny11(x: Vec Bool 11) -> Bool {\n  idx(x, 0) and idx(x, 10)\n}\n")
        out = os.path.join(tmp, "tiny11")
        t0 = time.time()
        rc, so, se = certify(args.cqr, src11, out, "--solutions", "512")
        dt = time.time() - t0
        last = so.rstrip("\n").split("\n")[-1]
        assert rc == 0 and last == "certified (conditional on: solution_count = 512)", (rc, so, se)
        c11, t11 = check_dir(out, validator)
        assert c11["solution_count"] == {"value": 512, "status": "hypothesis"}, c11["solution_count"]
        assert c11["hypotheses"][0] == "solution_count = 512 (hM_card, supplied, not decided)"
        assert c11["status"] == "certified" and c11["axioms"] == STANDARD and c11["obligations"] == []
        assert "(hM_card :" in t11 and "hM_count" not in t11 and "Network.pred net 11 " in t11
        check_front_end(t11, 11, "tiny11")
        assert dt < 60, f"(f') took {dt:.0f} s (budget 60 s)"
        print(f"ok:   (f') n = 11 without --count-limit (default 10): `{last}`, Cert.lean with "
              f"hM_card, solution_count.status hypothesis (exit 0, {dt:.0f} s)")
        # (g) the renamed profile has no alias: --profile illustrative_sc is an unknown profile
        out = os.path.join(tmp, "kyiv_old")
        rc, so, se = certify(args.cqr, src, out, "--profile", "ibm_kyiv")
        assert rc == 2 and "profiles/ibm_kyiv.json not found" in se and \
            "available profiles: illustrative_sc" in se, (rc, so, se)
        assert not os.path.exists(out)
        print("ok:   (g) --profile ibm_kyiv: unknown profile (exit 2), the diagnostic lists "
              "illustrative_sc; nothing written")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("certify_check: all checks passed")


if __name__ == "__main__":
    main()
