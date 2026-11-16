"""Stage 27b2 — the committed conditional certificates are the artifacts', their bounds are the mirror's,
and the emulator comparison at δ' is recomputed (PHASE2_SPEC §C.4 (4); report §2.3.2, §6.6, §8.4).

  python -I tests/diff/hw_noisecert_check.py --cqr <cqr>   (.venv; no Qiskit)

For each of examples/certs/hw_n2_torino, hw_n3_torino (with a logical certificate) and
mbu_gadget_torino (the channel form):
  * `manifest.json`: the artifact hashes, the target snapshot and file hashes (and, with a logical
    certificate, `certificate.json`'s bytes); the status words contain `noise_conditional`; the four
    premises P-cal, P-stoch, P-ro, P-idle are present with the meaning sentence;
  * `noise.noise_bound`, `clamped`, `noise_vacuous` and `physical_bound_p_eq_r` equal `hw/noisebound.py`'s;
  * the emulator comparison: when a run report exists, `threshold_at_delta_prime` equals the recorded
    threshold + the recorded δ_hw − δ' (exactly, as Fractions of the printed decimals) and the result
    is `passes` iff p̂ ≥ that threshold; `emulator_validated` is present iff it passes; without a run
    report the manifest says "no run recorded for this artifact";
  * the three files are byte-identical to what `cqr hw noisecert` regenerates.
The kernel check of the Lean files (`lake env lean`) is the bash step's. Conditional on the premises;
nothing here is a fact about a device or "verified on hardware".
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import noisebound  # noqa: E402

TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}
CERTS = [("hw_n2_torino", "hw_n2", "PhysCert.lean"), ("hw_n3_torino", "hw_n3", "PhysCert.lean"),
         ("mbu_gadget_torino", None, "NoiseCert.lean")]
PREMISES = ["P-cal", "P-stoch", "P-ro", "P-idle"]


def sha3(data):
    return hashlib.sha3_256(data if isinstance(data, bytes) else data.encode("utf-8")).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def frac(s):
    return Fraction(str(s))


def check_cert(cqr, name, logical, lean_file, errors):
    cdir = os.path.join(ROOT, "examples", "certs", name)
    man = json.load(open(os.path.join(cdir, "manifest.json"), encoding="utf-8"))
    adir = os.path.join(ROOT, man["artifact"]["dir"])
    amanifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
    tpath = os.path.join(ROOT, TARGET_FILES[amanifest["target"]])
    want = {
        "logical_circuit": sha3(canonical(json.load(open(os.path.join(adir, "logical.json"), encoding="utf-8")))),
        "witness": sha3(canonical(json.load(open(os.path.join(adir, "witness.json"), encoding="utf-8")))),
        "physical_json": sha3(canonical(json.load(open(os.path.join(adir, "physical.json"), encoding="utf-8")))),
        "target_snapshot": json.load(open(tpath, encoding="utf-8"))["snapshot"]["hash"],
        "target_file_sha3": sha3(open(tpath, "rb").read()),
    }
    if logical:
        want["certificate_json"] = sha3(open(os.path.join(ROOT, "examples", "certs", logical, "certificate.json"), "rb").read())
    for k, v in want.items():
        if man["hashes"].get(k) != v:
            errors.append(f"{name}: manifest hash {k}: {man['hashes'].get(k)} differs from {v}")
    words = man["status"]
    if "noise_conditional" not in words or "physical_translation_validated" not in words:
        errors.append(f"{name}: status words {words} lack noise_conditional / physical_translation_validated")
    if ("logical_certified" in words) != bool(logical):
        errors.append(f"{name}: logical_certified present={('logical_certified' in words)} but logical certificate={logical}")
    noise = man["noise"]
    for p in PREMISES:
        if p not in noise.get("premises", {}):
            errors.append(f"{name}: premise {p} missing")
    if "not verified on hardware" not in noise.get("meaning", "") or "assumptions about the device" not in noise.get("meaning", ""):
        errors.append(f"{name}: the meaning sentence is not the conditional one")
    py = noisebound.noise_of_artifact(adir, tpath)
    for k in ("noise_bound", "clamped", "noise_vacuous", "physical_bound_p_eq_r"):
        if canonical(noise[k]) != canonical(py[k]):
            errors.append(f"{name}: noise.{k} {noise[k]} differs from Python {py[k]}")
    # the emulator comparison
    run_path = os.path.join(ROOT, "docs", "hw_runs", f"{amanifest['instance']}__{amanifest['target']}.json")
    emu = man["emulator_comparison"]
    if os.path.exists(run_path):
        r = json.load(open(run_path, encoding="utf-8"))
        thr = frac(r["check"]["threshold"]) + frac(r["delta_hw"]) - frac(noise["noise_bound"])
        passes = frac(r["noisy"]["p_hat"]) >= thr
        if not isinstance(emu, dict):
            errors.append(f"{name}: a run report exists but the manifest has no comparison: {emu}")
        else:
            if frac(emu["threshold_at_delta_prime"]) != thr:
                errors.append(f"{name}: threshold_at_delta_prime {emu['threshold_at_delta_prime']} differs from {thr}")
            if (emu["result"] == "passes") != passes:
                errors.append(f"{name}: emulator result {emu['result']} but recomputed passes={passes}")
        if ("emulator_validated" in words) != passes:
            errors.append(f"{name}: emulator_validated present={('emulator_validated' in words)} but passes={passes}")
    else:
        if emu != "no run recorded for this artifact" or "emulator_validated" in words:
            errors.append(f"{name}: no run report, but the manifest says {emu!r} / words {words}")
    # regeneration
    lat = [L for L in man.get("ff_latency_ns", ["0"]) if L != "0"]
    lat = lat[0] if lat else "1000"
    with tempfile.TemporaryDirectory() as tmp:
        cmd = [cqr, "hw", "noisecert", "--artifact", adir, "--target", tpath, "--ff-latency", lat, "--out", tmp]
        if logical:
            cmd += ["--cert", os.path.join(ROOT, "examples", "certs", logical)]
        p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
        if p.returncode != 0:
            errors.append(f"{name}: cqr hw noisecert failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
        else:
            for f in (lean_file, "physical.qasm", "manifest.json"):
                if open(os.path.join(tmp, f), "rb").read() != open(os.path.join(cdir, f), "rb").read():
                    errors.append(f"{name}: {f} differs from the regenerated file")
    return float(frac(noise["noise_bound"])), words, emu if isinstance(emu, str) else emu["result"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    a = ap.parse_args()
    errors = []
    for name, logical, lean_file in CERTS:
        nb, words, emu = check_cert(a.cqr, name, logical, lean_file, errors)
        print(f"hw_noisecert_check: {name}: delta' {nb:.4f}; status {', '.join(words)}; emulator {emu}")
    for e in errors:
        print("hw_noisecert_check: " + e)
    if errors:
        return 1
    print(f"hw_noisecert_check: {len(CERTS)} conditional certificates: hashes, premises, bounds, emulator comparison and regeneration ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
