"""Emulator runs on the fake backend's noise model — Stage 25b V1/V2 (PHASE2_SPEC §C.2 "The runs";
report §5.3, §3.3.3).

Untrusted Python tool, not a `cqr` subcommand (`cqr` stays free of the Python environment). An
**emulator run on the fake backend's noise model** of a committed physical artifact of Stage 25a:

  python -I hw/run.py --sim <artifact dir> --shots N --seed s [--json out] [--md out] [--cqr path]
  python -I hw/run.py --table <run json>… --out docs/hw_runs/RUNS.md [--comment file]

* **The circuit.** `physical.qasm` and `manifest.json` of the artifact are loaded; the circuit is
  reduced to its used qubits with the shared helper `transpile.compact_from_qiskit` (the mapping
  of Stage 25a's equivalence check); the readout of the n data qubits at
  `manifest.layout.data_physical` (and, for the wrapped gadget, of every logical qubit) is
  appended into a new classical register `r` — the IR has no final readout.
* **The noise model.** `NoiseModel.from_backend(<fake>)`, restricted to the used qubits and
  remapped to the compact indices (`compact_noise_model`); the mapping is checked error by error
  against the full model. Mid-circuit measurements get the fake's readout error: the labelled
  assumption of Stage 24c, stated in every report.
* **The success predicate.** Grover instances: P(x) on the data readout, with P's truth table from
  `cqr check <source> --truth-table` (bit k of x = data qubit k). The wrapped MBU gadget: the
  all-zero readout of its three qubits (the wrapper of hw/artifact.py prepares |++>, applies the
  gadget and undoes the ideal output's preparation).
* **The report** (`docs/hw_run.schema.json` 1.0.0): the manifest, target-snapshot and QASM hashes,
  the seed, the shots and the versions; the counts on `r` and p̂ = successes / shots; the two-sided
  95 % Clopper–Pearson interval and the one-sided 95 % lower bound; the ideal success frequency
  (Aer without noise on the same compact circuit, same shots and seed) and the reference (1 − δ,
  or 1 for the gadget); δ_hw from the manifest; the one-sided check
  p̂ ≥ 1 − δ_hw − √(ln(1/α) / (2·shots)) at α = 0.05: "passes", "fails" or "vacuous (δ_hw ≥ 1)".

Nothing here validates the certificate or the device: a simulator run is an emulation, and the
figures are reported, not certified. Never "verified on hardware".
"""

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import warnings
from fractions import Fraction

warnings.simplefilter("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

ALPHA = 0.05
WORDING = "emulator run on the fake backend's noise model; reported, not certified (Stage 27); not a device run"
MID_ASSUMPTION = ("mid-circuit measurements carry the fake backend's readout error in Aer's noise model "
                  "(the labelled assumption of Stage 24c: the snapshot gives no mid-circuit error)")


def sha3(data):
    return hashlib.sha3_256(data if isinstance(data, bytes) else data.encode("utf-8")).hexdigest()


def default_cqr():
    for c in ("cqr.exe", "cqr"):
        p = os.path.join(ROOT, ".lake", "build", "bin", c)
        if os.path.exists(p):
            return p
    return None


# --- Clopper–Pearson

def clopper_pearson(k, n, alpha=ALPHA):
    """The two-sided (1 − α) interval and the one-sided (1 − α) lower bound of a binomial proportion."""
    from scipy.stats import beta
    lo = 0.0 if k == 0 else float(beta.ppf(alpha / 2, k, n - k + 1))
    hi = 1.0 if k == n else float(beta.ppf(1 - alpha / 2, k + 1, n - k))
    lo1 = 0.0 if k == 0 else float(beta.ppf(alpha, k, n - k + 1))
    return lo, hi, lo1


def threshold(delta_hw, shots, alpha=ALPHA):
    return 1.0 - float(delta_hw) - math.sqrt(math.log(1.0 / alpha) / (2.0 * shots))


# --- the noise model on the compact circuit

def compact_noise_model(nm_full, used):
    """`nm_full` (NoiseModel.from_backend) restricted to `used` physical qubits and remapped to
    compact indices; returns (model, number of errors kept)."""
    from qiskit_aer.noise import NoiseModel
    comp = {p: i for i, p in enumerate(used)}
    d = nm_full.to_dict()
    kept = []
    for e in d["errors"]:
        gq = [list(q) for q in e["gate_qubits"] if all(x in comp for x in q)]
        if gq:
            e2 = dict(e)
            e2["gate_qubits"] = [[comp[x] for x in q] for q in gq]
            kept.append(e2)
    return NoiseModel.from_dict({"errors": kept}), len(kept)


def check_noise_mapping(nm_full, nm_compact, used):
    """Every error of the compact model is the full model's error on the corresponding physical
    qubits: quantum errors compared as channels (their SuperOp matrices, to 1e-10 — the dict round
    trip renames Pauli instructions to labelled unitaries but keeps the channel), readout errors by
    their exact probabilities. Returns the number of errors compared."""
    import numpy as np
    from qiskit_aer.noise import QuantumError
    comp = {p: i for i, p in enumerate(used)}
    full = {}
    for e in nm_full.to_dict()["errors"]:
        for q in e["gate_qubits"]:
            if all(x in comp for x in q):
                full[(e["type"], tuple(e["operations"]), tuple(comp[x] for x in q))] = e
    n = 0
    for e in nm_compact.to_dict()["errors"]:
        for q in e["gate_qubits"]:
            key = (e["type"], tuple(e["operations"]), tuple(q))
            if key not in full:
                raise ValueError(f"compact error {key} has no counterpart in the full model")
            f = full[key]
            if e["type"] == "roerror":
                if [[float(x) for x in row] for row in e["probabilities"]] != [[float(x) for x in row] for row in f["probabilities"]]:
                    raise ValueError(f"compact readout error {key} differs from the full model's")
            else:
                a = QuantumError.from_dict({**e, "gate_qubits": [list(q)]}).to_quantumchannel().data
                b = QuantumError.from_dict({**f, "gate_qubits": [list(q)]}).to_quantumchannel().data
                if a.shape != b.shape or not np.allclose(a, b, atol=1e-10):
                    raise ValueError(f"compact error {key} differs from the full model's as a channel")
            n += 1
    if n != sum(len(e["gate_qubits"]) for e in nm_compact.to_dict()["errors"]):
        raise ValueError("error count mismatch")
    return n


# --- the success predicate

def truth_table(cqr, source):
    p = subprocess.run([cqr, "check", os.path.join(ROOT, source), "--truth-table"], capture_output=True,
                       text=True, encoding="utf-8")
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if p.returncode != 0 or not lines:
        raise SystemExit(f"cqr check --truth-table {source} failed: {p.stderr.strip()[:200]}")
    r = json.loads(lines[-1])
    assert r["evaluator"] == r["network"], "evaluator and network truth tables differ"
    return r["evaluator"]


def predicate_of(manifest, cqr):
    """(kind, description, success(bits) -> bool, reference probability) where `bits` is the readout
    bitstring of register r with bit k = its k-th qubit."""
    if manifest["instance"] == "mbu_gadget_wrapped":
        return ("all_zero", "the all-zero readout of the two data qubits and the ancilla (the wrapper: |++>, the "
                "gadget, then H x1; CNOT x0->x1; H x0 undo the ideal output CZ|++>)", lambda bits: all(b == 0 for b in bits), Fraction(1))
    if manifest["source"] is None:
        raise SystemExit(f"{manifest['instance']}: no success predicate (use the wrapped gadget)")
    tt = truth_table(cqr, manifest["source"])
    n = manifest["grover"]["n"]
    assert len(tt) == 2 ** n

    def success(bits):
        x = sum(b << k for k, b in enumerate(bits[:n]))
        return tt[x] == "1"
    delta = Fraction(manifest["bound"]["delta"])
    return ("truth_table", f"P(x) on the data readout; truth table of {manifest['source']} (bit k of x = data qubit k)",
            success, 1 - delta), tt


def parse_counts(counts, n_r):
    """Aer's counts keyed 'r c' (space-separated registers, each big-endian) -> {tuple of r bits (bit k = qubit k): count}."""
    out = {}
    for key, c in counts.items():
        r = key.split(" ")[0]
        bits = tuple(int(r[len(r) - 1 - k]) for k in range(n_r))
        out[bits] = out.get(bits, 0) + c
    return out


# --- the run

def run_sim(art_dir, shots, seed, cqr):
    import qiskit
    import qiskit_aer
    from qiskit import ClassicalRegister, qasm3
    from qiskit_aer import AerSimulator
    from qiskit_aer.noise import NoiseModel
    import qiskit_ibm_runtime.fake_provider as fp
    from transpile import compact_from_qiskit

    manifest_bytes = open(os.path.join(art_dir, "manifest.json"), "rb").read()
    manifest = json.loads(manifest_bytes.decode("utf-8"))
    qasm = open(os.path.join(art_dir, "physical.qasm"), encoding="utf-8").read()
    assert sha3(qasm) == manifest["hashes"]["physical_qasm3"], "physical.qasm does not match its manifest hash"
    used = manifest["layout"]["used_qubits"]
    qc_full = qasm3.loads(qasm)
    qc, comp = compact_from_qiskit(qc_full, used)
    n_data = manifest["grover"]["n"] if manifest["grover"] else 2
    if manifest["instance"] == "mbu_gadget_wrapped":
        readout_phys = list(manifest["layout"]["final"])          # every logical qubit
    else:
        readout_phys = list(manifest["layout"]["data_physical"])
    rd = ClassicalRegister(len(readout_phys), "r")
    qc.add_register(rd)
    for k, p in enumerate(readout_phys):
        qc.measure(comp[p], rd[k])
    backend = getattr(fp, manifest["target_class"].rsplit(".", 1)[1])()
    nm_full = NoiseModel.from_backend(backend)
    nm, n_err = compact_noise_model(nm_full, used)
    n_checked = check_noise_mapping(nm_full, nm, used)
    pred = predicate_of(manifest, cqr)
    tt = None
    if isinstance(pred, tuple) and len(pred) == 2:
        pred, tt = pred
    kind, desc, success, reference = pred
    noisy = AerSimulator(noise_model=nm).run(qc, shots=shots, seed_simulator=seed).result().get_counts()
    ideal = AerSimulator().run(qc, shots=shots, seed_simulator=seed).result().get_counts()
    nc, ic = parse_counts(noisy, len(readout_phys)), parse_counts(ideal, len(readout_phys))
    k = sum(c for bits, c in nc.items() if success(bits))
    k_ideal = sum(c for bits, c in ic.items() if success(bits))
    p_hat, p_ideal = k / shots, k_ideal / shots
    lo, hi, lo1 = clopper_pearson(k, shots)
    delta_hw = Fraction(manifest["bound"]["bound"])
    thr = threshold(delta_hw, shots)
    if delta_hw >= 1:
        result = "vacuous (delta_hw >= 1)"
    else:
        result = "passes" if p_hat >= thr else "fails"
    rep = {
        "schema_version": "1.0.0",
        "kind": WORDING,
        "instance": manifest["instance"],
        "target": manifest["target"],
        "target_class": manifest["target_class"],
        "artifact_dir": os.path.relpath(art_dir, ROOT).replace("\\", "/"),
        "hashes": {"manifest": sha3(manifest_bytes), "target_snapshot": manifest["hashes"]["target_snapshot"],
                   "physical_qasm3": manifest["hashes"]["physical_qasm3"], "logical_circuit": manifest["hashes"]["logical_circuit"]},
        "seed": seed,
        "shots": shots,
        "versions": {"qiskit": qiskit.__version__, "qiskit_aer": qiskit_aer.__version__,
                     "run_py": "hw/run.py (Stage 25b)"},
        "circuit": {"used_physical_qubits": used, "compact_qubits": len(used), "readout_physical_qubits": readout_phys,
                    "readout_register": "r", "instructions": len(qc.data)},
        "noise_model": {"source": f"NoiseModel.from_backend({manifest['target_class'].rsplit('.', 1)[1]}()) restricted to the used qubits",
                        "errors_kept": n_err, "errors_checked_against_full_model": n_checked, "mapping_checked": True,
                        "mid_circuit_assumption": MID_ASSUMPTION},
        "success_predicate": {"kind": kind, "description": desc, "truth_table": tt},
        "noisy": {"counts": {"".join(str(b) for b in bits): c for bits, c in sorted(nc.items())}, "successes": k, "p_hat": p_hat,
                  "clopper_pearson_95": [lo, hi], "one_sided_lower_95": lo1},
        "ideal": {"successes": k_ideal, "p_ideal": p_ideal, "note": "Aer without noise on the same compact circuit, same shots and seed"},
        "reference": str(reference), "reference_float": float(reference),
        "delta": manifest["bound"]["delta"], "delta_hw": manifest["bound"]["bound"], "delta_hw_float": float(delta_hw),
        "delta_hw_vacuous": bool(delta_hw >= 1),
        "check": {"alpha": ALPHA, "statement": "p_hat >= 1 - delta_hw - sqrt(ln(1/alpha) / (2 shots))", "threshold": thr,
                  "result": result},
    }
    return rep


def markdown(rep):
    lines = [f"# {rep['instance']} on {rep['target']} — {rep['kind']}", "",
             f"- artifact `{rep['artifact_dir']}`, manifest hash `{rep['hashes']['manifest'][:16]}…`, snapshot `{rep['hashes']['target_snapshot'][:16]}…`",
             f"- seed {rep['seed']}, shots {rep['shots']}, qiskit {rep['versions']['qiskit']}, qiskit-aer {rep['versions']['qiskit_aer']}",
             f"- noise model: {rep['noise_model']['source']} ({rep['noise_model']['errors_kept']} errors, mapping checked); {rep['noise_model']['mid_circuit_assumption']}",
             f"- success predicate: {rep['success_predicate']['description']}",
             f"- δ = {rep['delta']}, δ_hw = {rep['delta_hw']} ≈ {rep['delta_hw_float']:.4g}{' (vacuous)' if rep['delta_hw_vacuous'] else ''}",
             f"- ideal (noiseless, same shots) {rep['ideal']['p_ideal']:.4f}; reference {rep['reference_float']:.4f}",
             f"- noisy p̂ = {rep['noisy']['p_hat']:.4f} ({rep['noisy']['successes']} / {rep['shots']}); 95 % Clopper–Pearson "
             f"[{rep['noisy']['clopper_pearson_95'][0]:.4f}, {rep['noisy']['clopper_pearson_95'][1]:.4f}]; one-sided 95 % lower bound {rep['noisy']['one_sided_lower_95']:.4f}",
             f"- check {rep['check']['statement']} at α = {rep['check']['alpha']}: threshold {rep['check']['threshold']:.4f} → **{rep['check']['result']}**",
             ""]
    return "\n".join(lines)


def table(reports, comment=None):
    lines = ["# Emulator runs on the fake backends' noise models (Stage 25b; PHASE2_SPEC §C.2)", "",
             "Every row is an **emulator run on the fake backend's noise model** of a committed physical artifact of",
             "Stage 25a (`hw/artifacts/`), by `hw/run.py --sim` (`scripts/hw_runs.sh`): Aer's `NoiseModel.from_backend`",
             "restricted to the used qubits, the n data qubits read out at their final physical positions, the",
             "success predicate P(x) (the all-zero readout for the wrapped MBU gadget). δ_hw is the bound on the",
             "physical circuit from the artifact's manifest; the check is p̂ ≥ 1 − δ_hw − √(ln(1/α)/(2·shots)) at",
             "α = 0.05, \"vacuous\" when δ_hw ≥ 1. Mid-circuit measurements carry the readout error (the Stage 24c",
             "assumption). Nothing here is a device run or a validation of a certificate; the figures are reported,",
             "not certified (Stage 27).", "",
             "| instance | target | seed | shots | δ | δ_hw | ideal | p̂ | 95 % CP interval | check |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for r in reports:
        lines.append(f"| {r['instance']} | {r['target']} | {r['seed']} | {r['shots']} | {r['delta']} | "
                     f"{r['delta_hw_float']:.4g}{' (vac.)' if r['delta_hw_vacuous'] else ''} | {r['ideal']['p_ideal']:.4f} | "
                     f"{r['noisy']['p_hat']:.4f} | [{r['noisy']['clopper_pearson_95'][0]:.4f}, {r['noisy']['clopper_pearson_95'][1]:.4f}] | "
                     f"{r['check']['result']} |")
    lines.append("")
    if comment:
        lines += ["## Comment", "", comment.strip(), ""]
    lines += ["Per-run reports: the JSON files next to this table (`docs/hw_run.schema.json`).", ""]
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--sim", metavar="ARTIFACT_DIR")
    ap.add_argument("--shots", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=25)
    ap.add_argument("--json")
    ap.add_argument("--md")
    ap.add_argument("--cqr", default=default_cqr())
    ap.add_argument("--table", nargs="*", metavar="RUN_JSON")
    ap.add_argument("--out")
    ap.add_argument("--comment")
    a = ap.parse_args(argv)
    if a.table is not None:
        reps = [json.load(open(p, encoding="utf-8")) for p in a.table]
        reps.sort(key=lambda r: (r["instance"], r["target"]))
        comment = open(a.comment, encoding="utf-8").read() if a.comment else None
        text = table(reps, comment)
        if a.out:
            with open(a.out, "w", encoding="utf-8", newline="\n") as f:
                f.write(text)
        else:
            sys.stdout.write(text)
        return 0
    if not a.sim:
        ap.error("--sim <artifact dir> or --table")
    rep = run_sim(a.sim, a.shots, a.seed, a.cqr)
    if a.json:
        with open(a.json, "w", encoding="utf-8", newline="\n") as f:
            f.write(json.dumps(rep, indent=1, sort_keys=True) + "\n")
    if a.md:
        with open(a.md, "w", encoding="utf-8", newline="\n") as f:
            f.write(markdown(rep))
    print(f"{rep['instance']} on {rep['target']}: p_hat {rep['noisy']['p_hat']:.4f} "
          f"[{rep['noisy']['clopper_pearson_95'][0]:.4f}, {rep['noisy']['clopper_pearson_95'][1]:.4f}], ideal {rep['ideal']['p_ideal']:.4f}, "
          f"reference {rep['reference_float']:.4f}, delta_hw {rep['delta_hw_float']:.4g}, check {rep['check']['result']} "
          f"({rep['kind']})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
