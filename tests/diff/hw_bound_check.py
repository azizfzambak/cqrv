"""Hardware bound check (Stage 24c; PHASE2_SPEC §C.1 "Per-operation rates"; report §3.1.3, §3.3.3).
Run with the .venv-hw Python (the transpiled counts need Qiskit).

An independent recomputation, from the circuit JSON (`cqr synthesize --grover --json`) and the
target JSON, of everything `cqr hw bound --json` prints: the counts under the decomposition table
(cz basis: h ↦ rz sx rz, x ↦ x, s sdg t tdg z p ↦ rz, cnot ↦ h cz h, cz ↦ cz; cx basis: cnot ↦
cx, cz ↦ h cx h; cp by its five-gate decomposition; a conditioned gate counts; a measure is
mid-circuit when an operation follows it), the worst and median rates (exact fractions over the
snapshot's decimal strings), each term, the sums, δ (the Grover success probability after r
iterations by an exact rational recurrence), both bound figures and the vacuity flag. Every
figure must agree exactly (fractions); only the median float line is compared with a tolerance.

Configurations: grover_pred_037 (tree mbu, tree coherent, few:log mbu) and simple_alu_x0_1 with
--solutions 30 (tree mbu, tree coherent, few:log mbu), against fake_torino (all) and
fake_washington (coherent only; mbu is refused with exit 2).

For information only (not compared): Qiskit's seeded transpile (optimization level 0) of the
lowered circuit against the fake backend, with its op counts next to the table's — how far the
table is from the transpiler before Stage 25 (routing SWAPs). Factors above 3 are flagged.

Usage: python -I tests/diff/hw_bound_check.py --cqr <path to cqr> [--targets hw/targets]
"""

import argparse
import json
import os
import subprocess
import sys
import warnings
from fractions import Fraction

warnings.simplefilter("ignore")
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))

fails = 0
rows = []


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


# --- the table

def add(a, b):
    return {k: a.get(k, 0) + b.get(k, 0) for k in set(a) | set(b)}


H = {"rz": 2, "sx": 1}


def cnot_counts(basis):
    return {"two": 1} if basis == "cx" else add(add(H, {"two": 1}), H)


def cz_counts(basis):
    return {"two": 1} if basis == "cz" else add(add(H, {"two": 1}), H)


def gate_counts(basis, g):
    op = g["op"]
    if op == "h":
        return dict(H)
    if op == "x":
        return {"x": 1}
    if op in ("s", "sdg", "t", "tdg", "z", "p"):
        return {"rz": 1}
    if op == "cnot":
        return cnot_counts(basis)
    if op == "cz":
        return cz_counts(basis)
    if op == "cp":
        c = cnot_counts(basis)
        return add({"rz": 3}, {k: 2 * v for k, v in c.items()})
    if op in ("measure", "alloc", "free"):
        return {}
    raise ValueError(op)


def basis_counts(basis, circ):
    gates = circ["gates"]
    tot = {"rz": 0, "sx": 0, "x": 0, "two": 0, "mid": 0, "final": 0}
    for i, g in enumerate(gates):
        if g["op"] == "measure":
            follows = any(h["op"] not in ("alloc", "free") for h in gates[i + 1:])
            tot["mid" if follows else "final"] += 1
        else:
            tot = add(tot, gate_counts(basis, g))   # `if` gates count as executed
    return tot


# --- rates

def frac_values(obj):
    return [Fraction(v) for v in obj.values()]


def worst(vals):
    return max(vals)


def median(vals):
    s = sorted(vals)
    n = len(s)
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2


def rates_of(target, basis):
    cal = target["calibration"]
    out = {}
    for g in ("rz", "sx", "x"):
        v = frac_values(cal["one_qubit_gate_error"][g])
        out[g] = (worst(v), median(v), len(v))
    v = frac_values(cal["two_qubit_gate_error"][basis])
    out["two"] = (worst(v), median(v), len(v))
    v = frac_values(cal["readout_error"])
    out["readout"] = (worst(v), median(v), len(v))
    return out


# --- δ: 1 − sin²((2r+1)θ) with sin²θ = M/N, by an exact rational recurrence on
#        p = a², c = sin(2θ)·a·b for the rotation (a, b) ↦ (cos2θ a + sin2θ b, −sin2θ a + cos2θ b)

def grover_delta(r, n, M):
    N = Fraction(2 ** n)
    x = Fraction(M) / N
    C = 1 - 2 * x                 # cos 2θ
    S2 = 4 * x * (1 - x)          # sin² 2θ
    p, c = x, 2 * Fraction(M) * (N - M) / N ** 2   # a₀² = M/N, sin2θ·a₀b₀ = 2M(N−M)/N²
    for _ in range(r):
        p, c = C * C * p + 2 * C * c + S2 * (1 - p), -S2 * C * p + (C * C - S2) * c + S2 * C * (1 - p)
    return 1 - p


def F(s):
    return Fraction(s)


def run(cqr, *args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True, encoding="utf-8")
    return p.returncode, p.stdout.replace("\r", ""), p.stderr.replace("\r", "")


def circuit_of(cqr, src, flags):
    rc, out, err = run(cqr, "synthesize", src, "--grover", *flags, "--json")
    lines = [l for l in out.splitlines() if l.startswith("{")]
    assert rc == 0 and lines, (rc, err[:200])
    return json.loads(lines[-1])["circuit"]


def transpiled_counts(circ, backend_class):
    import lower
    from qiskit import transpile
    import qiskit_ibm_runtime.fake_provider as fp
    qc = lower.lower(circ)
    tq = transpile(qc, backend=getattr(fp, backend_class)(), optimization_level=0, seed_transpiler=24)
    return {k: int(v) for k, v in tq.count_ops().items()}


def check_config(cqr, src, name, flags, target_path, target):
    basis = "cz" if "cz" in target["basis_gates"] else "cx"
    mode = "coherent" if "coherent" in flags else "mbu"
    label = f"{name} on {target['name']}"
    rc, out, err = run(cqr, "hw", "bound", src, "--target", target_path, *flags, "--json")
    if mode == "mbu" and not target["capabilities"]["feed_forward"]["value"]:
        check(rc == 2 and "mbu needs feed-forward" in err, f"{label}: mbu refused, exit {rc}")
        return
    check(rc == 0, f"{label}: cqr hw bound --json exit {rc} {err[:120]}")
    if rc != 0:
        return
    J = json.loads(out.strip().splitlines()[-1])
    circ = circuit_of(cqr, src, flags)
    n, r, M = circ["n_data"], J["r"], J["M"]
    cnt = basis_counts(basis, circ)
    rates = rates_of(target, basis)
    meas = cnt["mid"] + cnt["final"] + n
    ok = True
    # counts
    want = {"rz": cnt["rz"], "sx": cnt["sx"], "x": cnt["x"], basis: cnt["two"],
            "mid_circuit_measurements": cnt["mid"], "final_measurements": cnt["final"],
            "data_readout": n, "measurements_total": meas,
            "total": cnt["rz"] + cnt["sx"] + cnt["x"] + cnt["two"] + cnt["mid"] + cnt["final"] + n}
    for k, v in want.items():
        if J["counts"].get(k) != v:
            ok = False
            print(f"      counts.{k}: cqr {J['counts'].get(k)} vs recomputed {v}")
    # rates
    for k, (w, m, e) in rates.items():
        jk = basis if k == "two" else k
        jr = J["rates"][jk]
        if (F(jr["worst"]), F(jr["median"]), jr["entries"]) != (w, m, e):
            ok = False
            print(f"      rates.{jk}: cqr {jr} vs recomputed ({w}, {m}, {e})")
    # terms and sums
    terms_w = {"rz": cnt["rz"] * rates["rz"][0], "sx": cnt["sx"] * rates["sx"][0], "x": cnt["x"] * rates["x"][0],
               basis: cnt["two"] * rates["two"][0], "measurements": meas * rates["readout"][0]}
    terms_m = {"rz": cnt["rz"] * rates["rz"][1], "sx": cnt["sx"] * rates["sx"][1], "x": cnt["x"] * rates["x"][1],
               basis: cnt["two"] * rates["two"][1], "measurements": meas * rates["readout"][1]}
    sum_w, sum_m = sum(terms_w.values()), sum(terms_m.values())
    for k, v in terms_w.items():
        if F(J["terms_worst"][k]) != v:
            ok = False
            print(f"      terms_worst.{k}: cqr {J['terms_worst'][k]} vs {v}")
    for k, v in terms_m.items():
        if F(J["terms_median"][k]) != v:
            ok = False
            print(f"      terms_median.{k}: cqr {J['terms_median'][k]} vs {v}")
    if F(J["terms_worst"]["sum"]) != sum_w or F(J["terms_median"]["sum"]) != sum_m:
        ok = False
        print("      sums differ")
    # δ and the bounds
    delta = grover_delta(r, n, M)
    if F(J["delta"]) != delta:
        ok = False
        print(f"      delta: cqr {J['delta']} vs recurrence {delta}")
    bw, bm = delta + sum_w, delta + sum_m
    if F(J["bound"]["worst"]) != bw or F(J["bound"]["median"]) != bm or J["bound"]["worst_vacuous"] != (bw >= 1):
        ok = False
        print(f"      bound: cqr {J['bound']} vs worst {bw} median {bm} vacuous {bw >= 1}")
    if abs(float(J["bound"]["median_float"]) - float(bm)) > 1e-6 * max(1.0, float(bm)):
        ok = False
        print(f"      median_float: cqr {J['bound']['median_float']} vs {float(bm)}")
    if J["eta_mid_coefficient"] != cnt["mid"] or "not certified" not in J["status"]:
        ok = False
        print("      eta_mid / status differ")
    check(ok, f"{label}: counts, rates, terms, δ = {delta}, worst {float(bw):.4g}"
              f"{' (vacuous)' if bw >= 1 else ''}, median {float(bm):.4g} — all equal to cqr hw bound")
    # the text form
    rc2, out2, _ = run(cqr, "hw", "bound", src, "--target", target_path, *flags)
    check(rc2 == 0 and "reported, not certified (Stage 27)" in out2
          and (("VACUOUS" in out2) == (bw >= 1)) and "typical, not a bound" in out2,
          f"{label}: text form says reported-not-certified, vacuity marked = {bw >= 1}")
    # transpiled counts, for information
    cls = target["source"]["class"].rsplit(".", 1)[1]
    try:
        tc = transpiled_counts(circ, cls)
        t1 = sum(v for k, v in tc.items() if k in ("rz", "sx", "x", "id"))
        t2 = tc.get(basis, 0)
        c1 = cnt["rz"] + cnt["sx"] + cnt["x"]
        f1 = t1 / c1 if c1 else float("inf")
        f2 = t2 / cnt["two"] if cnt["two"] else float("inf")
        flag = " <-- factor > 3" if max(f1, f2) > 3 else ""
        print(f"info  {label}: table 1q {c1}, 2q {cnt['two']}, meas {cnt['mid'] + cnt['final']}; transpiled (level 0, seed 24) "
              f"1q {t1}, {basis} {t2}, measure {tc.get('measure', 0)}, if_else {tc.get('if_else', 0)}; "
              f"factors 1q {f1:.2f}, 2q {f2:.2f}{flag}")
        rows.append((label, c1, cnt["two"], t1, t2, f1, f2))
    except Exception as e:  # noqa: BLE001 — information only
        print(f"info  {label}: transpile failed: {type(e).__name__}: {str(e)[:120]}")
    rows.append(("bound " + label, cnt, {k: (str(v[0]), float(v[1])) for k, v in rates.items()}, str(delta), str(bw), bw >= 1, float(bm)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--targets", default=os.path.join(ROOT, "hw", "targets"))
    a = ap.parse_args()
    targets = []
    for f in sorted(os.listdir(a.targets)):
        if f.endswith(".json"):
            p = os.path.join(a.targets, f)
            targets.append((p, json.load(open(p, encoding="utf-8"))))
    check(len(targets) >= 2, f"{len(targets)} targets")
    configs = [
        ("grover_pred_037", "tree mbu", []),
        ("grover_pred_037", "tree coherent", ["--uncompute", "coherent"]),
        ("grover_pred_037", "few:log mbu", ["--shape", "few:log"]),
        ("simple_alu_x0_1", "tree mbu M=30", ["--solutions", "30"]),
        ("simple_alu_x0_1", "tree coherent M=30", ["--solutions", "30", "--uncompute", "coherent"]),
        ("simple_alu_x0_1", "few:log mbu M=30", ["--solutions", "30", "--shape", "few:log"]),
    ]
    for ex, name, flags in configs:
        src = os.path.join(ROOT, "examples", f"{ex}.cqr")
        for tp, t in targets:
            check_config(a.cqr, src, f"{ex} {name}", flags, tp, t)
    # usage errors
    rc, _, err = run(a.cqr, "hw", "bound", os.path.join(ROOT, "examples", "grover_pred_037.cqr"))
    check(rc == 2 and "hw bound" in err, f"hw bound without --target: exit {rc}, usage")
    rc, _, err = run(a.cqr, "hw", "bound", os.path.join(ROOT, "examples", "grover_pred_037.cqr"),
                     "--target", os.path.join(a.targets, "no_such.json"))
    check(rc == 2 and "cqr hw bound:" in err, f"hw bound with a missing target: exit {rc}")
    print(f"hw_bound_check: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
