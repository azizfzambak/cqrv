"""Stage 27c — the feasibility frontier (PHASE2_SPEC §C.4; STAGE27_TASK.md 27c; report §2.3.2, §6.6).

For each target, mode and routing, the frontier is the largest instance of the family
`examples/frontier/fr_n<k>.cqr` (Grover on x_0 ∧ … ∧ x_{n−1}, M = 1, n = 2…7) whose conditional
bound `noiseBound` (the Pauli reading, `cqr hw noise`) is below 1. A measured table, not a
certificate; certificates are made only at the frontier's largest instances (F3).

  python -I scripts/frontier.py --cqr <cqr> --series <target>:<mode>:<routing> [--seeds 0-19]
      runs one series (modes: tree_mbu, tree_coherent, fewlog_mbu; routings: a = the full coupling
      map, b = the edges of calibrated error >= 0.5 removed, largest connected component), with the
      early stop (two consecutive vacuous n skip the larger n); the artifacts go to .lake/frontier/
      (scratch, git-ignored) and the rows to docs/hw_frontier/frontier.json
  python -I scripts/frontier.py --cqr <cqr> --render
      writes docs/hw_frontier/FRONTIER.md from frontier.json (the full table, the frontier per
      (target, mode, routing), the idle-exposure diagnostic, the premises paragraph)
  python -I scripts/frontier.py --cqr <cqr> --promote <row name>
      copies a scratch artifact into hw/artifacts/ (with logical.json and physical.json) for a
      frontier certificate; the certificate commands are printed, not run

The idle-exposure diagnostic (F2, Python only): each used qubit's idle time under the ASAP schedule
of hw/physgrade.py divided by its T2 from the target file; the maximum and the sum over the used
qubits, at L = 0 and 1000 ns. Reported, not part of any bound: it shows how far (P-idle) is from a
device. Untrusted tool; nothing here is certified or "verified on hardware".
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "hw"))
sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
import physgrade  # noqa: E402

TARGET_FILES = {"fake_torino": "hw/targets/fake_torino.json", "fake_washington": "hw/targets/fake_washington.json"}

SCRATCH = os.path.join(ROOT, ".lake", "frontier")
ROWS = os.path.join(ROOT, "docs", "hw_frontier", "frontier.json")
TABLE = os.path.join(ROOT, "docs", "hw_frontier", "FRONTIER.md")
NS = list(range(2, 8))
MODES = {"tree_mbu": ([], "mbu"), "tree_coherent": (["--uncompute", "coherent"], "coherent"),
         "fewlog_mbu": (["--shape", "few:log"], "mbu")}
THRESHOLD = Fraction(1, 2)


def seeds_of(spec):
    a, b = spec.split("-")
    return list(range(int(a), int(b) + 1))


def restricted_coupling(target, basis):
    """Routing (b): the directed edges of calibrated error < 1/2, restricted to the largest connected
    component; returns (CouplingMap, info dict)."""
    from qiskit.transpiler import CouplingMap
    two = target["calibration"]["two_qubit_gate_error"][basis]
    edges = [(p, q) for p, q in target["coupling_map"] if Fraction(two.get(f"{p},{q}", two.get(f"{q},{p}", "1"))) < THRESHOLD]
    removed = len(target["coupling_map"]) - len(edges)
    adj = {}
    for p, q in edges:
        adj.setdefault(p, set()).add(q)
        adj.setdefault(q, set()).add(p)
    seen, best = set(), set()
    for start in adj:
        if start in seen:
            continue
        comp, stack = set(), [start]
        while stack:
            v = stack.pop()
            if v in comp:
                continue
            comp.add(v)
            stack.extend(adj[v] - comp)
        seen |= comp
        if len(comp) > len(best):
            best = comp
    kept = [(p, q) for p, q in edges if p in best]
    info = {"kind": "edges_below_threshold", "threshold": "1/2", "edges_removed": removed,
            "component_qubits": len(best), "edges_kept": len(kept)}
    return CouplingMap(couplinglist=kept), info


def idle_diagnostic(ops, target, used, L):
    """Each used qubit's idle time (depth − busy) under the ASAP schedule of hw/physgrade.py, over its
    T2 (seconds in the target file → ns); the maximum and the sum over the used qubits."""
    L = Fraction(L)
    dur, cal = target["durations"], target["calibration"]
    tq = {p: Fraction(0) for p in used}
    busy = {p: Fraction(0) for p in used}
    tb = {}
    for op, cond in physgrade.flat(ops):
        d = physgrade.duration(dur, None, op)
        start = max(tq[p] for p in op["q"])
        if cond is not None:
            start = max(start, tb.get(cond, Fraction(0)) + L)
        fin = start + d
        for p in op["q"]:
            tq[p] = fin
            busy[p] += d
        if op["op"] == "measure":
            tb[op["c"]] = fin
    depth = max(list(tq.values()) + list(tb.values()) + [Fraction(0)])
    ratios = {}
    for p in used:
        t2_ns = Fraction(cal["t2_s"][str(p)]) * 10**9
        ratios[p] = (depth - busy[p]) / t2_ns
    return {"depth_ns": physgrade.frac_str(depth), "max_idle_over_t2": float(max(ratios.values())),
            "sum_idle_over_t2": float(sum(ratios.values())),
            "worst_qubit": max(ratios, key=ratios.get)}


def cqr_json(cqr, args):
    p = subprocess.run([cqr, *args], capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit(f"cqr {' '.join(args)} failed ({p.returncode}): {(p.stdout + p.stderr).strip()[:300]}")
    return json.loads(p.stdout.strip().splitlines()[-1])


def load_rows():
    if os.path.exists(ROWS):
        return json.load(open(ROWS, encoding="utf-8"))
    return {"rows": [], "series": {}}


def save_rows(data):
    os.makedirs(os.path.dirname(ROWS), exist_ok=True)
    with open(ROWS, "w", encoding="utf-8", newline="\n") as f:
        f.write(json.dumps(data, indent=1, sort_keys=True) + "\n")


def run_series(cqr, target_name, mode, routing, seeds):
    import artifact as art  # Qiskit-side; imported here so that --render and the CI check need no Qiskit
    flags, uncompute = MODES[mode]
    target = art.load_target(target_name)
    basis = "cz" if "cz" in target["basis_gates"] else "cx"
    if uncompute == "mbu" and not target["capabilities"]["feed_forward"]["value"]:
        print(f"{target_name}:{mode}: mbu needs feed-forward — not run")
        return
    cm, rinfo = (None, {"kind": "full_coupling_map"}) if routing == "a" else restricted_coupling(target, basis)
    data = load_rows()
    key = f"{target_name}:{mode}:{routing}"
    data["rows"] = [r for r in data["rows"] if r["series"] != key]
    tpath = os.path.join(ROOT, TARGET_FILES[target_name])
    vac_streak = 0
    series = {"routing": rinfo, "seeds": seeds, "skipped": []}
    for n in NS:
        if vac_streak >= 2:
            series["skipped"].append({"n": n, "reason": f"skipped (vacuous at n={n-1}, n={n-2})"})
            continue
        name = f"fr_n{n}_{mode}" + ("" if routing == "a" else "_rb")
        inst = (name, f"examples/frontier/fr_n{n}.cqr", flags, uncompute, [target_name], None)
        t0 = time.time()
        try:
            manifest, w, qasm, best = art.build(cqr, inst, target_name, seeds=seeds, coupling_map=cm,
                                                 routing=None if routing == "a" else rinfo)
        except SystemExit as e:
            print(f"{key} n={n}: synthesis/routing not available: {e}")
            series["skipped"].append({"n": n, "reason": f"not run: {str(e)[:120]}"})
            continue
        d = os.path.join(SCRATCH, "artifacts", f"{name}__{target_name}")
        art.write_artifact(d, manifest, w, qasm)
        circ, _ = art.logical_circuit(cqr, inst)
        art.write_extra(d, circ, best["final_phys"])
        g0 = cqr_json(cqr, ["hw", "grade", "--artifact", d, "--target", tpath, "--ff-latency", "0", "--json"])
        g1 = cqr_json(cqr, ["hw", "grade", "--artifact", d, "--target", tpath, "--ff-latency", "1000", "--json"])
        nz = cqr_json(cqr, ["hw", "noise", "--artifact", d, "--target", tpath, "--json"])
        ops = json.load(open(os.path.join(d, "physical.json"), encoding="utf-8"))
        used = manifest["layout"]["used_qubits"]
        tgt = physgrade.load_target(tpath)
        row = {"series": key, "name": name, "target": target_name, "mode": mode, "routing": routing, "n": n,
               "r": manifest["grover"]["r"], "ands": n - 1, "seed": manifest["seed"],
               "used_qubits": len(used), "two_qubit": g0["two_qubit"], "mid_measurements": g0["mid_measurements"],
               "depth_ns_L0": g0["depth_ns"], "depth_ns_L1000": g1["depth_ns"],
               "noise_bound": nz["noise_bound"], "noise_bound_float": float(Fraction(nz["noise_bound"])),
               "p_eq_r": nz["physical_bound_p_eq_r"], "p_eq_r_float": float(Fraction(nz["physical_bound_p_eq_r"])),
               "clamped": nz["clamped"], "noise_vacuous": nz["noise_vacuous"],
               "idle_L0": idle_diagnostic(ops, tgt, used, 0), "idle_L1000": idle_diagnostic(ops, tgt, used, 1000),
               "seconds": round(time.time() - t0, 1), "scratch_dir": os.path.relpath(d, ROOT).replace("\\", "/")}
        data["rows"].append(row)
        vac_streak = vac_streak + 1 if row["noise_vacuous"] else 0
        print(f"{key} n={n} r={row['r']}: used {row['used_qubits']}, two-qubit {row['two_qubit']}, noiseBound "
              f"{row['noise_bound_float']:.4f}{' VACUOUS' if row['noise_vacuous'] else ''}{' clamped' if row['clamped'] else ''}, "
              f"p=r {row['p_eq_r_float']:.4f}, idle/T2 max {row['idle_L0']['max_idle_over_t2']:.3f} ({row['seconds']} s)")
        data["series"][key] = series
        save_rows(data)
    data["series"][key] = series
    save_rows(data)


def frontier_of(data):
    """Per series: the largest n with a non-vacuous noise bound (or None)."""
    out = {}
    for key in sorted(data["series"]):
        rows = [r for r in data["rows"] if r["series"] == key]
        ok = [r for r in rows if not r["noise_vacuous"]]
        out[key] = max(ok, key=lambda r: r["n"]) if ok else None
    return out


def render(data):
    fr = frontier_of(data)
    lines = ["# The feasibility frontier (Stage 27c; PHASE2_SPEC §C.4)", "",
             "Generated by `scripts/frontier.py` (do not edit). For each target, mode and routing, the **frontier** is the",
             "largest instance of the family `examples/frontier/fr_n<k>.cqr` — Grover on `x_0 ∧ … ∧ x_{n−1}`, M = 1,",
             "n = 2…7, r = r⋆ the iteration count `cqr` chooses — whose **conditional bound `noiseBound`** (the Pauli",
             "reading of Stage 27b, `cqr hw noise`) is below 1. A measured table, not a certificate: the bounds are",
             "conditional on the premises (P-cal), (P-stoch), (P-ro), (P-idle); the routing is Qiskit's (untrusted; the",
             "witness is checked); nothing here is \"verified on hardware\". Routing (a) is the full coupling map with the",
             "seed search 0..19 as in 25a; routing (b) removes the edges of calibrated error ≥ 1/2 and routes on the",
             "largest connected component. A series stops after two consecutive vacuous n.", "",
             "## The frontier per (target, mode, routing)", "",
             "| target | mode | routing | frontier n | r | noiseBound | 25a's p = r | two-qubit | used qubits | idle/T2 max (L=0) |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for key, r in fr.items():
        t, m, ro = key.split(":")
        if r is None:
            lines.append(f"| {t} | {m} | {ro} | none (vacuous from n = 2) | — | — | — | — | — | — |")
        else:
            lines.append(f"| {t} | {m} | {ro} | {r['n']} | {r['r']} | {r['noise_bound_float']:.4f} | {r['p_eq_r_float']:.4f} | "
                         f"{r['two_qubit']} | {r['used_qubits']} | {r['idle_L0']['max_idle_over_t2']:.3f} |")
    lines += ["", "## The full table", "",
              "| series | n | r | ANDs | seed | used | two-qubit | mid-meas | depth L=0 (ns) | depth L=1000 (ns) | noiseBound | p = r | clamped | vacuous | idle/T2 max L=0 | idle/T2 sum L=0 | idle/T2 max L=1000 | idle/T2 sum L=1000 | s |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in sorted(data["rows"], key=lambda r: (r["series"], r["n"])):
        lines.append(f"| {r['series']} | {r['n']} | {r['r']} | {r['ands']} | {r['seed']} | {r['used_qubits']} | {r['two_qubit']} | "
                     f"{r['mid_measurements']} | {float(Fraction(r['depth_ns_L0'])):.0f} | {float(Fraction(r['depth_ns_L1000'])):.0f} | "
                     f"{r['noise_bound_float']:.4f} | {r['p_eq_r_float']:.4f} | {'yes' if r['clamped'] else 'no'} | "
                     f"{'yes' if r['noise_vacuous'] else 'no'} | {r['idle_L0']['max_idle_over_t2']:.3f} | {r['idle_L0']['sum_idle_over_t2']:.3f} | "
                     f"{r['idle_L1000']['max_idle_over_t2']:.3f} | {r['idle_L1000']['sum_idle_over_t2']:.3f} | {r['seconds']} |")
    lines += ["", "Skipped rows (the early stop):", ""]
    for key in sorted(data["series"]):
        for s in data["series"][key]["skipped"]:
            lines.append(f"- {key} n = {s['n']}: {s['reason']}")
    if not any(data["series"][k]["skipped"] for k in data["series"]):
        lines.append("- none")
    lines += ["", "Routing (b) per target: " + "; ".join(
        f"{k}: {v['routing'].get('edges_removed', 0)} edges removed, component of {v['routing'].get('component_qubits', '—')} qubits"
        for k, v in sorted(data["series"].items()) if k.endswith(":b")), "",
        "## The premises and the idle-exposure diagnostic", "",
        "Every bound above is conditional: (P-cal) the calibration is the target file's snapshot, shipped with",
        "qiskit-ibm-runtime and recorded from a real device on a past date; (P-stoch) each basis operation is ideal with",
        "probability `1 − p`, `p = min 1 ((d+1)/d · r)`, and otherwise an arbitrary channel on the whole register;",
        "(P-ro) each readout is ideal with probability `1 − r`; (P-idle) idle qubits suffer no error. (P-idle) is the",
        "premise furthest from a device: the **idle-exposure diagnostic** is each used qubit's idle time under the ASAP",
        "schedule (`hw/physgrade.py`; the depth minus the qubit's busy time) divided by its T2 from the target file",
        "(`calibration.t2_s`), reported as the maximum and the sum over the used qubits at L = 0 and 1000 ns. A ratio",
        "near or above 1 means a qubit idles for about a coherence time while the bound assumes it keeps its state:",
        "the conditional statement then says little about the device even when the bound is below 1. The diagnostic is",
        "reported, not part of any bound, and the Lean theory is unchanged by it.", ""]
    for key, r in fr.items():
        if r is not None:
            lines.append(f"- frontier {key} (n = {r['n']}): idle/T2 max {r['idle_L0']['max_idle_over_t2']:.3f} (qubit {r['idle_L0']['worst_qubit']}), "
                         f"sum {r['idle_L0']['sum_idle_over_t2']:.3f} at L = 0; max {r['idle_L1000']['max_idle_over_t2']:.3f}, "
                         f"sum {r['idle_L1000']['sum_idle_over_t2']:.3f} at L = 1000 ns")
    lines += ["", "## The frontier certificates", "",
              "The committed certificates at the frontier (hw_n2 and hw_n3 are the n = 2, 3 tree-mbu instances on",
              "FakeTorino, certified in 27b): see `examples/certs/fr_*` and `hw/artifacts/fr_*` — their δ' is the row's",
              "`noiseBound`; `tests/diff/hw_frontier_check.py` checks the rows of the committed instances against",
              "`cqr hw noise` and `cqr hw grade` and the frontier rows against the certificates.", ""]
    with open(TABLE, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {os.path.relpath(TABLE, ROOT)} ({len(data['rows'])} rows)")
    for key, r in fr.items():
        print(f"frontier {key}: " + (f"n = {r['n']} noiseBound {r['noise_bound_float']:.4f} ({r['name']})" if r else "none"))


def promote(name, target_name):
    src = os.path.join(SCRATCH, "artifacts", f"{name}__{target_name}")
    dst = os.path.join(ROOT, "hw", "artifacts", f"{name}__{target_name}")
    if os.path.exists(dst):
        raise SystemExit(f"{dst} exists: an existing artifact is never overwritten")
    shutil.copytree(src, dst)
    n = int(name.split("_")[1][1:])
    m = json.load(open(os.path.join(dst, "manifest.json"), encoding="utf-8"))
    tshort = target_name.replace("fake_", "")
    cert = f"examples/certs/fr_n{n}_{name.split('_', 2)[2]}"
    print(f"copied to hw/artifacts/{name}__{target_name}; the certificate commands (kernel jobs; run one Lean process at a time):")
    print(f"  cqr certify examples/frontier/fr_n{n}.cqr --solutions 1 --iterations {m['grover']['r']}"
          f"{' --uncompute coherent' if m['uncompute'] == 'coherent' else ''}{' --shape few:log' if m['grover']['shape'] != 'tree' else ''} --out {cert}")
    print(f"  cqr hw check --artifact hw/artifacts/{name}__{target_name} --target {TARGET_FILES[target_name]}")
    print(f"  cqr hw noisecert --artifact hw/artifacts/{name}__{target_name} --target {TARGET_FILES[target_name]} --ff-latency 1000 --cert {cert} --out examples/certs/{os.path.basename(cert)}_{tshort}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--cqr", required=True)
    ap.add_argument("--series", help="<target>:<mode>:<routing>")
    ap.add_argument("--seeds", default="0-19")
    ap.add_argument("--render", action="store_true")
    ap.add_argument("--promote", help="<row name>:<target>")
    a = ap.parse_args(argv)
    if a.series:
        t, m, r = a.series.split(":")
        run_series(a.cqr, t, m, r, seeds_of(a.seeds))
    if a.promote:
        name, t = a.promote.split(":")
        promote(name, t)
    if a.render:
        render(load_rows())
    return 0


if __name__ == "__main__":
    sys.exit(main())
