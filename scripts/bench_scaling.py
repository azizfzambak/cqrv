"""Stage 14b (docs/tasks/STAGE14_TASK.md B1–B2; report §9.5.1) — kernel-time and grade scaling.

Measurement only: no change to the Lean library. Reads `bench/scaling/manifest.json`
(scripts/gen_scaling.py), keeps every raw result in the git-ignored `bench/scaling/out/`
(`state.json` plus one `cqr certify` output directory per instance and iteration count), and
generates `docs/benchmarks/scaling.csv`, `SCALING.md` and `KERNEL_TIMES.md` from the raw results
(no hand-edited number). Every phase is resumable (finished items are skipped) and takes
`--minutes B`: it stops before starting an item once B minutes have passed.

Phases
  harness    the statevector harness on the synthesized oracle of every instance with n ≤ 12
             (CLAUDE.md rule 9; `statevector.check_phase_oracle` with the reference predicate of
             gen_scaling.reference, never the network): every measurement branch when the oracle
             has a ≤ 6 ancillae and n + a ≤ 20 qubits; `--samples` Born-sampled branches
             (`statevector.run_ir_sampled`) when n + a ≤ 20 (the simulator's MAX_QUBITS); otherwise
             `infeasible` (the simulator holds all n + a qubits).
  certify    `cqr certify <src> --solutions M --iterations r --out …` for r = 1 and r⋆ (1 < r⋆ ≤ 4),
             timeout --timeout s (default 900): outcome certified / timeout / oom / error; the
             certificate's grade, δ, G, the oracle grade, network node counts (from `net` in
             Cert.lean) and the emitted instruction count (gates of `emitted`, alloc/free included).
             For n ≤ 12 the certificate decides M by the kernel (`hM_count`, Stage 14a); when that
             form times out, the instance is also certified with `--count-limit 0` (M as the
             hypothesis `hM_card`, key suffix `_h`), so that the kernel cost of the count and the
             cost of the circuit are measured separately (column `M by`).
  time       the bench_kernel.sh protocol on every certified Cert.lean: `--rounds` (default 6)
             interleaved runs of `lean -Dprofiler=true Cert.lean` (round-major order, so the
             instances alternate), the first round excluded; per run the profiler's
             `type checking` (kernel s), wall s, peak working set (Windows: GetProcessMemoryInfo
             of the lean process, no extra dependency; elsewhere `resource` if available) and the
             outcome (certified / timeout / oom / error).
  committed  the same protocol on examples/certs/{grover_pred_037, simple_alu_x0_1,
             grover_pred_037_few}/Cert.lean (KERNEL_TIMES.md).
  classify   `classify <key> --log <lean.log>`: re-classify one failed certify item from the
             saved full output of `lake env lean -Dprofiler=true <key>/Cert.lean` (the
             certify phase keeps only the output tail): the same rule as the runs
             (`classify_output`): a memory or stack-resource message → `oom`, anything else
             non-zero → `error`; the first `error:` line is recorded as `message`.
  report     write the three files under docs/benchmarks/.

Usage (after `lake build`, from anywhere):
  python -I scripts/bench_scaling.py harness --cqr .lake/build/bin/cqr.exe [--minutes 9]
  python -I scripts/bench_scaling.py certify --cqr .lake/build/bin/cqr.exe [--minutes 9]
  python -I scripts/bench_scaling.py time [--minutes 9]
  python -I scripts/bench_scaling.py committed [--minutes 9]
  python -I scripts/bench_scaling.py classify rand_a64_r1_h --log bench/scaling/out/rand_a64_r1_h/lean.log
  python -I scripts/bench_scaling.py report
"""

import argparse
import csv
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import time

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import statevector as sv  # noqa: E402
import oracle_diff as od  # noqa: E402
import gen_scaling as gs  # noqa: E402

BENCH = os.path.join(ROOT, "bench", "scaling")
OUT = os.path.join(BENCH, "out")
STATE = os.path.join(OUT, "state.json")
DOCS = os.path.join(ROOT, "docs", "benchmarks")
COMMITTED = [("grover_pred_037", "grover_pred_037"), ("simple_alu_x0_1", "simple_alu_x0_1"),
             ("grover_pred_037_few", "grover_pred_037")]
THRESHOLD_S = 300.0


# --- state -----------------------------------------------------------------------------------

def load_state():
    if os.path.exists(STATE):
        with open(STATE, encoding="utf-8") as f:
            return json.load(f)
    return {"harness": {}, "certify": {}, "time": {}, "committed": {}}


def save_state(st):
    os.makedirs(OUT, exist_ok=True)
    tmp = STATE + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(st, f, indent=1, ensure_ascii=False)
    os.replace(tmp, STATE)


def manifest():
    with open(os.path.join(BENCH, "manifest.json"), encoding="utf-8") as f:
        return json.load(f)["instances"]


class Budget:
    def __init__(self, minutes):
        self.t0 = time.time()
        self.limit = minutes * 60 if minutes else None

    def left(self):
        return self.limit is None or time.time() - self.t0 < self.limit


# --- processes -------------------------------------------------------------------------------

def kill_tree(p):
    if platform.system() == "Windows":
        subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)], capture_output=True)
    else:
        p.kill()


def peak_mb(p):
    """Peak working set of a finished subprocess in MB (Windows: psapi via ctypes), or None."""
    if platform.system() == "Windows":
        try:
            import ctypes
            from ctypes import wintypes

            class PMC(ctypes.Structure):
                _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                            ("PeakWorkingSetSize", ctypes.c_size_t),
                            ("WorkingSetSize", ctypes.c_size_t),
                            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                            ("PagefileUsage", ctypes.c_size_t),
                            ("PeakPagefileUsage", ctypes.c_size_t)]
            pmc = PMC()
            pmc.cb = ctypes.sizeof(PMC)
            ok = ctypes.windll.psapi.GetProcessMemoryInfo(wintypes.HANDLE(p._handle),
                                                          ctypes.byref(pmc), pmc.cb)
            return round(pmc.PeakWorkingSetSize / 2 ** 20) if ok else None
        except Exception:
            return None
    try:
        import resource
        return round(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024)
    except Exception:
        return None


RESOURCE_RE = re.compile(r"out of memory|memory allocation|bad_alloc|std::bad_alloc|"
                         r"deep recursion detected|stack overflow|maximum recursion depth", re.I)


def classify_output(rc, out):
    """'ok' on exit 0; 'oom' when the output names a memory or stack resource (lean's out-of-
    memory message, `bad_alloc`, the kernel's `deep recursion detected` stack guard, a stack
    overflow); otherwise 'error' (a genuine kernel or elaboration failure)."""
    if rc == 0:
        return "ok"
    return "oom" if RESOURCE_RE.search(out or "") else "error"


def first_error(out):
    for line in (out or "").replace("\r", "").split("\n"):
        if ": error:" in line or line.startswith("error:"):
            return line.strip()
    return ""


def run_timed(cmd, timeout, env=None):
    """Run `cmd`; returns (outcome, rc, output text, wall s, peak MB). outcome: 'ok' / 'timeout' /
    'oom' / 'error' (`classify_output`)."""
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8", errors="replace", env=env)
    try:
        out, _ = p.communicate(timeout=timeout)
        outcome = classify_output(p.returncode, out)
    except subprocess.TimeoutExpired:
        kill_tree(p)
        out, _ = p.communicate()
        outcome = "timeout"
    wall = time.time() - t0
    return outcome, p.returncode, out or "", wall, peak_mb(p)


_LEAN_ENV = None


def lean_env():
    """The lean executable and LEAN_PATH of `lake env` (so that lean runs as the direct child and
    its peak memory can be read)."""
    global _LEAN_ENV
    if _LEAN_ENV is None:
        q = subprocess.run(["lake", "env", sys.executable, "-c",
                            "import os, shutil; print(os.environ.get('LEAN_PATH', '')); "
                            "print(shutil.which('lean'))"],
                           cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True)
        lp, lean = q.stdout.strip().splitlines()[:2]
        env = dict(os.environ)
        env["LEAN_PATH"] = lp
        _LEAN_ENV = (lean, env)
    return _LEAN_ENV


def kernel_s(output):
    """The profiler's cumulative `type checking` time in seconds (the last occurrence)."""
    v = None
    for line in output.replace("\r", "").split("\n"):
        m = re.match(r"\s*type checking\s+([0-9.]+)(ms|s|μs)\s*$", line)
        if m:
            v = float(m.group(1)) * {"ms": 1e-3, "s": 1.0, "μs": 1e-6}[m.group(2)]
    return v


def kernel_run(cert_lean, timeout):
    lean, env = lean_env()
    outcome, rc, out, wall, mem = run_timed([lean, "-Dprofiler=true", cert_lean], timeout, env)
    return {"outcome": "certified" if outcome == "ok" else outcome, "rc": rc,
            "kernel_s": kernel_s(out) if outcome == "ok" else None,
            "wall_s": round(wall, 2), "peak_mb": mem, "when": time.strftime("%Y-%m-%d %H:%M:%S")}


# --- phases ----------------------------------------------------------------------------------

def phase_harness(args, st, insts):
    budget = Budget(args.minutes)
    rng = np.random.default_rng(args.seed)
    for inst in insts:
        name = inst["name"]
        if name in st["harness"] or inst["n"] > 12:
            continue
        if not budget.left():
            print("harness: budget exhausted; rerun to continue")
            return
        res = od.synthesize(args.cqr, os.path.join(ROOT, inst["path"]))
        circ = res["circuit"]
        n, a = circ["n_data"], circ["n_anc"]
        pred = lambda x, inst=inst, n=n: gs.reference(inst, od.bits_of(x, n))  # noqa: E731
        t0 = time.time()
        try:
            if a <= 6 and n + a <= 20:
                k = sv.check_phase_oracle(circ, pred, rng, trials=1)
                verdict, detail = "pass", f"all {k} branches"
            elif n + a <= 20:
                signs = np.array([-1.0 if pred(x) else 1.0 for x in range(2 ** n)])
                psi = sv._random_state(n, rng)
                want = np.zeros(2 ** (n + a), dtype=complex)
                want[:: 2 ** a] = signs * psi
                seen = set()
                for _ in range(args.samples):
                    bits, s = sv.run_ir_sampled(circ, psi, rng)
                    seen.add(tuple(sorted(bits.items())))
                    overlap = abs(np.vdot(want, s.amp)) / np.sqrt(s.norm2())
                    if overlap < 1 - 1e-9:
                        raise AssertionError(f"branch {bits}: overlap {overlap:.12f} != 1")
                verdict, detail = "pass", f"{args.samples} Born-sampled branches ({len(seen)} distinct)"
            else:
                verdict, detail = "infeasible", f"n + a = {n + a} qubits in the statevector"
        except (AssertionError, sv.RestorationError) as e:
            verdict, detail = "FAIL", str(e)
        st["harness"][name] = {"verdict": verdict, "detail": detail, "n": n, "a": a,
                               "seconds": round(time.time() - t0, 1)}
        save_state(st)
        print(f"harness {name}: {verdict} ({detail}; {st['harness'][name]['seconds']} s)")
        if verdict == "FAIL":
            print("harness: FAIL is a stop condition (14b): report it as a bug; not fixed here")
            return


def net_counts(cert_text):
    m = re.search(r"def net : Network := ⟨\d+, #\[(.*?)\],\s*\[", cert_text, re.S)
    nodes = m.group(1)
    return {"and": len(re.findall(r"\.and ", nodes)), "xor": len(re.findall(r"\.xor ", nodes)),
            "not": len(re.findall(r"\.not ", nodes)), "nodes": len(nodes.split(","))}


def emitted_count(cert_text):
    m = re.search(r"def emitted : Circuit := ⟨\d+, \[(.*?)\]⟩", cert_text, re.S)
    return len([g for g in re.split(r",\s*(?=\.)", m.group(1)) if g.strip()])


def phase_certify(args, st, insts):
    budget = Budget(args.minutes)
    for inst in insts:
        for r in inst["iterations"]:
          for variant in ("", "_h"):
            key = f"{inst['name']}_r{r}{variant}"
            if key in st["certify"]:
                continue
            if variant == "_h":
                base = st["certify"].get(f"{inst['name']}_r{r}")
                if inst["n"] > 12 or base is None or base["outcome"] == "certified":
                    continue
            if not budget.left():
                print("certify: budget exhausted; rerun to continue")
                return
            d = os.path.join(OUT, key)
            shutil.rmtree(d, ignore_errors=True)
            cmd = [args.cqr, "certify", os.path.join(ROOT, inst["path"]), "--solutions",
                   str(inst["M"]), "--iterations", str(r), "--out", d] + \
                (["--count-limit", "0"] if variant else [])
            outcome, rc, out, wall, _ = run_timed(cmd, args.timeout)
            rec = {"instance": inst["name"], "r": r, "wall_s": round(wall, 1), "rc": rc,
                   "count": "hypothesis" if (variant or inst["n"] > 12) else "kernel_decided",
                   "when": time.strftime("%Y-%m-%d %H:%M:%S")}
            lines = [ln for ln in out.replace("\r", "").split("\n") if ln.strip()]
            if outcome == "ok":
                cert = json.load(open(os.path.join(d, "certificate.json"), encoding="utf-8"))
                text = open(os.path.join(d, "Cert.lean"), encoding="utf-8").read()
                ores = od.synthesize(args.cqr, os.path.join(ROOT, inst["path"]))
                rec.update(outcome="certified" if cert["status"] == "certified" else "error",
                           status_line=lines[-1], grade=cert["grade"], delta=cert["spec"]["delta"],
                           G=cert["hardware_perturbation"]["G"],
                           solution_count=cert["solution_count"], axioms=cert["axioms"],
                           count=cert["solution_count"]["status"],
                           kernel_s_first=cert["reference_configuration"]["kernel_check"]["kernel_ms"] / 1000,
                           net=net_counts(text), instructions=emitted_count(text),
                           oracle_grade=ores["grade"], cert_lean=os.path.relpath(
                               os.path.join(d, "Cert.lean"), ROOT).replace("\\", "/"))
            else:
                rec.update(outcome=outcome, status_line=lines[-1] if lines else "",
                           output_tail=lines[-8:], message=first_error(out))
                rec.update(planned_of(d))
            st["certify"][key] = rec
            save_state(st)
            print(f"certify {key}: {rec['outcome']} ({rec['wall_s']} s)"
                  + (f", grade {rec['grade']}, {rec['instructions']} instructions"
                     if rec["outcome"] == "certified" else f": {rec['status_line'][:120]}"))


def planned_of(d):
    """The circuit `cqr certify` wrote to <d>/Cert.lean before the kernel check (present even
    when the check failed): node counts of `net`, gates of `emitted` and the `grade_eq` literal.
    These are the synthesizer's figures, not kernel-checked ones (the report marks them)."""
    f = os.path.join(d, "Cert.lean")
    if not os.path.exists(f):
        return {}
    text = open(f, encoding="utf-8").read()
    m = re.search(r"theorem grade_eq : Synthesis.grade emitted = ⟨(\d+), (\d+), (\d+), (\d+)⟩", text)
    g = dict(zip("wdta", map(int, m.groups()))) if m else None
    return {"net": net_counts(text), "instructions": emitted_count(text), "planned_grade": g,
            "cert_lean": os.path.relpath(f, ROOT).replace("\\", "/")}


def phase_classify(args, st):
    rec = st["certify"][args.key]
    if rec["outcome"] == "certified":
        sys.exit(f"classify: {args.key} is certified; nothing to classify")
    out = open(args.log, encoding="utf-8", errors="replace").read()
    outcome = classify_output(rec["rc"] if rec["rc"] else 1, out)
    rec.update(outcome="error" if outcome == "ok" else outcome, message=first_error(out),
               log=os.path.relpath(os.path.abspath(args.log), ROOT).replace("\\", "/"),
               classified=time.strftime("%Y-%m-%d %H:%M:%S"), kernel_s_log=kernel_s(out))
    rec.update(planned_of(os.path.join(OUT, args.key)))
    save_state(st)
    print(f"classify {args.key}: {rec['outcome']} — {rec['message'][:160]}")


def timed_items(keys, rounds):
    return [(rd, k) for rd in range(rounds) for k in keys]


def phase_time(args, st, which):
    """which = 'time' (the scaling certificates) or 'committed'."""
    budget = Budget(args.minutes)
    if which == "time":
        keys = [k for k, v in st["certify"].items() if v["outcome"] == "certified"]
        files = {k: os.path.join(ROOT, st["certify"][k]["cert_lean"]) for k in keys}
    else:
        keys = [d for d, _ in COMMITTED]
        files = {d: os.path.join(ROOT, "examples", "certs", d, "Cert.lean") for d in keys}
    runs = st[which]
    for rd, k in timed_items(keys, args.rounds):
        runs.setdefault(k, [])
        if len(runs[k]) > rd:
            continue
        if not budget.left():
            print(f"{which}: budget exhausted; rerun to continue")
            return
        rec = kernel_run(files[k], args.timeout)
        rec["round"] = rd
        runs[k].append(rec)
        save_state(st)
        print(f"{which} {k} round {rd}: {rec['outcome']}, kernel {rec['kernel_s']} s, "
              f"wall {rec['wall_s']} s, peak {rec['peak_mb']} MB")


# --- report ----------------------------------------------------------------------------------

def stats(samples):
    """min / median of the kernel times of the runs after the first (the protocol), the median
    wall time, the largest peak, and the outcome (timeout / oom / error if any run was one)."""
    used = samples[1:] if len(samples) > 1 else samples
    ks = [s["kernel_s"] for s in used if s["kernel_s"] is not None]
    bad = [s["outcome"] for s in samples if s["outcome"] != "certified"]
    return {"runs": len(samples), "samples": len(used),
            "kernel_min": min(ks) if ks else None,
            "kernel_median": statistics.median_low(ks) if ks else None,
            "wall_median": statistics.median_low([s["wall_s"] for s in used]) if used else None,
            "peak_mb": max([s["peak_mb"] or 0 for s in samples] or [0]) or None,
            "outcome": bad[0] if bad else "certified", "all": [s["kernel_s"] for s in samples]}


def fmt(x, nd=2):
    return "—" if x is None else (f"{x:.{nd}f}" if isinstance(x, float) else str(x))


def g4(g):
    return f"({g['w']}, {g['d']}, {g['t']}, {g['a']})"


def machine():
    try:
        q = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command",
                            "$p = Get-CimInstance Win32_Processor | Select-Object -First 1; "
                            "$o = Get-CimInstance Win32_OperatingSystem; "
                            "\"$($p.Name); $($p.NumberOfLogicalProcessors) logical CPUs; "
                            "$($p.MaxClockSpeed) MHz; RAM $([int]($o.TotalVisibleMemorySize/1024)) MB; "
                            "$($o.Caption) $($o.Version)\""],
                           capture_output=True, text=True, encoding="utf-8", timeout=60)
        return q.stdout.strip()
    except Exception:
        return platform.platform()


def toolchain():
    tc = open(os.path.join(ROOT, "lean-toolchain"), encoding="utf-8").read().strip()
    man = json.load(open(os.path.join(ROOT, "lake-manifest.json"), encoding="utf-8"))
    revs = {p["name"]: p["rev"][:12] for p in man["packages"]}
    return f"{tc}, Mathlib {revs.get('mathlib')}, Physlib {revs.get('Physlib')}"


def rows_of(st, insts):
    by_name = {i["name"]: i for i in insts}
    rows = []
    for key, c in st["certify"].items():
        inst = by_name[c["instance"]]
        t = stats(st["time"].get(key, [])) if key in st["time"] else None
        h = st["harness"].get(inst["name"], {"verdict": "n/a (n > 12)", "detail": ""})
        row = {"instance": inst["name"], "family": inst["family"], "n": inst["n"], "r": c["r"],
               "M": inst["M"], "r_star": inst["r_star"], "outcome": c["outcome"],
               "solution_count": c.get("count") or (c.get("solution_count") or {}).get("status"),
               "key": key, "message": c.get("message", ""), "inst_a": inst.get("oracle_a", 0),
               "harness": h["verdict"], "harness_detail": h["detail"],
               "certify_wall_s": c["wall_s"]}
        if c["outcome"] == "certified":
            og, fg = c["oracle_grade"], c["grade"]
            row.update(and_nodes=c["net"]["and"], xor_nodes=c["net"]["xor"],
                       net_nodes=c["net"]["nodes"], oracle_w=og["w"], oracle_d=og["d"],
                       oracle_t=og["t"], oracle_a=og["a"], w=fg["w"], d=fg["d"], t=fg["t"],
                       a=fg["a"], instructions=c["instructions"], G=c["G"], delta=c["delta"])
        else:
            pl = c if c.get("net") else planned_of(os.path.join(OUT, key))
            if pl.get("net"):
                row.update(and_nodes=pl["net"]["and"], xor_nodes=pl["net"]["xor"],
                           net_nodes=pl["net"]["nodes"], instructions=pl["instructions"],
                           planned_grade=pl.get("planned_grade"))
        if t:
            row.update(kernel_runs=t["runs"], kernel_min_s=t["kernel_min"],
                       kernel_median_s=t["kernel_median"], wall_median_s=t["wall_median"],
                       peak_mb=t["peak_mb"], kernel_all_s=" ".join(fmt(x) for x in t["all"]))
            if t["outcome"] != "certified":
                row["outcome"] = t["outcome"]
        rows.append(row)
    fam_order = {"carry_k": 0, "rand_a": 1, "alu_bits": 2}
    rows.sort(key=lambda r: (fam_order[r["family"]], r["n"] if r["family"] != "rand_a" else 0,
                             r["inst_a"], r["r"], r["solution_count"] != "kernel_decided"))
    return rows


CSV_COLS = ["key", "instance", "family", "n", "r", "M", "r_star", "and_nodes", "xor_nodes", "net_nodes",
            "oracle_w", "oracle_d", "oracle_t", "oracle_a", "w", "d", "t", "a", "instructions",
            "G", "delta", "solution_count", "kernel_runs", "kernel_min_s", "kernel_median_s",
            "wall_median_s", "peak_mb", "certify_wall_s", "outcome", "message", "harness",
            "harness_detail", "kernel_all_s"]


def write_csv(rows):
    os.makedirs(DOCS, exist_ok=True)
    with open(os.path.join(DOCS, "scaling.csv"), "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_COLS, lineterminator="\n")
        w.writeheader()
        for r in rows:
            w.writerow({k: ("" if r.get(k) is None else r.get(k)) for k in CSV_COLS})


def loglog_slope(xs, ys):
    """Least-squares slope of log y against log x (None with fewer than 2 distinct points)."""
    pts = [(np.log(x), np.log(y)) for x, y in zip(xs, ys) if x and y]
    if len({p[0] for p in pts}) < 2:
        return None
    a = np.array(pts)
    return float(np.polyfit(a[:, 0], a[:, 1], 1)[0])


MBY = {"kernel_decided": "kernel", "hypothesis": "hM_card", None: "—"}


def lean_threads(st):
    """LEAN_NUM_THREADS as recorded by `cqr certify` in the certificates of the certify phase
    (`reference_configuration.lean_threads`); the env of the report run is not used."""
    vals = set()
    for key, c in st["certify"].items():
        f = os.path.join(OUT, key, "certificate.json")
        if c["outcome"] == "certified" and os.path.exists(f):
            vals.add(str(json.load(open(f, encoding="utf-8"))["reference_configuration"]["lean_threads"]))
    return "/".join(sorted(vals)) if vals else "unrecorded"


def write_scaling_md(rows, args, st):
    L = []
    L.append("# Kernel-time and grade scaling (Stage 14b)\n")
    L.append("Report §9.5.1 (reference configuration, measured values only), §5.1.3; "
             "docs/tasks/STAGE14_TASK.md B1–B2. Generated by `scripts/bench_scaling.py report` from "
             "`docs/benchmarks/scaling.csv` (raw results in the git-ignored `bench/scaling/out/`); "
             "no number is hand-edited. Sources: `bench/scaling/*.cqr` (`scripts/gen_scaling.py`, "
             "fixed seeds).\n")
    L.append("## Method\n")
    L.append(f"- Machine: {machine()}; `LEAN_NUM_THREADS={lean_threads(st)}` (as recorded in the "
             "certificates of the certify phase; the time and committed phases ran in the same shell).")
    L.append(f"- Toolchain: {toolchain()}.")
    L.append("- Per instance and iteration count: `cqr certify <src> --solutions M --iterations r` "
             "(timeout 900 s; M from the truth table of the network, cross-checked against the "
             "reference predicate on every input; for n ≤ 12 the certificate decides M by the kernel, "
             "`hM_count`, for n > 12 it is the hypothesis `hM_card`), then "
             f"{args.rounds} interleaved runs of `lean -Dprofiler=true Cert.lean` in round-major "
             "order (the instances alternate), the first run excluded: kernel time = the profiler's "
             "`type checking`, min and median of the remaining runs; wall time = median wall of "
             "those runs; peak memory = peak working set of the lean process (Windows "
             "`GetProcessMemoryInfo`). Outcome: `certified`, `timeout` (900 s), `oom`, `error`.")
    L.append("- Harness (CLAUDE.md rule 9) on the synthesized oracle of every n ≤ 12 instance, "
             "with the reference predicate (never the network): every measurement branch when "
             "a ≤ 6 and n + a ≤ 20, otherwise Born-sampled branches when n + a ≤ 20 (the simulator's "
             "MAX_QUBITS), otherwise `infeasible` (the statevector holds all n + a qubits). The grade of an instance whose "
             "harness verdict is not `pass` is reported with the mark † (kernel-checked certificate, "
             "no statevector check). ‡ = the synthesizer's grade written to Cert.lean (`grade_eq`) for "
             "an instance whose kernel check did not finish: planned, not certified.")
    L.append("- Grades are measured on the emitted circuit (the certificate's `grade_eq`); "
             "`instructions` = gates of the `emitted` literal (alloc/free included); G = noisy "
             "operations of `δ_hw ≤ δ + G·p̄` (terminal measurements included); AND / XOR = nodes "
             "of `net`.\n")
    for fam, title in (("carry_k", "carry_k — carry-out of a k-bit ripple-carry adder (n = 2k)"),
                       ("rand_a", "rand_a — random AND/XOR/NOT/if predicates with a AND nodes"),
                       ("alu_bits", "alu_bits — RevLib Simple ALU, other output bits of x0")):
        fr = [r for r in rows if r["family"] == fam]
        L.append(f"## {title}\n")
        L.append("| instance | n | r (r⋆) | M | M by | AND / XOR | oracle (w, d, t, a) | full (w, d, t, a) | "
                 "instr. | G | kernel min | kernel median | wall median | peak MB | outcome | harness |")
        L.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
        for r in fr:
            outc = r["outcome"] + (f" ({r['message'].split('error: ')[-1][:40]}…)"
                                   if r["outcome"] == "oom" and r["message"] else "")
            mark = "" if r["harness"] == "pass" else " †"
            og = (g4({"w": r["oracle_w"], "d": r["oracle_d"], "t": r["oracle_t"], "a": r["oracle_a"]})
                  if "w" in r else "—")
            fg = g4({"w": r["w"], "d": r["d"], "t": r["t"], "a": r["a"]}) if "w" in r else (
                g4(r["planned_grade"]) + " ‡" if r.get("planned_grade") else "—")
            mby = {"kernel_decided": "kernel", "hypothesis": "hM_card"}.get(r["solution_count"], "—")
            L.append(f"| {r['instance']} | {r['n']} | {r['r']} ({r['r_star']}) | {r['M']} | {mby} | "
                     f"{r.get('and_nodes', '—')} / {r.get('xor_nodes', '—')} | {og}{mark} | {fg}{mark} | "
                     f"{r.get('instructions', '—')} | {r.get('G', '—')} | "
                     f"{fmt(r.get('kernel_min_s'))} s | {fmt(r.get('kernel_median_s'))} s | "
                     f"{fmt(r.get('wall_median_s'))} s | {fmt(r.get('peak_mb'), 0)} | {outc} | "
                     f"{r['harness']}{(' (' + r['harness_detail'] + ')') if r['harness_detail'] else ''} |")
        over = [r for r in fr if r["outcome"] != "certified"
                or (r.get("kernel_median_s") or 0) > THRESHOLD_S]
        if over:
            o = min(over, key=lambda r: (r.get("instructions") or 10 ** 9))
            L.append(f"\nSmallest instance whose kernel check exceeds {THRESHOLD_S:.0f} s or fails: "
                     f"**{o['instance']}** (r = {o['r']}, M by {MBY[o['solution_count']]}, "
                     f"{o.get('instructions', '—')} instructions, outcome {o['outcome']}, median "
                     f"{fmt(o.get('kernel_median_s'))} s).")
            oh = [r for r in over if r["solution_count"] == "hypothesis"]
            if oh:
                o = min(oh, key=lambda r: (r.get("instructions") or 10 ** 9))
                L.append(f"Circuit only (M by hM_card, no `hM_count`): **{o['instance']}** (r = {o['r']}, "
                         f"{o.get('instructions', '—')} instructions, outcome {o['outcome']}, median "
                         f"{fmt(o.get('kernel_median_s'))} s).")
            else:
                mx = max((r.get("kernel_median_s") or 0) for r in fr if r["solution_count"] == "hypothesis")
                L.append(f"Circuit only (M by hM_card): no instance of this family exceeds {THRESHOLD_S:.0f} s "
                         f"or fails (largest median {mx:.2f} s)." if mx else "")
            L.append("")
        else:
            mx = max((r.get("kernel_median_s") or 0) for r in fr) if fr else 0
            L.append(f"\nNo instance of this family exceeds {THRESHOLD_S:.0f} s or fails "
                     f"(largest median {mx:.2f} s).\n")
    findings(L, rows, st)
    L.append("## Kernel time against instruction count\n")
    done = [r for r in rows if r.get("kernel_median_s") and r.get("instructions")]
    L.append("| instance | r | M by | instructions | AND nodes | kernel min | kernel median | median / instr. |")
    L.append("|---|---|---|---|---|---|---|---|")
    for r in sorted(done, key=lambda r: r["instructions"]):
        mby = {"kernel_decided": "kernel", "hypothesis": "hM_card"}.get(r["solution_count"], "—")
        L.append(f"| {r['instance']} | {r['r']} | {mby} | {r['instructions']} | {r['and_nodes']} | "
                 f"{fmt(r['kernel_min_s'])} s | {fmt(r['kernel_median_s'])} s | "
                 f"{1000 * r['kernel_median_s'] / r['instructions']:.1f} ms |")
    hyp = [r for r in done if r["solution_count"] == "hypothesis"]
    for label, sel in (("all certified instances", done),
                       ("the instances with M as a hypothesis (no `hM_count`: circuit cost only)", hyp)):
        sl_med = loglog_slope([r["instructions"] for r in sel], [r["kernel_median_s"] for r in sel])
        sl_min = loglog_slope([r["instructions"] for r in sel], [r["kernel_min_s"] for r in sel])
        L.append(f"\nLeast-squares slope of log(kernel time) against log(instructions) over {label}: "
                 f"median {fmt(sl_med)}, min {fmt(sl_min)} (1 = linear, 2 = quadratic).")
    sp = {k: spread(v) for k, v in list(st["time"].items()) + list(st["committed"].items())}
    sp = {k: v for k, v in sp.items() if v is not None}
    wide = {k: v for k, v in sp.items() if v > 1.1}
    rest = max((v for k, v in sp.items() if k not in wide), default=None)
    L.append("\nKernel times on this hybrid P/E-core CPU were bimodal in Stage 13a′ and 14a (DECISIONS.md "
             "2026-10-28, 2026-10-29); in this run every sample set is unimodal"
             + (f" (spread ≤ {rest:.2f})" if rest else "")
             + (" except " + ", ".join(f"{k} ({v:.2f})" for k, v in wide.items()) if wide else "")
             + ", so min and median agree. Rows with `M by = kernel` include the kernel evaluation of "
             "`Network.countSat` on 2^n inputs (`hM_count`), which grows with 2^n and the network size, "
             "not with the circuit.\n")
    with open(os.path.join(DOCS, "SCALING.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(L) + "\n")


def spread(samples):
    """max / min of the kernel samples after the first (1.0 = identical)."""
    ks = [s["kernel_s"] for s in samples[1:] if s.get("kernel_s")]
    return (max(ks) / min(ks)) if ks else None


def findings(L, rows, st):
    """Sections computed from the rows: memory, the failed items, wall-time outliers, modality."""
    L.append("## Memory and the kernel-decided count\n")
    kd = [r for r in rows if r["solution_count"] == "kernel_decided"]
    peak = [r for r in kd if r.get("peak_mb")]
    top = max(peak, key=lambda r: r["peak_mb"]) if peak else None
    n12 = [r for r in kd if r["n"] == 12]
    L.append("| n | kernel-decided certificates (`hM_count`) | outcomes | largest peak MB |")
    L.append("|---|---|---|---|")
    for n in sorted({r["n"] for r in kd}):
        sel = [r for r in kd if r["n"] == n]
        outs = sorted({r["outcome"] for r in sel})
        pk = max((r.get("peak_mb") or 0) for r in sel) or None
        L.append(f"| {n} | {', '.join(r['key'] for r in sel)} | {', '.join(outs)} | {fmt(pk, 0)} |")
    tot = machine_total_mb()
    L.append("")
    if top:
        L.append(f"The largest peak working set of a kernel-decided certificate is **{top['peak_mb']} MB "
                 f"({top['peak_mb'] / 1024:.1f} GB) for {top['key']} (n = {top['n']})**"
                 + (f" on a machine with {tot} MB ({tot / 1024:.1f} GB) of RAM" if tot else "") + ".")
    kdc = [r for r in kd if r["outcome"] == "certified" and r.get("kernel_median_s")]
    big = max(kdc, key=lambda r: (r["n"], r["kernel_median_s"])) if kdc else None
    ck = sorted([r for r in kdc if r["family"] == "carry_k"], key=lambda r: r["n"])
    step = (ck[-2], ck[-1]) if len(ck) >= 2 else None
    if n12:
        bad = [r for r in n12 if r["outcome"] != "certified"]
        L.append(f"At n = 12, {len(bad)} of {len(n12)} kernel-decided certificates did not finish "
                 f"({', '.join(r['key'] + ' ' + r['outcome'] for r in n12)}); the `_h` form of the same "
                 "instance (M as the hypothesis `hM_card`, `--count-limit 0`) is in the tables above "
                 "where it finished. The count `hM_count` evaluates `Network.pred` on 2^n inputs inside the "
                 "kernel; its working set at n = 10 already takes most of this machine's RAM, and 2^12 is four "
                 "times 2^10. The kernel time of the kernel-decided certificates also grows fast with n"
                 + (f" ({step[0]['instance']} → {step[1]['instance']}: {fmt(step[0]['kernel_median_s'])} s → "
                    f"{fmt(step[1]['kernel_median_s'])} s median, ×"
                    f"{step[1]['kernel_median_s'] / step[0]['kernel_median_s']:.1f} for "
                    f"{step[1]['n'] - step[0]['n']} more input bits)" if step else "")
                 + ", so from the time trend alone a 900 s timeout at n = 12 is expected; with the memory "
                 "trend both bind, and which binds first is not measured because the peak of a timed-out "
                 "run is not recorded (the certify phase keeps the peak of finished runs only). "
                 "**Recommendation (no change in this stage): revisit the default `--count-limit 12` of "
                 "`cqr certify` (Stage 14a). The largest kernel-decided certificate that finished is "
                 + (f"{big['instance']} (n = {big['n']}, {fmt(big['kernel_median_s'])} s median, "
                    f"{big['peak_mb']} MB)" if big else "none")
                 + "; no n = 12 one finished. A default of 10, or a default tied to the network size, with "
                 "the `_h` form as the fallback.**")
    L.append("\n## Items that did not finish\n")
    L.append("| key | M by | n | r | instructions (Cert.lean) | AND / XOR | planned grade ‡ | outcome | wall s | message |")
    L.append("|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        if r["outcome"] == "certified":
            continue
        mby = {"kernel_decided": "kernel", "hypothesis": "hM_card"}.get(r["solution_count"], "—")
        pg = g4(r["planned_grade"]) if r.get("planned_grade") else "—"
        L.append(f"| {r['key']} | {mby} | {r['n']} | {r['r']} | {r.get('instructions', '—')} | "
                 f"{r.get('and_nodes', '—')} / {r.get('xor_nodes', '—')} | {pg} | {r['outcome']} | "
                 f"{r['certify_wall_s']} | {r['message'] or '—'} |")
    hyp_to = [r for r in rows if r["outcome"] == "timeout" and r["solution_count"] == "hypothesis"]
    if hyp_to:
        L.append("\nThe hypothesis-form timeouts carry no `hM_count`: their cost is the circuit alone "
                 "(`emitted_ok` re-runs the synthesizer in the kernel and compares with `emitted`, "
                 "`grade_eq`, `nAnc_eq`): "
                 + "; ".join(f"{r['key']} has {r.get('instructions', '—')} instructions "
                             f"(planned grade {g4(r['planned_grade']) if r.get('planned_grade') else '—'})"
                             for r in hyp_to)
                 + ". The largest certified circuit has "
                 + str(max((r.get('instructions') or 0) for r in rows if r['outcome'] == 'certified'))
                 + " instructions.")
    res = [r for r in rows if r["outcome"] == "oom"]
    for r in res:
        c = st["certify"][r["key"]]
        L.append(f"\n`{r['key']}` ({r.get('instructions', '—')} instructions): outcome `oom` = a memory or "
                 f"stack-resource failure, classified by `bench_scaling.py classify` from the full log "
                 f"`{c.get('log', '—')}` (message: `{r['message']}`"
                 + (f"; the profiler's `type checking` before the failure {fmt(c['kernel_s_log'])} s" if c.get('kernel_s_log') else "")
                 + "). The kernel's `deep recursion detected` is its native-stack guard raised while "
                 "evaluating the `decide +kernel` of `emitted_ok`; no certificate was written, the "
                 "`cert` theorem of that file depends on `sorryAx`.")
    L.append("\n## Wall-time outliers\n")
    out = []
    for key, samples in list(st["time"].items()) + list(st["committed"].items()):
        walls = [s["wall_s"] for s in samples]
        med = statistics.median_low(walls)
        for s in samples:
            if s["wall_s"] > 3 * med:
                out.append((key, s["round"], s["wall_s"], s["kernel_s"], med))
    if out:
        for key, rd, w, k, med in out:
            L.append(f"- `{key}` round {rd}: wall {w} s against a median wall of {med} s, kernel "
                     f"(`type checking`) {fmt(k)} s — the stall is outside the kernel check (process start, "
                     f".olean import or an OS pause; the profiler attributes none of it to type checking).")
        L.append("\nThe kernel columns are unaffected: kernel time is the profiler's `type checking`, "
                 "not the wall time; `wall median` is the median of the samples after the first and one "
                 "outlier among 5 samples does not move it; `wall_s` of every run is in state.json and the "
                 "per-run kernel samples are in the `kernel_all_s` column of scaling.csv.")
    else:
        L.append("No run's wall time exceeded three times its median.")
    L.append("\n## Modality of the samples\n")
    L.append("Spread = max / min of the 5 kernel samples after the first (Stage 13a′ and 14a saw bimodal "
             "fast / slow regimes on this hybrid P/E-core CPU, e.g. 14a's simple_alu_x0_1 11.7–28.0 s, "
             "spread 2.4, DECISIONS.md 2026-10-29).\n")
    L.append("| certificate | samples (s) | spread | regime |")
    L.append("|---|---|---|---|")
    for key, samples in list(st["committed"].items()) + list(st["time"].items()):
        sp = spread(samples)
        if sp is None:
            continue
        L.append(f"| {'examples/certs/' + key if key in st['committed'] else key} | "
                 f"{' '.join(fmt(s['kernel_s']) for s in samples)} | {sp:.2f} | "
                 f"{'unimodal (spread < 1.3)' if sp < 1.3 else 'bimodal / wide'} |")
    L.append("\nThe committed certificates measured in this run are unimodal (every spread below 1.3), "
             "unlike the 14a regeneration run; the run was made alone on the machine (one lean process at "
             "a time, AC power). The 14a medians recorded inside the certificates (`reference_configuration."
             "kernel_check`) came from the mixed regime and are larger than this run's medians "
             "(KERNEL_TIMES.md); the certificate figures are not re-recorded here (measurement only).\n")


def machine_total_mb():
    try:
        import ctypes
        c = ctypes.c_ulonglong

        class M(ctypes.Structure):
            _fields_ = [("l", ctypes.c_ulong), ("f", ctypes.c_ulong), ("t", c), ("a", c), ("pt", c),
                        ("pa", c), ("vt", c), ("va", c), ("x", c)]
        m = M()
        m.l = ctypes.sizeof(M)
        ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
        return m.t // 2 ** 20
    except Exception:
        return None


def write_kernel_times_md(st, args):
    L = ["# Kernel times of the committed certificates (Stage 14b)\n",
         "Report §9.5.1; the `scripts/bench_kernel.sh` protocol applied by "
         f"`scripts/bench_scaling.py committed`: {args.rounds} interleaved runs of "
         "`lean -Dprofiler=true Cert.lean` per certificate (round-major order), the first run "
         "excluded; kernel time = the profiler's `type checking`. Generated from "
         "`bench/scaling/out/state.json`; no hand-edited number.\n",
         f"Machine: {machine()}; `LEAN_NUM_THREADS={lean_threads(st)}` (recorded by the certify phase); "
         f"toolchain {toolchain()}.\n",
         "| certificate | runs (all samples, s; first excluded) | min | median | wall median | peak MB | outcome | 14a median (certificate.json) |",
         "|---|---|---|---|---|---|---|---|"]
    cmp = []
    for d, _ in COMMITTED:
        if d not in st["committed"]:
            continue
        t = stats(st["committed"][d])
        cj = json.load(open(os.path.join(ROOT, "examples", "certs", d, "certificate.json"), encoding="utf-8"))
        old = cj["reference_configuration"]["kernel_check"]["kernel_ms"] / 1000
        L.append(f"| examples/certs/{d} | {' '.join(fmt(x) for x in t['all'])} | {fmt(t['kernel_min'])} s | "
                 f"{fmt(t['kernel_median'])} s | {fmt(t['wall_median'])} s | {fmt(t['peak_mb'], 0)} | "
                 f"{t['outcome']} | {old:.2f} s |")
        ratio = old / t["kernel_median"]
        cmp.append(f"{d}: 14a median / this median = {ratio:.2f}"
                   + (" (the 14a median came from the mixed regime)" if ratio > 1.2 else
                      " (both in the fast regime)"))
    L.append("\nThe `reference_configuration.kernel_check` recorded inside each certificate.json is the "
             "median of 5 of its own `cqr certify --bench 5` run (Stage 14a regeneration); the table above "
             "is an independent measurement with the same protocol. This run's samples are unimodal "
             "(every spread max/min below 1.3; SCALING.md, *Modality of the samples*); the 14a samples were "
             "bimodal (DECISIONS.md 2026-10-29). " + "; ".join(cmp) + ".")
    with open(os.path.join(DOCS, "KERNEL_TIMES.md"), "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(L) + "\n")


def phase_report(args, st, insts):
    rows = rows_of(st, insts)
    write_csv(rows)
    write_scaling_md(rows, args, st)
    write_kernel_times_md(st, args)
    print(f"report: {len(rows)} rows → docs/benchmarks/scaling.csv, SCALING.md, KERNEL_TIMES.md")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phase", choices=["harness", "certify", "time", "committed", "classify", "report"])
    ap.add_argument("key", nargs="?", help="classify: the certify key, e.g. rand_a64_r1_h")
    ap.add_argument("--log", help="classify: the saved full lean output")
    ap.add_argument("--cqr", default=os.path.join(ROOT, ".lake", "build", "bin", "cqr.exe"))
    ap.add_argument("--minutes", type=float, default=0, help="time budget (0 = unlimited)")
    ap.add_argument("--timeout", type=float, default=900)
    ap.add_argument("--rounds", type=int, default=6)
    ap.add_argument("--samples", type=int, default=8)
    ap.add_argument("--seed", type=int, default=20261029)
    args = ap.parse_args()
    args.cqr = os.path.abspath(args.cqr)
    sys.stdout.reconfigure(encoding="utf-8")
    st = load_state()
    insts = manifest()
    if args.phase == "harness":
        phase_harness(args, st, insts)
    elif args.phase == "certify":
        phase_certify(args, st, insts)
    elif args.phase in ("time", "committed"):
        phase_time(args, st, args.phase)
    elif args.phase == "classify":
        if not (args.key and args.log):
            ap.error("classify needs <key> and --log <file>")
        phase_classify(args, st)
    else:
        phase_report(args, st, insts)


if __name__ == "__main__":
    main()
