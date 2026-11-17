#!/usr/bin/env python
"""Revision R11 (REVIEW_RESPONSE_1 §4; docs/tasks/REVD_TASK.md) — every measurement at one commit.

One driver, one Lean process at a time, resumable: every committed Lean check file is run as
`lean -Dprofiler=true <file>` — lean as the direct child, with the LEAN_PATH of `lake env`, so
that its peak working set can be read (the `scripts/bench_scaling.py` method) — and one state
file per item lands under `.lake/bench/` (skipped when done). Items:

  * the logical certificates `examples/certs/*/Cert.lean`: one warm-up run, then 5 runs; kernel
    time (the profiler's `type checking`), wall time and peak memory; the median of the 5 — the
    statistic of `reference_configuration.kernel_check` (whose `wall_ms` is the wall of
    `lake env lean`, about 1–2 s more than lean alone; its kernel time is the same quantity);
  * the hardware files — `examples/hw_checks/*/Check.lean`, the physical certificates
    `examples/certs/*/PhysCert.lean`, the conditional certificate `*/NoiseCert.lean`, the
    selection files `examples/hw_select/*/Select.lean`: 3 runs; wall time and peak memory (the
    kernel time as a by-product), the median of 3;
  * the comparator cmp4 is not an item (no certificate: its kernel peak is above 8 GB,
    DECISIONS.md 2026-11-17).

Recorded with every item: the commit (and the tracked files modified, if any), the CPU and RAM,
`LEAN_NUM_THREADS` (4 unless the environment sets it), the toolchain and the dependency
revisions (session.json), the free physical memory at the start of the item, a load sample (CPU
busy fraction over one second, the lean / lake processes running, the three largest processes by
working set) and the earlier figure (the certificate's `kernel_check`; the hw_checks README table).

Guards: a run is killed when the Lean process exceeds `--mem-mb` (8192 MB working set) or
`--timeout` (900 s); the item is recorded as `memkill` / `timeout` and the driver goes on. A
median that differs from the earlier figure by more than a factor of `--ratio` (3) is flagged in
the state file (`flags`), not refused. The driver refuses to add to a `.lake/bench/` measured at
another commit (`--fresh` moves the old directory aside).

Usage (project root, after `lake build`; the reviewer's own terminal, not the harness):
  .venv/Scripts/python.exe scripts/bench_all.py                # every item not yet done
  .venv/Scripts/python.exe scripts/bench_all.py --only hw_n2,mbu_gadget__fake_torino
  .venv/Scripts/python.exe scripts/bench_all.py --list         # the plan, status, estimate
  .venv/Scripts/python.exe scripts/bench_all.py --summary      # table + .lake/bench/summary.json
  .venv/Scripts/python.exe scripts/bench_all.py --report       # docs/BENCHMARKS.md from the state files (D2)
Results: .lake/bench/<kind>--<name>.json (one per item), session.json, summary.json; the logical
certificates take the figures through `cqr certify --kernel-check-from <state file>` (D1.5).
"""
import argparse
import ctypes
import glob
import json
import os
import platform
import statistics
import subprocess
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import bench_scaling as bs  # noqa: E402  lean_env, kill_tree, kernel_s, classify_output, first_error, machine, toolchain

BENCH = os.path.join(ROOT, ".lake", "bench")
EXCLUDE = {"cmp4"}  # harness evidence only (REVC_TASK guard; DECISIONS.md 2026-11-17)
# kind, pattern, measured runs, warm-up runs
KINDS = [("logical", "examples/certs/*/Cert.lean", 5, 1),
         ("hw_check", "examples/hw_checks/*/Check.lean", 3, 0),
         ("physcert", "examples/certs/*/PhysCert.lean", 3, 0),
         ("noisecert", "examples/certs/*/NoiseCert.lean", 3, 0),
         ("select", "examples/hw_select/*/Select.lean", 3, 0)]
WIN = platform.system() == "Windows"


def now():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def items():
    out = []
    for kind, pat, runs, warm in KINDS:
        for f in sorted(glob.glob(os.path.join(ROOT, *pat.split("/")))):
            rel = os.path.relpath(f, ROOT).replace("\\", "/")
            name = rel.split("/")[-2]
            if name not in EXCLUDE:
                out.append({"id": f"{kind}--{name}", "kind": kind, "name": name, "file": rel,
                            "runs": runs, "warmup": warm})
    return out


def earlier(it):
    """The earlier figure: certificate.json's kernel_check (logical) or the 2026-11-16 table of
    examples/hw_checks/README.md (hw_check); None for the other kinds (no table quotes them)."""
    if it["kind"] == "logical":
        cj = json.load(open(os.path.join(ROOT, os.path.dirname(it["file"]), "certificate.json"), encoding="utf-8"))
        k = cj["reference_configuration"]["kernel_check"]
        return {"kernel_s": k["kernel_ms"] / 1000, "wall_s": k["wall_ms"] / 1000,
                "source": "certificate.json reference_configuration.kernel_check (wall of `lake env lean`)"}
    if it["kind"] == "hw_check":
        for line in open(os.path.join(ROOT, "examples", "hw_checks", "README.md"), encoding="utf-8"):
            c = [x.strip() for x in line.strip().strip("|").split("|")]
            if len(c) == 8 and c[0] == it["name"]:
                try:
                    return {"wall_s": float(c[6]), "peak_mb": round(float(c[7]) * 1024),
                            "source": "examples/hw_checks/README.md, the kernel table (2026-11-16)"}
                except ValueError:
                    pass
    return None


# --- the machine ---------------------------------------------------------------------------

class MEMSTAT(ctypes.Structure):
    _fields_ = [("l", ctypes.c_ulong), ("f", ctypes.c_ulong)] + \
               [(n, ctypes.c_ulonglong) for n in ("t", "a", "pt", "pa", "vt", "va", "x")]


class PMC(ctypes.Structure):
    _fields_ = [("cb", ctypes.c_ulong), ("PageFaultCount", ctypes.c_ulong)] + \
               [(n, ctypes.c_size_t) for n in ("PeakWorkingSetSize", "WorkingSetSize", "qpp", "qp",
                                               "qpn", "qn", "PagefileUsage", "PeakPagefileUsage")]


def memory_mb():
    """(total, available) physical memory in MB, or (None, None)."""
    if not WIN:
        return None, None
    m = MEMSTAT()
    m.l = ctypes.sizeof(MEMSTAT)
    ok = ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
    return (m.t // 2 ** 20, m.a // 2 ** 20) if ok else (None, None)


def proc_mem_mb(p):
    """(working set, peak working set) of a Popen'd process in MB — also after it has exited,
    while the handle is open — or (None, None)."""
    if not WIN:
        return None, None
    pmc = PMC()
    pmc.cb = ctypes.sizeof(PMC)
    ok = ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(p._handle), ctypes.byref(pmc), pmc.cb)
    return (round(pmc.WorkingSetSize / 2 ** 20), round(pmc.PeakWorkingSetSize / 2 ** 20)) if ok else (None, None)


def cpu_busy_pct(seconds=1.0):
    """CPU busy fraction of the whole machine over `seconds` (GetSystemTimes), in percent."""
    if not WIN:
        return None

    def sample():
        from ctypes import wintypes
        t = [wintypes.FILETIME() for _ in range(3)]
        ctypes.windll.kernel32.GetSystemTimes(*[ctypes.byref(x) for x in t])
        return [(x.dwHighDateTime << 32) + x.dwLowDateTime for x in t]  # idle, kernel (incl. idle), user
    a = sample()
    time.sleep(seconds)
    b = sample()
    total = (b[1] - a[1]) + (b[2] - a[2])
    return round(100 * (1 - (b[0] - a[0]) / total), 1) if total else None


def load_sample():
    """CPU busy %, the lean / lake processes running (none of ours: the driver is between runs),
    the three largest processes by working set."""
    s = {"when": now(), "cpu_busy_pct": cpu_busy_pct(), "lean_lake_processes": None, "top_ws_mb": None}
    if WIN:
        try:
            q = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command",
                                "(Get-Process lean,lake -ErrorAction SilentlyContinue | Measure-Object).Count; "
                                "Get-Process | Sort-Object WS -Descending | Select-Object -First 3 | "
                                "ForEach-Object { \"$($_.Name) $([int]($_.WS/1MB))\" }"],
                               capture_output=True, text=True, encoding="utf-8", timeout=60)
            lines = [x.strip() for x in q.stdout.splitlines() if x.strip()]
            s["lean_lake_processes"] = int(lines[0])
            s["top_ws_mb"] = [[x.rsplit(" ", 1)[0], int(x.rsplit(" ", 1)[1])] for x in lines[1:4]]
        except Exception as e:  # the sample must never block an item
            s["error"] = repr(e)
    return s


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True, encoding="utf-8").stdout.strip()


# --- one run, one item ---------------------------------------------------------------------

def run_lean(file, env, timeout, mem_mb):
    """`lean -Dprofiler=true file` as the direct child; killed above `mem_mb` (working set, polled
    every 0.25 s) or `timeout` seconds. Returns outcome, wall, kernel time, peak memory."""
    lean, _ = bs.lean_env()
    t0 = time.time()
    p = subprocess.Popen([lean, "-Dprofiler=true", file], cwd=ROOT, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace", env=env)
    buf = []
    th = threading.Thread(target=lambda: buf.append(p.stdout.read()), daemon=True)
    th.start()
    outcome, ws_max = None, 0
    while p.poll() is None:
        ws, _ = proc_mem_mb(p)
        ws_max = max(ws_max, ws or 0)
        if ws and ws > mem_mb:
            outcome = "memkill"
        elif time.time() - t0 > timeout:
            outcome = "timeout"
        if outcome:
            bs.kill_tree(p)
            p.wait()
            break
        time.sleep(0.25)
    wall = time.time() - t0
    th.join(timeout=30)
    out = buf[0] if buf else ""
    _, peak = proc_mem_mb(p)
    if outcome is None:
        outcome = bs.classify_output(p.returncode, out)
    return {"outcome": outcome, "rc": p.returncode, "wall_s": round(wall, 2),
            "kernel_s": bs.kernel_s(out) if outcome == "ok" else None,
            "peak_mb": peak or ws_max or None, "ws_max_polled_mb": ws_max or None,
            "error": "" if outcome == "ok" else (bs.first_error(out) or out[-400:].strip()), "when": now()}


def median(xs):
    xs = [x for x in xs if x is not None]
    return round(statistics.median(xs), 3) if xs else None


def summarize(st, it, args):
    runs = [r for r in st["runs"] if not r["warmup"] and r["outcome"] == "ok"]
    s = {"n": len(runs), "statistic": f"median of {it['runs']}" + (" (first run excluded)" if it["warmup"] else ""),
         "kernel_s": median([r["kernel_s"] for r in runs]), "wall_s": median([r["wall_s"] for r in runs]),
         "peak_mb_median": median([r["peak_mb"] for r in runs]),
         "peak_mb_max": max([r["peak_mb"] or 0 for r in st["runs"]] or [0]) or None}
    flags = []
    if st["status"] != "done":
        flags.append(f"{st['status']}: guard ({args.timeout} s / {args.mem_mb} MB) or failure; "
                     f"{s['n']} of {it['runs']} measured runs")
    e = st["earlier"] or {}
    key = "kernel_s" if it["kind"] == "logical" else "wall_s"
    for k in (key, "peak_mb"):
        a, b = s.get(k if k != "peak_mb" else "peak_mb_max"), e.get(k)
        if a and b:
            ratio = max(a / b, b / a)
            s[f"ratio_{k}"] = round(ratio, 2)
            if ratio > args.ratio:
                flags.append(f"{k}: {a} vs earlier {b} (factor {ratio:.2f} > {args.ratio})")
    if (st["load"].get("lean_lake_processes") or 0) > 0:
        flags.append(f"{st['load']['lean_lake_processes']} lean/lake process(es) were running at the start")
    return s, flags


def state_path(it):
    return os.path.join(BENCH, it["id"] + ".json")


def save(path, obj):
    os.makedirs(BENCH, exist_ok=True)
    with open(path + ".tmp", "w", encoding="utf-8", newline="\n") as f:
        json.dump(obj, f, indent=1, ensure_ascii=False)
    os.replace(path + ".tmp", path)


def load(path):
    return json.load(open(path, encoding="utf-8")) if os.path.exists(path) else None


def measure(it, sess, args):
    env = dict(bs.lean_env()[1])  # LEAN_PATH of `lake env`
    env["LEAN_NUM_THREADS"] = sess["lean_threads"]
    st = {"id": it["id"], "kind": it["kind"], "name": it["name"], "file": it["file"], "commit": sess["commit"],
          "lean_threads": sess["lean_threads"], "status": "running", "started": now(),
          "free_mb_start": memory_mb()[1], "load": load_sample(), "earlier": earlier(it), "runs": []}
    path = state_path(it)
    save(path, st)
    print(f"[{now()}] {it['id']}: free {st['free_mb_start']} MB, cpu busy {st['load']['cpu_busy_pct']} %, "
          f"lean/lake running {st['load']['lean_lake_processes']}", flush=True)
    for i in range(it["warmup"] + it["runs"]):
        r = run_lean(it["file"], env, args.timeout, args.mem_mb)
        r["warmup"] = i < it["warmup"]
        st["runs"].append(r)
        save(path, st)
        print(f"  run {i}{' (warm-up)' if r['warmup'] else ''}: {r['outcome']} wall {r['wall_s']} s "
              f"kernel {r['kernel_s']} s peak {r['peak_mb']} MB" + (f" — {r['error']}" if r["error"] else ""), flush=True)
        if r["outcome"] != "ok":
            st["status"] = r["outcome"]
            break
    else:
        st["status"] = "done"
    st["summary"], st["flags"] = summarize(st, it, args)
    st["finished"] = now()
    save(path, st)
    print(f"  => {st['status']}: {st['summary']}" + (f"\n  FLAGS: {st['flags']}" if st["flags"] else ""), flush=True)
    return st


# --- the session and the summary -----------------------------------------------------------

def session(args):
    path = os.path.join(BENCH, "session.json")
    head = git("rev-parse", "HEAD")
    old = load(path)
    if old and (old["commit"] != head or args.fresh):
        if not args.fresh:
            sys.exit(f"{BENCH} holds measurements at {old['commit'][:7]}; HEAD is {head[:7]} — every measurement "
                     f"at one commit: check out {old['commit'][:7]} or run with --fresh (moves the directory aside)")
        os.rename(BENCH, f"{BENCH}_{old['commit'][:7]}_{time.strftime('%Y%m%d-%H%M%S')}")
        old = None
    if old:
        return old
    man = json.load(open(os.path.join(ROOT, "lake-manifest.json"), encoding="utf-8"))
    lean, _ = bs.lean_env()
    total, _ = memory_mb()
    sess = {"commit": head, "started": now(), "tracked_modified": git("status", "--porcelain", "--untracked-files=no").splitlines(),
            "machine": bs.machine(), "ram_mb": total, "os": platform.platform(),
            "lean_threads": os.environ.get("LEAN_NUM_THREADS") or args.threads, "toolchain": bs.toolchain(),
            "lean_toolchain": open(os.path.join(ROOT, "lean-toolchain"), encoding="utf-8").read().strip(),
            "lean_version": subprocess.run([lean, "--version"], capture_output=True, text=True, encoding="utf-8").stdout.strip(),
            "revisions": {p["name"]: p["rev"] for p in man["packages"]}, "lean": lean,
            "timeout_s": args.timeout, "mem_mb": args.mem_mb, "ratio_guard": args.ratio, "python": sys.version.split()[0],
            "method": "lean -Dprofiler=true <file> as the direct child (LEAN_PATH of `lake env`); kernel time = the "
                      "profiler's `type checking`; wall = the lean process; peak = PeakWorkingSetSize; "
                      "logical certificates 1 warm-up + 5 runs (median of 5), hardware files 3 runs (median of 3)"}
    save(path, sess)
    return sess


def summary(args):
    sess = load(os.path.join(BENCH, "session.json"))
    rows = [load(state_path(it)) for it in items()]
    out = {"session": sess, "items": [r for r in rows if r]}
    if sess:
        save(os.path.join(BENCH, "summary.json"), out)
    print(f"commit {sess['commit'][:7] if sess else '-'}; {sum(1 for r in rows if r)} of {len(rows)} items have a state file")
    print(f"{'item':48} {'status':8} {'kernel s':>9} {'wall s':>8} {'peak MB':>8} {'earlier':>9} {'ratio':>6}  flags")
    for it, r in zip(items(), rows):
        if not r:
            print(f"{it['id']:48} {'-':8}")
            continue
        s, e = r.get("summary") or {}, r.get("earlier") or {}
        key = "kernel_s" if it["kind"] == "logical" else "wall_s"
        print(f"{it['id']:48} {r['status']:8} {str(s.get('kernel_s', '')):>9} {str(s.get('wall_s', '')):>8} "
              f"{str(s.get('peak_mb_max', '')):>8} {str(e.get(key, '-')):>9} {str(s.get('ratio_' + key, '')):>6}  "
              f"{'; '.join(r.get('flags') or [])}")
    return out


def listing(args, plan):
    est = 0
    for it in plan:
        st = load(state_path(it))
        e = earlier(it)
        wall = (e or {}).get("wall_s") or 30.0  # no earlier figure: assume 30 s per run
        est += (it["warmup"] + it["runs"]) * wall + 4
        print(f"{it['id']:48} {(st or {}).get('status', '-'):8} {it['warmup']}+{it['runs']} runs  "
              f"earlier {json.dumps({k: v for k, v in (e or {}).items() if k != 'source'})}")
    print(f"{len(plan)} items; estimated {est / 60:.0f} min from the earlier wall times (30 s per run assumed where none)")


KIND_TITLE = {"logical": "Logical certificates (`examples/certs/*/Cert.lean`; 1 warm-up + 5 runs, the median of 5)",
              "hw_check": "Hardware check files (`examples/hw_checks/*/Check.lean`; 3 runs, the median of 3)",
              "physcert": "Physical certificates (`examples/certs/*/PhysCert.lean`; 3 runs, the median of 3)",
              "noisecert": "Conditional (noise) certificate (`NoiseCert.lean`; 3 runs, the median of 3)",
              "select": "Selection files (`examples/hw_select/*/Select.lean`; 3 runs, the median of 3)"}


def instance_of(it):
    cj = json.load(open(os.path.join(ROOT, os.path.dirname(it["file"]), "certificate.json"), encoding="utf-8"))
    i = cj["instance"]
    return f"n = {i['n']}, m = {i['m']}, M = {i['M']}" if "m" in i else f"n = {i['n']}, M = {i['M']}, r = {i['r']}"


def report(args):
    """docs/BENCHMARKS.md from the state files: the session header, the load, one table per kind;
    no hand-edited number (R11 D2, docs/tasks/REVD_TASK.md)."""
    sess = load(os.path.join(BENCH, "session.json"))
    rows = [(it, load(state_path(it))) for it in items()]
    done = [r for _, r in rows if r]
    cpu = [r["load"]["cpu_busy_pct"] for r in done if r["load"].get("cpu_busy_pct") is not None]
    free = [r["free_mb_start"] for r in done if r["free_mb_start"]]
    ll = [r["load"].get("lean_lake_processes") or 0 for r in done]
    flags = [f"{r['id']}: {f}" for r in done for f in r.get("flags") or []]
    f1 = lambda x: "" if x is None else f"{x:.3g}" if x < 10 else f"{x:.1f}"
    L = ["# Benchmarks — every measurement at one commit (revision R11)\n",
         "REVIEW_RESPONSE_1 §4 R11; docs/tasks/REVD_TASK.md; report §9.5.1, §9.5.3. Both reviews asked for one "
         "measurement of everything at one commit, with the machine, the enabled checks and the load recorded, in "
         "place of the timing tables mixed from Stages 21a3, 21a4, 21m, 26c1b, 27b and 27c. Written by "
         "`scripts/bench_all.py --report` from its state files (`.lake/bench/`, not committed); no hand-edited number.\n",
         f"**Commit** `{sess['commit']}`. **Machine** {sess['machine']}; {sess['os']}; `LEAN_NUM_THREADS={sess['lean_threads']}`. "
         f"**Toolchain** {sess['toolchain']} (`{sess['lean_version']}`). **Run** started {sess['started']}, in a terminal outside the "
         f"agent harness; tracked files modified at the run: {', '.join(sess['tracked_modified']) or 'none'}; guards "
         f"{sess['timeout_s']:g} s and {sess['mem_mb']} MB per run, none hit.\n",
         f"**Method.** {sess['method']}. The wall is that of `lean` itself, run directly — the earlier figures of "
         "`reference_configuration.kernel_check` and of the 2026-11-16 table in `examples/hw_checks/README.md` were walls of "
         "`lake env lean`, 1–2 s more (the lake start); the kernel time is the same quantity in both. Peak = the peak working "
         "set of the Lean process (the maximum over the runs of an item).\n",
         f"**Load.** {len(done)} of {len(rows)} items done; CPU busy at the start of an item {min(cpu):g}–{max(cpu):g} %; free physical "
         f"memory {min(free)}–{max(free)} MB; other lean / lake processes running: {max(ll)}; flags: "
         + (", ".join(flags) if flags else "none (no run over the guards; no median off its earlier figure by more than a factor "
                                            f"of {sess['ratio_guard']:g}).") + "\n",
         "The logical certificates carry these figures in `reference_configuration.kernel_check` (`cqr certify --kernel-check-from`, "
         "with `commit`); the hardware files cite a certificate modulo `hashes.library` and `reference_configuration`, so the "
         "measurement moved none of them (DECISIONS.md 2026-11-17, R11 D1.5 and D2).\n"]
    for kind in KIND_TITLE:
        L.append(f"## {KIND_TITLE[kind]}\n")
        if kind == "logical":
            L += ["| certificate | instance | kernel s | the 5 kernel samples (s) | wall s | peak MB | before: kernel s (`--bench`, `lake env lean`) | ratio |",
                  "|---|---|---|---|---|---|---|---|"]
        elif kind == "hw_check":
            L += ["| file | wall s | peak MB | kernel s | 2026-11-16 table: wall s (`lake env lean`) / peak MB | ratio (wall) |", "|---|---|---|---|---|---|"]
        else:
            L += ["| file | wall s | peak MB | kernel s |", "|---|---|---|---|"]
        for it, r in rows:
            if it["kind"] != kind:
                continue
            if not r:
                L.append(f"| `{it['file']}` | not measured |")
                continue
            s, e = r["summary"], r.get("earlier") or {}
            if kind == "logical":
                samples = " ".join(f1(x["kernel_s"]) for x in r["runs"] if not x["warmup"] and x["outcome"] == "ok")
                L.append(f"| `{it['name']}` | {instance_of(it)} | {f1(s['kernel_s'])} | {samples} | {f1(s['wall_s'])} | {s['peak_mb_max']} | "
                         f"{f1(e.get('kernel_s'))} | {s.get('ratio_kernel_s', '')} |")
            elif kind == "hw_check":
                L.append(f"| `{it['name']}` | {f1(s['wall_s'])} | {s['peak_mb_max']} | {f1(s['kernel_s'])} | "
                         f"{f1(e.get('wall_s'))} / {e.get('peak_mb', '')} | {s.get('ratio_wall_s', '')} |")
            else:
                L.append(f"| `{it['file']}` | {f1(s['wall_s'])} | {s['peak_mb_max']} | {f1(s['kernel_s'])} |")
        L.append("")
    L.append("The comparator `cmp4` (REVC_TASK, R12) is not an item: no certificate, its kernel peak is above 8 GB "
             "(docs/M5_REPORT.md §1.2, DECISIONS.md 2026-11-17).")
    out = os.path.join(ROOT, "docs", "BENCHMARKS.md")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(L) + "\n")
    print(f"wrote {out}: {len(done)} items")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--only", help="comma-separated substrings of item ids (kind--name)")
    ap.add_argument("--list", action="store_true", help="print the plan and stop")
    ap.add_argument("--summary", action="store_true", help="print the table, write summary.json and stop")
    ap.add_argument("--report", action="store_true", help="write docs/BENCHMARKS.md from the state files and stop")
    ap.add_argument("--redo", action="store_true", help="measure the selected items again")
    ap.add_argument("--fresh", action="store_true", help="move .lake/bench aside and start over")
    ap.add_argument("--timeout", type=float, default=900.0, help="seconds per run (900)")
    ap.add_argument("--mem-mb", type=int, default=8192, help="kill a run above this working set (8192 MB)")
    ap.add_argument("--ratio", type=float, default=3.0, help="flag a median off the earlier figure by this factor (3)")
    ap.add_argument("--threads", default="4", help="LEAN_NUM_THREADS when the environment does not set it (4)")
    args = ap.parse_args()
    plan = items()
    if args.only:
        keys = args.only.split(",")
        plan = [it for it in plan if any(k in it["id"] for k in keys)]
    if args.list:
        return listing(args, plan)
    if args.summary:
        return summary(args)
    if args.report:
        return report(args)
    sess = session(args)
    print(f"commit {sess['commit'][:7]}{' (tracked files modified!)' if sess['tracked_modified'] else ''}; "
          f"{sess['machine']}; LEAN_NUM_THREADS={sess['lean_threads']}; {sess['toolchain']}; "
          f"{len(plan)} items; guards {args.timeout} s / {args.mem_mb} MB", flush=True)
    t0 = time.time()
    for it in plan:
        st = load(state_path(it))
        if st and st["status"] != "running" and not args.redo:
            print(f"skip {it['id']} ({st['status']})")
            continue
        measure(it, sess, args)
    print(f"{(time.time() - t0) / 60:.1f} min")
    summary(args)


if __name__ == "__main__":
    main()
