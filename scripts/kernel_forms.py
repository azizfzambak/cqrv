"""Stage 18a (docs/tasks/STAGE18_TASK.md A0, A2; report §9.5.1) — the kernel-evaluation probe.

Measurement only: no change to the Lean library. Every raw result goes to the git-ignored
`bench/forms/out/` (`state.json`, one `cqr certify` output directory per probe, the Lean logs) and
`docs/benchmarks/KERNEL_FORMS.md` is generated from it (the hand-written reading after the marker
`<!-- reading -->` at the end of that file is preserved). Exactly one Lean process runs at a time;
every Lean run has a timeout (default 900 s) and a **memory kill**: a `lean` process whose working
set exceeds --mem-kill-mb (default 8000; the laptop has 16 GB and thrashed at 10.4 GB on the first
run, 2026-10-31) is killed, the outcome recorded as `mem-kill` with the partial output (`tasklist`
polled every second on Windows, `ps` elsewhere); the peak working set is recorded
(`scripts/bench_scaling.py`: `lean_env`, `kernel_s`, `peak_mb`, `first_error`).

Probes (`--only` selects a subset; default natm,committed,rand-small)
  rand       rand_a64 (bench/scaling/rand_a64.cqr, n = 12, 64 AND nodes; the Stage 14b failure at
             1953 emitted instructions) at r = 1, 2, 3: `cqr certify … --solutions 1853
             --iterations r --count-limit 0` (the hypothesis form, as 14b's `_h` items; cqr's own
             kernel check is one `lake env lean -Dprofiler=true Cert.lean`), then one profiled run
             of the written Cert.lean **per declaration**: a copy with `#print axioms <name>` after
             every declaration, `lean -DElab.async=false -Dprofiler=true -Dprofiler.threshold=T`,
             so that the profiler's unpositioned `… took` lines fall between the markers of the
             declaration they belong to (asynchronous elaboration off, so the order is the
             declaration order). Memory guard: r = 3 runs only if r = 2 finished within the timeout
             with a peak below --mem-guard-mb (default 9216). **Not in the default set since the
             first run (reviewer decision 2026-10-31)**: r = 1 timed out at 900 s in `cqr certify`
             and its profiled run was stopped at 10.4 GB; r = 2 and r = 3 are not run. The report
             prints those records (`REVIEWER_RECORD`).
  rand-small the attribution probe that fits in memory (reviewer decision 2026-10-31): the largest
             Stage 14b instances that certified within 900 s, in the hypothesis form, per
             declaration under the memory kill — carry_7 (612 instructions), carry_8 (706; 14b
             peak 8167 MB under the old scheduler) and carry_5 at r = 2 (about 830, between carry_8
             and the 1123 of rand_a32, which timed out in 14b); the sequence stops at the first
             timeout or memory kill (the larger ones would not fit either).
  natm       A0: bench/forms/nat_m.cqr (`(x : Vec Bool 4) (k : Nat 3)`) and three variants
             (nat_ret.cqr: a `Nat 3`-returning program; nat_wide.cqr: `k : Nat 65536`, 16 bits;
             for_idx.cqr: a `for` index read as a value). The extractor classifies a two-parameter
             program as a decision problem, so `cqr certify` cannot certify it (the run is recorded:
             the Grover hint, exit 1); the front-end block a certificate would carry (`net`, `prog`,
             `prog_scoped`, `net_ok`, `front_end`) is written by `scripts/CertifyTool.lean
             front-end` and profiled per declaration as above, next to the same block of
             examples/grover_pred_037.cqr (Vec-only) as the baseline.
  committed  the four committed certificates: the full Cert.lean per declaration, and `grade_eq`
             alone / `gradeExt_eq` alone with the certificate's metric (the Stage 17b scratch-file
             method: `net`, `emitted` and that one theorem; cumulative `type checking` of
             `lean -Dprofiler=true`), the minimum of --repeat runs (default 2; the machine has two
             speed regimes, DECISIONS.md 2026-10-28). "Before A1" are the Stage 17b figures
             (DECISIONS.md 2026-10-31, 17b decision 9), quoted as such.

Usage (after `lake build`, from the repository root, LEAN_NUM_THREADS=4):
    scripts/kernel_forms.sh [--only rand,natm,committed] [--timeout 900] [--r-max 3]
                            [--mem-guard-mb 9216] [--repeat 2] [--threshold-ms 1000] [--report-only]
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
from bench_scaling import (emitted_count, first_error, kernel_s, lean_env, machine,  # noqa: E402
                           toolchain, loglog_slope, kill_tree, peak_mb, classify_output)
import platform  # noqa: E402
import tempfile  # noqa: E402

OUT = os.path.join(ROOT, "bench", "forms", "out")
STATE = os.path.join(OUT, "state.json")
MD = os.path.join(ROOT, "docs", "benchmarks", "KERNEL_FORMS.md")
READING_MARK = "<!-- reading -->"
CERTS = ["grover_pred_037", "simple_alu_x0_1", "grover_pred_037_few", "grover_pred_037_coh"]
# Stage 17b (DECISIONS.md 2026-10-31, decision 9): grade_eq alone / gradeExt_eq alone, before A1
BEFORE = {"grover_pred_037": (7.04, 9.26), "simple_alu_x0_1": (5.58, 7.03),
          "grover_pred_037_few": (5.98, 7.95), "grover_pred_037_coh": (13.5, 17.5)}
RE_FRONT_END = re.compile(r"/-- The typed term of the request.*?#print axioms front_end\n\n", re.S)
RE_DECL = re.compile(r"^(?:theorem|def) ([A-Za-z_][A-Za-z0-9_']*)")
RE_TOOK = re.compile(r"^(.*?) took ([0-9.]+)(ms|s|μs)\s*$")
RE_MARK = re.compile(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)")
UNIT = {"ms": 1e-3, "s": 1.0, "μs": 1e-6}


def cqr():
    p = os.path.join(ROOT, ".lake", "build", "bin", "cqr")
    if os.path.exists(p + ".exe"):
        p += ".exe"
    if not os.path.exists(p):
        raise SystemExit(f"{p} not found (run lake build first)")
    return p


def read(path):
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def load_state():
    if os.path.exists(STATE):
        return json.load(open(STATE, encoding="utf-8"))
    return {"rand": {}, "natm": {}, "committed": {}, "meta": {}}


def save_state(st):
    os.makedirs(OUT, exist_ok=True)
    write(STATE, json.dumps(st, indent=1, ensure_ascii=False))


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def lean_processes():
    """[(pid, working set MB)] of every running `lean` process (Windows `tasklist`, else `ps`)."""
    out = []
    try:
        if platform.system() == "Windows":
            q = subprocess.run(["tasklist", "/FI", "IMAGENAME eq lean.exe", "/FO", "CSV", "/NH"],
                               capture_output=True, text=True, encoding="utf-8", errors="replace",
                               timeout=30)
            for ln in q.stdout.splitlines():
                cells = [c.strip('"') for c in ln.strip().split('","')]
                if len(cells) >= 5 and cells[0].lower() == "lean.exe":
                    kb = int(re.sub(r"[^0-9]", "", cells[4]) or 0)
                    out.append((int(cells[1]), kb // 1024))
        else:
            q = subprocess.run(["ps", "-eo", "pid,rss,comm"], capture_output=True, text=True,
                               encoding="utf-8", errors="replace", timeout=30)
            for ln in q.stdout.splitlines()[1:]:
                parts = ln.split()
                if len(parts) >= 3 and parts[2].endswith("lean"):
                    out.append((int(parts[0]), int(parts[1]) // 1024))
    except Exception:
        pass
    return out


def run_guarded(cmd, timeout, mem_kill_mb, env=None):
    """Run `cmd` with the timeout and the memory kill: every second the working sets of all `lean`
    processes are read (the command's own lean, or cqr's lean child); above `mem_kill_mb` the
    command's process tree and that lean are killed. Returns (outcome, rc, output, wall s,
    peak MB of the direct child, max lean MB seen): outcome 'ok' / 'timeout' / 'mem-kill' / 'oom' /
    'error' (`bench_scaling.classify_output`). The output goes through a temporary file so that
    the partial output of a killed run is kept."""
    t0 = time.time()
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8", errors="replace") as tmp:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=tmp, stderr=subprocess.STDOUT, env=env)
        outcome, max_lean = None, 0
        while True:
            rc = p.poll()
            if rc is not None:
                break
            if time.time() - t0 > timeout:
                kill_tree(p)
                outcome = "timeout"
                break
            for pid, mb in lean_processes():
                max_lean = max(max_lean, mb)
                if mb > mem_kill_mb:
                    log(f"  memory kill: lean pid {pid} at {mb} MB > {mem_kill_mb} MB")
                    kill_tree(p)
                    log("  memory kill: process tree killed")
                    if platform.system() == "Windows":
                        subprocess.run(["taskkill", "/F", "/PID", str(pid)], capture_output=True)
                    else:
                        subprocess.run(["kill", "-9", str(pid)], capture_output=True)
                    log("  memory kill: lean killed")
                    outcome = "mem-kill"
                    break
            if outcome:
                break
            time.sleep(1.0)
        p.wait()
        wall = time.time() - t0
        if outcome:
            log(f"  {outcome}: process exited (rc {p.returncode}), wall {wall:.1f} s")
        tmp.seek(0)
        out = tmp.read()
    if outcome is None:
        outcome = classify_output(p.returncode, out)
    return outcome, p.returncode, out, wall, peak_mb(p), max_lean


# --- the per-declaration profile ------------------------------------------------------------

def with_markers(text):
    """A copy of a Lean file with `#print axioms <name>` after every top-level `theorem` / `def`
    (before the next top-level item), so the profiler lines between two markers belong to the
    declaration the second marker names."""
    lines = text.replace("\r\n", "\n").split("\n")
    out, pending = [], None
    for ln in lines:
        top = (ln.startswith(("theorem ", "def ", "/--", "/-!", "#print", "end ", "namespace ",
                              "open ", "import ", "set_option")) or ln == "")
        m = RE_DECL.match(ln)
        if pending and top and not ln.startswith(" ") and ln != "" and not ln.startswith("#print axioms " + pending):
            out.append(f"#print axioms {pending}")
            pending = None
        if m:
            pending = m.group(1)
        out.append(ln)
    if pending:
        out.append(f"#print axioms {pending}")
    # drop duplicate consecutive markers (a file may already print the axioms of a theorem)
    dedup = []
    for ln in out:
        if ln.startswith("#print axioms ") and ln in dedup[-3:]:
            continue
        dedup.append(ln)
    return "\n".join(dedup) + ("\n" if not text.endswith("\n") else "")


def per_declaration(output):
    """Attribute the profiler's `… took` lines to declarations by the `#print axioms` markers:
    {name: {category: seconds}} in file order, plus the lines before the first marker under
    '(imports)'."""
    decls, order, cur = {}, [], {}
    for ln in output.replace("\r", "").split("\n"):
        ln = ln.strip()
        m = RE_TOOK.match(ln)
        if m and not ln.startswith("cumulative"):
            cat = m.group(1).split(" of ")[0]
            cur[cat] = cur.get(cat, 0.0) + float(m.group(2)) * UNIT[m.group(3)]
            continue
        m = RE_MARK.match(ln)
        if m:
            name = m.group(1).split(".")[-1]
            if name in decls:  # a second marker for the same name: keep the first attribution
                for k, v in cur.items():
                    decls[name][k] = decls[name].get(k, 0.0) + v
            else:
                decls[name] = cur
                order.append(name)
            cur = {}
    if cur:
        decls["(after the last marker)"] = cur
        order.append("(after the last marker)")
    return order, decls


MEM_KILL_MB = 8000  # set from --mem-kill-mb in main()


def profile(lean_file, timeout, threshold_ms, label):
    """One Lean run of `lean_file` with markers: per-declaration times, the cumulative kernel
    time, wall, peak MB, outcome. Writes `<file>.marked.lean` and `<file>.log` next to it."""
    marked = lean_file[:-5] + ".marked.lean"
    write(marked, with_markers(read(lean_file)))
    lean, env = lean_env()
    cmd = [lean, "-DElab.async=false", "-Dprofiler=true", f"-Dprofiler.threshold={threshold_ms}",
           marked]
    log(f"profile {label}: {os.path.relpath(marked, ROOT)}")
    outcome, rc, out, wall, mem, max_lean = run_guarded(cmd, timeout, MEM_KILL_MB, env)
    write(lean_file[:-5] + ".log", out)
    order, decls = per_declaration(out)
    rec = {"outcome": "ok" if outcome == "ok" else outcome, "rc": rc, "kernel_s": kernel_s(out),
           "wall_s": round(wall, 2), "peak_mb": mem or max_lean or None, "max_lean_mb": max_lean,
           "error": first_error(out),
           "order": order, "decls": {k: {c: round(v, 3) for c, v in d.items()} for k, d in decls.items()},
           "when": time.strftime("%Y-%m-%d %H:%M:%S")}
    log(f"  -> {rec['outcome']}, kernel {rec['kernel_s']} s, wall {rec['wall_s']} s, "
        f"peak {rec['peak_mb']} MB" + (f": {rec['error'][:160]}" if rec["error"] else ""))
    return rec


# --- probes ----------------------------------------------------------------------------------

def certify(args_list, out_dir, timeout):
    cmd = [cqr(), "certify", *args_list, "--out", os.path.relpath(out_dir, ROOT)]
    log("certify: " + " ".join(cmd[1:]))
    outcome, rc, out, wall, mem, max_lean = run_guarded(cmd, timeout, MEM_KILL_MB)
    write(os.path.join(out_dir, "certify.log"), out)
    last = [ln for ln in out.replace("\r", "").split("\n") if ln.strip()]
    rec = {"outcome": outcome, "rc": rc, "wall_s": round(wall, 2), "peak_mb_cqr": mem,
           "max_lean_mb": max_lean, "last_line": last[-1] if last else "", "error": first_error(out),
           "when": time.strftime("%Y-%m-%d %H:%M:%S")}
    cert = os.path.join(out_dir, "Cert.lean")
    if os.path.exists(cert):
        rec["instructions"] = emitted_count(read(cert))
    log(f"  -> {outcome} (rc {rc}), wall {rec['wall_s']} s, lean up to {max_lean} MB; "
        f"{rec['last_line'][:140]}")
    return rec


# the first run (2026-10-31, before the memory kill existed): recorded from the user's terminal
REVIEWER_RECORD = {
    "r1": "certify timeout 900 s (900.22 s, rc 1, 23:00:06; certify.log empty); the profiled run was "
          "stopped by the reviewer at 10.4 GB peak with 0.5 GB RAM free, machine thrashing; nothing "
          "saved (reviewer decision 2026-10-31)",
    "r2": "not run (reviewer decision 2026-10-31, memory)",
    "r3": "not run (reviewer decision 2026-10-31, memory)"}

# the attribution probe that fits in memory (reviewer decision 2026-10-31): hypothesis form
SMALL = [("carry_7_r1", os.path.join("bench", "scaling", "carry_7.cqr"), 8128, 1),
         ("carry_8_r1", os.path.join("bench", "scaling", "carry_8.cqr"), 32640, 1),
         ("carry_5_r2", os.path.join("bench", "scaling", "carry_5.cqr"), 496, 2)]


def probe_small(args, st):
    st.setdefault("small", {})
    for key, src, M, r in SMALL:
        if key in st["small"] and st["small"][key].get("profile") and not args.redo:
            log(f"{key}: done, skipped")
            continue
        out_dir = os.path.join(OUT, key)
        rec = {"source": src, "M": M, "r": r,
               "certify": certify([src, "--solutions", str(M), "--iterations", str(r),
                                   "--count-limit", "0"], out_dir, args.timeout)}
        cert = os.path.join(out_dir, "Cert.lean")
        if os.path.exists(cert):
            rec["instructions"] = rec["certify"].get("instructions")
            rec["profile"] = profile(cert, args.timeout, args.threshold_ms, key)
        st["small"][key] = rec
        save_state(st)
        bad = {rec["certify"]["outcome"], (rec.get("profile") or {}).get("outcome")} & {"timeout", "mem-kill", "oom"}
        if bad:
            log(f"{key}: {bad} — the larger probes of this set are not run")
            for k2, _, _, _ in SMALL[SMALL.index((key, src, M, r)) + 1:]:
                st["small"].setdefault(k2, {"skipped": f"not run: {key} ended with {', '.join(sorted(bad))}"})
            save_state(st)
            break


def probe_rand(args, st):
    src = os.path.join("bench", "scaling", "rand_a64.cqr")
    for r in range(1, args.r_max + 1):
        key = f"r{r}"
        if key in st["rand"] and st["rand"][key].get("profile") and not args.redo:
            log(f"rand_a64 {key}: done, skipped")
            continue
        if r == 3:
            prev = st["rand"].get("r2", {})
            peak = (prev.get("profile") or {}).get("peak_mb") or 0
            ok = prev.get("certify", {}).get("outcome") != "timeout" and \
                (prev.get("profile") or {}).get("outcome") != "timeout" and peak < args.mem_guard_mb
            if not ok:
                st["rand"][key] = {"skipped": f"guard (r = 2: outcome {prev.get('certify', {}).get('outcome')}, "
                                              f"profile {(prev.get('profile') or {}).get('outcome')}, "
                                              f"peak {peak} MB, guard {args.mem_guard_mb} MB)"}
                save_state(st)
                log(f"rand_a64 r3: skipped ({st['rand'][key]['skipped']})")
                continue
        out_dir = os.path.join(OUT, f"rand_a64_{key}")
        rec = {"certify": certify([src, "--solutions", "1853", "--iterations", str(r),
                                   "--count-limit", "0"], out_dir, args.timeout)}
        cert = os.path.join(out_dir, "Cert.lean")
        if os.path.exists(cert):
            rec["instructions"] = rec["certify"].get("instructions")
            rec["profile"] = profile(cert, args.timeout, args.threshold_ms, f"rand_a64 {key}")
        st["rand"][key] = rec
        save_state(st)


def front_end_file(src, out_lean):
    lake = shutil.which("lake")
    p = subprocess.run([lake, "env", "lean", "--run", os.path.join("scripts", "CertifyTool.lean"),
                        "front-end", src, os.path.relpath(out_lean, ROOT)], cwd=ROOT,
                       capture_output=True, text=True, encoding="utf-8")
    return p.returncode, (p.stdout + p.stderr).replace("\r", "")


FRONT_END_SOURCES = [("nat_m", os.path.join("bench", "forms", "nat_m.cqr")),
                     ("nat_ret", os.path.join("bench", "forms", "nat_ret.cqr")),
                     ("nat_wide", os.path.join("bench", "forms", "nat_wide.cqr")),
                     ("for_idx", os.path.join("bench", "forms", "for_idx.cqr")),
                     ("grover_pred_037", os.path.join("examples", "grover_pred_037.cqr"))]


def probe_natm(args, st):
    if st["natm"].get("front_end") and not args.redo:
        log("natm: done, skipped")
        return
    src = os.path.join("bench", "forms", "nat_m.cqr")
    out_dir = os.path.join(OUT, "nat_m")
    st["natm"]["source"] = read(os.path.join(ROOT, src))
    st["natm"]["certify"] = certify([src, "--solutions", "1", "--count-limit", "0"], out_dir,
                                    args.timeout)
    for label, s in FRONT_END_SOURCES:
        fe = os.path.join(out_dir, f"FrontEnd_{label}.lean")
        rc, out = front_end_file(s, fe)
        log(f"front-end {label}: rc {rc} {out.strip()[:120]}")
        if rc != 0:
            st["natm"][f"front_end_{label}"] = {"outcome": "error", "error": out.strip()[:400]}
            continue
        st["natm"][f"front_end_{label}"] = profile(fe, args.timeout, 500, f"front-end {label}")
    st["natm"]["front_end"] = True
    save_state(st)


def scratch(cert_text, name, theorem_re):
    """The Stage 17b scratch file: `net`, `emitted` and one theorem (the front-end block dropped)."""
    text = RE_FRONT_END.sub("", cert_text.replace("\r\n", "\n"))
    lines = text.split("\n")
    ns = next(i for i, l in enumerate(lines) if l.startswith("namespace "))
    em = next(i for i, l in enumerate(lines) if l.startswith("def emitted"))
    end = next(i for i in range(em + 1, len(lines))
               if lines[i].startswith("theorem") or lines[i].startswith("/--"))
    body = lines[ns:end]
    body[0] = f"namespace Forms.{name}"
    thm = re.search(theorem_re, text).group(0)
    return "import CQRV\n\n" + "\n".join(body) + "\n\n" + thm + f"\n\nend Forms.{name}\n"


def probe_committed(args, st):
    lean, env = lean_env()
    for d in CERTS:
        if d in st["committed"] and not args.redo:
            log(f"committed {d}: done, skipped")
            continue
        cert = os.path.join(ROOT, "examples", "certs", d, "Cert.lean")
        text = read(cert)
        rec = {"instructions": emitted_count(text)}
        out_dir = os.path.join(OUT, "committed", d)
        full = os.path.join(out_dir, "Cert.lean")
        write(full, text)
        rec["profile"] = profile(full, args.timeout, args.threshold_ms, f"committed {d}")
        for key, rx in (("grade_eq", r"theorem grade_eq : Synthesis\.grade emitted = ⟨[^⟩]*⟩ := by decide \+kernel"),
                        ("gradeExt_eq", r"theorem gradeExt_eq : Synthesis\.gradeExt emitted = ⟨[^⟩]*⟩ := by decide \+kernel")):
            f = os.path.join(out_dir, f"{key}_alone.lean")
            write(f, scratch(text, d, rx))
            samples = []
            for i in range(args.repeat):
                log(f"  {d} {key} alone, run {i + 1}/{args.repeat}")
                outcome, rc, out, wall, mem, _ = run_guarded([lean, "-Dprofiler=true", f], args.timeout,
                                                             MEM_KILL_MB, env)
                samples.append({"outcome": outcome, "kernel_s": kernel_s(out), "wall_s": round(wall, 2),
                                "peak_mb": mem})
            ks = [s["kernel_s"] for s in samples if s["kernel_s"] is not None]
            rec[key] = {"samples": samples, "min_kernel_s": min(ks) if ks else None}
            log(f"  -> {key} alone: {[s['kernel_s'] for s in samples]} s")
        st["committed"][d] = rec
        save_state(st)


# --- the report ------------------------------------------------------------------------------

DECLS = ["net", "prog", "prog_scoped", "net_ok", "front_end", "emitted", "emitted_ok", "delta_eq",
         "grade_eq", "gradeExt_eq", "nAnc_eq", "hM_count", "oracleCircuit", "oracle", "mczCircuit",
         "mcz_ok", "mcz", "diffCircuit", "diff_ok", "cert"]


def fmt(x, nd=2):
    return "—" if x is None else f"{x:.{nd}f}"


def decl_table(prof, title):
    if not prof:
        return f"_{title}: no profile._\n"
    rows = [f"### {title}", "",
            f"Outcome {prof['outcome']}, cumulative kernel `type checking` {fmt(prof['kernel_s'])} s, "
            f"wall {fmt(prof['wall_s'])} s, peak {prof['peak_mb']} MB"
            + (f"; first error: `{prof['error']}`" if prof.get("error") else "") + ".", "",
            "| declaration | type checking s | elaboration s | other profiler lines |", "|---|---|---|---|"]
    names = [n for n in DECLS if n in prof["decls"]] + [n for n in prof["order"] if n not in DECLS]
    for n in names:
        d = prof["decls"].get(n, {})
        other = ", ".join(f"{k} {v:.2f}" for k, v in d.items()
                          if k not in ("type checking", "elaboration") and v >= 0.5)
        rows.append(f"| `{n}` | {fmt(d.get('type checking'))} | {fmt(d.get('elaboration'))} | {other or '—'} |")
    return "\n".join(rows) + "\n"


def report(args, st):
    meta = st.get("meta", {})
    parts = ["# Kernel-evaluation forms (Stage 18a)", "",
             "Report §9.5.1 (measured values only), §5.1.3; docs/tasks/STAGE18_TASK.md A0, A2; "
             "PHASE2_SPEC.md §A.2 (amendments before Stage 18). Generated by `scripts/kernel_forms.py` "
             "from `bench/forms/out/state.json` (git-ignored; the Lean logs sit next to each probe); "
             "the reading after the marker at the end is hand-written and preserved by the generator.", "",
             "## Method", "",
             f"- Machine: {meta.get('machine', '?')}; `LEAN_NUM_THREADS={meta.get('lean_threads', '?')}`; "
             f"run {meta.get('when', '?')} (the four committed certificates were last regenerated at Stage 17b, "
             "9fc909b; this run is after A1, the cons-list scheduler).",
             f"- Toolchain: {meta.get('toolchain', '?')}.",
             f"- Per declaration: a copy of the Lean file with `#print axioms <name>` after every declaration, "
             f"`lean -DElab.async=false -Dprofiler=true -Dprofiler.threshold={args.threshold_ms}` (500 ms for the "
             f"front-end probes), timeout {args.timeout} s; the profiler's `… took` lines between two markers "
             "belong to the declaration the second marker names (asynchronous elaboration off, so the order is "
             "the declaration order; lines below the threshold are not printed, so small declarations show `—`). "
             "`type checking` is the kernel; `elaboration` includes the elaborator's own evaluation of "
             "`decide` / `decide +kernel`. Peak MB = peak working set of the lean process.",
             "- `cqr certify` runs its own kernel check (`lake env lean -Dprofiler=true Cert.lean`, one run, "
             "no `--bench`); its outcome and wall time are recorded, and the largest working set of its lean "
             "child seen by the one-second poll (`max_lean_mb`).",
             f"- Memory kill: a `lean` process above {args.mem_kill_mb} MB is killed and the outcome is "
             "`mem-kill` (added after the first run, in which the profiled rand_a64 r = 1 reached 10.4 GB and "
             "the machine thrashed; the 900 s timeout stays).",
             "- `grade_eq` alone / `gradeExt_eq` alone: the Stage 17b scratch-file method (`net`, `emitted` and "
             "that one theorem; cumulative `type checking` of `lean -Dprofiler=true`), the minimum of "
             f"{args.repeat} runs; \"before A1\" are the Stage 17b figures (DECISIONS.md 2026-10-31, 17b "
             "decision 9), not re-measured.", ""]
    # 1. rand_a64
    parts += ["## 1. rand_a64 (n = 12, 64 AND nodes), hypothesis form, after A1", "",
              "| r | instructions | certify outcome | certify wall s | profile outcome | kernel s (cumulative) | "
              "wall s | peak MB | `emitted_ok` s | `grade_eq` s | `gradeExt_eq` s | `cert` s | first error |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    pts = []
    for key in ("r1", "r2", "r3"):
        rec = st["rand"].get(key)
        if not rec:
            instr = "—"
            cert = os.path.join(OUT, f"rand_a64_{key}", "Cert.lean")
            if os.path.exists(cert):
                instr = emitted_count(read(cert))
            parts.append(f"| {key[1:]} | {instr} | see note | — | — | — | — | — | — | — | — | — | "
                         f"{REVIEWER_RECORD[key]} |")
            continue
        if "skipped" in rec:
            parts.append(f"| {key[1:]} | — | skipped | — | — | — | — | — | — | — | — | — | {rec['skipped']} |")
            continue
        c, p = rec["certify"], rec.get("profile") or {}
        dd = p.get("decls", {})
        tc = lambda n: fmt(dd.get(n, {}).get("type checking"))  # noqa: E731
        parts.append(f"| {key[1:]} | {rec.get('instructions', '—')} | {c['outcome']} | {fmt(c['wall_s'])} | "
                     f"{p.get('outcome', '—')} | {fmt(p.get('kernel_s'))} | {fmt(p.get('wall_s'))} | "
                     f"{p.get('peak_mb', '—')} | {tc('emitted_ok')} | {tc('grade_eq')} | {tc('gradeExt_eq')} | "
                     f"{tc('cert')} | {(p.get('error') or c.get('error') or '—')[:140]} |")
        g = dd.get("grade_eq", {}).get("type checking")
        if g and rec.get("instructions"):
            pts.append((rec["instructions"], g))
    parts.append("")
    for key in ("r1", "r2", "r3"):
        rec = st["rand"].get(key)
        if rec and rec.get("profile"):
            parts.append(decl_table(rec["profile"], f"rand_a64 r = {key[1:]}, per declaration"))
    # 1b. the attribution probe within memory
    parts += ["## 1b. The attribution probe within memory (hypothesis form, after A1)", "",
              "| instance | r | instructions | certify outcome | certify wall s | lean MB seen | profile outcome | "
              "kernel s (cumulative) | wall s | peak MB | `emitted_ok` s | `grade_eq` s | `gradeExt_eq` s | "
              "`cert` s | note |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for key, src, M, r in SMALL:
        rec = st.get("small", {}).get(key)
        if not rec:
            parts.append(f"| {key} | {r} | — | not run | — | — | — | — | — | — | — | — | — | — | — |")
            continue
        if "skipped" in rec:
            parts.append(f"| {key} | {r} | — | skipped | — | — | — | — | — | — | — | — | — | — | {rec['skipped']} |")
            continue
        c, p = rec["certify"], rec.get("profile") or {}
        dd = p.get("decls", {})
        tc = lambda n: fmt(dd.get(n, {}).get("type checking"))  # noqa: E731
        parts.append(f"| {key} | {r} | {rec.get('instructions', '—')} | {c['outcome']} | {fmt(c['wall_s'])} | "
                     f"{c.get('max_lean_mb', '—')} | {p.get('outcome', '—')} | {fmt(p.get('kernel_s'))} | "
                     f"{fmt(p.get('wall_s'))} | {p.get('peak_mb', '—')} | {tc('emitted_ok')} | {tc('grade_eq')} | "
                     f"{tc('gradeExt_eq')} | {tc('cert')} | {(p.get('error') or c.get('error') or '—')[:140]} |")
        g = dd.get("grade_eq", {}).get("type checking")
        if g and rec.get("instructions"):
            pts.append((rec["instructions"], g))
    parts.append("")
    for key, _, _, _ in SMALL:
        rec = st.get("small", {}).get(key)
        if rec and rec.get("profile"):
            parts.append(decl_table(rec["profile"], f"{key}, per declaration"))
    # 2. committed
    parts += ["## 2. The four committed certificates, after A1", "",
              "| certificate | instructions | profile outcome | kernel s (cumulative) | peak MB | `emitted_ok` s | "
              "`hM_count` s | `grade_eq` s | `gradeExt_eq` s | `cert` s | median of 5 in certificate.json (Stage 18a regeneration) |",
              "|---|---|---|---|---|---|---|---|---|---|---|"]
    for d in CERTS:
        rec = st["committed"].get(d)
        if not rec:
            parts.append(f"| {d} | — | not run | — | — | — | — | — | — | — | — |")
            continue
        p = rec["profile"]
        dd = p.get("decls", {})
        tc = lambda n: fmt(dd.get(n, {}).get("type checking"))  # noqa: E731
        try:
            cj = json.load(open(os.path.join(ROOT, "examples", "certs", d, "certificate.json"), encoding="utf-8"))
            med = cj["reference_configuration"]["kernel_check"]["kernel_ms"] / 1000
        except Exception:
            med = None
        parts.append(f"| {d} | {rec['instructions']} | {p['outcome']} | {fmt(p['kernel_s'])} | {p['peak_mb']} | "
                     f"{tc('emitted_ok')} | {tc('hM_count')} | {tc('grade_eq')} | {tc('gradeExt_eq')} | "
                     f"{tc('cert')} | {fmt(med)} |")
        g = dd.get("grade_eq", {}).get("type checking")
        if g:
            pts.append((rec["instructions"], g))
    parts += ["", "### `grade_eq` alone and `gradeExt_eq` alone: before A1 (Stage 17b) → after A1", "",
              "| certificate | instructions | `grade_eq` before | `grade_eq` after | `gradeExt_eq` before | "
              "`gradeExt_eq` after | samples after (grade_eq; gradeExt_eq) |", "|---|---|---|---|---|---|---|"]
    for d in CERTS:
        rec = st["committed"].get(d)
        b = BEFORE[d]
        if not rec:
            parts.append(f"| {d} | — | {b[0]} | — | {b[1]} | — | — |")
            continue
        ga, ea = rec["grade_eq"], rec["gradeExt_eq"]
        parts.append(f"| {d} | {rec['instructions']} | {b[0]} | {fmt(ga['min_kernel_s'])} | {b[1]} | "
                     f"{fmt(ea['min_kernel_s'])} | {' '.join(fmt(s['kernel_s']) for s in ga['samples'])}; "
                     f"{' '.join(fmt(s['kernel_s']) for s in ea['samples'])} |")
    slope = loglog_slope([x for x, _ in pts], [y for _, y in pts]) if len(pts) >= 2 else None
    parts += ["", f"Least-squares slope of log(`grade_eq` kernel s) against log(instructions) over the "
                  f"{len(pts)} profiled points above: **{fmt(slope)}** (Stage 14b measured 2.09 for the whole "
                  "kernel check against instructions).", ""]
    for d in CERTS:
        rec = st["committed"].get(d)
        if rec:
            parts.append(decl_table(rec["profile"], f"{d}, per declaration"))
    # 3. A0
    parts += ["## 3. A0 — the `Nat m` front-end block", ""]
    nm = st.get("natm", {})
    for label, s in FRONT_END_SOURCES[:-1]:
        try:
            parts += [f"`{s.replace(os.sep, '/')}`:", "", "```", read(os.path.join(ROOT, s)).rstrip("\n"),
                      "```", ""]
        except OSError:
            pass
    c = nm.get("certify")
    if c:
        parts += [f"`cqr certify bench/forms/nat_m.cqr --solutions 1 --count-limit 0`: exit {c['rc']}, "
                  f"{fmt(c['wall_s'])} s; last line: `{c['last_line'][:300]}`", ""]
    for label, _ in FRONT_END_SOURCES:
        p = nm.get(f"front_end_{label}")
        if p and p.get("outcome") != "error":
            parts.append(decl_table(p, f"front-end block of {label} (CertifyTool front-end), per declaration"))
        elif p:
            parts.append(f"front-end block of {label}: {p.get('error')}\n")
    body = "\n".join(parts)
    reading = ""
    if os.path.exists(MD):
        old = read(MD)
        if READING_MARK in old:
            reading = old[old.index(READING_MARK):]
    if not reading:
        reading = READING_MARK + "\n\n## Reading\n\n_(hand-written after the run)_\n"
    write(MD, body + "\n" + reading)
    log(f"wrote {os.path.relpath(MD, ROOT)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="natm,committed,rand-small")
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--r-max", type=int, default=3)
    ap.add_argument("--mem-guard-mb", type=int, default=9216)
    ap.add_argument("--mem-kill-mb", type=int, default=8000,
                    help="kill a lean process above this working set (MB); outcome mem-kill")
    ap.add_argument("--repeat", type=int, default=2)
    ap.add_argument("--threshold-ms", type=int, default=1000)
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--redo", action="store_true", help="re-run probes already in state.json")
    args = ap.parse_args()
    global MEM_KILL_MB
    MEM_KILL_MB = args.mem_kill_mb
    st = load_state()
    if not args.report_only:
        st["meta"] = {"machine": machine(), "toolchain": toolchain(),
                      "lean_threads": os.environ.get("LEAN_NUM_THREADS", "unset"),
                      "when": time.strftime("%Y-%m-%d %H:%M:%S")}
        save_state(st)
        only = args.only.split(",")
        if "natm" in only:
            probe_natm(args, st)
        if "committed" in only:
            probe_committed(args, st)
        if "rand-small" in only:
            probe_small(args, st)
        if "rand" in only:
            probe_rand(args, st)
    report(args, st)


if __name__ == "__main__":
    main()
