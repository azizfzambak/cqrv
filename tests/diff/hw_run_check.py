"""Hardware run check (Stage 25b V3; PHASE2_SPEC §C.2 "The runs"; report §5.3). Two modes:

  python -I tests/diff/hw_run_check.py --schema-only          (.venv: jsonschema 4.26.0)
      every committed run report docs/hw_runs/*.json validates against docs/hw_run.schema.json; the
      Clopper–Pearson figures and the check's arithmetic of every committed report are recomputed
      (no simulation);

  python -I tests/diff/hw_run_check.py --cqr <path to cqr>   (.venv-hw)
      the CI subset — the wrapped MBU gadget, hw_n2 and hw_n3 on FakeTorino at 2000 shots — run
      in-process by hw/run.py: the noiseless run agrees with the reference (1 − δ, or 1) within a
      5-sigma binomial tolerance; the Clopper–Pearson figures and the check's arithmetic
      recomputed; the manifest hash link; determinism (the same seed gives the same counts); the
      report validates against the schema when jsonschema is importable. Every outcome of the
      one-sided check is reported as it is: a "fails" is a finding, not a failure of this check.
"""

import argparse
import glob
import hashlib
import json
import math
import os
import sys
import time
import warnings

warnings.simplefilter("ignore")
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "hw"))

fails = 0
CI_SUBSET = ["mbu_gadget_wrapped__fake_torino", "hw_n2_tree_mbu__fake_torino", "hw_n3_tree_mbu__fake_torino"]


def check(cond, msg):
    global fails
    if cond:
        print(f"ok    {msg}")
    else:
        fails += 1
        print(f"FAIL  {msg}")


def cp_recompute(k, n, alpha=0.05):
    """Clopper–Pearson by bisection on the binomial CDF (independent of scipy)."""
    from math import exp, lgamma, log

    def cdf(p, kk):          # P(X <= kk), each term in log space (stable for n in the thousands)
        if p <= 0:
            return 1.0
        if p >= 1:
            return 1.0 if kk >= n else 0.0
        lc = lgamma(n + 1)
        return sum(exp(lc - lgamma(i + 1) - lgamma(n - i + 1) + i * log(p) + (n - i) * log(1 - p)) for i in range(kk + 1))

    def solve(f, target, increasing):   # f monotone in p on [0, 1]; the p with f(p) = target
        lo, hi = 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            if (f(mid) < target) == increasing:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2
    # lower bounds: P(X >= k) = 1 - cdf(p, k-1), increasing in p; upper bound: cdf(p, k), decreasing
    lo = 0.0 if k == 0 else solve(lambda p: 1 - cdf(p, k - 1), alpha / 2, True)
    hi = 1.0 if k == n else solve(lambda p: cdf(p, k), alpha / 2, False)
    lo1 = 0.0 if k == 0 else solve(lambda p: 1 - cdf(p, k - 1), alpha, True)
    return lo, hi, lo1


def arithmetic(rep, tol=1e-9):
    """The report's own arithmetic: p̂, the Clopper–Pearson figures, the threshold and the result."""
    k, n = rep["noisy"]["successes"], rep["shots"]
    ok = abs(rep["noisy"]["p_hat"] - k / n) < tol
    if n <= 10000:  # the binomial CDF by log-space summation
        lo, hi, lo1 = cp_recompute(k, n)
        got = rep["noisy"]["clopper_pearson_95"] + [rep["noisy"]["one_sided_lower_95"]]
        ok = ok and all(abs(a - b) < 1e-6 for a, b in zip(got, (lo, hi, lo1)))
    dhw = rep["delta_hw_float"]
    thr = 1 - dhw - math.sqrt(math.log(1 / rep["check"]["alpha"]) / (2 * n))
    ok = ok and abs(thr - rep["check"]["threshold"]) < tol
    want = "vacuous (delta_hw >= 1)" if dhw >= 1 else ("passes" if rep["noisy"]["p_hat"] >= thr else "fails")
    ok = ok and rep["check"]["result"] == want and rep["delta_hw_vacuous"] == (dhw >= 1)
    return ok


def validate_schema(rep):
    try:
        import jsonschema
    except ImportError:
        return None
    schema = json.load(open(os.path.join(ROOT, "docs", "hw_run.schema.json"), encoding="utf-8"))
    jsonschema.validate(rep, schema, cls=jsonschema.Draft202012Validator)
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cqr")
    ap.add_argument("--schema-only", action="store_true")
    ap.add_argument("--runs", default=os.path.join(ROOT, "docs", "hw_runs"))
    ap.add_argument("--shots", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=25)
    a = ap.parse_args()
    if a.schema_only:
        import jsonschema
        schema = json.load(open(os.path.join(ROOT, "docs", "hw_run.schema.json"), encoding="utf-8"))
        jsonschema.Draft202012Validator.check_schema(schema)
        check(True, "docs/hw_run.schema.json is a valid draft 2020-12 schema")
        paths = sorted(glob.glob(os.path.join(a.runs, "*.json")))
        check(len(paths) >= 11, f"{len(paths)} committed run reports in docs/hw_runs/")
        for p in paths:
            rep = json.load(open(p, encoding="utf-8"))
            try:
                jsonschema.validate(rep, schema, cls=jsonschema.Draft202012Validator)
                sch = True
            except jsonschema.ValidationError as e:
                sch = False
                print(f"      {e.message[:160]}")
            check(sch and arithmetic(rep) and "verified on hardware" not in json.dumps(rep),
                  f"{os.path.basename(p)}: schema, Clopper–Pearson and check arithmetic recomputed; result {rep['check']['result']}")
        check(os.path.exists(os.path.join(a.runs, "RUNS.md")), "docs/hw_runs/RUNS.md exists")
        print(f"hw_run_check --schema-only: {'all checks passed' if fails == 0 else f'{fails} FAILED'}")
        return 1 if fails else 0
    if not a.cqr:
        ap.error("--cqr is required without --schema-only")
    import run as hwrun
    t_all = time.time()
    for name in CI_SUBSET:
        d = os.path.join(ROOT, "hw", "artifacts", name)
        t0 = time.time()
        rep = hwrun.run_sim(d, a.shots, a.seed, a.cqr)
        p_ref = rep["reference_float"]
        sigma = math.sqrt(max(p_ref * (1 - p_ref), 1e-12) / a.shots)
        dev = abs(rep["ideal"]["p_ideal"] - p_ref)
        check(dev <= 5 * sigma + 1e-12, f"{name}: noiseless run {rep['ideal']['p_ideal']:.4f} vs reference {p_ref:.4f} "
                                        f"(deviation {dev:.4f} <= 5 sigma = {5 * sigma:.4f})")
        check(arithmetic(rep), f"{name}: p_hat, Clopper–Pearson and the check's arithmetic recomputed")
        mh = hashlib.sha3_256(open(os.path.join(d, "manifest.json"), "rb").read()).hexdigest()
        check(rep["hashes"]["manifest"] == mh, f"{name}: manifest hash link")
        rep2 = hwrun.run_sim(d, a.shots, a.seed, a.cqr)
        check(rep2["noisy"]["counts"] == rep["noisy"]["counts"] and rep2["ideal"]["successes"] == rep["ideal"]["successes"],
              f"{name}: deterministic (same seed, same counts)")
        sch = validate_schema(rep)
        check(sch is not False, f"{name}: report schema ({'jsonschema' if sch else 'jsonschema not importable here; skipped'})")
        check("verified on hardware" not in json.dumps(rep), f"{name}: wording ({rep['kind'][:48]}…)")
        print(f"info  {name}: p_hat {rep['noisy']['p_hat']:.4f} [{rep['noisy']['clopper_pearson_95'][0]:.4f}, "
              f"{rep['noisy']['clopper_pearson_95'][1]:.4f}], delta_hw {rep['delta_hw_float']:.4g}, threshold "
              f"{rep['check']['threshold']:.4f}, one-sided check: {rep['check']['result']} (a finding, reported as it is); "
              f"{time.time() - t0:.1f} s")
    print(f"hw_run_check: {'all checks passed' if fails == 0 else f'{fails} FAILED'}; {time.time() - t_all:.1f} s")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
