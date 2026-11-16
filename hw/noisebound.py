"""Stage 27b (B2) — the Python mirror of `CQRV/Hardware/Noise.lean` (PHASE2_SPEC §C.4 (4); report
§2.3.2, §6.6): the conditional noise bound of an artifact's physical circuit on its target, exact.

  python -I hw/noisebound.py <artifact dir> <target.json> [--json]

(P-stoch): for a basis operation on k qubits, p = min 1 ((d+1)/d · r) with d = 2^k — 3/2 · r for
`sx` and `x`, 5/4 · r for `cz` and `cx`; virtual `rz` has r = 0 so p = 0; a conditioned gate takes the
rate of its gate. (P-ro): a mid-circuit measurement and a data readout take p = r, the readout rate,
with no factor. The bound is δ + Σ p + Σ r (everything clamped to [0, 1]); `clamped` records whether
some unclamped p exceeded 1 (then the bound is vacuous). 25a's p = r figure (`hw/physgrade.py`) is
printed beside it. The JSON printed is byte-identical to `cqr hw noise --json`
(`tests/diff/hw_noise_check.py` compares them on all twelve artifacts).

Untrusted mirror: the Lean function is what the kernel evaluates in the conditional certificate.
Conditional on the premises, never a fact about a device; never "verified on hardware".
"""
import json
import os
import sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "hw"))
import physgrade  # noqa: E402

FACTOR = {"rz": Fraction(0), "sx": Fraction(3, 2), "x": Fraction(3, 2), "cz": Fraction(5, 4), "cx": Fraction(5, 4),
          "measure": Fraction(1)}


def clamp01(q):
    return max(Fraction(0), min(Fraction(1), Fraction(q)))


def noise_bound(ops, target, basis, data_phys, delta):
    """The record of `noiseBound`: noise_bound, noise_vacuous, clamped."""
    cal = target["calibration"]
    raw = [FACTOR[op["op"]] * physgrade.rate(cal, basis, op) for op, _cond in physgrade.flat(ops)]
    ro = [Fraction(cal["readout_error"][str(p)]) for p in data_phys]
    bound = Fraction(delta) + (sum(clamp01(q) for q in raw) + sum(clamp01(q) for q in ro))
    return {"noise_bound": physgrade.frac_str(bound), "noise_vacuous": bound >= 1,
            "clamped": any(q > 1 for q in raw) or any(q > 1 for q in ro)}


def noise_of_artifact(adir, target_path):
    manifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
    ops = json.load(open(os.path.join(adir, "physical.json"), encoding="utf-8"))
    target = physgrade.load_target(target_path)
    g = manifest.get("grover")
    if g is None:
        delta = Fraction(0)
    else:
        sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
        from hw_bound_check import grover_delta
        delta = grover_delta(g["r"], g["n"], g["M"])
    used = manifest["layout"]["used_qubits"]
    data_phys = manifest["layout"]["data_physical"]
    nb = noise_bound(ops, target, manifest["basis"], data_phys, delta)
    pg = physgrade.phys_grade(ops, target, manifest["basis"], used, data_phys, delta, 0)
    nb["physical_bound_p_eq_r"] = pg["bound"]
    return nb


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    as_json = "--json" in argv
    argv = [a for a in argv if a != "--json"]
    nb = noise_of_artifact(argv[0], argv[1])
    if as_json:
        print(physgrade.canonical(nb))
    else:
        for k, v in nb.items():
            print(f"{k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
