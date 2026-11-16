"""Stage 26c2 (P1) — the Python mirror of `CQRV/Hardware/PhysGrade.lean` (PHASE2_SPEC §C.3; report
§3.1, §5.3, §9.1.1): the physical grade of an artifact's physical circuit on its target at a
feed-forward latency L (ns), exact.

  python -I hw/physgrade.py <artifact dir> <target.json> <L ns> [--json]

Durations are the exact rationals of the decimal numbers in the target file (`parse_float=Fraction`,
never a float); the calibration rates are its decimal strings. The ASAP model: a gate starts when
all its qubits are free; a gate conditioned on a bit also waits for the end of the measurement that
wrote the bit, plus L. The bound is 25a's `physical_bound` (δ + every operation's rate + the data
readouts at their final positions). The JSON printed is byte-identical to `cqr hw grade --json`
(`tests/diff/hw_physgrade_check.py` compares them on all twelve artifacts).

Untrusted mirror: the Lean function is what the kernel evaluates in the physical certificate.
"""
import json
import os
import sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ONE_Q = ("rz", "sx", "x")
TWO_Q = ("cz", "cx")


def frac_str(f):
    f = Fraction(f)
    return f"{f.numerator}/{f.denominator}" if f.denominator != 1 else str(f.numerator)


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def load_target(path):
    return json.load(open(path, encoding="utf-8"), parse_float=Fraction)


def flat(ops):
    """(op, conditioning bit or None) for every basis op, blocks included."""
    for pop in ops:
        if "if" in pop:
            for b in pop["body"]:
                yield b, pop["if"]
        else:
            yield pop, None


def duration(dur, basis, op):
    name, q = op["op"], op["q"]
    if name == "measure":
        return Fraction(dur["measure"][str(q[0])])
    if name in TWO_Q:
        tab = dur["gates"][name]
        k, k2 = f"{q[0]},{q[1]}", f"{q[1]},{q[0]}"
        if k in tab:
            return Fraction(tab[k])
        if k2 in tab:
            return Fraction(tab[k2])
        raise KeyError(f"no duration for {name} on the edge {k}")
    return Fraction(dur["gates"][name][str(q[0])])


def rate(cal, basis, op):
    name, q = op["op"], op["q"]
    if name == "measure":
        return Fraction(cal["readout_error"][str(q[0])])
    if name in TWO_Q:
        tab = cal["two_qubit_gate_error"][name]
        k, k2 = f"{q[0]},{q[1]}", f"{q[1]},{q[0]}"
        if k in tab:
            return Fraction(tab[k])
        if k2 in tab:
            return Fraction(tab[k2])
        raise KeyError(f"no calibration for the edge {k}")
    return Fraction(cal["one_qubit_gate_error"][name][str(q[0])])


def phys_grade(ops, target, basis, used, data_phys, delta, L):
    """The record of `physGrade`: qubits, two_qubit, mid_measurements, feed_forward, depth (ns), bound,
    vacuous. `ops` are the device-level ops of physical.json; `used` the used device qubits."""
    L = Fraction(L)
    dur, cal = target["durations"], target["calibration"]
    assert dur["unit"] == "ns"
    tq = {p: Fraction(0) for p in used}
    tb = {}
    two = mid = ff = 0
    total = Fraction(0)
    for op, cond in flat(ops):
        d = duration(dur, basis, op)
        start = max(tq[p] for p in op["q"])
        if cond is not None:
            start = max(start, tb.get(cond, Fraction(0)) + L)
            ff += 1
        fin = start + d
        for p in op["q"]:
            tq[p] = fin
        if op["op"] == "measure":
            tb[op["c"]] = fin
            mid += 1
        if op["op"] in TWO_Q:
            two += 1
        total += rate(cal, basis, op)
    for p in data_phys:
        total += Fraction(cal["readout_error"][str(p)])
    depth = max(list(tq.values()) + list(tb.values()) + [Fraction(0)])
    bound = Fraction(delta) + total
    return {"qubits": len(used), "two_qubit": two, "mid_measurements": mid, "feed_forward": ff,
            "depth_ns": frac_str(depth), "bound": frac_str(bound), "vacuous": bound >= 1,
            "ff_latency_ns": frac_str(L)}


def grade_of_artifact(adir, target_path, L):
    manifest = json.load(open(os.path.join(adir, "manifest.json"), encoding="utf-8"))
    ops = json.load(open(os.path.join(adir, "physical.json"), encoding="utf-8"))
    target = load_target(target_path)
    g = manifest.get("grover")
    if g is None:
        delta = Fraction(0)
    else:
        sys.path.insert(0, os.path.join(ROOT, "tests", "diff"))
        from hw_bound_check import grover_delta
        delta = grover_delta(g["r"], g["n"], g["M"])
    return phys_grade(ops, target, manifest["basis"], manifest["layout"]["used_qubits"],
                      manifest["layout"]["data_physical"], delta, L)


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    as_json = "--json" in argv
    argv = [a for a in argv if a != "--json"]
    adir, target_path, L = argv[0], argv[1], argv[2]
    g = grade_of_artifact(adir, target_path, L)
    if as_json:
        print(canonical(g))
    else:
        for k, v in g.items():
            print(f"{k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
