"""Extract a `HardwareTarget` JSON (docs/hardware_target.schema.json v1.0.0) from a Qiskit fake
backend — Stage 24a (PHASE2_SPEC §C.1, Track C; report §3.1.3, §5.3).

Untrusted tool: it reads `backend.target` (basis gates, coupling map, durations, errors), the
qubit properties (T1, T2) and the calibration timestamp of a fake backend of
`qiskit_ibm_runtime.fake_provider`, and writes the canonical JSON — keys sorted by code point,
no whitespace (`json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=False)`), a
trailing newline. Every number inside `calibration` is a decimal string (`repr` of the float the
source gives), so that `snapshot.hash` — `hashlib.sha3_256` of the canonical `calibration` — is
computed identically by Lean (`CQRV.Hardware.Target.checkHash`, `Lean.Json.compress` on the parsed
object). Entries whose source gives no value are omitted. The fake provider gives no mid-circuit
measurement error: that field is null with a note, and the readout error is not substituted.

Usage (from the repository root, inside .venv-hw):
    python -I hw/target.py FakeTorino --out hw/targets/fake_torino.json
    python -I hw/target.py FakeTorino --feed-forward-off --out hw/targets/fake_torino_noff.json
`--feed-forward-off` writes a hand-made variant: `capabilities.feed_forward.value` false, the
name suffixed `_noff`, `source.variant` = "feed_forward_off"; it exercises the coherent-only
path (PHASE2_SPEC §C.1). Nothing here touches the network.
"""

import argparse
import hashlib
import json
import math
import sys

EXTRACTED_BY = "hw/target.py (Stage 24a)"
MCM_NOTE = ("the fake provider gives no mid-circuit measurement error; the readout error is "
            "not substituted")


def canonical(obj):
    """The canonical JSON form shared with Lean's `Json.compress`."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def calibration_hash(calibration):
    return hashlib.sha3_256(canonical(calibration).encode("utf-8")).hexdigest()


def dec(x):
    """A finite float as a decimal string (Python's shortest round-trip repr)."""
    x = float(x)
    if not math.isfinite(x):
        raise ValueError(f"non-finite calibration value {x!r}")
    return repr(x)


def tuple_key(qargs):
    return ",".join(str(int(q)) for q in qargs)


def versions():
    import qiskit
    import qiskit_aer
    import qiskit_ibm_runtime
    return {"qiskit": qiskit.__version__, "qiskit_ibm_runtime": qiskit_ibm_runtime.__version__,
            "qiskit_aer": qiskit_aer.__version__}


def timestamp_of(backend):
    """The calibration timestamp the source gives (ISO 8601), or None."""
    props = None
    try:
        props = backend.properties()
    except Exception:  # noqa: BLE001 — a fake without properties
        props = None
    if props is not None:
        lud = getattr(props, "last_update_date", None)
        if lud is not None:
            return lud.isoformat() if hasattr(lud, "isoformat") else str(lud)
    return None


def extract(backend, feed_forward_off=False):
    """The target dict for `backend` (a fake backend instance)."""
    from qiskit.circuit import Gate

    tgt = backend.target
    n = int(tgt.num_qubits)
    names = sorted(tgt.operation_names)
    gates = sorted(nm for nm in names if isinstance(tgt.operation_from_name(nm), Gate))
    cmap = tgt.build_coupling_map()
    edges = sorted([int(a), int(b)] for a, b in cmap.get_edges()) if cmap is not None else []

    dur_gates, dur_measure = {}, {}
    one_err, two_err, readout = {}, {}, {}
    for nm in names:
        props = tgt[nm]
        if props is None:
            continue
        for qargs, ip in props.items():
            if qargs is None or ip is None:
                continue
            key = tuple_key(qargs)
            if ip.duration is not None:
                ns = float(ip.duration) * 1e9
                if nm == "measure":
                    dur_measure[key] = ns
                else:
                    dur_gates.setdefault(nm, {})[key] = ns
            if ip.error is not None:
                if nm == "measure":
                    readout[key] = dec(ip.error)
                elif nm in gates and len(qargs) == 1:
                    one_err.setdefault(nm, {})[key] = dec(ip.error)
                elif nm in gates and len(qargs) == 2:
                    two_err.setdefault(nm, {})[key] = dec(ip.error)
    t1, t2 = {}, {}
    qprops = tgt.qubit_properties or []
    for q, qp in enumerate(qprops):
        if qp is None:
            continue
        if getattr(qp, "t1", None) is not None:
            t1[str(q)] = dec(qp.t1)
        if getattr(qp, "t2", None) is not None:
            t2[str(q)] = dec(qp.t2)

    cls = type(backend)
    cls_name = f"{cls.__module__}.{cls.__name__}"
    ts = timestamp_of(backend)
    if ts is None:
        raise ValueError(f"{cls_name}: the source gives no calibration timestamp")

    def cap(flag, op):
        return {"value": bool(flag), "source": f"`{op}` in backend.target.operation_names"}

    capabilities = {
        "mid_circuit_measurement": cap("measure" in names, "measure"),
        "feed_forward": cap("if_else" in names, "if_else"),
        "reset": cap("reset" in names, "reset"),
    }
    capabilities["mid_circuit_measurement"]["source"] += (
        "; the fake provider does not distinguish mid-circuit from final measurement")
    name = str(backend.name)
    source = {"class": cls_name, "extracted_by": EXTRACTED_BY, **versions()}
    if feed_forward_off:
        name += "_noff"
        capabilities["feed_forward"] = {
            "value": False,
            "source": f"hand-made variant of {cls_name}: feed_forward set to false to exercise "
                      "the coherent-only path; not a property of the backend"}
        source["variant"] = "feed_forward_off"
        source["note"] = "hand-made variant: every other field is the backend's"
    calibration = {
        "source": f"backend.target instruction properties (error) and qubit properties (t1, t2) "
                  f"of {cls_name}; entries the source leaves None are omitted",
        "one_qubit_gate_error": one_err,
        "two_qubit_gate_error": two_err,
        "readout_error": readout,
        "mid_circuit_measurement_error": None,
        "mid_circuit_measurement_note": MCM_NOTE,
        "t1_s": t1,
        "t2_s": t2,
    }
    return {
        "schema_version": "1.0.0",
        "name": name,
        "source": source,
        "num_qubits": n,
        "basis_gates": gates,
        "coupling_map": edges,
        "capabilities": capabilities,
        "durations": {
            "source": f"backend.target instruction properties (duration, seconds × 1e9) of {cls_name}",
            "unit": "ns", "gates": dur_gates, "measure": dur_measure},
        "calibration": calibration,
        "snapshot": {"timestamp": ts, "hash": calibration_hash(calibration)},
    }


def fake_backend(class_name):
    import qiskit_ibm_runtime.fake_provider as fp
    cls = getattr(fp, class_name, None)
    if cls is None:
        raise SystemExit(f"hw/target.py: no fake backend `{class_name}` in "
                         f"qiskit_ibm_runtime.fake_provider")
    return cls()


def render(target):
    return canonical(target) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("backend", help="a class of qiskit_ibm_runtime.fake_provider, e.g. FakeTorino")
    ap.add_argument("--out", required=True, help="the target JSON to write")
    ap.add_argument("--feed-forward-off", action="store_true",
                    help="write the hand-made variant with feed_forward false")
    a = ap.parse_args(argv)
    target = extract(fake_backend(a.backend), feed_forward_off=a.feed_forward_off)
    with open(a.out, "w", encoding="utf-8", newline="\n") as f:
        f.write(render(target))
    print(f"{a.out}: {target['name']}, {target['num_qubits']} qubits, "
          f"modes {'mbu, coherent' if target['capabilities']['mid_circuit_measurement']['value'] and target['capabilities']['feed_forward']['value'] else 'coherent'}, "
          f"hash {target['snapshot']['hash']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
