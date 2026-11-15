"""Layout and routing with a witness — Stage 25a U2/U3 (PHASE2_SPEC §C.2; report §5.3).

Untrusted tool, with every claim about the transpiler's output checked against that output.
The pipeline keeps what we do apart from what Qiskit does:

1. **Our translation** (hw/decomp.py): the IR circuit becomes a flat list of basis gates with
   provenance; a conditioned IR gate is one `if_test` block holding its basis sequence.
2. **Qiskit does layout and routing only**: `SabreLayout(coupling_map, seed=s)` of qiskit 2.6.2 in a
   `PassManager` on its own. In this version it lays out and routes in one pass (its Rust
   implementation), supports control flow (it routes inside `if_test` blocks and restores the
   layout at the end of each block), inserts the routing swaps as `swap` gates, applies the layout
   (the physical circuit has the device's width) and touches neither the basis gates nor their
   parameters. All of that is **checked** below, never assumed: `extract` reads the physical
   circuit back, `witness_of` matches every physical gate to a translated element through the
   layout it tracks (and fails if the physical order violates a dependency of the translated
   circuit, if a gate or an angle differs, or if a block does not restore the layout), and
   `reconstruct(translated, witness)` rebuilds the physical circuit from the witness alone, which
   must equal the extracted one gate for gate.
3. **The witness** (`docs/hw_witness.schema.json` 1.0.0): the initial and final layouts
   (logical → physical), the order of the translated elements as the physical circuit executes
   them with every routing swap at its position and physical edge (top level and inside each
   block), the table entries used, the classical-bit map, the seed, the versions.
4. **The swaps are then decomposed by the table** (`swap` entry: three controlled-NOTs, each by
   the basis' entry), giving the final physical circuit (`expand_swaps`) whose counts per used
   qubit and edge feed the bound on the physical circuit (`physical_bound`, exact fractions, with
   the n data readouts at their final physical positions and the mid-circuit readout assumption
   of Stage 24c). `seed_search` tries a fixed seed list and keeps the least bound.

Representation: a *physical op* is `{"op", "q": [physical qubits], "angle"?: "num/den" (turns),
"c"?: clbit}` for a basis gate or a measurement, `{"op": "swap", "q": [p, q]}` for a routing
swap, or `{"if": clbit, "body": [ops]}` for a block. Nothing here touches the network.
"""

import math
from fractions import Fraction

from qiskit.circuit import IfElseOp
from qiskit.transpiler import PassManager
from qiskit.transpiler.passes import SabreLayout

import decomp

ONE_Q = ("rz", "sx", "x")
TWO_Q = ("cz", "cx")


# --- the translated circuit as elements

def elements(gates):
    """Top-level elements of a translated gate list: `{"g": i}` for a plain gate, or
    `{"if": bit, "ir": k, "members": [i…]}` for the basis gates of one conditioned IR gate."""
    els, i = [], 0
    while i < len(gates):
        g = gates[i]
        if "if" in g:
            j = i
            while j < len(gates) and gates[j].get("if") == g["if"] and gates[j]["ir"] == g["ir"]:
                j += 1
            els.append({"if": g["if"], "ir": g["ir"], "members": list(range(i, j))})
            i = j
        else:
            els.append({"g": i})
            i += 1
    return els


def gate_qubits(gates, el):
    if "g" in el:
        return list(gates[el["g"]]["q"])
    qs = []
    for m in el["members"]:
        for q in gates[m]["q"]:
            if q not in qs:
                qs.append(q)
    return qs


def gate_bits(gates, el):
    if "g" in el:
        g = gates[el["g"]]
        return [g["c"]] if g["op"] == "measure" else []
    return [el["if"]]


# --- reading the physical circuit back

def angle_turns(theta):
    """The exact turn fraction of an rz angle the translation wrote (2π·f with f a dyadic
    fraction of denominator ≤ 2^12), or None."""
    f = Fraction(theta / (2 * math.pi)).limit_denominator(4096)
    return f if abs(float(f) * 2 * math.pi - theta) < 1e-9 else None


def extract(tq):
    """The physical ops of a Qiskit circuit (after SabreLayout), with physical qubit indices."""
    def conv(instrs):
        out = []
        for ins in instrs:
            name = ins.operation.name
            q = [tq.find_bit(b).index for b in ins.qubits]
            if isinstance(ins.operation, IfElseOp):
                cond = ins.operation.condition
                assert cond is not None and cond[1] == 1 and len(ins.operation.blocks) == 1, "unexpected if_else"
                blk = ins.operation.blocks[0]
                # block qubits are the block's own; map them through ins.qubits
                qmap = {blk.qubits[i]: tq.find_bit(ins.qubits[i]).index for i in range(len(ins.qubits))}
                body = []
                for i2 in blk.data:
                    n2 = i2.operation.name
                    q2 = [qmap[b] for b in i2.qubits]
                    assert n2 != "if_else", "nested if_else"
                    if n2 == "rz":
                        body.append({"op": "rz", "q": q2, "angle": decomp.frac_str(angle_turns(float(i2.operation.params[0])))})
                    else:
                        body.append({"op": n2, "q": q2})
                out.append({"if": tq.find_bit(cond[0]).index, "body": body})
            elif name == "measure":
                out.append({"op": "measure", "q": q, "c": tq.find_bit(ins.clbits[0]).index})
            elif name == "rz":
                f = angle_turns(float(ins.operation.params[0]))
                assert f is not None, f"rz angle {ins.operation.params[0]} is not a dyadic turn"
                out.append({"op": "rz", "q": q, "angle": decomp.frac_str(f)})
            elif name in ("sx", "x", "cz", "cx", "swap"):
                out.append({"op": name, "q": q})
            else:
                raise ValueError(f"unexpected physical op {name}")
        return out
    return conv(tq.data)


# --- routing

def route(translated_qc, coupling_map, seed):
    """SabreLayout alone (layout + routing, swaps kept, no optimization, no basis change)."""
    pm = PassManager([SabreLayout(coupling_map, seed=seed)])
    return pm.run(translated_qc)


# --- the witness

class WitnessError(Exception):
    pass


def _match_gate(gates, g_idx, pop, phys_q, layout_inv, used):
    """Check that the physical gate `pop` is the translated gate `g_idx` under the inverse layout."""
    g = gates[g_idx]
    logical = [layout_inv.get(p) for p in phys_q]
    if g["op"] != pop["op"] or logical != list(g["q"]):
        raise WitnessError(f"physical {pop} is not translated gate {g_idx} {g} (logical {logical})")
    if g["op"] == "rz" and Fraction(g["angle"]) != Fraction(pop["angle"]):
        raise WitnessError(f"angle differs at translated gate {g_idx}: {g['angle']} vs {pop['angle']}")
    if g["op"] == "measure" and g["c"] != pop["c"]:
        raise WitnessError(f"clbit differs at measure {g_idx}")
    used.add(g.get("entry"))


def witness_of(gates, phys_ops, initial_layout, seed, basis, target_name, versions, n_logical):
    """Match the physical ops to the translated elements and build the witness. The layout is a
    list logical → physical. Dependency order: an element is consumed only when it is at the head
    of the queue of every logical qubit and classical bit it touches."""
    els = elements(gates)
    qqueue = {}   # logical qubit -> [element indices]
    bqueue = {}   # clbit -> [element indices]
    for ei, el in enumerate(els):
        for q in gate_qubits(gates, el):
            qqueue.setdefault(q, []).append(ei)
        for b in gate_bits(gates, el):
            bqueue.setdefault(b, []).append(ei)
    layout = list(initial_layout)                      # logical -> physical
    inv = {p: l for l, p in enumerate(layout)}         # physical -> logical (only laid-out qubits)
    order, blocks, used, swaps = [], {}, set(), 0

    def ready(ei):
        el = els[ei]
        return all(qqueue[q] and qqueue[q][0] == ei for q in gate_qubits(gates, el)) and \
            all(bqueue[b] and bqueue[b][0] == ei for b in gate_bits(gates, el))

    def consume(ei):
        el = els[ei]
        for q in gate_qubits(gates, el):
            qqueue[q].pop(0)
        for b in gate_bits(gates, el):
            bqueue[b].pop(0)

    def do_swap(lay, inv_map, p, q):
        a, b = inv_map.get(p), inv_map.get(q)
        if a is not None:
            lay[a] = q
        if b is not None:
            lay[b] = p
        inv_map.pop(p, None)
        inv_map.pop(q, None)
        if a is not None:
            inv_map[q] = a
        if b is not None:
            inv_map[p] = b

    for pop in phys_ops:
        if "if" in pop:
            c = pop["if"]
            if not bqueue.get(c):
                raise WitnessError(f"if_else on clbit {c} with no pending conditioned element")
            ei = bqueue[c][0]
            el = els[ei]
            if "members" not in el or not ready(ei):
                raise WitnessError(f"if_else on clbit {c}: element {ei} not a ready block")
            # inside: a local layout; members matched by local queues
            lay2, inv2 = list(layout), dict(inv)
            mq = {}
            for m in el["members"]:
                for q in gates[m]["q"]:
                    mq.setdefault(q, []).append(m)
            body = []
            for bop in pop["body"]:
                if bop["op"] == "swap":
                    do_swap(lay2, inv2, *bop["q"])
                    body.append({"swap": list(bop["q"])})
                    swaps += 1
                    continue
                logical = [inv2.get(p) for p in bop["q"]]
                if logical[0] is None or not mq.get(logical[0]):
                    raise WitnessError(f"block gate {bop} on no pending member")
                m = mq[logical[0]][0]
                if any(not mq.get(q) or mq[q][0] != m for q in gates[m]["q"]):
                    raise WitnessError(f"block gate {bop}: member {m} not ready")
                _match_gate(gates, m, bop, bop["q"], inv2, used)
                for q in gates[m]["q"]:
                    mq[q].pop(0)
                body.append({"g": m})
            if any(mq[q] for q in mq):
                raise WitnessError(f"block {ei}: members left unexecuted")
            if lay2 != layout:
                raise WitnessError(f"block {ei} does not restore the layout")
            consume(ei)
            order.append({"e": ei})
            blocks[str(ei)] = body
        elif pop["op"] == "swap":
            do_swap(layout, inv, *pop["q"])
            order.append({"swap": list(pop["q"])})
            swaps += 1
        else:
            logical = [inv.get(p) for p in pop["q"]]
            if logical[0] is None or not qqueue.get(logical[0]):
                raise WitnessError(f"physical {pop} on logical {logical} with no pending element")
            ei = qqueue[logical[0]][0]
            el = els[ei]
            if "g" not in el or not ready(ei):
                raise WitnessError(f"physical {pop}: element {ei} not a ready plain gate")
            _match_gate(gates, el["g"], pop, pop["q"], inv, used)
            consume(ei)
            order.append({"e": ei})
    left = [ei for ei, _ in enumerate(els) if any(qqueue[q] and qqueue[q][0] == ei for q in gate_qubits(gates, els[ei]))]
    if any(qqueue[q] for q in qqueue) or any(bqueue[b] for b in bqueue):
        raise WitnessError(f"translated elements left unexecuted: {left[:5]}")
    n_bits = max([g.get("c", -1) for g in gates] + [g.get("if", -1) for g in gates] + [0]) + 1
    return {
        "schema_version": "1.0.0",
        "basis": basis,
        "target": target_name,
        "n_logical": n_logical,
        "initial_layout": list(initial_layout),
        "final_layout": layout,
        "order": order,
        "blocks": blocks,
        "swaps": swaps,
        "entries_used": sorted(e for e in used if e is not None),
        "clbit_map": list(range(n_bits)),
        "seed": seed,
        "versions": versions,
    }


def reconstruct(gates, witness):
    """The physical ops from the translated gates and the witness alone (deterministic)."""
    els = elements(gates)
    layout = list(witness["initial_layout"])
    out = []

    def phys(g, lay):
        bg = {"op": g["op"], "q": [lay[q] for q in g["q"]]}
        if "angle" in g:
            bg["angle"] = g["angle"]
        if g["op"] == "measure":
            bg["c"] = g["c"]
        return bg

    def swap_in(lay, p, q):
        for l, pp in enumerate(lay):
            if pp == p:
                lay[l] = q
            elif pp == q:
                lay[l] = p

    for entry in witness["order"]:
        if "swap" in entry:
            p, q = entry["swap"]
            out.append({"op": "swap", "q": [p, q]})
            swap_in(layout, p, q)
            continue
        el = els[entry["e"]]
        if "g" in el:
            out.append(phys(gates[el["g"]], layout))
        else:
            lay2 = list(layout)
            body = []
            for b in witness["blocks"][str(entry["e"])]:
                if "swap" in b:
                    p, q = b["swap"]
                    body.append({"op": "swap", "q": [p, q]})
                    swap_in(lay2, p, q)
                else:
                    body.append(phys(gates[b["g"]], lay2))
            out.append({"if": el["if"], "body": body})
    return out, layout


# --- the final physical circuit and its bound

def expand_swaps(phys_ops, basis):
    """Every routing swap replaced by the table's `swap` entry on its physical edge."""
    sw_gates, _ = decomp.table(basis)["swap"]
    out = []
    for pop in phys_ops:
        if "if" in pop:
            out.append({"if": pop["if"], "body": expand_swaps(pop["body"], basis)})
        elif pop["op"] == "swap":
            p, q = pop["q"]
            for name, roles, f in sw_gates:
                bg = {"op": name, "q": [(p, q)[r] for r in roles]}
                if f is not None:
                    bg["angle"] = decomp.frac_str(f)
                out.append(bg)
        else:
            out.append(dict(pop))
    return out


def flat_ops(phys_ops):
    """Every basis op, block bodies included (a conditioned gate counts as executed)."""
    for pop in phys_ops:
        if "if" in pop:
            yield from pop["body"]
        else:
            yield pop


def used_qubits(phys_ops):
    s = set()
    for op in flat_ops(phys_ops):
        s.update(op["q"])
    return sorted(s)


def physical_counts(phys_ops, basis):
    """Counts per (op, physical qubit or edge) of the final physical circuit."""
    counts = {}
    for op in flat_ops(phys_ops):
        key = (op["op"], tuple(op["q"]))
        counts[key] = counts.get(key, 0) + 1
    return counts


def edge_rate(two, basis, p, q):
    tab = two[basis]
    k = f"{p},{q}"
    if k in tab:
        return Fraction(tab[k])
    k2 = f"{q},{p}"
    if k2 in tab:
        return Fraction(tab[k2])
    raise KeyError(f"no calibration for edge {p},{q}")


def physical_bound(phys_ops, basis, target, final_layout, n_data, delta):
    """δ + Σ over the physical operations of their rates (exact), plus the n data readouts at their
    final physical positions; mid-circuit measurements take the readout rate of their physical
    qubit (the labelled assumption). Returns a dict with the figure, the parts and the edge flags."""
    cal = target["calibration"]
    one, two, ro = cal["one_qubit_gate_error"], cal["two_qubit_gate_error"], cal["readout_error"]
    terms = {"rz": Fraction(0), "sx": Fraction(0), "x": Fraction(0), basis: Fraction(0), "measure": Fraction(0), "data_readout": Fraction(0)}
    counts = {"rz": 0, "sx": 0, "x": 0, basis: 0, "measure": 0, "data_readout": n_data}
    vacuous_edges = []
    for op in flat_ops(phys_ops):
        name = op["op"]
        if name in ONE_Q:
            terms[name] += Fraction(one[name][str(op["q"][0])])
            counts[name] += 1
        elif name in TWO_Q:
            r = edge_rate(two, basis, *op["q"])
            terms[name] += r
            counts[name] += 1
            if r >= 1:
                vacuous_edges.append(list(op["q"]))
        elif name == "measure":
            terms["measure"] += Fraction(ro[str(op["q"][0])])
            counts["measure"] += 1
        else:
            raise ValueError(name)
    data_phys = [final_layout[l] for l in range(n_data)]
    for p in data_phys:
        terms["data_readout"] += Fraction(ro[str(p)])
    total = sum(terms.values())
    bound = Fraction(delta) + total
    return {"delta": Fraction(delta), "bound": bound, "vacuous": bound >= 1, "sum": total,
            "terms": terms, "counts": counts, "uses_error_1_edge": bool(vacuous_edges),
            "error_1_edges": sorted({tuple(sorted(e)) for e in vacuous_edges}),
            "data_physical": data_phys, "used_qubits": used_qubits(phys_ops)}


# --- the pipeline for one seed and the seed search

def versions_dict():
    import qiskit
    import qiskit_aer
    import qiskit_ibm_runtime
    return {"qiskit": qiskit.__version__, "qiskit_aer": qiskit_aer.__version__,
            "qiskit_ibm_runtime": qiskit_ibm_runtime.__version__, "transpile_py": "hw/transpile.py (Stage 25a)",
            "passes": "SabreLayout(coupling_map, seed) alone in a PassManager (qiskit 2.6.2)"}


def pipeline(circ, basis, backend, target, seed, delta):
    """Translate, route with `seed`, extract, witness, reconstruct (checked), expand the swaps,
    bound. Returns a dict with everything or raises WitnessError."""
    n = circ["n_data"] + circ["n_anc"]
    gates = decomp.translate(circ, basis)
    n_bits = decomp.n_bits_of(circ)
    tqc = decomp.to_qiskit(gates, n, n_bits)
    cm = backend.target.build_coupling_map()
    tq = route(tqc, cm, seed)
    phys = extract(tq)
    initial = list(tq.layout.initial_index_layout(filter_ancillas=True))
    w = witness_of(gates, phys, initial, seed, basis, target["name"], versions_dict(), n)
    rec, final = reconstruct(gates, w)
    if rec != phys:
        raise WitnessError("reconstruction differs from the physical circuit")
    if final != w["final_layout"]:
        raise WitnessError("final layout of the reconstruction differs from the witness")
    qfinal = list(tq.layout.final_index_layout(filter_ancillas=True))
    if qfinal != final:
        raise WitnessError(f"final layout differs from Qiskit's: {final[:6]}… vs {qfinal[:6]}…")
    edges = set(cm.get_edges())
    for op in flat_ops(phys):
        if op["op"] in TWO_Q + ("swap",) and tuple(op["q"]) not in edges and tuple(reversed(op["q"])) not in edges:
            raise WitnessError(f"two-qubit op {op} not on a coupling edge")
    final_phys = expand_swaps(phys, basis)
    bound = physical_bound(final_phys, basis, target, final, circ["n_data"], delta)
    return {"gates": gates, "n": n, "n_bits": n_bits, "translated_qc": tqc, "routed_qc": tq, "phys": phys,
            "witness": w, "final_phys": final_phys, "bound": bound, "device_width": tq.num_qubits}


def seed_search(circ, basis, backend, target, seeds, delta):
    """Every seed's figure; the choice is the least bound (ties: the smallest seed)."""
    trials, best = [], None
    for s in seeds:
        r = pipeline(circ, basis, backend, target, s, delta)
        b = r["bound"]
        trials.append({"seed": s, "bound": decomp.frac_str(b["bound"]), "bound_float": float(b["bound"]),
                       "vacuous": b["vacuous"], "uses_error_1_edge": b["uses_error_1_edge"],
                       "swaps": r["witness"]["swaps"], "used_qubits": len(b["used_qubits"]),
                       "two_qubit": b["counts"][basis]})
        if best is None or b["bound"] < best["bound"]["bound"]:
            best = r
    return best, trials


def to_qiskit_physical(final_phys, width, n_bits):
    """A Qiskit circuit of the final physical ops on `width` qubits (for the QASM 3 export)."""
    from qiskit import ClassicalRegister, QuantumCircuit, QuantumRegister
    qc = QuantumCircuit(QuantumRegister(width, "q"), ClassicalRegister(max(1, n_bits), "c"))
    for pop in final_phys:
        if "if" in pop:
            with qc.if_test((qc.clbits[pop["if"]], 1)):
                for b in pop["body"]:
                    decomp.apply_basis_gate(qc, b)
        else:
            decomp.apply_basis_gate(qc, pop)
    return qc
