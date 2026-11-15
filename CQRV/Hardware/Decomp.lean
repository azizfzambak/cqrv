module

public import CQRV.Circuit.IR
public import CQRV.Hardware.Bound
public import Mathlib.Data.Rat.Defs

/-!
# CQRV.Hardware.Decomp

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26a, Track C) — the basis gates of the hardware
targets, their embedding in the IR, the decomposition table of `hw/decomp.py` as Lean data, and
the translation of an IR circuit. Physlib-free (the data side; the proofs are
`CQRV.Hardware.DecompSound`).

**The embedding.** Every basis gate is an IR gate list up to a global phase:
`sx = h s h` exactly as matrices, `rz a k` (the angle `2πa/2^k`) is `e^{−iπa/2^k} · p a k`, and
`x`, `cz`, `cx = cnot` are IR gates. `BasisGate.expand` is that list; `BasisGate.embedPhase` is
the phase, in turns, by which the expansion differs from the basis gate's matrix
(`expand (rz a k) = e^{2πi · a/2^(k+1)} · rz a k`; `0` for the others).

**The table** (`decompTable`, entry for entry the table of `hw/decomp.py`): `h ↦ rz(1/4) sx rz(1/4)`
with phase `−1/8`; `s sdg t tdg z ↦ rz` with phases `−1/8, 1/8, −1/16, 1/16, −1/4`; `x ↦ x`;
`p a k ↦ rz a k` with phase `−a/2^(k+1)`; `cnot ↦ h(t) cz h(t)` (phase `−1/4`) in the cz basis
and `cx` in the cx basis; `cz ↦ cz` in the cz basis and `h(b) cx h(b)` (phase `−1/4`) in the cx
basis; `cp a k` by the five-gate decomposition of `Circuit.decomposeCp` through the entries;
`swap ↦ cnot cnot(reversed) cnot` (`swapEntry`, for the routing of 26b). The phase of an entry
is the one of the basis matrices: the product of the basis matrices equals `e^{2πi·phase}` times
the IR gate's matrix (`hw/decomp.py`'s `check_table`). The phase of the **expanded** IR list is
`Entry.irPhase = phase + Σ embedPhase` — the form `decomp_sound` proves; the two differ because
`expand (rz a k) = p a k` carries no phase. A conditioned gate keeps its condition on every basis
gate (`ifBit j` on each); `measure` is kept; `alloc` / `free` vanish.

**Conditioned gates and well-formedness.** `Circuit.WF` allows under `ifBit` only Clifford gates
(`Gate.isClifford`: `h s sdg x z cnot cz`, `p a k` iff `2^k ∣ 4a`, `cp a k` iff `2^k ∣ 2a`). The
expansion of a conditioned Clifford gate is Clifford gate by gate (`h` and `s` are, `rz 1 2 = p 1 2`
is, the `p a (k+1)` of a Clifford `cp a k` is), so the translation of a well-formed circuit is
well formed (`translate_wf`). A conditioned `rz a k` with a non-Clifford angle expands to a
conditioned non-Clifford `p a k`, which no well-formed IR circuit contains — exactly as in the IR;
the table never produces one from a well-formed circuit.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV

/-- PHASE2_SPEC §C.3 — the basis gates of the targets (`rz` with the angle `2πa/2^k`), the
measurement and the conditioned gate. -/
inductive BasisGate where
  | rz (a : Int) (k : Nat) (q : Qubit)
  | sx (q : Qubit)
  | x (q : Qubit)
  | cz (a b : Qubit)
  | cx (c t : Qubit)
  | measure (q : Qubit) (j : Nat)
  | ifBit (j : Nat) (g : BasisGate)
  deriving Repr, DecidableEq, Inhabited

namespace BasisGate

/-- PHASE2_SPEC §C.3 — the embedding in the IR: `sx = h s h`, `rz a k ↦ p a k` (up to the phase
`embedPhase`), `cx ↦ cnot`; `ifBit` maps structurally (a conditioned multi-gate expansion is the
list of conditioned IR gates). -/
def expand : BasisGate → List Gate
  | .rz a k q => [.p a k q]
  | .sx q => [.h q, .s q, .h q]
  | .x q => [.x q]
  | .cz a b => [.cz a b]
  | .cx c t => [.cnot c t]
  | .measure q j => [.measure q j]
  | .ifBit j g => g.expand.map (Gate.ifBit j)

/-- The phase (in turns) by which `expand g` differs from the basis gate's matrix:
`p a k = e^{2πi·a/2^(k+1)} · rz a k`, the others exact. -/
def embedPhase : BasisGate → ℚ
  | .rz a k _ => (a : ℚ) / 2 ^ (k + 1)
  | .ifBit _ g => g.embedPhase
  | _ => 0

/-- The qubits of a basis gate. -/
def qubits : BasisGate → List Qubit
  | .rz _ _ q | .sx q | .x q | .measure q _ => [q]
  | .cz a b => [a, b]
  | .cx c t => [c, t]
  | .ifBit _ g => g.qubits

/-- The name of a basis gate, as `hw/decomp.py` prints it. -/
def opName : BasisGate → String
  | .rz _ _ _ => "rz" | .sx _ => "sx" | .x _ => "x" | .cz _ _ => "cz" | .cx _ _ => "cx"
  | .measure _ _ => "measure" | .ifBit _ g => g.opName

end BasisGate

/-- One table entry: the basis gates and the phase (in turns) with
`product of basis matrices = e^{2πi·phase} · IR matrix`. -/
structure Entry where
  gates : List BasisGate
  phase : ℚ
  deriving Repr, DecidableEq

/-- The phase of the **expanded** IR list: `phase + Σ embedPhase` (what `decomp_sound` proves). -/
def Entry.irPhase (e : Entry) : ℚ := e.phase + (e.gates.map BasisGate.embedPhase).sum

/-- The entry `h ↦ rz(1/4) sx rz(1/4)`; its phase is `−1/8`. -/
def hGates (q : Qubit) : List BasisGate := [.rz 1 2 q, .sx q, .rz 1 2 q]

def hPhase : ℚ := -1 / 8

/-- `cnot c t`: `cx` itself, or `h(t) cz h(t)` (phase `2 · hPhase = −1/4`). -/
def cnotEntry : TargetBasis → Qubit → Qubit → Entry
  | .cx, c, t => ⟨[.cx c t], 0⟩
  | .cz, c, t => ⟨hGates t ++ [.cz c t] ++ hGates t, 2 * hPhase⟩

/-- `cz a b`: `cz` itself, or `h(b) cx h(b)` (phase `−1/4`). -/
def czEntry : TargetBasis → Qubit → Qubit → Entry
  | .cz, a, b => ⟨[.cz a b], 0⟩
  | .cx, a, b => ⟨hGates b ++ [.cx a b] ++ hGates b, 2 * hPhase⟩

/-- The routing swap (Stage 26b): `cnot p q; cnot q p; cnot p q` through the basis' entry. -/
def swapEntry (b : TargetBasis) (p q : Qubit) : Entry :=
  let c := cnotEntry b p q
  let c' := cnotEntry b q p
  ⟨c.gates ++ c'.gates ++ c.gates, 3 * c.phase⟩

/-- `p a k ↦ rz a k`, phase `−a/2^(k+1)` (`rz(θ) = e^{−iθ/2} p(θ)`). -/
def pEntry (a : Int) (k : Nat) (q : Qubit) : Entry :=
  ⟨[.rz a k q], -((a : ℚ) / 2 ^ (k + 1))⟩

/-- `cp a k c t` by the five-gate decomposition `p a (k+1) c; p a (k+1) t; cnot c t;
p (−a) (k+1) t; cnot c t` (`Circuit.decomposeCp`), each piece through its entry; the phase is the
sum of the pieces' (`−g/2 − g/2 + cnot + g/2 + cnot` with `g = a/2^(k+1)`). -/
def cpEntry (b : TargetBasis) (a : Int) (k : Nat) (c t : Qubit) : Entry :=
  let g : ℚ := (a : ℚ) / 2 ^ (k + 1)
  let cn := cnotEntry b c t
  ⟨[.rz a (k + 1) c, .rz a (k + 1) t] ++ cn.gates ++ [.rz (-a) (k + 1) t] ++ cn.gates,
   -g / 2 + 2 * cn.phase⟩

/-- PHASE2_SPEC §C.3 — the decomposition table of `hw/decomp.py`, entry for entry. `measure` is
kept, `ifBit j g` is `g`'s entry with `ifBit j` on every basis gate, `alloc` / `free` vanish. -/
def decompTable (b : TargetBasis) : Gate → Entry
  | .h q => ⟨hGates q, hPhase⟩
  | .s q => ⟨[.rz 1 2 q], -1 / 8⟩
  | .sdg q => ⟨[.rz (-1) 2 q], 1 / 8⟩
  | .t q => ⟨[.rz 1 3 q], -1 / 16⟩
  | .tdg q => ⟨[.rz (-1) 3 q], 1 / 16⟩
  | .z q => ⟨[.rz 1 1 q], -1 / 4⟩
  | .x q => ⟨[.x q], 0⟩
  | .cnot c t => cnotEntry b c t
  | .cz p q => czEntry b p q
  | .p a k q => pEntry a k q
  | .cp a k c t => cpEntry b a k c t
  | .measure q j => ⟨[.measure q j], 0⟩
  | .ifBit j g => let e := decompTable b g; ⟨e.gates.map (BasisGate.ifBit j), e.phase⟩
  | .alloc _ => ⟨[], 0⟩
  | .free _ => ⟨[], 0⟩

/-- The IR expansion of one gate's entry. -/
def expansion (b : TargetBasis) (g : Gate) : List Gate :=
  (decompTable b g).gates.flatMap BasisGate.expand

theorem expansion_ifBit (b : TargetBasis) (j : ℕ) (g : Gate) :
    expansion b (.ifBit j g) = (expansion b g).map (Gate.ifBit j) := by
  simp only [expansion, decompTable]
  induction (decompTable b g).gates with
  | nil => rfl
  | cons bg l ih => simp [List.flatMap_cons, List.map_append, ih, BasisGate.expand]

/-- PHASE2_SPEC §C.3 — the translation of a circuit, gate by gate, conditions kept. -/
def translate (b : TargetBasis) (C : Circuit) : List BasisGate :=
  C.gates.flatMap fun g => (decompTable b g).gates

/-- The translated circuit, read back as an IR circuit through the embedding. -/
def translateCircuit (b : TargetBasis) (C : Circuit) : Circuit :=
  ⟨C.nData, C.gates.flatMap (expansion b)⟩

theorem translateCircuit_gates (b : TargetBasis) (C : Circuit) :
    (translateCircuit b C).gates = (translate b C).flatMap BasisGate.expand := by
  simp only [translateCircuit, translate]
  induction C.gates with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons, List.flatMap_append, ih, expansion]

/-! ## The table as JSON (`cqr hw table`) -/

open Lean in
/-- A basis gate on the symbolic qubits `data 0` (role 0) and `data 1` (role 1) as
`{op, q: [roles], angle?}`, the format of `hw/decomp.py`. -/
def BasisGate.toJson : BasisGate → Json
  | .rz a k q => Json.mkObj [("op", "rz"), ("q", Json.arr #[roleOf q]),
      ("angle", ratStr ((a : Rat) / 2 ^ k))]
  | .sx q => Json.mkObj [("op", "sx"), ("q", Json.arr #[roleOf q])]
  | .x q => Json.mkObj [("op", "x"), ("q", Json.arr #[roleOf q])]
  | .cz a b => Json.mkObj [("op", "cz"), ("q", Json.arr #[roleOf a, roleOf b])]
  | .cx c t => Json.mkObj [("op", "cx"), ("q", Json.arr #[roleOf c, roleOf t])]
  | .measure q j => Json.mkObj [("op", "measure"), ("q", Json.arr #[roleOf q]), ("c", j)]
  | .ifBit j g => match g.toJson with
    | .obj kvs => .obj (kvs.insert "if" (Lean.toJson j))
    | js => js
where
  roleOf : Qubit → Json
    | .data i => Lean.toJson i
    | .anc i => Lean.toJson (i + 100)

open Lean in
def Entry.toJson (e : Entry) : Json :=
  Json.mkObj [("gates", Json.arr (e.gates.map BasisGate.toJson).toArray), ("phase", ratStr e.phase)]

/-- The angles `(a, k)` at which `hw/decomp.py`'s `check_table` and the comparison sample `p` and
`cp`. -/
def sampleAngles : List (Int × Nat) := [(1, 1), (1, 2), (-1, 3), (3, 3), (5, 4), (-7, 5), (1, 8), (0, 1)]

open Lean in
/-- PHASE2_SPEC §C.3 — the table of a basis as JSON, in `hw/decomp.py --json`'s format: the
fixed entries on `data 0` / `data 1`, `p a k` and `cp a k` at `sampleAngles`, and `swap`. -/
def tableJson (b : TargetBasis) : Json :=
  let q0 : Qubit := .data 0
  let q1 : Qubit := .data 1
  let fixed : List (String × Gate) :=
    [("h", .h q0), ("s", .s q0), ("sdg", .sdg q0), ("t", .t q0), ("tdg", .tdg q0), ("z", .z q0),
     ("x", .x q0), ("cnot", .cnot q0 q1), ("cz", .cz q0 q1)]
  let ps := sampleAngles.map fun (a, k) => (s!"p {a} {k}", Gate.p a k q0)
  let cps := sampleAngles.map fun (a, k) => (s!"cp {a} {k}", Gate.cp a k q0 q1)
  let entries := (fixed ++ ps ++ cps).map fun (name, g) => (name, (decompTable b g).toJson)
  Json.mkObj [("basis", b.twoQubit), ("entries", Json.mkObj (entries ++ [("swap", (swapEntry b q0 q1).toJson)]))]

end CQRV.Hardware
