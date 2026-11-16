module

public import CQRV.Hardware.Check
public import CQRV.Hardware.PhysGrade
public import CQRV.Hardware.SelectPhys
public import CQRV.Certify.Generate

/-!
# CQRV.Hardware.CheckGen

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c1b, L4) — the generator of the per-instance
hardware checks, `cqr hw check --artifact DIR --target FILE`, Physlib-free.

It reads an artifact's `logical.json`, `witness.json`, `physical.json` and `manifest.json` and the
target file, re-checks three hashes (the logical circuit against the manifest's `logical_circuit`,
through both the file and the Lean literal's own `circuitHash`; the witness; the target snapshot
through 24a's `HardwareTarget`), compacts the witness and the physical circuit through the
manifest's `used_qubits`, and prints `examples/hw_checks/<artifact>/Check.lean`: the literals and
the kernel-checked theorems (`recon`, `phys_wf`, `phys_nBits`, `c_wf`, `edges_ok`, `init_eq`,
`phys_channel`, `phys_zero`), two tampering theorems and the `#print axioms` lines. The printer is
unverified, as the certificate generator's is: the kernel checks the file.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV Lean

/-! ## Reading the artifact -/

/-- A flat qubit index of the JSON export: `i < nData` is `data i`, the rest are ancillae. -/
def qubitOfIndex (nData i : Nat) : Qubit := if i < nData then .data i else .anc (i - nData)

/-- One IR gate from its flat JSON object (`Circuit.gateJson`'s format). -/
def gateOfJson (nData : Nat) (j : Json) : Except String Gate := do
  let op ← strField "gate" j "op"
  let qs ← natList "gate.q" (← field "gate" j "q")
  let q (i : Nat) : Except String Qubit :=
    match qs[i]? with
    | some x => pure (qubitOfIndex nData x)
    | none => throw s!"gate {op}: missing qubit {i}"
  let base ← match op with
    | "h" => pure <| Gate.h (← q 0)
    | "s" => pure <| Gate.s (← q 0)
    | "sdg" => pure <| Gate.sdg (← q 0)
    | "t" => pure <| Gate.t (← q 0)
    | "tdg" => pure <| Gate.tdg (← q 0)
    | "x" => pure <| Gate.x (← q 0)
    | "z" => pure <| Gate.z (← q 0)
    | "cnot" => pure <| Gate.cnot (← q 0) (← q 1)
    | "cz" => pure <| Gate.cz (← q 0) (← q 1)
    | "alloc" => pure <| Gate.alloc (← q 0)
    | "free" => pure <| Gate.free (← q 0)
    | "measure" => pure <| Gate.measure (← q 0) (← natField "gate" j "c")
    | "p" =>
      let a ← (← field "gate" j "a").getInt?.mapError fun _ => "gate p: `a` must be an integer"
      pure <| Gate.p a (← natField "gate" j "k") (← q 0)
    | "cp" =>
      let a ← (← field "gate" j "a").getInt?.mapError fun _ => "gate cp: `a` must be an integer"
      pure <| Gate.cp a (← natField "gate" j "k") (← q 0) (← q 1)
    | other => throw s!"gate: unknown op {other}"
  match j.getObjVal? "if" with
  | .ok c => return .ifBit (← c.getNat?.mapError fun _ => "gate: `if` must be a natural number") base
  | .error _ => return base

/-- The logical circuit from `logical.json` (`Circuit.toJson`'s format). -/
def circuitOfJson (j : Json) : Except String Circuit := do
  let nData ← natField "circuit" j "n_data"
  let gates ← (← (← field "circuit" j "gates").getArr?.mapError fun _ => "circuit: gates must be an array").toList.mapM
    (gateOfJson nData)
  return ⟨nData, gates⟩

/-- An angle in turns, `"a/2^k"` or an integer, as the pair `(a, k)` of `rz a k`. -/
def angleOfString (s : String) : Except String (Int × Nat) := do
  let parts := s.splitOn "/"
  match parts with
  | [num] =>
    let a ← match num.toInt? with | some a => pure a | none => throw s!"angle: {s}"
    return (a, 0)
  | [num, den] =>
    let a ← match num.toInt? with | some a => pure a | none => throw s!"angle: {s}"
    let d ← match den.toNat? with | some d => pure d | none => throw s!"angle: {s}"
    let k := Nat.log2 d
    unless 2 ^ k == d do throw s!"angle: the denominator of {s} is not a power of two"
    return (a, k)
  | _ => throw s!"angle: {s}"

/-- One physical basis gate (`physical.json`, the ops `hw/transpile.py` prints), its device
qubits compacted through `used`. -/
def basisGateOfJson (used : List Nat) (j : Json) : Except String BasisGate := do
  let op ← strField "physical" j "op"
  let qs ← natList "physical.q" (← field "physical" j "q")
  let q (i : Nat) : Except String Qubit :=
    match qs[i]? with
    | some x => return .data (← compactOf used "physical" x)
    | none => throw s!"physical {op}: missing qubit {i}"
  match op with
  | "rz" =>
    let (a, k) ← angleOfString (← strField "physical" j "angle")
    return .rz a k (← q 0)
  | "sx" => return .sx (← q 0)
  | "x" => return .x (← q 0)
  | "cz" => return .cz (← q 0) (← q 1)
  | "cx" => return .cx (← q 0) (← q 1)
  | "measure" => return .measure (← q 0) (← natField "physical" j "c")
  | other => throw s!"physical: unknown op {other}"

/-- The physical circuit: plain ops and `{if, body}` blocks, every gate of a block conditioned. -/
def physOfJson (used : List Nat) (j : Json) : Except String (List BasisGate) := do
  let ops ← (j.getArr?.mapError fun _ => "physical: not an array")
  let parts ← ops.toList.mapM fun op => do
    match op.getObjVal? "if" with
    | .ok c =>
      let bit ← c.getNat?.mapError fun _ => "physical: `if` must be a natural number"
      let body ← (← field "physical" op "body").getArr?.mapError fun _ => "physical: body must be an array"
      let gs ← body.toList.mapM (basisGateOfJson used)
      return gs.map (BasisGate.ifBit bit)
    | .error _ => return [← basisGateOfJson used op]
  return parts.flatMap id

/-- What the generator takes from `manifest.json`. -/
structure ManifestData where
  instance_ : String
  target : String
  basis : TargetBasis
  usedQubits : List Nat
  logicalHash : String
  witnessHash : String
  targetHash : String
  uncompute : String

def manifestOfJson (j : Json) : Except String ManifestData := do
  let instance_ ← strField "manifest" j "instance"
  let target ← strField "manifest" j "target"
  let basis ← match ← strField "manifest" j "basis" with
    | "cz" => pure TargetBasis.cz
    | "cx" => pure TargetBasis.cx
    | b => throw s!"manifest: basis {b}"
  let layout ← field "manifest" j "layout"
  let usedQubits ← natList "manifest.layout.used_qubits" (← field "manifest.layout" layout "used_qubits")
  let hashes ← field "manifest" j "hashes"
  return { instance_, target, basis, usedQubits, uncompute := ← strField "manifest" j "uncompute",
           logicalHash := ← strField "manifest.hashes" hashes "logical_circuit",
           witnessHash := ← strField "manifest.hashes" hashes "witness",
           targetHash := ← strField "manifest.hashes" hashes "target_snapshot" }

/-! ## Printing the check file -/

def basisGateLit : BasisGate → String
  | .rz a k q => s!".rz {Certify.intLit a} {k} {Certify.qubitLit q}"
  | .sx q => s!".sx {Certify.qubitLit q}"
  | .x q => s!".x {Certify.qubitLit q}"
  | .cz a b => s!".cz {Certify.qubitLit a} {Certify.qubitLit b}"
  | .cx c t => s!".cx {Certify.qubitLit c} {Certify.qubitLit t}"
  | .measure q j => s!".measure {Certify.qubitLit q} {j}"
  | .ifBit j g => s!".ifBit {j} ({basisGateLit g})"

def orderEntryLit : OrderEntry → String
  | .elem i => s!".elem {i}"
  | .swap p q => s!".swap {p} {q}"

def blockEntryLit : BlockEntry → String
  | .gate k => s!".gate {k}"
  | .swap p q => s!".swap {p} {q}"

def basisLit : TargetBasis → String
  | .cz => ".cz"
  | .cx => ".cx"

def witnessLit (w : Witness) : String :=
  s!"\{ basis := {basisLit w.basis}, nLogical := {w.nLogical}, initial := {w.initial}, final := {w.final},\n" ++
  s!"    order := [\n      {Certify.joinWrapped (w.order.map orderEntryLit) 10 "      "}],\n" ++
  s!"    blocks := [\n      {Certify.joinWrapped (w.blocks.map fun (i, body) => s!"({i}, [{", ".intercalate (body.map blockEntryLit)}])") 4 "      "}],\n" ++
  s!"    clbitMap := {w.clbitMap}, seed := {w.seed} }"

def edgesLit (edges : List (Nat × Nat)) : String :=
  Certify.joinWrapped (edges.map fun (a, b) => s!"({a}, {b})") 12 "    "

/-- A compact pair that is not an edge of the target, for the tampering test. -/
def offEdgePair (N : Nat) (dev : List Nat) (edges : List (Nat × Nat)) : Option (Nat × Nat) :=
  (List.range N).findSome? fun p => (List.range N).findSome? fun q =>
    if p == q then none
    else
      let a := dev.getD p 0
      let b := dev.getD q 0
      if edges.contains (a, b) || edges.contains (b, a) then none else some (p, q)

/-- A gate that differs from `G`'s first gate, for the tampering test. -/
def tamperGate (G : List BasisGate) : BasisGate :=
  match G.head? with
  | some (.sx _) => .x (.data 0)
  | _ => .sx (.data 0)

/-- The literals and the kernel-checked theorems of an artifact, inside a namespace (shared by the
check files and the physical certificate). -/
def checkBody (C : Circuit) (W : Witness) (G : List BasisGate) (dev : List Nat)
    (edges : List (Nat × Nat)) (b : TargetBasis) (targetFile : String) : String :=
  let n := C.nData
  let a := C.nAnc
  let N := dev.length
  let bb := N - (n + a)
  let reg := "(C.nData + (C.nAnc + bb))"
  let tamperEdges := match offEdgePair N dev edges with
    | some (p, q) =>
      s!"/-- A two-qubit gate on compact qubits {p}, {q} (device {dev.getD p 0}, {dev.getD q 0}), not an edge, is refused. -/\n" ++
      s!"theorem tamper_edges : edgesOk (G ++ [.{basisLit b |>.drop 1} (.data {p}) (.data {q})]) dev edges = false := by decide +kernel\n"
    | none => "-- every pair of used qubits is an edge: no off-edge tampering test\n"
  s!"/-- The logical circuit (`logical.json`): {C.gates.length} gates on {n} data qubits and {a} ancillae. -/
def C : Circuit := {Certify.circuitLit C}

/-- The witness (`witness.json`) on the compact register: {W.order.length} order entries, {W.blocks.length} blocks. -/
def W : Witness :=
  {witnessLit W}

/-- The physical circuit (`physical.json`) on the compact register: {G.length} basis gates. -/
def G : List BasisGate := [
    {Certify.joinWrapped (G.map basisGateLit) 6 "    "}]

/-- Compact qubit `i` is device qubit `dev[i]` (the manifest's `layout.used_qubits`). -/
def dev : List ℕ := {dev}

/-- The target's coupling map (`coupling_map` of `{targetFile}`, {edges.length} directed edges). -/
def edges : List (ℕ × ℕ) := [
    {edgesLit edges}]

/-- The idle qubits of the compact register. -/
abbrev bb : ℕ := {bb}

theorem nData_eq : C.nData = {n} := rfl
theorem nAnc_eq : C.nAnc = {a} := by decide +kernel
theorem reg_eq : {reg} = {N} := by decide +kernel
theorem c_wf : C.WF := by decide +kernel

/-- **`recon`**: the linear check reconstructs the artifact's physical circuit exactly (the kernel
evaluates `applyWitnessQ`). -/
theorem recon : applyWitnessQ {basisLit b} C W {reg} = .ok G := by rfl

theorem phys_wf : (physCircuit {reg} G).WF := by decide +kernel
theorem phys_nBits : (physCircuit {reg} G).nBits = C.nBits := by decide +kernel

/-- **`edges_ok`**: every two-qubit gate of `G` lies on a coupling edge of the target. -/
theorem edges_ok : edgesOk G dev edges = true := by decide +kernel

theorem init_layout : IsLayout {reg} (C.nData + C.nAnc) W.initial := by decide +kernel

/-- The initial layout as a permutation of the compact register. -/
noncomputable def σ₀ : Equiv.Perm (Fin {reg}) := layPerm _ (C.nData + C.nAnc) W.initial

theorem init_eq : W.initial = layOf {reg} (C.nData + C.nAnc) σ₀ := (layOf_layPerm _ _ _ init_layout).symm

/-- The final layout as a permutation: the SWAPs of the reconstruction applied to `σ₀`. -/
noncomputable def σf : Equiv.Perm (Fin {reg}) := finalPerm {basisLit b} C W _ σ₀

/-- **`phys_channel`** (`applyWitness_sound` at this instance, through `applyWitnessQ_ok`): on the
embedded input laid out by `σ₀`, the physical circuit gives the embedded output of `C` laid out by
`σf`, which extends the witness's final layout. -/
theorem phys_channel :
    W.final = layOf {reg} (C.nData + C.nAnc) σf ∧
      ∀ ρ : MState (Reg C.nData × Reg C.nAnc),
        channelDenote {reg} 0 (physCircuit {reg} G) (embed bb σ₀ ρ) =
          embed bb σf (channelDenote C.nData C.nAnc C ρ) :=
  applyWitnessQ_sound {basisLit b} C W bb c_wf G recon phys_wf phys_nBits σ₀ init_eq

/-- **`phys_zero`**: from the all-|0⟩ physical state (the state the device starts from), the
output is `σf`'s embedding of the logical output from |0⟩. -/
theorem phys_zero :
    channelDenote {reg} 0 (physCircuit {reg} G) (ancZero {reg} ⊗ᴹ ancZero 0) =
      embed bb σf (channelDenote C.nData C.nAnc C (ancZero C.nData ⊗ᴹ ancZero C.nAnc)) := by
  rw [← embed_zero bb σ₀]
  exact phys_channel.2 _

/-- `G` with its first gate changed is not the reconstruction. -/
theorem tamper_recon : applyWitnessQ {basisLit b} C W {reg} ≠ .ok (G.set 0 ({basisGateLit (tamperGate G)})) := by
  rw [recon]
  intro h
  exact absurd (Except.ok.inj h) (by decide +kernel)

{tamperEdges}"

/-- PHASE2_SPEC §C.3 (26c1b) — the text of `Check.lean` for one artifact. -/
def checkFile (name : String) (C : Circuit) (W : Witness) (G : List BasisGate) (dev : List Nat)
    (edges : List (Nat × Nat)) (b : TargetBasis) (targetName targetFile : String) (m : ManifestData)
    (physHash : String) : String :=
  let N := dev.length
  s!"import CQRV.Hardware.CheckSound

/-!
# Hardware check `{name}` (generated by `cqr hw check`; do not edit)

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c1b). The artifact `hw/artifacts/{name}/`:
the logical circuit `logical.json` (SHA3-256 `{m.logicalHash}`, the manifest's
`logical_circuit`, also the `circuitHash` of the literal `C`), the witness `witness.json`
(SHA3-256 `{m.witnessHash}`), the physical circuit `physical.json` (SHA3-256 `{physHash}`),
the target `{targetName}` (`{targetFile}`, snapshot `{m.targetHash}`), compacted to the
{N} used qubits `{dev}` (compact qubit `i` is device qubit `dev[i]`). Checked by `lake env lean`:
every theorem is the kernel's (`rfl`, `decide +kernel`). The link from `C` to the logical circuit
of the instance `{m.instance_}` is the hash above, which is untrusted; 26c2 adds the trusted link
for the certified instance. Nothing here is \"verified on hardware\": the physical circuit is
validated against the logical one (`phys_channel`), on the target's coupling map (`edges_ok`).
-/

set_option maxRecDepth 100000

namespace CQRV.HwCheck.«{name}»

open CQRV CQRV.Hardware
open scoped MState

{checkBody C W G dev edges b targetFile}
#print axioms phys_channel
#print axioms phys_zero

end CQRV.HwCheck.«{name}»
"

/-- The report of a generation: what was checked and where the file went. -/
structure CheckReport where
  name : String
  gates : Nat
  order : Nat
  physical : Nat
  usedQubits : Nat
  file : String

/-- PHASE2_SPEC §C.3 (26c1b) — read the artifact and the target, check the hashes, and produce the
check file's text. -/
def generateCheck (manifestText logicalText witnessText physicalText : String) (t : HardwareTarget)
    (targetFile : String) : Except String (String × CheckReport) := do
  let mj ← Json.parse manifestText
  let m ← manifestOfJson mj
  let lj ← Json.parse logicalText
  let C ← circuitOfJson lj
  -- the three hashes
  let fileHash := Certify.SHA3.sha3String lj.compress
  unless fileHash == m.logicalHash do
    throw s!"logical.json: SHA3-256 {fileHash} differs from the manifest's {m.logicalHash}"
  let litHash := Certify.circuitHash C
  unless litHash == m.logicalHash do
    throw s!"logical circuit: the Lean literal's circuitHash {litHash} differs from the manifest's {m.logicalHash}"
  let wj ← Json.parse witnessText
  let wHash := Certify.SHA3.sha3String wj.compress
  unless wHash == m.witnessHash do
    throw s!"witness.json: SHA3-256 {wHash} differs from the manifest's {m.witnessHash}"
  unless t.snapshotHash == m.targetHash do
    throw s!"target: snapshot hash {t.snapshotHash} differs from the manifest's {m.targetHash}"
  unless t.checkHash do
    throw s!"target: the calibration's SHA3-256 differs from snapshot.hash {t.snapshotHash}"
  unless t.name == m.target || true do pure ()
  let W ← Witness.ofJson wj m.usedQubits
  unless W.basis == m.basis do throw "witness: basis differs from the manifest's"
  let pj ← Json.parse physicalText
  let physHash := Certify.SHA3.sha3String pj.compress
  let G ← physOfJson m.usedQubits pj
  let name := s!"{m.instance_}__{m.target}"
  -- the target file is named from the manifest, not from the argument: the file is path-independent
  let _ := targetFile
  let text := checkFile name C W G m.usedQubits t.couplingMap m.basis t.name s!"hw/targets/{m.target}.json" m physHash
  return (text, { name, gates := C.gates.length, order := W.order.length, physical := G.length,
                  usedQubits := m.usedQubits.length, file := s!"examples/hw_checks/{name}/Check.lean" })

/-! ## The physical certificate (26c2, P2) -/

/-- A rational angle in turns `a / 2^k` as an OpenQASM 3 angle expression: `pi*num/den` with
`num/den = 2a / 2^k` in lowest terms (`rz(θ)`'s θ = 2π · turns). -/
def qasmAngle (a : Int) (k : Nat) : String :=
  let q : Rat := (2 * a : Int) / ((2 ^ k : Nat) : Rat)
  if q.den = 1 then s!"pi*{q.num}" else s!"pi*{q.num}/{q.den}"

/-- One basis gate as an OpenQASM 3 statement on the device qubits (`dev`). -/
def qasmGate (dev : List Nat) : BasisGate → String
  | .rz a k (.data q) => s!"rz({qasmAngle a k}) q[{dev.getD q 0}];"
  | .sx (.data q) => s!"sx q[{dev.getD q 0}];"
  | .x (.data q) => s!"x q[{dev.getD q 0}];"
  | .cz (.data p) (.data q) => s!"cz q[{dev.getD p 0}], q[{dev.getD q 0}];"
  | .cx (.data p) (.data q) => s!"cx q[{dev.getD p 0}], q[{dev.getD q 0}];"
  | .measure (.data q) j => s!"c[{j}] = measure q[{dev.getD q 0}];"
  | .ifBit j g => s!"if (c[{j}]) \{\n  {qasmGate dev g}\n}"
  | g => s!"// not a device gate: {repr g}"

/-- PHASE2_SPEC §C.3 (26c2) — the physical circuit as OpenQASM 3 text on the device (`width` qubits,
`nBits` classical bits): the file one would run (an unverified printer, as §5.3's; the Python check
parses it back to the artifact's gate list). -/
def qasmOf (G : List BasisGate) (dev : List Nat) (width nBits : Nat) : String :=
  s!"OPENQASM 3.0;\ninclude \"stdgates.inc\";\nbit[{max 1 nBits}] c;\nqubit[{width}] q;\n" ++
  String.intercalate "\n" (G.map (qasmGate dev)) ++ "\n"

/-- A `Durations` as a Lean literal (restricted to the used qubits). -/
def durationsLit (d : Durations) : String :=
  let tab (t : List (String × Rat)) : String :=
    "[" ++ ", ".intercalate (t.map fun (k, v) => s!"(\"{k}\", {ratStr v})") ++ "]"
  s!"\{ gates := [{", ".intercalate (d.gates.map fun (op, t) => s!"(\"{op}\", {tab t})")}],\n" ++
  s!"    measure := {tab d.measure} }"

/-- A `RateTable` as a Lean literal (restricted to the used qubits). -/
def rateTableLit (r : RateTable) : String :=
  let tab (t : List (String × Rat)) : String :=
    "[" ++ ", ".intercalate (t.map fun (k, v) => s!"(\"{k}\", {ratStr v})") ++ "]"
  s!"\{ one := [{", ".intercalate (r.one.map fun (op, t) => s!"(\"{op}\", {tab t})")}],\n" ++
  s!"    two := [{", ".intercalate (r.two.map fun (op, t) => s!"(\"{op}\", {tab t})")}],\n" ++
  s!"    readout := {tab r.readout} }"

def physGradeLit (g : PhysGrade) : String :=
  s!"⟨{g.qubits}, {g.twoQubit}, {g.midMeas}, {g.feedForward}, {ratStr g.depth}, {ratStr g.bound}, {g.vacuous}⟩"

/-- R3 — the status word of a passing emulator comparison. -/
def emulatorWord : String := "emulator_sanity_checked"

/-- The status words (P3): `logical_certified` (the committed certificate), `hardware_compatible`
(the edges and the capabilities the uncomputation mode needs), `physical_translation_validated`
(this file's theorems, sorry-free, three axioms), and `emulator_sanity_checked` only when the run
report of this artifact passed its check — named `emulator_validated` before revision R3
(REVIEW_RESPONSE_1 §4): the emulator's noise model is not of the (P-stoch) form, so a passing run is
a sanity check of the pipeline, not evidence for the premise. -/
def statusWords (hardwareCompatible : Bool) (emulatorPassed : Bool) : List String :=
  ["logical_certified"] ++ (if hardwareCompatible then ["hardware_compatible"] else []) ++
  ["physical_translation_validated"] ++ (if emulatorPassed then [emulatorWord] else [])

/-- R4 (REVIEW_RESPONSE_1 §4; paper v2 Table 1, §8.3) — the model premises every physical and
conditional manifest states, one sentence each: `ideal_device` (the physical statement only; the
conditional certificates replace it by `noise.premises`), `P-prep`, `P-ctrl`. One source of truth: the
Python checks assert the keys. -/
def modelPremisesJson (physical : Bool) : Json :=
  Json.mkObj ((if physical then [("ideal_device", Json.str "the device applies exactly the target's basis gates on its coupling map, without noise (the physical statement phys_realizes; a conditional certificate replaces this premise by noise.premises P-cal, P-stoch, P-ro, P-idle)")] else []) ++
    [("P-prep", Json.str "every qubit used, data and ancillae, starts in |0> exactly (phys_start: the all-|0> device state is the embedded logical |0>)"),
     ("P-ctrl", Json.str "mid-circuit outcomes are recorded and fed forward exactly and the classical bookkeeping (bits, layouts) is exact; the feed-forward latency L is an assumption used for the timing (PhysGrade) only")])

/-- The data of a physical certificate, for the file and the manifest. -/
structure PhysCertData where
  certName : String
  logicalCertNamespace : String
  logicalBody : String
  m : ManifestData
  /-- the logical certificate.json's SHA3-256 with `hashes.library` set to null
  (`Certify.certJsonModLibrary`; R5) -/
  certJsonHash : String
  /-- R5: `hashes.library` of the tree the certificate is generated in -/
  libHash : String
  physHash : String
  targetFileHash : String
  targetFile : String
  targetName : String
  C : Circuit
  W : Witness
  G : List BasisGate
  dev : List Nat
  edges : List (Nat × Nat)
  dataPhys : List Nat
  delta : Rat
  deltaExpr : String
  specExpr : String
  povmExpr : String
  gradeExpr : String
  deltaRealExpr : String
  durs : Durations
  rates : RateTable
  grades : List (Rat × PhysGrade)
  hardwareCompatible : Bool
  emulatorPassed : Bool
  emulatorNote : String

/-- PHASE2_SPEC §C.3 (26c2, P2) — the text of `PhysCert.lean`: self-contained — the committed
logical certificate's body verbatim (its `emitted`, its `cert`), the artifact's literals and
theorems (`checkBody`), the trusted link `emitted = C`, `RealizesExact` transferred to the
physical circuit from the all-|0⟩ state, and `PhysGrade` evaluated by the kernel at each stated
feed-forward latency. -/
def physCertFile (d : PhysCertData) (extra : String := "") (extraWords : List String := []) : String :=
  let reg := "(C.nData + (C.nAnc + bb))"
  let gradeThms := String.intercalate "\n" (d.grades.map fun (L, g) =>
    s!"/-- `PhysGrade` at the feed-forward latency L = {ratStr L} ns (an assumption, not a property of the device). -/\n" ++
    s!"theorem physGrade_L{(ratStr L).replace "/" "_"} : (physGrade durations rates {basisLit d.m.basis} dev G ({ratStr L} : Rat) dataPhys delta).toOption = some {physGradeLit g} := by decide +kernel\n")
  -- the generated imports are concatenated so that no source line of this module starts with `import`
  "import CQRV\n" ++ "import CQRV.Hardware.CheckSound\n" ++ "import CQRV.Hardware.PhysGrade\n" ++ s!"
/-!
# Physical certificate `{d.certName}` (generated by `cqr hw certify`; do not edit)

Report §5.3, §8.4, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c2). The committed logical certificate
`{d.logicalCertNamespace}` (certificate.json SHA3-256 modulo `hashes.library` `{d.certJsonHash}`; `circuit_hash`
`{d.m.logicalHash}`), re-derived verbatim below on its `emitted` literal, and the artifact
`hw/artifacts/{d.m.instance_}__{d.m.target}/` (`logical.json` SHA3-256 `{d.m.logicalHash}`,
`witness.json` `{d.m.witnessHash}`, `physical.json` `{d.physHash}`), on the target `{d.targetName}`
(`{d.targetFile}`: snapshot `{d.m.targetHash}`, file bytes SHA3-256 `{d.targetFileHash}` — the
durations are outside the snapshot hash), compacted to the {d.dev.length} used qubits `{d.dev}`.

**The trusted link** is `emitted_eq : emitted = C`, decided by the kernel: the artifact's logical
circuit is the certified circuit. **The physical statement** (`phys_realizes`): on an ideal device
with the target's gates and coupling map, started from all-|0⟩ on its used qubits, the physical
circuit realizes the specification with the certified δ, at the physical circuit's own grade.
**The grade** (`PhysGrade`) is evaluated by the kernel at the stated feed-forward latencies; the
bound is a sum of calibrated rates (reported, not certified: Stage 27 is the noise theorem).
Nothing here is \"verified on hardware\"; noise is not addressed. Status: {", ".intercalate (statusWords d.hardwareCompatible d.emulatorPassed ++ extraWords)}{if d.emulatorNote.isEmpty then "" else s!" ({d.emulatorNote})"}.
-/

set_option maxRecDepth 100000

{d.logicalBody}

namespace CQRV.PhysCert.«{d.certName}»

open CQRV CQRV.Hardware CQRV.Synthesis CQRV.Grover CQRV.Certify {d.logicalCertNamespace}
open scoped MState

{checkBody d.C d.W d.G d.dev d.edges d.m.basis d.targetFile}
/-- **The trusted link**: the artifact's logical circuit is the certificate's emitted circuit. -/
theorem emitted_eq : emitted = C := by decide +kernel

/-- The start state of the device, all-|0⟩, is the embedded logical |0⟩ for the initial layout. -/
theorem phys_start : embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc) = ancZero {reg} ⊗ᴹ ancZero 0 :=
  embed_zero bb σ₀

/-- **`phys_realizes`**: the certified realization transferred to the physical circuit
(`realizesExact_phys` through `emitted_eq`), from the all-|0⟩ physical state (`physGroverChannel`
prepares `embed bb σ₀ |0⟩`, which `phys_start` identifies), with the same decoding, at the physical
circuit's own grade. -/
theorem phys_realizes :
    ∃ σf' : Equiv.Perm (Fin {reg}), W.final = layOf {reg} (C.nData + C.nAnc) σf' ∧
      RealizesExact {d.specExpr} {d.povmExpr}
        (physGroverChannel bb σ₀ σf' (physCircuit {reg} G)) {d.deltaRealExpr}
        (Synthesis.grade (physCircuit {reg} G)) :=
  realizesExact_phys {basisLit d.m.basis} C W bb c_wf G (applyWitnessQ_ok _ _ c_wf _ _ _ recon) phys_wf
    phys_nBits σ₀ init_eq _ _ _ _ (emitted_eq ▸ cert.1)

/-- The durations of the target on the used qubits (ns, exact; `{d.targetFile}`). -/
def durations : Durations :=
  {durationsLit d.durs}

/-- The calibrated rates of the target on the used qubits (exact; the snapshot of `{d.targetFile}`). -/
def rates : RateTable :=
  {rateTableLit d.rates}

/-- The device qubits of the data register at the final layout. -/
def dataPhys : List ℕ := {d.dataPhys}

/-- The certified δ. -/
def delta : Rat := {d.deltaExpr}

{gradeThms}{extra}
#print axioms emitted_eq
#print axioms phys_channel
#print axioms phys_zero
#print axioms phys_realizes

end CQRV.PhysCert.«{d.certName}»
"

/-- The logical certificate's body: from its `namespace` line to its `end` line. -/
def logicalBodyOf (certText : String) : Except String (String × String) := do
  let lines := certText.splitOn "\n"
  let some nsLine := lines.find? (·.startsWith "namespace ") | throw "Cert.lean: no namespace line"
  let ns := (nsLine.drop "namespace ".length).trimAscii.toString
  let some startIdx := lines.idxOf? nsLine | throw "Cert.lean: namespace line not found"
  let endMarker := s!"end {ns}"
  let some endIdx := lines.idxOf? endMarker | throw s!"Cert.lean: no `{endMarker}` line"
  if endIdx ≤ startIdx then throw "Cert.lean: malformed"
  return (ns, "\n".intercalate ((lines.drop startIdx).take (endIdx - startIdx + 1)))

/-- The result of a run report (`docs/hw_runs/<artifact>.json`): `check.result`. -/
def runResultOf (runText : Option String) : Except String (Bool × String) := do
  match runText with
  | none => return (false, "no emulator run report")
  | some t =>
    let j ← Json.parse t
    let r ← strField "run.check" (← field "run" j "check") "result"
    if r == "passes" then return (true, "")
    else if r.startsWith "vacuous" then return (false, "vacuous bound, not tested")
    else return (false, s!"emulator run: {r}")

/-- The feed-forward latencies a certificate evaluates: 0 and the one requested (deduplicated). -/
def latenciesOf (L : Rat) : List Rat := if L == 0 then [0] else [0, L]

/-- Everything the physical certificate's outputs are built from (26c2; split out in 27b2 so the
conditional certificate reuses the reading and the checks). -/
structure PhysCertPrep where
  d : PhysCertData
  grades : List (Rat × PhysGrade)
  certCircuit : String
  deltaStr : String
  uncompute : String
  nsAscii : String
  edgesOkB : Bool
  capsOk : Bool
  deviceWidth : Nat
  nBits : Nat

/-- PHASE2_SPEC §C.3 (26c2, P2) — read everything, check the hashes (the artifact's three as
`generateCheck`, the logical certificate's `circuit_hash` against the manifest's `logical_circuit`,
the target's snapshot and its file bytes), and compute the grades. R5 (DECISIONS.md 2026-11-16): the
artifact's `certificate_json` is the historical full hash of the certificate.json it was transpiled
from and is no longer compared; the physical files cite the certificate by
`Certify.certJsonModLibrary` and carry `libHash` (`hashes.library`). -/
def preparePhysCert (certName : String) (certLeanText certJsonText : String)
    (manifestText logicalText witnessText physicalText : String) (t : HardwareTarget)
    (targetFile targetText : String) (L : Rat) (deviceWidth : Nat) (dataPhys : List Nat)
    (nBits : Nat) (runText : Option String) (libHash : String) : Except String PhysCertPrep := do
  let mj ← Json.parse manifestText
  let m ← manifestOfJson mj
  let lj ← Json.parse logicalText
  let C ← circuitOfJson lj
  unless Certify.SHA3.sha3String lj.compress == m.logicalHash do
    throw s!"logical.json: SHA3-256 differs from the manifest's {m.logicalHash}"
  unless Certify.circuitHash C == m.logicalHash do
    throw "logical circuit: the Lean literal's circuitHash differs from the manifest's"
  let wj ← Json.parse witnessText
  unless Certify.SHA3.sha3String wj.compress == m.witnessHash do throw "witness.json: SHA3-256 differs from the manifest's"
  unless t.snapshotHash == m.targetHash do throw "target: snapshot hash differs from the manifest's"
  unless t.checkHash do throw "target: the calibration's SHA3-256 differs from snapshot.hash"
  -- the logical certificate
  let cj ← Json.parse certJsonText
  let certJsonHash := Certify.SHA3.sha3String (Certify.certJsonModLibrary certJsonText)
  let hashes ← field "manifest" mj "hashes"
  -- the artifact's `certificate_json` is the full SHA3-256 of the certificate.json it was transpiled from, a
  -- historical record (null for an artifact made before its certificate: hw_n2, hw_n3, 25a); since R5 it is
  -- checked for shape only — the link is `circuit_hash = logical_circuit`, checked below
  match (← field "manifest.hashes" hashes "certificate_json") with
  | .null => pure ()
  | mj' =>
    let _ ← mj'.getStr?.mapError fun _ => "manifest.hashes: `certificate_json` must be a string or null"
  let certCircuit ← strField "certificate.hashes" (← field "certificate" cj "hashes") "circuit"
  unless certCircuit == m.logicalHash do
    throw s!"certificate.json: circuit_hash {certCircuit} differs from the artifact's logical circuit {m.logicalHash}"
  let spec ← field "certificate" cj "spec"
  let deltaStr ← strField "certificate.spec" spec "delta"
  let deltaRat ← match deltaStr.splitOn "/" with
    | [p, q] => match p.toNat?, q.toNat? with
      | some p, some q => pure ((p : Rat) / (q : Rat))
      | _, _ => throw s!"certificate: delta {deltaStr}"
    | [p] => match p.toNat? with | some p => pure (p : Rat) | none => throw s!"certificate: delta {deltaStr}"
    | _ => throw s!"certificate: delta {deltaStr}"
  let inst ← field "certificate" cj "instance"
  let n ← natField "certificate.instance" inst "n"
  let uncompute ← strField "certificate" cj "uncompute"
  let (ns, body) ← logicalBodyOf certLeanText
  -- the artifact
  let W ← Witness.ofJson wj m.usedQubits
  let pj ← Json.parse physicalText
  let physHash := Certify.SHA3.sha3String pj.compress
  let G ← physOfJson m.usedQubits pj
  let dev := m.usedQubits
  let edges := t.couplingMap
  -- hardware compatibility: the edges, and the capabilities the mode needs
  let edgesOkB := edgesOk G dev edges
  let capsOk := if uncompute == "mbu" then t.capabilities.feedForward.value && t.capabilities.midCircuitMeasurement.value else true
  let (emulatorPassed, emulatorNote) ← runResultOf runText
  -- the grades
  let rates ← RateTable.ofCalibration t.calibration
  let durs := t.durations.restrict dev
  let ratesR := rates.restrict dev
  let grades ← (latenciesOf L).mapM fun l => do
    let g ← physGrade durs ratesR m.basis dev G l dataPhys deltaRat
    return (l, g)
  -- the target file is named from the manifest, not from the argument: the files are path-independent
  let _ := targetFile
  let targetFile := s!"hw/targets/{m.target}.json"
  let nsAscii := (ns.replace "«" "").replace "»" ""
  -- the real δ in the form of the logical certificate's `delta_eq` (`p / q`; `0 / 1` for δ = 0)
  let deltaRealExpr := if deltaRat.den = 1 then s!"({ratStr deltaRat} / 1 : ℝ)" else s!"({ratStr deltaRat} : ℝ)"
  let d : PhysCertData := {
    certName, logicalCertNamespace := ns, logicalBody := body, m, certJsonHash, libHash, physHash,
    targetFileHash := Certify.SHA3.sha3String targetText, targetFile, targetName := t.name,
    C, W, G, dev, edges, dataPhys, delta := deltaRat, deltaExpr := ratStr deltaRat,
    specExpr := s!"(SearchSpec (Network.pred net {n}))", povmExpr := s!"(basisPOVM {n})",
    gradeExpr := "", deltaRealExpr,
    durs, rates := ratesR, grades, hardwareCompatible := edgesOkB && capsOk, emulatorPassed, emulatorNote }
  return { d, grades, certCircuit, deltaStr, uncompute, nsAscii, edgesOkB, capsOk, deviceWidth, nBits }

/-- The manifest of a physical certificate (26c2), with the status `words` and `extra` fields;
`physical` selects the `ideal_device` premise (R4). -/
def physCertManifest (p : PhysCertPrep) (certName certBase : String) (words : List String)
    (emulatorRun : String) (extra : List (String × Json)) (physical : Bool := true) : Json :=
  let d := p.d
  let gradesJson := Json.mkObj (p.grades.map fun (l, g) => (ratStr l, g.toJson l))
  Json.mkObj (([
    ("schema_version", "1.2.0"),
    ("certificate", certName),
    ("logical_certificate", Json.mkObj [("dir", s!"examples/certs/{certBase}"), ("namespace", p.nsAscii),
      ("theorem", s!"{p.nsAscii}.cert"), ("certificate_json_sha3_mod_library", d.certJsonHash), ("circuit_hash", p.certCircuit),
      ("delta", p.deltaStr), ("uncompute", p.uncompute)]),
    ("artifact", Json.mkObj [("dir", s!"hw/artifacts/{d.m.instance_}__{d.m.target}"), ("instance", d.m.instance_),
      ("target", d.m.target), ("basis", d.m.basis.twoQubit), ("used_qubits", Json.arr (d.dev.map (fun x => (x : Json))).toArray),
      ("data_physical", Json.arr (d.dataPhys.map (fun x => (x : Json))).toArray)]),
    ("hashes", Json.mkObj [("logical_circuit", d.m.logicalHash), ("witness", d.m.witnessHash), ("physical_json", d.physHash),
      ("target_snapshot", d.m.targetHash), ("target_file_sha3", d.targetFileHash),
      ("certificate_json_mod_library", d.certJsonHash), ("library", d.libHash)]),
    ("ff_latency_ns", Json.arr ((p.grades.map fun (l, _) => (ratStr l : Json))).toArray),
    ("ff_latency_note", "the feed-forward latency is an assumption stated by this certificate, not a property of the device"),
    ("phys_grade", gradesJson),
    ("bound_note", "delta + sum of the calibrated rates + the data readouts at the final layout (25a's physical_bound); reported, not certified: the noise theorem is Stage 27"),
    ("hardware_compatible", Json.mkObj [("edges_ok", p.edgesOkB), ("capabilities_ok", p.capsOk)]),
    ("model_premises", modelPremisesJson physical),
    ("emulator_run", emulatorRun),
    ("status", Json.arr (words.map fun w => (w : Json)).toArray),
    ("meaning_physical_translation", "physically validated: on an ideal device with the target's gates and coupling map, started from all-|0> on its used qubits, the physical circuit realizes the specification with the certified delta under the final layout; not a statement about noise; not verified on hardware")] : List (String × Json))
    ++ extra)

/-- PHASE2_SPEC §C.3 (26c2, P2) — `PhysCert.lean`, `physical.qasm` and `manifest.json` of a physical
certificate (unchanged output since 26c2). -/
def generatePhysCert (certName certBase : String) (certLeanText certJsonText : String)
    (manifestText logicalText witnessText physicalText : String) (t : HardwareTarget)
    (targetFile targetText : String) (L : Rat) (deviceWidth : Nat) (dataPhys : List Nat)
    (nBits : Nat) (runText : Option String) (libHash : String) :
    Except String (String × String × String × List (Rat × PhysGrade)) := do
  let p ← preparePhysCert certName certLeanText certJsonText manifestText logicalText witnessText physicalText
    t targetFile targetText L deviceWidth dataPhys nBits runText libHash
  let lean := physCertFile p.d
  let qasm := qasmOf p.d.G p.d.dev deviceWidth nBits
  let words := statusWords p.d.hardwareCompatible p.d.emulatorPassed
  let emulatorRun := if p.d.emulatorPassed then "passes (docs/hw_runs)" else p.d.emulatorNote
  return (lean, qasm, (physCertManifest p certName certBase words emulatorRun []).compress, p.grades)

/-! ## Selection by the physical grade (26c2b, P4) -/

/-- One candidate of a selection: the artifact's data the kernel grades. -/
structure SelCand where
  name : String
  mbu : Bool
  basis : TargetBasis
  G : List BasisGate
  dev : List Nat
  dataPhys : List Nat
  delta : Rat
  physHash : String
  durs : Durations
  rates : RateTable

/-- The grades of the candidates at `L`, and the candidates for `selectPhys`. -/
def gradeCands (cs : List SelCand) (L : Rat) : Except String (List (SelCand × PhysGrade)) :=
  cs.mapM fun c => do return (c, ← physGrade c.durs c.rates c.basis c.dev c.G L c.dataPhys c.delta)

def toPhysCands (gs : List (SelCand × PhysGrade)) : List PhysCand :=
  gs.map fun (c, g) => ⟨c.name, c.mbu, g⟩

def physCandLit (c : PhysCand) : String :=
  s!"⟨\"{c.name}\", {c.mbu}, {physGradeLit c.grade}⟩"

/-- PHASE2_SPEC §C.3 (26c2b, P4) — the text of `Select.lean` for one request on one target: every
candidate's `G` and its tables as literals (its `physical.json` hash linking it to its committed
`Check.lean`), each `PhysGrade` by the kernel, `selectPhys … = some c` or `= none` by the kernel,
the `selectPhys_spec` instance and `#print axioms`. -/
def selectFile (name request targetName targetFile : String) (ff : Bool) (p : PhysPref) (L : Rat)
    (budget : Option Rat) (gs : List (SelCand × PhysGrade)) (choice : Option PhysCand) : String :=
  let idx := gs.zipIdx
  let candDefs := String.intercalate "\n" (idx.map fun ((c, g), i) =>
    s!"/-- Candidate {i}: `{c.name}` ({if c.mbu then "mbu" else "coherent"}); `physical.json` SHA3-256 `{c.physHash}` — its
reconstruction, edges and channel theorem are `examples/hw_checks/{c.name}/Check.lean`'s. -/
def G{i} : List BasisGate := [
    {Certify.joinWrapped (c.G.map basisGateLit) 6 "    "}]
def dev{i} : List ℕ := {c.dev}
def durations{i} : Durations :=
  {durationsLit c.durs}
def rates{i} : RateTable :=
  {rateTableLit c.rates}
def dataPhys{i} : List ℕ := {c.dataPhys}
def delta{i} : Rat := {ratStr c.delta}
theorem grade{i} : (physGrade durations{i} rates{i} {basisLit c.basis} dev{i} G{i} ({ratStr L} : Rat) dataPhys{i} delta{i}).toOption =
    some {physGradeLit g} := by decide +kernel
")
  let cands := String.intercalate ",\n    " (gs.map fun (c, g) => physCandLit ⟨c.name, c.mbu, g⟩)
  let budgetLit := match budget with | some b => s!"some ({ratStr b} : Rat)" | none => "none"
  let choiceThm := match choice with
    | some c =>
      s!"/-- **`choice`**: the first minimal admissible candidate under `{p.name}` is `{c.name}`. -/
theorem choice : selectPhys ff budget .{p.name} cands = some {physCandLit c} := by decide +kernel

/-- `selectPhys_spec` at this instance: the choice is admissible and minimal for the component among
the admissible candidates. -/
theorem choice_spec :
    ({physCandLit c} : PhysCand) ∈ cands ∧ admissible ff budget .{p.name} {physCandLit c} = true ∧
      ∀ y ∈ cands, admissible ff budget .{p.name} y = true →
        PhysPref.key .{p.name} ({physCandLit c} : PhysCand).grade ≤ PhysPref.key .{p.name} y.grade :=
  (selectPhys_spec ff budget .{p.name} cands).1 _ choice
"
    | none =>
      s!"/-- **`choice`**: no candidate is admissible under `{p.name}`{match budget with | some b => s!" within the budget {ratStr b}" | none => ""} — the honest answer, not an error. -/
theorem choice : selectPhys ff budget .{p.name} cands = none := by decide +kernel

/-- `selectPhys_spec` at this instance: no candidate is admissible. -/
theorem choice_spec : ∀ y ∈ cands, admissible ff budget .{p.name} y = false :=
  (selectPhys_spec ff budget .{p.name} cands).2.mp choice
"
  s!"import CQRV.Hardware.SelectPhys

/-!
# Selection `{name}` (generated by `cqr hw select`; do not edit)

Report §3.1.3, §5.3; PHASE2_SPEC §C.3 (Stage 26c2b, P4). The request `{request}` on the target
`{targetName}` (`{targetFile}`; feed-forward {ff}): the candidates are its committed artifacts, each
graded by the kernel at the feed-forward latency L = {ratStr L} ns (an assumption), and the choice
under the preference `{p.name}`{match budget with | some b => s!" with the budget {ratStr b}" | none => ""} is decided by the kernel (`selectPhys`, `selectPhys_spec`).
Each candidate's `physical.json` hash links it to its `examples/hw_checks/<artifact>/Check.lean`,
where its reconstruction, edges and channel theorem are checked; this file does not repeat them.
The bound is reported, not certified (Stage 27 is the noise theorem); nothing is \"verified on
hardware\".
-/

set_option maxRecDepth 100000

namespace CQRV.HwSelect.«{name}»

open CQRV CQRV.Hardware

{candDefs}
/-- The candidates with their grades at L = {ratStr L} ns. -/
def cands : List PhysCand := [
    {cands}]

/-- The target's feed-forward capability. -/
abbrev ff : Bool := {ff}
/-- The budget on the component (`none`: no budget). -/
def budget : Option Rat := {budgetLit}

{choiceThm}
#print axioms choice_spec

end CQRV.HwSelect.«{name}»
"

/-- One row of the choice table: the preference, the latency, the choice. -/
def choiceRow (p : PhysPref) (L : Rat) (ff : Bool) (budget : Option Rat) (cs : List SelCand) :
    Except String String := do
  let gs ← gradeCands cs L
  let choice := selectPhys ff budget p (toPhysCands gs)
  let grades := ", ".intercalate (gs.map fun (c, g) => s!"{c.name}: {ratStr (p.key g)}")
  return s!"{p.name}@L={ratStr L}: {match choice with | some c => s!"{c.name} ({ratStr (p.key c.grade)})" | none => "none (no admissible candidate)"} [{grades}]"

end CQRV.Hardware
