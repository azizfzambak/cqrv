module

public import CQRV.Hardware.Check
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
  return { instance_, target, basis, usedQubits,
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

/-- PHASE2_SPEC §C.3 (26c1b) — the text of `Check.lean` for one artifact. -/
def checkFile (name : String) (C : Circuit) (W : Witness) (G : List BasisGate) (dev : List Nat)
    (edges : List (Nat × Nat)) (b : TargetBasis) (targetName targetFile : String) (m : ManifestData)
    (physHash : String) : String :=
  let n := C.nData
  let a := C.nAnc
  let N := dev.length
  let bb := N - (n + a)
  let reg := "(C.nData + (C.nAnc + bb))"
  let tamperEdges := match offEdgePair N dev edges with
    | some (p, q) =>
      s!"/-- A two-qubit gate on compact qubits {p}, {q} (device {dev.getD p 0}, {dev.getD q 0}), not an edge, is refused. -/\n" ++
      s!"theorem tamper_edges : edgesOk (G ++ [.{basisLit b |>.drop 1} (.data {p}) (.data {q})]) dev edges = false := by decide +kernel\n\n"
    | none => "-- every pair of used qubits is an edge: no off-edge tampering test\n\n"
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

/-- The logical circuit (`logical.json`): {C.gates.length} gates on {n} data qubits and {a} ancillae. -/
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

{tamperEdges}#print axioms phys_channel
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

end CQRV.Hardware
