module

public import CQRV.Hardware.CheckGen
public import CQRV.Hardware.Noise

/-!
# CQRV.Hardware.NoiseCertGen

Report §2.3.2, §5.3, §6.6, §8.4; PHASE2_SPEC §C.4 (4); STAGE27_TASK.md 27b2 B4 — **the conditional
certificates** (`cqr hw noisecert`), Physlib-free, in the cqr closure. Two forms:

* **with a logical certificate** (hw_n2, hw_n3): 26c2's `PhysCert.lean` (`emitted_eq`, `phys_channel`,
  `phys_zero`, `phys_realizes`, `PhysGrade`) plus the noise block — the probabilities `ps`
  (`noiseProbs`) and `rs` (`readoutRates`) as literals, `noiseBound_eq`, the kernel-decided identity
  `noise_key : δ + (Σ clamp01 ps + Σ clamp01 rs) = noiseB`, and **`phys_noisy_inst`**: for every
  choice of the arbitrary channels (any `T` with the basis gates `G` and the probabilities `ps`, any
  `R` with the probabilities `rs`), the noisy physical channel `RealizesExact` the specification with
  `δ' = noiseB` — a one-line instance of `phys_noisy_inst_of`;
* **the channel form** (the bare MBU gadget, which has no logical certificate but the theorem
  `mbu_channel_correct`): the check body, `c_eq : C = mbuCircuit` by the kernel, the noise block, and
  **`gadget_noisy`**: for every choice of the arbitrary channels, the noisy output from the embedded
  input is within `noiseB` in trace distance of `σf`'s embedding of the gadget's correct output
  (`phys_noisy_channel_stochastic`).

**The manifest** names the status word `noise_conditional`, the bound (exact and rounded), the clamp
flag, the vacuity, 25a's `p = r` figure, **the four premises** by name — (P-cal) the calibration
snapshot by hash, shipped with qiskit-ibm-runtime and recorded from a real device on a past date;
(P-stoch) the Pauli reading with the clamp; (P-ro); (P-idle) — and the meaning sentence: conditional
on the premises, the device's success probability is at least `1 − δ'`; the premises are assumptions
about the device, not facts proved here; not verified on hardware.

**The emulator comparison** applies 25b's acceptance criterion to the recorded run report with the
new δ', without re-running: 25b's check is `p̂ ≥ 1 − δ_hw − √(ln(1/α) / (2·shots))`; the margin
`√(ln(1/α) / (2·shots))` is not rational, so "exactly in `Rat`" is read as: the margin is taken from
the recorded run as the exact rational of its printed decimals, `margin = (1 − δ_hw) − threshold`,
and the new threshold is `threshold' = 1 − δ' − margin = threshold + δ_hw − δ'`; `emulator_validated`
is given only when `p̂ ≥ threshold'`. The emulator's noise model is not of the (P-stoch) form, so the
comparison is a sanity check, not evidence for the premise.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV Lean

/-- What the noise block of a certificate needs: the probabilities, the bound, the texts. -/
structure NoiseData where
  ps : List Rat
  rs : List Rat
  nb : NoiseBound
  physBound : Rat
  deltaRat : Rat

/-- A list of rationals as `mkRat num den` literals (a long list of `p / q` literals exhausts the
elaborator's heartbeats on `/`; `mkRat` takes integer literals only). -/
def ratListLit (l : List Rat) : String :=
  "[" ++ Certify.joinWrapped (l.map fun q => s!"mkRat {q.num} {q.den}") 6 "    " ++ "]"

/-- The literals and the kernel-decided facts of the noise bound: `ps`, `rs`, `noiseB`, their
equations with `noiseProbs`, `readoutRates`, `noiseBound`, and the identity `noise_key`. `rates`,
`dev`, `G`, `dataPhys`, `delta` are the certificate's definitions. -/
def noiseLiterals (nd : NoiseData) : String :=
  s!"/-- (P-stoch): the probabilities `p_g = min 1 ((d+1)/d · r_g)` of the {nd.ps.length} basis operations, in order
(`noiseProbs`; virtual `rz` has `p = 0`). -/
def ps : List Rat := {ratListLit nd.ps}

theorem ps_eq : (noiseProbs rates dev G).toOption = some ps := by decide +kernel

/-- (P-ro): the readout rates `r_j` of the {nd.rs.length} data qubits at the final layout (`readoutRates`). -/
def rs : List Rat := {ratListLit nd.rs}

theorem rs_eq : (readoutRates rates dataPhys).toOption = some rs := by decide +kernel

/-- **The conditional bound** `δ' = δ + Σ p_g + Σ r_j` (exact; ≈ {ratFloat nd.nb.bound}){if nd.nb.clamped then "; some `p` reached the clamp, so the bound is vacuous" else ""}{if nd.nb.vacuous then "; VACUOUS (≥ 1)" else ""}. -/
def noiseB : Rat := {ratStr nd.nb.bound}

theorem noiseBound_eq : (noiseBound rates dev G dataPhys delta).toOption =
    some ⟨noiseB, {nd.nb.clamped}, {nd.nb.vacuous}⟩ := by decide +kernel

/-- The identity behind the real bound of the noise theorem, decided by the kernel. -/
theorem noise_key : delta + ((ps.map clamp01).sum + (rs.map clamp01).sum) = noiseB := by decide +kernel
"

/-- The noise block of a certificate with a logical certificate: `phys_noisy_inst`. -/
def noiseBlockLogical (nd : NoiseData) (basis : TargetBasis) (specExpr povmExpr deltaRealExpr : String) : String :=
  let reg := "(C.nData + (C.nAnc + bb))"
  let X := s!"XReg {reg} 0 (physCircuit {reg} G).nBits"
  s!"
/-! ## The conditional certificate (Stage 27b2; PHASE2_SPEC §C.4) -/

{noiseLiterals nd}
theorem delta_cast : ((delta : Rat) : ℝ) = {deltaRealExpr} := by norm_num [delta]

/-- **`phys_noisy_inst`**: under (P-stoch) at the basis operations with the probabilities `ps`, (P-ro) at
the data readouts with the rates `rs`, and (P-idle) (only the listed steps act), **for every choice of
the arbitrary channels** (the third components of `T` and the second of `R`), the noisy physical
channel `RealizesExact` the specification with `δ' = noiseB`, at the physical circuit's grade
(`phys_noisy_inst_of`, through `emitted_eq`). Conditional on the premises; not a fact about a device. -/
theorem phys_noisy_inst
    (T : List (BasisGate × Prob × CPTPMap ({X}) ({X}))) (hT : T.map (·.1) = G)
    (hp : T.map (·.2.1) = ps.map probOfRat)
    (R : List (Prob × CPTPMap ({X}) ({X}))) (hR : R.map (·.1) = rs.map probOfRat) :
    ∃ σf' : Equiv.Perm (Fin {reg}), W.final = layOf {reg} (C.nData + C.nAnc) σf' ∧
      RealizesExact {specExpr} {povmExpr}
        ⟨unembed bb σf' ∘ₘ CPTPMap.traceRight ∘ₘ
            steps (stochasticSteps {reg} (physCircuit {reg} G).nBits T R) ∘ₘ
            physPrep {reg} (physCircuit {reg} G).nBits (embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc)),
          Synthesis.grade (physCircuit {reg} G)⟩
        ((noiseB : Rat) : ℝ) (Synthesis.grade (physCircuit {reg} G)) :=
  phys_noisy_inst_of {basisLit basis} C W bb c_wf G (applyWitnessQ_ok _ _ c_wf _ _ _ recon) phys_wf
    phys_nBits σ₀ init_eq _ _ _ _ (emitted_eq ▸ cert.1) T hT ps hp R rs hR delta noiseB delta_cast noise_key

#print axioms phys_noisy_inst
"

/-- The channel-form certificate of the bare MBU gadget (`cqr hw noisecert` without `--cert`). -/
def gadgetNoiseCertFile (certName : String) (m : ManifestData) (physHash targetFileHash targetFile targetName : String)
    (C : Circuit) (W : Witness) (G : List BasisGate) (dev : List Nat) (edges : List (Nat × Nat))
    (dataPhys : List Nat) (rates : RateTable) (nd : NoiseData) (words : List String) : String :=
  let reg := "(C.nData + (C.nAnc + bb))"
  let X := s!"XReg {reg} 0 (physCircuit {reg} G).nBits"
  "import CQRV\n" ++ "import CQRV.Hardware.CheckSound\n" ++ "import CQRV.Hardware.Noise\n" ++ s!"
/-!
# Conditional certificate `{certName}` (generated by `cqr hw noisecert`; do not edit)

Report §2.3.2, §6.2.2, §6.6; PHASE2_SPEC §C.4 (Stage 27b2). The MBU gadget has no logical certificate;
its logical statement is the theorem `mbu_channel_correct` (`CQRV.Circuit.Restoration`): on every data
state the gadget applies `CZ` and restores its ancilla. The artifact `hw/artifacts/{m.instance_}__{m.target}/`
(`logical.json` SHA3-256 `{m.logicalHash}`, `witness.json` `{m.witnessHash}`, `physical.json` `{physHash}`)
on the target `{targetName}` (`{targetFile}`: snapshot `{m.targetHash}`, file bytes SHA3-256
`{targetFileHash}`), compacted to the {dev.length} used qubits `{dev}`.

**The trusted link** is `c_eq : C = mbuCircuit`, decided by the kernel. **The conditional statement**
(`gadget_noisy`): under the premises (P-stoch), (P-ro), (P-idle), (P-cal), for every choice of the
arbitrary channels, the noisy physical output from the embedded input is within `δ' = noiseB` in
trace distance of `σf`'s embedding of the gadget's correct output. The premises are assumptions about
the device, not facts proved here; nothing is \"verified on hardware\". Status: {", ".intercalate words}.
-/

set_option maxRecDepth 100000

namespace CQRV.NoiseCert.«{certName}»

open CQRV CQRV.Hardware CQRV.Synthesis
open scoped MState

{checkBody C W G dev edges .cz targetFile}
/-- **The trusted link**: the artifact's logical circuit is the MBU gadget of `CQRV.Circuit.Restoration`. -/
theorem c_eq : C = mbuCircuit := by decide +kernel

/-- The calibrated rates of the target on the used qubits (exact; the snapshot of `{targetFile}`). -/
def rates : RateTable :=
  {rateTableLit rates}

/-- The device qubits of the data register at the final layout. -/
def dataPhys : List ℕ := {dataPhys}

/-- The gadget's logical statement is exact: δ = 0. -/
def delta : Rat := 0

{noiseLiterals nd}
/-- **`gadget_noisy`**: for every choice of the arbitrary channels, the noisy physical channel's output on
the embedded `ρ ⊗ |0⟩⟨0|` (ancilla `|0⟩`) is within `noiseB` in trace distance of `σf`'s embedding of
`(CZ ρ CZ†) ⊗ |0⟩⟨0|` (`mbu_channel_correct` through `phys_channel`, `phys_noisy_channel_stochastic`). -/
theorem gadget_noisy
    (T : List (BasisGate × Prob × CPTPMap ({X}) ({X}))) (hT : T.map (·.1) = G)
    (hp : T.map (·.2.1) = ps.map probOfRat)
    (R : List (Prob × CPTPMap ({X}) ({X}))) (hR : R.map (·.1) = rs.map probOfRat)
    (ρ : MState (Reg 2)) :
    TrDistance
      (CPTPMap.traceRight (d₁ := Reg {reg} × Reg 0) (d₂ := Reg (physCircuit {reg} G).nBits)
        (steps (stochasticSteps {reg} (physCircuit {reg} G).nBits T R)
          (withBits {reg} 0 (physCircuit {reg} G).nBits (embed bb σ₀ (ρ ⊗ᴹ ancZero 1)))))
      (embed bb σf ((czU ◃ ρ) ⊗ᴹ ancZero 1)) ≤ ((noiseB : Rat) : ℝ) := by
  have h := phys_noisy_channel_stochastic C bb G phys_wf σ₀ σf phys_channel.2 T hT R (ρ ⊗ᴹ ancZero 1)
  have hmc : channelDenote C.nData C.nAnc C (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 := by
    have h0 := mbu_channel_correct ρ
    rw [← c_eq] at h0
    exact h0
  rw [hmc, sum_probs_of_map T _ ps hp, sum_probs_of_map R _ rs hR] at h
  have hnb : ((noiseB : Rat) : ℝ) =
      (((ps.map clamp01).sum : Rat) : ℝ) + (((rs.map clamp01).sum : Rat) : ℝ) := by
    rw [← noise_key]; push_cast; simp [delta]
  rw [hnb]
  exact h

#print axioms c_eq
#print axioms phys_channel
#print axioms gadget_noisy

end CQRV.NoiseCert.«{certName}»
"

/-! ## The emulator comparison at δ' -/

/-- The recorded run's figures and the comparison at the new bound. -/
structure EmulatorCompare where
  pHat : Rat
  shots : Nat
  alpha : Rat
  thresholdOld : Rat
  deltaOld : Rat
  thresholdNew : Rat
  passes : Bool

def jsonRat (ctx : String) (j : Json) : Except String Rat :=
  match j with
  | .num n => pure (jsonNumberToRat n)
  | .str s => match parseDecimalSci s with
    | some q => pure q
    | none => throw s!"{ctx}: `{s}` is not a decimal"
  | _ => throw s!"{ctx}: not a number"

/-- A fraction string `p/q` or a decimal, exactly. -/
def fracOrDecimal (ctx : String) (s : String) : Except String Rat :=
  match s.splitOn "/" with
  | [p, q] => match p.toNat?, q.toNat? with
    | some p, some q => pure ((p : Rat) / (q : Rat))
    | _, _ => throw s!"{ctx}: `{s}`"
  | _ => match parseDecimalSci s with
    | some q => pure q
    | none => throw s!"{ctx}: `{s}`"

/-- PHASE2_SPEC §C.4 (4), the emulator comparison: 25b's criterion with the recorded margin and the
new δ' (`threshold' = threshold + δ_hw − δ'`), exactly in `Rat`. -/
def emulatorCompare (runText : String) (deltaNew : Rat) : Except String EmulatorCompare := do
  let j ← Json.parse runText
  let noisy ← field "run" j "noisy"
  let pHat ← jsonRat "run.noisy.p_hat" (← field "run.noisy" noisy "p_hat")
  let shots ← natField "run" j "shots"
  let check ← field "run" j "check"
  let alpha ← jsonRat "run.check.alpha" (← field "run.check" check "alpha")
  let thresholdOld ← jsonRat "run.check.threshold" (← field "run.check" check "threshold")
  let deltaOld ← fracOrDecimal "run.delta_hw" (← strField "run" j "delta_hw")
  let thresholdNew := thresholdOld + deltaOld - deltaNew
  return { pHat, shots, alpha, thresholdOld, deltaOld, thresholdNew, passes := decide (thresholdNew ≤ pHat) }

def EmulatorCompare.toJson (e : EmulatorCompare) (runFile : String) : Json :=
  Json.mkObj [("run", runFile), ("p_hat", ratStr e.pHat), ("shots", e.shots), ("alpha", ratStr e.alpha),
    ("threshold_recorded", ratStr e.thresholdOld), ("delta_hw_recorded", ratStr e.deltaOld),
    ("threshold_at_delta_prime", ratStr e.thresholdNew), ("threshold_at_delta_prime_float", Lean.toJson (ratFloat e.thresholdNew)),
    ("statement", "p_hat >= threshold_recorded + delta_hw_recorded - delta_prime (25b's criterion with its recorded margin, not re-run)"),
    ("result", if e.passes then "passes" else "fails"),
    ("note", "the emulator's noise model (Aer, from the fake backend) is not of the (P-stoch) form: a sanity check, not evidence for the premise")]

/-- The four premises, by name. -/
def premisesJson (targetFile snapshotHash : String) (clamped : Bool) : Json :=
  Json.mkObj [
    ("P-cal", s!"the calibration snapshot of {targetFile} (SHA3-256 {snapshotHash}), shipped with qiskit-ibm-runtime and recorded from a real device on a past date; not a live calibration"),
    ("P-stoch", s!"every basis operation on k qubits is, with probability at least 1 - p, its ideal channel and otherwise an arbitrary channel on the whole register, with p = min 1 ((d+1)/d * r), d = 2^k, r its calibrated error (the Pauli reading of a randomized-benchmarking error: 3/2 r one-qubit, 5/4 r two-qubit; virtual rz has r = 0){if clamped then "; some p reached the clamp" else "; no p reached the clamp"}"),
    ("P-ro", "every readout, the mid-circuit measurements included, is with probability at least 1 - r its ideal channel and otherwise arbitrary, with r the calibrated readout error of its qubit"),
    ("P-idle", "idle qubits suffer no error: only the listed operations act (the step list of the theorem); the idle-exposure diagnostic of Stage 27c is not part of the bound")]

def noiseMeaning : String :=
  "conditional on the premises P-cal, P-stoch, P-ro, P-idle, the device's success probability is at least 1 - delta_prime (noise_bound); the premises are assumptions about the device, not facts proved here; not verified on hardware"

/-- The noise part of a manifest. -/
def noiseJson (nd : NoiseData) (targetFile snapshotHash : String) (emu : Option (EmulatorCompare × String))
    (emuNote : String) : List (String × Json) :=
  [("noise", Json.mkObj [("noise_bound", ratStr nd.nb.bound), ("noise_bound_float", Lean.toJson (ratFloat nd.nb.bound)),
      ("noise_vacuous", nd.nb.vacuous), ("clamped", nd.nb.clamped),
      ("physical_bound_p_eq_r", ratStr nd.physBound), ("physical_bound_p_eq_r_float", Lean.toJson (ratFloat nd.physBound)),
      ("probabilities", Json.arr (nd.ps.map fun q => (ratStr q : Json)).toArray),
      ("readout_rates", Json.arr (nd.rs.map fun q => (ratStr q : Json)).toArray),
      ("premises", premisesJson targetFile snapshotHash nd.nb.clamped),
      ("meaning", noiseMeaning)]),
   ("emulator_comparison", match emu with
      | some (e, f) => e.toJson f
      | none => Json.str emuNote)]

/-! ## The generators -/

/-- The probabilities and the bound of an artifact's physical circuit on the restricted rate table. -/
def noiseDataOf (rates : RateTable) (dev : List Nat) (G : List BasisGate) (dataPhys : List Nat)
    (delta physBound : Rat) : Except String NoiseData := do
  let ps ← noiseProbs rates dev G
  let rs ← readoutRates rates dataPhys
  let nb ← noiseBound rates dev G dataPhys delta
  return { ps, rs, nb, physBound, deltaRat := delta }

/-- The status words of a conditional certificate: the physical words (never `emulator_validated`
from the recorded result), `noise_conditional`, and `emulator_validated` only when the comparison at
δ' passes. -/
def noiseWords (logical hardwareCompatible : Bool) (emuPassed : Bool) : List String :=
  (if logical then ["logical_certified"] else []) ++ (if hardwareCompatible then ["hardware_compatible"] else []) ++
  ["physical_translation_validated", "noise_conditional"] ++ (if emuPassed then ["emulator_validated"] else [])

/-- PHASE2_SPEC §C.4 (4) — the conditional certificate with a logical certificate (hw_n2, hw_n3):
`PhysCert.lean` with the noise block, `physical.qasm`, `manifest.json` with the noise part. -/
def generateNoiseCert (certName certBase : String) (certLeanText certJsonText : String)
    (manifestText logicalText witnessText physicalText : String) (t : HardwareTarget)
    (targetFile targetText : String) (L : Rat) (deviceWidth : Nat) (dataPhys : List Nat)
    (nBits : Nat) (runText : Option String) (runFile : String) :
    Except String (String × String × String × NoiseData × Option EmulatorCompare) := do
  let p ← preparePhysCert certName certLeanText certJsonText manifestText logicalText witnessText physicalText
    t targetFile targetText L deviceWidth dataPhys nBits runText
  let d := p.d
  let physBound := match p.grades.head? with | some (_, g) => g.bound | none => 0
  let nd ← noiseDataOf d.rates d.dev d.G d.dataPhys d.delta physBound
  let emu ← match runText with
    | some r => do
      let e ← emulatorCompare r nd.nb.bound
      pure (some e)
    | none => pure none
  let emuPassed := match emu with | some e => e.passes | none => false
  let emuNote := match emu with | some _ => "" | none => "no run recorded for this artifact"
  let words := noiseWords true d.hardwareCompatible emuPassed
  let d' := { d with emulatorPassed := false }
  let lean := physCertFile d' (noiseBlockLogical nd d.m.basis d.specExpr d.povmExpr d.deltaRealExpr)
    (["noise_conditional"] ++ (if emuPassed then ["emulator_validated"] else []))
  let qasm := qasmOf d.G d.dev deviceWidth nBits
  let emulatorRun := match emu with
    | some e => if e.passes then s!"passes at delta_prime ({runFile})" else s!"fails at delta_prime ({runFile})"
    | none => emuNote
  let manifest := physCertManifest p certName certBase words emulatorRun
    (noiseJson nd d.targetFile d.m.targetHash (emu.map fun e => (e, runFile)) emuNote)
  return (lean, qasm, manifest.compress, nd, emu)

/-- PHASE2_SPEC §C.4 (4) — the channel-form conditional certificate of the bare MBU gadget:
`NoiseCert.lean`, `physical.qasm`, `manifest.json`. The artifact's logical circuit must be
`mbuCircuit` (the kernel decides `c_eq`; the generator checks the hash link to `mbuCircuit` first). -/
def generateGadgetNoiseCert (certName : String) (manifestText logicalText witnessText physicalText : String)
    (t : HardwareTarget) (targetFile targetText : String) (deviceWidth : Nat) (dataPhys : List Nat)
    (nBits : Nat) (runText : Option String) (runFile : String) :
    Except String (String × String × String × NoiseData × Option EmulatorCompare) := do
  let mj ← Json.parse manifestText
  let m ← manifestOfJson mj
  let lj ← Json.parse logicalText
  let C ← circuitOfJson lj
  unless Certify.SHA3.sha3String lj.compress == m.logicalHash do
    throw s!"logical.json: SHA3-256 differs from the manifest's {m.logicalHash}"
  unless Certify.circuitHash C == m.logicalHash do
    throw "logical circuit: the Lean literal's circuitHash differs from the manifest's"
  -- `mbuCircuit` lives Physlib-side (`CQRV.Circuit.Restoration`): the generator checks the instance name,
  -- the kernel decides `c_eq : C = mbuCircuit` in the certificate
  unless m.instance_ == "mbu_gadget" do throw s!"instance {m.instance_}: the channel form is the bare MBU gadget's (`mbu_gadget`)"
  let wj ← Json.parse witnessText
  unless Certify.SHA3.sha3String wj.compress == m.witnessHash do throw "witness.json: SHA3-256 differs from the manifest's"
  unless t.snapshotHash == m.targetHash do throw "target: snapshot hash differs from the manifest's"
  unless t.checkHash do throw "target: the calibration's SHA3-256 differs from snapshot.hash"
  let W ← Witness.ofJson wj m.usedQubits
  let pj ← Json.parse physicalText
  let physHash := Certify.SHA3.sha3String pj.compress
  let G ← physOfJson m.usedQubits pj
  let dev := m.usedQubits
  let edges := t.couplingMap
  let edgesOkB := edgesOk G dev edges
  let capsOk := if m.uncompute == "mbu" then t.capabilities.feedForward.value && t.capabilities.midCircuitMeasurement.value else true
  let rates ← RateTable.ofCalibration t.calibration
  let ratesR := rates.restrict dev
  let durs := t.durations.restrict dev
  let g ← physGrade durs ratesR m.basis dev G 0 dataPhys 0
  let nd ← noiseDataOf ratesR dev G dataPhys 0 g.bound
  let emu ← match runText with
    | some r => do
      let e ← emulatorCompare r nd.nb.bound
      pure (some e)
    | none => pure none
  let emuPassed := match emu with | some e => e.passes | none => false
  let emuNote := match emu with | some _ => "" | none => "no run recorded for this artifact"
  let words := noiseWords false (edgesOkB && capsOk) emuPassed
  let _ := targetFile
  let targetFile := s!"hw/targets/{m.target}.json"
  let targetFileHash := Certify.SHA3.sha3String targetText
  let lean := gadgetNoiseCertFile certName m physHash targetFileHash targetFile t.name C W G dev edges dataPhys ratesR nd words
  let qasm := qasmOf G dev deviceWidth nBits
  let emulatorRun := match emu with
    | some e => if e.passes then s!"passes at delta_prime ({runFile})" else s!"fails at delta_prime ({runFile})"
    | none => emuNote
  let manifest := Json.mkObj (([
    ("schema_version", "1.0.0"),
    ("certificate", certName),
    ("logical_statement", Json.mkObj [("theorem", "CQRV.mbu_channel_correct"), ("module", "CQRV.Circuit.Restoration"),
      ("link", "c_eq : C = mbuCircuit, decided by the kernel"), ("delta", "0")]),
    ("artifact", Json.mkObj [("dir", s!"hw/artifacts/{m.instance_}__{m.target}"), ("instance", m.instance_),
      ("target", m.target), ("basis", m.basis.twoQubit), ("used_qubits", Json.arr (dev.map (fun x => (x : Json))).toArray),
      ("data_physical", Json.arr (dataPhys.map (fun x => (x : Json))).toArray)]),
    ("hashes", Json.mkObj [("logical_circuit", m.logicalHash), ("witness", m.witnessHash), ("physical_json", physHash),
      ("target_snapshot", m.targetHash), ("target_file_sha3", targetFileHash)]),
    ("phys_grade", Json.mkObj [("0", g.toJson 0)]),
    ("hardware_compatible", Json.mkObj [("edges_ok", edgesOkB), ("capabilities_ok", capsOk)]),
    ("emulator_run", emulatorRun),
    ("status", Json.arr (words.map fun w => (w : Json)).toArray),
    ("meaning", "channel form: on an ideal device, from the embedded input, the physical circuit outputs the embedding of the gadget's correct output (mbu_channel_correct through phys_channel); the noise part is conditional on the premises; not verified on hardware")] : List (String × Json))
    ++ noiseJson nd targetFile m.targetHash (emu.map fun e => (e, runFile)) emuNote)
  return (lean, qasm, manifest.compress, nd, emu)

end CQRV.Hardware
