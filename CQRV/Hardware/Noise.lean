module

public import CQRV.Hardware.PhysGrade

/-!
# CQRV.Hardware.Noise

Report §2.3.2, §6.6; PHASE2_SPEC §C.4 (4); STAGE27_TASK.md 27b B2 — **the conditional noise bound**
`noiseBound = δ + Σ_g p_g + Σ_j r_j`, Physlib-free, in the cqr closure, exact in `Rat`, on the rate
tables of `PhysGrade` (`rateOf`: the directed pair or its reverse):

* **(P-stoch)** for a basis operation on `k` qubits, `p_g = min 1 ((d+1)/d · r_g)` with `d = 2^k` —
  the Pauli reading of a randomized-benchmarking error (for a Pauli error channel of total
  probability `p`, the average infidelity is `d p / (d + 1)`): `3/2 · r` for `sx` and `x`, `5/4 · r`
  for `cz` and `cx`; virtual `rz` has `r = 0`, so `p = 0`; a conditioned gate takes the rate of its
  gate (`pauliFactor`, `rawP`, `clamp01`);
* **(P-ro)** a mid-circuit measurement and a data readout take `p = r_j`, the readout rate, with no
  factor;
* **the clamp**: `clamped` records whether some unclamped `p` exceeded `1` (then the bound is `≥ 1`,
  vacuous); the fakes' error-1.0 edges give `5/4` before the clamp.

The Python mirror is `hw/noisebound.py`; Lean must equal Python on all twelve artifacts
(`tests/diff/hw_noise_check.py`); 25a's `p = r` figure (`PhysGrade.bound`) is printed beside it.
The bound is what the conditional certificate's theorem `phys_noisy_inst` states as `δ'`
(`CQRV.Noise.Stochastic`): conditional on the premises, never a fact about a device.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV Lean

/-- PHASE2_SPEC §C.4 (4), (P-stoch)/(P-ro) — the factor `(d+1)/d` of the Pauli reading: `3/2` for a
one-qubit gate, `5/4` for a two-qubit gate, `1` for a measurement (P-ro: `p = r`), `0` for the virtual
`rz`; a conditioned gate takes its gate's factor. -/
def pauliFactor : BasisGate → Rat
  | .rz _ _ _ => 0
  | .sx _ => 3 / 2
  | .x _ => 3 / 2
  | .cz _ _ => 5 / 4
  | .cx _ _ => 5 / 4
  | .measure _ _ => 1
  | .ifBit _ g => pauliFactor g

/-- The clamp to `[0, 1]`. -/
def clamp01 (q : Rat) : Rat := max 0 (min 1 q)

/-- The unclamped `(d+1)/d · r_g` of a basis gate. -/
def rawP (r : RateTable) (dev : List Nat) (g : BasisGate) : Except String Rat := do
  return pauliFactor g * (← rateOf r dev g)

/-- The probabilities `p_g = clamp01 ((d+1)/d · r_g)` of the basis gates, in order. -/
def noiseProbs (r : RateTable) (dev : List Nat) (G : List BasisGate) : Except String (List Rat) := do
  return (← G.mapM (rawP r dev)).map clamp01

/-- The readout rates `r_j` of the data qubits at their final device positions. -/
def readoutRates (r : RateTable) (dataPhys : List Nat) : Except String (List Rat) :=
  dataPhys.mapM fun p => match r.readout.lookup (toString p) with
    | some x => pure x
    | none => throw s!"calibration: no readout error for the data qubit {p}"

/-- PHASE2_SPEC §C.4 (4) — the conditional noise bound: `δ' = δ + Σ p_g + Σ r_j`, whether some `p`
was clamped, and whether it is vacuous (`1 ≤ δ'`). -/
structure NoiseBound where
  bound : Rat
  clamped : Bool
  vacuous : Bool
  deriving Repr, DecidableEq

/-- **`noiseBound`**: `δ + Σ_g clamp01 ((d+1)/d · r_g) + Σ_j clamp01 r_j`. -/
def noiseBound (r : RateTable) (dev : List Nat) (G : List BasisGate) (dataPhys : List Nat) (delta : Rat) :
    Except String NoiseBound := do
  let raw ← G.mapM (rawP r dev)
  let ro ← readoutRates r dataPhys
  let bound := delta + ((raw.map clamp01).sum + (ro.map clamp01).sum)
  return { bound,
           clamped := raw.any (fun q => decide (1 < q)) || ro.any (fun q => decide (1 < q)),
           vacuous := decide (1 ≤ bound) }

/-- The bound from a target (the tables of its calibration). -/
def noiseBoundOf (t : HardwareTarget) (dev : List Nat) (G : List BasisGate) (dataPhys : List Nat)
    (delta : Rat) : Except String NoiseBound := do
  noiseBound (← RateTable.ofCalibration t.calibration) dev G dataPhys delta

/-- The bound as canonical JSON, beside 25a's `p = r` figure (the form `hw/noisebound.py` prints). -/
def NoiseBound.toJson (nb : NoiseBound) (physBound : Rat) : Json :=
  Json.mkObj [("noise_bound", ratStr nb.bound), ("noise_vacuous", nb.vacuous), ("clamped", nb.clamped),
    ("physical_bound_p_eq_r", ratStr physBound)]

end CQRV.Hardware
