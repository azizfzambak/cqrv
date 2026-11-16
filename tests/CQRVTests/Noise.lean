module

public import CQRV.Noise.Stochastic
public import CQRV.Hardware.SelectPhys
meta import CQRV.Noise.Stochastic
meta import CQRV.Hardware.SelectPhys

/-!
# Tests for `CQRV.Noise` (Stage 27a; PHASE2_SPEC §C.4; report §2.3.2, §6.6)

The axiom lines of `channelDenote_eq_steps`, `diamondDist_steps_le`, `diamondDist_mix_le`,
`noisy_realization` and `phys_noisy` (the standard three); `channelDenote_eq_steps` on the MBU
gadget; `diamondDist_mix_le` at `p = 0` (the distance is 0) and at `p = 1`; and
`noisy_realization_stochastic` on a toy one-gate circuit (one `X` on one data qubit, no classical
bits): a realization with `δ` becomes one with `δ + p` when the gate is ideal with probability `1 − p`.
-/

namespace CQRV.Tests.Noise

open CQRV
open scoped MState

@[expose] public section

/-- info: 'CQRV.channelDenote_eq_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms channelDenote_eq_steps

/-- info: 'CQRV.diamondDist_steps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diamondDist_steps_le

/-- info: 'CQRV.diamondDist_mix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diamondDist_mix_le

/-- info: 'CQRV.noisy_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noisy_realization

/-- info: 'CQRV.phys_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phys_noisy

/-- info: 'CQRV.phys_noisy_stochastic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phys_noisy_stochastic

/-- info: 'CQRV.phys_noisy_inst_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phys_noisy_inst_of

/-- info: 'CQRV.phys_noisy_channel_stochastic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phys_noisy_channel_stochastic

/-- info: 'CQRV.Hardware.selectNoise_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hardware.selectNoise_spec

/-! ## `channelDenote_eq_steps` on the MBU gadget -/

/-- The gadget has one classical bit. -/
example : mbuCircuit.nBits = 1 := by decide

/-- The branch semantics of the MBU gadget is its step semantics with the bit traced out. -/
example (ρ : MState (Reg 2 × Reg 1)) :
    channelDenote 2 1 mbuCircuit ρ =
      CPTPMap.traceRight (d₁ := Reg 2 × Reg 1) (d₂ := Reg mbuCircuit.nBits)
        (stepsOf 2 1 mbuCircuit.nBits mbuCircuit.gates (ρ ⊗ᴹ ancZero mbuCircuit.nBits)) :=
  channelDenote_eq_steps 2 1 mbuCircuit mbuCircuit_WF ρ

/-- The channel form on the gadget. -/
example : channelDenote 2 1 mbuCircuit =
    CPTPMap.traceRight ∘ₘ stepsOf 2 1 mbuCircuit.nBits mbuCircuit.gates ∘ₘ withBits 2 1 mbuCircuit.nBits :=
  channelDenote_eq_steps_chan 2 1 mbuCircuit mbuCircuit_WF

/-! ## `diamondDist_mix_le` at `p = 0` and `p = 1` -/

/-- At `p = 0` the mixture is within `0` of the ideal channel: the distance is `0`. -/
example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Φ Φ' : CPTPMap A B) :
    diamondDist (mix 0 Φ Φ') Φ = 0 := by
  have h := diamondDist_mix_le 0 Φ Φ'
  rw [show ((0 : Prob) : ℝ) = 0 from Prob.coe_zero, mul_zero] at h
  exact le_antisymm h (diamondDist_nonneg _ _)

/-- At `p = 1` the bound is `2`, the trivial bound (`diamondDist_le_two`). -/
example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Φ Φ' : CPTPMap A B) :
    diamondDist (mix 1 Φ Φ') Φ ≤ 2 := by
  have h := diamondDist_mix_le 1 Φ Φ'
  rwa [show ((1 : Prob) : ℝ) = 1 from Prob.coe_one, mul_one] at h

/-! ## `noisy_realization_stochastic` on a toy one-gate circuit -/

/-- The toy: the step channel of one `X` gate on one data qubit, no ancilla, no classical bit. -/
noncomputable def toyGate : CPTPMap (XReg 1 0 0) (XReg 1 0 0) := stepChan 1 0 0 (.x (.data 0))

/-- If the ideal toy circuit realizes `S` with `δ`, the circuit whose gate is ideal with probability
`1 − p` and arbitrary otherwise realizes `S` with `δ + p`. -/
example {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y) (dec : POVM Y (Reg 1))
    (prep : CPTPMap Unit (XReg 1 0 0)) (Γ : CPTPMap (Reg 1 × Reg 0) (Reg 1)) (p : Prob)
    (Φ' : CPTPMap (XReg 1 0 0) (XReg 1 0 0)) {δ : ℝ} {g r : Grade}
    (h : RealizesExact S dec ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps [toyGate] ∘ₘ prep, g⟩ δ r) :
    RealizesExact S dec ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps [mix p toyGate Φ'] ∘ₘ prep, g⟩
      (δ + (p : ℝ)) r := by
  have := noisy_realization_stochastic S dec prep Γ [(toyGate, p, Φ')] (by simpa using h)
  simpa using this

end

end CQRV.Tests.Noise
