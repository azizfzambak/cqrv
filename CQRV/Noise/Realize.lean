module

public import CQRV.Noise.Steps
public import CQRV.Hardware.WitnessSound

/-!
# CQRV.Noise.Realize

Report §2.3.2 (Theorem 3.3b), §6.6; PHASE2_SPEC §C.4 (3); STAGE27_TASK.md 27a N3 — **the noise
theorem**: a realization survives a noisy implementation of its steps, at a cost of half the sum of
the per-step diamond distances.

* `noisy_realization_core`: the one-step form — if `Γ ∘ Λ ∘ prep` realizes `S` with `δ` and
  `‖Λ' − Λ‖⋄ ≤ η`, then `Γ ∘ Λ' ∘ prep` realizes `S` with `δ + η/2`, at the same declared grade
  (`diamond_dominates` at the state `prep (encode x)`, data processing for `Γ`, and the measurement
  bound `prob_sub_le_trDistance_of`, as in Theorem 3.3b);
* **`noisy_realization`** (`RealizesExact`) and `noisy_realization_realizes` (`Realizes`, with `ε`):
  the ideal composite `Γ ∘ traceBits ∘ steps Φs ∘ prep` realizes `S` with `δ`; every step `Ψᵢ` of a
  noisy implementation is within `ηᵢ` of its ideal `Φᵢ` (a list of triples (Φᵢ, Ψᵢ, ηᵢ)); then the
  noisy composite realizes `S` with `δ + (∑ ηᵢ)/2`. Readout steps are ordinary list entries after
  the circuit's steps (the ideal readout is `id`).
* **`noisy_realization_stochastic`**: under the stochastic premise (P-stoch), `Ψᵢ = mix pᵢ Φᵢ Φ'ᵢ`,
  the bound is `δ + ∑ pᵢ` (`diamondDist_mix_le`: `ηᵢ = 2pᵢ`).
* **`phys_noisy`**: the instance on Stage 26's `physGroverChannel` — `realizesExact_phys`'s
  hypotheses, a list of triples whose ideal steps are the step channels of the routed circuit
  followed by `k` identity (readout) steps, with per-step bounds; the noisy physical channel
  `RealizesExact` `S` with `δ + (∑ ηᵢ)/2`, through `channelDenote_eq_steps_chan` and
  `noisy_realization`.

The premises (P-cal), (P-stoch), (P-ro), (P-idle) of a conditional certificate are the hypotheses'
form, named in PHASE2_SPEC §C.4 (4); nothing here is a statement about a device.
-/

@[expose] public section

noncomputable section

namespace CQRV

open scoped MState

section Core

variable {X Y dY R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype dY] [DecidableEq dY] [Fintype R] [DecidableEq R]

/-- Report §2.3.2, Theorem 3.3b — **the one-step noise bound** (`RealizesExact`): replacing the middle
channel `Λ` by `Λ'` with `‖Λ' − Λ‖⋄ ≤ η` costs at most `η/2` in `δ`, at the same declared grade. -/
theorem noisy_realization_core (S : Spec X Y) (dec : POVM Y dY) (prep : CPTPMap X R)
    (Γ : CPTPMap R dY) (Λ Λ' : CPTPMap R R) {η δ : ℝ} {g r : Grade}
    (hideal : RealizesExact S dec ⟨Γ ∘ₘ Λ ∘ₘ prep, g⟩ δ r) (hd : diamondDist Λ' Λ ≤ η) :
    RealizesExact S dec ⟨Γ ∘ₘ Λ' ∘ₘ prep, g⟩ (δ + η / 2) r := by
  refine ⟨hideal.1, fun x hx => ?_⟩
  have hid := hideal.2 x hx
  simp only [CPTPMap.compose_eq] at hid ⊢
  set σ := prep (encode x)
  have hdp := trDistance_cptp_le Γ (Λ σ) (Λ' σ)
  have hdom := diamond_dominates Λ' Λ σ
  rw [trDistance_symm] at hdom
  have hm := prob_sub_le_trDistance_of dec (Γ (Λ σ)) (Γ (Λ' σ)) (S x)
  linarith

/-- The one-step noise bound for `Realizes` (with `ε`, on a pseudo-metric output space). -/
theorem noisy_realization_core_realizes [PseudoMetricSpace Y] (S : Spec X Y) (dec : POVM Y dY)
    (prep : CPTPMap X R) (Γ : CPTPMap R dY) (Λ Λ' : CPTPMap R R) {ε η δ : ℝ} {g r : Grade}
    (hideal : Realizes S dec ⟨Γ ∘ₘ Λ ∘ₘ prep, g⟩ ε δ r) (hd : diamondDist Λ' Λ ≤ η) :
    Realizes S dec ⟨Γ ∘ₘ Λ' ∘ₘ prep, g⟩ ε (δ + η / 2) r := by
  refine ⟨hideal.1, fun x hx => ?_⟩
  have hid := hideal.2 x hx
  simp only [CPTPMap.compose_eq] at hid ⊢
  set σ := prep (encode x)
  have hdp := trDistance_cptp_le Γ (Λ σ) (Λ' σ)
  have hdom := diamond_dominates Λ' Λ σ
  rw [trDistance_symm] at hdom
  have hm := prob_sub_le_trDistance_of dec (Γ (Λ σ)) (Γ (Λ' σ)) (S.relax ε x)
  linarith

end Core

section Steps

variable {X Y dY Q M : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype dY] [DecidableEq dY] [Fintype Q] [DecidableEq Q] [Fintype M] [DecidableEq M]

/-- Report §2.3.2, §6.6; PHASE2_SPEC §C.4 (3) — **`noisy_realization`** (`RealizesExact`): the ideal
composite `Γ ∘ traceBits ∘ steps Φs ∘ prep` realizes `S` with `δ` at grade `r`, and each noisy step
is within `ηᵢ` of its ideal (`L` lists the triples `(Φᵢ, Ψᵢ, ηᵢ)`); then the noisy composite realizes
`S` with `δ + (∑ ηᵢ)/2`, at the same grade. -/
theorem noisy_realization (S : Spec X Y) (dec : POVM Y dY) (prep : CPTPMap X (Q × M))
    (Γ : CPTPMap Q dY) (L : List (CPTPMap (Q × M) (Q × M) × CPTPMap (Q × M) (Q × M) × ℝ))
    {δ : ℝ} {g r : Grade}
    (hideal : RealizesExact S dec
      ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.1)) ∘ₘ prep, g⟩ δ r)
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    RealizesExact S dec ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.2.1)) ∘ₘ prep, g⟩
      (δ + (L.map (·.2.2)).sum / 2) r :=
  noisy_realization_core S dec prep (Γ ∘ₘ CPTPMap.traceRight) _ _ hideal
    (diamondDist_steps_le_list L hL)

/-- **`noisy_realization_realizes`**: the same for `Realizes` with `ε`. -/
theorem noisy_realization_realizes [PseudoMetricSpace Y] (S : Spec X Y) (dec : POVM Y dY)
    (prep : CPTPMap X (Q × M)) (Γ : CPTPMap Q dY)
    (L : List (CPTPMap (Q × M) (Q × M) × CPTPMap (Q × M) (Q × M) × ℝ)) {ε δ : ℝ} {g r : Grade}
    (hideal : Realizes S dec
      ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.1)) ∘ₘ prep, g⟩ ε δ r)
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    Realizes S dec ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.2.1)) ∘ₘ prep, g⟩ ε
      (δ + (L.map (·.2.2)).sum / 2) r :=
  noisy_realization_core_realizes S dec prep (Γ ∘ₘ CPTPMap.traceRight) _ _ hideal
    (diamondDist_steps_le_list L hL)

/-- PHASE2_SPEC §C.4 (3), (P-stoch) — **`noisy_realization_stochastic`**: when every noisy step is
`mix pᵢ Φᵢ Φ'ᵢ` (with probability `1 − pᵢ` the ideal step, otherwise an arbitrary channel `Φ'ᵢ` on the
whole register; `T` lists the triples `(Φᵢ, pᵢ, Φ'ᵢ)`), the bound is `δ + ∑ pᵢ`. -/
theorem noisy_realization_stochastic (S : Spec X Y) (dec : POVM Y dY) (prep : CPTPMap X (Q × M))
    (Γ : CPTPMap Q dY) (T : List (CPTPMap (Q × M) (Q × M) × Prob × CPTPMap (Q × M) (Q × M)))
    {δ : ℝ} {g r : Grade}
    (hideal : RealizesExact S dec
      ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (T.map (·.1)) ∘ₘ prep, g⟩ δ r) :
    RealizesExact S dec
      ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (T.map fun t => mix t.2.1 t.1 t.2.2) ∘ₘ prep, g⟩
      (δ + (T.map fun t => ((t.2.1 : Prob) : ℝ)).sum) r := by
  have h := noisy_realization S dec prep Γ
    (T.map fun t => (t.1, mix t.2.1 t.1 t.2.2, 2 * ((t.2.1 : Prob) : ℝ)))
    (by simpa [List.map_map, Function.comp_def] using hideal)
    (fun t ht => by
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 ht
      exact diamondDist_mix_le s.2.1 s.1 s.2.2)
  simp only [List.map_map, Function.comp_def] at h
  rw [List.sum_map_mul_left] at h
  convert h using 2
  ring

end Steps

/-! ## The instance: the routed physical circuit (Stage 26, PHASE2_SPEC §C.3) -/

section Phys

open CQRV.Hardware

variable (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ)

/-- PHASE2_SPEC §C.4 (3) — the preparation of the physical run on the extended register: the
embedded all-|0⟩ state of the device, with the classical register at `0…0`. -/
def physPrep (N m : ℕ) (ρ₀ : MState (Reg N × Reg 0)) : CPTPMap Unit (XReg N 0 m) :=
  withBits N 0 m ∘ₘ CPTPMap.replacement ρ₀

/-- PHASE2_SPEC §C.4 (3) — **`phys_noisy`**: the noise theorem at the routed physical circuit. Under
`realizesExact_phys`'s hypotheses (the logical certificate, the validated witness, the start layout),
and a list `L` of triples (ideal step, noisy step, bound) whose ideal steps are the step channels of
the physical circuit followed by `k` identity steps (the ideal readouts), with
`‖Ψᵢ − Φᵢ‖⋄ ≤ ηᵢ` for every triple: the noisy physical channel — the physical preparation, the noisy
steps, the bits traced out, the final layout undone — `RealizesExact` `S` with `δ + (∑ ηᵢ)/2` at the
physical circuit's grade. The premises (P-stoch), (P-ro) are the form of `L`'s bounds; (P-idle) is
that only the listed steps act. -/
theorem phys_noisy (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg C.nData)) (δ : ℝ) (r : Grade)
    (h : RealizesExact S dec (Grover.groverChannel C.nData C) δ r)
    (k : ℕ)
    (L : List (CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                       (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits) ×
               CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                       (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits) × ℝ))
    (hL₁ : L.map (·.1) =
      stepList (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
          (physCircuit (C.nData + (C.nAnc + bb)) G).gates ++
        List.replicate k CPTPMap.id)
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      RealizesExact S dec
        ⟨unembed bb σf ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.2.1)) ∘ₘ
            physPrep (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
              (embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc)),
          Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)⟩
        (δ + (L.map (·.2.2)).sum / 2) (Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)) := by
  obtain ⟨σf, hf, hreal⟩ := realizesExact_phys b C w bb hC G hG hWF hM σ₀ h₀ S dec δ r h
  refine ⟨σf, hf, ?_⟩
  refine noisy_realization S dec _ (unembed bb σf) L ?_ hL
  rw [hL₁, steps_append, steps_replicate_id, CPTPMap.id_compose]
  convert hreal using 2
  · simp only [physGroverChannel, physPrep, stepsOf, channelDenote_eq_steps_chan _ _ _ hWF,
      CPTPMap.compose_assoc]
  · rfl

end Phys

end CQRV

end
