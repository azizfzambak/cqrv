module

public import CQRV.Noise.Realize
public import CQRV.Hardware.Noise

/-!
# CQRV.Noise.Stochastic

Report §2.3.2, §6.6; PHASE2_SPEC §C.4 (3)–(4); STAGE27_TASK.md 27b B1 — **the stochastic premise at
basis operations**. The calibrated operations of a device are the basis gates of the routed circuit,
not the IR gates of their expansion (`sx` expands to `h, s, h`), so the premise (P-stoch) attaches to
basis gates: with probability at least `1 − p_g` the basis gate acts ideally — the composite of the
step channels of its expansion, `basisChan` — and otherwise an arbitrary channel `Φ'_g` on the whole
register acts; (P-ro) adds, after the circuit, one step per data readout, `mix r_j id Φ'_j`.

* `steps_flatMap`: the composite of a flattened list is the composite of the per-element composites;
  `stepsOf_physCircuit`: the step semantics of the routed circuit is the composite of the basis
  composites;
* `phys_noisy_steps`: `phys_noisy` with the ideal list given up to channel equality of its composite;
* **`phys_noisy_stochastic`**: for every choice of the arbitrary channels (they are components of the
  lists `T` and `R`, universally quantified), the noisy physical channel `RealizesExact` `S` with
  `δ + Σ p_g + Σ r_j`;
* `noisy_trDistance` and **`phys_noisy_channel_stochastic`**: the channel form, for a circuit with a
  `phys_channel` theorem and no logical certificate (the MBU gadget): the noisy output is within
  `Σ p_g + Σ r_j` in trace distance of `σ_f`'s embedding of the ideal logical output.

The premises are the hypotheses' form; (P-idle) is that only the listed steps act. Nothing here is a
statement about a device.
-/

@[expose] public section

noncomputable section

namespace CQRV

open scoped MState
open CQRV.Hardware

section Flat

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The composite of a flattened list is the composite of the per-element composites. -/
theorem steps_flatMap {β : Type} (f : β → List (CPTPMap A A)) (L : List β) :
    steps (L.flatMap f) = steps (L.map fun b => steps (f b)) := by
  induction L with
  | nil => rfl
  | cons b L ih => rw [List.flatMap_cons, List.map_cons, steps_append, steps_cons, ih]

theorem steps_map_const_id {β : Type} (L : List β) :
    steps (L.map fun _ => (CPTPMap.id : CPTPMap A A)) = CPTPMap.id := by
  simp [steps_replicate_id]

/-- Trace distance after noisy versus ideal steps, through the same post-processing `Γ`:
at most half the sum of the per-step bounds. -/
theorem noisy_trDistance {Q M dY : Type} [Fintype Q] [DecidableEq Q] [Fintype M] [DecidableEq M]
    [Fintype dY] [DecidableEq dY] (Γ : CPTPMap Q dY)
    (L : List (CPTPMap (Q × M) (Q × M) × CPTPMap (Q × M) (Q × M) × ℝ))
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) (σ : MState (Q × M)) :
    TrDistance (Γ (CPTPMap.traceRight (d₁ := Q) (d₂ := M) (steps (L.map (·.2.1)) σ)))
        (Γ (CPTPMap.traceRight (d₁ := Q) (d₂ := M) (steps (L.map (·.1)) σ))) ≤
      (L.map (·.2.2)).sum / 2 := by
  have hdp := trDistance_cptp_le (Γ ∘ₘ CPTPMap.traceRight) (steps (L.map (·.2.1)) σ)
    (steps (L.map (·.1)) σ)
  have hdom := diamond_dominates (steps (L.map (·.2.1))) (steps (L.map (·.1))) σ
  have hs := diamondDist_steps_le_list L hL
  simp only [CPTPMap.compose_eq] at hdp
  linarith

end Flat

section Phys

variable (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ)

/-- PHASE2_SPEC §C.4 (4), (P-stoch) — the ideal channel of one basis operation on the extended
register: the composite of the step channels of its expansion. -/
def basisChan (N m : ℕ) (g : BasisGate) : CPTPMap (XReg N 0 m) (XReg N 0 m) :=
  stepsOf N 0 m g.expand

/-- The step semantics of the routed circuit is the composite of its basis composites. -/
theorem stepsOf_physCircuit (N m : ℕ) (G : List BasisGate) :
    stepsOf N 0 m (physCircuit N G).gates = steps (G.map (basisChan N m)) := by
  simp only [stepsOf, stepList, physCircuit, List.map_flatMap, steps_flatMap]
  rfl

/-- PHASE2_SPEC §C.4 (3) — `phys_noisy` with the ideal list given up to channel equality: any list
of triples whose ideal composite is the routed circuit's step semantics. -/
theorem phys_noisy_steps (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg C.nData)) (δ : ℝ) (r : Grade)
    (h : RealizesExact S dec (Grover.groverChannel C.nData C) δ r)
    (L : List (CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                       (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits) ×
               CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                       (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits) × ℝ))
    (hL₁ : steps (L.map (·.1)) =
      stepsOf (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
        (physCircuit (C.nData + (C.nAnc + bb)) G).gates)
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
  rw [hL₁]
  convert hreal using 2
  · simp only [physGroverChannel, physPrep, channelDenote_eq_steps_chan _ _ _ hWF,
      CPTPMap.compose_assoc]
  · rfl

/-- PHASE2_SPEC §C.4 (3)–(4) — the noisy step list under the stochastic premise: per basis gate
`(g, p_g, Φ'_g)` the step `mix p_g (basisChan g) Φ'_g`, then per data readout `(r_j, Φ'_j)` the step
`mix r_j id Φ'_j`. -/
def stochasticSteps (N m : ℕ) (T : List (BasisGate × Prob × CPTPMap (XReg N 0 m) (XReg N 0 m)))
    (R : List (Prob × CPTPMap (XReg N 0 m) (XReg N 0 m))) : List (CPTPMap (XReg N 0 m) (XReg N 0 m)) :=
  T.map (fun t => mix t.2.1 (basisChan N m t.1) t.2.2) ++ R.map (fun r => mix r.1 CPTPMap.id r.2)

/-- The stochastic premise as a list of triples for `phys_noisy_steps`: ideal, noisy, bound `2p`. -/
def stochasticTriples (N m : ℕ) (T : List (BasisGate × Prob × CPTPMap (XReg N 0 m) (XReg N 0 m)))
    (R : List (Prob × CPTPMap (XReg N 0 m) (XReg N 0 m))) :
    List (CPTPMap (XReg N 0 m) (XReg N 0 m) × CPTPMap (XReg N 0 m) (XReg N 0 m) × ℝ) :=
  T.map (fun t => (basisChan N m t.1, mix t.2.1 (basisChan N m t.1) t.2.2, 2 * ((t.2.1 : Prob) : ℝ))) ++
    R.map (fun r => (CPTPMap.id, mix r.1 CPTPMap.id r.2, 2 * ((r.1 : Prob) : ℝ)))

theorem stochasticTriples_noisy (N m : ℕ) (T) (R) :
    (stochasticTriples N m T R).map (·.2.1) = stochasticSteps N m T R := by
  simp [stochasticTriples, stochasticSteps, List.map_map, Function.comp_def]

theorem stochasticTriples_ideal (N m : ℕ) (T) (R) :
    (stochasticTriples N m T R).map (·.1) =
      (T.map (·.1)).map (basisChan N m) ++ R.map fun _ => (CPTPMap.id : CPTPMap (XReg N 0 m) (XReg N 0 m)) := by
  simp [stochasticTriples, List.map_map, Function.comp_def]

theorem stochasticTriples_bound (N m : ℕ) (T) (R) :
    ((stochasticTriples N m T R).map (·.2.2)).sum / 2 =
      (T.map fun t => ((t.2.1 : Prob) : ℝ)).sum + (R.map fun r => ((r.1 : Prob) : ℝ)).sum := by
  simp only [stochasticTriples, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    List.sum_map_mul_left]
  ring

theorem stochasticTriples_le (N m : ℕ) (T) (R) :
    ∀ t ∈ stochasticTriples N m T R, diamondDist t.2.1 t.1 ≤ t.2.2 := by
  intro t ht
  simp only [stochasticTriples, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩
  · exact diamondDist_mix_le _ _ _
  · exact diamondDist_mix_le _ _ _

/-- PHASE2_SPEC §C.4 (3)–(4) — **`phys_noisy_stochastic`**: under (P-stoch) at basis operations and
(P-ro) at the data readouts, **for every choice of the arbitrary channels** (the components of `T`
and `R`), the noisy physical channel `RealizesExact` `S` with `δ + Σ p_g + Σ r_j`, at the physical
circuit's grade. `T.map (·.1) = G` fixes the basis gates; the `p_g`, `r_j` and the `Φ'` are free. -/
theorem phys_noisy_stochastic (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg C.nData)) (δ : ℝ) (r : Grade)
    (h : RealizesExact S dec (Grover.groverChannel C.nData C) δ r)
    (T : List (BasisGate × Prob × CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                                         (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)))
    (hT : T.map (·.1) = G)
    (R : List (Prob × CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                             (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits))) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      RealizesExact S dec
        ⟨unembed bb σf ∘ₘ CPTPMap.traceRight ∘ₘ
            steps (stochasticSteps (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits T R) ∘ₘ
            physPrep (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
              (embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc)),
          Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)⟩
        (δ + ((T.map fun t => ((t.2.1 : Prob) : ℝ)).sum + (R.map fun r => ((r.1 : Prob) : ℝ)).sum))
        (Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)) := by
  have hL₁ : steps ((stochasticTriples _ _ T R).map (·.1)) =
      stepsOf (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
        (physCircuit (C.nData + (C.nAnc + bb)) G).gates := by
    rw [stochasticTriples_ideal, hT, steps_append, steps_map_const_id, CPTPMap.id_compose,
      stepsOf_physCircuit]
  have := phys_noisy_steps b C w bb hC G hG hWF hM σ₀ h₀ S dec δ r h (stochasticTriples _ _ T R) hL₁
    (stochasticTriples_le _ _ T R)
  rw [stochasticTriples_noisy, stochasticTriples_bound] at this
  exact this

/-- PHASE2_SPEC §C.4 (4), the channel form (for a circuit with a `phys_channel` theorem and no
logical certificate, such as the MBU gadget): for every choice of the arbitrary channels, the noisy
physical output from the embedded input laid out by `σ₀` is within `Σ p_g + Σ r_j` in trace distance
of `σf`'s embedding of the ideal logical output. -/
theorem phys_noisy_channel_stochastic {n a : ℕ} (G : List BasisGate)
    (hWF : (physCircuit (n + (a + bb)) G).WF)
    (σ₀ σf : Equiv.Perm (Fin (n + (a + bb))))
    (hchan : ∀ ρ : MState (Reg n × Reg a),
      channelDenote (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G) (embed bb σ₀ ρ) =
        embed bb σf (channelDenote n a C ρ))
    (T : List (BasisGate × Prob × CPTPMap (XReg (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G).nBits)
                                         (XReg (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G).nBits)))
    (hT : T.map (·.1) = G)
    (R : List (Prob × CPTPMap (XReg (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G).nBits)
                             (XReg (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G).nBits)))
    (ρ : MState (Reg n × Reg a)) :
    TrDistance
      (CPTPMap.traceRight (d₁ := Reg (n + (a + bb)) × Reg 0) (d₂ := Reg (physCircuit (n + (a + bb)) G).nBits)
        (steps (stochasticSteps (n + (a + bb)) (physCircuit (n + (a + bb)) G).nBits T R)
          (withBits (n + (a + bb)) 0 (physCircuit (n + (a + bb)) G).nBits (embed bb σ₀ ρ))))
      (embed bb σf (channelDenote n a C ρ)) ≤
      (T.map fun t => ((t.2.1 : Prob) : ℝ)).sum + (R.map fun r => ((r.1 : Prob) : ℝ)).sum := by
  have hideal : CPTPMap.traceRight (d₁ := Reg (n + (a + bb)) × Reg 0) (d₂ := Reg (physCircuit (n + (a + bb)) G).nBits)
      (steps ((stochasticTriples _ _ T R).map (·.1)) (withBits (n + (a + bb)) 0 _ (embed bb σ₀ ρ))) =
        embed bb σf (channelDenote n a C ρ) := by
    rw [stochasticTriples_ideal, hT, steps_append, steps_map_const_id, CPTPMap.id_compose,
      ← stepsOf_physCircuit, ← hchan ρ, channelDenote_eq_steps _ _ _ hWF, withBits_apply]
  have h := noisy_trDistance CPTPMap.id (stochasticTriples _ _ T R) (stochasticTriples_le _ _ T R)
    (withBits (n + (a + bb)) 0 _ (embed bb σ₀ ρ))
  rw [CPTPMap.id_MState, CPTPMap.id_MState, hideal, stochasticTriples_noisy,
    stochasticTriples_bound] at h
  exact h

/-! ## The link to the exact bound (`CQRV.Hardware.Noise`) -/

/-- A probability from a rational, clamped to `[0, 1]` (`clamp01`). -/
def probOfRat (q : Rat) : Prob :=
  ⟨((clamp01 q : Rat) : ℝ),
    ⟨by exact_mod_cast le_max_left (0 : Rat) (min 1 q),
     by exact_mod_cast max_le zero_le_one (min_le_left (1 : Rat) q)⟩⟩

theorem probOfRat_val (q : Rat) : ((probOfRat q : Prob) : ℝ) = ((clamp01 q : Rat) : ℝ) := rfl

theorem sum_probOfRat (l : List Rat) :
    (l.map fun q => ((probOfRat q : Prob) : ℝ)).sum = (((l.map clamp01).sum : Rat) : ℝ) := by
  simp [probOfRat_val, Function.comp_def]

/-- The real sum of the probabilities of a list whose probability components are `ps.map probOfRat`
is the cast of the exact sum `Σ clamp01 ps`. -/
theorem sum_probs_of_map {α : Type} (T : List α) (f : α → Prob) (ps : List Rat)
    (h : T.map f = ps.map probOfRat) :
    (T.map fun t => ((f t : Prob) : ℝ)).sum = (((ps.map clamp01).sum : Rat) : ℝ) := by
  rw [show (T.map fun t => ((f t : Prob) : ℝ)) = (T.map f).map (fun p : Prob => (p : ℝ)) from
    List.map_map.symm, h, List.map_map]
  simpa [Function.comp_def] using sum_probOfRat ps

/-- PHASE2_SPEC §C.4 (4) — **the instance form of a conditional certificate**: with the probabilities
fixed to `ps.map probOfRat` (the `p_g` of `noiseProbs`) and `rs.map probOfRat` (the readout rates),
for every choice of the arbitrary channels, the noisy physical channel `RealizesExact` `S` with
`δ' = nb` (the exact `noiseBound`, whose identity `δ + Σ clamp01 ps + Σ clamp01 rs = nb` the
certificate decides in the kernel). -/
theorem phys_noisy_inst_of (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg C.nData)) (δ : ℝ) (r : Grade)
    (h : RealizesExact S dec (Grover.groverChannel C.nData C) δ r)
    (T : List (BasisGate × Prob × CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                                         (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)))
    (hT : T.map (·.1) = G) (ps : List Rat) (hp : T.map (·.2.1) = ps.map probOfRat)
    (R : List (Prob × CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
                             (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)))
    (rs : List Rat) (hR : R.map (·.1) = rs.map probOfRat)
    (δq nb : Rat) (hδ : ((δq : Rat) : ℝ) = δ)
    (hkey : δq + ((ps.map clamp01).sum + (rs.map clamp01).sum) = nb) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      RealizesExact S dec
        ⟨unembed bb σf ∘ₘ CPTPMap.traceRight ∘ₘ
            steps (stochasticSteps (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits T R) ∘ₘ
            physPrep (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
              (embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc)),
          Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)⟩
        ((nb : Rat) : ℝ) (Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)) := by
  have h' := phys_noisy_stochastic b C w bb hC G hG hWF hM σ₀ h₀ S dec δ r h T hT R
  rw [sum_probs_of_map T _ ps hp, sum_probs_of_map R _ rs hR, ← hδ] at h'
  have hnb : ((nb : Rat) : ℝ) =
      ((δq : Rat) : ℝ) + ((((ps.map clamp01).sum : Rat) : ℝ) + (((rs.map clamp01).sum : Rat) : ℝ)) := by
    rw [← hkey]; push_cast; ring
  rw [hnb]
  exact h'

end Phys

end CQRV

end
