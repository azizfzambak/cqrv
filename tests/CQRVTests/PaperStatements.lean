module

public import CQRV.Realizability.Obstruction
public import CQRV.Realizability.Composition
public import CQRV.Realizability.Coherent
public import CQRV.Circuit.OracleCorrect
public import CQRV.Circuit.QFTCorrect
public import CQRV.Circuit.MBUGeneral
public import CQRV.Circuit.MBUClifford
public import CQRV.Circuit.MBUBoundary
public import CQRV.Circuit.RestoreRegimes
public import CQRV.Grover.Lemma
public import CQRV.Grover.MczFewAll
public import CQRV.Grover.Counting
public import CQRV.Grover.AmplitudeEstimation
public import CQRV.Synthesis.Problem1
public import CQRV.Hardware.CheckSound
public import CQRV.Noise.Stochastic
meta import CQRV.Realizability.Obstruction
meta import CQRV.Realizability.Composition
meta import CQRV.Realizability.Coherent
meta import CQRV.Circuit.OracleCorrect
meta import CQRV.Circuit.QFTCorrect
meta import CQRV.Circuit.MBUGeneral
meta import CQRV.Circuit.MBUClifford
meta import CQRV.Circuit.MBUBoundary
meta import CQRV.Circuit.RestoreRegimes
meta import CQRV.Grover.Lemma
meta import CQRV.Grover.MczFewAll
meta import CQRV.Grover.Counting
meta import CQRV.Grover.AmplitudeEstimation
meta import CQRV.Synthesis.Problem1
meta import CQRV.Hardware.CheckSound
meta import CQRV.Noise.Stochastic

/-!
# The paper's Lean statements, checked against the library (revision R10)

REVIEW_RESPONSE_1 §4 R10; docs/tasks/REVB_TASK.md. Paper v2, Appendix A, transliterates the
library's statements by hand. Each `example` below restates one of them in full (implicit and
instance arguments included) and proves it by the library name applied to its arguments, so that
the kernel confirms that the stated form is the library's. `docs/PAPER_STATEMENTS.md` maps every
name to its file and line and to the line here. Nothing is proved anew: a statement that differed
from the library in substance would not elaborate.
-/

namespace CQRV.Tests.PaperStatements

open CQRV CQRV.Hardware CQRV.Grover CQRV.Synthesis Matrix
open scoped MState Kronecker

@[expose] public section

/-! ## The definitions (report §2.1.2, §2.3.1, §6.2.1) -/

example {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype dY]
    [DecidableEq dY] [PseudoMetricSpace Y] (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY)
    (ε δ : ℝ) (r : Grade) :
    Realizes S dec Φ ε δ r ↔
      (Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S.relax ε x)) :=
  Iff.rfl

example {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype dY]
    [DecidableEq dY] (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (δ : ℝ) (r : Grade) :
    RealizesExact S dec Φ δ r ↔
      (Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S x)) :=
  Iff.rfl

example (n a : ℕ) (C : Circuit) (U : 𝐔[Reg n]) :
    AncRestore n a C U ↔
      ∀ ρ : MState (Reg n), channelDenote n a C (ρ ⊗ᴹ ancZero a) = (U ◃ ρ) ⊗ᴹ ancZero a :=
  Iff.rfl

example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Λ₁ Λ₂ : CPTPMap A B) :
    diamondDist Λ₁ Λ₂ = ⨆ ρ : MState (A × A),
      2 * TrDistance ((Λ₁ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id (dIn := A)) ρ) :=
  rfl

/-! ## No cloning (report §2.2.2, Theorem 3.1; R1) -/

example {d : Type} [Fintype d] [Nonempty d] :
    ¬ ∃ C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ), ∀ ψ : d → ℂ, C ψ = fun ij => ψ ij.1 * ψ ij.2 :=
  no_cloning_linear

example {d : Type} [Fintype d] [DecidableEq d] (hd : 2 ≤ Fintype.card d) :
    ¬ ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ,
      ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ) :=
  no_cloning_pure hd

example {d : Type} [Fintype d] [DecidableEq d] (hd : Fintype.card d = 1) :
    ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ,
      ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ) :=
  pure_cloning_of_card_one hd

/-! ## Composition (report §2.3.2, Theorems 3.3a and 3.3b) -/

example {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] [Fintype dY] [DecidableEq dY] [Fintype dZ] [DecidableEq dZ]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {ε_f ε_g δ_f δ_g : ℝ} {r s : Grade}
    (hf : Realizes S_f dec_f Φ ε_f δ_f r) (hg : Realizes S_g dec_g Ψ ε_g δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    Realizes (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (ε_f + ε_g) (δ_f + δ_g) (r + s) :=
  measured_composition_pseudo hf hg hdom hnonexp hδf hδg hδg1

example {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] [Fintype dY] [DecidableEq dY] [Fintype dZ] [DecidableEq dZ] [MetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec : POVM Z dZ}
    {Φ₁ : CPTPMap X dY} {Ψ₁ : CPTPMap dY dZ} {Φ₂ : GradedChannel X dY} {Ψ₂ : GradedChannel dY dZ}
    {ε₀ δ₀ η_f η_g : ℝ} {r s : Grade}
    (hideal : Realizes (S_g.comp S_f) dec ⟨Ψ₁ ∘ₘ Φ₁, 0⟩ ε₀ δ₀ 0)
    (hΦ : diamondDist Φ₂.chan Φ₁ ≤ η_f) (hΨ : diamondDist Ψ₂.chan Ψ₁ ≤ η_g)
    (hr : Φ₂.grade ≤ r) (hs : Ψ₂.grade ≤ s) :
    Realizes (S_g.comp S_f) dec ⟨Ψ₂.chan ∘ₘ Φ₂.chan, Φ₂.grade + Ψ₂.grade⟩ ε₀
      (δ₀ + (η_f + η_g) / 2) (r + s) :=
  coherent_composition_diamond hideal hΦ hΨ hr hs

/-! ## Oracle synthesis and Lemma 6.3.2 (report §6.1, §6.3.2, §9.1.1) -/

example (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C) (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData)) :=
  lemma_6_3_2_xor N C hC hWF

example {N : Network} {C : Circuit} (hN : N.WF) (hC : synthesizeOracle N = .ok C) : C.WF :=
  synthesizeOracle_WF hN hC

example {N : Network} (hN : N.WF) (h1 : N.outputs.length = 1) :
    ∃ C, synthesizeOracle N = .ok C :=
  synthesizeOracle_succeeds hN h1

/-! ## Grover (report §5.2.4, §8.2) and the few-ancilla MCZ (§6.1.4; KG Theorem 5.1) -/

example (gp : GroverParams) (Dc : Circuit) (hDb : Dc.bitsOk = true)
    (hDr : ∀ a, Dc.nAnc ≤ a → AncRestore gp.n a Dc (diffU gp.n)) (r : ℕ) {C : Circuit}
    (hC : C = groverCircuitOf gp.oracle.C Dc gp.n r) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
        (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) ∧
      AncRestore gp.n C.nAnc C (groverOp gp.oracle.P ^ r * hadamardU gp.n) :=
  grover_parametric_lemma_diff gp Dc hDb hDr r hC

example {n : ℕ} (hn : n ≠ 0) : ∃ C, mczFew n .logDepth = .ok C := mczFew_logDepth_ok hn

example {n : ℕ} {C : Circuit} (hC : mczFew n .logDepth = .ok C) :
    AncRestore n 2 C (phaseOracle allOnes) :=
  mczFew_logDepth_ancRestore hC

example {n : ℕ} {D : Circuit} (hD : diffusionFew n .logDepth = .ok D) :
    ∀ a, D.nAnc ≤ a → AncRestore n a D (diffU n) :=
  diffusionFew_logDepth_ancRestore hD

/-! ## Counting and amplitude estimation (PHASE2_SPEC §A.4, §A.2) -/

open Classical in
example (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) :
    8 / Real.pi ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg m =>
        |Real.sin (Real.pi * y.toNat / 2 ^ m) ^ 2 - gp.M / 2 ^ gp.n| ≤ ae_eps (gp.M / 2 ^ gp.n) m),
      phaseDist gp m y :=
  qpe_success gp hm

example (gp : GroverData) {m : ℕ} (hm : 1 ≤ m) {N : Network} (hN : N.WF) (hn : N.nInputs = gp.n)
    (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P) {shape : DiffusionShape}
    {mode : UncomputeMode} {C : Circuit} (hC : countingCircuit N gp.n m none shape mode = .ok C)
    (g : Grade) (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (gp.M / 2 ^ gp.n : ℝ)) (countPOVM gp.n m (gp.M / 2 ^ gp.n : ℝ))
        (groverChannel (gp.n + m) C) (ae_eps (gp.M / 2 ^ gp.n : ℝ) m) ae_delta g ∧
      AncRestore (gp.n + m) C.nAnc C (Counting.U_count gp.P m none) :=
  ae_parametric_lemma gp hm hN hn h1 hP hC g hg

example (m kmax : ℕ) :
    diamondDist (channelDenote m 0 (qftCircuit m)) (channelDenote m 0 (aqftCircuit m kmax)) ≤
      eta_aqft m kmax :=
  aqft_diamond_le m kmax

/-! ## Measurement-based uncomputation (report §6.2; PHASE2_SPEC §B.1) and the regimes (R2) -/

example {n a : ℕ} {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) (hanc : ∃ i, i < a ∧ t = .anc i)
    {f : Reg n → Bool} {φ : Reg n → ℂ} (hB : ComputesInto n a B t f φ) (hO : PhaseImpl n a O f) :
    AncRestore n a C (diagU φ hB.norm) :=
  mbu_general hWF hgates hanc hB hO

example {n : ℕ} (f : Reg n → Bool) : IsCliffordDiag (phaseDiag f) ↔ IsQuadratic f :=
  clifford_iff_quadratic f

example {n a : ℕ} {B : List Gate} (hB : ∀ g ∈ B, g.qubitsOk n = true ∧ g.isUnitary = true)
    {t : Qubit} (hanc : ∃ i, i < a ∧ t = .anc i) (f : Reg n → Bool) :
    (∃ (j : ℕ) (O : List Gate) (C : Circuit), C.nData = n ∧ C.WF ∧
        C.gates = B ++ [.z t] ++ mbuUncompute t j O ∧ PhaseImpl n a O f) ↔ IsQuadratic f :=
  mbu_exactly_quadratic hB hanc f

example {n a : ℕ} (ω : MState (Reg n × Reg a)) (hω : ancProj n a * ω.m * ancProj n a = ω.m) :
    ω = ω.traceRight ⊗ᴹ ancZero a :=
  supportFactor ω hω

example {n a : ℕ} {C : Circuit} {U : 𝐔[Reg n]} :
    AncRestoreCond n a C U (fun _ => true) ↔ AncRestore n a C U :=
  ancRestoreCond_true_iff

/-! ## The 8n − 24 theorem (PHASE2_SPEC §B.2, 23c) -/

example {L : ℕ} {s : Problem1.P1State L} {os : List (Problem1.P1Op L)} {n : ℕ}
    (h : Problem1.valid s os = true) (hn : s.live = n) (hf : s.freshCard = 2)
    (hk : (Problem1.run s os).live ≤ 2) (h4 : 4 ≤ n) : 8 * n - 24 ≤ Problem1.cost s os :=
  Problem1.problem1_T_lower_bound h hn hf hk h4

/-! ## The hardware witness (PHASE2_SPEC §C.3) -/

example (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ) (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      ∀ ρ : MState (Reg C.nData × Reg C.nAnc),
        channelDenote (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G)
            (embed bb σ₀ ρ) =
          embed bb σf (channelDenote C.nData C.nAnc C ρ) :=
  applyWitness_sound b C w bb hC G hG hWF hM σ₀ h₀

example (b : TargetBasis) (C : Circuit) (hC : C.WF) (w : Witness) (N : ℕ) (G : List BasisGate)
    (h : applyWitnessQ b C w N = .ok G) : applyWitness b C w N = .ok G :=
  applyWitnessQ_ok b C hC w N G h

example (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ) (hC : C.WF) (G : List BasisGate)
    (hG : applyWitnessQ b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀) :
    w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) (finalPerm b C w _ σ₀) ∧
      ∀ ρ : MState (Reg C.nData × Reg C.nAnc),
        channelDenote (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G)
            (embed bb σ₀ ρ) =
          embed bb (finalPerm b C w _ σ₀) (channelDenote C.nData C.nAnc C ρ) :=
  applyWitnessQ_sound b C w bb hC G hG hWF hM σ₀ h₀

/-! ## Noise (report §2.3.2, §6.6; PHASE2_SPEC §C.4) -/

example (n a : ℕ) (C : Circuit) (hC : C.WF) (ρ : MState (Reg n × Reg a)) :
    channelDenote n a C ρ =
      CPTPMap.traceRight (d₁ := Reg n × Reg a) (d₂ := Reg C.nBits)
        (stepsOf n a C.nBits C.gates (ρ ⊗ᴹ ancZero C.nBits)) :=
  channelDenote_eq_steps n a C hC ρ

example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (p : Prob)
    (Φ Φ' : CPTPMap A B) : diamondDist (mix p Φ Φ') Φ ≤ 2 * (p : ℝ) :=
  diamondDist_mix_le p Φ Φ'

example {X Y dY Q M : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype dY]
    [DecidableEq dY] [Fintype Q] [DecidableEq Q] [Fintype M] [DecidableEq M]
    (S : Spec X Y) (dec : POVM Y dY) (prep : CPTPMap X (Q × M)) (Γ : CPTPMap Q dY)
    (L : List (CPTPMap (Q × M) (Q × M) × CPTPMap (Q × M) (Q × M) × ℝ)) {δ : ℝ} {g r : Grade}
    (hideal : RealizesExact S dec
      ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.1)) ∘ₘ prep, g⟩ δ r)
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    RealizesExact S dec ⟨Γ ∘ₘ CPTPMap.traceRight ∘ₘ steps (L.map (·.2.1)) ∘ₘ prep, g⟩
      (δ + (L.map (·.2.2)).sum / 2) r :=
  noisy_realization S dec prep Γ L hideal hL

example (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ) (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] (S : Spec Unit Y) (dec : POVM Y (Reg C.nData)) (δ : ℝ)
    (r : Grade) (h : RealizesExact S dec (Grover.groverChannel C.nData C) δ r)
    (T : List (BasisGate × Prob ×
      CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
              (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)))
    (hT : T.map (·.1) = G)
    (R : List (Prob ×
      CPTPMap (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits)
              (XReg (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G).nBits))) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      RealizesExact S dec
        ⟨unembed bb σf ∘ₘ CPTPMap.traceRight ∘ₘ
            steps (stochasticSteps (C.nData + (C.nAnc + bb))
              (physCircuit (C.nData + (C.nAnc + bb)) G).nBits T R) ∘ₘ
            physPrep (C.nData + (C.nAnc + bb)) (physCircuit (C.nData + (C.nAnc + bb)) G).nBits
              (embed bb σ₀ (ancZero C.nData ⊗ᴹ ancZero C.nAnc)),
          Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)⟩
        (δ + ((T.map fun t => ((t.2.1 : Prob) : ℝ)).sum + (R.map fun r => ((r.1 : Prob) : ℝ)).sum))
        (Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)) :=
  phys_noisy_stochastic b C w bb hC G hG hWF hM σ₀ h₀ S dec δ r h T hT R

end

end CQRV.Tests.PaperStatements
