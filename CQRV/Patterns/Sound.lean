module

public import CQRV.Patterns.Basic
public import CQRV.Grover.Lemma
public import CQRV.Grover.AmplitudeEstimation

/-!
# CQRV.Patterns.Sound

Report §3.2, Definition 4.1 (the QPLP as the dependent record ⟨S, φ, C, g, π⟩); PHASE2_SPEC.md §A.5
amendment (6) and the refinement (6′) at the 21a2 review — the **semantic layer** of the QPLP
record (Stage 21a3), Physlib-side, imported by `CQRV.lean` only: `QPLP.Sem Params` states, for every
parameter `p` satisfying the side conditions `pre p`, that the circuit the Physlib-free builder
returns realizes the specification under the decoding within the stated grade and restores its
ancillae while applying the target unitary.

**The claim is uniform** (6′): the proof field states `Realizes` for every instance. The Grover
output `Reg n` has no metric, so it enters through the type synonym `DiscreteOut (Reg n)` with the
discrete metric (distance 0 or 1); its ε = 0 realization is the existing `RealizesExact`
(`realizes_zero_iff`, `realizes_discrete_of_exact`). The two instances are `groverSem` (from
`grover_parametric_lemma`) and `countSem` (from `ae_parametric_lemma_mk`); each proof field is
exactly its lemma's conclusion read through the record. Neither lemma is re-proved. The composed
bound of a certificate is the corollary `QPLP.Sem.realizes_of_le` (monotonicity of `Realizes` in
the grade).
-/

@[expose] public section

namespace CQRV.Patterns

open CQRV CQRV.Grover CQRV.Synthesis CQRV.Counting

/-! ## The discrete output -/

/-- PHASE2_SPEC §A.5 (6′) — a type with the discrete metric (distance 0 or 1), as a synonym (the
carrier is `α`; the metric is the point). -/
def DiscreteOut (α : Type) : Type := α

instance (α : Type) [Fintype α] : Fintype (DiscreteOut α) := inferInstanceAs (Fintype α)

instance (α : Type) [DecidableEq α] : DecidableEq (DiscreteOut α) :=
  inferInstanceAs (DecidableEq α)

/-- The discrete metric: `dist x y = if x = y then 0 else 1`. Mathlib has no reusable discrete
metric instance (checked, CLAUDE.md rule 2), so it is defined here. -/
noncomputable instance (α : Type) [DecidableEq α] : MetricSpace (DiscreteOut α) where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · subst hxy; simp
    · by_cases hyz : y = z
      · subst hyz; simp [hxy]
      · simp only [hxy, hyz, ↓reduceIte]
        split <;> norm_num
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    simp [hne] at h

/-- The distance of the discrete metric. -/
theorem DiscreteOut.dist_eq {α : Type} [DecidableEq α] (x y : DiscreteOut α) :
    dist x y = if x = y then 0 else 1 := rfl

/-- PHASE2_SPEC §A.5 (6′) — an exact realization is a `Realizes` with ε = 0 at the discrete output
(`realizes_zero_iff`: `S^0 = S`). -/
theorem realizes_discrete_of_exact {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype dY] [DecidableEq dY] {S : Spec X Y} {dec : POVM Y dY}
    {Φ : GradedChannel X dY} {δ : ℝ} {g : Grade} (h : RealizesExact S dec Φ δ g) :
    Realizes (Y := DiscreteOut Y) S dec Φ 0 δ g :=
  realizes_zero_iff.2 h

/-! ## Definition 4.1 as a dependent record -/

/-- Report §3.2, Definition 4.1; PHASE2_SPEC §A.5 (6), (6′) — the semantic QPLP record over a type
of parameters: the side conditions `pre`, the data register size, the output type with its
instances, the specification and the decoding, the Physlib-free builder, ε, δ and the grade
function, the target unitary of the restoration, and the proof: for every instance whose builder
succeeds, realization within the grade and restoration. -/
structure QPLP.Sem (Params : Type) where
  (pre : Params → Prop)
  (nData : Params → ℕ)
  (Out : Params → Type)
  [fin : ∀ p, Fintype (Out p)]
  [dec : ∀ p, DecidableEq (Out p)]
  [pm : ∀ p, PseudoMetricSpace (Out p)]
  (spec : ∀ p, Spec Unit (Out p))
  (povm : ∀ p, POVM (Out p) (Reg (nData p)))
  /-- the Physlib-free builder -/
  (circuit : Params → Except DSL.Diagnostic Circuit)
  (eps : Params → ℝ)
  (delta : Params → ℝ)
  (grade : Params → Circuit → Grade)
  (target : ∀ p, 𝐔[Reg (nData p)])
  (proof : ∀ p, pre p → ∀ C, circuit p = .ok C →
    Realizes (spec p) (povm p) (groverChannel (nData p) C) (eps p) (delta p) (grade p C) ∧
      AncRestore (nData p) C.nAnc C (target p))

attribute [instance] QPLP.Sem.fin QPLP.Sem.dec QPLP.Sem.pm

/-- Report §3.1.2, §2.3.1 — `Realizes` is monotone in the grade (the fibre test `Φ.grade ≤ r`). -/
theorem Realizes.mono_grade {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype dY] [DecidableEq dY] [PseudoMetricSpace Y] {S : Spec X Y}
    {dec : POVM Y dY} {Φ : GradedChannel X dY} {ε δ : ℝ} {g g' : Grade}
    (h : Realizes S dec Φ ε δ g) (hg : g ≤ g') : Realizes S dec Φ ε δ g' :=
  ⟨le_trans h.1 hg, h.2⟩

/-- PHASE2_SPEC §A.5 (6) — a certificate's composed bound `g ≥ grade p C` is a consequence of the
record: realization within every grade above the stated one. -/
theorem QPLP.Sem.realizes_of_le {Params : Type} (S : QPLP.Sem Params) (p : Params) (hp : S.pre p)
    (C : Circuit) (hC : S.circuit p = .ok C) (g : Grade) (hg : S.grade p C ≤ g) :
    Realizes (S.spec p) (S.povm p) (groverChannel (S.nData p) C) (S.eps p) (S.delta p) g :=
  Realizes.mono_grade (S.proof p hp C hC).1 hg

/-! ## The two instances -/

/-- The parameters of the Grover instance: the Grover parameters (`n`, `M ≥ 1`, the certified
oracle, `hM_card`), a certified diffusion and the iteration count `r`. -/
structure GroverSemParams where
  gp : GroverParams
  D : DiffusionCert gp.n
  r : ℕ

/-- Report §8.2.4, §8.3.4 Figure 8.1; PHASE2_SPEC §A.5 (6′) — **the Grover QPLP**: Definition 4.1
instantiated from `grover_parametric_lemma`, with the discrete output. `pre` is the side condition
`1 ≤ M` of `groverEntry` (also a field of the parameters); ε = 0, δ = 1 − sin²((2r+1)θ); the grade
is the measured grade of the circuit; the target is `G^r H^{⊗n}`. -/
noncomputable def groverSem : QPLP.Sem GroverSemParams where
  pre p := 1 ≤ p.gp.M
  nData p := p.gp.n
  Out p := DiscreteOut (Reg p.gp.n)
  spec p := SearchSpec p.gp.oracle.P
  povm p := basisPOVM p.gp.n
  circuit p := groverCircuit p.gp.oracle.N p.gp.n p.r
  eps _ := 0
  delta p := 1 - Real.sin ((2 * p.r + 1) * p.gp.θ) ^ 2
  grade _ C := Synthesis.grade C
  target p := groverOp p.gp.oracle.P ^ p.r * hadamardU p.gp.n
  proof p _ _C hC :=
    have h := grover_parametric_lemma p.gp p.D p.r hC
    ⟨realizes_discrete_of_exact h.1, h.2⟩

/-- The parameters of the counting instance: `n`, `M`, `m`, the network with the facts
`ae_parametric_lemma_mk` takes, the shape and the mode. -/
structure CountSemParams where
  n : ℕ
  M : ℕ
  m : ℕ
  N : Network
  P : Reg n → Bool
  hcard : (Finset.univ.filter fun x => P x = true).card = M
  hN : N.WF
  hn : N.nInputs = n
  h1 : N.outputs.length = 1
  hP : N.pred n = P
  shape : DiffusionShape
  mode : UncomputeMode

/-- PHASE2_SPEC §A.4, §A.5 (6) — **the counting QPLP**: Definition 4.1 instantiated from
`ae_parametric_lemma_mk`. `pre` holds the side conditions `1 ≤ m` (of `countEntry`) and `1 ≤ M`;
the output is `CountOut m (M/2^n)` with its pseudo-metric; ε = `ae_eps (M/2^n) m`, δ = `ae_delta`;
the grade is the measured grade of the circuit (a certificate's composed bound is
`realizes_of_le`); the target is `U_count P m none`. -/
noncomputable def countSem : QPLP.Sem CountSemParams where
  pre p := 1 ≤ p.m ∧ 1 ≤ p.M
  nData p := p.n + p.m
  Out p := CountOut p.m (p.M / 2 ^ p.n : ℝ)
  spec p := CountSpec p.m (p.M / 2 ^ p.n : ℝ)
  povm p := countPOVM p.n p.m (p.M / 2 ^ p.n : ℝ)
  circuit p := countingCircuit p.N p.n p.m none p.shape p.mode
  eps p := ae_eps (p.M / 2 ^ p.n : ℝ) p.m
  delta _ := ae_delta
  grade _ C := Synthesis.grade C
  target p := U_count p.P p.m none
  proof p hp _C hC :=
    ae_parametric_lemma_mk p.n p.M hp.2 p.P p.hcard hp.1 p.hN p.hn p.h1 p.hP hC _ le_rfl

end CQRV.Patterns

end
