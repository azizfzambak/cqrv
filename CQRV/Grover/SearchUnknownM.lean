module

public import CQRV.Patterns.Sound
public import CQRV.Realizability.MeasurePrepare
public import CQRV.Certify.Specialize

/-!
# CQRV.Grover.SearchUnknownM

Stage 21b2 (PHASE2_SPEC §A.7, §A.9 "21b1 done" and refinements (9)–(12); report §2.3.2, §8.2) —
**search with an unknown number of solutions**: quantum counting (stage 1, the record `countSem`)
followed, through the measured interface of Theorem 3.3a, by Grover search at the iteration count
read off the estimate (stage 2, the record `groverSem` on every branch).

* `searchStage n C g` — stage 2 as one `GradedChannel` on the counting output: the
  measure-and-prepare channel that, on the outcome `y`, prepares the output of the Grover circuit
  `C y`; its declared grade `g` must bound every branch (refinement (9): the channel runs `C y` on
  every outcome, not only on the outcomes in the domain), which `search_unknown_M` carries as the
  conjunct `∀ y, (groverChannel n (C y)).grade ≤ (searchStage n C g).grade`.
* `SearchAfterCount m a P ε` — the specification of stage 2: on an estimate within `ε` of `a`,
  a solution of `P`; its domain, non-expansiveness and compatibility with `CountSpec`.
* `searchStage_realizes` — stage 2 realizes `SearchAfterCount` exactly, with the δ of `groverSem`,
  under the good-domain hypothesis: every outcome within `ε` of `a` gets the circuit `C₀` of `r₀`
  iterations (refinement (10): the post-processing table `C` is a parameter; `rStar` computes in
  `Float`, which no theorem evaluates).
* `search_unknown_M` — the composite over the two records' parameters (refinement (11)), by
  `measured_composition_pseudo` from `countSem.proof` and `searchStage_realizes`; the circuits,
  ε and δ are the records' fields, the specifications and decodings are written out
  (`CountSpec`, `countPOVM`, `basisPOVM`: what the records' fields reduce to; the record
  projections of the output types would carry their own instances into the statement); `_rat`
  states δ through `groverDelta`, as the certificates' `delta_eq` do.
* `domain_8_32_5`, `search_unknown_M_8_32_5` — the instance `grover_pred_037` at `(n, M, m) =
  (8, 32, 5)`: the domain lemma (real analysis specific to the instance, refinement (12)) and the
  corollary whose remaining hypotheses are decidable circuit facts at the instance.

No committed certificate carries this (refinement (12)): the domain lemma is instance-specific
real analysis that no generator produces.
-/

@[expose] public section

noncomputable section

namespace CQRV.Grover

open CQRV CQRV.Patterns CQRV.Synthesis CQRV.Certify Real

/-! ## Stage 2 as a graded channel -/

/-- Report §2.3.2 (Stage 21b2) — **stage 2**: on the counting outcome `y`, run the Grover circuit
`C y` (the measure-and-prepare channel of the branch outputs); declared grade `g`. -/
def searchStage (n : ℕ) {m : ℕ} {a : ℝ} (C : CountOut m a → Circuit) (g : Grade) :
    GradedChannel (CountOut m a) (Reg n) :=
  ⟨measurePrepare fun y => (groverChannel n (C y)).chan (encode ()), g⟩

/-- On the encoded outcome `y`, stage 2 is the Grover channel of `C y` on `encode ()`. -/
theorem searchStage_encode (n : ℕ) {m : ℕ} {a : ℝ} (C : CountOut m a → Circuit) (g : Grade)
    (y : CountOut m a) :
    (searchStage n C g).chan (encode y) = (groverChannel n (C y)).chan (encode ()) :=
  measurePrepare_encode _ y

/-- PHASE2_SPEC §A.9 (9) — the declared grade of stage 2 bounds the grade of every branch. -/
theorem searchStage_grade_bounds (n : ℕ) {m : ℕ} {a : ℝ} (C : CountOut m a → Circuit) (g : Grade)
    (hg : ∀ y, Synthesis.grade (C y) ≤ g) (y : CountOut m a) :
    (groverChannel n (C y)).grade ≤ (searchStage n C g).grade := by
  show Synthesis.grade (C y) ≤ g
  exact hg y

/-! ## The specification of stage 2 -/

/-- Report §2.3.2, §8.1 (Stage 21b2) — **search after counting**: on an estimate within `ε` of `a`,
accept a solution of `P` (discrete output, as `groverSem`). -/
def SearchAfterCount (m : ℕ) (a : ℝ) {n : ℕ} (P : Reg n → Bool) (ε : ℝ) :
    Spec (CountOut m a) (DiscreteOut (Reg n)) :=
  fun y z => |countEst m a y - a| ≤ ε ∧ P z = true

/-- Report §8.1 — `M ≥ 1` solutions give a solution. -/
theorem exists_solution_of_card {n M : ℕ} (P : Reg n → Bool)
    (hcard : (Finset.univ.filter fun x => P x = true).card = M) (hM : 1 ≤ M) :
    ∃ z, P z = true := by
  have hpos : 0 < (Finset.univ.filter fun x => P x = true).card := by rw [hcard]; exact hM
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

/-- Report §2.1.1 — the domain of `SearchAfterCount`, when `P` has a solution: the outcomes whose
estimate lies within `ε` of `a`. -/
theorem searchAfterCount_dom {m : ℕ} {a : ℝ} {n : ℕ} (P : Reg n → Bool) (hex : ∃ z, P z = true)
    (ε : ℝ) (y : CountOut m a) :
    y ∈ (SearchAfterCount m a P ε).dom ↔ |countEst m a y - a| ≤ ε := by
  constructor
  · rintro ⟨z, hz, -⟩
    exact hz
  · intro h
    obtain ⟨z, hz⟩ := hex
    exact ⟨z, h, hz⟩

/-- Report §2.3.2, Theorem 3.3a hypothesis (ii) — `SearchAfterCount` is non-expansive: for `y` in
the domain, every output acceptable for `y'` is acceptable for `y` (take `z = z'`). -/
theorem searchAfterCount_nonexp {m : ℕ} {a : ℝ} {n : ℕ} (P : Reg n → Bool) (ε : ℝ) :
    ∀ y ∈ (SearchAfterCount m a P ε).dom, ∀ y' z', SearchAfterCount m a P ε y' z' →
      ∃ z, SearchAfterCount m a P ε y z ∧ dist z z' ≤ dist y y' := by
  rintro y ⟨_, hy, -⟩ y' z' ⟨-, hz'⟩
  exact ⟨z', ⟨hy, hz'⟩, by rw [dist_self]; exact dist_nonneg⟩

/-- Report §2.3.2, Theorem 3.3a hypothesis (i) — domain compatibility with `CountSpec` at the same
`ε`: an `ε`-acceptable counting outcome lies in the domain of `SearchAfterCount`
(`countSpec_relax`). -/
theorem searchAfterCount_domCompat {m : ℕ} {a : ℝ} {n : ℕ} (P : Reg n → Bool)
    (hex : ∃ z, P z = true) (ε : ℝ) :
    ∀ x ∈ (CountSpec m a).dom, ∀ y, (CountSpec m a).relax ε x y →
      y ∈ (SearchAfterCount m a P ε).dom := by
  intro x _ y hy
  cases x
  exact (searchAfterCount_dom P hex ε y).2 ((countSpec_relax m a ε y).1 hy)

/-! ## The δ of the records -/

/-- Report §8.2.3 — `ae_delta = 1 − 8/π² ≥ 0` (`π > 3`). -/
theorem ae_delta_nonneg : 0 ≤ ae_delta := by
  unfold ae_delta
  have h := Real.pi_gt_three
  rw [sub_nonneg, div_le_one (by positivity)]
  nlinarith

/-- `0 ≤ 1 − sin²((2r+1)θ)`. -/
theorem groverSem_delta_nonneg (p : GroverSemParams) : 0 ≤ groverSem.delta p := by
  show 0 ≤ 1 - Real.sin ((2 * p.r + 1) * p.gp.θ) ^ 2
  exact sub_nonneg.2 (Real.sin_sq_le_one _)

/-- `1 − sin²((2r+1)θ) ≤ 1`. -/
theorem groverSem_delta_le_one (p : GroverSemParams) : groverSem.delta p ≤ 1 := by
  show 1 - Real.sin ((2 * p.r + 1) * p.gp.θ) ^ 2 ≤ 1
  exact sub_le_self _ (sq_nonneg _)

/-- Report §5.1.3, §8.4.1 — the δ of `groverSem` is the rational `groverDelta r n M` of the
certificates (`sin_sq_odd_mul`, as `grover_certificate`). -/
theorem groverSem_delta_eq (p : GroverSemParams) :
    groverSem.delta p = ((groverDelta p.r p.gp.n p.gp.M : ℚ) : ℝ) := by
  have hs : ((solutionFraction p.gp.n p.gp.M : ℚ) : ℝ) = Real.sin p.gp.θ ^ 2 := by
    rw [p.gp.sin_θ_eq, Real.sq_sqrt (by positivity), solutionFraction]
    push_cast
    rfl
  show 1 - Real.sin ((2 * p.r + 1) * p.gp.θ) ^ 2 = _
  rw [sin_sq_odd_mul _ _ hs p.r, groverDelta, Rat.cast_sub, Rat.cast_one]

/-! ## Stage 2 realizes its specification -/

/-- Report §2.3.2, §8.2.4 (Stage 21b2) — **stage 2 realizes `SearchAfterCount`** exactly (ε = 0)
with the δ of `groverSem` at `r₀`, under the good-domain hypothesis `hgood`: every outcome whose
estimate lies within `ε` of `a` gets the circuit `C₀` of `groverSem.circuit p` (refinement (10)).
The proof is `groverSem.proof` on the branch `C₀`, through `searchStage_encode`; the outcomes
outside the domain are unconstrained. -/
theorem searchStage_realizes (p : GroverSemParams) {C₀ : Circuit}
    (hC₀ : groverSem.circuit p = .ok C₀) {m : ℕ} {a : ℝ} (ε : ℝ) (C : CountOut m a → Circuit)
    (hgood : ∀ y, |countEst m a y - a| ≤ ε → C y = C₀) (g : Grade) :
    Realizes (SearchAfterCount m a p.gp.oracle.P ε) (basisPOVM p.gp.n) (searchStage p.gp.n C g) 0
      (groverSem.delta p) g := by
  have hex : ∃ z, p.gp.oracle.P z = true :=
    exists_solution_of_card _ p.gp.hM_card p.gp.hM_pos
  refine ⟨le_rfl, fun y hy => ?_⟩
  have hb := (searchAfterCount_dom _ hex ε y).1 hy
  rw [searchStage_encode, hgood y hb]
  -- the proof field of the record, at the discrete output
  have h0 : Realizes (Y := DiscreteOut (Reg p.gp.n)) (SearchSpec p.gp.oracle.P) (basisPOVM p.gp.n)
      (groverChannel p.gp.n C₀) 0 (groverSem.delta p) (Synthesis.grade C₀) :=
    (groverSem.proof p p.gp.hM_pos C₀ hC₀).1
  have h := realizes_zero_iff.1 h0
  have hdom : () ∈ (SearchSpec p.gp.oracle.P).dom := by
    obtain ⟨z, hz⟩ := hex
    exact ⟨z, hz⟩
  refine (h.2 () hdom).trans (prob_mono _ fun z hz => ?_)
  exact ⟨z, ⟨hb, hz⟩, le_of_eq (dist_self z)⟩

/-! ## The composite -/

/-- Report §2.3.2, Theorem 3.3a exercised (Stage 21b2; PHASE2_SPEC §A.7, §A.9 (9)–(11)) —
**search with an unknown number of solutions**, over the parameters of the two QPLP records:
stage 1 is `countSem` at `p₁` (circuit `C₁`), stage 2 runs on every outcome `y` the Grover circuit
`C y`, where the outcomes within `ε_f = countSem.eps p₁` of `a = M/2ⁿ` get the circuit `C₀` of
`groverSem` at `p₂` (`hgood`, refinement (10)), and `g₂` bounds every branch (refinement (9)).
Then the measured composite realizes `SearchAfterCount ∘ CountSpec` with ε = `ε_f`,
δ = `ae_delta + (1 − sin²((2r₀+1)θ))` and grade `grade C₁ ⊕ g₂`, and `g₂` bounds every branch
channel. Proof: `measured_composition_pseudo` on `countSem.proof` and `searchStage_realizes`, with
the domain compatibility and non-expansiveness of `SearchAfterCount`. -/
theorem search_unknown_M (p₁ : CountSemParams) (hp₁ : countSem.pre p₁) (p₂ : GroverSemParams)
    {C₁ C₀ : Circuit} (hC₁ : countSem.circuit p₁ = .ok C₁) (hC₀ : groverSem.circuit p₂ = .ok C₀)
    (C : CountOut p₁.m (p₁.M / 2 ^ p₁.n : ℝ) → Circuit)
    (hgood : ∀ y, |countEst p₁.m (p₁.M / 2 ^ p₁.n : ℝ) y - (p₁.M / 2 ^ p₁.n : ℝ)| ≤ countSem.eps p₁ →
      C y = C₀)
    (g₂ : Grade) (hg₂ : ∀ y, Synthesis.grade (C y) ≤ g₂) :
    Realizes ((SearchAfterCount p₁.m (p₁.M / 2 ^ p₁.n : ℝ) p₂.gp.oracle.P (countSem.eps p₁)).comp
          (CountSpec p₁.m (p₁.M / 2 ^ p₁.n : ℝ)))
        (basisPOVM p₂.gp.n)
        (measuredComp (groverChannel (p₁.n + p₁.m) C₁) (countPOVM p₁.n p₁.m (p₁.M / 2 ^ p₁.n : ℝ))
          (searchStage p₂.gp.n C g₂))
        (countSem.eps p₁) (countSem.delta p₁ + groverSem.delta p₂) (Synthesis.grade C₁ + g₂) ∧
      ∀ y, (groverChannel p₂.gp.n (C y)).grade ≤ (searchStage p₂.gp.n C g₂).grade := by
  have hex : ∃ z, p₂.gp.oracle.P z = true :=
    exists_solution_of_card _ p₂.gp.hM_card p₂.gp.hM_pos
  -- the proof field of the counting record (stage 1)
  have h1 : Realizes (CountSpec p₁.m (p₁.M / 2 ^ p₁.n : ℝ))
      (countPOVM p₁.n p₁.m (p₁.M / 2 ^ p₁.n : ℝ)) (groverChannel (p₁.n + p₁.m) C₁)
      (countSem.eps p₁) (countSem.delta p₁) (Synthesis.grade C₁) :=
    (countSem.proof p₁ hp₁ C₁ hC₁).1
  have h2 := searchStage_realizes p₂ hC₀ (countSem.eps p₁) C hgood g₂
  have h : Realizes
      ((SearchAfterCount p₁.m (p₁.M / 2 ^ p₁.n : ℝ) p₂.gp.oracle.P (countSem.eps p₁)).comp
        (CountSpec p₁.m (p₁.M / 2 ^ p₁.n : ℝ)))
      (basisPOVM p₂.gp.n)
      (measuredComp (groverChannel (p₁.n + p₁.m) C₁) (countPOVM p₁.n p₁.m (p₁.M / 2 ^ p₁.n : ℝ))
        (searchStage p₂.gp.n C g₂))
      (countSem.eps p₁ + 0) (countSem.delta p₁ + groverSem.delta p₂) (Synthesis.grade C₁ + g₂) :=
    measured_composition_pseudo h1 h2 (searchAfterCount_domCompat _ hex _)
      (searchAfterCount_nonexp _ _) ae_delta_nonneg (groverSem_delta_nonneg p₂)
      (groverSem_delta_le_one p₂)
  rw [add_zero] at h
  exact ⟨h, searchStage_grade_bounds _ C g₂ hg₂⟩

/-- `search_unknown_M` with δ through the rational `groverDelta`, as the certificates' `delta_eq`
(PHASE2_SPEC §A.9 "21b1 done", J2). -/
theorem search_unknown_M_rat (p₁ : CountSemParams) (hp₁ : countSem.pre p₁) (p₂ : GroverSemParams)
    {C₁ C₀ : Circuit} (hC₁ : countSem.circuit p₁ = .ok C₁) (hC₀ : groverSem.circuit p₂ = .ok C₀)
    (C : CountOut p₁.m (p₁.M / 2 ^ p₁.n : ℝ) → Circuit)
    (hgood : ∀ y, |countEst p₁.m (p₁.M / 2 ^ p₁.n : ℝ) y - (p₁.M / 2 ^ p₁.n : ℝ)| ≤ countSem.eps p₁ →
      C y = C₀)
    (g₂ : Grade) (hg₂ : ∀ y, Synthesis.grade (C y) ≤ g₂) :
    Realizes ((SearchAfterCount p₁.m (p₁.M / 2 ^ p₁.n : ℝ) p₂.gp.oracle.P (countSem.eps p₁)).comp
          (CountSpec p₁.m (p₁.M / 2 ^ p₁.n : ℝ)))
        (basisPOVM p₂.gp.n)
        (measuredComp (groverChannel (p₁.n + p₁.m) C₁) (countPOVM p₁.n p₁.m (p₁.M / 2 ^ p₁.n : ℝ))
          (searchStage p₂.gp.n C g₂))
        (countSem.eps p₁) (countSem.delta p₁ + ((groverDelta p₂.r p₂.gp.n p₂.gp.M : ℚ) : ℝ))
        (Synthesis.grade C₁ + g₂) ∧
      ∀ y, (groverChannel p₂.gp.n (C y)).grade ≤ (searchStage p₂.gp.n C g₂).grade := by
  rw [← groverSem_delta_eq p₂]
  exact search_unknown_M p₁ hp₁ p₂ hC₁ hC₀ C hgood g₂ hg₂

/-! ## The instance `grover_pred_037`: (n, M, m) = (8, 32, 5)

The domain lemma is real analysis specific to the instance (refinement (12)): with `a = 1/8` and
`ε_f = ae_eps (1/8) 5 ≈ 0.0746`, the outcomes within `ε_f` of `a` are exactly `3, 4, 28, 29` (and
the ideal point). By the symmetry `y ↔ 32 − y` and the monotonicity of `sin²` on `[0, π/2]`, only
the two boundary inequalities need real bounds: `sin²(2π/32) < 1/8 − ε_f` (through `sin x ≤ x`)
and `sin²(5π/32) > 1/8 + ε_f` (through `sin x > x − x³/6`), with `π` bounded by `Real.pi_gt_d4`
and `Real.pi_lt_d4` (`docs/notes/PROBE_21B1.md`, Q4). -/

/-- `ae_eps (1/8) 5 < 0.0746` (the probe's value 0.074575). -/
theorem ae_eps_8_32_5_lt : ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5 < 0.0746 := by
  unfold ae_eps
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hsqrt : Real.sqrt (((32 : ℕ) / 2 ^ 8 : ℝ) * (1 - ((32 : ℕ) / 2 ^ 8 : ℝ))) < 0.330725 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (((32 : ℕ) / 2 ^ 8 : ℝ) * (1 - ((32 : ℕ) / 2 ^ 8 : ℝ))) :=
    Real.sqrt_nonneg _
  nlinarith [mul_pos hpi0 hpi0, mul_nonneg hpi0.le hsqrt0]

/-- The estimates at `y ≤ 2` lie below `1/8 − ε_f`: `sin²(πy/32) ≤ (2π/32)² < 0.0504`. -/
theorem est_le_two (t : ℕ) (ht : t ≤ 2) : Real.sin (π * t / 2 ^ 5) ^ 2 < 0.0504 := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
  have hx0 : 0 ≤ π * t / 2 ^ 5 := by positivity
  have hs0 : 0 ≤ Real.sin (π * t / 2 ^ 5) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by nlinarith)
  have hs : Real.sin (π * t / 2 ^ 5) ≤ π * t / 2 ^ 5 := Real.sin_le hx0
  have hx : π * t / 2 ^ 5 ≤ π * 2 / 2 ^ 5 := by gcongr
  have hsq : Real.sin (π * t / 2 ^ 5) ^ 2 ≤ (π * 2 / 2 ^ 5) ^ 2 :=
    pow_le_pow_left₀ hs0 (hs.trans hx) 2
  nlinarith [mul_pos hpi0 hpi0]

/-- The estimates at `5 ≤ y ≤ 16` lie above `1/8 + ε_f`: `sin²(πy/32) ≥ sin²(5π/32) > 0.1996`. -/
theorem est_ge_five (t : ℕ) (h5 : 5 ≤ t) (h16 : t ≤ 16) :
    0.1996 < Real.sin (π * t / 2 ^ 5) ^ 2 := by
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h5' : (5 : ℝ) ≤ t := by exact_mod_cast h5
  have h16' : (t : ℝ) ≤ 16 := by exact_mod_cast h16
  have hx5 : π * 5 / 2 ^ 5 ≤ π * t / 2 ^ 5 := by gcongr
  have hxh : π * t / 2 ^ 5 ≤ π / 2 := by nlinarith
  have hmono : Real.sin (π * 5 / 2 ^ 5) ≤ Real.sin (π * t / 2 ^ 5) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) hxh hx5
  have hlow : 0.4711 < Real.sin (π * 5 / 2 ^ 5) := by
    have hx : 0 < π * 5 / 2 ^ 5 := by positivity
    have hcube := Real.sin_gt_sub_cube hx
    have hxl : 0.490859 < π * 5 / 2 ^ 5 := by nlinarith
    have hxu : π * 5 / 2 ^ 5 < 0.490875 := by nlinarith
    have hx2 : (π * 5 / 2 ^ 5) ^ 2 < 0.490875 ^ 2 := by nlinarith
    have hx3 : (π * 5 / 2 ^ 5) ^ 3 < 0.490875 ^ 3 := by nlinarith
    nlinarith
  have hs0 : 0 ≤ Real.sin (π * 5 / 2 ^ 5) := by linarith
  have hsq : Real.sin (π * 5 / 2 ^ 5) ^ 2 ≤ Real.sin (π * t / 2 ^ 5) ^ 2 :=
    pow_le_pow_left₀ hs0 hmono 2
  nlinarith

/-- The symmetry `y ↔ 32 − y` of the estimate: `sin(π − x) = sin x`. -/
theorem est_symm (t : ℕ) (ht : t ≤ 32) :
    Real.sin (π * t / 2 ^ 5) ^ 2 = Real.sin (π * ((32 - t : ℕ) : ℝ) / 2 ^ 5) ^ 2 := by
  have : π * ((32 - t : ℕ) : ℝ) / 2 ^ 5 = π - π * t / 2 ^ 5 := by
    rw [Nat.cast_sub ht]
    push_cast
    ring
  rw [this, Real.sin_pi_sub]

/-- Report §2.3.2, §8.2 (Stage 21b2; PHASE2_SPEC §A.9 (12)) — **the domain lemma at
`(n, M, m) = (8, 32, 5)`**: every counting outcome whose estimate lies within `ae_eps (1/8) 5` of
`a = 32/2⁸ = 1/8` is the ideal point or one of the outcomes `3, 4, 28, 29` (the four outcomes of
`docs/notes/PROBE_21B1.md`, Q3, all with `r = 2`). Instance-specific real analysis: the two
boundary inequalities `est_le_two`, `est_ge_five`, the symmetry `est_symm`, and `ae_eps_8_32_5_lt`. -/
theorem domain_8_32_5 (y : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ))
    (hy : |countEst 5 ((32 : ℕ) / 2 ^ 8 : ℝ) y - ((32 : ℕ) / 2 ^ 8 : ℝ)| ≤
      ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5) :
    y = Sum.inr () ∨
      ∃ k : Reg 5, y = Sum.inl k ∧ (k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 28 ∨ k.toNat = 29) := by
  rcases y with k | u
  · right
    refine ⟨k, rfl, ?_⟩
    have hε := ae_eps_8_32_5_lt
    have hlt := k.toNat_lt
    have ha : ((32 : ℕ) / 2 ^ 8 : ℝ) = 1 / 8 := by norm_num
    change |Real.sin (π * k.toNat / 2 ^ 5) ^ 2 - ((32 : ℕ) / 2 ^ 8 : ℝ)| ≤ _ at hy
    rw [ha] at hy
    have key : ∀ t : ℕ, t < 32 → ¬ (t = 3 ∨ t = 4 ∨ t = 28 ∨ t = 29) →
        0.0746 < |Real.sin (π * t / 2 ^ 5) ^ 2 - 1 / 8| := by
      intro t ht hnot
      have hcases : t ≤ 2 ∨ (5 ≤ t ∧ t ≤ 16) ∨ (17 ≤ t ∧ t ≤ 27) ∨ (30 ≤ t ∧ t ≤ 31) := by
        omega
      rcases hcases with h | ⟨h5, h16⟩ | ⟨h17, h27⟩ | ⟨h30, h31⟩
      · have := est_le_two t h
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        linarith
      · have := est_ge_five t h5 h16
        rw [abs_of_pos (by linarith)]
        linarith
      · rw [est_symm t (by omega)]
        have := est_ge_five (32 - t) (by omega) (by omega)
        rw [abs_of_pos (by linarith)]
        linarith
      · rw [est_symm t (by omega)]
        have := est_le_two (32 - t) (by omega)
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        linarith
    by_contra hnot
    have := key k.toNat hlt hnot
    linarith
  · left
    cases u
    rfl

/-- Report §2.3.2, Theorem 3.3a exercised at `grover_pred_037` (Stage 21b2; PHASE2_SPEC §A.9
(9)–(12)) — **the corollary at `(n, M, m) = (8, 32, 5)`**, `r₀ = 2`, δ = `ae_delta + groverDelta
2 8 32` (= 1 − 8/π² + 7/128 ≈ 0.2441). Its hypotheses are the oracle and diffusion certificates
`O`, `D` (the network facts of the Grover QPLP), the two decidable network facts `countSem` needs,
the solution count `hcard` (a specification promise, §5.1.3), the two circuit equalities, the
table property — the outcomes `3, 4, 28, 29` and the ideal point get the Grover circuit `C₀` at
`r = 2` (`domain_8_32_5`) — and the grade bound `hg₂` over every branch.

The numbers of the instance (`scripts/probes/probe_21b1.py --table`, `docs/notes/PROBE_21B1.md`
"21b2"): `rStar 8 (M̃ y)` over the 32 outcomes is `12, 8, 3, 2, 2, 1, 1, 1, 0 × 9, 0 × 8, 1, 1, 1,
2, 2, 3, 8` for `y = 0 … 31` (the ideal point: 2); the largest `r` is 12 at `y = 0`, whose Grover
grade `(15, 794, 432, 7)` is the honest `g₂` (refinement (9)); with the stage-1 grade
`(21, 2862, 1364, 8)` of the counting certificate at `m = 5` the composite grade is
`(21, 2862, 1364, 8) ⊕ (15, 794, 432, 7) = (21, 3656, 1796, 8)`; over the domain alone it would
be `(21, 2996, 1436, 8)`, the 21b1 figure, which is not a grade of the channel. -/
theorem search_unknown_M_8_32_5 (O : OracleCert 8) (D : DiffusionCert 8) (hWF : O.N.WF)
    (h1 : O.N.outputs.length = 1) (hcard : (Finset.univ.filter fun x => O.P x = true).card = 32)
    (shape : DiffusionShape) (mode : UncomputeMode) {C₁ C₀ : Circuit}
    (hC₁ : countingCircuit O.N 8 5 none shape mode = .ok C₁) (hC₀ : groverCircuit O.N 8 2 = .ok C₀)
    (C : CountOut 5 ((32 : ℕ) / 2 ^ 8 : ℝ) → Circuit)
    (htab : ∀ k : Reg 5, (k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 28 ∨ k.toNat = 29) →
      C (Sum.inl k) = C₀)
    (hideal : C (Sum.inr ()) = C₀) (g₂ : Grade) (hg₂ : ∀ y, Synthesis.grade (C y) ≤ g₂) :
    Realizes ((SearchAfterCount 5 ((32 : ℕ) / 2 ^ 8 : ℝ) O.P (ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5)).comp
          (CountSpec 5 ((32 : ℕ) / 2 ^ 8 : ℝ)))
        (basisPOVM 8)
        (measuredComp (groverChannel (8 + 5) C₁) (countPOVM 8 5 ((32 : ℕ) / 2 ^ 8 : ℝ))
          (searchStage 8 C g₂))
        (ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5) (ae_delta + ((groverDelta 2 8 32 : ℚ) : ℝ))
        (Synthesis.grade C₁ + g₂) ∧
      ∀ y, (groverChannel 8 (C y)).grade ≤ (searchStage 8 C g₂).grade := by
  have hgood : ∀ y, |countEst 5 ((32 : ℕ) / 2 ^ 8 : ℝ) y - ((32 : ℕ) / 2 ^ 8 : ℝ)| ≤
      ae_eps ((32 : ℕ) / 2 ^ 8 : ℝ) 5 → C y = C₀ := by
    intro y hy
    rcases domain_8_32_5 y hy with h | ⟨k, rfl, hk⟩
    · rw [h]; exact hideal
    · exact htab k hk
  exact search_unknown_M_rat ⟨8, 32, 5, O.N, O.P, hcard, hWF, O.hn, h1, rfl, shape, mode⟩
    ⟨by norm_num, by norm_num⟩ ⟨⟨8, 32, by norm_num, O, hcard⟩, D, 2⟩ hC₁ hC₀ C hgood g₂ hg₂

end CQRV.Grover

end

end
