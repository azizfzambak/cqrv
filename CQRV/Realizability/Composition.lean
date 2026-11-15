module

public import CQRV.Realizability.Realizes

/-!
# CQRV.Realizability.Composition

Report §2.3.2 — Theorem 3.3a (measured-interface composition), with the hypotheses that the
report lists under "Hypotheses made explicit": (i) domain compatibility, (ii) non-expansiveness.

The measured interface measures the intermediate output with the first stage's decoding POVM
and re-encodes it in the computational basis (`POVM.measureDiscard`, matching `encode`).
-/

@[expose] public section

noncomputable section

namespace CQRV

/-! ## Event probabilities (helpers for the union bound) -/

/-- Report §2.1.2 — event probabilities are non-negative. -/
theorem prob_nonneg {Y : Type} [Fintype Y] (p : ProbDistribution Y) (E : Y → Prop) :
    0 ≤ prob p E := by
  unfold prob
  exact Finset.sum_nonneg fun y _ => by split_ifs <;> simp [Prob.zero_le_coe]

/-- Report §2.1.2 — event probability is monotone in the event. -/
theorem prob_mono {Y : Type} [Fintype Y] (p : ProbDistribution Y) {E F : Y → Prop}
    (h : ∀ y, E y → F y) : prob p E ≤ prob p F := by
  unfold prob
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hE : E y
  · simp [hE, h y hE]
  · by_cases hF : F y <;> simp [hE, hF, Prob.zero_le_coe]

/-- Report §2.3.2 — the probability of an event under a mixture `q = ∑ y, p y · qs y` is the
`p`-average of its probabilities under the components. -/
theorem prob_mixture {Y Z : Type} [Fintype Y] [Fintype Z] {p : ProbDistribution Y}
    {qs : Y → ProbDistribution Z} {q : ProbDistribution Z}
    (h : ∀ z, (q z : ℝ) = ∑ y, (p y : ℝ) * (qs y z : ℝ)) (E : Z → Prop) :
    prob q E = ∑ y, (p y : ℝ) * prob (qs y) E := by
  unfold prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [h z]
  split_ifs <;> simp

/-! ## Linearity of a channel on a classical mixture -/

/-- Report §2.1.2 — `POVM.measure` as a trace: `Pr[z] = Re tr(M_z ρ)`. -/
theorem measure_eq_re_trace {Z dZ : Type} [Fintype Z] [DecidableEq Z] [Fintype dZ]
    [DecidableEq dZ] (dec : POVM Z dZ) (ρ : MState dZ) (z : Z) :
    (dec.measure ρ z : ℝ) = RCLike.re ((dec.mats z).mat * ρ.m).trace := by
  show inner ℝ (dec.mats z) ρ.M = _
  rw [HermitianMat.inner_eq_re_trace]
  rfl

/-- Report §2.1.2, §2.3.2 — a classical state is the `p`-mixture of encoded basis states:
`ofClassical p = ∑ y, p y · |y⟩⟨y|` (as matrices). -/
theorem ofClassical_m_eq_sum {Y : Type} [Fintype Y] [DecidableEq Y] (p : ProbDistribution Y) :
    (MState.ofClassical p).m = ∑ y, ((p y : ℝ) : ℂ) • (encode y).m := by
  ext i j
  rw [MState.m, MState.coe_ofClassical, HermitianMat.diagonal_mat, Matrix.sum_apply]
  simp only [encode, MState.m, MState.coe_ofClassical, HermitianMat.diagonal_mat,
    Matrix.smul_apply, Matrix.diagonal_apply, ProbDistribution.constant_eq]
  by_cases h : i = j <;> simp [h, apply_ite]

/-- Report §2.3.2 — measuring `Ψ` applied to a classical mixture gives the mixture of the
outcome distributions on the encoded basis states (linearity of `Ψ` and of the Born rule). -/
theorem measure_chan_ofClassical {Y Z dZ : Type} [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] [Fintype dZ] [DecidableEq dZ] (dec : POVM Z dZ) (Ψ : CPTPMap Y dZ)
    (p : ProbDistribution Y) (z : Z) :
    (dec.measure (Ψ (MState.ofClassical p)) z : ℝ) =
      ∑ y, (p y : ℝ) * (dec.measure (Ψ (encode y)) z : ℝ) := by
  simp only [measure_eq_re_trace, CPTPMap.mat_coe_eq_apply_mat, ofClassical_m_eq_sum, map_sum,
    map_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, map_sum]
  simp

/-- Report §2.3.2 — the union-bound step of Theorem 3.3a, shared by the exact and the general
case: if the first stage hits the event `E_f` with probability `≥ 1 − δ_f`, and from every
`y ∈ E_f` the second stage hits `E` with probability `≥ 1 − δ_g`, then the mixture hits `E` with
probability `≥ 1 − (δ_f + δ_g)`, via `(1 − δ_g)(1 − δ_f) ≥ 1 − δ_f − δ_g`. -/
theorem mixture_union_bound {Y Z : Type} [Fintype Y] [Fintype Z] {p : ProbDistribution Y}
    {qs : Y → ProbDistribution Z} {E_f : Y → Prop} {E : Z → Prop} {δ_f δ_g : ℝ}
    (hf : 1 - δ_f ≤ prob p E_f) (hg : ∀ y, E_f y → 1 - δ_g ≤ prob (qs y) E)
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    1 - (δ_f + δ_g) ≤ ∑ y, (p y : ℝ) * prob (qs y) E := by
  classical
  have key : ∀ y, (p y : ℝ) * (if E_f y then 1 - δ_g else 0) ≤ (p y : ℝ) * prob (qs y) E := by
    intro y
    refine mul_le_mul_of_nonneg_left ?_ Prob.zero_le_coe
    split_ifs with h
    · exact hg y h
    · exact prob_nonneg _ _
  have hsum : ∑ y, (p y : ℝ) * (if E_f y then 1 - δ_g else 0) = (1 - δ_g) * prob p E_f := by
    unfold prob
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  have hlow := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => key y
  rw [hsum] at hlow
  have h2 : (1 - δ_g) * (1 - δ_f) ≤ (1 - δ_g) * prob p E_f :=
    mul_le_mul_of_nonneg_left hf (by linarith)
  nlinarith [mul_nonneg hδf hδg]

/-! ## The measured interface and Theorem 3.3a -/

variable {X Y Z dY dZ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z] [Fintype dY] [DecidableEq dY] [Fintype dZ] [DecidableEq dZ]

/-- Report §2.3.2, Theorem 3.3a — the measured interface `Ψ ∘ (measure-and-re-encode) ∘ Φ`:
the first stage's output is measured with `dec_f` and re-encoded in the computational basis
(`POVM.measureDiscard`). Its grade is `Φ.grade ⊕ Ψ.grade`: the measurement and the
re-encoding are counted at grade 0, as in the report's `r ⊕ s` (docs/DECISIONS.md,
2026-10-23). -/
def measuredComp (Φ : GradedChannel X dY) (dec_f : POVM Y dY) (Ψ : GradedChannel Y dZ) :
    GradedChannel X dZ :=
  ⟨Ψ.chan ∘ₘ dec_f.measureDiscard ∘ₘ Φ.chan, Φ.grade + Ψ.grade⟩

/-- Report §2.3.2, Theorem 3.3a with exact stages (`ε_f = ε_g = 0`, the Grover slice and the
pipeline of §2.3.3). Hypotheses: (i) domain compatibility in its `ε_f = 0` form
`S_f(dom S_f) ⊆ dom S_g`; and `0 ≤ δ_f`, `0 ≤ δ_g`, `δ_g ≤ 1`, which the report leaves
implicit and the union bound `(1 − δ_f)(1 − δ_g) ≥ 1 − δ_f − δ_g` needs
(docs/DECISIONS.md, 2026-10-23). Stated over `RealizesExact`, so no metric on `Y` or `Z` is
needed; on metric spaces it is the `ε = 0` case of `Realizes` (`realizes_zero_iff`). -/
theorem measured_composition_exact
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {δ_f δ_g : ℝ} {r s : Grade}
    (hf : RealizesExact S_f dec_f Φ δ_f r) (hg : RealizesExact S_g dec_g Ψ δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f x y → y ∈ S_g.dom)
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    RealizesExact (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (δ_f + δ_g) (r + s) := by
  classical
  refine ⟨Grade.seqComp_mono hf.1 hg.1, ?_⟩
  rintro x ⟨z, y, hxy, -⟩
  have hx : x ∈ S_f.dom := ⟨y, hxy⟩
  have hchan : (measuredComp Φ dec_f Ψ).chan (encode x) =
      Ψ.chan (MState.ofClassical (dec_f.measure (Φ.chan (encode x)))) := by
    simp [measuredComp, POVM.measureDiscard_apply]
  rw [hchan, prob_mixture (measure_chan_ofClassical dec_g Ψ.chan _)]
  -- Each intermediate value acceptable for `f` lies in `dom S_g`, where `g` succeeds w.p. ≥ 1 − δ_g.
  exact mixture_union_bound (hf.2 x hx)
    (fun y' h => (hg.2 y' (hdom x hx y' h)).trans (prob_mono _ fun z hz => ⟨y', h, hz⟩))
    hδf hδg hδg1

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- Report §2.3.2, Theorem 3.3a, Hypotheses made explicit (i) domain compatibility and
(ii) non-expansiveness — the event inclusion of the general case: an `ε_f`-acceptable
intermediate `y` followed by an `ε_g`-acceptable output `z` of `y` is `(ε_f + ε_g)`-acceptable for
the composite. Non-expansiveness is used only at the exact intermediate `y₀` (`S_f x y₀`), which
lies in `dom S_g` by (i) (docs/DECISIONS.md, 2026-10-23). -/
theorem relax_comp [PseudoMetricSpace Y] [PseudoMetricSpace Z] {S_f : Spec X Y} {S_g : Spec Y Z}
    {ε_f ε_g : ℝ} (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    {x : X} (hx : x ∈ S_f.dom) {y : Y} {z : Z} (hy : S_f.relax ε_f x y)
    (hz : S_g.relax ε_g y z) : (S_g.comp S_f).relax (ε_f + ε_g) x z := by
  obtain ⟨y₀, hxy₀, hyy₀⟩ := hy
  have hε : 0 ≤ ε_f := dist_nonneg.trans hyy₀
  have hy₀ : y₀ ∈ S_g.dom := hdom x hx y₀ ⟨y₀, hxy₀, by rw [dist_self]; exact hε⟩
  obtain ⟨z', hyz', hzz'⟩ := hz
  obtain ⟨z₀, hy₀z₀, hz₀z'⟩ := hnonexp y₀ hy₀ y z' hyz'
  refine ⟨z₀, ⟨y₀, hxy₀, hy₀z₀⟩, ?_⟩
  calc dist z z₀ ≤ dist z z' + dist z' z₀ := dist_triangle z z' z₀
    _ ≤ ε_g + ε_f := by
        rw [dist_comm z' z₀]
        exact add_le_add hzz' (hz₀z'.trans ((dist_comm y₀ y).trans_le hyy₀))
    _ = ε_f + ε_g := add_comm _ _

/-- Report §2.3.2, Theorem 3.3a (general ε). Hypotheses: (i) domain compatibility
`S_f^{ε_f}(dom S_f) ⊆ dom S_g`; (ii) non-expansiveness of `S_g` (`L_g ≤ 1`), stated
relationally on the domain of `S_g`: for `y ∈ dom S_g`, every output `z'` acceptable for `y'`
has an output acceptable for `y` within `dist y y'` (for a function on its domain this is
exactly 1-Lipschitz; quantifying over all `y` would force `dom S_g = Y`,
docs/DECISIONS.md, 2026-10-23); and the δ-ranges of `measured_composition_exact`.
The event inclusion is `relax_comp`; the union bound is `mixture_union_bound`. -/
theorem measured_composition [MetricSpace Y] [MetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {ε_f ε_g δ_f δ_g : ℝ} {r s : Grade}
    (hf : Realizes S_f dec_f Φ ε_f δ_f r) (hg : Realizes S_g dec_g Ψ ε_g δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    Realizes (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (ε_f + ε_g) (δ_f + δ_g) (r + s) := by
  classical
  refine ⟨Grade.seqComp_mono hf.1 hg.1, ?_⟩
  rintro x ⟨z, y, hxy, -⟩
  have hx : x ∈ S_f.dom := ⟨y, hxy⟩
  have hchan : (measuredComp Φ dec_f Ψ).chan (encode x) =
      Ψ.chan (MState.ofClassical (dec_f.measure (Φ.chan (encode x)))) := by
    simp [measuredComp, POVM.measureDiscard_apply]
  rw [hchan, prob_mixture (measure_chan_ofClassical dec_g Ψ.chan _)]
  exact mixture_union_bound (hf.2 x hx)
    (fun y' h => (hg.2 y' (hdom x hx y' h)).trans
      (prob_mono _ fun _ hz => relax_comp hdom hnonexp hx h hz))
    hδf hδg hδg1

/-- Report §2.3.2, Theorem 3.3a on **pseudo-metric** output spaces (Stage 21b2; PHASE2_SPEC §A.9
"21b1 done", Q1) — the statement of `measured_composition` with `[PseudoMetricSpace Y]
[PseudoMetricSpace Z]` in place of `[MetricSpace _]`, and its proof verbatim: no lemma it uses
needs a metric (`relax_comp` is stated on pseudo-metrics; `mixture_union_bound`, `prob_mixture`,
`measure_chan_ofClassical`, `prob_mono` need none). This is the form the counting output
`CountOut m a` needs, whose distance `|countEst y − countEst y'|` is a pseudo-metric (`y` and its
reflection `2^m − y` have the same estimate). `measured_composition` keeps its statement. -/
theorem measured_composition_pseudo [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {ε_f ε_g δ_f δ_g : ℝ} {r s : Grade}
    (hf : Realizes S_f dec_f Φ ε_f δ_f r) (hg : Realizes S_g dec_g Ψ ε_g δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    Realizes (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (ε_f + ε_g) (δ_f + δ_g) (r + s) := by
  classical
  refine ⟨Grade.seqComp_mono hf.1 hg.1, ?_⟩
  rintro x ⟨z, y, hxy, -⟩
  have hx : x ∈ S_f.dom := ⟨y, hxy⟩
  have hchan : (measuredComp Φ dec_f Ψ).chan (encode x) =
      Ψ.chan (MState.ofClassical (dec_f.measure (Φ.chan (encode x)))) := by
    simp [measuredComp, POVM.measureDiscard_apply]
  rw [hchan, prob_mixture (measure_chan_ofClassical dec_g Ψ.chan _)]
  exact mixture_union_bound (hf.2 x hx)
    (fun y' h => (hg.2 y' (hdom x hx y' h)).trans
      (prob_mono _ fun _ hz => relax_comp hdom hnonexp hx h hz))
    hδf hδg hδg1

/-- Report §2.3.2 — consistency of the two statements of Theorem 3.3a: on metric output
spaces, `measured_composition_exact` follows from `measured_composition` at `ε_f = ε_g = 0`
(`realizes_zero_iff`, `Spec.relax_zero`). The general statement carries the non-expansiveness
hypothesis (ii) even at `ε = 0`, so it appears here although the exact case does not need it
(docs/DECISIONS.md, 2026-10-25). -/
theorem measured_composition_exact' [MetricSpace Y] [MetricSpace Z]
    {S_f : Spec X Y} {S_g : Spec Y Z} {dec_f : POVM Y dY} {dec_g : POVM Z dZ}
    {Φ : GradedChannel X dY} {Ψ : GradedChannel Y dZ} {δ_f δ_g : ℝ} {r s : Grade}
    (hf : RealizesExact S_f dec_f Φ δ_f r) (hg : RealizesExact S_g dec_g Ψ δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hδf : 0 ≤ δ_f) (hδg : 0 ≤ δ_g) (hδg1 : δ_g ≤ 1) :
    RealizesExact (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (δ_f + δ_g) (r + s) := by
  have h := measured_composition (realizes_zero_iff.mpr hf) (realizes_zero_iff.mpr hg)
    (by rw [Spec.relax_zero]; exact hdom) hnonexp hδf hδg hδg1
  rw [add_zero] at h
  exact realizes_zero_iff.mp h

end CQRV

end

end
