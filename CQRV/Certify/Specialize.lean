module

public import CQRV.Grover.Instance
public import CQRV.Certify.Certificate

/-!
# CQRV.Certify.Specialize

Report §5.1.3 (per-request work = proof specialization + kernel checking), §8.4.1 (specializing
π to concrete parameters), §8.2.3 (exact δ) — the lemmas a generated certificate
(`CQRV.Certify.Generate`, `certs/<name>/Cert.lean`) instantiates. Stage 8b, reviewer decision 1.

* `sin_sq_odd_mul`: `sin²((2r+1)θ) = groverSuccess r (sin²θ)` for a rational `sin²θ` (the
  Chebyshev computation of `CQRV.Certify.Certificate`, proved for every `r`): so the exact
  rational δ of the CLI is the δ of the parametric lemma, and a certificate discharges
  `groverDelta r n M = δ` by kernel evaluation.
* `grover_certificate`: `grover_parametric_lemma` with `GroverParams` built from an oracle
  certificate and the solution count `hM_card` as a **hypothesis** (§5.2.4, never decided);
  δ, grade and ancilla count are side conditions the certificate discharges by `decide +kernel`.
-/

@[expose] public section

namespace CQRV.Certify

open CQRV CQRV.Synthesis CQRV.Grover

/-! ## Exact δ (§8.2.3) -/

/-- One step of `chebyshevU.go`: `(U_k, U_{k+1}) ↦ (U_{k+1}, 2c·U_{k+1} − U_k)`. -/
theorem chebyshevU_go_succ (s : Rat) (k : Nat) :
    chebyshevU.go s (k + 1) =
      ((chebyshevU.go s k).2,
        (2 * (chebyshevU.go s k).2.2 * (1 - s) - (chebyshevU.go s k).1.1,
          2 * (chebyshevU.go s k).2.1 - (chebyshevU.go s k).1.2)) := by
  simp only [chebyshevU.go, twoCTimes]

/-- `U_{2r}` has no `c` part and `U_{2r+1}` no constant part. -/
theorem chebyshevU_go_even (s : Rat) (r : Nat) :
    (chebyshevU.go s (2 * r)).1.2 = 0 ∧ (chebyshevU.go s (2 * r)).2.1 = 0 := by
  induction r with
  | zero => simp [chebyshevU.go]
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, chebyshevU_go_succ, chebyshevU_go_succ]
    simp only [ih.1, ih.2]
    constructor <;> ring

/-- `sin((k+1)θ) = sin θ · U_k(cos θ)` and `sin((k+2)θ) = sin θ · U_{k+1}(cos θ)`, with
`U_k = a + b·c` read in `ℚ[c]/(c² − (1 − s))`, `s = sin²θ`. -/
theorem sin_mul_chebyshevU (s : Rat) (θ : ℝ) (hs : (s : ℝ) = Real.sin θ ^ 2) (k : Nat) :
    Real.sin ((k + 1) * θ) = Real.sin θ * ((chebyshevU.go s k).1.1 +
        (chebyshevU.go s k).1.2 * Real.cos θ) ∧
      Real.sin ((k + 2) * θ) = Real.sin θ * ((chebyshevU.go s k).2.1 +
        (chebyshevU.go s k).2.2 * Real.cos θ) := by
  induction k with
  | zero =>
    simp only [chebyshevU.go, Nat.cast_zero, zero_add, one_mul]
    refine ⟨by push_cast; ring, ?_⟩
    rw [show (2 : ℝ) * θ = 2 * θ from rfl, Real.sin_two_mul]
    push_cast; ring
  | succ k ih =>
    rw [chebyshevU_go_succ]
    refine ⟨by rw [show ((k + 1 : ℕ) : ℝ) + 1 = k + 2 by push_cast; ring]; exact ih.2, ?_⟩
    have hc : Real.cos θ ^ 2 = 1 - (s : ℝ) := by
      rw [hs]; linarith [Real.sin_sq_add_cos_sq θ]
    have hadd : Real.sin ((k + 3) * θ) + Real.sin ((k + 1) * θ) =
        2 * Real.sin ((k + 2) * θ) * Real.cos θ := by
      rw [show (k + 3 : ℝ) * θ = (k + 2) * θ + θ by ring,
        show (k + 1 : ℝ) * θ = (k + 2) * θ - θ by ring, Real.sin_add, Real.sin_sub]
      ring
    rw [show ((k + 1 : ℕ) : ℝ) + 2 = k + 3 by push_cast; ring,
      show Real.sin ((k + 3) * θ) = 2 * Real.sin ((k + 2) * θ) * Real.cos θ -
        Real.sin ((k + 1) * θ) by linarith, ih.1, ih.2]
    push_cast
    linear_combination 2 * Real.sin θ * ((chebyshevU.go s k).2.2 : ℝ) * hc

/-- Report §8.2, §8.2.3 — **the exact success probability**: for a rational `s = sin²θ`,
`sin²((2r+1)θ) = groverSuccess r s` (every `r`). -/
theorem sin_sq_odd_mul (s : Rat) (θ : ℝ) (hs : (s : ℝ) = Real.sin θ ^ 2) (r : Nat) :
    Real.sin ((2 * r + 1) * θ) ^ 2 = (groverSuccess r s : ℝ) := by
  have h := (sin_mul_chebyshevU s θ hs (2 * r)).1
  rw [(chebyshevU_go_even s r).1] at h
  push_cast at h
  rw [h, groverSuccess, chebyshevU]
  push_cast
  rw [hs]
  ring

/-! ## The specialization (§8.4.1) -/

/-- The hash link of a generated certificate: an `Except` value whose `.ok` payload the kernel
compared with a literal `c` is `.ok c` (one kernel evaluation of `e`). -/
theorem except_ok_of_check {ε α : Type} [DecidableEq α] (e : Except ε α) (c : α)
    (h : (match e with | .ok c' => decide (c' = c) | .error _ => false) = true) :
    e = .ok c := by
  cases e with
  | ok c' => rw [of_decide_eq_true h]
  | error _ => exact absurd h Bool.false_ne_true

/-- The `.ok` payload of an `Except` value (`default` on `.error`). Generated certificates name
the synthesized oracle and MCZ as `okPayload (synthesizeOracle …)` (Stage 9b): with one shared
function the elaborator unifies the field `C` with `except_eq_ok_okPayload`'s statement
syntactically, instead of reducing two different auxiliary matchers, which evaluates the
synthesizer in the elaborator and exceeded `maxRecDepth` on `simple_alu_x0_1`. -/
def okPayload {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok c => c
  | .error _ => default

/-- An `Except` value known to be `.ok` is `.ok` of its `okPayload` (as `except_eq_ok_payload`,
with the payload as a named function). -/
theorem except_eq_ok_okPayload {ε α : Type} [Inhabited α] (e : Except ε α) (h : e.isOk = true) :
    e = .ok (okPayload e) := by
  cases e with
  | ok c => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

/-- Report §5.1.3, §8.4.1, §8.4.4 — **the certificate lemma**: `grover_parametric_lemma` at an
oracle certificate `O` and diffusion certificate `D`, with the solution count `hM_card` as a
hypothesis (§5.2.4) and δ, grade, ancilla count as equations the generated certificate
discharges by kernel evaluation (`groverDelta`, `Synthesis.grade`, `Circuit.nAnc`). -/
theorem grover_certificate {n M r a : ℕ} {δ : ℝ} {g : Grade} (O : OracleCert n)
    (D : DiffusionCert n) {C : Circuit} (hM_pos : 1 ≤ M)
    (hC : groverCircuit O.N n r = .ok C) (hδ : ((groverDelta r n M : ℚ) : ℝ) = δ)
    (hg : Synthesis.grade C = g) (ha : C.nAnc = a)
    (hM_card : (Finset.univ.filter fun x => O.P x = true).card = M) :
    RealizesExact (SearchSpec O.P) (basisPOVM n) (groverChannel n C) δ g ∧
      AncRestore n a C (groverOp O.P ^ r * hadamardU n) := by
  let gp : GroverParams := ⟨n, M, hM_pos, O, hM_card⟩
  obtain ⟨h1, h2⟩ := grover_parametric_lemma gp D r hC
  have hs : ((solutionFraction n M : ℚ) : ℝ) = Real.sin gp.θ ^ 2 := by
    rw [gp.sin_θ_eq, Real.sq_sqrt (by positivity), solutionFraction]
    push_cast
    rfl
  rw [sin_sq_odd_mul _ _ hs r, ← Rat.cast_one, ← Rat.cast_sub, ← groverDelta, hδ, hg] at h1
  rw [ha] at h2
  exact ⟨h1, h2⟩

end CQRV.Certify

end
