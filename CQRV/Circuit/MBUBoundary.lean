module

public import CQRV.Circuit.MBUClifford

/-!
# CQRV.Circuit.MBUBoundary

Stage 22c (PHASE2_SPEC §B.1 "22b done" and its refinement; report §6.2.2, §9.1.1; Track B) — **the
IR boundary of MBU**: in this IR, `mbu_general` applies exactly to the quadratic functions.

* **M1.** Paulis and Clifford unitaries on the IR's register `Reg n × Reg a`, in the symplectic
  representation: a Pauli is `pauliMono S T λ = λ • (X^S Z^T)`, with `S T : Reg n × Reg a` the sets
  of flipped and of sign-weighted qubits (bit vectors of the register itself), `xorV` the group law,
  `ip` the 𝔽₂ inner product and `sgnZ` the sign. `pauliMono_mul` is the exact product rule;
  `IsPauli` is closed under products and adjoints; the single-qubit `X` and `Z` gates are Paulis.
  `IsClifford U` says that `U` conjugates every Pauli to a Pauli — the standard notion, chosen so
  that `IsClifford.conj_pauli` is the definition and `IsClifford.mul` is immediate; the generator
  form of the task text (`U X_q Uᴴ`, `U Z_q Uᴴ` Paulis) is the corollary `IsClifford.conj_X` /
  `conj_Z`.
* **M2.** Every IR Clifford gate is Clifford (`gateU_isClifford`, no range hypothesis: a gate on a
  qubit outside the register is the identity): `X`, `Z` by the Pauli algebra; the phase gates `S`,
  `S†`, `Z`, `p a k` with `2^k ∣ 4a` through `conj_phaseMat` (`θ⁴ = 1`); `CZ` and `cp a k` with
  `2^k ∣ 2a` through `conj_czMat`; `CNOT` through the linearity of `cnotPerm`; `H` through
  `H = (1/√2)(Z + X)` and the Pauli algebra (`H X H = Z` and `H Z H = X` in one computation).
  `unitaryDenote_isClifford`: a list of such gates has a Clifford unitary.
* **M3.** The restriction `isCliffordDiag_of_tensor` (a Clifford `λ • (phaseDiag f ⊗ 1)` makes
  `phaseDiag f` `IsCliffordDiag`), **`mbu_wf_forces_quadratic`** (a well-formed circuit containing
  `mbuUncompute t j O` with `PhaseImpl n a O f` has `f` quadratic, because `Circuit.bitsOkFrom`
  demands `isClifford` under `ifBit`), and **`mbu_exactly_quadratic`** (a well-formed MBU circuit
  with a phase implementation of `f` exists iff `f` is quadratic). The classical bit `j` is
  quantified existentially in the latter: a well-formed MBU circuit has exactly one classical bit,
  so `j = 0` is forced, and the task's form with a fixed `j` fails at `j ≥ 1`.
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix
open scoped Kronecker

/-! ## M1 — the register as an 𝔽₂-vector space -/

section Register

variable {n a : ℕ}

/-- Pointwise XOR of two basis states. -/
def xorV (s t : Reg n × Reg a) : Reg n × Reg a :=
  (fun k => xor (s.1 k) (t.1 k), fun k => xor (s.2 k) (t.2 k))

/-- The all-zero basis state. -/
def zeroV : Reg n × Reg a := (fun _ => false, fun _ => false)

theorem xorV_comm (s t : Reg n × Reg a) : xorV s t = xorV t s := by
  simp only [xorV, Prod.mk.injEq]
  exact ⟨funext fun k => Bool.xor_comm _ _, funext fun k => Bool.xor_comm _ _⟩

theorem xorV_assoc (s t u : Reg n × Reg a) : xorV (xorV s t) u = xorV s (xorV t u) := by
  simp only [xorV, Prod.mk.injEq]
  exact ⟨funext fun k => Bool.xor_assoc _ _ _, funext fun k => Bool.xor_assoc _ _ _⟩

theorem xorV_self (s : Reg n × Reg a) : xorV s s = zeroV := by
  simp [xorV, zeroV]

theorem xorV_zero (s : Reg n × Reg a) : xorV s zeroV = s := by
  simp [xorV, zeroV]

theorem zero_xorV (s : Reg n × Reg a) : xorV zeroV s = s := by
  rw [xorV_comm, xorV_zero]

theorem xorV_xorV_cancel (s t : Reg n × Reg a) : xorV (xorV s t) t = s := by
  rw [xorV_assoc, xorV_self, xorV_zero]

theorem xorV_involutive (S : Reg n × Reg a) : Function.Involutive fun s => xorV s S :=
  fun s => xorV_xorV_cancel s S

/-- The 𝔽₂ inner product `∑ T_k s_k` over the data and the ancilla bits. -/
def ip (T s : Reg n × Reg a) : ZMod 2 :=
  ∑ k, toZ2 (T.1 k) * toZ2 (s.1 k) + ∑ k, toZ2 (T.2 k) * toZ2 (s.2 k)

theorem ip_xorV_right (T s t : Reg n × Reg a) : ip T (xorV s t) = ip T s + ip T t := by
  simp only [ip, xorV, toZ2_xor, mul_add, Finset.sum_add_distrib]
  ring

theorem ip_xorV_left (T T' s : Reg n × Reg a) : ip (xorV T T') s = ip T s + ip T' s := by
  simp only [ip, xorV, toZ2_xor, add_mul, Finset.sum_add_distrib]
  ring

theorem ip_zero_right (T : Reg n × Reg a) : ip T zeroV = 0 := by
  simp [ip, zeroV, toZ2]

theorem ip_zero_left (s : Reg n × Reg a) : ip zeroV s = 0 := by
  simp [ip, zeroV, toZ2]

theorem ip_comm (T s : Reg n × Reg a) : ip T s = ip s T := by
  simp only [ip, mul_comm]

/-- The sign `(−1)^z` of an 𝔽₂ value. -/
def sgnZ (z : ZMod 2) : ℂ := if z = 1 then -1 else 1

theorem sgnZ_zero : sgnZ 0 = 1 := by simp [sgnZ, show (0 : ZMod 2) ≠ 1 by decide]
theorem sgnZ_one : sgnZ 1 = -1 := by simp [sgnZ]

theorem sgnZ_add (u v : ZMod 2) : sgnZ (u + v) = sgnZ u * sgnZ v := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
    simp [sgnZ_zero, sgnZ_one, show (1 + 1 : ZMod 2) = 0 by decide]

theorem star_sgnZ (z : ZMod 2) : star (sgnZ z) = sgnZ z := by
  rcases zmod2_cases z with rfl | rfl <;> simp [sgnZ_zero, sgnZ_one]

theorem norm_sgnZ (z : ZMod 2) : ‖sgnZ z‖ = 1 := by
  rcases zmod2_cases z with rfl | rfl <;> simp [sgnZ_zero, sgnZ_one]

theorem sgnZ_mul_self (z : ZMod 2) : sgnZ z * sgnZ z = 1 := by
  rcases zmod2_cases z with rfl | rfl <;> simp [sgnZ_zero, sgnZ_one]

theorem sgnZ_toZ2 (b : Bool) : sgnZ (toZ2 b) = if b then (-1 : ℂ) else 1 := by
  cases b <;> simp [toZ2, sgnZ_zero, sgnZ_one]

/-- The basis state with the qubit `q` set and every other qubit `0` (`zeroV` for a qubit outside
the register). -/
def unitV (q : Qubit) : Reg n × Reg a := q.set true zeroV

theorem get_zeroV (q : Qubit) : q.get (zeroV : Reg n × Reg a) = false := by
  cases q <;> simp [Qubit.get, zeroV]

theorem get_xorV (q : Qubit) (s t : Reg n × Reg a) : q.get (xorV s t) = xor (q.get s) (q.get t) := by
  cases q <;> simp only [Qubit.get, xorV] <;> split_ifs <;> simp

/-- `X_q` is the translation by `unitV q`. -/
theorem flip_eq_xorV (q : Qubit) (s : Reg n × Reg a) : q.flip s = xorV s (unitV q) := by
  cases hq : q.inRange n a
  · rw [Qubit.flip, Qubit.set_of_not_inRange hq, unitV, Qubit.set_of_not_inRange hq, xorV_zero]
  · obtain ⟨i, hi⟩ : ∃ i, (match q with | .data i => i | .anc i => i) = i := ⟨_, rfl⟩
    cases q with
    | data i =>
      have h : i < n := by simpa [Qubit.inRange] using hq
      simp only [Qubit.flip, Qubit.get, Qubit.set, unitV, xorV, zeroV, h, ↓reduceDIte,
        Prod.mk.injEq]
      refine ⟨funext fun k => ?_, funext fun k => by simp⟩
      by_cases hk : k = ⟨i, h⟩
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    | anc i =>
      have h : i < a := by simpa [Qubit.inRange] using hq
      simp only [Qubit.flip, Qubit.get, Qubit.set, unitV, xorV, zeroV, h, ↓reduceDIte,
        Prod.mk.injEq]
      refine ⟨funext fun k => by simp, funext fun k => ?_⟩
      by_cases hk : k = ⟨i, h⟩
      · subst hk; simp
      · simp [Function.update_of_ne hk]

/-- `∑_k [k = i] s_k = s_i` in 𝔽₂. -/
theorem sum_toZ2_update_true {m : ℕ} (s : Reg m) (i : Fin m) :
    ∑ k, toZ2 (Function.update (fun _ : Fin m => false) i true k) * toZ2 (s k) = toZ2 (s i) := by
  rw [Finset.sum_eq_single i]
  · simp [toZ2]
  · intro k _ hk
    simp [Function.update_of_ne hk, toZ2]
  · simp

theorem sum_toZ2_false {m : ℕ} (s : Reg m) : ∑ k, toZ2 false * toZ2 (s k) = 0 := by
  simp [toZ2]

/-- `⟨unitV q, s⟩ = s_q`. -/
theorem ip_unitV (q : Qubit) (s : Reg n × Reg a) : ip (unitV q) s = toZ2 (q.get s) := by
  cases hq : q.inRange n a
  · rw [unitV, Qubit.set_of_not_inRange hq, ip_zero_left]
    cases q <;> simp_all [Qubit.get, Qubit.inRange, toZ2]
  · cases q with
    | data i =>
      have h : i < n := by simpa [Qubit.inRange] using hq
      simp only [unitV, Qubit.set, Qubit.get, zeroV, h, ↓reduceDIte, ip]
      rw [sum_toZ2_update_true, sum_toZ2_false, add_zero]
    | anc i =>
      have h : i < a := by simpa [Qubit.inRange] using hq
      simp only [unitV, Qubit.set, Qubit.get, zeroV, h, ↓reduceDIte, ip]
      rw [sum_toZ2_update_true, sum_toZ2_false, zero_add]

theorem get_unitV_self {q : Qubit} (hq : q.inRange n a = true) : q.get (unitV q : Reg n × Reg a) = true :=
  Qubit.get_set_self q hq _ _

end Register

/-! ## M1 — Paulis and Clifford unitaries -/

section Pauli

variable {n a : ℕ}

/-- A monomial matrix with a constant factor in its phase. -/
theorem monoMat_const_mul {ι : Type} [DecidableEq ι] (σ : ι → ι) (c : ℂ) (φ : ι → ℂ) :
    monoMat σ (fun j => c * φ j) = c • monoMat σ φ := by
  ext i j
  simp only [monoMat_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- PHASE2_SPEC §B.1 (22c) — **the Pauli `λ · X^S Z^T`** on the register: flip the qubits of `S`,
weight the basis state `s` by `(−1)^{⟨T, s⟩}`. -/
def pauliMono (S T : Reg n × Reg a) (lam : ℂ) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  lam • monoMat (fun s => xorV s S) (fun s => sgnZ (ip T s))

/-- A Pauli up to a unit phase. -/
def IsPauli (P : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) : Prop :=
  ∃ (S T : Reg n × Reg a) (lam : ℂ), ‖lam‖ = 1 ∧ P = pauliMono S T lam

theorem smul_pauliMono (c : ℂ) (S T : Reg n × Reg a) (lam : ℂ) :
    c • pauliMono S T lam = pauliMono S T (c * lam) := by
  rw [pauliMono, pauliMono, smul_smul]

theorem pauliMono_add_same (S T : Reg n × Reg a) (lam lam' : ℂ) :
    pauliMono S T lam + pauliMono S T lam' = pauliMono S T (lam + lam') := by
  rw [pauliMono, pauliMono, pauliMono, add_smul]

theorem pauliMono_zero (S T : Reg n × Reg a) : pauliMono S T 0 = 0 := by
  rw [pauliMono, zero_smul]

/-- **The product rule**: `(λ X^S Z^T)(λ' X^{S'} Z^{T'}) = λ λ' (−1)^{⟨T, S'⟩} X^{S ⊕ S'} Z^{T ⊕ T'}`. -/
theorem pauliMono_mul (S T : Reg n × Reg a) (lam : ℂ) (S' T' : Reg n × Reg a) (lam' : ℂ) :
    pauliMono S T lam * pauliMono S' T' lam' =
      pauliMono (xorV S S') (xorV T T') (lam * lam' * sgnZ (ip T S')) := by
  unfold pauliMono
  rw [smul_mul_smul_comm, monoMat_mul]
  have hσ : ((fun s => xorV s S) ∘ fun s => xorV s S') = fun s => xorV s (xorV S S') := by
    funext s
    simp only [Function.comp]
    rw [xorV_assoc, xorV_comm S' S]
  have hφ : (fun j => sgnZ (ip T (xorV j S')) * sgnZ (ip T' j)) =
      fun j => sgnZ (ip T S') * sgnZ (ip (xorV T T') j) := by
    funext j
    rw [ip_xorV_right, sgnZ_add, ip_xorV_left, sgnZ_add]
    ring
  simp only [hσ, hφ]
  rw [monoMat_const_mul, smul_smul]

theorem pauliMono_conjTranspose (S T : Reg n × Reg a) (lam : ℂ) :
    (pauliMono S T lam)ᴴ = pauliMono S T (star lam * sgnZ (ip T S)) := by
  rw [← Matrix.star_eq_conjTranspose, pauliMono, star_smul, star_monoMat (xorV_involutive S)]
  have hφ : (fun j => star (sgnZ (ip T (xorV j S)))) = fun j => sgnZ (ip T S) * sgnZ (ip T j) := by
    funext j
    rw [star_sgnZ, ip_xorV_right, sgnZ_add, mul_comm]
  rw [hφ, monoMat_const_mul, smul_smul, pauliMono]

theorem IsPauli.mul {P Q : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hP : IsPauli P)
    (hQ : IsPauli Q) : IsPauli (P * Q) := by
  obtain ⟨S, T, lam, hl, rfl⟩ := hP
  obtain ⟨S', T', lam', hl', rfl⟩ := hQ
  refine ⟨_, _, _, ?_, pauliMono_mul S T lam S' T' lam'⟩
  rw [norm_mul, norm_mul, hl, hl', norm_sgnZ, one_mul, one_mul]

theorem IsPauli.conjTranspose {P : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hP : IsPauli P) :
    IsPauli Pᴴ := by
  obtain ⟨S, T, lam, hl, rfl⟩ := hP
  refine ⟨S, T, _, ?_, pauliMono_conjTranspose S T lam⟩
  rw [norm_mul, norm_star, hl, norm_sgnZ, one_mul]

/-- `X_q` is the Pauli `X^{unitV q}`. -/
theorem gateU_x_eq_pauliMono (q : Qubit) :
    gateU n a (.x q) = pauliMono (unitV q) zeroV 1 := by
  rw [pauliMono, one_smul]
  show monoMat q.flip (fun _ => 1) = _
  congr 1
  · funext s; exact flip_eq_xorV q s
  · funext s; rw [ip_zero_left, sgnZ_zero]

/-- `Z_q` is the Pauli `Z^{unitV q}`. -/
theorem gateU_z_eq_pauliMono (q : Qubit) :
    gateU n a (.z q) = pauliMono zeroV (unitV q) 1 := by
  rw [pauliMono, one_smul, gateU_z, phaseMat]
  congr 1
  · funext s; rw [xorV_zero]; rfl
  · funext s; rw [ip_unitV, sgnZ_toZ2]

theorem isPauli_X (q : Qubit) : IsPauli (gateU n a (.x q)) :=
  ⟨_, _, 1, by simp, gateU_x_eq_pauliMono q⟩

theorem isPauli_Z (q : Qubit) : IsPauli (gateU n a (.z q)) :=
  ⟨_, _, 1, by simp, gateU_z_eq_pauliMono q⟩

/-- PHASE2_SPEC §B.1 (22c) — **a Clifford unitary** conjugates every Pauli to a Pauli. (The task's
generator form, `U X_q Uᴴ` and `U Z_q Uᴴ` Paulis, is `IsClifford.conj_X` / `conj_Z`; this
definition makes `conj_pauli` immediate and `IsClifford.mul` a one-line proof.) -/
def IsClifford (U : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) : Prop :=
  ∀ P, IsPauli P → IsPauli (U * P * Uᴴ)

theorem IsClifford.conj_pauli {U : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hU : IsClifford U)
    {P} (hP : IsPauli P) : IsPauli (U * P * Uᴴ) := hU P hP

theorem IsClifford.conj_X {U : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hU : IsClifford U)
    (q : Qubit) : IsPauli (U * gateU n a (.x q) * Uᴴ) := hU _ (isPauli_X q)

theorem IsClifford.conj_Z {U : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hU : IsClifford U)
    (q : Qubit) : IsPauli (U * gateU n a (.z q) * Uᴴ) := hU _ (isPauli_Z q)

theorem isClifford_one : IsClifford (1 : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) := by
  intro P hP
  simpa using hP

theorem IsClifford.mul {U V : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hU : IsClifford U)
    (hV : IsClifford V) : IsClifford (U * V) := by
  intro P hP
  have := hU _ (hV P hP)
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this

end Pauli

/-! ## M2 — the IR Clifford gates are Clifford -/

section Gates

variable {n a : ℕ}

/-- **Conjugating a Pauli by a monomial matrix** `M = monoMat σ φ` with `σ` involutive:
`M |j⟩ = φ j |σ j⟩`, so `M (λ X^S Z^T) Mᴴ |j⟩ = λ · φ(σ j ⊕ S) · (−1)^{⟨T, σ j⟩} · conj(φ(σ j))
|σ(σ j ⊕ S)⟩`. The result is a Pauli when the permutation `j ↦ σ (σ j ⊕ S)` is a translation
(`hperm`) and the phase is a constant times a sign character (`hphase`). -/
theorem isPauli_conj_monoMat {σ : Reg n × Reg a → Reg n × Reg a} (hσ : Function.Involutive σ)
    (φ : Reg n × Reg a → ℂ) (S T : Reg n × Reg a) {lam lam' : ℂ} (hl : ‖lam‖ = 1)
    (hl' : ‖lam'‖ = 1) (S' T' : Reg n × Reg a)
    (hperm : ∀ s, σ (xorV (σ s) S) = xorV s S')
    (hphase : ∀ j, φ (xorV (σ j) S) * sgnZ (ip T (σ j)) * star (φ (σ j)) = lam' * sgnZ (ip T' j)) :
    IsPauli (monoMat σ φ * pauliMono S T lam * (monoMat σ φ)ᴴ) := by
  refine ⟨S', T', lam * lam', by rw [norm_mul, hl, hl', one_mul], ?_⟩
  rw [← Matrix.star_eq_conjTranspose, star_monoMat hσ, pauliMono, Matrix.mul_smul, Matrix.smul_mul,
    monoMat_mul, monoMat_mul, pauliMono]
  ext i j
  simp only [monoMat_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul, hperm j, hphase j]
  split_ifs <;> ring

/-- A unit complex number with `θ⁴ = 1` has `star θ = θ³`. -/
theorem star_eq_pow_three_of_pow_four {θ : ℂ} (hθ : θ ^ 4 = 1) : star θ = θ ^ 3 := by
  have hnorm : ‖θ‖ = 1 := by
    have h : ‖θ‖ ^ 4 = 1 := by rw [← norm_pow, hθ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg θ) (by norm_num)).1 h
  have h1 : star θ * θ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]
    simp
  calc star θ = star θ * (θ * θ ^ 3) := by rw [← pow_succ', hθ, mul_one]
    _ = θ ^ 3 := by rw [← mul_assoc, h1, one_mul]

/-- **The phase gates are Clifford**: `diag(1, θ)` on `q` with `θ⁴ = 1` (`S`, `S†`, `Z`, and `p a k`
with `2^k ∣ 4a`). `X^S Z^T` is sent to itself when `q ∉ S`; when `q ∈ S` it picks up the phase `θ`
and, if `θ² = −1`, the factor `Z_q`. -/
theorem conj_phaseMat {θ : ℂ} (hθ : θ ^ 4 = 1) (q : Qubit) : IsClifford (phaseMat n a q θ) := by
  have hstar := star_eq_pow_three_of_pow_four hθ
  have hnorm : ‖θ‖ = 1 := by
    have h : ‖θ‖ ^ 4 = 1 := by rw [← norm_pow, hθ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg θ) (by norm_num)).1 h
  have hsq : θ ^ 2 = 1 ∨ θ ^ 2 = -1 := by
    rw [← mul_self_eq_one_iff]
    linear_combination hθ
  have h1 : star θ * θ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]
    simp
  rintro P ⟨S, T, lam, hl, rfl⟩
  rw [phaseMat]
  cases hS : q.get S
  · -- `q ∉ S`: the phases cancel
    refine isPauli_conj_monoMat (fun _ => rfl) _ S T hl (lam' := 1) norm_one S T (fun s => rfl)
      fun j => ?_
    simp only [id_eq, get_xorV, hS, Bool.xor_false]
    rcases Bool.eq_false_or_eq_true (q.get j) with hj | hj
    · simp only [hj, ↓reduceIte, one_mul]
      linear_combination (sgnZ (ip T j)) * h1
    · simp [hj]
  · rcases hsq with h2 | h2
    · -- `q ∈ S`, `θ² = 1`: the phase `θ`
      refine isPauli_conj_monoMat (fun _ => rfl) _ S T hl hnorm S T (fun s => rfl) fun j => ?_
      simp only [id_eq, get_xorV, hS, Bool.xor_true]
      rcases Bool.eq_false_or_eq_true (q.get j) with hj | hj
      · simp only [hj, Bool.not_true, ↓reduceIte, Bool.false_eq_true, one_mul]
        rw [hstar]
        linear_combination (sgnZ (ip T j) * θ) * h2
      · simp [hj]
    · -- `q ∈ S`, `θ² = −1`: the phase `θ` and the factor `Z_q`
      refine isPauli_conj_monoMat (fun _ => rfl) _ S T hl hnorm S (xorV T (unitV q)) (fun s => rfl)
        fun j => ?_
      simp only [id_eq, get_xorV, hS, Bool.xor_true, ip_xorV_left, sgnZ_add, ip_unitV, sgnZ_toZ2]
      rcases Bool.eq_false_or_eq_true (q.get j) with hj | hj
      · simp only [hj, Bool.not_true, ↓reduceIte, Bool.false_eq_true, one_mul]
        rw [hstar]
        linear_combination (sgnZ (ip T j) * θ) * h2
      · simp [hj]

/-- **`CZ` is Clifford**: `X^S Z^T` is sent to `(−1)^{S_c S_t} X^S Z^{T ⊕ S_t e_c ⊕ S_c e_t}`. -/
theorem conj_czMat (c t : Qubit) :
    IsClifford (monoMat id fun s : Reg n × Reg a => if c.get s && t.get s then (-1 : ℂ) else 1) := by
  rintro P ⟨S, T, lam, hl, rfl⟩
  have hsgn : ∀ u v : Bool, (if u && v then (-1 : ℂ) else 1) = sgnZ (toZ2 u * toZ2 v) := by
    intro u v; cases u <;> cases v <;> simp [toZ2, sgnZ_zero, sgnZ_one]
  have hite : ∀ (b : Bool) (p : Qubit) (j : Reg n × Reg a),
      ip (if b then unitV p else zeroV) j = toZ2 b * toZ2 (p.get j) := by
    intro b p j; cases b <;> simp [ip_unitV, ip_zero_left, toZ2]
  have h2 : (2 : ZMod 2) = 0 := by decide
  refine isPauli_conj_monoMat (fun _ => rfl) _ S T hl
    (norm_sgnZ (toZ2 (c.get S) * toZ2 (t.get S))) S
    (xorV T (xorV (if t.get S then unitV c else zeroV) (if c.get S then unitV t else zeroV)))
    (fun s => rfl) fun j => ?_
  simp only [id, hsgn, star_sgnZ, get_xorV, toZ2_xor, ip_xorV_left, hite, ← sgnZ_add]
  congr 1
  linear_combination (toZ2 (c.get j) * toZ2 (t.get j)) * h2

/-- `cnotPerm` as a translation: flip `t` when `c` reads `1`. -/
theorem cnotPerm_eq_xorV (c t : Qubit) (s : Reg n × Reg a) :
    cnotPerm n a c t s = xorV s (if c.get s then unitV t else zeroV) := by
  rw [cnotPerm]
  split_ifs with h
  · exact flip_eq_xorV t s
  · rw [xorV_zero]

/-- `cnotPerm` is 𝔽₂-linear. -/
theorem cnotPerm_xorV (c t : Qubit) (u v : Reg n × Reg a) :
    cnotPerm n a c t (xorV u v) = xorV (cnotPerm n a c t u) (cnotPerm n a c t v) := by
  rw [cnotPerm_eq_xorV, cnotPerm_eq_xorV, cnotPerm_eq_xorV, get_xorV]
  have h : ∀ b b' : Bool, (if xor b b' then unitV t else zeroV : Reg n × Reg a) =
      xorV (if b then unitV t else zeroV) (if b' then unitV t else zeroV) := by
    intro b b'; cases b <;> cases b' <;> simp [xorV_zero, zero_xorV, xorV_self]
  rw [h]
  -- (u ⊕ v) ⊕ (e_u ⊕ e_v) = (u ⊕ e_u) ⊕ (v ⊕ e_v)
  rw [xorV_assoc, xorV_assoc, ← xorV_assoc v, xorV_comm v, xorV_assoc]

/-- `⟨T, CNOT_{c→t} j⟩ = ⟨CNOT_{t→c} T, j⟩`. -/
theorem ip_cnotPerm (c t : Qubit) (T j : Reg n × Reg a) :
    ip T (cnotPerm n a c t j) = ip (cnotPerm n a t c T) j := by
  rw [cnotPerm_eq_xorV, cnotPerm_eq_xorV, ip_xorV_right, ip_xorV_left]
  congr 1
  rw [ip_comm T]
  cases hc : c.get j <;> cases ht : t.get T <;>
    simp [ip_unitV, ip_zero_left, hc, ht, toZ2]

/-- **`CNOT` is Clifford**: `X^S Z^T` is sent to `X^{CNOT S} Z^{CNOTᵀ T}`. -/
theorem conj_cnot (c t : Qubit) : IsClifford (gateU n a (.cnot c t)) := by
  by_cases hct : c = t
  · simp only [gateU, hct, ↓reduceIte]
    exact isClifford_one
  rintro P ⟨S, T, lam, hl, rfl⟩
  simp only [gateU, hct, ↓reduceIte]
  have hperm : ∀ s, cnotPerm n a c t (xorV (cnotPerm n a c t s) S) = xorV s (cnotPerm n a c t S) :=
    fun s => by rw [cnotPerm_xorV, cnotPerm_involutive n a hct s]
  have hphase : ∀ j : Reg n × Reg a,
      (fun _ => (1 : ℂ)) (xorV (cnotPerm n a c t j) S) * sgnZ (ip T (cnotPerm n a c t j)) *
        star ((fun _ => (1 : ℂ)) (cnotPerm n a c t j)) = 1 * sgnZ (ip (cnotPerm n a t c T) j) :=
    fun j => by simp [ip_cnotPerm]
  exact isPauli_conj_monoMat (cnotPerm_involutive n a hct) _ S T hl norm_one _ _ hperm hphase

/-- A sum of two Paulis one of whose coefficients vanishes. -/
theorem isPauli_two_terms (S T S' T' : Reg n × Reg a) {c₁ c₂ lam : ℂ} (hl : ‖lam‖ = 1)
    (h : (c₁ = lam ∧ c₂ = 0) ∨ (c₁ = 0 ∧ c₂ = lam)) :
    IsPauli (pauliMono S T c₁ + pauliMono S' T' c₂) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, pauliMono_zero, add_zero]
    exact ⟨S, T, lam, hl, rfl⟩
  · rw [h1, h2, pauliMono_zero, zero_add]
    exact ⟨S', T', lam, hl, rfl⟩

/-- **`H` is Clifford**: `H = (1/√2)(Z_q + X_q)` and `H P H` is one of `±P`, `X_q P Z_q`, `Z_q P X_q`
by the Pauli algebra, according to whether `q ∈ S`, `q ∈ T`. -/
theorem conj_h (q : Qubit) : IsClifford (gateU n a (.h q)) := by
  cases hq : q.inRange n a
  · simp only [gateU, hq, Bool.false_eq_true, ↓reduceIte]
    exact isClifford_one
  rintro P ⟨S, T, lam, hl, rfl⟩
  have hH : gateU n a (.h q) = ((Real.sqrt 2)⁻¹ : ℂ) •
      (pauliMono zeroV (unitV q) 1 + pauliMono (unitV q) zeroV 1) := by
    rw [← gateU_z_eq_pauliMono, ← gateU_x_eq_pauliMono, gateU_z]
    simp only [gateU, hq, ↓reduceIte, hMat]
    rfl
  have hstar : (gateU n a (.h q))ᴴ = gateU n a (.h q) := by
    rw [← Matrix.star_eq_conjTranspose]
    simp only [gateU, hq, ↓reduceIte]
    exact star_hMat (Qubit.flip_involutive q)
  set e : Reg n × Reg a := unitV q with he
  have hee : ip e e = 1 := by
    rw [he, ip_unitV, get_unitV_self hq]; rfl
  -- the four Pauli products
  have hZP : pauliMono zeroV e 1 * pauliMono S T lam =
      pauliMono S (xorV e T) (lam * sgnZ (toZ2 (q.get S))) := by
    rw [pauliMono_mul, zero_xorV, he, ip_unitV, one_mul]
  have hXP : pauliMono e zeroV 1 * pauliMono S T lam = pauliMono (xorV e S) T lam := by
    rw [pauliMono_mul, zero_xorV, ip_zero_left, sgnZ_zero, one_mul, mul_one]
  have hZPZ : pauliMono S (xorV e T) (lam * sgnZ (toZ2 (q.get S))) * pauliMono zeroV e 1 =
      pauliMono S T (lam * sgnZ (toZ2 (q.get S))) := by
    rw [pauliMono_mul, xorV_zero, xorV_comm e T, xorV_xorV_cancel, ip_zero_right, sgnZ_zero,
      mul_one, mul_one]
  have hZPX : pauliMono S (xorV e T) (lam * sgnZ (toZ2 (q.get S))) * pauliMono e zeroV 1 =
      pauliMono (xorV e S) (xorV e T) (lam * sgnZ (toZ2 (q.get S)) * sgnZ (1 + toZ2 (q.get T))) := by
    rw [pauliMono_mul, xorV_zero, ip_xorV_left, hee, ip_comm T, he, ip_unitV, mul_one, xorV_comm S]
  have hXPZ : pauliMono (xorV e S) T lam * pauliMono zeroV e 1 =
      pauliMono (xorV e S) (xorV e T) lam := by
    rw [pauliMono_mul, xorV_zero, ip_zero_right, sgnZ_zero, mul_one, mul_one, xorV_comm T]
  have hXPX : pauliMono (xorV e S) T lam * pauliMono e zeroV 1 =
      pauliMono S T (lam * sgnZ (toZ2 (q.get T))) := by
    rw [pauliMono_mul, xorV_comm e S, xorV_xorV_cancel, xorV_zero, ip_comm T, he, ip_unitV, mul_one]
  rw [hstar, hH, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, invSqrtTwo_mul_self]
  simp only [Matrix.add_mul, Matrix.mul_add]
  rw [hZP, hXP, hZPZ, hZPX, hXPZ, hXPX]
  have hgroup : pauliMono S T (lam * sgnZ (toZ2 (q.get S))) + pauliMono (xorV e S) (xorV e T) lam +
      (pauliMono (xorV e S) (xorV e T) (lam * sgnZ (toZ2 (q.get S)) * sgnZ (1 + toZ2 (q.get T))) +
        pauliMono S T (lam * sgnZ (toZ2 (q.get T)))) =
      pauliMono S T (lam * sgnZ (toZ2 (q.get S)) + lam * sgnZ (toZ2 (q.get T))) +
      pauliMono (xorV e S) (xorV e T)
        (lam * sgnZ (toZ2 (q.get S)) * sgnZ (1 + toZ2 (q.get T)) + lam) := by
    rw [← pauliMono_add_same, ← pauliMono_add_same]
    abel
  rw [hgroup, smul_add, smul_pauliMono, smul_pauliMono]
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have hl' : ‖-lam‖ = 1 := by rw [norm_neg, hl]
  rcases Bool.eq_false_or_eq_true (q.get S) with hS | hS <;>
  rcases Bool.eq_false_or_eq_true (q.get T) with hT | hT <;> rw [hS, hT] <;>
    simp only [toZ2, ↓reduceIte, Bool.false_eq_true, add_zero, h11, sgnZ_zero, sgnZ_one] <;>
    first
    | exact isPauli_two_terms _ _ _ _ hl (Or.inl ⟨by ring1, by ring1⟩)
    | exact isPauli_two_terms _ _ _ _ hl (Or.inr ⟨by ring1, by ring1⟩)
    | exact isPauli_two_terms _ _ _ _ hl' (Or.inl ⟨by ring1, by ring1⟩)

/-- `phaseOf a k` has order dividing `4` when `2^k ∣ 4a` (the Clifford condition of
`Gate.isClifford` for `p`). -/
theorem phaseOf_pow_four_eq_one {a' : ℤ} {k : ℕ} (h : (2 ^ k : ℤ) ∣ 4 * a') :
    phaseOf a' k ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h
  have hk : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm' : (4 : ℂ) * a' = 2 ^ k * m := by exact_mod_cast hm
  have hm'' : (4 : ℂ) * a' / 2 ^ k = m := by rw [hm', mul_div_cancel_left₀ _ hk]
  have key : ((4 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * a' / 2 ^ k) = m * (2 * Real.pi * Complex.I) := by
    rw [← hm'']
    push_cast
    ring
  rw [phaseOf, ← Complex.exp_nat_mul, key, Complex.exp_int_mul_two_pi_mul_I]

/-- `phaseOf a k` is `±1` when `2^k ∣ 2a` (the Clifford condition of `Gate.isClifford` for `cp`). -/
theorem phaseOf_sq_eq_one {a' : ℤ} {k : ℕ} (h : (2 ^ k : ℤ) ∣ 2 * a') :
    phaseOf a' k ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := h
  have hk : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm' : (2 : ℂ) * a' = 2 ^ k * m := by exact_mod_cast hm
  have hm'' : (2 : ℂ) * a' / 2 ^ k = m := by rw [hm', mul_div_cancel_left₀ _ hk]
  have key : ((2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * a' / 2 ^ k) = m * (2 * Real.pi * Complex.I) := by
    rw [← hm'']
    push_cast
    ring
  rw [phaseOf, ← Complex.exp_nat_mul, key, Complex.exp_int_mul_two_pi_mul_I]

/-- PHASE2_SPEC §B.1 (22c) — **every IR Clifford gate is Clifford** on the register (a gate on a
qubit outside the register is the identity, so no range hypothesis is needed). -/
theorem gateU_isClifford (g : Gate) (hg : g.isClifford = true) : IsClifford (gateU n a g) := by
  cases g with
  | h q => exact conj_h q
  | s q => exact conj_phaseMat (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num) q
  | sdg q => exact conj_phaseMat (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq, Complex.I_sq]; norm_num) q
  | x q => exact fun P hP => ((isPauli_X q).mul hP).mul (isPauli_X q).conjTranspose
  | z q => exact conj_phaseMat (by norm_num) q
  | cnot c t => exact conj_cnot c t
  | cz p q => exact conj_czMat p q
  | p m k q =>
    have hd : (2 ^ k : ℤ) ∣ 4 * m := by simpa [Gate.isClifford] using hg
    rw [gateU_p]
    exact conj_phaseMat (phaseOf_pow_four_eq_one hd) q
  | cp m k c t =>
    have hd : (2 ^ k : ℤ) ∣ 2 * m := by simpa [Gate.isClifford] using hg
    have h2 := phaseOf_sq_eq_one hd
    rw [gateU_cp]
    have h1 : phaseOf m k * phaseOf m k = 1 := by rw [← sq]; exact h2
    rcases mul_self_eq_one_iff.1 h1 with h1 | h1
    · rw [h1]
      simp only [ite_self]
      rw [monoMat_id_one]
      exact isClifford_one
    · rw [h1]
      exact conj_czMat c t
  | measure q j => simp [Gate.isClifford] at hg
  | ifBit j g => simp [Gate.isClifford] at hg
  | alloc q => simp [Gate.isClifford] at hg
  | free q => simp [Gate.isClifford] at hg
  | t q => simp [Gate.isClifford] at hg
  | tdg q => simp [Gate.isClifford] at hg

/-- A list of IR Clifford gates has a Clifford unitary. -/
theorem unitaryDenote_isClifford (gs : List Gate) (h : ∀ g ∈ gs, g.isClifford = true) :
    IsClifford (unitaryDenote n a gs) := by
  induction gs with
  | nil => exact isClifford_one
  | cons g gs ih =>
    rw [unitaryDenote]
    exact (ih fun g' hg' => h g' (List.mem_cons_of_mem g hg')).mul
      (gateU_isClifford g (h g (List.mem_cons_self ..)))

end Gates

/-! ## M3 — the restriction and the boundary -/

section Boundary

variable {n a : ℕ}

/-- `X` on the data qubit `i` is `pauliX i ⊗ 1`. -/
theorem gateU_x_data_kron (i : Fin n) :
    gateU n a (.x (.data i.val)) = pauliX i ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  ext ⟨x, w⟩ ⟨y, v⟩
  simp only [gateU, monoMat_apply, pauliX, kroneckerMap_apply, one_apply, Qubit.flip, Qubit.get,
    Qubit.set, i.isLt, ↓reduceDIte, Prod.mk.injEq, flipBit, Fin.eta]
  by_cases h1 : x = Function.update y i (!y i) <;> by_cases h2 : w = v <;> simp [h1, h2]

/-- Reading a diagonal sign matrix off a Pauli: if `(pauliX i * phaseDiag g) ⊗ 1` is a Pauli, then
`phaseDiag g` is a Pauli `Z`-string up to a phase (evaluate at the entries `((flip i y, 0), (y, 0))`). -/
theorem phaseDiag_eq_smul_pauliZ_of_isPauli {g : Reg n → Bool} {i : Fin n}
    (h : IsPauli ((pauliX i * phaseDiag g) ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ))) :
    ∃ (lam : ℂ) (b : Fin n → Bool), phaseDiag g = lam • pauliZ b := by
  obtain ⟨S, T, lam, -, hP⟩ := h
  refine ⟨lam, T.1, ?_⟩
  have key : ∀ y : Reg n, (if g y then (-1 : ℂ) else 1) = lam * if linPred T.1 y then -1 else 1 := by
    intro y
    have hy := congrFun (congrFun hP (flipBit i y, (fun _ => false : Reg a))) (y, fun _ => false)
    simp only [kroneckerMap_apply, one_apply, ↓reduceIte, pauliMono, Matrix.smul_apply, smul_eq_mul,
      monoMat_apply, pauliX, phaseDiag, Matrix.mul_apply, diagonal_apply, mul_ite, mul_one,
      mul_zero, one_mul, Finset.sum_ite_eq', Finset.mem_univ] at hy
    have hlin : linPred T.1 y = decide (ip T (y, fun _ => false) = 1) := by
      simp [linPred, ip, coord, toZ2]
    rw [hlin]
    by_cases hc : (flipBit i y, (fun _ => false : Reg a)) = xorV (y, fun _ => false) S
    · simp only [hc, ↓reduceIte] at hy
      rw [hy]
      congr 1
      simp [sgnZ]
    · simp only [hc, ↓reduceIte] at hy
      exact absurd hy (by split_ifs <;> norm_num)
  ext x y
  simp only [phaseDiag, pauliZ, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    simpa using key x
  · simp [hxy]

/-- PHASE2_SPEC §B.1 (22c) — **the restriction**: if `λ • (phaseDiag f ⊗ 1)` is Clifford on the
register, then `phaseDiag f` is Clifford in the diagonal sense of 22b. Through the derivative
criterion: conjugating `X_{data i} ⊗ 1` gives `(X_i · phaseDiag (D_i f)) ⊗ 1`, a Pauli, so every
derivative is affine. -/
theorem isCliffordDiag_of_tensor (f : Reg n → Bool) {lam : ℂ} (hl : ‖lam‖ = 1)
    (hU : IsClifford (lam • (phaseDiag f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)))) :
    IsCliffordDiag (phaseDiag f) := by
  rw [clifford_iff_quadratic, isQuadratic_iff_deriv_affine]
  intro i
  rw [← phaseDiag_eq_smul_pauliZ_iff]
  apply phaseDiag_eq_smul_pauliZ_of_isPauli (a := a) (i := i)
  have h := hU _ (isPauli_X (.data i.val))
  have hll : star lam * lam = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hl]
    simp
  rw [gateU_x_data_kron, Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hll,
    one_smul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.one_mul, conj_pauliX_phaseDiag] at h
  exact h

/-- Under `ifBit j`, the classical-bit discipline admits only Clifford gates. -/
theorem isClifford_of_bitsOkFrom_map_ifBit {m j : ℕ} {W : List ℕ} {O : List Gate}
    (h : Circuit.bitsOkFrom m W (O.map (Gate.ifBit j)) = true) :
    ∀ g ∈ O, g.isClifford = true := by
  induction O generalizing W with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.bitsOkFrom, Gate.bitOk, Bool.and_eq_true] at h
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact h.1.2
    · exact ih h.2 g' hg'

/-- PHASE2_SPEC §B.1 (22c) — **the IR boundary**: a well-formed circuit whose gates are a block `B`
followed by `mbuUncompute t j O`, with `O` a phase implementation of `f`, has `f` quadratic. The
bit discipline of `Circuit.WF` admits only Clifford gates under `ifBit`, so the unitary of `O` is
Clifford, so `phaseDiag f` is Clifford in the diagonal sense, so `f` is quadratic. (With `Z t`
before the uncompute, take `B ++ [.z t]` as the block.) -/
theorem mbu_wf_forces_quadratic {C : Circuit} (hWF : C.WF) {B O : List Gate} {t : Qubit} {j : ℕ}
    (hgates : C.gates = B ++ mbuUncompute t j O) {f : Reg n → Bool} (hO : PhaseImpl n a O f) :
    IsQuadratic f := by
  have hbits := hWF.bitsOk
  rw [Circuit.bitsOk, hgates, bitsOkFrom_append_list, Bool.and_eq_true, mbuUncompute,
    bitsOkFrom_append_list, bitsOkFrom_append_list, Bool.and_eq_true, Bool.and_eq_true] at hbits
  have hcl := isClifford_of_bitsOkFrom_map_ifBit hbits.2.1.2
  obtain ⟨lam, hl, hden⟩ := hO.phase
  have hU := unitaryDenote_isClifford (n := n) (a := a) O hcl
  rw [hden] at hU
  exact (clifford_iff_quadratic f).1 (isCliffordDiag_of_tensor f hl hU)

/-- A measurement-free gate list satisfies the bit discipline. -/
theorem bitsOkFrom_of_unitary (m : ℕ) (W : List ℕ) {gs : List Gate}
    (h : ∀ g ∈ gs, g.isUnitary = true) : Circuit.bitsOkFrom m W gs = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (List.mem_cons_self ..)
    rw [Circuit.bitsOkFrom, Bool.and_eq_true]
    refine ⟨?_, ih (W ++ g.writes) fun g' hg' => h g' (List.mem_cons_of_mem g hg')⟩
    cases g <;> simp_all [Gate.bitOk, Gate.isUnitary]

/-- The gates of `phaseCircuitQuad` are Clifford. -/
theorem phaseCircuitQuad_isClifford (a' : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2) :
    ∀ g ∈ phaseCircuitQuad a' b, g.isClifford = true := by
  intro g hg
  simp only [phaseCircuitQuad, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rfl

/-- `ifBit` checks the qubits of the controlled gate. -/
theorem qubitsOk_ifBit (m : ℕ) (j : ℕ) (g : Gate) (hg : g.isClifford = true) :
    (Gate.ifBit j g).qubitsOk m = g.qubitsOk m := by
  cases g <;> first | rfl | simp [Gate.isClifford] at hg

/-- The gates of `phaseCircuitQuad` act on distinct data qubits in range. -/
theorem phaseCircuitQuad_qubitsOk (a' : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2) :
    ∀ g ∈ phaseCircuitQuad a' b, g.qubitsOk n = true := by
  intro g hg
  simp only [phaseCircuitQuad, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, -, rfl⟩ | ⟨p, hp, rfl⟩
  · simp [Gate.qubitsOk, Gate.qubits, i.isLt]
  · have hlt : p.1 < p.2 := by
      simp only [czPairs, List.mem_flatMap, List.mem_map, List.mem_filter] at hp
      obtain ⟨i, -, j, ⟨-, hj⟩, rfl⟩ := hp
      exact (of_decide_eq_true hj).1
    have hne : (p.1 : ℕ) ≠ p.2 := Fin.val_ne_of_ne (ne_of_lt hlt)
    simp [Gate.qubitsOk, Gate.qubits, p.1.isLt, p.2.isLt, hne]

/-- Under the bit `j` already written, a list of Clifford gates under `ifBit j` satisfies the bit
discipline. -/
theorem bitsOkFrom_map_ifBit (m j : ℕ) (W : List ℕ) (hW : W.contains j = true) {O : List Gate}
    (hcl : ∀ g ∈ O, g.isClifford = true) :
    Circuit.bitsOkFrom m W (O.map (Gate.ifBit j)) = true := by
  induction O with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.bitsOkFrom, Gate.bitOk, Gate.writes, List.append_nil,
      Bool.and_eq_true]
    exact ⟨⟨hW, hcl g (List.mem_cons_self ..)⟩, ih fun g' hg' => hcl g' (List.mem_cons_of_mem g hg')⟩

/-- PHASE2_SPEC §B.1 (22c) — **MBU applies exactly to the quadratic functions**: for a
measurement-free block `B` on the register (its qubits in range, no measurement) and an in-range
ancilla `t`, a well-formed circuit `B; Z t; mbuUncompute t j O` with `O` a phase implementation of
`f` exists iff `f` is quadratic. The classical bit `j` is existential: a well-formed circuit of this
shape has one classical bit, so `j = 0` (the task text's fixed `j` fails at `j ≥ 1`: `measure t j`
violates `j < nBits = 1`). (⇐) takes `O = phaseCircuitQuad a b`, whose gates are Clifford. -/
theorem mbu_exactly_quadratic {B : List Gate}
    (hB : ∀ g ∈ B, g.qubitsOk n = true ∧ g.isUnitary = true) {t : Qubit}
    (hanc : ∃ i, i < a ∧ t = .anc i) (f : Reg n → Bool) :
    (∃ (j : ℕ) (O : List Gate) (C : Circuit), C.nData = n ∧ C.WF ∧
        C.gates = B ++ [.z t] ++ mbuUncompute t j O ∧ PhaseImpl n a O f) ↔ IsQuadratic f := by
  constructor
  · rintro ⟨j, O, C, -, hWF, hgates, hO⟩
    exact mbu_wf_forces_quadratic hWF hgates hO
  · rintro ⟨c, a', b, hf⟩
    obtain ⟨i, hi, rfl⟩ := hanc
    refine ⟨0, phaseCircuitQuad a' b,
      ⟨n, B ++ [.z (.anc i)] ++ mbuUncompute (.anc i) 0 (phaseCircuitQuad a' b)⟩, rfl, ?_, rfl,
      phaseCircuitQuad_phaseImpl hf⟩
    have hBu : ∀ g ∈ B ++ [Gate.z (.anc i)], g.isUnitary = true := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact (hB g hg).2
      · simp only [List.mem_singleton] at hg; subst hg; rfl
    have hn1 : (⟨n, B ++ [.z (.anc i)] ++ mbuUncompute (.anc i) 0 (phaseCircuitQuad a' b)⟩ :
        Circuit).nBits = 1 :=
      nBits_of_mbu (B := B ++ [.z (.anc i)]) rfl (List.all_eq_true.2 hBu)
    have hq : ∀ g ∈ (B ++ [Gate.z (.anc i)]) ++ mbuUncompute (.anc i) 0 (phaseCircuitQuad a' b),
        g.qubitsOk n = true := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact (hB g hg).1
        · rw [List.mem_singleton] at hg
          subst hg
          rfl
      · rw [mbuUncompute] at hg
        rcases List.mem_append.1 hg with hg | hg
        · rcases List.mem_append.1 hg with hg | hg
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl <;> rfl
          · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
            rw [qubitsOk_ifBit _ _ _ (phaseCircuitQuad_isClifford a' b g' hg')]
            exact phaseCircuitQuad_qubitsOk a' b g' hg'
        · rw [List.mem_singleton] at hg
          subst hg
          rfl
    have hb : Circuit.bitsOkFrom 1 [] ((B ++ [Gate.z (.anc i)]) ++
        mbuUncompute (.anc i) 0 (phaseCircuitQuad a' b)) = true := by
      rw [bitsOkFrom_append_list, Bool.and_eq_true,
        Circuit.written_eq_nil_of_unitary (List.all_eq_true.2 hBu), List.append_nil]
      refine ⟨bitsOkFrom_of_unitary 1 [] hBu, ?_⟩
      simp only [mbuUncompute, bitsOkFrom_append_list, written_append_list, written_map_ifBit,
        Bool.and_eq_true]
      exact ⟨⟨rfl, bitsOkFrom_map_ifBit 1 0 _ rfl (phaseCircuitQuad_isClifford a' b)⟩, rfl⟩
    show Circuit.wf _ = true
    rw [Circuit.wf, Bool.and_eq_true, List.all_eq_true, Circuit.bitsOk, hn1]
    exact ⟨hq, hb⟩

end Boundary

end CQRV

end

end
