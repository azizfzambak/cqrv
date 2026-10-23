module

public import CQRV.Circuit.IR
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP

/-!
# CQRV.Circuit.Semantics

Report §9.1.1 — denotational semantics of the gate-level IR (`CQRV.Circuit.IR`): unitary
semantics of the measurement-free fragment and density-matrix semantics into a Physlib
`CPTPMap` (DECISIONS.md 2026-10-23, Stage 6 decisions 1–3).

* Register (decision 1): basis index `Reg k := Fin k → Bool`; a circuit acts on
  `Reg n × Reg a` (data × ancilla), so that `CPTPMap.traceRight` traces out the ancilla.
  `x[i]` is `s.1 i`, `anc[i]` is `s.2 i`. A qubit outside the register is acted on as the
  identity (excluded by `Circuit.WF`).
* Gates are *monomial* matrices (a permutation of the basis times a phase), except `H`, which
  is `(1/√2)(Z + X)`. Unitarity is proved once for monomial matrices.
* Measurement (decision 2): for `m` classical bits, every assignment `c : Fin m → Bool` gives one
  Kraus operator `krausOps … c`, the gate product in which `measure q → j` is the projector onto
  `q = c j` and `ifBit j g` is `g` if `c j`, else `1`. The channel is `ρ ↦ ∑_c K_c ρ K_cᴴ`
  (`CPTPMap.of_kraus_CPTPMap`). `alloc` / `free` denote the identity: that ancillae come back as
  |0⟩ is what `AncRestore` proves (`CQRV.Circuit.Restoration`), not what the semantics assumes.
* Well-formedness (decision 3): `Circuit.WF`.
-/

@[expose] public section

namespace CQRV

/-- Report §9.1.1 — the basis index of a `k`-qubit register (Stage 6 decision 1). -/
abbrev Reg (k : ℕ) := Fin k → Bool

/-! ## Well-formedness (decision 3) -/

namespace Gate

/-- The classical bits a gate writes (`measure q → j` writes `j`). -/
def writes : Gate → List Nat
  | .measure _ j => [j]
  | _ => []

/-- Report §6.2.2, §9.1.1 — classical-bit discipline of one gate, given the bits `W` written
before it and the number `m` of classical bits: a measurement writes a fresh bit `j < m`; an
`ifBit j g` reads a bit already written and controls a Clifford gate. -/
def bitOk (m : Nat) (W : List Nat) : Gate → Bool
  | .measure _ j => decide (j < m) && !W.contains j
  | .ifBit j g => W.contains j && g.isClifford
  | _ => true

/-- Report §9.1.1 — qubit discipline of one gate on `x[0..nData)`: data indices in range and
two-qubit operands distinct (for `ifBit`, those of the controlled gate). -/
def qubitsOk (nData : Nat) (g : Gate) : Bool :=
  g.qubits.all (fun q => match q with | .data i => decide (i < nData) | .anc _ => true) &&
  match (match g with | .ifBit _ inner => inner | other => other) with
  | .cnot p q | .cz p q => p != q
  | _ => true

end Gate

namespace Circuit

/-- The classical bits written by a gate list, in program order. -/
def written (gs : List Gate) : List Nat := gs.flatMap Gate.writes

/-- Report §9.1.1 — the number of classical bits: one per `measure`. -/
def nBits (C : Circuit) : Nat := (written C.gates).length

/-- Classical-bit discipline of a gate list, the bits `W` being written before it. -/
def bitsOkFrom (m : Nat) : List Nat → List Gate → Bool
  | _, [] => true
  | W, g :: gs => g.bitOk m W && bitsOkFrom m (W ++ g.writes) gs

/-- Report §9.1.1 (decision 3) — the classical-bit part of well-formedness: every classical bit
`j < nBits` is written by exactly one `measure`, before any `ifBit` reads it. This is all
that Kraus completeness needs. -/
def bitsOk (C : Circuit) : Bool := bitsOkFrom C.nBits [] C.gates

/-- Report §9.1.1, Stage 6 decision 3 — well-formedness (decidable form). -/
def wf (C : Circuit) : Bool := C.gates.all (Gate.qubitsOk C.nData) && C.bitsOk

/-- Report §9.1.1, Stage 6 decision 3 — `Circuit.WF`: data-qubit indices in range (ancilla
indices are in range of `nAnc` by definition), gate operands distinct, every classical bit
written by exactly one `measure` before any `ifBit` reads it. All semantic theorems assume it. -/
def WF (C : Circuit) : Prop := C.wf = true

instance (C : Circuit) : Decidable C.WF := inferInstanceAs (Decidable (C.wf = true))

/-- Report §6.2.2, §9.1.1 — sequential composition with shifted classical bits: the gates of
`C₁`, then those of `C₂` with every classical bit shifted up by `C₁.nBits`, so the bits of the
two pieces never clash (DECISIONS.md, Stage 6b-1 review, (A)). The register is `C₁`'s. -/
def append (C₁ C₂ : Circuit) : Circuit :=
  ⟨C₁.nData, C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)⟩

end Circuit

noncomputable section

open Matrix

/-! ## Qubits as lenses on `Reg n × Reg a` -/

namespace Qubit

variable {n a : ℕ}

/-- Report §9.1.1 — whether a qubit lies in the register `Reg n × Reg a`. -/
def inRange (n a : ℕ) : Qubit → Bool
  | .data i => decide (i < n)
  | .anc i => decide (i < a)

/-- Report §9.1.1 — the value of qubit `q` in the basis state `s` (`false` outside the
register). -/
def get (q : Qubit) (s : Reg n × Reg a) : Bool :=
  match q with
  | .data i => if h : i < n then s.1 ⟨i, h⟩ else false
  | .anc i => if h : i < a then s.2 ⟨i, h⟩ else false

/-- Report §9.1.1 — set qubit `q` of the basis state `s` to `v` (no effect outside the
register). -/
def set (q : Qubit) (v : Bool) (s : Reg n × Reg a) : Reg n × Reg a :=
  match q with
  | .data i => if h : i < n then (Function.update s.1 ⟨i, h⟩ v, s.2) else s
  | .anc i => if h : i < a then (s.1, Function.update s.2 ⟨i, h⟩ v) else s

/-- Report §9.1.1 — flip qubit `q` of the basis state `s` (the action of `X q`). -/
def flip (q : Qubit) (s : Reg n × Reg a) : Reg n × Reg a := q.set (!q.get s) s

theorem get_set_self (q : Qubit) (hq : q.inRange n a = true) (v : Bool) (s : Reg n × Reg a) :
    q.get (q.set v s) = v := by
  cases q <;> simp_all [inRange, get, set]

theorem get_set_ne {p q : Qubit} (hpq : p ≠ q) (v : Bool) (s : Reg n × Reg a) :
    p.get (q.set v s) = p.get s := by
  cases p <;> cases q <;> simp only [get, set] <;> split_ifs <;>
    simp_all [Fin.ext_iff]

theorem set_get (q : Qubit) (s : Reg n × Reg a) : q.set (q.get s) s = s := by
  cases q <;> simp only [get, set] <;> split_ifs <;> simp

theorem set_set (q : Qubit) (v w : Bool) (s : Reg n × Reg a) :
    q.set v (q.set w s) = q.set v s := by
  cases q <;> simp only [set] <;> split_ifs <;> simp

theorem set_of_not_inRange {q : Qubit} (hq : q.inRange n a = false) (v : Bool)
    (s : Reg n × Reg a) : q.set v s = s := by
  cases q <;> simp_all [inRange, set]

theorem get_flip_self (q : Qubit) (hq : q.inRange n a = true) (s : Reg n × Reg a) :
    q.get (q.flip s) = !q.get s :=
  get_set_self q hq _ s

theorem get_flip_ne {p q : Qubit} (hpq : p ≠ q) (s : Reg n × Reg a) :
    p.get (q.flip s) = p.get s :=
  get_set_ne hpq _ s

theorem flip_involutive (q : Qubit) : Function.Involutive (q.flip (n := n) (a := a)) := by
  intro s
  cases hq : q.inRange n a
  · simp [flip, set_of_not_inRange hq]
  · simp [flip, get_set_self q hq, set_set, set_get]

end Qubit

/-! ## Monomial matrices -/

section Monomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Report §9.1.1 — the monomial matrix `|σ j⟩ ↦ φ j · |σ j⟩`… i.e. `M i j = φ j` if
`i = σ j`, else `0`. All gates except `H` are of this form. -/
def monoMat (σ : ι → ι) (φ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i = σ j then φ j else 0

omit [Fintype ι] in
theorem monoMat_apply (σ : ι → ι) (φ : ι → ℂ) (i j : ι) :
    monoMat σ φ i j = if i = σ j then φ j else 0 := rfl

theorem monoMat_mul (σ τ : ι → ι) (φ ψ : ι → ℂ) :
    monoMat σ φ * monoMat τ ψ = monoMat (σ ∘ τ) (fun j => φ (τ j) * ψ j) := by
  ext i j
  simp only [Matrix.mul_apply, monoMat_apply, Function.comp_apply, ite_mul, zero_mul, mul_ite,
    mul_zero]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk; simp [hk]
  · simp

omit [Fintype ι] in
theorem monoMat_add (σ : ι → ι) (φ ψ : ι → ℂ) :
    monoMat σ φ + monoMat σ ψ = monoMat σ (φ + ψ) := by
  ext i j
  simp only [Matrix.add_apply, monoMat_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype ι] in
theorem monoMat_id_one : monoMat (id : ι → ι) (fun _ => 1) = 1 := by
  ext i j
  simp [monoMat_apply, Matrix.one_apply]

omit [Fintype ι] in
theorem monoMat_zero (σ : ι → ι) : monoMat σ (0 : ι → ℂ) = 0 := by
  ext i j
  simp [monoMat_apply]

omit [Fintype ι] in
theorem star_monoMat {σ : ι → ι} (hσ : Function.Involutive σ) (φ : ι → ℂ) :
    star (monoMat σ φ) = monoMat σ (fun j => star (φ (σ j))) := by
  ext i j
  simp only [Matrix.star_apply, monoMat_apply]
  by_cases h : i = σ j
  · subst h; simp [hσ j]
  · have h' : ¬ j = σ i := fun h' => h (by rw [h', hσ i])
    simp [h, h']

theorem monoMat_mulVec {σ : ι → ι} (hσ : Function.Involutive σ) (φ : ι → ℂ) (v : ι → ℂ)
    (i : ι) : (monoMat σ φ *ᵥ v) i = φ (σ i) * v (σ i) := by
  simp only [Matrix.mulVec, dotProduct, monoMat_apply, ite_mul, zero_mul]
  have h : ∀ j, (i = σ j) ↔ (j = σ i) := fun j =>
    ⟨fun h => by rw [h, hσ j], fun h => by rw [h, hσ i]⟩
  simp_rw [h]
  simp

/-- Report §9.1.1 — a monomial matrix with an involutive permutation and unit phases is
unitary. -/
theorem monoMat_mem_unitaryGroup {σ : ι → ι} (hσ : Function.Involutive σ) {φ : ι → ℂ}
    (hφ : ∀ j, star (φ j) * φ j = 1) : monoMat σ φ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_monoMat hσ, monoMat_mul, hσ.comp_self]
  convert (monoMat_id_one (ι := ι)) using 2
  funext j
  simp only [hσ j, hφ]

/-- `star z * z = 1` for the phases ±1 of the sign function. -/
theorem star_sign_mul (b : Bool) :
    star (if b then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) = 1 := by
  cases b <;> simp

/-- Report §9.1.1 — the Hadamard-type matrix `(1/√2)(Z_b + X_f)` for a sign bit `b` and an
involution `f` flipping it (`b (f j) = !b j`). -/
def hMat (b : ι → Bool) (f : ι → ι) : Matrix ι ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (monoMat id (fun j => if b j then -1 else 1) + monoMat f (fun _ => 1))

theorem hMat_mulVec {b : ι → Bool} {f : ι → ι} (hf : Function.Involutive f) (v : ι → ℂ)
    (i : ι) : (hMat b f *ᵥ v) i =
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if b i then -1 else 1) * v i + v (f i)) := by
  rw [hMat, Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply, Pi.add_apply,
    monoMat_mulVec (fun _ => rfl), monoMat_mulVec hf]
  simp

/-- `(1/√2)² = 1/2` in `ℂ`. -/
theorem invSqrtTwo_mul_self : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem hMat_mem_unitaryGroup {b : ι → Bool} {f : ι → ι} (hf : Function.Involutive f)
    (hb : ∀ j, b (f j) = !b j) : hMat b f ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', hMat, star_smul, star_add,
    star_monoMat (fun _ => rfl), star_monoMat hf, smul_mul_smul_comm, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add, monoMat_mul, monoMat_mul, monoMat_mul, monoMat_mul,
    hf.comp_self]
  have hs : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    simp
  rw [hs, invSqrtTwo_mul_self]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, monoMat_apply, Function.comp_apply, id,
    Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have hne : ¬ i = f i := by
      intro h; have := hb i; rw [← h] at this; revert this; cases b i <;> simp
    simp only [hne, ite_true, ite_false, star_one, one_mul, mul_one]
    rw [star_sign_mul]
    norm_num
  · simp only [hij, ite_false]
    by_cases hfj : i = f j
    · subst hfj
      simp only [hb j, ite_true, star_one, one_mul, mul_one]
      cases b j <;> simp
    · simp [hfj]

end Monomial

/-! ## The T phase ω -/

/-- Report §6.2.2, §9.1.1 — the T phase `ω = exp(π/4 · i)`. -/
def ω : ℂ := Complex.exp (Real.pi / 4 * Complex.I)

theorem ω_sq : ω ^ 2 = Complex.I := by
  rw [ω, ← Complex.exp_nat_mul,
    show ((2 : ℕ) : ℂ) * (Real.pi / 4 * Complex.I) = Real.pi / 2 * Complex.I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

theorem ω_pow_four : ω ^ 4 = -1 := by
  rw [show ω ^ 4 = (ω ^ 2) ^ 2 by ring, ω_sq, Complex.I_sq]

theorem star_ω_mul_ω : star ω * ω = 1 := by
  rw [ω, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal, map_ofNat]
  ring_nf
  exact Complex.exp_zero

theorem ω_mul_star_ω : ω * star ω = 1 := by rw [mul_comm, star_ω_mul_ω]

/-- `ω̄ = −ω³` (from `ω ω̄ = 1` and `ω⁴ = −1`). -/
theorem star_ω : star ω = -ω ^ 3 := by
  linear_combination (star ω) * ω_pow_four - ω ^ 3 * star_ω_mul_ω

theorem ω_pow_five : ω ^ 5 = -ω := by linear_combination ω * ω_pow_four
theorem ω_pow_six : ω ^ 6 = -ω ^ 2 := by linear_combination ω ^ 2 * ω_pow_four
theorem ω_pow_seven : ω ^ 7 = -ω ^ 3 := by linear_combination ω ^ 3 * ω_pow_four
theorem ω_pow_eight : ω ^ 8 = 1 := by linear_combination (ω ^ 4 - 1) * ω_pow_four
theorem ω_pow_nine : ω ^ 9 = ω := by linear_combination ω * (ω ^ 4 - 1) * ω_pow_four
theorem ω_pow_ten : ω ^ 10 = ω ^ 2 := by linear_combination ω ^ 2 * (ω ^ 4 - 1) * ω_pow_four
theorem ω_pow_eleven : ω ^ 11 = ω ^ 3 := by linear_combination ω ^ 3 * (ω ^ 4 - 1) * ω_pow_four
theorem ω_pow_twelve : ω ^ 12 = -1 := by linear_combination (ω ^ 8 - ω ^ 4 + 1) * ω_pow_four

/-- `(1/√2)² = 1/2`, in the form `ring_nf` produces. -/
theorem invSqrtTwo_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-! ## Gate matrices and the unitary fragment -/

section Gates

variable (n a : ℕ)

/-- Report §9.1.1 — the phase gate `diag(1, p)` on qubit `q`. -/
def phaseMat (q : Qubit) (p : ℂ) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  monoMat id (fun s => if q.get s then p else 1)

/-- Report §9.1.1 — the CNOT basis permutation: flip `t` when `c` is 1. -/
def cnotPerm (c t : Qubit) (s : Reg n × Reg a) : Reg n × Reg a :=
  if c.get s then t.flip s else s

theorem cnotPerm_involutive {c t : Qubit} (hct : c ≠ t) :
    Function.Involutive (cnotPerm n a c t) := by
  intro s
  unfold cnotPerm
  cases hc : c.get s
  · simp [hc]
  · simp [hc, Qubit.get_flip_ne hct, (Qubit.flip_involutive t) s]

/-- Report §9.1.1, §6.2.2 — gate matrices of the unitary gates, defined by their basis action:
`H = (1/√2)(Z + X)`, `S = diag(1, i)`, `S† = diag(1, −i)`, `T = diag(1, ω)`,
`T† = diag(1, ω̄)`, `X`, `Z`, `CNOT`, `CZ`. A gate on a qubit outside the register, and a
two-qubit gate with a repeated operand, act as the identity (both excluded by `Circuit.WF`).
`measure`, `ifBit`, `alloc`, `free` are `1` here; their semantics is `krausOps`. -/
def gateU : Gate → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ
  | .h q => if q.inRange n a then hMat q.get q.flip else 1
  | .s q => phaseMat n a q Complex.I
  | .sdg q => phaseMat n a q (-Complex.I)
  | .t q => phaseMat n a q ω
  | .tdg q => phaseMat n a q (star ω)
  | .x q => monoMat q.flip (fun _ => 1)
  | .z q => phaseMat n a q (-1)
  | .cnot c t => if c = t then 1 else monoMat (cnotPerm n a c t) (fun _ => 1)
  | .cz p q => monoMat id (fun s => if p.get s && q.get s then -1 else 1)
  | .measure _ _ => 1
  | .ifBit _ _ => 1
  | .alloc _ => 1
  | .free _ => 1

theorem phaseMat_mem_unitaryGroup (q : Qubit) {p : ℂ} (hp : star p * p = 1) :
    phaseMat n a q p ∈ Matrix.unitaryGroup (Reg n × Reg a) ℂ :=
  monoMat_mem_unitaryGroup (fun _ => rfl) fun s => by split_ifs; exacts [hp, by simp]

/-- Report §9.1.1 — every gate matrix is unitary. -/
theorem gateU_mem_unitaryGroup (g : Gate) :
    gateU n a g ∈ Matrix.unitaryGroup (Reg n × Reg a) ℂ := by
  cases g with
  | h q =>
    simp only [gateU]
    split_ifs with hq
    · exact hMat_mem_unitaryGroup (Qubit.flip_involutive q) (Qubit.get_flip_self q hq)
    · exact one_mem _
  | s q => exact phaseMat_mem_unitaryGroup n a q (by simp)
  | sdg q => exact phaseMat_mem_unitaryGroup n a q (by simp)
  | t q => exact phaseMat_mem_unitaryGroup n a q star_ω_mul_ω
  | tdg q => exact phaseMat_mem_unitaryGroup n a q (by rw [star_star, ω_mul_star_ω])
  | x q => exact monoMat_mem_unitaryGroup (Qubit.flip_involutive q) (fun _ => by simp)
  | z q => exact phaseMat_mem_unitaryGroup n a q (by simp)
  | cnot c t =>
    simp only [gateU]
    split_ifs with hct
    · exact one_mem _
    · exact monoMat_mem_unitaryGroup (cnotPerm_involutive n a hct) (fun _ => by simp)
  | cz p q => exact monoMat_mem_unitaryGroup (fun _ => rfl) (fun s => star_sign_mul _)
  | measure _ _ => exact one_mem _
  | ifBit _ _ => exact one_mem _
  | alloc _ => exact one_mem _
  | free _ => exact one_mem _

/-- Report §9.1.1 — the unitary semantics of a gate list (first gate applied first). It is the
intended semantics on the unitary fragment (`Gate.isUnitary`); there it agrees with every
Kraus operator (`krausOps_of_unitary`). -/
def unitaryDenote : List Gate → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ
  | [] => 1
  | g :: gs => unitaryDenote gs * gateU n a g

/-- Report §9.1.1 — the unitary semantics of a circuit is unitary. -/
theorem unitaryDenote_mem_unitaryGroup (gs : List Gate) :
    unitaryDenote n a gs ∈ Matrix.unitaryGroup (Reg n × Reg a) ℂ := by
  induction gs with
  | nil => exact one_mem _
  | cons g gs ih => exact mul_mem ih (gateU_mem_unitaryGroup n a g)

theorem unitaryDenote_nil : unitaryDenote n a [] = 1 := rfl

theorem gateU_s (q : Qubit) : gateU n a (.s q) = phaseMat n a q Complex.I := rfl
theorem gateU_sdg (q : Qubit) : gateU n a (.sdg q) = phaseMat n a q (-Complex.I) := rfl
theorem gateU_t (q : Qubit) : gateU n a (.t q) = phaseMat n a q ω := rfl
theorem gateU_tdg (q : Qubit) : gateU n a (.tdg q) = phaseMat n a q (star ω) := rfl
theorem gateU_z (q : Qubit) : gateU n a (.z q) = phaseMat n a q (-1) := rfl

theorem unitaryDenote_cons_mulVec (g : Gate) (gs : List Gate) (v : Reg n × Reg a → ℂ) :
    unitaryDenote n a (g :: gs) *ᵥ v = unitaryDenote n a gs *ᵥ (gateU n a g *ᵥ v) := by
  rw [unitaryDenote, Matrix.mulVec_mulVec]


/-! Gate action on state vectors, pointwise (used for gate-by-gate proofs on basis inputs). -/

theorem gateU_h_mulVec {q : Qubit} (hq : q.inRange n a = true) (v : Reg n × Reg a → ℂ)
    (i : Reg n × Reg a) : (gateU n a (.h q) *ᵥ v) i =
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if q.get i then -1 else 1) * v i + v (q.flip i)) := by
  simp only [gateU, hq, ↓reduceIte]
  rw [hMat_mulVec (Qubit.flip_involutive q)]

theorem phaseMat_mulVec (q : Qubit) (p : ℂ) (v : Reg n × Reg a → ℂ) (i : Reg n × Reg a) :
    (phaseMat n a q p *ᵥ v) i = (if q.get i then p else 1) * v i := by
  rw [phaseMat, monoMat_mulVec (fun _ => rfl)]
  rfl

theorem gateU_x_mulVec (q : Qubit) (v : Reg n × Reg a → ℂ) (i : Reg n × Reg a) :
    (gateU n a (.x q) *ᵥ v) i = v (q.flip i) := by
  rw [gateU, monoMat_mulVec (Qubit.flip_involutive q), one_mul]

theorem gateU_cnot_mulVec {c t : Qubit} (hct : c ≠ t) (v : Reg n × Reg a → ℂ)
    (i : Reg n × Reg a) : (gateU n a (.cnot c t) *ᵥ v) i = v (cnotPerm n a c t i) := by
  simp only [gateU, hct, ↓reduceIte]
  rw [monoMat_mulVec (cnotPerm_involutive n a hct), one_mul]

theorem gateU_cz_mulVec (p q : Qubit) (v : Reg n × Reg a → ℂ) (i : Reg n × Reg a) :
    (gateU n a (.cz p q) *ᵥ v) i = (if p.get i && q.get i then -1 else 1) * v i := by
  rw [gateU, monoMat_mulVec (fun _ => rfl)]
  rfl

end Gates

/-- Report §9.1.1 — the unitary fragment: no `measure`, no `ifBit`. -/
def Gate.isUnitary : Gate → Bool
  | .measure _ _ | .ifBit _ _ => false
  | _ => true

/-! ## Kraus semantics (decision 2) -/

section Kraus

variable (n a : ℕ)

/-- Report §9.1.1 — the value of classical bit `j` under the assignment `c` (`false` for
`j ≥ m`, excluded by `Circuit.WF`). -/
def bitVal {m : ℕ} (c : Fin m → Bool) (j : ℕ) : Bool := if h : j < m then c ⟨j, h⟩ else false

/-- Report §9.1.1 — the projector onto `q = v` (computational-basis measurement outcome). -/
def projMat (q : Qubit) (v : Bool) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  monoMat id (fun s => if q.get s = v then 1 else 0)

/-- Report §9.1.1, Stage 6 decision 2 — one gate in the branch `c`: `measure q → j` is the
projector onto `q = c j`, `ifBit j g` is `g` if `c j` and `1` otherwise, a unitary gate is its
matrix. -/
def gateK {m : ℕ} (c : Fin m → Bool) : Gate → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ
  | .measure q j => projMat n a q (bitVal c j)
  | .ifBit j g => if bitVal c j then gateU n a g else 1
  | g => gateU n a g

/-- Report §9.1.1, Stage 6 decision 2 — the Kraus operator `K_c` of the branch
`c : Fin m → Bool`: the product of the branch's gate matrices (first gate applied first). -/
def krausOps (m : ℕ) : List Gate → (Fin m → Bool) → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ
  | [], _ => 1
  | g :: gs, c => krausOps m gs c * gateK n a c g

theorem projMat_conjTranspose_mul (q : Qubit) (v : Bool) :
    (projMat n a q v)ᴴ * projMat n a q v = projMat n a q v := by
  rw [← Matrix.star_eq_conjTranspose, projMat, star_monoMat (fun _ => rfl), monoMat_mul]
  congr 1
  funext s
  simp only [id]
  split_ifs <;> simp

theorem projMat_add_not (q : Qubit) (v : Bool) :
    projMat n a q v + projMat n a q (!v) = 1 := by
  rw [projMat, projMat, monoMat_add, ← monoMat_id_one]
  congr 1
  funext s
  simp only [Pi.add_apply]
  cases q.get s <;> cases v <;> simp

theorem krausOps_append (m : ℕ) (gs : List Gate) (g : Gate) (c : Fin m → Bool) :
    krausOps n a m (gs ++ [g]) c = gateK n a c g * krausOps n a m gs c := by
  induction gs with
  | nil => simp [krausOps]
  | cons g' gs ih => simp [krausOps, ih, mul_assoc]

/-- Report §9.1.1 — on the unitary fragment every Kraus operator is the unitary semantics. -/
theorem krausOps_of_unitary (m : ℕ) (gs : List Gate) (h : gs.all Gate.isUnitary = true)
    (c : Fin m → Bool) : krausOps n a m gs c = unitaryDenote n a gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [krausOps, unitaryDenote, ih h.2]
    cases g <;> simp_all [Gate.isUnitary, gateK]

theorem written_append (gs : List Gate) (g : Gate) :
    Circuit.written (gs ++ [g]) = Circuit.written gs ++ g.writes := by
  simp [Circuit.written, List.flatMap_append]

theorem bitsOkFrom_append (m : ℕ) (W : List ℕ) (gs : List Gate) (g : Gate) :
    Circuit.bitsOkFrom m W (gs ++ [g]) =
      (Circuit.bitsOkFrom m W gs && g.bitOk m (W ++ Circuit.written gs)) := by
  induction gs generalizing W with
  | nil => simp [Circuit.bitsOkFrom, Circuit.written]
  | cons g' gs ih =>
    simp only [List.cons_append, Circuit.bitsOkFrom, ih, Circuit.written, List.flatMap_cons,
      List.append_assoc, Bool.and_assoc]

/-- Completeness step for a gate that writes no bit: if `G c` is unitary in every branch, the
sum `∑_c K_cᴴ K_c` is unchanged. -/
theorem kraus_step_unitary {m : ℕ}
    (K G : (Fin m → Bool) → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ)
    (hG : ∀ c, (G c)ᴴ * G c = 1) :
    ∑ c, (G c * K c)ᴴ * (G c * K c) = ∑ c, (K c)ᴴ * K c := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (G c)ᴴ, hG, Matrix.one_mul]

/-- Flip classical bit `j` of an assignment. -/
def flipBit {m : ℕ} (j : Fin m) (c : Fin m → Bool) : Fin m → Bool :=
  Function.update c j (!c j)

theorem flipBit_involutive {m : ℕ} (j : Fin m) : Function.Involutive (flipBit j) := by
  intro c
  funext k
  by_cases hk : k = j
  · subst hk; simp [flipBit]
  · simp [flipBit, hk]

/-- Completeness step for `measure q → j` on a fresh bit `j < m`: when `K_c` does not depend on
bit `j`, `2 • ∑_c K_cᴴ P_{c j}ᴴ P_{c j} K_c = ∑_c K_cᴴ K_c` (pair `c` with `c` flipped at `j`,
then `P₀ + P₁ = 1`). -/
theorem kraus_step_measure {m : ℕ} (q : Qubit) (j : ℕ) (hj : j < m)
    (K : (Fin m → Bool) → Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ)
    (hK : ∀ c, K (flipBit ⟨j, hj⟩ c) = K c) :
    (2 : ℂ) • ∑ c, (projMat n a q (bitVal c j) * K c)ᴴ * (projMat n a q (bitVal c j) * K c) =
      ∑ c, (K c)ᴴ * K c := by
  have hP : ∀ c, (projMat n a q (bitVal c j) * K c)ᴴ * (projMat n a q (bitVal c j) * K c) =
      (K c)ᴴ * (projMat n a q (bitVal c j) * K c) := fun c => by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (projMat n a q _)ᴴ,
      projMat_conjTranspose_mul]
  simp_rw [hP]
  have hb : ∀ c, bitVal (flipBit ⟨j, hj⟩ c) j = !bitVal c j := fun c => by
    simp [bitVal, hj, flipBit]
  rw [two_smul]
  conv_lhs => arg 2; rw [← Equiv.sum_comp (flipBit_involutive ⟨j, hj⟩).toPerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Function.Involutive.coe_toPerm, hK, hb]
  rw [← Matrix.mul_add, ← Matrix.add_mul, projMat_add_not, Matrix.one_mul]

/-- Report §9.1.1 — the invariant behind Kraus completeness, for a prefix `gs` of a circuit with
`m` classical bits obeying the bit discipline: `K_c` depends only on the bits written so far,
and `2^|written| • ∑_c K_cᴴ K_c = 2^m • 1`. -/
theorem kraus_invariant (m : ℕ) (gs : List Gate) (h : Circuit.bitsOkFrom m [] gs = true) :
    (∀ c c' : Fin m → Bool, (∀ j ∈ Circuit.written gs, bitVal c j = bitVal c' j) →
        krausOps n a m gs c = krausOps n a m gs c') ∧
      (2 : ℂ) ^ (Circuit.written gs).length •
          ∑ c, (krausOps n a m gs c)ᴴ * krausOps n a m gs c =
        (2 : ℂ) ^ m • (1 : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ _ _ => rfl, ?_⟩
    simp only [Circuit.written, List.flatMap_nil, List.length_nil, pow_zero, one_smul, krausOps,
      Matrix.conjTranspose_one, Matrix.mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    rfl
  | append_singleton gs g ih =>
    rw [bitsOkFrom_append, Bool.and_eq_true, List.nil_append] at h
    obtain ⟨hind, hsum⟩ := ih h.1
    have hg := h.2
    simp only [krausOps_append, written_append]
    cases g with
    | measure q j =>
      simp only [Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      obtain ⟨hj, hnew⟩ := hg
      rw [← Bool.not_eq_true, List.contains_iff_mem] at hnew
      refine ⟨fun c c' hcc' => ?_, ?_⟩
      · have h1 : bitVal c j = bitVal c' j := hcc' j (by simp [Gate.writes])
        have h2 := hind c c' fun k hk => hcc' k (List.mem_append_left _ hk)
        simp only [gateK, h1, h2]
      · have hK : ∀ c, krausOps n a m gs (flipBit ⟨j, hj⟩ c) = krausOps n a m gs c := fun c =>
          hind _ _ fun k hk => by
            have hkj : k ≠ j := fun e => hnew (e ▸ hk)
            by_cases hkm : k < m
            · simp [bitVal, hkm, flipBit, Fin.ext_iff, hkj]
            · simp [bitVal, hkm]
        simp only [gateK, Gate.writes, List.length_append, List.length_singleton, pow_succ,
          mul_smul]
        rw [kraus_step_measure n a q j hj _ hK, hsum]
    | ifBit j u =>
      simp only [Gate.bitOk, Bool.and_eq_true, List.contains_iff_mem] at hg
      refine ⟨fun c c' hcc' => ?_, ?_⟩
      · simp only [Gate.writes, List.append_nil] at hcc'
        simp only [gateK, hcc' j hg.1, hind c c' hcc']
      · simp only [Gate.writes, List.append_nil]
        rw [kraus_step_unitary n a _ _ fun c => ?_, hsum]
        simp only [gateK]
        split_ifs
        · rw [← Matrix.star_eq_conjTranspose]
          exact (Matrix.mem_unitaryGroup_iff').mp (gateU_mem_unitaryGroup n a u)
        · simp
    | _ =>
      refine ⟨fun c c' hcc' => ?_, ?_⟩
      · simp only [Gate.writes, List.append_nil] at hcc'
        simp only [gateK, hind c c' hcc']
      · simp only [Gate.writes, List.append_nil]
        rw [kraus_step_unitary n a _ _ fun c => ?_, hsum]
        simp only [gateK]
        rw [← Matrix.star_eq_conjTranspose]
        exact (Matrix.mem_unitaryGroup_iff').mp (gateU_mem_unitaryGroup n a _)

/-- Report §9.1.1, Stage 6 task 2 — Kraus completeness `∑_c K_cᴴ K_c = 1` for a circuit obeying
the classical-bit discipline (`Circuit.bitsOk`, part of `Circuit.WF`). -/
theorem krausOps_complete (C : Circuit) (h : C.bitsOk = true) :
    ∑ c, (krausOps n a C.nBits C.gates c)ᴴ * krausOps n a C.nBits C.gates c = 1 :=
  smul_right_injective _ (pow_ne_zero C.nBits (two_ne_zero (α := ℂ)))
    (kraus_invariant n a C.nBits C.gates h).2

/-- Report §9.1.1, §6.2.2 — the density-matrix semantics `ρ ↦ ∑_c K_c ρ K_cᴴ` of a circuit on
`Reg n × Reg a` (Stage 6 decision 2). A circuit violating the classical-bit discipline has no
Kraus decomposition of this form and is mapped to the identity channel. No theorem relies on
that fallback: all theorems assume `Circuit.WF`, and `Circuit.WF.bitsOk` gives `C.bitsOk = true`,
so `channelDenote_of_WF` rewrites to the Kraus channel. -/
def channelDenote (C : Circuit) : CPTPMap (Reg n × Reg a) (Reg n × Reg a) :=
  if h : C.bitsOk = true then
    CPTPMap.of_kraus_CPTPMap (krausOps n a C.nBits C.gates) (krausOps_complete n a C h)
  else CPTPMap.id

/-- Report §9.1.1 — well-formedness includes the classical-bit discipline. -/
theorem Circuit.WF.bitsOk {C : Circuit} (h : C.WF) : C.bitsOk = true := by
  simp only [Circuit.WF, Circuit.wf, Bool.and_eq_true] at h
  exact h.2

/-- Report §9.1.1 — on a well-formed circuit `channelDenote` is the Kraus channel (never the
`CPTPMap.id` fallback). -/
theorem channelDenote_of_WF {C : Circuit} (h : C.WF) :
    channelDenote n a C =
      CPTPMap.of_kraus_CPTPMap (krausOps n a C.nBits C.gates) (krausOps_complete n a C h.bitsOk) := by
  simp only [channelDenote, h.bitsOk, ↓reduceDIte]

/-- Report §9.1.1 — the matrix of `channelDenote` under the classical-bit discipline:
`∑_c K_c ρ K_cᴴ`. -/
theorem channelDenote_m_of_bitsOk {C : Circuit} (h : C.bitsOk = true)
    (ρ : MState (Reg n × Reg a)) :
    (channelDenote n a C ρ).m =
      ∑ c, krausOps n a C.nBits C.gates c * ρ.m * (krausOps n a C.nBits C.gates c)ᴴ := by
  simp only [channelDenote, h, ↓reduceDIte]
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (∑ k, _ : MatrixMap _ _ ℂ) ρ.m = _
  rw [LinearMap.sum_apply]
  rfl

/-! ## Composition with shifted classical bits (`Circuit.append`) -/

theorem Gate.writes_shiftBits (k : ℕ) (g : Gate) :
    (g.shiftBits k).writes = g.writes.map (· + k) := by
  cases g <;> rfl

theorem written_append_list (gs₁ gs₂ : List Gate) :
    Circuit.written (gs₁ ++ gs₂) = Circuit.written gs₁ ++ Circuit.written gs₂ := by
  simp [Circuit.written, List.flatMap_append]

theorem written_map_shiftBits (k : ℕ) (gs : List Gate) :
    Circuit.written (gs.map (Gate.shiftBits k)) = (Circuit.written gs).map (· + k) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.written, List.flatMap_cons, List.map_append] at ih ⊢
    rw [Gate.writes_shiftBits, ih]

theorem Circuit.nBits_append (C₁ C₂ : Circuit) :
    (C₁.append C₂).nBits = C₁.nBits + C₂.nBits := by
  simp [Circuit.append, Circuit.nBits, written_append_list, written_map_shiftBits]

theorem bitsOkFrom_append_list (m : ℕ) (W : List ℕ) (gs₁ gs₂ : List Gate) :
    Circuit.bitsOkFrom m W (gs₁ ++ gs₂) =
      (Circuit.bitsOkFrom m W gs₁ && Circuit.bitsOkFrom m (W ++ Circuit.written gs₁) gs₂) := by
  induction gs₁ generalizing W with
  | nil => simp [Circuit.bitsOkFrom, Circuit.written]
  | cons g gs ih =>
    simp only [List.cons_append, Circuit.bitsOkFrom, ih, Circuit.written, List.flatMap_cons,
      List.append_assoc, Bool.and_assoc]

/-- The bit discipline survives a larger bit count, and the bits written stay below `m`. -/
theorem bitsOkFrom_mono {m M : ℕ} (hmM : m ≤ M) (W : List ℕ) (gs : List Gate)
    (h : Circuit.bitsOkFrom m W gs = true) :
    Circuit.bitsOkFrom M W gs = true ∧ ∀ j ∈ Circuit.written gs, j < m := by
  induction gs generalizing W with
  | nil => simp [Circuit.bitsOkFrom, Circuit.written]
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := ih _ h.2
    refine ⟨⟨?_, h1⟩, ?_⟩
    · have := h.1
      cases g <;> simp_all [Gate.bitOk]
      omega
    · intro j hj
      simp only [Circuit.written, List.flatMap_cons, List.mem_append] at hj
      rcases hj with hj | hj
      · have := h.1
        cases g <;> simp_all [Gate.writes, Gate.bitOk]
      · exact h2 j hj

/-- The bit discipline of a list shifted by `m₁`, after a prefix that wrote bits `V < m₁`. -/
theorem bitsOkFrom_shift {m₁ m₂ : ℕ} (W V : List ℕ) (hV : ∀ j ∈ V, j < m₁) (gs : List Gate)
    (h : Circuit.bitsOkFrom m₂ W gs = true) :
    Circuit.bitsOkFrom (m₁ + m₂) (V ++ W.map (· + m₁)) (gs.map (Gate.shiftBits m₁)) = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true, List.map_cons] at h ⊢
    refine ⟨?_, ?_⟩
    · have := h.1
      cases g with
      | measure q j =>
        simp only [Gate.shiftBits, Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true'] at this ⊢
        simp only [← Bool.not_eq_true, List.contains_iff_mem] at this ⊢
        obtain ⟨hj, hW⟩ := this
        refine ⟨by omega, ?_⟩
        simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and]
        exact ⟨fun hmem => by have := hV _ hmem; omega,
          fun b hb he => hW ((by omega : b = j) ▸ hb)⟩
      | ifBit j u =>
        simp only [Gate.shiftBits, Gate.bitOk, Bool.and_eq_true, List.contains_iff_mem] at this ⊢
        exact ⟨List.mem_append_right _ (List.mem_map_of_mem this.1), this.2⟩
      | _ => rfl
    · have := ih (W ++ g.writes) h.2
      rwa [List.map_append, ← List.append_assoc, ← Gate.writes_shiftBits] at this

/-- Report §9.1.1 — `Circuit.append` preserves the classical-bit discipline. -/
theorem Circuit.bitsOk_append {C₁ C₂ : Circuit} (h₁ : C₁.bitsOk = true)
    (h₂ : C₂.bitsOk = true) : (C₁.append C₂).bitsOk = true := by
  have hm := bitsOkFrom_mono (Nat.le_add_right C₁.nBits C₂.nBits) [] C₁.gates h₁
  have hs := bitsOkFrom_shift [] (Circuit.written C₁.gates) hm.2 C₂.gates h₂
  simp only [List.map_nil, List.append_nil] at hs
  unfold Circuit.bitsOk
  rw [Circuit.nBits_append]
  change Circuit.bitsOkFrom _ [] (C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)) = true
  rw [bitsOkFrom_append_list, hm.1, Bool.true_and, List.nil_append]
  exact hs

theorem bitVal_castAdd {m₁ m₂ : ℕ} (c : Fin (m₁ + m₂) → Bool) {j : ℕ} (hj : j < m₁) :
    bitVal c j = bitVal (fun i => c (Fin.castAdd m₂ i)) j := by
  simp [bitVal, hj, show j < m₁ + m₂ by omega]

theorem bitVal_natAdd {m₁ m₂ : ℕ} (c : Fin (m₁ + m₂) → Bool) (j : ℕ) :
    bitVal c (j + m₁) = bitVal (fun i => c (Fin.natAdd m₁ i)) j := by
  unfold bitVal
  by_cases hj : j < m₂
  · simp only [show j + m₁ < m₁ + m₂ by omega, hj, ↓reduceDIte]
    congr 1; ext; simp; omega
  · simp only [show ¬ j + m₁ < m₁ + m₂ by omega, hj, ↓reduceDIte]

/-- Report §9.1.1 — the Kraus operator of a concatenation, in one branch `c` over the same
classical bits: `K_c(gs₁ ++ gs₂) = K_c(gs₂) · K_c(gs₁)`. -/
theorem krausOps_append_gates (m : ℕ) (gs₁ gs₂ : List Gate) (c : Fin m → Bool) :
    krausOps n a m (gs₁ ++ gs₂) c = krausOps n a m gs₂ c * krausOps n a m gs₁ c := by
  induction gs₁ with
  | nil => simp [krausOps]
  | cons g gs ih => simp [krausOps, ih, Matrix.mul_assoc]

/-- A disciplined prefix with `m₁` bits only reads the first `m₁` bits of a branch. -/
theorem krausOps_castAdd {m₁ m₂ : ℕ} (W : List ℕ) (hW : ∀ j ∈ W, j < m₁) (gs : List Gate)
    (h : Circuit.bitsOkFrom m₁ W gs = true) (c : Fin (m₁ + m₂) → Bool) :
    krausOps n a (m₁ + m₂) gs c = krausOps n a m₁ gs (fun i => c (Fin.castAdd m₂ i)) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true] at h
    have hg := h.1
    rw [krausOps, krausOps, ih (W ++ g.writes) ?_ h.2]
    · congr 1
      cases g with
      | measure q j =>
        simp only [Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq] at hg
        simp only [gateK, bitVal_castAdd c hg.1]
      | ifBit j u =>
        simp only [Gate.bitOk, Bool.and_eq_true, List.contains_iff_mem] at hg
        simp only [gateK, bitVal_castAdd c (hW j hg.1)]
      | _ => rfl
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hW j hj
      · cases g <;> simp_all [Gate.writes, Gate.bitOk]

/-- A list shifted by `m₁` only reads the last `m₂` bits of a branch. -/
theorem krausOps_shift {m₁ m₂ : ℕ} (gs : List Gate) (c : Fin (m₁ + m₂) → Bool) :
    krausOps n a (m₁ + m₂) (gs.map (Gate.shiftBits m₁)) c =
      krausOps n a m₂ gs (fun i => c (Fin.natAdd m₁ i)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, krausOps, krausOps, ih]
    congr 1
    cases g with
    | measure q j => simp only [Gate.shiftBits, gateK, bitVal_natAdd]
    | ifBit j u => simp only [Gate.shiftBits, gateK, bitVal_natAdd]
    | _ => rfl

/-- Branch assignments of `m₁ + m₂` bits are pairs of assignments (`Fin.append`). -/
def appendEquiv (m₁ m₂ : ℕ) : (Fin (m₁ + m₂) → Bool) ≃ (Fin m₁ → Bool) × (Fin m₂ → Bool) where
  toFun c := (fun i => c (Fin.castAdd m₂ i), fun i => c (Fin.natAdd m₁ i))
  invFun p := Fin.append p.1 p.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv _ := Prod.ext (funext fun i => Fin.append_left _ _ i)
    (funext fun i => Fin.append_right _ _ i)

/-- The Kraus sum of a shifted concatenation is the composition of the two Kraus sums (split
the branch with `appendEquiv`). -/
theorem sum_krausOps_append {m₁ : ℕ} (m₂ : ℕ) (gs₁ gs₂ : List Gate)
    (h₁ : Circuit.bitsOkFrom m₁ [] gs₁ = true) (X : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    ∑ c, krausOps n a (m₁ + m₂) (gs₁ ++ gs₂.map (Gate.shiftBits m₁)) c * X *
        (krausOps n a (m₁ + m₂) (gs₁ ++ gs₂.map (Gate.shiftBits m₁)) c)ᴴ =
      ∑ c₂, krausOps n a m₂ gs₂ c₂ *
        (∑ c₁, krausOps n a m₁ gs₁ c₁ * X * (krausOps n a m₁ gs₁ c₁)ᴴ) *
          (krausOps n a m₂ gs₂ c₂)ᴴ := by
  rw [Fintype.sum_equiv (appendEquiv m₁ m₂) _ (fun p => krausOps n a m₂ gs₂ p.2 *
      (krausOps n a m₁ gs₁ p.1 * X * (krausOps n a m₁ gs₁ p.1)ᴴ) * (krausOps n a m₂ gs₂ p.2)ᴴ)
      fun c => ?_, Fintype.sum_prod_type, Finset.sum_comm]
  · refine Finset.sum_congr rfl fun c₂ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  · rw [krausOps_append_gates, krausOps_castAdd n a [] (by simp) gs₁ h₁, krausOps_shift,
      Matrix.conjTranspose_mul]
    simp only [appendEquiv, Equiv.coe_fn_mk, Matrix.mul_assoc]

/-- Report §9.1.1, §6.2.4 — channel composition: for circuits obeying the classical-bit
discipline (implied by `Circuit.WF`), the shifted append denotes the composed channel. -/
theorem channelDenote_append {C₁ C₂ : Circuit} (h₁ : C₁.bitsOk = true) (h₂ : C₂.bitsOk = true) :
    channelDenote n a (C₁.append C₂) = channelDenote n a C₂ ∘ₘ channelDenote n a C₁ := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  rw [CPTPMap.compose_eq, channelDenote_m_of_bitsOk n a (Circuit.bitsOk_append h₁ h₂),
    channelDenote_m_of_bitsOk n a h₂, channelDenote_m_of_bitsOk n a h₁]
  have hg : (C₁.append C₂).gates = C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits) := rfl
  rw [hg]
  generalize hM : (C₁.append C₂).nBits = M
  rw [Circuit.nBits_append] at hM
  subst hM
  exact sum_krausOps_append n a C₂.nBits C₁.gates C₂.gates h₁ ρ.m

end Kraus

end

end CQRV

end
