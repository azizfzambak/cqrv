module

public import CQRV.Hardware.Decomp
public import CQRV.Circuit.Restoration
public import CQRV.Grover.Lemma

/-!
# CQRV.Hardware.DecompSound

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26a, Track C) — the soundness of the decomposition
table and of the translation, Physlib-side.

* **The embedding is exact up to the recorded phase.** For every unitary IR gate `g` that the
  table covers, and either basis, `decomp_sound`:
  `unitaryDenote n a (expansion b g) = phaseQ (decompTable b g).irPhase • gateU n a g`,
  where `expansion b g` is the entry's basis gates read back into the IR through
  `BasisGate.expand` (`sx = h s h`, `rz a k = p a k`) and `irPhase = phase + Σ embedPhase` is the
  phase of that IR list (the table's own `phase` is the phase of the basis *matrices*, which
  differ from the expansion by the `rz` embedding phases `a/2^(k+1)`; the statement with `phase`
  alone is false — for `h` the expansion `p 1 2; h; s; h; p 1 2` is `e^{+iπ/4} h`, not
  `e^{−iπ/4} h`). Proved per entry on in-range operands through the `mulVec` gate lemmas of
  `Semantics.lean`; for `p` and `cp` parametrically in `a, k`.
* **The global-phase lemma.** A unit scalar on a unitary gate multiplies the Kraus operator of
  every branch by that scalar (inside a conditioned gate only on the branches where the bit is 1):
  `krausOps_expansion`. The channel is unchanged (`channelDenote_eq_of_kraus_smul`).
* **`translate_sound`.** For a well-formed circuit on in-range qubits, the translated circuit
  `translateCircuit b C` is well formed, has the same classical bits, and the same
  `channelDenote`. `AncRestore` and the channel of `groverChannel` transfer (`AncRestore.translate`,
  `groverChannel_translate_chan`, `realizes_translate`).
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV Matrix

noncomputable section

/-! ## Phases as fractions of a turn -/

/-- `e^{2πi q}` for a turn fraction `q`. -/
def phaseQ (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

theorem phaseQ_zero : phaseQ 0 = 1 := by simp [phaseQ]

theorem phaseQ_add (p q : ℚ) : phaseQ (p + q) = phaseQ p * phaseQ q := by
  rw [phaseQ, phaseQ, phaseQ, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseQ_eq_phaseOf (a : ℤ) (k : ℕ) : phaseQ ((a : ℚ) / 2 ^ k) = phaseOf a k := by
  rw [phaseQ, phaseOf]
  congr 1
  push_cast
  ring

theorem star_phaseQ_mul (q : ℚ) : star (phaseQ q) * phaseQ q = 1 := by
  rw [phaseQ, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (q : ℂ)) = -(2 * Real.pi * Complex.I * (q : ℂ)) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    ring
  rw [this, neg_add_cancel, Complex.exp_zero]

theorem phaseQ_mul_star (q : ℚ) : phaseQ q * star (phaseQ q) = 1 := by
  rw [mul_comm, star_phaseQ_mul]

theorem phaseQ_half : phaseQ (1 / 2) = -1 := by
  have := phaseQ_eq_phaseOf 1 1
  simp only [Int.cast_one, pow_one] at this
  rw [this, phaseOf_one_one]

theorem phaseQ_quarter : phaseQ (1 / 4) = Complex.I := by
  have := phaseQ_eq_phaseOf 1 2
  norm_num at this
  rw [this, phaseOf_one_two]

theorem phaseQ_eighth : phaseQ (1 / 8) = ω := by
  have := phaseQ_eq_phaseOf 1 3
  norm_num at this
  rw [this, phaseOf_one_three]

/-- `ω = e^{iπ/4} = (1 + i)/√2`. -/
theorem ω_eq : ω = ((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I) := by
  have h : (Real.pi / 4 : ℂ) * Complex.I = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ω, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have h2 : (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hpos : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    linarith
  rw [h2]
  push_cast
  ring

/-! ## Matrices from their action -/

theorem I_pow_three : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, Complex.I_sq]; ring

theorem Matrix.ext_of_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

section Entries

variable (n a : ℕ)

/-- The expansion of the `h` entry, as an IR list. -/
theorem expansion_h (b : TargetBasis) (q : Qubit) :
    expansion b (.h q) = [.p 1 2 q, .h q, .s q, .h q, .p 1 2 q] := rfl

/-- **`h` entry**: `p 1 2; h; s; h; p 1 2 = ω • h` (the `rz(1/4) sx rz(1/4)` of the table, read
through the embedding; `S H S H S = e^{iπ/4} H`). -/
theorem ud_hEntry {q : Qubit} (hq : q.inRange n a = true) :
    unitaryDenote n a [.p 1 2 q, .h q, .s q, .h q, .p 1 2 q] = ω • gateU n a (.h q) := by
  apply Matrix.ext_of_mulVec
  intro v
  funext i
  have hp : ∀ w : Reg n × Reg a → ℂ, gateU n a (.p 1 2 q) *ᵥ w = fun i => (if q.get i then Complex.I else 1) * w i := by
    intro w; funext i; rw [gateU_p_mulVec, phaseOf_one_two]
  have hs : ∀ w : Reg n × Reg a → ℂ, gateU n a (.s q) *ᵥ w = fun i => (if q.get i then Complex.I else 1) * w i := by
    intro w; funext i; rw [gateU_s, phaseMat_mulVec]
  have hh : ∀ w : Reg n × Reg a → ℂ, gateU n a (.h q) *ᵥ w =
      fun i => ((Real.sqrt 2)⁻¹ : ℂ) * ((if q.get i then -1 else 1) * w i + w (q.flip i)) := by
    intro w; funext i; rw [gateU_h_mulVec n a hq]
  rw [Matrix.smul_mulVec, Pi.smul_apply, hh, smul_eq_mul]
  simp only [unitaryDenote_cons_mulVec, unitaryDenote_nil, Matrix.one_mulVec, hp, hs, hh,
    Qubit.get_flip_self q hq, Qubit.flip_involutive q i]
  rw [ω_eq]
  cases q.get i <;> simp <;> ring_nf <;> simp only [Complex.I_sq, I_pow_three] <;> ring

/-- **`cnot` in the cz basis**: `h(t) cz h(t) = cnot c t`. -/
theorem h_cz_h {c t : Qubit} (hct : c ≠ t) (ht : t.inRange n a = true) :
    gateU n a (.h t) * (gateU n a (.cz c t) * gateU n a (.h t)) = gateU n a (.cnot c t) := by
  apply Matrix.ext_of_mulVec
  intro v
  funext i
  simp only [← Matrix.mulVec_mulVec]
  have hh : ∀ w : Reg n × Reg a → ℂ, gateU n a (.h t) *ᵥ w =
      fun i => ((Real.sqrt 2)⁻¹ : ℂ) * ((if t.get i then -1 else 1) * w i + w (t.flip i)) := by
    intro w; funext i; rw [gateU_h_mulVec n a ht]
  have hz : ∀ w : Reg n × Reg a → ℂ, gateU n a (.cz c t) *ᵥ w =
      fun i => (if c.get i && t.get i then -1 else 1) * w i := by
    intro w; funext i; rw [gateU_cz_mulVec]
  rw [gateU_cnot_mulVec n a hct, hh, hz, hh]
  simp only [Qubit.get_flip_self t ht, Qubit.get_flip_ne hct, Qubit.flip_involutive t i, cnotPerm]
  cases c.get i <;> cases t.get i <;> simp <;>
    first
    | linear_combination (2 * v i) * invSqrtTwo_mul_self
    | linear_combination (2 * v (t.flip i)) * invSqrtTwo_mul_self

/-- **`cz` in the cx basis**: `h(b) cnot(a → b) h(b) = cz a b`. -/
theorem h_cnot_h {p q : Qubit} (hpq : p ≠ q) (hq : q.inRange n a = true) :
    gateU n a (.h q) * (gateU n a (.cnot p q) * gateU n a (.h q)) = gateU n a (.cz p q) := by
  have h1 := h_cz_h n a hpq hq
  have hu := gateU_mem_unitaryGroup n a (.h q)
  -- h h = 1, so conjugating the identity above by h gives the claim
  have hh : gateU n a (.h q) * gateU n a (.h q) = 1 := by
    have h2 := Matrix.mem_unitaryGroup_iff.mp hu
    have hself : star (gateU n a (.h q)) = gateU n a (.h q) := (gateU_adjoint n a (.h q) rfl).symm
    rwa [hself] at h2
  calc gateU n a (.h q) * (gateU n a (.cnot p q) * gateU n a (.h q))
      = gateU n a (.h q) * (gateU n a (.h q) * (gateU n a (.cz p q) * gateU n a (.h q)) * gateU n a (.h q)) := by
        rw [h1]
    _ = (gateU n a (.h q) * gateU n a (.h q)) * gateU n a (.cz p q) * (gateU n a (.h q) * gateU n a (.h q)) := by
        simp only [Matrix.mul_assoc]
    _ = gateU n a (.cz p q) := by rw [hh, Matrix.one_mul, Matrix.mul_one]

/-- The expansion of the `cnot` entry. -/
theorem expansion_cnot_cz (c t : Qubit) :
    expansion .cz (.cnot c t) =
      [.p 1 2 t, .h t, .s t, .h t, .p 1 2 t] ++ [.cz c t] ++ [.p 1 2 t, .h t, .s t, .h t, .p 1 2 t] := rfl

theorem expansion_cnot_cx (c t : Qubit) : expansion .cx (.cnot c t) = [.cnot c t] := rfl

theorem expansion_cz_cz (p q : Qubit) : expansion .cz (.cz p q) = [.cz p q] := rfl

theorem expansion_cz_cx (p q : Qubit) :
    expansion .cx (.cz p q) =
      [.p 1 2 q, .h q, .s q, .h q, .p 1 2 q] ++ [.cnot p q] ++ [.p 1 2 q, .h q, .s q, .h q, .p 1 2 q] := rfl

/-- The `cnot` entry in the cz basis: `i • cnot` (two `h` entries at `ω` each). -/
theorem ud_cnot_cz {c t : Qubit} (hct : c ≠ t) (ht : t.inRange n a = true) :
    unitaryDenote n a (expansion .cz (.cnot c t)) = Complex.I • gateU n a (.cnot c t) := by
  rw [expansion_cnot_cz, unitaryDenote_append, unitaryDenote_append, ud_hEntry n a ht]
  have h1 : unitaryDenote n a [Gate.cz c t] = gateU n a (.cz c t) := by
    simp [unitaryDenote]
  rw [h1, ← h_cz_h n a hct ht, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, ← pow_two, ω_sq]

/-- The `cz` entry in the cx basis: `i • cz`. -/
theorem ud_cz_cx {p q : Qubit} (hpq : p ≠ q) (hq : q.inRange n a = true) :
    unitaryDenote n a (expansion .cx (.cz p q)) = Complex.I • gateU n a (.cz p q) := by
  rw [expansion_cz_cx, unitaryDenote_append, unitaryDenote_append, ud_hEntry n a hq]
  have h1 : unitaryDenote n a [Gate.cnot p q] = gateU n a (.cnot p q) := by
    simp [unitaryDenote]
  rw [h1, ← h_cnot_h n a hpq hq, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, ← pow_two, ω_sq]

/-- The `cnot` entry in either basis, with its phase: `i` in the cz basis, `1` in the cx basis. -/
def cnotScalar : TargetBasis → ℂ
  | .cz => Complex.I
  | .cx => 1

theorem ud_cnotEntry (b : TargetBasis) {c t : Qubit} (hct : c ≠ t) (ht : t.inRange n a = true) :
    unitaryDenote n a ((cnotEntry b c t).gates.flatMap BasisGate.expand) =
      cnotScalar b • gateU n a (.cnot c t) := by
  cases b
  · exact ud_cnot_cz n a hct ht
  · simp [cnotEntry, BasisGate.expand, unitaryDenote, cnotScalar]

/-- The expansion of the `cp` entry: the five pieces. -/
theorem expansion_cp (b : TargetBasis) (m : ℤ) (k : ℕ) (c t : Qubit) :
    expansion b (.cp m k c t) =
      [.p m (k + 1) c] ++ [.p m (k + 1) t] ++ (cnotEntry b c t).gates.flatMap BasisGate.expand ++
        [.p (-m) (k + 1) t] ++ (cnotEntry b c t).gates.flatMap BasisGate.expand := by
  simp [expansion, decompTable, cpEntry, BasisGate.expand, List.flatMap_append]

/-- The `cp` entry: `cnotScalar b ^ 2 • cp` (the five-gate decomposition `decomposeCp_gate`). -/
theorem ud_cp (b : TargetBasis) {c t : Qubit} (hct : c ≠ t) (ht : t.inRange n a = true) (m : ℤ)
    (k : ℕ) :
    unitaryDenote n a (expansion b (.cp m k c t)) = (cnotScalar b * cnotScalar b) • gateU n a (.cp m k c t) := by
  rw [expansion_cp, unitaryDenote_append, unitaryDenote_append, unitaryDenote_append,
    unitaryDenote_append, ud_cnotEntry n a b hct ht]
  have hfive := decomposeCp_gate n a hct ht m k
  simp only [unitaryDenote, Matrix.one_mul, Matrix.mul_assoc] at hfive
  simp only [unitaryDenote, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hfive]

end Entries

/-! ## `decomp_sound` -/

section Sound

variable (n a : ℕ)

theorem irPhase_fixed (q : Qubit) :
    (decompTable .cz (.h q)).irPhase = 1 / 8 ∧ (decompTable .cx (.h q)).irPhase = 1 / 8 ∧
    (decompTable .cz (.s q)).irPhase = 0 ∧ (decompTable .cz (.sdg q)).irPhase = 0 ∧
    (decompTable .cz (.t q)).irPhase = 0 ∧ (decompTable .cz (.tdg q)).irPhase = 0 ∧
    (decompTable .cz (.z q)).irPhase = 0 := by
  simp only [decompTable, Entry.irPhase, hGates, hPhase, BasisGate.embedPhase, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-- The `irPhase` of an entry that is a single `rz a k` with the phase `−a/2^(k+1)` is `0`. -/
theorem irPhase_pEntry (m : ℤ) (k : ℕ) (q : Qubit) : (pEntry m k q).irPhase = 0 := by
  simp [pEntry, Entry.irPhase, BasisGate.embedPhase]

theorem irPhase_cnotEntry (c t : Qubit) :
    (cnotEntry .cz c t).irPhase = 1 / 4 ∧ (cnotEntry .cx c t).irPhase = 0 := by
  simp only [cnotEntry, Entry.irPhase, hGates, hPhase, BasisGate.embedPhase, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num

theorem irPhase_czEntry (p q : Qubit) :
    (czEntry .cz p q).irPhase = 0 ∧ (czEntry .cx p q).irPhase = 1 / 4 := by
  simp only [czEntry, Entry.irPhase, hGates, hPhase, BasisGate.embedPhase, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num

theorem irPhase_cpEntry (b : TargetBasis) (m : ℤ) (k : ℕ) (c t : Qubit) :
    (cpEntry b m k c t).irPhase = 2 * (cnotEntry b c t).irPhase := by
  cases b <;>
    simp only [cpEntry, cnotEntry, Entry.irPhase, hGates, hPhase, BasisGate.embedPhase, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] <;>
    push_cast <;> ring

theorem phaseQ_cnot (b : TargetBasis) (c t : Qubit) :
    phaseQ (cnotEntry b c t).irPhase = cnotScalar b := by
  cases b
  · rw [(irPhase_cnotEntry c t).1, phaseQ_quarter]; rfl
  · rw [(irPhase_cnotEntry c t).2, phaseQ_zero]; rfl

/-- PHASE2_SPEC §C.3 — **`decomp_sound`**: for every unitary IR gate on in-range, distinct operands
and either basis, the expanded entry is the gate up to the phase `irPhase`. -/
theorem decomp_sound (b : TargetBasis) (g : Gate) (hu : g.isUnitary = true)
    (hr : ∀ q ∈ g.qubits, q.inRange n a = true) (hd : g.qubitsOk n = true) :
    unitaryDenote n a (expansion b g) = phaseQ (decompTable b g).irPhase • gateU n a g := by
  cases g with
  | h q =>
    have hq := hr q (by simp [Gate.qubits])
    have hH : unitaryDenote n a (expansion b (.h q)) = ω • gateU n a (.h q) := by
      rw [expansion_h]; exact ud_hEntry n a hq
    rw [hH]
    cases b
    · rw [(irPhase_fixed q).1, phaseQ_eighth]
    · rw [(irPhase_fixed q).2.1, phaseQ_eighth]
  | s q =>
    have : (decompTable b (.s q)).irPhase = 0 := by cases b <;> exact (irPhase_fixed q).2.2.1
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote, gateU_p_one_two]
  | sdg q =>
    have : (decompTable b (.sdg q)).irPhase = 0 := by cases b <;> exact (irPhase_fixed q).2.2.2.1
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote, gateU_p_neg_one_two]
  | t q =>
    have : (decompTable b (.t q)).irPhase = 0 := by cases b <;> exact (irPhase_fixed q).2.2.2.2.1
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote, gateU_p_one_three]
  | tdg q =>
    have : (decompTable b (.tdg q)).irPhase = 0 := by cases b <;> exact (irPhase_fixed q).2.2.2.2.2.1
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote, gateU_p_neg_one_three]
  | z q =>
    have : (decompTable b (.z q)).irPhase = 0 := by cases b <;> exact (irPhase_fixed q).2.2.2.2.2.2
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote, gateU_p_one_one]
  | x q =>
    have : (decompTable b (.x q)).irPhase = 0 := by
      cases b <;> simp [decompTable, Entry.irPhase, BasisGate.embedPhase]
    rw [this, phaseQ_zero, one_smul]
    cases b <;> simp [expansion, decompTable, BasisGate.expand, unitaryDenote]
  | cnot c t =>
    have hct : c ≠ t := by have h := hd; simp [Gate.qubitsOk] at h; exact h.2
    have ht := hr t (by simp [Gate.qubits])
    have h1 : expansion b (.cnot c t) = (cnotEntry b c t).gates.flatMap BasisGate.expand := rfl
    rw [h1, ud_cnotEntry n a b hct ht]
    congr 1
    exact (phaseQ_cnot b c t).symm
  | cz p q =>
    have hpq : p ≠ q := by have h := hd; simp [Gate.qubitsOk] at h; exact h.2
    have hq := hr q (by simp [Gate.qubits])
    cases b
    · rw [(show (decompTable .cz (.cz p q)).irPhase = 0 from (irPhase_czEntry p q).1), phaseQ_zero,
        one_smul, expansion_cz_cz]
      simp [unitaryDenote]
    · rw [(show (decompTable .cx (.cz p q)).irPhase = 1 / 4 from (irPhase_czEntry p q).2), phaseQ_quarter]
      exact ud_cz_cx n a hpq hq
  | p m k q =>
    have : (decompTable b (.p m k q)).irPhase = 0 := irPhase_pEntry m k q
    rw [this, phaseQ_zero, one_smul]
    simp [expansion, decompTable, pEntry, BasisGate.expand, unitaryDenote]
  | cp m k c t =>
    have hct : c ≠ t := by have h := hd; simp [Gate.qubitsOk] at h; exact h.2
    have ht := hr t (by simp [Gate.qubits])
    rw [ud_cp n a b hct ht m k]
    congr 1
    have h2 : (decompTable b (.cp m k c t)).irPhase = (cnotEntry b c t).irPhase + (cnotEntry b c t).irPhase := by
      show (cpEntry b m k c t).irPhase = _
      rw [irPhase_cpEntry]; ring
    rw [h2, phaseQ_add, phaseQ_cnot]
  | measure q j => simp [Gate.isUnitary] at hu
  | ifBit j g => simp [Gate.isUnitary] at hu
  | alloc q =>
    simp [expansion, decompTable, unitaryDenote, Entry.irPhase, phaseQ_zero, gateU]
  | free q =>
    simp [expansion, decompTable, unitaryDenote, Entry.irPhase, phaseQ_zero, gateU]

end Sound

/-! ## The global-phase lemma and the translation -/

section Translate

variable (n a : ℕ)

/-- The expansion of a unitary gate contains only unitary gates. -/
theorem expansion_isUnitary (b : TargetBasis) (g : Gate) (hu : g.isUnitary = true) :
    (expansion b g).all Gate.isUnitary = true := by
  cases g <;> cases b <;>
    simp [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry, BasisGate.expand,
      Gate.isUnitary] at hu ⊢

theorem krausOps_append_list {m : ℕ} (l₁ l₂ : List Gate) (c : Fin m → Bool) :
    krausOps n a m (l₁ ++ l₂) c = krausOps n a m l₂ c * krausOps n a m l₁ c := by
  induction l₁ with
  | nil => simp [krausOps]
  | cons g l ih => simp [krausOps, ih, Matrix.mul_assoc]

/-- The Kraus operator of a conditioned unitary list: the list's unitary when the bit is 1, `1`
otherwise. -/
theorem krausOps_map_ifBit {m : ℕ} (l : List Gate) (hl : l.all Gate.isUnitary = true) (j : ℕ)
    (c : Fin m → Bool) :
    krausOps n a m (l.map (Gate.ifBit j)) c = if bitVal c j then unitaryDenote n a l else 1 := by
  induction l with
  | nil => simp [krausOps, unitaryDenote]
  | cons g l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    simp only [List.map_cons, krausOps, unitaryDenote, ih hl.2, gateK]
    split_ifs <;> simp

/-- The branch scalar of one gate's expansion: the entry's phase for a unitary gate, `1` for a
measurement, and the phase on the branches where the bit is 1 for a conditioned gate. -/
def branchPhase (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) : Gate → ℂ
  | .ifBit j g => if bitVal c j then phaseQ (decompTable b g).irPhase else 1
  | .measure _ _ => 1
  | g => phaseQ (decompTable b g).irPhase

theorem branchPhase_unit (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) (g : Gate) :
    star (branchPhase b c g) * branchPhase b c g = 1 := by
  cases g with
  | ifBit j g' =>
    simp only [branchPhase]
    split_ifs
    · exact star_phaseQ_mul _
    · simp
  | measure q j => simp [branchPhase]
  | _ => simp only [branchPhase]; exact star_phaseQ_mul _

theorem gateK_of_unitary {m : ℕ} (c : Fin m → Bool) (g : Gate) (hu : g.isUnitary = true) :
    gateK n a c g = gateU n a g := by
  cases g <;> simp_all [gateK, Gate.isUnitary]

/-- **The global-phase lemma**: the Kraus operator of a gate's expansion is a unit scalar times
the gate's own, in every branch. -/
theorem qubitsOk_ifBit_of {nD : ℕ} (j : ℕ) (g : Gate) (h : g.qubitsOk nD = true) :
    (Gate.ifBit j g).qubitsOk nD = true := by
  cases g <;> simp_all [Gate.qubitsOk, Gate.qubits]

theorem qubitsOk_of_ifBit {nD : ℕ} {j : ℕ} {g : Gate} (hcl : g.isClifford = true)
    (h : (Gate.ifBit j g).qubitsOk nD = true) : g.qubitsOk nD = true := by
  cases g <;> simp_all [Gate.qubitsOk, Gate.qubits, Gate.isClifford]

theorem isUnitary_of_isClifford (g : Gate) (h : g.isClifford = true) : g.isUnitary = true := by
  cases g <;> simp_all [Gate.isClifford, Gate.isUnitary]

theorem krausOps_expansion (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) (g : Gate)
    (hr : ∀ q ∈ g.qubits, q.inRange n a = true) (hd : g.qubitsOk n = true)
    (hcl : ∀ j g', g = .ifBit j g' → g'.isClifford = true) :
    krausOps n a m (expansion b g) c = branchPhase b c g • gateK n a c g := by
  cases hg : g.isUnitary with
  | true =>
    rw [krausOps_of_unitary n a m _ (expansion_isUnitary b g hg), decomp_sound n a b g hg hr hd,
      gateK_of_unitary n a c g hg]
    cases g <;> simp_all [branchPhase, Gate.isUnitary]
  | false =>
    cases g with
    | measure q j => simp [expansion, decompTable, BasisGate.expand, krausOps, branchPhase, gateK]
    | ifBit j g' =>
      have hu' : g'.isUnitary = true := isUnitary_of_isClifford g' (hcl j g' rfl)
      rw [expansion_ifBit, krausOps_map_ifBit n a _ (expansion_isUnitary b g' hu') j c]
      simp only [branchPhase, gateK]
      have hr' : ∀ q ∈ g'.qubits, q.inRange n a = true := by simpa [Gate.qubits] using hr
      have hd' : g'.qubitsOk n = true := qubitsOk_of_ifBit (hcl j g' rfl) hd
      split_ifs with hb
      · rw [decomp_sound n a b g' hu' hr' hd']
      · simp
    | _ => simp_all [Gate.isUnitary]

/-- The branch scalar of a gate list: the product of its gates' scalars. -/
def translatePhase (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) (gs : List Gate) : ℂ :=
  (gs.map (branchPhase b c)).prod

theorem translatePhase_unit (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) (gs : List Gate) :
    star (translatePhase b c gs) * translatePhase b c gs = 1 := by
  induction gs with
  | nil => simp [translatePhase]
  | cons g gs ih =>
    simp only [translatePhase, List.map_cons, List.prod_cons] at ih ⊢
    calc star (branchPhase b c g * (gs.map (branchPhase b c)).prod) *
          (branchPhase b c g * (gs.map (branchPhase b c)).prod)
        = (star (branchPhase b c g) * branchPhase b c g) *
          (star (gs.map (branchPhase b c)).prod * (gs.map (branchPhase b c)).prod) := by
          rw [star_mul]; ring
      _ = 1 := by rw [branchPhase_unit, ih, one_mul]

/-- The Kraus operators of a translated gate list: a unit scalar times the original's, branch
by branch. -/
theorem krausOps_translate (b : TargetBasis) {m : ℕ} (c : Fin m → Bool) (gs : List Gate)
    (hr : ∀ g ∈ gs, ∀ q ∈ g.qubits, q.inRange n a = true) (hd : ∀ g ∈ gs, g.qubitsOk n = true)
    (hcl : ∀ g ∈ gs, ∀ j g', g = .ifBit j g' → g'.isClifford = true) :
    krausOps n a m (gs.flatMap (expansion b)) c = translatePhase b c gs • krausOps n a m gs c := by
  induction gs with
  | nil => simp [translatePhase, krausOps]
  | cons g gs ih =>
    simp only [List.flatMap_cons, krausOps_append_list, krausOps, translatePhase, List.map_cons,
      List.prod_cons]
    have hr' : ∀ g ∈ gs, ∀ q ∈ g.qubits, q.inRange n a = true := fun g hg => hr g (List.mem_cons_of_mem _ hg)
    have hd' : ∀ g ∈ gs, g.qubitsOk n = true := fun g hg => hd g (List.mem_cons_of_mem _ hg)
    have hcl' : ∀ g ∈ gs, ∀ j g', g = .ifBit j g' → g'.isClifford = true :=
      fun g hg => hcl g (List.mem_cons_of_mem _ hg)
    rw [ih hr' hd' hcl', krausOps_expansion n a b c g (hr g (List.mem_cons_self ..))
      (hd g (List.mem_cons_self ..)) (hcl g (List.mem_cons_self ..))]
    simp only [translatePhase]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

/-! ## Well-formedness of the translation -/

theorem written_map_ifBit (j : ℕ) (l : List Gate) : Circuit.written (l.map (Gate.ifBit j)) = [] := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [Circuit.written, Gate.writes, List.flatMap_cons]

theorem written_expansion (b : TargetBasis) (g : Gate) :
    Circuit.written (expansion b g) = g.writes := by
  cases g with
  | ifBit j g' => rw [expansion_ifBit, written_map_ifBit]; rfl
  | _ => cases b <;> simp [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry,
      BasisGate.expand, Circuit.written, Gate.writes]

theorem written_translate (b : TargetBasis) (gs : List Gate) :
    Circuit.written (gs.flatMap (expansion b)) = Circuit.written gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, written_append_list, written_expansion, ih]
    rfl

theorem nBits_translate (b : TargetBasis) (C : Circuit) :
    (translateCircuit b C).nBits = C.nBits := by
  simp [Circuit.nBits, translateCircuit, written_translate]

/-- The expansion of a Clifford gate with in-range data indices and distinct operands keeps both. -/
theorem qubitsOk_expansion_clifford (b : TargetBasis) {nD : ℕ} (g : Gate) (h : g.qubitsOk nD = true)
    (hcl : g.isClifford = true) : ∀ g' ∈ expansion b g, g'.qubitsOk nD = true := by
  cases g <;> cases b <;> simp_all [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry,
    BasisGate.expand, Gate.qubitsOk, Gate.qubits, Gate.isClifford]

/-- The expansion of a gate with in-range data indices and distinct operands keeps both. -/
theorem qubitsOk_expansion (b : TargetBasis) {nD : ℕ} (g : Gate) (h : g.qubitsOk nD = true)
    (hcl : ∀ j g', g = .ifBit j g' → g'.isClifford = true) :
    ∀ g' ∈ expansion b g, g'.qubitsOk nD = true := by
  cases g with
  | ifBit j g' =>
    intro x hx
    rw [expansion_ifBit] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hc := hcl j g' rfl
    exact qubitsOk_ifBit_of j y (qubitsOk_expansion_clifford b g' (qubitsOk_of_ifBit hc h) hc y hy)
  | _ => cases b <;> simp_all [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry,
      BasisGate.expand, Gate.qubitsOk, Gate.qubits]

/-- The expansion of a Clifford gate is Clifford gate by gate (`p 1 2` is; the `p a (k+1)` of a
Clifford `cp a k` is, since `2^k ∣ 2a` gives `2^(k+1) ∣ 4a`). -/
theorem isClifford_expansion (b : TargetBasis) (g : Gate) (h : g.isClifford = true) :
    ∀ g' ∈ expansion b g, g'.isClifford = true := by
  cases g with
  | cp m k c t =>
    simp only [Gate.isClifford, decide_eq_true_eq] at h
    have h2 : (2 : ℤ) ^ (k + 1) ∣ 4 * m := by
      rw [pow_succ, show (4 : ℤ) * m = 2 * m * 2 by ring]
      exact mul_dvd_mul_right h 2
    cases b <;> simp [expansion, decompTable, cpEntry, cnotEntry, hGates, BasisGate.expand,
      Gate.isClifford, h2]
  | _ => cases b <;> simp_all [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry,
      BasisGate.expand, Gate.isClifford]

theorem bitOk_of_unitary {m : ℕ} (W : List ℕ) (g : Gate) (hu : g.isUnitary = true) :
    g.bitOk m W = true := by
  cases g <;> simp_all [Gate.bitOk, Gate.isUnitary]

theorem bitsOkFrom_of_unitary {m : ℕ} (W : List ℕ) (l : List Gate) (hl : l.all Gate.isUnitary = true) :
    Circuit.bitsOkFrom m W l = true := by
  induction l generalizing W with
  | nil => rfl
  | cons g l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true]
    exact ⟨bitOk_of_unitary W g hl.1, ih _ hl.2⟩

theorem bitsOkFrom_map_ifBit {m : ℕ} (W : List ℕ) (j : ℕ) (l : List Gate)
    (hW : W.contains j = true) (hl : ∀ x ∈ l, x.isClifford = true) :
    Circuit.bitsOkFrom m W (l.map (Gate.ifBit j)) = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, Circuit.bitsOkFrom, Gate.bitOk, Gate.writes, List.append_nil,
      Bool.and_eq_true]
    exact ⟨⟨hW, hl x (List.mem_cons_self ..)⟩, ih fun y hy => hl y (List.mem_cons_of_mem _ hy)⟩

theorem bitsOkFrom_expansion (b : TargetBasis) {m : ℕ} (W : List ℕ) (g : Gate)
    (h : g.bitOk m W = true) : Circuit.bitsOkFrom m W (expansion b g) = true := by
  cases hu : g.isUnitary with
  | true => exact bitsOkFrom_of_unitary W _ (expansion_isUnitary b g hu)
  | false =>
    cases g with
    | measure q j => simpa [expansion, decompTable, BasisGate.expand, Circuit.bitsOkFrom] using h
    | ifBit j g' =>
      simp only [Gate.bitOk, Bool.and_eq_true] at h
      rw [expansion_ifBit]
      exact bitsOkFrom_map_ifBit W j _ h.1 (isClifford_expansion b g' h.2)
    | _ => simp_all [Gate.isUnitary]

theorem bitsOkFrom_translate (b : TargetBasis) {m : ℕ} (W : List ℕ) (gs : List Gate)
    (h : Circuit.bitsOkFrom m W gs = true) :
    Circuit.bitsOkFrom m W (gs.flatMap (expansion b)) = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true] at h
    simp only [List.flatMap_cons, bitsOkFrom_append_list, written_expansion, Bool.and_eq_true]
    exact ⟨bitsOkFrom_expansion b W g h.1, ih _ h.2⟩

/-- Every conditioned gate of a bit-disciplined list controls a Clifford gate. -/
theorem clifford_of_bitsOkFrom {m : ℕ} (W : List ℕ) (gs : List Gate)
    (h : Circuit.bitsOkFrom m W gs = true) :
    ∀ g ∈ gs, ∀ j g', g = .ifBit j g' → g'.isClifford = true := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true] at h
    intro x hx j g' hx'
    rcases List.mem_cons.mp hx with rfl | hx
    · subst hx'
      have h1 := h.1
      simp [Gate.bitOk] at h1
      exact h1.2
    · exact ih _ h.2 x hx j g' hx'

theorem _root_.CQRV.Circuit.WF.qubitsOk {C : Circuit} (h : C.WF) : ∀ g ∈ C.gates, g.qubitsOk C.nData = true := by
  simp only [Circuit.WF, Circuit.wf, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem _root_.CQRV.Circuit.WF.clifford {C : Circuit} (h : C.WF) :
    ∀ g ∈ C.gates, ∀ j g', g = .ifBit j g' → g'.isClifford = true :=
  clifford_of_bitsOkFrom [] C.gates h.bitsOk

/-- PHASE2_SPEC §C.3 — the translation of a well-formed circuit is well formed. -/
theorem translate_wf (b : TargetBasis) (C : Circuit) (h : C.WF) : (translateCircuit b C).WF := by
  have hq := h.qubitsOk
  have hcl := h.clifford
  simp only [Circuit.WF, Circuit.wf, Bool.and_eq_true, List.all_eq_true, translateCircuit,
    Circuit.bitsOk, Circuit.nBits]
  constructor
  · intro g' hg'
    obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hg'
    exact qubitsOk_expansion b g (hq g hg) (hcl g hg) g' hg'
  · rw [written_translate]
    exact bitsOkFrom_translate b [] C.gates h.bitsOk

/-! ## The channel -/

theorem channelDenote_m_gen {C : Circuit} (h : C.bitsOk = true) {m : ℕ} (hm : C.nBits = m)
    (ρ : MState (Reg n × Reg a)) :
    (channelDenote n a C ρ).m =
      ∑ c : Fin m → Bool, krausOps n a m C.gates c * ρ.m * (krausOps n a m C.gates c)ᴴ := by
  subst hm
  exact channelDenote_m_of_bitsOk n a h ρ

/-- **The global-phase lemma for channels**: two well-formed circuits with the same classical bits
whose Kraus operators differ by a unit scalar per branch have the same channel. -/
theorem channelDenote_eq_of_kraus_smul {C C' : Circuit} (hC : C.WF) (hC' : C'.WF)
    (hn : C'.nBits = C.nBits) (Λ : (Fin C.nBits → Bool) → ℂ) (hΛ : ∀ c, star (Λ c) * Λ c = 1)
    (hK : ∀ c, krausOps n a C.nBits C'.gates c = Λ c • krausOps n a C.nBits C.gates c) :
    channelDenote n a C' = channelDenote n a C := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  rw [channelDenote_m_gen n a hC'.bitsOk hn ρ, channelDenote_m_of_bitsOk n a hC.bitsOk ρ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hK c, Matrix.smul_mul, Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.mul_smul, smul_smul,
    mul_comm, hΛ c, one_smul]

/-- PHASE2_SPEC §C.3 — **`translate_sound`**, the channel part: a well-formed circuit on in-range
qubits and its translation have the same channel. -/
theorem translate_channel (b : TargetBasis) (C : Circuit) (hC : C.WF)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n a = true) :
    channelDenote n a (translateCircuit b C) = channelDenote n a C :=
  channelDenote_eq_of_kraus_smul n a hC (translate_wf b C hC) (nBits_translate b C)
    (fun c => translatePhase b c C.gates) (fun c => translatePhase_unit b c C.gates)
    (fun c => krausOps_translate n a b c C.gates hr hd hC.clifford)

/-- PHASE2_SPEC §C.3 — `translate_sound`: well-formed, the same classical bits, the same channel. -/
theorem translate_sound (b : TargetBasis) (C : Circuit) (hC : C.WF)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n a = true) :
    (translateCircuit b C).WF ∧ (translateCircuit b C).nBits = C.nBits ∧
      channelDenote n a (translateCircuit b C) = channelDenote n a C :=
  ⟨translate_wf b C hC, nBits_translate b C, translate_channel n a b C hC hd hr⟩

/-! ## Transfer -/

/-- Report §6.3.2 — `AncRestore` transfers to the translation. -/
theorem AncRestore.translate (b : TargetBasis) {C : Circuit} {U : 𝐔[Reg n]} (hC : C.WF)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n a = true) (h : AncRestore n a C U) :
    AncRestore n a (translateCircuit b C) U := by
  intro ρ
  rw [translate_channel n a b C hC hd hr]
  exact h ρ

end Translate

/-- `groverChannel` with the ancilla count as a parameter (`groverChannel n C = groverChannelAt n C.nAnc C`). -/
def groverChannelAt (n a : ℕ) (C : Circuit) : GradedChannel Unit (Reg n) :=
  GradedChannel.traceAnc
    ⟨channelDenote n a C ∘ₘ CPTPMap.replacement (ancZero n ⊗ᴹ ancZero a), Synthesis.grade C⟩

theorem groverChannel_eq_at (n : ℕ) (C : Circuit) :
    Grover.groverChannel n C = groverChannelAt n C.nAnc C := rfl

theorem groverChannelAt_chan_congr (n a : ℕ) {C C' : Circuit}
    (h : channelDenote n a C' = channelDenote n a C) :
    (groverChannelAt n a C').chan = (groverChannelAt n a C).chan := by
  simp [groverChannelAt, h, GradedChannel.traceAnc]

/-- Report §8.2.1 — the Grover channel of the translation is the Grover channel of the circuit
(the ancilla count of the translation is that of the circuit: the same qubits occur). -/
theorem groverChannel_translate_chan (n : ℕ) (b : TargetBasis) (C : Circuit) (hC : C.WF)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n C.nAnc = true)
    (hanc : (translateCircuit b C).nAnc = C.nAnc) :
    (Grover.groverChannel n (translateCircuit b C)).chan = (Grover.groverChannel n C).chan := by
  rw [groverChannel_eq_at, groverChannel_eq_at, hanc]
  exact groverChannelAt_chan_congr n C.nAnc (translate_channel n C.nAnc b C hC hd hr)

/-- Report §2.1.2 — `Realizes` transfers to the translation, at the translation's own grade. -/
theorem realizes_translate (n : ℕ) (b : TargetBasis) (C : Circuit) (hC : C.WF)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n C.nAnc = true)
    (hanc : (translateCircuit b C).nAnc = C.nAnc)
    {Y : Type} [Fintype Y] [DecidableEq Y] [PseudoMetricSpace Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg n)) (ε δ : ℝ) (r : Grade)
    (h : Realizes S dec (Grover.groverChannel n C) ε δ r) :
    Realizes S dec (Grover.groverChannel n (translateCircuit b C)) ε δ
      (Grover.groverChannel n (translateCircuit b C)).grade := by
  refine ⟨le_rfl, fun x hx => ?_⟩
  rw [groverChannel_translate_chan n b C hC hd hr hanc]
  exact h.2 x hx

end

end CQRV.Hardware
