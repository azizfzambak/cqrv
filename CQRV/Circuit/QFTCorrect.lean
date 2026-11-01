module

public import CQRV.Circuit.Basis
public import CQRV.Circuit.Restoration
public import CQRV.Synthesis.QFT

/-!
# CQRV.Circuit.QFTCorrect

PHASE2_SPEC.md §A.2 (Stage 18b, docs/tasks/STAGE18_TASK.md B3) — the QFT circuit computes the
Fourier transform, pointwise on the circuit's own register `Reg m × Reg 0`:

```
qft_basis : (unitaryDenote m 0 (qftGates m) *ᵥ basisVec (x, reg0)) (s, reg0) =
  (√2)⁻¹ ^ m · exp (2πi · x.toNat · (bitRev s).toNat / 2^m)
```

the textbook output without the final swaps (`(bitRev s).toNat = s.toNatLE`; the swaps are
absorbed by the decoding map of §A.4). Proof by the block invariant: after blocks `0 .. j−1` the
state is `⊗_{i<j} (|0⟩ + e^{2πi φ_i} |1⟩)/√2 ⊗ |x_j … x_{m−1}⟩` with `φ_i = qftPhase m i x =
(x.toNat mod 2^{m−i}) / 2^{m−i}` (`prefixAmp`, `qft_prefix`), block `j` gate by gate (`h_step`
with `gateU_h_mulVec`, `cps_step` with `gateU_cp_mulVec`, `midAmp`), the phase of one block
(`exp_phase_block`) and the arithmetic identity `exp_sum_phases` (the two exponents differ by the
integer `∑_i [s_i] ⌊x.toNat / 2^{m−i}⌋`). Corollaries: `qft_unitary`, `aqft_eq_qft_of_le`.
Every statement is indexed by `ℕ` through `Reg.bit` (= `Qubit.get (.data l)`).

Also here (B1): `qftCircuit_WF`, `aqftCircuit_WF`, `qftGates_unitary`, `aqftGates_unitary` —
`Circuit.WF` and `Gate.isUnitary` are defined in `CQRV.Circuit.Semantics`, and
`CQRV.Synthesis.QFT` stays in the Physlib-free closure of the synthesizer (see its header).
-/

public section

namespace CQRV

open CQRV.Synthesis Matrix

/-! ## Well-formedness and unitarity (PHASE2_SPEC.md §A.2, B1; `Circuit.WF` and `Gate.isUnitary`
live in `CQRV.Circuit.Semantics`, which is why these are not in `CQRV.Synthesis.QFT`) -/

theorem qftGates_unitary (m : ℕ) : ∀ g ∈ qftGates m, g.isUnitary = true := by
  intro g hg
  obtain ⟨j, _, hgj⟩ := mem_qftGates hg
  rcases mem_qftBlock hgj with rfl | ⟨i, _, rfl⟩ <;> rfl

theorem aqftGates_unitary (m kmax : ℕ) : ∀ g ∈ aqftGates m kmax, g.isUnitary = true :=
  fun g hg => qftGates_unitary m g (mem_aqftGates hg)

/-- A measurement-free gate list satisfies the classical-bit discipline for every prefix `W`. -/
theorem bitsOkFrom_of_unitary (n : ℕ) (W : List ℕ) {gs : List Gate}
    (h : ∀ g ∈ gs, g.isUnitary = true) : Circuit.bitsOkFrom n W gs = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.isUnitary = true := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true]
    refine ⟨?_, ih _ hgs⟩
    cases g <;> simp_all [Gate.bitOk, Gate.isUnitary]

theorem qftBlock_qubitsOk {m j : ℕ} (hj : j < m) {g : Gate} (hg : g ∈ qftBlock m j) :
    g.qubitsOk m = true := by
  rcases mem_qftBlock hg with rfl | ⟨i, hi, rfl⟩
  · simp [Gate.qubitsOk, Gate.qubits, hj]
  · simp only [Gate.qubitsOk, Gate.qubits, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Qubit.data.injEq]
    omega

theorem qftGates_qubitsOk {m : ℕ} {g : Gate} (hg : g ∈ qftGates m) : g.qubitsOk m = true := by
  obtain ⟨j, hj, hgj⟩ := mem_qftGates hg
  exact qftBlock_qubitsOk hj hgj

/-- PHASE2_SPEC.md §A.2 — the QFT circuit is well-formed (report §9.1.1). -/
theorem qftCircuit_WF (m : ℕ) : (qftCircuit m).WF := by
  show (qftCircuit m).wf = true
  rw [Circuit.wf, Circuit.bitsOk, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun g hg => qftGates_qubitsOk hg, bitsOkFrom_of_unitary _ _ (qftGates_unitary m)⟩

/-- PHASE2_SPEC.md §A.2 — the approximate QFT circuit is well-formed. -/
theorem aqftCircuit_WF (m kmax : ℕ) : (aqftCircuit m kmax).WF := by
  show (aqftCircuit m kmax).wf = true
  rw [Circuit.wf, Circuit.bitsOk, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun g hg => qftGates_qubitsOk (mem_aqftGates hg),
    bitsOkFrom_of_unitary _ _ (aqftGates_unitary m kmax)⟩

/-! ## Size -/

theorem qftGates_prefix_length (m : ℕ) : ∀ k ≤ m,
    ((List.range k).flatMap (qftBlock m)).length = ∑ j ∈ Finset.range k, (m - j) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega),
      Finset.sum_range_succ, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      qftBlock_length (by omega)]

/-- PHASE2_SPEC.md §A.2 — the QFT has `m (m + 1) / 2` gates (`m` Hadamards and
`m (m − 1) / 2` rotations). -/
theorem qftGates_length (m : ℕ) : (qftGates m).length = m * (m + 1) / 2 := by
  rw [qftGates, qftGates_prefix_length m m le_rfl]
  have h1 : ∑ j ∈ Finset.range m, (m - j) = ∑ j ∈ Finset.range m, (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => j + 1) m]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h2 := Finset.sum_range_id_mul_two m
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  cases m with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel] at h2
    nlinarith [h2]

noncomputable section

/-- PHASE2_SPEC.md §A.2 — the binary fraction `0.x_j x_{j+1} … x_{m−1}` written by block `j`:
`φ m j x = (x.toNat mod 2^{m−j}) / 2^{m−j}`. -/
def qftPhase (m j : ℕ) (x : Reg m) : ℝ := ((x.toNat % 2 ^ (m - j) : ℕ) : ℝ) / 2 ^ (m - j)

/-- `exp (2πi · qftPhase m j x)`, the relative phase of qubit `j` in the output. -/
def qftExp (m j : ℕ) (x : Reg m) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (qftPhase m j x : ℂ))

/-- The bits `j ≤ l` of the data register of `p` agree with `x`. -/
def agreesFrom (m j : ℕ) (x : Reg m) (p : Reg m × Reg 0) : Prop :=
  ∀ l, j ≤ l → p.1.bit l = x.bit l

/-- The output phases of the finished qubits `i < j`. -/
def phaseProd (m j : ℕ) (x s : Reg m) : ℂ :=
  ∏ i ∈ Finset.range m, (if i < j ∧ s.bit i then qftExp m i x else 1)

open Classical in
/-- The amplitude of the state after blocks `0 .. j−1`. -/
def prefixAmp (m j : ℕ) (x : Reg m) (p : Reg m × Reg 0) : ℂ :=
  if agreesFrom m j x p then ((Real.sqrt 2)⁻¹ : ℂ) ^ j * phaseProd m j x p.1 else 0

open Classical in
/-- The amplitude of the state inside block `j`, after its `H` and its first `r` rotations. -/
def midAmp (m j r : ℕ) (x : Reg m) (p : Reg m × Reg 0) : ℂ :=
  if agreesFrom m (j + 1) x p then
    ((Real.sqrt 2)⁻¹ : ℂ) ^ (j + 1) * phaseProd m j x p.1 *
      (if p.1.bit j then
        (if x.bit j then (-1 : ℂ) else 1) *
          ∏ i ∈ Finset.range r, (if x.bit (j + i + 1) then phaseOf 1 (i + 2) else 1)
      else 1)
  else 0

/-! ## Arithmetic of the phases -/

/-- The binary fraction of block `j` as a sum of the selected powers `2^{−(i+1)}`. -/
theorem qftPhase_eq_sum {m j : ℕ} (x : Reg m) (hj : j ≤ m) :
    qftPhase m j x = ∑ i ∈ Finset.range (m - j),
      (if x.bit (j + i) then (1 : ℝ) / 2 ^ (i + 1) else 0) := by
  unfold qftPhase
  rw [Reg.toNat_mod_eq_sum_Ico x hj, Finset.sum_Ico_eq_sum_range, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h2 : (2 : ℝ) ^ (m - j) = 2 ^ (m - 1 - (j + i)) * 2 ^ (i + 1) := by
    rw [← pow_add]; congr 1; omega
  split_ifs
  · rw [Nat.cast_pow, Nat.cast_ofNat, h2]
    field_simp
  · simp

/-- PHASE2_SPEC.md §A.2 — the phase written by block `j`: the `H` sign and the `m − j − 1`
rotations multiply to `exp (2πi · φ m j x)`. -/
theorem exp_phase_block {m j : ℕ} (x : Reg m) (hj : j < m) :
    (if x.bit j then (-1 : ℂ) else 1) *
        ∏ i ∈ Finset.range (m - j - 1), (if x.bit (j + i + 1) then phaseOf 1 (i + 2) else 1) =
      qftExp m j x := by
  have hsign : (if x.bit j then (-1 : ℂ) else 1) =
      Complex.exp (2 * Real.pi * Complex.I * (if x.bit j then (1 : ℂ) / 2 else 0)) := by
    split_ifs
    · rw [← Complex.exp_pi_mul_I]; congr 1; ring
    · simp
  have hfac : ∀ i, (if x.bit (j + i + 1) then phaseOf 1 (i + 2) else 1) =
      Complex.exp (2 * Real.pi * Complex.I *
        (if x.bit (j + i + 1) then (1 : ℂ) / 2 ^ (i + 2) else 0)) := by
    intro i
    split_ifs
    · simp only [phaseOf, Int.cast_one]; congr 1; ring
    · simp
  rw [hsign, Finset.prod_congr rfl (fun i _ => hfac i), ← Complex.exp_sum, ← Complex.exp_add,
    qftExp]
  congr 1
  rw [← Finset.mul_sum, ← mul_add]
  congr 1
  rw [qftPhase_eq_sum x (le_of_lt hj)]
  have hmj : m - j = (m - j - 1) + 1 := by omega
  rw [hmj, Finset.sum_range_succ', Complex.ofReal_add, Complex.ofReal_sum, add_comm]
  congr 1
  all_goals first
    | (apply Finset.sum_congr rfl
       intro i _
       have : j + (i + 1) = j + i + 1 := by omega
       rw [this]
       split_ifs <;> simp)
    | (simp only [Nat.add_zero, zero_add, pow_one]
       split_ifs <;> simp)

/-- PHASE2_SPEC.md §A.2 — the arithmetic identity behind `qft_basis`: the output phases sum to
`x.toNat · s.toNatLE / 2^m` up to the integer `∑_i [s_i] ⌊x.toNat / 2^{m−i}⌋` (pure arithmetic
on binary fractions). -/
theorem exp_sum_phases (m : ℕ) (x s : Reg m) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((∑ i ∈ Finset.range m, (if s.bit i then qftPhase m i x else 0) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.toNat * s.toNatLE : ℕ) : ℂ) / 2 ^ m) := by
  -- the real identity, term by term
  have hterm : ∀ i ∈ Finset.range m, (if s.bit i then qftPhase m i x else 0) =
      (if s.bit i then (x.toNat : ℝ) * 2 ^ i / 2 ^ m else 0) -
        (if s.bit i then ((x.toNat / 2 ^ (m - i) : ℕ) : ℝ) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs
    · unfold qftPhase
      have hdm := Nat.div_add_mod x.toNat (2 ^ (m - i))
      have h2 : (2 : ℝ) ^ m = 2 ^ (m - i) * 2 ^ i := by rw [← pow_add]; congr 1; omega
      have hcast : ((x.toNat % 2 ^ (m - i) : ℕ) : ℝ) =
          (x.toNat : ℝ) - 2 ^ (m - i) * ((x.toNat / 2 ^ (m - i) : ℕ) : ℝ) := by
        have := congrArg (fun n : ℕ => (n : ℝ)) hdm
        push_cast at this
        linarith
      rw [hcast, h2]
      field_simp
    · simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  set K : ℕ := ∑ i ∈ Finset.range m, (if s.bit i then x.toNat / 2 ^ (m - i) else 0) with hK
  have hKcast : (∑ i ∈ Finset.range m,
      (if s.bit i then ((x.toNat / 2 ^ (m - i) : ℕ) : ℝ) else 0)) = (K : ℝ) := by
    rw [hK, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hT : (∑ i ∈ Finset.range m, (if s.bit i then (x.toNat : ℝ) * 2 ^ i / 2 ^ m else 0)) =
      ((x.toNat * s.toNatLE : ℕ) : ℝ) / 2 ^ m := by
    rw [Reg.toNatLE_eq_sum_range, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hKcast, hT, Complex.ofReal_sub, mul_sub, Complex.exp_sub, Complex.ofReal_natCast,
    mul_comm _ (K : ℂ), Complex.exp_nat_mul_two_pi_mul_I, div_one]
  congr 1
  push_cast
  ring

/-! ## The register bits under `H` and `cp` -/

theorem inRange_data {m j : ℕ} (hj : j < m) : (Qubit.data j).inRange m 0 = true := by
  simp [Qubit.inRange, hj]

theorem bit_flip_self {m j : ℕ} (hj : j < m) (p : Reg m × Reg 0) :
    ((Qubit.data j).flip p).1.bit j = !p.1.bit j :=
  Qubit.get_flip_self (Qubit.data j) (inRange_data hj) p

theorem bit_flip_ne {m j l : ℕ} (hl : l ≠ j) (p : Reg m × Reg 0) :
    ((Qubit.data j).flip p).1.bit l = p.1.bit l :=
  Qubit.get_flip_ne (p := Qubit.data l) (q := Qubit.data j) (by simpa using hl) p

theorem agreesFrom_succ_iff {m j : ℕ} (x : Reg m) (p : Reg m × Reg 0) :
    agreesFrom m j x p ↔ agreesFrom m (j + 1) x p ∧ p.1.bit j = x.bit j := by
  constructor
  · intro h
    exact ⟨fun l hl => h l (by omega), h j le_rfl⟩
  · rintro ⟨h, hj⟩ l hl
    rcases Nat.eq_or_lt_of_le hl with rfl | hlt
    · exact hj
    · exact h l hlt

theorem agreesFrom_flip_iff {m j : ℕ} (x : Reg m) (p : Reg m × Reg 0) :
    agreesFrom m (j + 1) x ((Qubit.data j).flip p) ↔ agreesFrom m (j + 1) x p := by
  unfold agreesFrom
  constructor
  · intro h l hl
    have := h l hl
    rwa [bit_flip_ne (by omega)] at this
  · intro h l hl
    rw [bit_flip_ne (by omega)]
    exact h l hl

theorem phaseProd_flip {m j : ℕ} (x : Reg m) (p : Reg m × Reg 0) :
    phaseProd m j x ((Qubit.data j).flip p).1 = phaseProd m j x p.1 := by
  unfold phaseProd
  apply Finset.prod_congr rfl
  intro i _
  by_cases hij : i < j
  · rw [bit_flip_ne (by omega)]
  · simp [hij]

theorem agreesFrom_zero_iff {m : ℕ} (x : Reg m) (p : Reg m × Reg 0) :
    agreesFrom m 0 x p ↔ p = (x, reg0) := by
  constructor
  · intro h
    exact Prod.ext (Reg.ext_bit fun l => h l (Nat.zero_le l)) (reg0_unique _)
  · rintro rfl l _
    rfl

theorem phaseProd_zero {m : ℕ} (x s : Reg m) : phaseProd m 0 x s = 1 :=
  Finset.prod_eq_one fun i _ => by simp

/-- `phaseProd` grows by the factor of qubit `j`. -/
theorem phaseProd_succ {m j : ℕ} (hj : j < m) (x s : Reg m) :
    phaseProd m (j + 1) x s = phaseProd m j x s * (if s.bit j then qftExp m j x else 1) := by
  unfold phaseProd
  have hpt : ∀ i, (if i < j + 1 ∧ s.bit i then qftExp m i x else 1) =
      (if i < j ∧ s.bit i then qftExp m i x else 1) *
        (if i = j ∧ s.bit i then qftExp m i x else 1) := by
    intro i
    by_cases hb : s.bit i = true <;> by_cases hlt : i < j <;> by_cases heq : i = j <;>
      simp [hb, hlt, heq] <;> omega
  rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

/-! ## The block invariant -/

theorem qft_prefix_zero (m : ℕ) (x : Reg m) :
    unitaryDenote m 0 [] *ᵥ basisVec (x, reg0) = prefixAmp m 0 x := by
  rw [unitaryDenote_nil, one_mulVec]
  funext p
  unfold prefixAmp basisVec
  by_cases hp : p = (x, reg0)
  · subst hp
    have hA := (agreesFrom_zero_iff x (x, reg0)).mpr rfl
    simp [hA, phaseProd_zero]
  · have hA : ¬ agreesFrom m 0 x p := fun h => hp ((agreesFrom_zero_iff x p).mp h)
    simp only [hp, hA, ↓reduceIte]

/-- The `H` of block `j` on the prefix state. -/
theorem h_step {m j : ℕ} (hj : j < m) (x : Reg m) :
    gateU m 0 (.h (.data j)) *ᵥ prefixAmp m j x = midAmp m j 0 x := by
  funext p
  rw [gateU_h_mulVec m 0 (inRange_data hj)]
  unfold prefixAmp midAmp
  have hget : (Qubit.data j).get p = p.1.bit j := rfl
  rw [hget, Finset.range_zero, Finset.prod_empty, mul_one]
  by_cases hA : agreesFrom m (j + 1) x p
  · have hAf : agreesFrom m (j + 1) x ((Qubit.data j).flip p) := (agreesFrom_flip_iff x p).mpr hA
    rw [phaseProd_flip]
    by_cases hb : p.1.bit j = x.bit j
    · have h1 : agreesFrom m j x p := (agreesFrom_succ_iff x p).mpr ⟨hA, hb⟩
      have h2 : ¬ agreesFrom m j x ((Qubit.data j).flip p) := by
        rw [agreesFrom_succ_iff, bit_flip_self hj]
        rintro ⟨-, h⟩
        rw [← hb] at h
        exact absurd h (by cases p.1.bit j <;> simp)
      simp only [hA, h1, h2, ↓reduceIte]
      rw [add_zero, ← hb, pow_succ]
      cases p.1.bit j <;> simp <;> ring
    · have h1 : ¬ agreesFrom m j x p := fun h => hb ((agreesFrom_succ_iff x p).mp h).2
      have h2 : agreesFrom m j x ((Qubit.data j).flip p) := by
        rw [agreesFrom_succ_iff, bit_flip_self hj]
        refine ⟨hAf, ?_⟩
        cases hpj : p.1.bit j <;> cases hxj : x.bit j <;> simp_all
      simp only [hA, h1, h2, ↓reduceIte]
      rw [mul_zero, zero_add, pow_succ]
      cases hpj : p.1.bit j <;> cases hxj : x.bit j <;> simp_all <;> ring
  · have h1 : ¬ agreesFrom m j x p := fun h => hA ((agreesFrom_succ_iff x p).mp h).1
    have h2 : ¬ agreesFrom m j x ((Qubit.data j).flip p) := fun h =>
      hA ((agreesFrom_flip_iff x p).mp ((agreesFrom_succ_iff x _).mp h).1)
    simp only [hA, h1, h2, ↓reduceIte]
    simp

/-- The first `r` rotations of block `j` on the mid-block state. -/
theorem cps_step {m j : ℕ} (x : Reg m) (r : ℕ) :
    unitaryDenote m 0 ((List.range r).map fun i => Gate.cp 1 (i + 2) (.data (j + i + 1)) (.data j))
        *ᵥ midAmp m j 0 x = midAmp m j r x := by
  induction r with
  | zero => rw [List.range_zero, List.map_nil, unitaryDenote_nil, one_mulVec]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, unitaryDenote_append,
      ← Matrix.mulVec_mulVec, ih, unitaryDenote_cons_mulVec, unitaryDenote_nil, one_mulVec]
    funext p
    rw [gateU_cp_mulVec]
    unfold midAmp
    by_cases hA : agreesFrom m (j + 1) x p
    · simp only [hA, ↓reduceIte]
      have hget : (Qubit.data (j + r + 1)).get p = x.bit (j + r + 1) := hA _ (by omega)
      have hgetj : (Qubit.data j).get p = p.1.bit j := rfl
      rw [hget, hgetj, Finset.prod_range_succ]
      cases p.1.bit j
      · simp
      · simp only [Bool.and_true, ↓reduceIte]
        split_ifs <;> ring
    · simp only [hA, ↓reduceIte, mul_zero]

/-- The state at the end of block `j` is the prefix state of block `j + 1`. -/
theorem midAmp_last {m j : ℕ} (hj : j < m) (x : Reg m) :
    midAmp m j (m - j - 1) x = prefixAmp m (j + 1) x := by
  funext p
  unfold midAmp prefixAmp
  by_cases hA : agreesFrom m (j + 1) x p
  · simp only [hA, ↓reduceIte]
    rw [exp_phase_block x hj, phaseProd_succ hj, mul_assoc]
  · simp only [hA, ↓reduceIte]

/-- Block `j` of the QFT on the prefix state. -/
theorem block_step {m j : ℕ} (hj : j < m) (x : Reg m) :
    unitaryDenote m 0 (qftBlock m j) *ᵥ prefixAmp m j x = prefixAmp m (j + 1) x := by
  rw [qftBlock, unitaryDenote_cons_mulVec, h_step hj, cps_step x (m - j - 1), midAmp_last hj]

/-- PHASE2_SPEC.md §A.2 — the block invariant: after blocks `0 .. j−1` the state on input
`|x⟩` is `prefixAmp m j x`. -/
theorem qft_prefix (m : ℕ) (x : Reg m) : ∀ j ≤ m,
    unitaryDenote m 0 ((List.range j).flatMap (qftBlock m)) *ᵥ basisVec (x, reg0) =
      prefixAmp m j x := by
  intro j hj
  induction j with
  | zero => rw [List.range_zero, List.flatMap_nil, qft_prefix_zero]
  | succ j ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, unitaryDenote_append, ← Matrix.mulVec_mulVec, ih (by omega),
      block_step (by omega)]

/-! ## The theorem -/

theorem agreesFrom_self (m : ℕ) (x s : Reg m) : agreesFrom m m x (s, reg0) := fun l hl => by
  simp [Reg.bit_of_le _ hl]

theorem phaseProd_full (m : ℕ) (x s : Reg m) :
    phaseProd m m x s = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ i ∈ Finset.range m, (if s.bit i then qftPhase m i x else 0) : ℝ) : ℂ)) := by
  unfold phaseProd
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [hi, true_and, qftExp]
  split_ifs <;> simp

/-- PHASE2_SPEC.md §A.2 — the QFT on a basis state, pointwise: the amplitude of output `s` is
`2^{−m/2} · exp (2πi · x · bitrev(s) / 2^m)` (the textbook output without the final swaps). -/
theorem qft_basis (m : ℕ) (x s : Reg m) :
    (unitaryDenote m 0 (qftGates m) *ᵥ basisVec (x, reg0)) (s, reg0) =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * ((x.toNat * (bitRev s).toNat : ℕ) : ℂ) / 2 ^ m) := by
  rw [qftGates, qft_prefix m x m le_rfl]
  simp only [prefixAmp, agreesFrom_self, ↓reduceIte]
  congr 1
  rw [phaseProd_full, Reg.toNat_bitRev]
  exact exp_sum_phases m x s

/-- PHASE2_SPEC.md §A.2 — the QFT circuit is unitary (`unitaryDenote_mem_unitaryGroup`). -/
theorem qft_unitary (m : ℕ) :
    unitaryDenote m 0 (qftGates m) ∈ Matrix.unitaryGroup (Reg m × Reg 0) ℂ :=
  unitaryDenote_mem_unitaryGroup m 0 (qftGates m)

/-- PHASE2_SPEC.md §A.2 — with `kmax ≥ m` the approximate QFT is the QFT. -/
theorem aqft_eq_qft_of_le {m kmax : ℕ} (h : m ≤ kmax) :
    unitaryDenote m 0 (aqftGates m kmax) = unitaryDenote m 0 (qftGates m) := by
  rw [aqftGates_eq_self h]

end

end CQRV

end
