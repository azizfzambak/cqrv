module

public import CQRV.Circuit.Basis
public import CQRV.Circuit.Restoration
public import CQRV.Circuit.UnitaryChannel
public import CQRV.Realizability.Diamond
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

Stage 18c (STAGE18_TASK.md C1, C4; PHASE2_SPEC.md §A.2 (4)–(5)): the operator-norm bound
`aqft_opNorm_le : ‖U_qft − U_aqft‖ ≤ 2π m / 2^kmax` (`unitaryDenote_filter_sub_le`,
`gateU_cp_sub_one_le`, the geometric tail `tailSum_le`) in the L2 operator norm
`Matrix.Norms.L2Operator`, and the client `aqft_diamond_le : diamondDist (channelDenote (qftCircuit
m)) (channelDenote (aqftCircuit m kmax)) ≤ eta_aqft m kmax = 4π m / 2^kmax` from the channel bridge
(`CQRV.Circuit.UnitaryChannel`) and `diamondDist_ofUnitary_le` (`CQRV.Realizability.Diamond`);
`aqft_adjoint_diamond_le` for the inverse circuits. Import discipline: PHASE2_SPEC.md §A.8 item 6.
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

/-! ## C1. The operator-norm bound (PHASE2_SPEC.md §A.2 (4); Stage 18c, STAGE18_TASK.md C1)

`‖·‖` on matrices is the L2 operator norm `Matrix.Norms.L2Operator`, the instance of Physlib's
`Matrix.traceNorm_mul_le_opNorm_traceNorm` and of `CQRV.Realizability.Diamond`. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

section OpNorm

variable (n a : ℕ)

theorem gateU_norm_le_one (g : Gate) : ‖gateU n a g‖ ≤ 1 :=
  l2_opNorm_le_one_of_mem_unitaryGroup (gateU_mem_unitaryGroup n a g)

theorem unitaryDenote_norm_le_one (gs : List Gate) : ‖unitaryDenote n a gs‖ ≤ 1 :=
  l2_opNorm_le_one_of_mem_unitaryGroup (unitaryDenote_mem_unitaryGroup n a gs)

/-- PHASE2_SPEC.md §A.2 (4) — telescoping over a filtered gate list: dropping the gates `g` with
`keep g = false` changes the unitary semantics by at most `∑ ‖gateU g − 1‖` over the dropped
gates (every gate matrix and every prefix product has norm at most `1`; no unitarity hypothesis
is needed). -/
theorem unitaryDenote_filter_sub_le (gs : List Gate) (keep : Gate → Bool) :
    ‖unitaryDenote n a gs - unitaryDenote n a (gs.filter keep)‖ ≤
      ((gs.filter fun g => !keep g).map fun g => ‖gateU n a g - 1‖).sum := by
  induction gs with
  | nil => simp [unitaryDenote]
  | cons g gs ih =>
    by_cases hg : keep g = true
    · rw [List.filter_cons_of_pos hg, List.filter_cons_of_neg (by simpa using hg)]
      simp only [unitaryDenote]
      rw [← Matrix.sub_mul]
      calc ‖(unitaryDenote n a gs - unitaryDenote n a (gs.filter keep)) * gateU n a g‖
          ≤ ‖unitaryDenote n a gs - unitaryDenote n a (gs.filter keep)‖ * ‖gateU n a g‖ :=
            Matrix.l2_opNorm_mul (unitaryDenote n a gs - unitaryDenote n a (gs.filter keep))
              (gateU n a g)
        _ ≤ ‖unitaryDenote n a gs - unitaryDenote n a (gs.filter keep)‖ * 1 :=
            mul_le_mul_of_nonneg_left (gateU_norm_le_one n a g) (norm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact ih
    · rw [List.filter_cons_of_neg hg, List.filter_cons_of_pos (by simpa using hg)]
      simp only [unitaryDenote, List.map_cons, List.sum_cons]
      have hsplit : unitaryDenote n a gs * gateU n a g - unitaryDenote n a (gs.filter keep) =
          unitaryDenote n a gs * (gateU n a g - 1) +
            (unitaryDenote n a gs - unitaryDenote n a (gs.filter keep)) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [hsplit]
      have hm : ‖unitaryDenote n a gs * (gateU n a g - 1)‖ ≤
          ‖unitaryDenote n a gs‖ * ‖gateU n a g - 1‖ := Matrix.l2_opNorm_mul _ _
      have hm' : ‖unitaryDenote n a gs‖ * ‖gateU n a g - 1‖ ≤ 1 * ‖gateU n a g - 1‖ :=
        mul_le_mul_of_nonneg_right (unitaryDenote_norm_le_one n a gs) (norm_nonneg _)
      have hadd := norm_add_le (unitaryDenote n a gs * (gateU n a g - 1))
        (unitaryDenote n a gs - unitaryDenote n a (gs.filter keep))
      rw [one_mul] at hm'
      linarith

/-- `monoMat id φ` is the diagonal matrix of `φ` (`gateU` of `cz`, `cp`, `p` and the phase
gates). -/
theorem monoMat_id_eq_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → ℂ) :
    monoMat id φ = Matrix.diagonal φ := by
  ext i j
  simp only [monoMat_apply, id, Matrix.diagonal_apply]
  split_ifs with h <;> simp [h]

/-- `‖e^{2πi/2^k} − 1‖ ≤ 2π/2^k` (`Real.norm_exp_I_mul_ofReal_sub_one_le`, Mathlib's
`‖exp (I x) − 1‖ ≤ ‖x‖`). -/
theorem norm_phaseOf_one_sub_one_le (k : ℕ) : ‖phaseOf 1 k - 1‖ ≤ 2 * Real.pi / 2 ^ k := by
  have hx : (0 : ℝ) ≤ 2 * Real.pi / 2 ^ k := by positivity
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi / 2 ^ k)
  rw [Real.norm_eq_abs, abs_of_nonneg hx] at h
  have e : phaseOf 1 k = Complex.exp (Complex.I * ((2 * Real.pi / 2 ^ k : ℝ) : ℂ)) := by
    simp only [phaseOf]
    congr 1
    push_cast
    ring
  rw [e]
  exact h

set_option linter.unusedVariables false in
/-- PHASE2_SPEC.md §A.2 (4) — `‖cp 1 k − 1‖ ≤ 2π/2^k`: `gateU (cp 1 k)` is the diagonal matrix
with entries `1` and `e^{2πi/2^k}` (`l2_opNorm_diagonal`), and `|e^{iφ} − 1| ≤ |φ|`. The bound
holds for `k = 0` as well; `hk` is the hypothesis of the task text (unused, linter silenced). -/
theorem gateU_cp_sub_one_le (k : ℕ) (hk : 1 ≤ k) {c t : Qubit} :
    ‖gateU n a (.cp 1 k c t) - 1‖ ≤ 2 * Real.pi / 2 ^ k := by
  rw [gateU_cp, monoMat_id_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
  split_ifs
  · exact norm_phaseOf_one_sub_one_le k
  · rw [sub_self, norm_zero]
    positivity

end OpNorm

/-! The dropped-gate weight of `aqftGates`: block `j` drops `cp 1 k` for `k = kmax+1 .. m−j`,
`∑ 2π/2^k ≤ 2π/2^kmax` (the geometric tail `tailSum`), `m` blocks. -/

/-- The weight of a gate in the operator-norm bound: `2π/2^k` for a rotation `cp a k`, `0`
otherwise. -/
@[expose] def cpWeight : Gate → ℝ
  | .cp _ k _ _ => 2 * Real.pi / 2 ^ k
  | _ => 0

/-- The keep predicate of `aqftGates m kmax` (its `List.filter`), named. -/
@[expose] def aqftKeep (kmax : ℕ) : Gate → Bool
  | .cp _ k _ _ => decide (k ≤ kmax)
  | _ => true

theorem aqftGates_eq_filter (m kmax : ℕ) :
    aqftGates m kmax = (qftGates m).filter (aqftKeep kmax) := rfl

theorem sum_map_filter_eq {α : Type} (l : List α) (p : α → Bool) (w : α → ℝ) :
    ((l.filter p).map w).sum = (l.map fun x => if p x = true then w x else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filter_cons]
    split_ifs with h <;> simp [h, ih]

theorem sum_map_const_mul {α : Type} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

/-- `tailTerm kmax i = 2^{−(i+2)}` if `kmax < i + 2`, else `0`. -/
@[expose] def tailTerm (kmax i : ℕ) : ℝ := if kmax < i + 2 then ((2 : ℝ) ^ (i + 2))⁻¹ else 0

/-- `tailSum kmax N = ∑_{i < N, kmax < i+2} 2^{−(i+2)}`, the dropped weights of one block over
`2π`. -/
@[expose] def tailSum (kmax N : ℕ) : ℝ := ((List.range N).map (tailTerm kmax)).sum

theorem tailSum_succ (kmax N : ℕ) : tailSum kmax (N + 1) = tailSum kmax N + tailTerm kmax N := by
  simp [tailSum, List.range_succ]

theorem tailSum_eq_zero (kmax : ℕ) : ∀ N, N + 1 ≤ kmax → tailSum kmax N = 0
  | 0, _ => by simp [tailSum]
  | N + 1, h => by
    rw [tailSum_succ, tailSum_eq_zero kmax N (by omega)]
    have h' : ¬ kmax < N + 2 := by omega
    simp [tailTerm, h']

theorem tailSum_add_le (kmax : ℕ) :
    ∀ N, kmax ≤ N + 1 → tailSum kmax N + ((2 : ℝ) ^ (N + 1))⁻¹ ≤ ((2 : ℝ) ^ kmax)⁻¹
  | 0, h => by
    simp only [tailSum, List.range_zero, List.map_nil, List.sum_nil, zero_add]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two h)
  | N + 1, h => by
    rw [tailSum_succ]
    by_cases hk : kmax ≤ N + 1
    · have ih := tailSum_add_le kmax N hk
      have h' : kmax < N + 2 := by omega
      have e : ((2 : ℝ) ^ (N + 1 + 1))⁻¹ + ((2 : ℝ) ^ (N + 1 + 1))⁻¹ = ((2 : ℝ) ^ (N + 1))⁻¹ := by
        rw [pow_succ, mul_inv]
        ring
      simp only [tailTerm, h', ↓reduceIte]
      linarith
    · have hk' : kmax = N + 2 := by omega
      subst hk'
      rw [tailSum_eq_zero _ N (by omega)]
      simp [tailTerm, add_assoc]

/-- The geometric tail: `∑_{i < N, kmax < i+2} 2^{−(i+2)} ≤ 2^{−kmax}`. -/
theorem tailSum_le (kmax N : ℕ) : tailSum kmax N ≤ ((2 : ℝ) ^ kmax)⁻¹ := by
  by_cases h : kmax ≤ N + 1
  · have h1 := tailSum_add_le kmax N h
    have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (N + 1))⁻¹ := by positivity
    linarith
  · rw [tailSum_eq_zero kmax N (by omega)]
    positivity

theorem qftBlock_dropped_weight (m kmax j : ℕ) :
    (((qftBlock m j).filter fun g => !aqftKeep kmax g).map cpWeight).sum =
      2 * Real.pi * tailSum kmax (m - j - 1) := by
  rw [qftBlock, List.filter_cons_of_neg (by simp [aqftKeep]), List.filter_map, List.map_map,
    sum_map_filter_eq, tailSum, ← sum_map_const_mul]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, aqftKeep, cpWeight, tailTerm]
  by_cases h : kmax < i + 2
  · have h' : ¬ i + 2 ≤ kmax := by omega
    simp [h, h', div_eq_mul_inv]
  · have h' : i + 2 ≤ kmax := by omega
    simp [h, h']

theorem qftGates_dropped_weight_le (m kmax : ℕ) :
    (((qftGates m).filter fun g => !aqftKeep kmax g).map cpWeight).sum ≤
      m * (2 * Real.pi / 2 ^ kmax) := by
  have hblock : ∀ j, (((qftBlock m j).filter fun g => !aqftKeep kmax g).map cpWeight).sum ≤
      2 * Real.pi / 2 ^ kmax := by
    intro j
    rw [qftBlock_dropped_weight, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (tailSum_le kmax _) (by positivity)
  have key : ∀ js : List ℕ,
      (((js.flatMap (qftBlock m)).filter fun g => !aqftKeep kmax g).map cpWeight).sum ≤
        js.length * (2 * Real.pi / 2 ^ kmax) := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      rw [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append,
        List.length_cons]
      push_cast
      linarith [hblock j, ih]
  have h := key (List.range m)
  rwa [List.length_range] at h

/-- PHASE2_SPEC.md §A.2 (4) — **the AQFT operator-norm bound**
`‖U_qft − U_aqft‖ ≤ 2π m / 2^kmax`: telescoping (`unitaryDenote_filter_sub_le`), each dropped
`cp 1 k` contributes at most `2π/2^k` (`gateU_cp_sub_one_le`), block `j` drops `k = kmax+1 ..
m−j` with `∑ 2π/2^k ≤ 2π/2^kmax` (`tailSum_le`), `m` blocks. -/
theorem aqft_opNorm_le (m kmax : ℕ) :
    ‖unitaryDenote m 0 (qftGates m) - unitaryDenote m 0 (aqftGates m kmax)‖ ≤
      2 * Real.pi * m / 2 ^ kmax := by
  rw [aqftGates_eq_filter]
  refine (unitaryDenote_filter_sub_le m 0 (qftGates m) (aqftKeep kmax)).trans ?_
  refine (List.sum_le_sum (f := fun g => ‖gateU m 0 g - 1‖) (g := cpWeight) ?_).trans ?_
  · intro g hg
    rw [List.mem_filter] at hg
    obtain ⟨j, _, hgj⟩ := mem_qftGates hg.1
    rcases mem_qftBlock hgj with rfl | ⟨i, _, rfl⟩
    · simp [aqftKeep] at hg
    · exact gateU_cp_sub_one_le m 0 (i + 2) (by omega)
  · refine (qftGates_dropped_weight_le m kmax).trans (le_of_eq ?_)
    ring

/-! ## C4. The client (PHASE2_SPEC.md §A.2 (5); STAGE18_TASK.md C4): the diamond-distance bound
Theorem 3.3b consumes, for the QFT / AQFT circuits and for their inverses (§A.0.1). -/

theorem qftGates_all_unitary (m : ℕ) : (qftGates m).all Gate.isUnitary = true :=
  List.all_eq_true.mpr (qftGates_unitary m)

theorem aqftGates_all_unitary (m kmax : ℕ) : (aqftGates m kmax).all Gate.isUnitary = true :=
  List.all_eq_true.mpr (aqftGates_unitary m kmax)

/-- PHASE2_SPEC.md §A.2 — `η_aqft m kmax = 4π m / 2^kmax`, the diamond-distance budget of the
approximate QFT (`2 · 2π m / 2^kmax`). -/
@[expose] def eta_aqft (m kmax : ℕ) : ℝ := 4 * Real.pi * m / 2 ^ kmax

/-- PHASE2_SPEC.md §A.2 (5) — **the client**: `‖Φ_qft − Φ_aqft‖⋄ ≤ η_aqft m kmax`, from the
channel bridge (`channelDenote_of_unitary`; both circuits are WF and unitary, 18b),
`diamondDist_ofUnitary_le` and `aqft_opNorm_le`. -/
theorem aqft_diamond_le (m kmax : ℕ) :
    diamondDist (channelDenote m 0 (qftCircuit m)) (channelDenote m 0 (aqftCircuit m kmax)) ≤
      eta_aqft m kmax := by
  rw [channelDenote_of_unitary m 0 (qftCircuit_WF m) (qftGates_all_unitary m),
    channelDenote_of_unitary m 0 (aqftCircuit_WF m kmax) (aqftGates_all_unitary m kmax)]
  refine (diamondDist_ofUnitary_le _ _).trans ?_
  have h := aqft_opNorm_le m kmax
  have e : eta_aqft m kmax = 2 * (2 * Real.pi * m / 2 ^ kmax) := by
    unfold eta_aqft
    ring
  rw [e]
  change 2 * ‖unitaryDenote m 0 (qftGates m) - unitaryDenote m 0 (aqftGates m kmax)‖ ≤ _
  linarith

/-! The inverse circuits: `adjointGates` keeps well-formedness and unitarity, and
`unitaryDenote_adjoint` with `‖Aᴴ‖ = ‖A‖` gives the same bound. -/

theorem Gate.isUnitary_adjoint (g : Gate) : g.adjoint.isUnitary = g.isUnitary := by
  cases g <;> rfl

theorem Gate.qubitsOk_adjoint (nD : ℕ) (g : Gate) : g.adjoint.qubitsOk nD = g.qubitsOk nD := by
  cases g <;> rfl

theorem adjointGates_unitary {gs : List Gate} (h : ∀ g ∈ gs, g.isUnitary = true) :
    ∀ g ∈ adjointGates gs, g.isUnitary = true := by
  intro g hg
  rw [adjointGates, List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rw [Gate.isUnitary_adjoint]
  exact h g' hg'

theorem adjointGates_qubitsOk {nD : ℕ} {gs : List Gate} (h : ∀ g ∈ gs, g.qubitsOk nD = true) :
    ∀ g ∈ adjointGates gs, g.qubitsOk nD = true := by
  intro g hg
  rw [adjointGates, List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rw [Gate.qubitsOk_adjoint]
  exact h g' hg'

/-- PHASE2_SPEC.md §A.0.1 — the inverse of a well-formed unitary circuit is well formed. -/
theorem adjointCircuit_WF {C : Circuit} (hWF : C.WF) (hU : ∀ g ∈ C.gates, g.isUnitary = true) :
    (⟨C.nData, adjointGates C.gates⟩ : Circuit).WF := by
  have hq : ∀ g ∈ C.gates, g.qubitsOk C.nData = true := by
    have h := hWF
    simp only [Circuit.WF, Circuit.wf, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1
  simp only [Circuit.WF, Circuit.wf, Circuit.bitsOk, Bool.and_eq_true, List.all_eq_true]
  exact ⟨adjointGates_qubitsOk hq, bitsOkFrom_of_unitary _ _ (adjointGates_unitary hU)⟩

/-- PHASE2_SPEC.md §A.2 (5), §A.0.1 — the same bound for the inverse circuits
`adjointGates (qftGates m)` and `adjointGates (aqftGates m kmax)` (`unitaryDenote_adjoint`,
`l2_opNorm_conjTranspose`). -/
theorem aqft_adjoint_diamond_le (m kmax : ℕ) :
    diamondDist (channelDenote m 0 ⟨m, adjointGates (qftGates m)⟩)
        (channelDenote m 0 ⟨m, adjointGates (aqftGates m kmax)⟩) ≤ eta_aqft m kmax := by
  have h₁ := channelDenote_of_unitary m 0 (C := ⟨m, adjointGates (qftGates m)⟩)
    (adjointCircuit_WF (qftCircuit_WF m) (qftGates_unitary m))
    (List.all_eq_true.mpr (adjointGates_unitary (qftGates_unitary m)))
  have h₂ := channelDenote_of_unitary m 0 (C := ⟨m, adjointGates (aqftGates m kmax)⟩)
    (adjointCircuit_WF (aqftCircuit_WF m kmax) (aqftGates_unitary m kmax))
    (List.all_eq_true.mpr (adjointGates_unitary (aqftGates_unitary m kmax)))
  rw [h₁, h₂]
  refine (diamondDist_ofUnitary_le _ _).trans ?_
  have h := aqft_opNorm_le m kmax
  have e : eta_aqft m kmax = 2 * (2 * Real.pi * m / 2 ^ kmax) := by
    unfold eta_aqft
    ring
  rw [e]
  change 2 * ‖unitaryDenote m 0 (adjointGates (qftGates m)) -
    unitaryDenote m 0 (adjointGates (aqftGates m kmax))‖ ≤ _
  rw [unitaryDenote_adjoint m 0 _ (qftGates_unitary m),
    unitaryDenote_adjoint m 0 _ (aqftGates_unitary m kmax), ← star_sub,
    Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
  linarith

end

end CQRV

end
