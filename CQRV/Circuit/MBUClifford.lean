module

public import CQRV.Circuit.MBUGeneral

/-!
# CQRV.Circuit.MBUClifford

Stage 22b (PHASE2_SPEC §B.1 "The Clifford corollary"; report §6.2.2; Track B) — **the Clifford
corollary, the mathematics**: the correction `O` of `mbu_general` can be chosen Clifford iff `f` has
algebraic degree ≤ 2 over 𝔽₂.

* **L1.** Boolean functions as 𝔽₂-valued forms: `toZ2`, `coord`, `affForm`, `quadForm`, `IsAffine`,
  `IsQuadratic`, the derivative `deriv f i x := f x ⊕ f (flipBit i x)`, and the criterion
  `isQuadratic_iff_deriv_affine : IsQuadratic f ↔ ∀ i, IsAffine (deriv f i)`. The (⇐) direction
  reconstructs the coefficients from the derivatives (`c = f 0`, `a_i` the constant of the `i`-th
  derivative, `b_ij` the `j`-th coefficient of the `i`-th derivative, symmetric by
  `deriv_coeff_symm`) and proves the identity by induction on the support of `x`
  (`Finset.induction_on`, `ind S` the indicator vector of `S`).
* **L2.** The constructive direction: `phaseCircuitQuad a b`, the `Z` gates on the data qubits
  where `a_i = 1` and the `CZ` gates where `b_ij = 1`, is a `PhaseImpl` of every `f` with
  `toZ2 (f x) = quadForm c a b x`, with the global phase `(−1)^c`
  (`phaseCircuitQuad_phaseImpl`); `mbu_quadratic` is the positive half of the corollary as a
  theorem about circuits (`mbu_general_phase_one`).
* **L3.** Clifford for diagonal unitaries: `pauliX i` (the permutation matrix of `flipBit i`),
  `pauliZ b` (`diag((−1)^{⊕ b_i ∧ x_i})`), `IsCliffordDiag D` (every `X_i` is conjugated by `D` to a
  Pauli up to a phase), `conj_pauliX_phaseDiag` (`D X_i Dᴴ = X_i · diag((−1)^{D_i f})`),
  `phaseDiag_eq_smul_pauliZ_iff` (a sign diagonal is a Pauli `Z`-string up to a phase iff its
  function is affine), and `clifford_iff_quadratic : IsCliffordDiag (phaseDiag f) ↔ IsQuadratic f`.

Scalars in vector and matrix statements are written `(-1 : ℂ)` (Stage 22a, DECISIONS 2026-11-15).
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix
open scoped Kronecker

/-! ## L1 — quadratic Boolean functions over 𝔽₂ -/

/-- A Boolean as an element of 𝔽₂. -/
def toZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ2_xor (a b : Bool) : toZ2 (xor a b) = toZ2 a + toZ2 b := by
  cases a <;> cases b <;> decide

theorem toZ2_and (a b : Bool) : toZ2 (a && b) = toZ2 a * toZ2 b := by
  cases a <;> cases b <;> decide

theorem toZ2_eq_one_iff (b : Bool) : toZ2 b = 1 ↔ b = true := by
  cases b <;> decide

theorem decide_toZ2_eq_one (b : Bool) : decide (toZ2 b = 1) = b := by
  cases b <;> decide

/-- Every element of 𝔽₂ is `0` or `1`. -/
theorem zmod2_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s
  decide

theorem toZ2_decide_eq_one (s : ZMod 2) : toZ2 (decide (s = 1)) = s := by
  rcases zmod2_cases s with rfl | rfl <;> decide

theorem zmod2_mul_eq_ite (s v : ZMod 2) : s * v = if s = 1 then v else 0 := by
  rcases zmod2_cases s with rfl | rfl
  · simp [show (0 : ZMod 2) ≠ 1 by decide]
  · simp

/-- `x + x = 0` in 𝔽₂. -/
theorem zmod2_add_self (s : ZMod 2) : s + s = 0 := CharTwo.add_self_eq_zero s

/-- `[c + s = 1] = c ⊕ [s = 1]` in 𝔽₂. -/
theorem decide_toZ2_add (c : Bool) (s : ZMod 2) :
    decide (toZ2 c + s = 1) = xor c (decide (s = 1)) := by
  rcases zmod2_cases s with rfl | rfl <;> cases c <;> decide

/-- The coordinate `x_i` of a basis state, in 𝔽₂. -/
def coord {n : ℕ} (x : Reg n) (i : Fin n) : ZMod 2 := toZ2 (x i)

theorem coord_flipBit {n : ℕ} (k : Fin n) (x : Reg n) (i : Fin n) :
    coord (flipBit k x) i = coord x i + if i = k then 1 else 0 := by
  by_cases h : i = k
  · subst h
    simp only [coord, flipBit, Function.update_self, ↓reduceIte]
    rcases Bool.eq_false_or_eq_true (x i) with hx | hx <;> rw [hx] <;> decide
  · simp [coord, flipBit, h]

/-- The affine form `c + ∑ a_i x_i`. -/
def affForm {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) (x : Reg n) : ZMod 2 :=
  c + ∑ i, a i * coord x i

/-- The quadratic form `c + ∑ a_i x_i + ∑_{i<j} b_ij x_i x_j`. -/
def quadForm {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2) (x : Reg n) :
    ZMod 2 :=
  c + ∑ i, a i * coord x i + ∑ i, ∑ j, if i < j then b i j * coord x i * coord x j else 0

/-- PHASE2_SPEC §B.1 — `g` is affine over 𝔽₂. -/
def IsAffine {n : ℕ} (g : Reg n → Bool) : Prop :=
  ∃ (c : ZMod 2) (a : Fin n → ZMod 2), ∀ x, toZ2 (g x) = affForm c a x

/-- PHASE2_SPEC §B.1 — `f` has algebraic degree ≤ 2 over 𝔽₂. -/
def IsQuadratic {n : ℕ} (f : Reg n → Bool) : Prop :=
  ∃ (c : ZMod 2) (a : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2),
    ∀ x, toZ2 (f x) = quadForm c a b x

instance {n : ℕ} (g : Reg n → Bool) : Decidable (IsAffine g) := by
  unfold IsAffine
  infer_instance

instance {n : ℕ} (f : Reg n → Bool) : Decidable (IsQuadratic f) := by
  unfold IsQuadratic
  infer_instance

/-- PHASE2_SPEC §B.1 — the derivative of `f` in the direction `i`: `f x ⊕ f (x ⊕ e_i)`. -/
def deriv {n : ℕ} (f : Reg n → Bool) (i : Fin n) (x : Reg n) : Bool :=
  xor (f x) (f (flipBit i x))

theorem toZ2_flipBit {n : ℕ} (f : Reg n → Bool) (i : Fin n) (x : Reg n) :
    toZ2 (f (flipBit i x)) = toZ2 (f x) + toZ2 (deriv f i x) := by
  rw [deriv, toZ2_xor, ← add_assoc, zmod2_add_self, zero_add]

theorem sum_mul_coord_flipBit {n : ℕ} (a : Fin n → ZMod 2) (k : Fin n) (x : Reg n) :
    ∑ i, a i * coord (flipBit k x) i = ∑ i, a i * coord x i + a k := by
  simp only [coord_flipBit, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem affForm_flipBit {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) (k : Fin n) (x : Reg n) :
    affForm c a (flipBit k x) = affForm c a x + a k := by
  simp only [affForm, sum_mul_coord_flipBit, add_assoc]

/-- The change of the quadratic form under a flip of the coordinate `k`. -/
theorem quadForm_flipBit {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2)
    (k : Fin n) (x : Reg n) :
    quadForm c a b (flipBit k x) = quadForm c a b x + a k +
      ∑ i, (if i < k then b i k * coord x i else 0) +
      ∑ j, (if k < j then b k j * coord x j else 0) := by
  have hterm : ∀ i j, (if i < j then b i j * coord (flipBit k x) i * coord (flipBit k x) j else 0) =
      (if i < j then b i j * coord x i * coord x j else 0) +
        (if j = k then (if i < k then b i k * coord x i else 0) else 0) +
        (if i = k then (if k < j then b k j * coord x j else 0) else 0) := by
    intro i j
    rw [coord_flipBit, coord_flipBit]
    by_cases hik : i = k
    · subst hik
      by_cases hjk : j = i
      · subst hjk
        simp
      · simp only [hjk, ↓reduceIte, add_zero]
        split_ifs <;> ring
    · by_cases hjk : j = k
      · subst hjk
        simp only [hik, ↓reduceIte, add_zero]
        split_ifs <;> ring
      · simp [hik, hjk]
  simp only [quadForm, hterm, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, sum_mul_coord_flipBit]
  ring

/-- The indicator vector of a set of coordinates. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Reg n := fun i => decide (i ∈ S)

theorem ind_empty {n : ℕ} : (ind (∅ : Finset (Fin n))) = fun _ => false := by
  funext i
  simp [ind]

theorem ind_insert {n : ℕ} (k : Fin n) (S : Finset (Fin n)) (hk : k ∉ S) :
    ind (insert k S) = flipBit k (ind S) := by
  funext i
  simp only [ind, flipBit, Function.update_apply, Finset.mem_insert]
  by_cases h : i = k
  · subst h
    simp [hk]
  · simp [h]

theorem ind_filter {n : ℕ} (x : Reg n) : ind (Finset.univ.filter fun i => x i = true) = x := by
  funext i
  simp [ind]

theorem coord_ind {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    coord (ind S) i = if i ∈ S then 1 else 0 := by
  by_cases h : i ∈ S <;> simp [coord, ind, toZ2, h]

theorem affForm_ind_empty {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) : affForm c a (ind ∅) = c := by
  simp [affForm, coord_ind]

theorem affForm_ind_singleton {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2) (i : Fin n) :
    affForm c a (ind {i}) = c + a i := by
  simp [affForm, coord_ind, Finset.mem_singleton, Finset.sum_ite_eq']

theorem quadForm_ind_empty {n : ℕ} (c : ZMod 2) (a : Fin n → ZMod 2)
    (b : Fin n → Fin n → ZMod 2) : quadForm c a b (ind ∅) = c := by
  simp [quadForm, coord_ind]

theorem flipBit_ind_empty {n : ℕ} (i : Fin n) : flipBit i (ind (∅ : Finset (Fin n))) = ind {i} := by
  rw [← ind_insert i ∅ (Finset.notMem_empty i), Finset.insert_empty]

theorem flipBit_ind_singleton {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    flipBit i (ind {j}) = ind {i, j} :=
  (ind_insert i {j} (by simp [h])).symm

/-- The mixed coefficients of the derivatives are symmetric: the `j`-th coefficient of the `i`-th
derivative equals the `i`-th coefficient of the `j`-th. -/
theorem deriv_coeff_symm {n : ℕ} (f : Reg n → Bool) (cd : Fin n → ZMod 2)
    (ad : Fin n → Fin n → ZMod 2)
    (hd : ∀ i x, toZ2 (deriv f i x) = affForm (cd i) (ad i) x) (i j : Fin n) :
    ad i j = ad j i := by
  by_cases hij : i = j
  · subst hij; rfl
  have h1 := hd i (ind {j})
  have h2 := hd i (ind ∅)
  have h3 := hd j (ind {i})
  have h4 := hd j (ind ∅)
  rw [affForm_ind_singleton, deriv, toZ2_xor, flipBit_ind_singleton hij] at h1
  rw [affForm_ind_empty, deriv, toZ2_xor, flipBit_ind_empty] at h2
  rw [affForm_ind_singleton, deriv, toZ2_xor, flipBit_ind_singleton (Ne.symm hij),
    Finset.pair_comm] at h3
  rw [affForm_ind_empty, deriv, toZ2_xor, flipBit_ind_empty] at h4
  have h5 : (2 : ZMod 2) = 0 := by decide
  linear_combination -h1 + h2 + h3 - h4 + (toZ2 (f (ind {j})) - toZ2 (f (ind {i}))) * h5

/-- PHASE2_SPEC §B.1 — **the derivative criterion**: `f` is quadratic iff every derivative is
affine. (⇒) is a computation (`quadForm_flipBit`); (⇐) reconstructs the coefficients from the
derivatives and proves the identity by induction on the support of `x`. -/
theorem isQuadratic_iff_deriv_affine {n : ℕ} (f : Reg n → Bool) :
    IsQuadratic f ↔ ∀ i, IsAffine (deriv f i) := by
  constructor
  · rintro ⟨c, a, b, hf⟩ i
    refine ⟨a i, fun j => if j < i then b j i else if i < j then b i j else 0, fun x => ?_⟩
    have h := toZ2_flipBit f i x
    rw [hf, hf, quadForm_flipBit] at h
    have hsum : ∑ j, (if j < i then b j i else if i < j then b i j else 0) * coord x j =
        ∑ j, (if j < i then b j i * coord x j else 0) +
          ∑ j, (if i < j then b i j * coord x j else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy j i with hji | hji | hji
      · simp [hji, not_lt.mpr hji.le]
      · subst hji
        simp
      · simp [hji, not_lt.mpr hji.le]
    rw [affForm, hsum]
    linear_combination -h
  · intro h
    choose cd ad hd using h
    have hsym := deriv_coeff_symm f cd ad hd
    have key : ∀ S : Finset (Fin n),
        toZ2 (f (ind S)) = quadForm (toZ2 (f (ind ∅))) cd (fun i j => ad i j) (ind S) := by
      intro S
      induction S using Finset.induction_on with
      | empty => rw [quadForm_ind_empty]
      | insert k S hk ih =>
        rw [ind_insert k S hk, toZ2_flipBit, ih, hd k, quadForm_flipBit, affForm]
        have hyk : coord (ind S) k = 0 := by simp [coord_ind, hk]
        have hsum : ∑ i, ad k i * coord (ind S) i =
            ∑ i, (if i < k then ad i k * coord (ind S) i else 0) +
              ∑ j, (if k < j then ad k j * coord (ind S) j else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases lt_trichotomy i k with hik | hik | hik
          · simp [hik, not_lt.mpr hik.le, hsym k i]
          · subst hik
            simp [hyk]
          · simp [hik, not_lt.mpr hik.le]
        rw [hsum]
        ring
    refine ⟨toZ2 (f (ind ∅)), cd, fun i j => ad i j, fun x => ?_⟩
    rw [← ind_filter x]
    exact key _

/-! ## L2 — the constructive direction -/

/-- The indices with a linear coefficient. -/
def zIdx {n : ℕ} (a : Fin n → ZMod 2) : List (Fin n) := (List.finRange n).filter fun i => a i = 1

/-- The pairs `i < j` with a quadratic coefficient. -/
def czPairs {n : ℕ} (b : Fin n → Fin n → ZMod 2) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j ∧ b i j = 1).map fun j => (i, j)

/-- PHASE2_SPEC §B.1 — the phase circuit of a quadratic form: `Z` on `x[i]` where `a_i = 1`, `CZ`
on `(x[i], x[j])` where `i < j` and `b_ij = 1`. -/
def phaseCircuitQuad {n : ℕ} (a : Fin n → ZMod 2) (b : Fin n → Fin n → ZMod 2) : List Gate :=
  ((zIdx a).map fun i : Fin n => Gate.z (.data i.val)) ++
    ((czPairs b).map fun p : Fin n × Fin n => Gate.cz (.data p.1.val) (.data p.2.val))

/-- `phaseDiag` of the constant `false` is the identity. -/
theorem phaseDiag_false {n : ℕ} : phaseDiag (fun _ : Reg n => false) = 1 := by
  simp [phaseDiag, Matrix.diagonal_one]

theorem phaseDiag_decide_zero {n : ℕ} :
    phaseDiag (fun _ : Reg n => decide ((0 : ZMod 2) = 1)) = 1 := by
  rw [show (fun _ : Reg n => decide ((0 : ZMod 2) = 1)) = fun _ => false from by
    funext; decide, phaseDiag_false]

/-- The unitary of a list of `Z` gates on data qubits: the sign of the parity of the listed bits. -/
theorem unitaryDenote_zList {n a : ℕ} (l : List (Fin n)) :
    unitaryDenote n a (l.map fun i : Fin n => Gate.z (.data i.val)) =
      phaseDiag (fun x => decide ((l.map fun i => coord x i).sum = 1)) ⊗ₖ
        (1 : Matrix (Reg a) (Reg a) ℂ) := by
  induction l with
  | nil =>
    simp only [List.map_nil, unitaryDenote_nil, List.sum_nil]
    rw [phaseDiag_decide_zero, Matrix.one_kronecker_one]
  | cons i l ih =>
    rw [List.map_cons, unitaryDenote, ih, gateU_z_data n a i.val i.isLt, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, phaseDiag_mul]
    congr 1
    congr 1
    funext x
    simp only [List.map_cons, List.sum_cons, Fin.eta]
    rw [coord, decide_toZ2_add, Bool.xor_comm]

/-- The unitary of a list of `CZ` gates on data-qubit pairs: the sign of the parity of the listed
products. -/
theorem unitaryDenote_czList {n a : ℕ} (l : List (Fin n × Fin n)) :
    unitaryDenote n a (l.map fun p : Fin n × Fin n => Gate.cz (.data p.1.val) (.data p.2.val)) =
      phaseDiag (fun x => decide ((l.map fun p => coord x p.1 * coord x p.2).sum = 1)) ⊗ₖ
        (1 : Matrix (Reg a) (Reg a) ℂ) := by
  induction l with
  | nil =>
    simp only [List.map_nil, unitaryDenote_nil, List.sum_nil]
    rw [phaseDiag_decide_zero, Matrix.one_kronecker_one]
  | cons p l ih =>
    rw [List.map_cons, unitaryDenote, ih, gateU_cz_data n a p.1.val p.2.val p.1.isLt p.2.isLt,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, phaseDiag_mul]
    congr 1
    congr 1
    funext x
    simp only [List.map_cons, List.sum_cons, Fin.eta]
    rw [coord, coord, ← toZ2_and, decide_toZ2_add, Bool.xor_comm]

theorem list_sum_map_filter {α : Type} (l : List α) (p : α → Bool) (g : α → ZMod 2) :
    ((l.filter p).map g).sum = (l.map fun i => if p i then g i else 0).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, ih]
    · rw [ih, zero_add]

theorem list_sum_map_flatMap {α β : Type} (l : List α) (F : α → List β) (g : β → ZMod 2) :
    ((l.flatMap F).map g).sum = (l.map fun i => ((F i).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- The parity computed by the `Z` gates of `phaseCircuitQuad` is `∑ a_i x_i`. -/
theorem zList_sum {n : ℕ} (a : Fin n → ZMod 2) (x : Reg n) :
    ((zIdx a).map fun i => coord x i).sum = ∑ i, a i * coord x i := by
  rw [zIdx, list_sum_map_filter, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zmod2_mul_eq_ite]
  simp

/-- The parity computed by the `CZ` gates of `phaseCircuitQuad` is `∑_{i<j} b_ij x_i x_j`. -/
theorem czList_sum {n : ℕ} (b : Fin n → Fin n → ZMod 2) (x : Reg n) :
    ((czPairs b).map fun p => coord x p.1 * coord x p.2).sum =
      ∑ i, ∑ j, if i < j then b i j * coord x i * coord x j else 0 := by
  rw [czPairs, list_sum_map_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.map_map, list_sum_map_filter, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  by_cases hij : i < j
  · rcases zmod2_cases (b i j) with h | h <;> simp [hij, h]
  · simp [hij]

/-- The sign diagonal of `c ⊕ g` is `(−1)^c` times that of `g`. -/
theorem phaseDiag_xor_const {n : ℕ} (c : Bool) (g : Reg n → Bool) :
    phaseDiag (fun x => xor c (g x)) = (if c then (-1 : ℂ) else 1) • phaseDiag g := by
  ext x y
  simp only [phaseDiag, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : x = y
  · subst h
    cases c <;> by_cases hg : g x = true <;> simp [hg]
  · simp [h]

/-- PHASE2_SPEC §B.1 — **the constructive direction**: `phaseCircuitQuad a b` is a phase
implementation of every `f` with `toZ2 (f x) = quadForm c a b x`, with the global phase `(−1)^c`. -/
theorem phaseCircuitQuad_phaseImpl {n a' : ℕ} {f : Reg n → Bool} {c : ZMod 2} {a : Fin n → ZMod 2}
    {b : Fin n → Fin n → ZMod 2} (hf : ∀ x, toZ2 (f x) = quadForm c a b x) :
    PhaseImpl n a' (phaseCircuitQuad a b) f where
  unitary := by
    rw [List.all_eq_true]
    intro g hg
    simp only [phaseCircuitQuad, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rfl
  dataOnly := by
    rw [List.all_eq_true]
    intro g hg
    simp only [phaseCircuitQuad, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rfl
  phase := by
    refine ⟨if decide (c = 1) then -1 else 1, by split_ifs <;> simp, ?_⟩
    rw [phaseCircuitQuad, unitaryDenote_append, unitaryDenote_zList, unitaryDenote_czList,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, phaseDiag_mul, ← Matrix.smul_kronecker,
      ← phaseDiag_xor_const]
    congr 1
    congr 1
    funext x
    have hx : f x = decide (toZ2 (f x) = 1) := (decide_toZ2_eq_one (f x)).symm
    rw [hx, hf, quadForm, zList_sum, czList_sum]
    rcases zmod2_cases c with hc | hc <;>
    rcases zmod2_cases (∑ i, a i * coord x i) with h1 | h1 <;>
    rcases zmod2_cases (∑ i, ∑ j, if i < j then b i j * coord x i * coord x j else 0) with h2 | h2 <;>
      rw [hc, h1, h2] <;> decide

/-- PHASE2_SPEC §B.1 — **MBU for quadratic functions**: for every quadratic `f` (with the
coefficients `c, a, b`) and every phase-exact compute block for `f`, the circuit "compute; `Z t`;
`mbuUncompute` with `phaseCircuitQuad a b`" restores its ancilla and applies `phaseOracle f`. The
positive half of the Clifford corollary as a theorem about circuits. -/
theorem mbu_quadratic {n a' : ℕ} {C : Circuit} (hWF : C.WF) {B : List Gate} {t : Qubit} {j : ℕ}
    {c : ZMod 2} {a : Fin n → ZMod 2} {b : Fin n → Fin n → ZMod 2}
    (hgates : C.gates = B ++ [.z t] ++ mbuUncompute t j (phaseCircuitQuad a b))
    (hanc : ∃ i, i < a' ∧ t = .anc i) {f : Reg n → Bool}
    (hf : ∀ x, toZ2 (f x) = quadForm c a b x) (hB : ComputesInto n a' B t f fun _ => 1) :
    AncRestore n a' C (phaseOracle f) :=
  mbu_general_phase_one hWF hgates hanc hB (phaseCircuitQuad_phaseImpl hf)

/-! ## L3 — Clifford for diagonal unitaries -/

/-- The Pauli `X` on the data qubit `i`: the permutation matrix of `flipBit i`. -/
def pauliX {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ := monoMat (flipBit i) fun _ => 1

/-- The parity `⊕_i b_i ∧ x_i` of the bits selected by `b`. -/
def linPred {n : ℕ} (b : Fin n → Bool) (x : Reg n) : Bool :=
  decide (∑ i, toZ2 (b i) * coord x i = 1)

/-- The Pauli `Z`-string of the bits selected by `b`: `diag((−1)^{⊕ b_i ∧ x_i})`. -/
def pauliZ {n : ℕ} (b : Fin n → Bool) : Matrix (Reg n) (Reg n) ℂ := phaseDiag (linPred b)

/-- PHASE2_SPEC §B.1 — **the Clifford condition for a diagonal unitary** `D`: every `X_i` is
conjugated by `D` to a Pauli up to a phase, `D X_i Dᴴ = λ · X_i Z_b`. A diagonal `D` commutes with
every `Z`-type Pauli, so the `X_i` are the only generators to check; and `D X_i Dᴴ` is `X_i` times
a diagonal, so the Pauli it can equal is an `X_i Z_b`. -/
def IsCliffordDiag {n : ℕ} (D : Matrix (Reg n) (Reg n) ℂ) : Prop :=
  ∀ i, ∃ (lam : ℂ) (b : Fin n → Bool), ‖lam‖ = 1 ∧ D * pauliX i * Dᴴ = lam • (pauliX i * pauliZ b)

theorem phaseDiag_eq_monoMat {n : ℕ} (f : Reg n → Bool) :
    phaseDiag f = monoMat id fun x => if f x then (-1 : ℂ) else 1 := by
  ext x y
  simp only [phaseDiag, Matrix.diagonal_apply, monoMat_apply, id]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

theorem pauliX_mul_self {n : ℕ} (i : Fin n) : pauliX i * pauliX i = 1 := by
  rw [pauliX, monoMat_mul, (flipBit_involutive i).comp_self]
  simpa using monoMat_id_one (ι := Reg n)

theorem pauliX_mul_left_cancel {n : ℕ} (i : Fin n) {A B : Matrix (Reg n) (Reg n) ℂ}
    (h : pauliX i * A = pauliX i * B) : A = B := by
  have := congrArg (fun M => pauliX i * M) h
  simpa only [← Matrix.mul_assoc, pauliX_mul_self, Matrix.one_mul] using this

/-- PHASE2_SPEC §B.1 — conjugating `X_i` by the sign diagonal of `f` leaves `X_i` times the sign
diagonal of the derivative `D_i f`. -/
theorem conj_pauliX_phaseDiag {n : ℕ} (f : Reg n → Bool) (i : Fin n) :
    phaseDiag f * pauliX i * (phaseDiag f)ᴴ = pauliX i * phaseDiag (deriv f i) := by
  rw [← Matrix.star_eq_conjTranspose, phaseDiag_eq_monoMat, pauliX, star_monoMat (fun _ => rfl),
    monoMat_mul, monoMat_mul, phaseDiag_eq_monoMat, monoMat_mul]
  congr 1
  funext j
  simp only [id, deriv, one_mul, mul_one]
  by_cases h1 : f j = true <;> by_cases h2 : f (flipBit i j) = true <;> simp [h1, h2]

theorem linPred_ind_empty {n : ℕ} (b : Fin n → Bool) : linPred b (ind ∅) = false := by
  simp [linPred, coord_ind]

/-- The sign of a Boolean, injective. -/
theorem sign_injective {a b : Bool} (h : (if a then (-1 : ℂ) else 1) = if b then -1 else 1) :
    a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by norm_num)

/-- PHASE2_SPEC §B.1 — a sign diagonal is a Pauli `Z`-string up to a phase iff its function is
affine. -/
theorem phaseDiag_eq_smul_pauliZ_iff {n : ℕ} (g : Reg n → Bool) :
    (∃ (lam : ℂ) (b : Fin n → Bool), phaseDiag g = lam • pauliZ b) ↔ IsAffine g := by
  constructor
  · rintro ⟨lam, b, h⟩
    have hent : ∀ x, (if g x then (-1 : ℂ) else 1) = lam * if linPred b x then -1 else 1 := by
      intro x
      have := congrFun (congrFun h x) x
      simpa [phaseDiag, pauliZ, Matrix.diagonal_apply] using this
    have hlam : lam = if g (ind ∅) then -1 else 1 := by
      have := hent (ind ∅)
      rw [linPred_ind_empty] at this
      simpa using this.symm
    refine ⟨toZ2 (g (ind ∅)), fun i => toZ2 (b i), fun x => ?_⟩
    have hx : g x = xor (g (ind ∅)) (linPred b x) := by
      apply sign_injective
      rw [hent x, hlam]
      by_cases h0 : g (ind ∅) = true <;> by_cases hl : linPred b x = true <;> simp [h0, hl]
    rw [hx, toZ2_xor, affForm, linPred, toZ2_decide_eq_one]
  · rintro ⟨c, a, h⟩
    refine ⟨if decide (c = 1) then -1 else 1, fun i => decide (a i = 1), ?_⟩
    rw [pauliZ, ← phaseDiag_xor_const]
    congr 1
    funext x
    have hx : g x = decide (toZ2 (g x) = 1) := (decide_toZ2_eq_one (g x)).symm
    rw [hx, h, affForm, linPred]
    simp only [toZ2_decide_eq_one]
    rcases zmod2_cases c with hc | hc <;>
    rcases zmod2_cases (∑ i, a i * coord x i) with hs | hs <;> rw [hc, hs] <;> decide

theorem norm_eq_one_of_phaseDiag_eq_smul {n : ℕ} {g : Reg n → Bool} {lam : ℂ} {b : Fin n → Bool}
    (h : phaseDiag g = lam • pauliZ b) : ‖lam‖ = 1 := by
  have := congrFun (congrFun h (ind ∅)) (ind ∅)
  simp only [phaseDiag, pauliZ, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul,
    linPred_ind_empty, Bool.false_eq_true, ↓reduceIte, mul_one] at this
  rw [← this]
  by_cases h0 : g (ind ∅) = true <;> simp [h0]

/-- PHASE2_SPEC §B.1 — **the Clifford corollary**: the sign diagonal of `f` is Clifford iff `f`
is quadratic over 𝔽₂. Through `conj_pauliX_phaseDiag`, `phaseDiag_eq_smul_pauliZ_iff` and the
derivative criterion. -/
theorem clifford_iff_quadratic {n : ℕ} (f : Reg n → Bool) :
    IsCliffordDiag (phaseDiag f) ↔ IsQuadratic f := by
  unfold IsCliffordDiag
  rw [isQuadratic_iff_deriv_affine]
  refine forall_congr' fun i => ?_
  rw [← phaseDiag_eq_smul_pauliZ_iff]
  simp only [conj_pauliX_phaseDiag]
  constructor
  · rintro ⟨lam, b, -, h⟩
    refine ⟨lam, b, pauliX_mul_left_cancel i ?_⟩
    rw [h, Matrix.mul_smul]
  · rintro ⟨lam, b, h⟩
    exact ⟨lam, b, norm_eq_one_of_phaseDiag_eq_smul h, by rw [h, Matrix.mul_smul]⟩

end CQRV

end

end
