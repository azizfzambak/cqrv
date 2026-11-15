module

public import CQRV.Hardware.Relabel
public import CQRV.Hardware.DecompSound
public import CQRV.Circuit.RestoreAlgebra

/-!
# CQRV.Hardware.Route

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 step 2 (Stage 26b1, Track C) — routing, Physlib-side:
relabeling the qubits of a circuit conjugates its channel by the induced permutation of basis
states; the routing SWAP is such a permutation; the table's SWAP entry is sound; the logical
register embeds into the compact physical register.

**One theorem for every renaming.** A qubit map `f` together with an equivalence of basis states
`E : Reg N × Reg A ≃ Reg n × Reg a` that intertwines `get` and `flip` on the gate's qubits
(`f q` reads on `u` what `q` reads on `E u`, and flipping `f q` then applying `E` is applying `E`
then flipping `q`) gives `gateU_map : gateU N A (g.map f) = (gateU n a g).submatrix E E`, hence
`krausOps_map` and `channelDenote_map`: `channelDenote N A (C.map f) (ρ.relabel E) =
(channelDenote n a C ρ).relabel E`. The permutation of the data qubits (`Qubit.relabel N σ`,
`stateEquiv σ`, `permMat σ`) and the canonical placement (`Qubit.place n`, `placeEquiv`) are the
two instances; the embedding of the logical register into the physical one composes 23a's
widening (`wide`, |0⟩ on the idle qubits) with the placement and a permutation.

`ud_swapEntry`: the expansion of the table's `swap` entry is `phaseQ irPhase • permMat (swap p q)`
in both bases (`i³ = −i` turns in the cz basis, `0` in the cx basis).
-/

@[expose] public section

open CQRV Matrix

namespace CQRV.Hardware

noncomputable section

/-! ## Monomial and Hadamard matrices under a reindexing -/

section Reindex

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

theorem monoMat_submatrix (σ : ι → ι) (φ : ι → ℂ) (E : κ ≃ ι) :
    (monoMat σ φ).submatrix E E = monoMat (E.symm ∘ σ ∘ E) (φ ∘ E) := by
  ext u v
  simp only [Matrix.submatrix_apply, monoMat_apply, Function.comp_apply]
  have : (E u = σ (E v)) ↔ (u = E.symm (σ (E v))) := by
    constructor
    · intro h; rw [← h, Equiv.symm_apply_apply]
    · intro h; rw [h, Equiv.apply_symm_apply]
  simp only [this]

theorem hMat_submatrix (b : ι → Bool) (f : ι → ι) (E : κ ≃ ι) :
    (hMat b f).submatrix E E = hMat (b ∘ E) (E.symm ∘ f ∘ E) := by
  ext u v
  simp only [hMat, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.add_apply, monoMat_apply,
    Function.comp_apply, id]
  have : (E u = f (E v)) ↔ (u = E.symm (f (E v))) := by
    constructor
    · intro h; rw [← h, Equiv.symm_apply_apply]
    · intro h; rw [h, Equiv.apply_symm_apply]
  simp only [this, Equiv.apply_eq_iff_eq]

/-- A monomial matrix of a bijection with unit phases is unitary (the involutive case is
`monoMat_mem_unitaryGroup`). -/
theorem star_monoMat_equiv (e : ι ≃ ι) (φ : ι → ℂ) :
    star (monoMat e φ) = monoMat e.symm (fun j => star (φ (e.symm j))) := by
  ext i j
  simp only [Matrix.star_apply, monoMat_apply]
  by_cases h : j = e i
  · subst h; simp
  · have h' : ¬ i = e.symm j := fun h' => h (by rw [h', Equiv.apply_symm_apply])
    simp [h, h']

theorem monoMat_equiv_mem_unitaryGroup [Fintype ι] (e : ι ≃ ι) {φ : ι → ℂ}
    (hφ : ∀ j, star (φ j) * φ j = 1) : monoMat e φ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_monoMat_equiv, monoMat_mul]
  convert (monoMat_id_one (ι := ι)) using 2
  · funext j; simp
  · funext j
    simp only [Equiv.symm_apply_apply]
    exact hφ j

omit [DecidableEq κ] in
theorem mul_monoMat_equiv [Fintype ι] (M : Matrix κ ι ℂ) (e : ι ≃ ι) :
    M * monoMat e (fun _ => 1) = M.submatrix id e := by
  ext u v
  simp only [Matrix.mul_apply, monoMat_apply, mul_ite, mul_one, mul_zero, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (e v)]
  · simp
  · intro k _ hk; simp [hk]
  · simp

omit [DecidableEq κ] in
theorem monoMat_equiv_mul [Fintype ι] (e : ι ≃ ι) (M : Matrix ι κ ℂ) :
    monoMat e (fun _ => 1) * M = M.submatrix e.symm id := by
  ext u v
  simp only [Matrix.mul_apply, monoMat_apply, ite_mul, one_mul, zero_mul, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (e.symm u)]
  · simp
  · intro k _ hk
    have : ¬ u = e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · simp

/-- Conjugation by the permutation matrix of `e⁻¹` reindexes by `e`. -/
theorem monoMat_equiv_conj [Fintype ι] (e : ι ≃ ι) (M : Matrix ι ι ℂ) :
    monoMat e.symm (fun _ => 1) * M * (monoMat e.symm (fun _ => 1))ᴴ = M.submatrix e e := by
  rw [← Matrix.star_eq_conjTranspose, star_monoMat_equiv, Equiv.symm_symm]
  simp only [star_one]
  rw [Matrix.mul_assoc, mul_monoMat_equiv, monoMat_equiv_mul, Equiv.symm_symm]
  rfl

end Reindex

/-! ## The gate matrices under a qubit map with an intertwining state equivalence -/

section GateMap

variable {n a N A : ℕ}

/-- `f` and `E` intertwine on the qubits of `g`: `f q` reads on `u` what `q` reads on `E u`;
flipping `f q` commutes with `E`; `f q` is in range; `f` is injective on the gate's qubits. -/
structure Intertwines (f : Qubit → Qubit) (E : Reg N × Reg A ≃ Reg n × Reg a) (g : Gate) : Prop where
  get : ∀ q ∈ g.qubits, ∀ u, (f q).get u = q.get (E u)
  flip : ∀ q ∈ g.qubits, ∀ u, E ((f q).flip u) = q.flip (E u)
  range : ∀ q ∈ g.qubits, (f q).inRange N A = q.inRange n a
  inj : ∀ q ∈ g.qubits, ∀ q' ∈ g.qubits, f q = f q' → q = q'

variable {f : Qubit → Qubit} {E : Reg N × Reg A ≃ Reg n × Reg a}

theorem Intertwines.flip' {g : Gate} (h : Intertwines f E g) {q : Qubit} (hq : q ∈ g.qubits) (u) :
    (f q).flip u = E.symm (q.flip (E u)) := by
  rw [← h.flip q hq u, Equiv.symm_apply_apply]

theorem Intertwines.cnotPerm {g : Gate} (h : Intertwines f E g) {c t : Qubit} (hc : c ∈ g.qubits)
    (ht : t ∈ g.qubits) :
    cnotPerm N A (f c) (f t) = E.symm ∘ cnotPerm n a c t ∘ E := by
  funext u
  simp only [CQRV.cnotPerm, Function.comp_apply, h.get c hc u]
  split_ifs
  · exact h.flip' ht u
  · rw [Equiv.symm_apply_apply]

theorem Intertwines.ifBit {j : ℕ} {g : Gate} (h : Intertwines f E (.ifBit j g)) : Intertwines f E g :=
  ⟨fun q hq => h.get q (by simpa [Gate.qubits] using hq), fun q hq => h.flip q (by simpa [Gate.qubits] using hq),
   fun q hq => h.range q (by simpa [Gate.qubits] using hq),
   fun q hq q' hq' => h.inj q (by simpa [Gate.qubits] using hq) q' (by simpa [Gate.qubits] using hq')⟩

/-- **The gate matrices under a renaming**: `gateU N A (g.map f) = (gateU n a g).submatrix E E`. -/
theorem gateU_map (g : Gate) (h : Intertwines f E g) :
    gateU N A (g.map f) = (gateU n a g).submatrix E E := by
  have hmono : ∀ (q : Qubit), q ∈ g.qubits → ∀ (p : ℂ),
      phaseMat N A (f q) p = (phaseMat n a q p).submatrix E E := fun q hq p => by
    rw [phaseMat, phaseMat, monoMat_submatrix]
    congr 1
    · funext u; simp
    · funext u; simp [h.get q hq u]
  cases g with
  | h q =>
    have hq : q ∈ (Gate.h q).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateU, h.range q hq]
    split_ifs
    · rw [hMat_submatrix]
      congr 1
      · funext u; exact h.get q hq u
      · funext u; exact h.flip' hq u
    · rw [Matrix.submatrix_one_equiv]
  | s q => exact hmono q (by simp [Gate.qubits]) _
  | sdg q => exact hmono q (by simp [Gate.qubits]) _
  | t q => exact hmono q (by simp [Gate.qubits]) _
  | tdg q => exact hmono q (by simp [Gate.qubits]) _
  | z q => exact hmono q (by simp [Gate.qubits]) _
  | p m k q => exact hmono q (by simp [Gate.qubits]) _
  | x q =>
    have hq : q ∈ (Gate.x q).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateU]
    rw [monoMat_submatrix]
    congr 1
    funext u
    exact h.flip' hq u
  | cnot c t =>
    have hc : c ∈ (Gate.cnot c t).qubits := by simp [Gate.qubits]
    have ht : t ∈ (Gate.cnot c t).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateU]
    by_cases hct : c = t
    · subst hct; simp [Matrix.submatrix_one_equiv]
    · have hct' : ¬ f c = f t := fun h' => hct (h.inj c hc t ht h')
      simp only [hct, hct', ↓reduceIte]
      rw [monoMat_submatrix, h.cnotPerm hc ht]
      rfl
  | cz c t =>
    have hc : c ∈ (Gate.cz c t).qubits := by simp [Gate.qubits]
    have ht : t ∈ (Gate.cz c t).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateU]
    rw [monoMat_submatrix]
    congr 1
    · funext u; simp
    · funext u; simp [h.get c hc u, h.get t ht u]
  | cp m k c t =>
    have hc : c ∈ (Gate.cp m k c t).qubits := by simp [Gate.qubits]
    have ht : t ∈ (Gate.cp m k c t).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateU]
    rw [monoMat_submatrix]
    congr 1
    · funext u; simp
    · funext u; simp [h.get c hc u, h.get t ht u]
  | measure q j => simp [Gate.map, gateU, Matrix.submatrix_one_equiv]
  | ifBit j g => simp [Gate.map, gateU, Matrix.submatrix_one_equiv]
  | alloc q => simp [Gate.map, gateU, Matrix.submatrix_one_equiv]
  | free q => simp [Gate.map, gateU, Matrix.submatrix_one_equiv]

theorem gateK_map {m : ℕ} (c : Fin m → Bool) (g : Gate) (h : Intertwines f E g) :
    gateK N A c (g.map f) = (gateK n a c g).submatrix E E := by
  cases g with
  | measure q j =>
    have hq : q ∈ (Gate.measure q j).qubits := by simp [Gate.qubits]
    simp only [Gate.map, gateK, projMat]
    rw [monoMat_submatrix]
    congr 1
    · funext u; simp
    · funext u; simp [h.get q hq u]
  | ifBit j g' =>
    simp only [Gate.map, gateK]
    split_ifs
    · exact gateU_map g' h.ifBit
    · rw [Matrix.submatrix_one_equiv]
  | _ => exact gateU_map _ h

theorem krausOps_map {m : ℕ} (gs : List Gate) (h : ∀ g ∈ gs, Intertwines f E g) (c : Fin m → Bool) :
    krausOps N A m (gs.map (Gate.map f)) c = (krausOps n a m gs c).submatrix E E := by
  induction gs with
  | nil => simp [krausOps, Matrix.submatrix_one_equiv]
  | cons g gs ih =>
    simp only [List.map_cons, krausOps]
    rw [ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')), gateK_map c g (h g (List.mem_cons_self ..)),
      Matrix.submatrix_mul_equiv]

theorem written_map (f : Qubit → Qubit) (gs : List Gate) :
    Circuit.written (gs.map (Gate.map f)) = Circuit.written gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [Circuit.written, List.flatMap_cons, Gate.map_writes] at ih ⊢; exact ih

theorem nBits_map (f : Qubit → Qubit) (nD : ℕ) (C : Circuit) : (C.map f nD).nBits = C.nBits := by
  simp [Circuit.nBits, Circuit.map, written_map]

theorem bitsOkFrom_map (f : Qubit → Qubit) {m : ℕ} (W : List ℕ) (gs : List Gate) :
    Circuit.bitsOkFrom m W (gs.map (Gate.map f)) = Circuit.bitsOkFrom m W gs := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Circuit.bitsOkFrom, Gate.map_writes, ih]
    congr 1
    cases g <;> simp [Gate.bitOk, Gate.map, Gate.map_isClifford]

/-- **The channel under a renaming**: on relabeled inputs the renamed circuit's output is the
relabeled output. -/
theorem channelDenote_map_m (nD : ℕ) (C : Circuit) (hC : C.bitsOk = true) (hC' : (C.map f nD).bitsOk = true)
    (h : ∀ g ∈ C.gates, Intertwines f E g) (ρ : MState (Reg n × Reg a)) :
    (channelDenote N A (C.map f nD) (ρ.relabel E)).m = ((channelDenote n a C ρ).relabel E).m := by
  rw [MState.relabel_m, channelDenote_m_gen N A hC' (nBits_map f nD C) (ρ.relabel E),
    channelDenote_m_of_bitsOk n a hC ρ]
  simp only [Circuit.map, krausOps_map C.gates h, MState.relabel_m]
  ext u v
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.submatrix_mul_equiv, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rfl

theorem channelDenote_map (nD : ℕ) (C : Circuit) (hC : C.bitsOk = true) (hC' : (C.map f nD).bitsOk = true)
    (h : ∀ g ∈ C.gates, Intertwines f E g) (ρ : MState (Reg n × Reg a)) :
    channelDenote N A (C.map f nD) (ρ.relabel E) = (channelDenote n a C ρ).relabel E := by
  apply MState.ext_m
  exact channelDenote_map_m nD C hC hC' h ρ

end GateMap

/-! ## Permutations of the data qubits -/

section Perm

variable {N A : ℕ} (σ : Equiv.Perm (Fin N))

/-- The basis states permuted with the data qubits: position `i` of `stateEquiv σ u` holds what
position `σ i` of `u` holds (so a gate on `σ i` of `u` is a gate on `i` of `stateEquiv σ u`). -/
def stateEquiv : Reg N × Reg A ≃ Reg N × Reg A where
  toFun u := (u.1 ∘ σ, u.2)
  invFun u := (u.1 ∘ σ.symm, u.2)
  left_inv u := by ext i <;> simp
  right_inv u := by ext i <;> simp

theorem stateEquiv_apply (u : Reg N × Reg A) : stateEquiv (A := A) σ u = (u.1 ∘ σ, u.2) := rfl

theorem stateEquiv_symm_apply (u : Reg N × Reg A) : (stateEquiv (A := A) σ).symm u = (u.1 ∘ σ.symm, u.2) := rfl

/-- `permMat σ`: the permutation matrix of basis states that moves the bit at position `i` to
position `σ i` (`permMat σ * ρ.m * (permMat σ)ᴴ = (ρ.relabel (stateEquiv σ)).m`). -/
def permMat : Matrix (Reg N × Reg A) (Reg N × Reg A) ℂ :=
  monoMat (stateEquiv (A := A) σ).symm (fun _ => 1)

theorem permMat_mem_unitaryGroup : permMat (A := A) σ ∈ Matrix.unitaryGroup (Reg N × Reg A) ℂ :=
  monoMat_equiv_mem_unitaryGroup _ fun _ => by simp

theorem permFn_lt {i : ℕ} (hi : i < N) : permFn N σ i = (σ ⟨i, hi⟩).val := by
  simp [permFn, hi]

theorem get_relabel (q : Qubit) (u : Reg N × Reg A) :
    (q.relabel N σ).get u = q.get (stateEquiv (A := A) σ u) := by
  cases q with
  | data i =>
    simp only [Qubit.relabel, Qubit.get, stateEquiv_apply, Function.comp_apply]
    by_cases hi : i < N
    · simp [permFn_lt σ hi, hi]
    · have : ¬ permFn N σ i < N := by simp [permFn, hi]
      simp [hi, this]
  | anc i => rfl

theorem set_relabel (q : Qubit) (v : Bool) (u : Reg N × Reg A) :
    stateEquiv (A := A) σ ((q.relabel N σ).set v u) = q.set v (stateEquiv σ u) := by
  cases q with
  | data i =>
    simp only [Qubit.relabel, Qubit.set, stateEquiv_apply]
    by_cases hi : i < N
    · have hlt : permFn N σ i < N := by rw [permFn_lt σ hi]; exact (σ ⟨i, hi⟩).isLt
      have ha : (⟨permFn N σ i, hlt⟩ : Fin N) = σ ⟨i, hi⟩ := Fin.ext (permFn_lt σ hi)
      simp only [hi, hlt, ↓reduceDIte]
      refine Prod.ext ?_ rfl
      show Function.update u.1 ⟨permFn N σ i, hlt⟩ v ∘ σ = Function.update (u.1 ∘ σ) ⟨i, hi⟩ v
      rw [Function.update_comp_equiv, ha, Equiv.symm_apply_apply]
    · have : ¬ permFn N σ i < N := by simp [permFn, hi]
      simp [hi, this]
  | anc i =>
    simp only [Qubit.relabel, Qubit.set, stateEquiv_apply]
    split_ifs <;> rfl

theorem flip_relabel (q : Qubit) (u : Reg N × Reg A) :
    stateEquiv (A := A) σ ((q.relabel N σ).flip u) = q.flip (stateEquiv σ u) := by
  rw [Qubit.flip, Qubit.flip, set_relabel, get_relabel]

theorem inRange_relabel (q : Qubit) : (q.relabel N σ).inRange N A = q.inRange N A := by
  cases q with
  | data i =>
    by_cases hi : i < N
    · simp [Qubit.relabel, Qubit.inRange, permFn_lt σ hi, hi, (σ ⟨i, hi⟩).isLt]
    · simp [Qubit.relabel, Qubit.inRange, permFn, hi]
  | anc i => rfl

theorem relabel_injective : Function.Injective (Qubit.relabel N σ) := by
  intro q q' h
  cases q with
  | anc i =>
    cases q' with
    | anc j => simpa [Qubit.relabel] using h
    | data j => simp [Qubit.relabel] at h
  | data i =>
    cases q' with
    | anc j => simp [Qubit.relabel] at h
    | data j =>
      simp only [Qubit.relabel, Qubit.data.injEq] at h ⊢
      by_cases hi : i < N <;> by_cases hj : j < N
      · rw [permFn_lt σ hi, permFn_lt σ hj] at h
        exact congrArg Fin.val (σ.injective (Fin.ext h))
      · rw [permFn_lt σ hi] at h
        simp only [permFn, hj, ↓reduceDIte] at h
        have := (σ ⟨i, hi⟩).isLt
        omega
      · rw [permFn_lt σ hj] at h
        simp only [permFn, hi, ↓reduceDIte] at h
        have := (σ ⟨j, hj⟩).isLt
        omega
      · simpa [permFn, hi, hj] using h

theorem intertwines_relabel (g : Gate) : Intertwines (Qubit.relabel N σ) (stateEquiv (A := A) σ) g :=
  ⟨fun q _ u => get_relabel σ q u, fun q _ u => flip_relabel σ q u, fun q _ => inRange_relabel σ q,
   fun _ _ _ _ h => relabel_injective σ h⟩

/-- **`gateU_relabel`**: the relabeled gate is the gate conjugated by the state permutation. -/
theorem gateU_relabel (g : Gate) :
    gateU N A (g.relabel N σ) = (gateU N A g).submatrix (stateEquiv σ) (stateEquiv σ) :=
  gateU_map g (intertwines_relabel σ g)

theorem Gate.relabel_eq_map : Gate.relabel N σ = Gate.map (Qubit.relabel N σ) := rfl

theorem Circuit.relabel_eq_map (C : Circuit) : C.relabel N σ = C.map (Qubit.relabel N σ) C.nData := rfl

theorem relabel_bitsOk (C : Circuit) (h : C.bitsOk = true) : (C.relabel N σ).bitsOk = true := by
  rw [Circuit.relabel_eq_map]
  simp only [Circuit.bitsOk, Circuit.map, Circuit.nBits, written_map, bitsOkFrom_map]
  exact h

/-- **`channelDenote_relabel`**: the relabeled circuit, on relabeled inputs, gives relabeled
outputs (PHASE2_SPEC §C.3: `Ad(permMat σ) ∘ channel ∘ Ad(permMat σ⁻¹)` in the relabeling form). -/
theorem channelDenote_relabel (C : Circuit) (hC : C.bitsOk = true) (ρ : MState (Reg N × Reg A)) :
    channelDenote N A (C.relabel N σ) (ρ.relabel (stateEquiv σ)) =
      (channelDenote N A C ρ).relabel (stateEquiv σ) := by
  rw [Circuit.relabel_eq_map]
  exact channelDenote_map C.nData C hC (relabel_bitsOk σ C hC) (fun g _ => intertwines_relabel σ g) ρ

/-- Relabeling a state by `stateEquiv σ` is conjugation by `permMat σ`, on the matrices. -/
theorem relabel_m_eq_permMat (ρ : MState (Reg N × Reg A)) :
    (ρ.relabel (stateEquiv σ)).m = permMat σ * ρ.m * (permMat σ)ᴴ := by
  rw [MState.relabel_m, permMat, monoMat_equiv_conj]

end Perm

/-! ## The SWAP entry -/

section Swap

variable (N A : ℕ)

/-- Two CNOTs then a CNOT: the state permutation of the transposition `swap p q` on the data
qubits (`cnotPerm p q ∘ cnotPerm q p ∘ cnotPerm p q` swaps the two bits). -/
theorem cnot_cnot_cnot (p q : Fin N) (hpq : p ≠ q) :
    gateU N A (.cnot (.data p) (.data q)) * (gateU N A (.cnot (.data q) (.data p)) *
      gateU N A (.cnot (.data p) (.data q))) = permMat (A := A) (swapPerm N p q) := by
  have hne : (Qubit.data (p : ℕ)) ≠ .data (q : ℕ) := fun h => hpq (Fin.ext (Qubit.data.inj h))
  simp only [gateU, hne, hne.symm, ↓reduceIte, monoMat_mul, permMat]
  congr 1
  · funext u
    refine Prod.ext ?_ ?_
    · ext i
      simp only [Function.comp_apply, stateEquiv_symm_apply, swapPerm, Equiv.symm_swap, CQRV.cnotPerm,
        Qubit.get, Qubit.flip, Qubit.set, Fin.is_lt, ↓reduceDIte, Fin.eta]
      by_cases hp : u.1 p <;> by_cases hq : u.1 q <;>
        simp [hp, hq, Function.update, Equiv.swap_apply_def, hpq, hpq.symm] <;>
        split_ifs <;> simp_all
    · simp only [Function.comp_apply, stateEquiv_symm_apply, CQRV.cnotPerm, Qubit.flip, Qubit.set,
        Qubit.get, Fin.is_lt, ↓reduceDIte]
      split_ifs <;> rfl
  · funext j; simp

/-- **`ud_swapEntry`**: the expansion of the table's `swap` entry is `phaseQ irPhase • permMat (swap p q)`. -/
theorem ud_swapEntry (b : TargetBasis) (p q : Fin N) (hpq : p ≠ q) :
    unitaryDenote N A ((swapEntry b (.data p) (.data q)).gates.flatMap BasisGate.expand) =
      phaseQ (swapEntry b (.data p) (.data q)).irPhase • permMat (A := A) (swapPerm N p q) := by
  have hne : (Qubit.data (p : ℕ)) ≠ .data (q : ℕ) := fun h => hpq (Fin.ext (Qubit.data.inj h))
  have hp : (Qubit.data (p : ℕ)).inRange N A = true := by simp [Qubit.inRange]
  have hq : (Qubit.data (q : ℕ)).inRange N A = true := by simp [Qubit.inRange]
  have hg : (swapEntry b (.data p) (.data q)).gates =
      (cnotEntry b (.data p) (.data q)).gates ++ (cnotEntry b (.data q) (.data p)).gates ++
        (cnotEntry b (.data p) (.data q)).gates := rfl
  rw [hg, List.flatMap_append, List.flatMap_append, unitaryDenote_append, unitaryDenote_append,
    ud_cnotEntry N A b hne hq, ud_cnotEntry N A b hne.symm hp]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [cnot_cnot_cnot N A p q hpq]
  congr 1
  have hphase : (swapEntry b (.data p) (.data q)).irPhase = 3 * (cnotEntry b (.data p) (.data q)).irPhase := by
    cases b <;> norm_num [swapEntry, cnotEntry, Entry.irPhase, hGates, hPhase, BasisGate.embedPhase]
  rw [hphase, show (3 : ℚ) * (cnotEntry b (.data p) (.data q)).irPhase =
    (cnotEntry b (.data p) (.data q)).irPhase + ((cnotEntry b (.data p) (.data q)).irPhase +
      (cnotEntry b (.data p) (.data q)).irPhase) by ring, phaseQ_add, phaseQ_add, phaseQ_cnot]
  ring

end Swap

/-! ## The canonical placement of the logical register on a flat register -/

section Place

variable (n a' : ℕ)

/-- `Reg (n + a') × Reg 0 ≃ Reg n × Reg a'`: drop the empty ancilla part and split the flat
register into its first `n` and its last `a'` positions. -/
def placeEquiv : Reg (n + a') × Reg 0 ≃ Reg n × Reg a' :=
  (Equiv.prodUnique (Reg (n + a')) (Reg 0)).trans (regEquiv n a')

theorem placeEquiv_apply (u : Reg (n + a') × Reg 0) : placeEquiv n a' u = splitReg u.1 := rfl

theorem splitReg_update_natAdd {a b : ℕ} (w : Reg (a + b)) (j : Fin b) (v : Bool) :
    splitReg (Function.update w (Fin.natAdd a j) v) =
      ((splitReg w).1, Function.update (splitReg w).2 j v) := by
  simp only [splitReg, Prod.mk.injEq]
  constructor
  · funext k
    rw [Function.update_of_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  · funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd] at this
      exact hk (Fin.ext (by omega))

theorem get_place {q : Qubit} (hq : q.inRange n a' = true) (u : Reg (n + a') × Reg 0) :
    (q.place n).get u = q.get (placeEquiv n a' u) := by
  cases q with
  | data i =>
    have hi : i < n := by simpa [Qubit.inRange] using hq
    simp only [Qubit.place, Qubit.get, placeEquiv_apply, splitReg, hi, show i < n + a' by omega, ↓reduceDIte]
    rfl
  | anc j =>
    have hj : j < a' := by simpa [Qubit.inRange] using hq
    simp only [Qubit.place, Qubit.get, placeEquiv_apply, splitReg, hj, show n + j < n + a' by omega, ↓reduceDIte]
    rfl

theorem set_place {q : Qubit} (hq : q.inRange n a' = true) (v : Bool) (u : Reg (n + a') × Reg 0) :
    placeEquiv n a' ((q.place n).set v u) = q.set v (placeEquiv n a' u) := by
  cases q with
  | data i =>
    have hi : i < n := by simpa [Qubit.inRange] using hq
    simp only [Qubit.place, Qubit.set, placeEquiv_apply, hi, show i < n + a' by omega, ↓reduceDIte]
    have : (⟨i, show i < n + a' by omega⟩ : Fin (n + a')) = Fin.castAdd a' ⟨i, hi⟩ := Fin.ext rfl
    rw [this, splitReg_update_castAdd]
  | anc j =>
    have hj : j < a' := by simpa [Qubit.inRange] using hq
    simp only [Qubit.place, Qubit.set, placeEquiv_apply, hj, show n + j < n + a' by omega, ↓reduceDIte]
    have : (⟨n + j, show n + j < n + a' by omega⟩ : Fin (n + a')) = Fin.natAdd n ⟨j, hj⟩ := Fin.ext rfl
    rw [this, splitReg_update_natAdd]

theorem flip_place {q : Qubit} (hq : q.inRange n a' = true) (u : Reg (n + a') × Reg 0) :
    placeEquiv n a' ((q.place n).flip u) = q.flip (placeEquiv n a' u) := by
  rw [Qubit.flip, Qubit.flip, set_place n a' hq, get_place n a' hq]

theorem inRange_place {q : Qubit} (hq : q.inRange n a' = true) : (q.place n).inRange (n + a') 0 = true := by
  cases q with
  | data i => have hi : i < n := by simpa [Qubit.inRange] using hq
              simp [Qubit.place, Qubit.inRange]; omega
  | anc j => have hj : j < a' := by simpa [Qubit.inRange] using hq
             simp [Qubit.place, Qubit.inRange]; omega

theorem place_inj {q q' : Qubit} (hq : q.inRange n a' = true) (hq' : q'.inRange n a' = true)
    (h : q.place n = q'.place n) : q = q' := by
  cases q <;> cases q' <;> simp [Qubit.place] at h ⊢ <;> simp [Qubit.inRange] at hq hq' <;> omega

theorem intertwines_place (g : Gate) (hg : ∀ q ∈ g.qubits, q.inRange n a' = true) :
    Intertwines (Qubit.place n) (placeEquiv n a') g :=
  ⟨fun q hq u => get_place n a' (hg q hq) u, fun q hq u => flip_place n a' (hg q hq) u,
   fun q hq => by rw [inRange_place n a' (hg q hq), hg q hq],
   fun q hq q' hq' h => place_inj n a' (hg q hq) (hg q' hq') h⟩

theorem place_bitsOk (C : Circuit) (h : C.bitsOk = true) : (C.place n a').bitsOk = true := by
  simp only [Circuit.bitsOk, Circuit.place, Circuit.map, Circuit.nBits, written_map, bitsOkFrom_map]
  exact h

/-- **The channel of the placed circuit**: on the flat register, on placed inputs, the placed
circuit gives placed outputs. -/
theorem channelDenote_place (C : Circuit) (hC : C.bitsOk = true)
    (hr : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n a' = true) (ρ : MState (Reg n × Reg a')) :
    channelDenote (n + a') 0 (C.place n a') (ρ.relabel (placeEquiv n a')) =
      (channelDenote n a' C ρ).relabel (placeEquiv n a') :=
  channelDenote_map (n + a') C hC (place_bitsOk n a' C hC) (fun g hg => intertwines_place n a' g (hr g hg)) ρ

end Place

/-! ## The embedding: idle ancillae, placement, layout -/

section Embed

variable {n a : ℕ} (b : ℕ)

/-- A logical state with `b` more ancillae in |0⟩ (23a's widening, as a state). -/
def embedState (ρ : MState (Reg n × Reg a)) : MState (Reg n × Reg (a + b)) :=
  (ρ ⊗ᴹ ancZero b).relabel (wEquiv n a b)

theorem embedState_m (ρ : MState (Reg n × Reg a)) : (embedState b ρ).m = wideZ (b := b) ρ.m := by
  rw [embedState, MState.relabel_m]
  rfl

/-- **The channel on the widened register**: a circuit whose ancillae lie below `a` acts on the
widened state as it acts on the state (23a's `krausOps_wide`, as a channel equality). -/
theorem channelDenote_widen (C : Circuit) (hC : C.WF) (hq : ancsBelow C.gates a = true)
    (ρ : MState (Reg n × Reg a)) :
    channelDenote n (a + b) C (embedState b ρ) = embedState b (channelDenote n a C ρ) := by
  apply MState.ext_m
  rw [embedState_m, channelDenote_m_of_bitsOk n (a + b) hC.bitsOk, channelDenote_m_of_bitsOk n a hC.bitsOk,
    embedState_m]
  simp only [krausOps_wide C.gates hq, wide_conjTranspose, wide_mul_wideZ_mul_wide]
  rw [wideZ_sum]

variable (σ : Equiv.Perm (Fin (n + (a + b))))

/-- The physical circuit of a logical one: `b` idle ancillae, the canonical placement, the layout
`σ` (the initial layout of a witness is the permutation taking the canonical positions to the
physical ones). -/
def physOf (C : Circuit) : Circuit := (C.place n (a + b)).relabel (n + (a + b)) σ

/-- The logical state on the physical register: |0⟩ on the idle qubits, placed, laid out. -/
def embed (ρ : MState (Reg n × Reg a)) : MState (Reg (n + (a + b)) × Reg 0) :=
  ((embedState b ρ).relabel (placeEquiv n (a + b))).relabel (stateEquiv σ)

theorem inRange_of_qubitsOk_ancsBelow {C : Circuit} (hd : ∀ g ∈ C.gates, g.qubitsOk n = true)
    (hq : ancsBelow C.gates a = true) : ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange n (a + b) = true := by
  intro g hg q hqg
  cases q with
  | data i =>
    have := hd g hg
    simp only [Gate.qubitsOk, Bool.and_eq_true, List.all_eq_true] at this
    have := this.1 (.data i) hqg
    simpa [Qubit.inRange] using this
  | anc i =>
    have := ancBelow_of_mem hq hg hqg
    simp only [Qubit.ancBelow, decide_eq_true_eq] at this
    simp [Qubit.inRange]; omega

/-- **`channelDenote_embed`**: the physical circuit on the embedded input gives the embedded
output of the logical circuit. -/
theorem channelDenote_embed (C : Circuit) (hC : C.WF) (hq : ancsBelow C.gates a = true)
    (hd : ∀ g ∈ C.gates, g.qubitsOk n = true) (ρ : MState (Reg n × Reg a)) :
    channelDenote (n + (a + b)) 0 (physOf b σ C) (embed b σ ρ) = embed b σ (channelDenote n a C ρ) := by
  unfold physOf embed
  rw [channelDenote_relabel σ _ (place_bitsOk n (a + b) C hC.bitsOk),
    channelDenote_place n (a + b) C hC.bitsOk (inRange_of_qubitsOk_ancsBelow b hd hq),
    channelDenote_widen b C hC hq]

end Embed

end

end CQRV.Hardware
