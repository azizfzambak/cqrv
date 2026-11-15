module

public import CQRV.Hardware.Route
public import CQRV.Hardware.Witness

/-!
# CQRV.Hardware.Reorder

Report §9.1.1; PHASE2_SPEC §C.3 step 2 (Stage 26b2, Track C) — commutation of gates on disjoint
qubits and the soundness of the dependency-queue reordering, Physlib-side.

* **Locality.** Every gate matrix of the IR is a monomial matrix or `hMat`, a scalar times a sum
  of two monomial matrices; the permutation of basis states of a gate changes and reads only the
  gate's qubits (`Supported`), and its phase function reads only them (`Depends`). `Local Q M`
  records that for a matrix `M` and a qubit list `Q`; two local matrices on disjoint lists
  commute (`Local.comm`), and every Kraus factor `gateK` is local to its gate's qubits
  (`gateK_local`).
* **`gateK_comm_of_disjoint`.** Two gates with disjoint qubit lists have commuting Kraus factors
  in every branch. The classical bits do not enter the matrices of a fixed branch; they enter
  well-formedness, which `applyWitness` checks by evaluation (`Witness.lean`).
* **`krausOps_reorder`.** `validReorder` (`Witness.lean`: a reordering that takes, at each step,
  an element at the head of every dependency queue it touches — the Python matcher's acceptance)
  preserves the Kraus operators of the flattened segments in every branch. Stated for segments
  (lists of IR gates: a basis gate's expansion, or a conditioned block), as the witness reorders
  elements; the qubit part of `indep` is what the proof uses.
* **`krausOps_swap_migrate`.** A routing SWAP followed by gates relabeled by its transposition
  equals the gates followed by the SWAP, Kraus operator for Kraus operator: the step that moves
  every SWAP of a witness to the end of the circuit (26b3).
-/

@[expose] public section

open CQRV Matrix

namespace CQRV.Hardware

noncomputable section

/-! ## Locality of permutations and phases -/

section Locality

variable {n a : ℕ}

/-- States agree on a qubit list. -/
def AgreeOn (Q : List Qubit) (s t : Reg n × Reg a) : Prop := ∀ q ∈ Q, q.get s = q.get t

/-- A state permutation supported on `Q`: it fixes the bits outside `Q`, and what it writes in `Q`
depends only on the bits in `Q`. -/
structure Supported (Q : List Qubit) (P : Reg n × Reg a → Reg n × Reg a) : Prop where
  fix : ∀ s q, q ∉ Q → q.get (P s) = q.get s
  dep : ∀ s t, AgreeOn Q s t → AgreeOn Q (P s) (P t)

/-- A phase function reading only the bits in `Q`. -/
def Depends (Q : List Qubit) (φ : Reg n × Reg a → ℂ) : Prop :=
  ∀ s t, AgreeOn Q s t → φ s = φ t

/-- A basis state is determined by the values of its qubits. -/
theorem ext_get {s t : Reg n × Reg a} (h : ∀ q : Qubit, q.get s = q.get t) : s = t := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · have := h (.data i); simpa [Qubit.get, i.isLt] using this
  · have := h (.anc j); simpa [Qubit.get, j.isLt] using this

theorem Supported.id (Q : List Qubit) : Supported (n := n) (a := a) Q id :=
  ⟨fun _ _ _ => rfl, fun _ _ h => h⟩

/-- Permutations supported on disjoint lists commute. -/
theorem Supported.comm {Q₁ Q₂ : List Qubit} {P₁ P₂ : Reg n × Reg a → Reg n × Reg a}
    (h₁ : Supported Q₁ P₁) (h₂ : Supported Q₂ P₂) (hd : ∀ q ∈ Q₁, q ∉ Q₂) :
    P₁ ∘ P₂ = P₂ ∘ P₁ := by
  funext s
  apply ext_get
  intro q
  simp only [Function.comp_apply]
  by_cases hq1 : q ∈ Q₁
  · have hq2 : q ∉ Q₂ := hd q hq1
    rw [h₂.fix _ q hq2]
    exact h₁.dep (P₂ s) s (fun r hr => h₂.fix s r (hd r hr)) q hq1
  · by_cases hq2 : q ∈ Q₂
    · rw [h₁.fix _ q hq1]
      exact (h₂.dep (P₁ s) s (fun r hr => h₁.fix s r (fun h => hd r h hr)) q hq2).symm
    · rw [h₁.fix _ q hq1, h₂.fix _ q hq2, h₂.fix _ q hq2, h₁.fix _ q hq1]

theorem Depends.comp {Q₁ Q₂ : List Qubit} {φ : Reg n × Reg a → ℂ}
    {P : Reg n × Reg a → Reg n × Reg a} (hφ : Depends Q₁ φ) (hP : Supported Q₂ P)
    (hd : ∀ q ∈ Q₁, q ∉ Q₂) : ∀ s, φ (P s) = φ s :=
  fun s => hφ (P s) s fun q hq => hP.fix s q (hd q hq)

/-- Monomial matrices local to disjoint lists commute. -/
theorem monoMat_comm_of_local {Q₁ Q₂ : List Qubit} {σ τ : Reg n × Reg a → Reg n × Reg a}
    {φ ψ : Reg n × Reg a → ℂ} (hσ : Supported Q₁ σ) (hφ : Depends Q₁ φ) (hτ : Supported Q₂ τ)
    (hψ : Depends Q₂ ψ) (hd : ∀ q ∈ Q₁, q ∉ Q₂) :
    monoMat σ φ * monoMat τ ψ = monoMat τ ψ * monoMat σ φ := by
  rw [monoMat_mul, monoMat_mul, hσ.comm hτ hd]
  congr 1
  funext j
  rw [hφ.comp hτ hd, hψ.comp hσ (fun q hq hq' => hd q hq' hq), mul_comm]

/-- A matrix local to `Q`: a monomial matrix supported on `Q`, or a scalar times a sum of two
local matrices. -/
inductive Local (Q : List Qubit) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ → Prop
  | mono {σ φ} (hσ : Supported Q σ) (hφ : Depends Q φ) : Local Q (monoMat σ φ)
  | sum {c : ℂ} {A B} (hA : Local Q A) (hB : Local Q B) : Local Q (c • (A + B))

/-- **Local matrices on disjoint qubit lists commute.** -/
theorem Local.comm {Q₁ Q₂ : List Qubit} {M N : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ}
    (hM : Local Q₁ M) (hN : Local Q₂ N) (hd : ∀ q ∈ Q₁, q ∉ Q₂) : M * N = N * M := by
  induction hM with
  | mono hσ hφ =>
    induction hN with
    | mono hτ hψ => exact monoMat_comm_of_local hσ hφ hτ hψ hd
    | sum _ _ ihA ihB =>
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ihA, ihB]
  | sum _ _ ihA ihB =>
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, ihA, ihB]

theorem Local.one (Q : List Qubit) : Local (n := n) (a := a) Q 1 := by
  rw [← monoMat_id_one]
  exact .mono (Supported.id Q) fun _ _ _ => rfl

theorem Local.mono_of_subset {Q Q' : List Qubit} {M : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ}
    (h : Local Q M) (hQ : ∀ q ∈ Q, q ∈ Q') : Local Q' M := by
  induction h with
  | mono hσ hφ =>
    refine .mono ⟨fun s q hq => hσ.fix s q (fun h => hq (hQ q h)), fun s t hst => ?_⟩
      (fun s t hst => hφ s t fun q hq => hst q (hQ q hq))
    intro q hq
    by_cases hq' : q ∈ Q
    · exact hσ.dep s t (fun r hr => hst r (hQ r hr)) q hq'
    · rw [hσ.fix s q hq', hσ.fix t q hq']; exact hst q hq
  | sum _ _ ihA ihB => exact .sum ihA ihB

/-! ## The gate matrices are local to their qubits -/

theorem get_flip_eq (r t : Qubit) (s : Reg n × Reg a) :
    r.get (t.flip s) = if r = t ∧ t.inRange n a = true then !r.get s else r.get s := by
  by_cases hrt : r = t
  · subst hrt
    cases ht : r.inRange n a
    · simp [Qubit.flip, Qubit.set_of_not_inRange ht]
    · simp [Qubit.get_flip_self r ht]
  · simp [hrt, Qubit.get_flip_ne hrt]

theorem supported_flip (q : Qubit) : Supported (n := n) (a := a) [q] q.flip :=
  ⟨fun s r hr => by rw [get_flip_eq]; simp [show r ≠ q by simpa using hr],
   fun s t hst r hr => by rw [get_flip_eq, get_flip_eq, hst r hr]⟩

theorem supported_cnotPerm (c t : Qubit) : Supported (n := n) (a := a) [c, t] (cnotPerm n a c t) :=
  ⟨fun s r hr => by
    simp only [CQRV.cnotPerm]
    split_ifs
    · rw [get_flip_eq]; simp [show r ≠ t from fun h => hr (by simp [h])]
    · rfl,
   fun s t' hst r hr => by
    have hc : c.get s = c.get t' := hst c (by simp)
    simp only [CQRV.cnotPerm, hc]
    split_ifs
    · rw [get_flip_eq, get_flip_eq, hst r hr]
    · exact hst r hr⟩

theorem depends_one (q : Qubit) (f : Bool → ℂ) : Depends (n := n) (a := a) [q] (fun s => f (q.get s)) :=
  fun s t h => by show f (q.get s) = f (q.get t); rw [h q (by simp)]

theorem depends_two (c t : Qubit) (f : Bool → Bool → ℂ) :
    Depends (n := n) (a := a) [c, t] (fun s => f (c.get s) (t.get s)) :=
  fun s t' h => by show f (c.get s) (t.get s) = f (c.get t') (t.get t'); rw [h c (by simp), h t (by simp)]

theorem depends_const (Q : List Qubit) (z : ℂ) : Depends (n := n) (a := a) Q (fun _ => z) :=
  fun _ _ _ => rfl

theorem phaseMat_local (q : Qubit) (p : ℂ) : Local [q] (phaseMat n a q p) :=
  .mono (Supported.id _) (depends_one q fun b => if b then p else 1)

/-- Every gate matrix is local to the gate's qubits. -/
theorem gateU_local (g : Gate) : Local g.qubits (gateU n a g) := by
  cases g with
  | h q =>
    simp only [gateU, Gate.qubits]
    split_ifs
    · rw [hMat]
      exact .sum (.mono (Supported.id _) (depends_one q fun b => if b then -1 else 1))
        (.mono (supported_flip q) (depends_const _ 1))
    · exact Local.one _
  | s q => exact phaseMat_local q _
  | sdg q => exact phaseMat_local q _
  | t q => exact phaseMat_local q _
  | tdg q => exact phaseMat_local q _
  | z q => exact phaseMat_local q _
  | p m k q => exact phaseMat_local q _
  | x q => exact .mono (supported_flip q) (depends_const _ 1)
  | cnot c t =>
    simp only [gateU, Gate.qubits]
    split_ifs
    · exact Local.one _
    · exact .mono (supported_cnotPerm c t) (depends_const _ 1)
  | cz c t =>
    exact .mono (Supported.id _) (depends_two c t fun x y => if x && y then -1 else 1)
  | cp m k c t =>
    exact .mono (Supported.id _) (depends_two c t fun x y => if x && y then phaseOf m k else 1)
  | measure q j => exact Local.one _
  | ifBit j g => exact Local.one _
  | alloc q => exact Local.one _
  | free q => exact Local.one _

/-- Every Kraus factor is local to the gate's qubits, in every branch. -/
theorem gateK_local {m : ℕ} (c : Fin m → Bool) (g : Gate) : Local g.qubits (gateK n a c g) := by
  cases g with
  | measure q j =>
    simp only [gateK, projMat, Gate.qubits]
    exact .mono (Supported.id _) (depends_one q fun b => if b = bitVal c j then 1 else 0)
  | ifBit j g' =>
    simp only [gateK, Gate.qubits]
    split_ifs
    · exact gateU_local g'
    · exact Local.one _
  | _ => exact gateU_local _

/-- **`gateK_comm_of_disjoint`**: gates on disjoint qubits have commuting Kraus factors. -/
theorem gateK_comm_of_disjoint {m : ℕ} (c : Fin m → Bool) {g₁ g₂ : Gate}
    (hd : ∀ q ∈ g₁.qubits, q ∉ g₂.qubits) :
    gateK n a c g₁ * gateK n a c g₂ = gateK n a c g₂ * gateK n a c g₁ :=
  (gateK_local c g₁).comm (gateK_local c g₂) hd

theorem krausOps_local {m : ℕ} (c : Fin m → Bool) (gs : List Gate) :
    Local (gs.flatMap Gate.qubits) (krausOps n a m gs c) := by
  induction gs with
  | nil => exact Local.one _
  | cons g gs ih =>
    simp only [krausOps, List.flatMap_cons]
    -- a product of local matrices is local to the union: through `monoMat_mul` on the pieces
    exact local_mul (ih.mono_of_subset fun q hq => List.mem_append_right _ hq)
      ((gateK_local c g).mono_of_subset fun q hq => List.mem_append_left _ hq)
where
  local_mul {Q : List Qubit} {M N : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ} (hM : Local Q M)
      (hN : Local Q N) : Local Q (M * N) := by
    induction hM with
    | @mono σ φ hσ hφ =>
      induction hN with
      | @mono τ ψ hτ hψ =>
        rw [monoMat_mul]
        exact .mono ⟨fun s q hq => by show q.get (σ (τ s)) = q.get s; rw [hσ.fix _ q hq, hτ.fix s q hq],
          fun s t hst => hσ.dep _ _ (hτ.dep s t hst)⟩
          (fun s t hst => by
            show φ (τ s) * ψ s = φ (τ t) * ψ t
            rw [hφ _ _ (hτ.dep s t hst), hψ s t hst])
      | sum _ _ ihA ihB =>
        rw [Matrix.mul_smul, Matrix.mul_add]
        exact .sum ihA ihB
    | sum _ _ ihA ihB =>
      rw [Matrix.smul_mul, Matrix.add_mul]
      exact .sum ihA ihB

/-- Segments on disjoint qubits have commuting Kraus operators. -/
theorem krausOps_comm_of_disjoint {m : ℕ} (c : Fin m → Bool) {s₁ s₂ : List Gate}
    (hd : ∀ q ∈ s₁.flatMap Gate.qubits, q ∉ s₂.flatMap Gate.qubits) :
    krausOps n a m s₁ c * krausOps n a m s₂ c = krausOps n a m s₂ c * krausOps n a m s₁ c :=
  (krausOps_local c s₁).comm (krausOps_local c s₂) hd

end Locality

/-! ## The reordering -/

section Reorder

variable {n a : ℕ}

theorem splitFirst_spec {α : Type} [DecidableEq α] {x : α} {l pre post : List α}
    (h : splitFirst x l = some (pre, post)) : l = pre ++ x :: post := by
  induction l generalizing pre with
  | nil => simp [splitFirst] at h
  | cons y ys ih =>
    simp only [splitFirst] at h
    split_ifs at h with hy
    · subst hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · cases hs : splitFirst x ys with
      | none => simp [hs] at h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih hs]

/-- The qubits of a segment. -/
def segQubits (s : List Gate) : List Qubit := s.flatMap Gate.qubits

/-- **`krausOps_reorder`**: a valid reordering of segments (the dependency queues of qubits and
classical bits, as the matcher accepts them) has the same Kraus operators in every branch. -/
theorem krausOps_reorder {m : ℕ} (bits : List Gate → List ℕ) (segs segs' : List (List Gate))
    (h : validReorder segQubits bits segs segs' = true) (c : Fin m → Bool) :
    krausOps n a m (segs'.flatMap id) c = krausOps n a m (segs.flatMap id) c := by
  induction segs' generalizing segs with
  | nil =>
    simp only [validReorder, List.isEmpty_iff] at h
    subst h
    rfl
  | cons g rest ih =>
    simp only [validReorder] at h
    cases hs : splitFirst g segs with
    | none => rw [hs] at h; simp at h
    | some p =>
      obtain ⟨pre, post⟩ := p
      rw [hs] at h
      simp only [Bool.and_eq_true] at h
      rw [splitFirst_spec hs, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
        krausOps_append_list, krausOps_append_list, krausOps_append_list, ih (pre ++ post) h.2,
        List.flatMap_append, krausOps_append_list, id]
      -- `g` is independent of every segment before it, so its Kraus operator commutes with theirs
      have hcomm : krausOps n a m (pre.flatMap id) c * krausOps n a m g c =
          krausOps n a m g c * krausOps n a m (pre.flatMap id) c := by
        apply krausOps_comm_of_disjoint
        intro q hq hq'
        obtain ⟨g', hg', hqg⟩ := List.mem_flatMap.mp hq
        obtain ⟨seg, hseg, hg'seg⟩ := List.mem_flatMap.mp hg'
        have hi := List.all_eq_true.mp h.1 seg hseg
        simp only [indep, Bool.and_eq_true] at hi
        have h1 := hi.1
        simp only [disjointL, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
        exact h1 q hq' (List.mem_flatMap.mpr ⟨g', hg'seg, hqg⟩)
      rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

end Reorder

/-! ## Moving a routing SWAP to the end -/

section Swap

variable {N A : ℕ} (τ : Equiv.Perm (Fin N))

theorem permMat_conjTranspose_mul : (permMat (A := A) τ)ᴴ * permMat τ = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp (permMat_mem_unitaryGroup (A := A) τ)
  rwa [Matrix.star_eq_conjTranspose] at this

/-- The Kraus factor of a relabeled gate is the conjugate of the gate's by `permMat τ`. -/
theorem gateK_relabel_eq {m : ℕ} (c : Fin m → Bool) (g : Gate) :
    gateK N A c (g.relabel N τ) = permMat τ * gateK N A c g * (permMat τ)ᴴ := by
  rw [Gate.relabel, gateK_map c g (intertwines_relabel τ g), permMat, monoMat_equiv_conj]

/-- Relabeled gates followed by the conjugating permutation = the permutation followed by the
gates. -/
theorem krausOps_relabel_mul_perm {m : ℕ} (c : Fin m → Bool) (L : List Gate) :
    krausOps N A m (L.map (Gate.relabel N τ)) c * permMat τ = permMat τ * krausOps N A m L c := by
  induction L with
  | nil => simp [krausOps]
  | cons g L ih =>
    simp only [List.map_cons, krausOps]
    rw [gateK_relabel_eq τ c g, Matrix.mul_assoc, Matrix.mul_assoc, permMat_conjTranspose_mul,
      Matrix.mul_one, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- **`krausOps_swap_migrate`**: the expansion `S` of the table's SWAP entry on `p, q`, followed by
gates relabeled by the transposition, has the Kraus operators of the gates followed by `S`. -/
theorem krausOps_swap_migrate {m : ℕ} (b : TargetBasis) (p q : Fin N) (hpq : p ≠ q)
    (L : List Gate) (c : Fin m → Bool) :
    krausOps N A m ((swapEntry b (.data p) (.data q)).gates.flatMap BasisGate.expand ++
        L.map (Gate.relabel N (swapPerm N p q))) c =
      krausOps N A m (L ++ (swapEntry b (.data p) (.data q)).gates.flatMap BasisGate.expand) c := by
  have hu : ((swapEntry b (.data p) (.data q)).gates.flatMap BasisGate.expand).all Gate.isUnitary = true := by
    cases b <;> simp [swapEntry, cnotEntry, hGates, BasisGate.expand, Gate.isUnitary]
  rw [krausOps_append_list, krausOps_append_list, krausOps_of_unitary N A m _ hu, ud_swapEntry N A b p q hpq,
    Matrix.mul_smul, Matrix.smul_mul, krausOps_relabel_mul_perm]

end Swap

end

end CQRV.Hardware
