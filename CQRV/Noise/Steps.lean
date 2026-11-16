module

public import CQRV.Circuit.Restoration
public import CQRV.Noise.Perturb

/-!
# CQRV.Noise.Steps

Report §6.6, §9.1.1; PHASE2_SPEC §C.4 (1); STAGE27_TASK.md 27a N1 — **the step semantics with the
classical register**. `channelDenote` (Stage 6) is a sum over branches of classical bits, so it is not
a composition of per-gate channels on the quantum register: a measurement and the conditioned gates
that read its bit are linked through the bits. The noise theorem needs per-gate channels, so the
register is extended by the bits, `X⁺ = (Reg n × Reg a) × Reg m` (`XReg`; the bits are `Reg m`, the
branch index of `krausOps`), and every gate becomes a channel on `X⁺`:

* a unitary gate `g` is `Ad(gateU g ⊗ 1)`; `ifBit j g` is the controlled unitary
  `∑_c gateK c g ⊗ |c⟩⟨c|` — both are the block operator `blockOp (gateK · g) id`
  (`gateK c g = gateU g` for a plain gate; `= if c j then gateU g else 1` for `ifBit`);
* `measure q → j` has the Kraus operators `P_{q=v} ⊗ X_j^v`, `v ∈ {0, 1}` (`blockOp (P_v) (flip_j^v)`):
  it records the outcome into bit `j`. It is a channel on every input (`stepK_complete`); on a bit
  that is still 0, which `bitsOk` guarantees, it records the outcome.

`stepChan g` is the Kraus channel of `stepK g`; `stepsOf gs` their composition, first gate first
(`steps`, `CQRV.Noise.Perturb`). **`channelDenote_eq_steps`**: for a well-formed `C`,
`channelDenote n a C ρ = traceRight (stepsOf C.gates (ρ ⊗ |0…0⟩⟨0…0|))`, and the channel form
`channelDenote_eq_steps_chan` with the preparation channel `withBits`.

The proof (`stepsOf_map`, by induction along the gate list): after the prefix `gs` with written bits
`W`, the state is `∑_d [supp d ⊆ W] (K_d ρ K_dᴴ) ⊗ |d⟩⟨d|` (`diagBlocks`, `branch`); a unitary step
conjugates every block by `gateK d g` (`krausOps_append`); a measurement of a fresh bit `j` splits
each block by `P_{d j}` and moves it to `d` (`kraus_invariant`: `K_d` does not depend on bit `j`).
Tracing out the bits leaves `∑_d K_d ρ K_dᴴ`, since every bit `< nBits` is written exactly once
(`bitsOk_complete`). The existing semantics is unchanged.
-/

@[expose] public section

noncomputable section

namespace CQRV

open Matrix
open scoped Kronecker MState

/-- PHASE2_SPEC §C.4 (1) — the extended register: the quantum register and the `m` classical bits. -/
abbrev XReg (n a m : ℕ) := (Reg n × Reg a) × Reg m

/-- The all-zero bit assignment. -/
def zeroBits (m : ℕ) : Reg m := fun _ => false

theorem zeroBits_def (m : ℕ) : zeroBits m = fun _ => false := rfl

/-! ## Block operators on `X × Reg m` -/

section Blocks

variable (m : ℕ) {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem kronecker_sum {ι : Type} [Fintype ι] (A : Matrix X X ℂ) (S : ι → Matrix (Reg m) (Reg m) ℂ) :
    A ⊗ₖ (∑ i, S i) = ∑ i, A ⊗ₖ S i := by
  ext ⟨x, c⟩ ⟨x', c'⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

omit [Fintype X] [DecidableEq X] in
theorem sum_kronecker {ι : Type} [Fintype ι] (A : ι → Matrix X X ℂ) (S : Matrix (Reg m) (Reg m) ℂ) :
    (∑ i, A i) ⊗ₖ S = ∑ i, A i ⊗ₖ S := by
  ext ⟨x, c⟩ ⟨x', c'⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- `∑_c B_c ⊗ |f c⟩⟨c|`: the operator that acts by `B_c` on the block of bit assignment `c` and moves
the block to `f c`. -/
def blockOp (B : Reg m → Matrix X X ℂ) (f : Reg m → Reg m) : Matrix (X × Reg m) (X × Reg m) ℂ :=
  ∑ c, B c ⊗ₖ Matrix.single (f c) c (1 : ℂ)

/-- `∑_d A_d ⊗ |d⟩⟨d|`: a block-diagonal matrix (a classical-quantum state when the `A_d` are
positive). -/
def diagBlocks (A : Reg m → Matrix X X ℂ) : Matrix (X × Reg m) (X × Reg m) ℂ :=
  ∑ d, A d ⊗ₖ Matrix.single d d (1 : ℂ)

omit [Fintype X] in
theorem diagBlocks_one : diagBlocks m (fun _ : Reg m => (1 : Matrix X X ℂ)) = 1 := by
  rw [diagBlocks, ← kronecker_sum, Matrix.sum_single_one, Matrix.one_kronecker_one]

omit [Fintype X] [DecidableEq X] in
theorem blockOp_conjTranspose (B : Reg m → Matrix X X ℂ) (f : Reg m → Reg m) :
    (blockOp m B f)ᴴ = ∑ c, (B c)ᴴ ⊗ₖ Matrix.single c (f c) (1 : ℂ) := by
  simp only [blockOp, Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_single, star_one]

omit [DecidableEq X] in
theorem blockOp_mul_block (B : Reg m → Matrix X X ℂ) (f : Reg m → Reg m) (A : Matrix X X ℂ) (d : Reg m) :
    blockOp m B f * (A ⊗ₖ Matrix.single d d (1 : ℂ)) = (B d * A) ⊗ₖ Matrix.single (f d) d 1 := by
  simp only [blockOp, Finset.sum_mul, ← Matrix.mul_kronecker_mul]
  rw [Finset.sum_eq_single d]
  · rw [Matrix.single_mul_single_same, one_mul]
  · intro c _ hc
    rw [Matrix.single_mul_single_of_ne _ _ _ _ hc, Matrix.kronecker_zero]
  · intro h; exact absurd (Finset.mem_univ d) h

omit [DecidableEq X] in
theorem block_mul_blockOp_conjTranspose (B : Reg m → Matrix X X ℂ) (f : Reg m → Reg m)
    (A : Matrix X X ℂ) (d : Reg m) :
    (A ⊗ₖ Matrix.single (f d) d (1 : ℂ)) * (blockOp m B f)ᴴ = (A * (B d)ᴴ) ⊗ₖ Matrix.single (f d) (f d) 1 := by
  rw [blockOp_conjTranspose]
  simp only [Finset.mul_sum, ← Matrix.mul_kronecker_mul]
  rw [Finset.sum_eq_single d]
  · rw [Matrix.single_mul_single_same, one_mul]
  · intro c _ hc
    rw [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hc), Matrix.kronecker_zero]
  · intro h; exact absurd (Finset.mem_univ d) h

omit [DecidableEq X] in
/-- A block operator conjugates a block-diagonal matrix block by block and relabels the blocks. -/
theorem blockOp_conj (B : Reg m → Matrix X X ℂ) (f : Reg m → Reg m) (A : Reg m → Matrix X X ℂ) :
    blockOp m B f * diagBlocks m A * (blockOp m B f)ᴴ =
      ∑ d, (B d * A d * (B d)ᴴ) ⊗ₖ Matrix.single (f d) (f d) (1 : ℂ) := by
  simp only [diagBlocks, Finset.mul_sum, Finset.sum_mul, blockOp_mul_block,
    block_mul_blockOp_conjTranspose]

omit [DecidableEq X] in
/-- `(blockOp B f)ᴴ (blockOp B' f) = ∑_c B_cᴴ B'_c ⊗ |c⟩⟨c|` when `f` is injective. -/
theorem blockOp_conjTranspose_mul (B B' : Reg m → Matrix X X ℂ) {f : Reg m → Reg m}
    (hf : Function.Injective f) :
    (blockOp m B f)ᴴ * blockOp m B' f = ∑ c, ((B c)ᴴ * B' c) ⊗ₖ Matrix.single c c (1 : ℂ) := by
  rw [blockOp_conjTranspose]
  simp only [blockOp, Finset.sum_mul, Finset.mul_sum, ← Matrix.mul_kronecker_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c]
  · rw [Matrix.single_mul_single_same, one_mul]
  · intro c' _ hc'
    rw [Matrix.single_mul_single_of_ne _ _ _ _ (fun h => hc' (hf h)), Matrix.kronecker_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

omit [Fintype X] [DecidableEq X] in
/-- The partial trace over the bits of a block-diagonal matrix is the sum of the blocks. -/
theorem traceRight_diagBlocks (A : Reg m → Matrix X X ℂ) : (diagBlocks m A).traceRight = ∑ d, A d := by
  ext x x'
  simp [Matrix.traceRight, diagBlocks, Matrix.sum_apply, Matrix.single_apply]

omit [Fintype X] [DecidableEq X] in
/-- Reindexing the blocks by an involution of the bit assignments. -/
theorem sum_block_reindex (σ : Reg m → Reg m) (hσ : Function.Involutive σ) (F : Reg m → Matrix X X ℂ) :
    ∑ d, F d ⊗ₖ Matrix.single (σ d) (σ d) (1 : ℂ) = ∑ d, F (σ d) ⊗ₖ Matrix.single d d (1 : ℂ) := by
  rw [← Equiv.sum_comp hσ.toPerm (fun d => F (σ d) ⊗ₖ Matrix.single d d (1 : ℂ))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Function.Involutive.coe_toPerm, hσ d]

end Blocks

/-! ## Bits -/

section Bits

variable (m : ℕ)

/-- Flip classical bit `j` (the identity for `j ≥ m`, which `Circuit.WF` excludes). -/
def flipBitN (j : ℕ) : Reg m → Reg m := if h : j < m then flipBit ⟨j, h⟩ else id

theorem flipBitN_involutive (j : ℕ) : Function.Involutive (flipBitN m j) := by
  unfold flipBitN
  split_ifs
  · exact flipBit_involutive _
  · exact fun _ => rfl

theorem flipBitN_of_lt {j : ℕ} (hj : j < m) (d : Reg m) : flipBitN m j d = flipBit ⟨j, hj⟩ d := by
  simp [flipBitN, hj]

theorem bitVal_of_lt {j : ℕ} (hj : j < m) (d : Reg m) : bitVal d j = d ⟨j, hj⟩ := by
  simp [bitVal, hj]

theorem bitVal_flipBit_self {j : ℕ} (hj : j < m) (d : Reg m) :
    bitVal (flipBit ⟨j, hj⟩ d) j = !bitVal d j := by
  simp [bitVal, hj, flipBit]

theorem bitVal_flipBit_ne {j k : ℕ} (hj : j < m) (hkj : k ≠ j) (d : Reg m) :
    bitVal (flipBit ⟨j, hj⟩ d) k = bitVal d k := by
  by_cases hk : k < m
  · simp [bitVal, hk, flipBit, Fin.ext_iff, hkj]
  · simp [bitVal, hk]

/-- `supp d ⊆ W`: every bit set in `d` has been written. -/
def padOk (W : List ℕ) (d : Reg m) : Prop := ∀ k : Fin m, d k = true → (k : ℕ) ∈ W

instance (W : List ℕ) : DecidablePred (padOk m W) := fun _ => by unfold padOk; infer_instance

theorem padOk_nil_iff (d : Reg m) : padOk m [] d ↔ d = zeroBits m := by
  constructor
  · intro h; funext k
    cases hk : d k
    · rfl
    · exact absurd (h k hk) (List.not_mem_nil)
  · rintro rfl k hk; cases hk

theorem padOk_of_complete {W : List ℕ} (hW : ∀ k, k < m → k ∈ W) (d : Reg m) : padOk m W d :=
  fun k _ => hW k k.isLt

/-- Appending a bit `j` that `d` does not have does not change `padOk`. -/
theorem padOk_append_of_false {W : List ℕ} {j : ℕ} (hj : j < m) {d : Reg m} (hd : d ⟨j, hj⟩ = false) :
    padOk m (W ++ [j]) d ↔ padOk m W d := by
  constructor
  · intro h k hk
    rcases List.mem_append.1 (h k hk) with hkW | hkj
    · exact hkW
    · exfalso
      have : k = ⟨j, hj⟩ := Fin.ext (List.mem_singleton.1 hkj)
      rw [this, hd] at hk; cases hk
  · intro h k hk; exact List.mem_append_left _ (h k hk)

/-- A `d` with bit `j ∉ W` set is not supported in `W`. -/
theorem not_padOk_of_true {W : List ℕ} {j : ℕ} (hj : j < m) (hjW : j ∉ W) {d : Reg m}
    (hd : d ⟨j, hj⟩ = true) : ¬ padOk m W d :=
  fun h => hjW (h ⟨j, hj⟩ hd)

/-- With bit `j ∉ W` set in `d`: `d` is supported in `W ++ [j]` iff `d` with bit `j` cleared is
supported in `W`. -/
theorem padOk_append_iff_flip {W : List ℕ} {j : ℕ} (hj : j < m) {d : Reg m} (hd : d ⟨j, hj⟩ = true) :
    padOk m (W ++ [j]) d ↔ padOk m W (flipBit ⟨j, hj⟩ d) := by
  constructor
  · intro h k hk
    by_cases hkj : k = ⟨j, hj⟩
    · subst hkj; simp [flipBit, hd] at hk
    · rw [flipBit, Function.update_of_ne hkj] at hk
      rcases List.mem_append.1 (h k hk) with hkW | hkj'
      · exact hkW
      · exact absurd (Fin.ext (List.mem_singleton.1 hkj')) hkj
  · intro h k hk
    by_cases hkj : k = ⟨j, hj⟩
    · subst hkj; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    · exact List.mem_append_left _ (h k (by rw [flipBit, Function.update_of_ne hkj]; exact hk))

end Bits

/-! ## The step channels -/

section Steps

variable (n a m : ℕ)

/-- PHASE2_SPEC §C.4 (1) — the Kraus operators of one gate on the extended register, indexed by
`Bool`: for `measure q → j` the two operators `P_{q=v} ⊗ X_j^v`; for every other gate the single
operator `∑_c gateK c g ⊗ |c⟩⟨c|` (at `true`; `0` at `false`) — `Ad(gateU g ⊗ 1)` for a plain gate,
the controlled unitary for `ifBit`. -/
def stepK : Gate → Bool → Matrix (XReg n a m) (XReg n a m) ℂ
  | .measure q j, true => blockOp m (fun _ => projMat n a q true) (flipBitN m j)
  | .measure q _, false => blockOp m (fun _ => projMat n a q false) id
  | g, true => blockOp m (fun c => gateK n a c g) id
  | _, false => 0

/-- Every branch operator of a non-measurement gate is unitary. -/
theorem gateK_conjTranspose_mul {c : Reg m} {g : Gate} (hg : ∀ q j, g ≠ .measure q j) :
    (gateK n a c g)ᴴ * gateK n a c g = 1 := by
  have hU : ∀ u : Gate, (gateU n a u)ᴴ * gateU n a u = 1 := fun u => by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (gateU_mem_unitaryGroup n a u)
  cases g with
  | measure q j => exact absurd rfl (hg q j)
  | ifBit j u =>
    simp only [gateK]
    split_ifs
    · exact hU u
    · simp
  | _ => exact hU _

theorem stepK_complete_of_unitary (g : Gate) (hg : ∀ q j, g ≠ .measure q j)
    (hKt : stepK n a m g true = blockOp m (fun c => gateK n a c g) id)
    (hKf : stepK n a m g false = 0) :
    ∑ v, (stepK n a m g v)ᴴ * stepK n a m g v = 1 := by
  rw [Fintype.sum_bool, hKt, hKf]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, add_zero]
  rw [blockOp_conjTranspose_mul _ _ _ Function.injective_id]
  simp only [gateK_conjTranspose_mul n a m hg]
  exact diagBlocks_one m

/-- PHASE2_SPEC §C.4 (1) — **the step operators are Kraus-complete on every input**: for a unitary
gate `∑_c 1 ⊗ |c⟩⟨c| = 1`; for a measurement `(P₀ + P₁) ⊗ 1 = 1`. -/
theorem stepK_complete (g : Gate) : ∑ v, (stepK n a m g v)ᴴ * stepK n a m g v = 1 := by
  cases g with
  | measure q j =>
    rw [Fintype.sum_bool]
    simp only [stepK]
    rw [blockOp_conjTranspose_mul _ _ _ (flipBitN_involutive m j).injective,
      blockOp_conjTranspose_mul _ _ _ Function.injective_id, ← Finset.sum_add_distrib]
    simp only [projMat_conjTranspose_mul, ← Matrix.add_kronecker]
    have h01 : projMat n a q true + projMat n a q false = 1 := by
      simpa using projMat_add_not n a q true
    rw [h01]
    exact diagBlocks_one m
  | ifBit j u => exact stepK_complete_of_unitary n a m _ (fun _ _ h => by cases h) rfl rfl
  | _ => exact stepK_complete_of_unitary n a m _ (fun _ _ h => by cases h) rfl rfl

/-- PHASE2_SPEC §C.4 (1) — **the step channel** of one gate on the extended register. -/
def stepChan (g : Gate) : CPTPMap (XReg n a m) (XReg n a m) :=
  CPTPMap.of_kraus_CPTPMap (stepK n a m g) (stepK_complete n a m g)

/-- The step channels of a gate list, in order. -/
def stepList (gs : List Gate) : List (CPTPMap (XReg n a m) (XReg n a m)) := gs.map (stepChan n a m)

/-- PHASE2_SPEC §C.4 (1) — **`stepsOf gs`**: the composition of the step channels, first gate first. -/
def stepsOf (gs : List Gate) : CPTPMap (XReg n a m) (XReg n a m) := steps (stepList n a m gs)

theorem stepList_append (gs : List Gate) (g : Gate) :
    stepList n a m (gs ++ [g]) = stepList n a m gs ++ [stepChan n a m g] := by
  simp [stepList]

/-- A Kraus channel on a matrix: `∑_k K_k X K_kᴴ`. -/
theorem of_kraus_map_apply {κ D E : Type} [Fintype κ] [Fintype D] [DecidableEq D] [Fintype E]
    (K : κ → Matrix E D ℂ) (h : ∑ k, (K k)ᴴ * K k = 1) (X : Matrix D D ℂ) :
    (CPTPMap.of_kraus_CPTPMap K h).map X = ∑ k, K k * X * (K k)ᴴ := by
  change (∑ k, _ : MatrixMap _ _ ℂ) X = _
  rw [LinearMap.sum_apply]
  rfl

theorem steps_append_single {A : Type} [Fintype A] [DecidableEq A] (L : List (CPTPMap A A))
    (Φ : CPTPMap A A) : steps (L ++ [Φ]) = Φ ∘ₘ steps L := by
  rw [steps_append, steps_cons, steps_nil, CPTPMap.id_compose]

/-- The block of the bit assignment `d` after the prefix `gs` with written bits `W`:
`[supp d ⊆ W] · K_d ρ K_dᴴ`. -/
def branch (gs : List Gate) (W : List ℕ) (ρ : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) (d : Reg m) :
    Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  if padOk m W d then krausOps n a m gs d * ρ * (krausOps n a m gs d)ᴴ else 0

theorem ancZero_m_eq_single : (ancZero m).m = Matrix.single (zeroBits m) (zeroBits m) (1 : ℂ) := by
  ext i j
  rw [ancZero_m_apply, Matrix.single_apply, zeroBits_def]
  by_cases h : i = (fun _ => false) ∧ j = (fun _ => false)
  · simp [h.1, h.2]
  · have h' : ¬ ((fun _ : Fin m => false) = i ∧ (fun _ : Fin m => false) = j) :=
      fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    simp [h, h']

/-- The matrix of the partial trace of a state. -/
theorem _root_.MState.traceRight_m {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂]
    [DecidableEq d₂] (σ : MState (d₁ × d₂)) : σ.traceRight.m = σ.m.traceRight := by
  simp only [MState.m, MState.traceRight_M, HermitianMat.traceRight_mat]

/-- PHASE2_SPEC §C.4 (1), the invariant: after the prefix `gs` (obeying the bit discipline from no
written bit), the step semantics on `ρ ⊗ |0⟩⟨0|` is the block-diagonal matrix of the branches
supported in the written bits. -/
theorem stepsOf_map (gs : List Gate) (h : Circuit.bitsOkFrom m [] gs = true)
    (ρ : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) :
    (stepsOf n a m gs).map (ρ ⊗ₖ Matrix.single (zeroBits m) (zeroBits m) (1 : ℂ)) =
      diagBlocks m (branch n a m gs (Circuit.written gs) ρ) := by
  induction gs using List.reverseRecOn with
  | nil =>
    simp only [stepsOf, stepList, List.map_nil, steps_nil, CPTPMap.id_map, LinearMap.id_apply,
      diagBlocks, branch, Circuit.written, List.flatMap_nil, krausOps, Matrix.conjTranspose_one,
      Matrix.mul_one, Matrix.one_mul]
    rw [Finset.sum_eq_single (zeroBits m)]
    · simp [(padOk_nil_iff m _).2 rfl]
    · intro d _ hd
      have hp : ¬ padOk m [] d := fun hp => hd ((padOk_nil_iff m d).1 hp)
      simp [hp]
    · intro h; exact absurd (Finset.mem_univ _) h
  | append_singleton gs g ih =>
    rw [bitsOkFrom_append, Bool.and_eq_true, List.nil_append] at h
    obtain ⟨h1, hg⟩ := h
    have ih := ih h1
    simp only [stepsOf, stepList_append, steps_append_single] at ih ⊢
    change (stepChan n a m g).map ((steps (stepList n a m gs)).map _) = _
    rw [ih, stepChan, of_kraus_map_apply, written_append]
    have hinv := (kraus_invariant n a m gs h1).1
    cases g with
    | measure q j =>
      simp only [Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      obtain ⟨hj, hjW⟩ := hg
      rw [← Bool.not_eq_true, List.contains_iff_mem] at hjW
      rw [Fintype.sum_bool]
      simp only [stepK, blockOp_conj, id_eq]
      rw [sum_block_reindex m (flipBitN m j) (flipBitN_involutive m j), ← Finset.sum_add_distrib]
      simp only [diagBlocks, Gate.writes, ← Matrix.add_kronecker]
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp only [branch, krausOps_append, gateK, flipBitN_of_lt m hj, bitVal_of_lt m hj,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hK : krausOps n a m gs (flipBit ⟨j, hj⟩ d) = krausOps n a m gs d :=
        hinv _ _ fun k hk => bitVal_flipBit_ne m hj (fun e => hjW (e ▸ hk)) d
      cases hd : d ⟨j, hj⟩
      · have h2 : ¬ padOk m (Circuit.written gs) (flipBit ⟨j, hj⟩ d) :=
          not_padOk_of_true m hj hjW (by simp [flipBit, hd])
        simp only [h2, ite_false, padOk_append_of_false m hj hd]
        split_ifs <;> simp [Matrix.mul_assoc]
      · have h1' : ¬ padOk m (Circuit.written gs) d := not_padOk_of_true m hj hjW hd
        simp only [h1', ite_false, padOk_append_iff_flip m hj hd, hK]
        split_ifs <;> simp [Matrix.mul_assoc]
    | _ =>
      rw [Fintype.sum_bool]
      simp only [stepK, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
      rw [blockOp_conj]
      simp only [diagBlocks, Gate.writes, List.append_nil, id_eq]
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp only [branch, krausOps_append, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      split_ifs <;> simp [Matrix.mul_assoc]

/-! ## Every bit is written exactly once -/

theorem written_nodup_of_bitsOkFrom (W : List ℕ) (gs : List Gate)
    (h : Circuit.bitsOkFrom m W gs = true) :
    (Circuit.written gs).Nodup ∧ ∀ j ∈ Circuit.written gs, j ∉ W := by
  induction gs generalizing W with
  | nil => simp [Circuit.written]
  | cons g gs ih =>
    simp only [Circuit.bitsOkFrom, Bool.and_eq_true] at h
    obtain ⟨hnd, hW⟩ := ih _ h.2
    cases g with
    | measure q j =>
      have hg := h.1
      simp only [Gate.bitOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
      rw [← Bool.not_eq_true, List.contains_iff_mem] at hg
      simp only [Circuit.written, List.flatMap_cons, Gate.writes, List.singleton_append,
        List.nodup_cons]
      refine ⟨⟨fun hj => hW j hj (List.mem_append_right _ (List.mem_singleton.2 rfl)), hnd⟩, ?_⟩
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hg.2
      · exact fun hkW => hW k hk (List.mem_append_left _ hkW)
    | _ =>
      simp only [Gate.writes, List.append_nil] at hW
      simpa [Circuit.written, Gate.writes] using And.intro hnd hW

/-- Report §9.1.1 — under the bit discipline every bit `k < nBits` is written (the written bits
are distinct, all `< nBits`, and there are `nBits` of them). -/
theorem bitsOk_complete (C : Circuit) (h : C.bitsOk = true) :
    ∀ k, k < C.nBits → k ∈ Circuit.written C.gates := by
  have hnd := (written_nodup_of_bitsOkFrom C.nBits [] C.gates h).1
  have hlt := (bitsOkFrom_mono le_rfl [] C.gates h).2
  have hsub : (Circuit.written C.gates).toFinset ⊆ Finset.range C.nBits :=
    fun k hk => Finset.mem_range.2 (hlt k (List.mem_toFinset.1 hk))
  have hcard : (Finset.range C.nBits).card ≤ (Circuit.written C.gates).toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd]
    exact le_of_eq rfl
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro k hk
  exact List.mem_toFinset.1 (heq ▸ Finset.mem_range.2 hk)

/-! ## The theorem -/

/-- PHASE2_SPEC §C.4 (1) — **`channelDenote_eq_steps`**: for a well-formed circuit,
`channelDenote n a C ρ = traceRight (stepsOf C.gates (ρ ⊗ |0…0⟩⟨0…0|))` — the branch semantics is
the step semantics on the extended register with the bits traced out. -/
theorem channelDenote_eq_steps (C : Circuit) (hC : C.WF) (ρ : MState (Reg n × Reg a)) :
    channelDenote n a C ρ =
      CPTPMap.traceRight (d₁ := Reg n × Reg a) (d₂ := Reg C.nBits)
        (stepsOf n a C.nBits C.gates (ρ ⊗ᴹ ancZero C.nBits)) := by
  apply MState.ext_m
  rw [channelDenote_m_of_bitsOk n a hC.bitsOk, CPTPMap.traceRight_eq_MState_traceRight,
    MState.traceRight_m]
  have hσ : (stepsOf n a C.nBits C.gates (ρ ⊗ᴹ ancZero C.nBits)).m =
      diagBlocks C.nBits (branch n a C.nBits C.gates (Circuit.written C.gates) ρ.m) := by
    rw [CPTPMap.mat_coe_eq_apply_mat,
      show (ρ ⊗ᴹ ancZero C.nBits).m = ρ.m ⊗ₖ (ancZero C.nBits).m from rfl, ancZero_m_eq_single]
    exact stepsOf_map n a C.nBits C.gates hC.bitsOk ρ.m
  rw [hσ, traceRight_diagBlocks]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [branch, padOk_of_complete C.nBits (bitsOk_complete C hC.bitsOk) d]

/-! ## The preparation channel `ρ ↦ ρ ⊗ |0…0⟩⟨0…0|` -/

/-- The isometry `|x⟩ ↦ |x⟩ ⊗ |0…0⟩`. -/
def embedMat : Matrix (XReg n a m) (Reg n × Reg a) ℂ :=
  Matrix.of fun p x => if p.1 = x ∧ p.2 = zeroBits m then 1 else 0

theorem embedMat_conjTranspose_mul : (embedMat n a m)ᴴ * embedMat n a m = 1 := by
  ext x x'
  rw [Matrix.mul_apply, Finset.sum_eq_single (x, zeroBits m)]
  · simp [embedMat, Matrix.one_apply]
  · rintro ⟨y, c⟩ _ hne
    have : ¬ (y = x ∧ c = zeroBits m) := fun h => hne (by rw [h.1, h.2])
    simp [embedMat, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- PHASE2_SPEC §C.4 (1) — **`withBits`**: the channel `ρ ↦ ρ ⊗ |0…0⟩⟨0…0|` that adjoins the
classical register in the all-zero state. -/
def withBits : CPTPMap (Reg n × Reg a) (XReg n a m) :=
  CPTPMap.of_kraus_CPTPMap (fun _ : Unit => embedMat n a m)
    (by rw [Fintype.sum_unique]; exact embedMat_conjTranspose_mul n a m)

theorem embedMat_mul_apply (ρ : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) (x y' : Reg n × Reg a)
    (c : Reg m) : (embedMat n a m * ρ) (x, c) y' = if c = zeroBits m then ρ x y' else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · simp [embedMat]
  · intro y _ hy; simp [embedMat, Ne.symm hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem embedMat_conj_apply (ρ : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) (x x' : Reg n × Reg a)
    (c c' : Reg m) :
    (embedMat n a m * ρ * (embedMat n a m)ᴴ) (x, c) (x', c') =
      if c = zeroBits m ∧ c' = zeroBits m then ρ x x' else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x']
  · rw [embedMat_mul_apply]
    simp only [embedMat, Matrix.conjTranspose_apply, Matrix.of_apply, true_and]
    split_ifs <;> simp_all
  · intro y' _ hy'
    rw [embedMat_mul_apply]
    simp [embedMat, Ne.symm hy']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem withBits_m (ρ : MState (Reg n × Reg a)) :
    (withBits n a m ρ).m = ρ.m ⊗ₖ Matrix.single (zeroBits m) (zeroBits m) (1 : ℂ) := by
  rw [CPTPMap.mat_coe_eq_apply_mat, withBits, of_kraus_map_apply, Fintype.sum_unique]
  ext ⟨x, c⟩ ⟨x', c'⟩
  rw [embedMat_conj_apply, Matrix.kronecker_apply, Matrix.single_apply]
  by_cases h : c = zeroBits m ∧ c' = zeroBits m
  · simp [h.1, h.2]
  · have h' : ¬ (zeroBits m = c ∧ zeroBits m = c') := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
    simp [h, h']

theorem withBits_apply (ρ : MState (Reg n × Reg a)) : withBits n a m ρ = ρ ⊗ᴹ ancZero m :=
  MState.ext_m (by
    rw [withBits_m]
    change _ = ρ.m ⊗ₖ (ancZero m).m
    rw [ancZero_m_eq_single])

/-- PHASE2_SPEC §C.4 (1) — **`channelDenote_eq_steps_chan`**, the channel form:
`channelDenote n a C = traceRight ∘ stepsOf C.gates ∘ withBits`. -/
theorem channelDenote_eq_steps_chan (C : Circuit) (hC : C.WF) :
    channelDenote n a C =
      CPTPMap.traceRight ∘ₘ stepsOf n a C.nBits C.gates ∘ₘ withBits n a C.nBits := by
  ext1 ρ
  rw [CPTPMap.compose_eq, CPTPMap.compose_eq, withBits_apply]
  exact channelDenote_eq_steps n a C hC ρ

end Steps

end CQRV

end
