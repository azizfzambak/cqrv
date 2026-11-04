module

public import CQRV.Synthesis.Counting
public import CQRV.Grover.Restore
public import CQRV.Circuit.QFTCorrect

/-!
# CQRV.Circuit.CountingCorrect

PHASE2_SPEC.md §A.3 as amended before Stage 19 (amendments (1)–(5)); report §6.2.4, §6.3.2
(Lemma 6.3.2), §8.2; docs/tasks/STAGE19_TASK.md B2 (lemmas), B4 (Stage 19b) — the counting circuit
restores its ancillae, **in the circuit's own factors**: every block of `countingCircuit` restores
its ancillae with the exact unitary its gate list denotes, and the whole circuit with the product
of those factors in program order. Nothing here is a global-phase argument: `AncRestore.congr` is
not used (amendment (2): inside a controlled block a sign is a relative phase).

* `Gate.shiftData` (B2): `isUnitary_shiftData`, `qubitsOk_shiftData` (`qubitsOk m g → qubitsOk
  (k + m) (g.shiftData k)`), `dataOnly_shiftData`.
* The data-only layers: `unitaryDenote_hUpTo` / `unitaryDenote_xUpTo` (the local `key`s of
  `unitaryDenote_hLayer` / `unitaryDenote_xLayer` as lemmas of their own: the first `k`
  Hadamards / `X` of a register of `N ≥ k` qubits denote `hUpTo N k ⊗ 1` / `flipUpToMat N k ⊗ 1`),
  `dataMat N gs` (the data-register matrix of a gate list, read off `unitaryDenote N 0`) and
  `unitaryDenote_dataOnly : unitaryDenote N a gs = dataMat N gs ⊗ₖ 1` for a unitary gate list all
  of whose operands are data qubits (`Gate.dataOnly`; the hypothesis the task text's statement
  lacks — `qubitsOk` admits ancilla operands, and `[h (anc 0)]` is a counterexample without it —
  and the register-range hypothesis `qubitsOk` is not needed: a data qubit outside the register
  acts as the identity on both sides), with `dataMat_mem_unitaryGroup`. It covers the phase fix
  `z (data (n+j))` and the shifted inverse (A)QFT.
* `Block n C U`: `C.nData = n`, `C.WF`, and `AncRestore n a C U` on every ancilla register
  `a ≥ C.nAnc`; closed under `Circuit.append` (`AncRestore.comp`, `Circuit.WF_append`,
  `nAnc_append`) and under `r ≥ 1` copies (`ancRestore_foldl`).
* The factors (amendment (5)): `preU` / `postU` (the `hUpTo` / `flipUpTo` unitaries of the
  diffusion's wrappers on `Reg (n+m)`), `cdiffU j = postU · U_{P_all ∧ c_j} · preU`,
  `cgU j = zU j · cdiffU j · U_{P ∧ c_j}` (Lemma 6.3.2 for the `withControl` networks, in either
  uncomputation mode: `lemma_6_3_2_mode_of_le`), `powersU = ∏_j cgU j ^ (2^j)` in program order,
  `qftInvU` the `dataMat` of the shifted inverse (A)QFT, and

  `countingCircuit_ancRestore_raw : C.WF ∧ AncRestore (n+m) C.nAnc C (qftInvU · powersU · H^{⊗(n+m)})`.

  The tensor form `U_count = liftP (QFT†_m) · ctrlPow G · H^{⊗(n+m)}` of these factors is Stage 19c.
Import discipline (PHASE2_SPEC.md §A.8 item 6): this module imports Physlib (through
`CQRV.Grover.Restore`) and is not in the `cqr` closure; a list that follows a newline is
parenthesised.
-/

@[expose] public section

namespace CQRV.Counting

open CQRV CQRV.Synthesis CQRV.Grover Matrix
open scoped MState Kronecker

/-! ## B2 — the lemmas of `Gate.shiftData` -/

/-- Every operand of the gate is a data qubit (the hypothesis of `unitaryDenote_dataOnly`). -/
def _root_.CQRV.Gate.dataOnly (g : Gate) : Bool :=
  g.qubits.all fun q => match q with | .data _ => true | .anc _ => false

theorem _root_.CQRV.Gate.isUnitary_shiftData (k : ℕ) (g : Gate) :
    (g.shiftData k).isUnitary = g.isUnitary := by
  cases g <;> rfl

theorem _root_.CQRV.Qubit.shiftData_inj {k : ℕ} {u v : Qubit} (h : u.shiftData k = v.shiftData k) :
    u = v := by
  cases u <;> cases v <;> simp_all [Qubit.shiftData]

theorem bne_shiftData (k : ℕ) (u v : Qubit) : (u.shiftData k != v.shiftData k) = (u != v) := by
  by_cases h : u = v
  · subst h
    simp
  · have h' : u.shiftData k ≠ v.shiftData k := fun e => h (Qubit.shiftData_inj e)
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
    exact ⟨fun _ => h, fun _ => h'⟩

/-- The gate `qubitsOk` inspects for distinct operands (the controlled gate under `ifBit`). -/
def innerGate : Gate → Gate
  | .ifBit _ g => g
  | g => g

/-- The distinct-operand clause of `qubitsOk`. -/
def distinctOps : Gate → Bool
  | .cnot u v | .cz u v | .cp _ _ u v => u != v
  | _ => true

theorem qubitsOk_eq (N : ℕ) (g : Gate) :
    g.qubitsOk N = (g.qubits.all (fun q => match q with
      | .data i => decide (i < N) | .anc _ => true) && distinctOps (innerGate g)) := by
  cases g <;> rfl

theorem innerGate_shiftData (k : ℕ) (g : Gate) :
    innerGate (g.shiftData k) = (innerGate g).shiftData k := by
  cases g <;> rfl

theorem distinctOps_shiftData (k : ℕ) (g : Gate) : distinctOps (g.shiftData k) = distinctOps g := by
  cases g <;> simp only [distinctOps, Gate.shiftData, bne_shiftData]

/-- B2 — a gate on `x[0..m)` shifted by `k` is on `x[0..k+m)` (indices in range, operands still
distinct). -/
theorem _root_.CQRV.Gate.qubitsOk_shiftData {m : ℕ} (k : ℕ) {g : Gate}
    (h : g.qubitsOk m = true) : (g.shiftData k).qubitsOk (k + m) = true := by
  rw [qubitsOk_eq] at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, by rw [innerGate_shiftData, distinctOps_shiftData]; exact h.2⟩
  rw [Gate.qubits_shiftData, List.all_map]
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have := h.1 q hq
  cases q with
  | data i =>
    simp only [Function.comp, Qubit.shiftData, decide_eq_true_eq] at this ⊢
    omega
  | anc i => rfl

theorem _root_.CQRV.Gate.dataOnly_shiftData (k : ℕ) (g : Gate) :
    (g.shiftData k).dataOnly = g.dataOnly := by
  unfold Gate.dataOnly
  rw [Gate.qubits_shiftData, List.all_map]
  congr 1
  funext q
  cases q <;> rfl

theorem _root_.CQRV.Gate.qubits_adjoint (g : Gate) : g.adjoint.qubits = g.qubits := by
  cases g <;> rfl

theorem _root_.CQRV.Gate.dataOnly_adjoint (g : Gate) : g.adjoint.dataOnly = g.dataOnly := by
  unfold Gate.dataOnly
  rw [Gate.qubits_adjoint]

theorem qftGates_dataOnly {m : ℕ} {g : Gate} (hg : g ∈ qftGates m) : g.dataOnly = true := by
  obtain ⟨j, -, hgj⟩ := mem_qftGates hg
  rcases mem_qftBlock hgj with rfl | ⟨i, -, rfl⟩ <;> rfl

/-! ## Kronecker products with the identity on the ancilla register -/

theorem kron_one_inj {N a : ℕ} {A B : Matrix (Reg N) (Reg N) ℂ} (u : Reg a)
    (h : A ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) = B ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) : A = B := by
  ext x y
  have := congrFun (congrFun h (x, u)) (y, u)
  simpa [Matrix.kroneckerMap_apply] using this

/-- A monomial matrix whose permutation and phases act on the data component only is a
Kronecker product with the identity. -/
theorem monoMat_prod_kron {N a : ℕ} (σ : Reg N → Reg N) (φ : Reg N → ℂ) :
    monoMat (fun s : Reg N × Reg a => (σ s.1, s.2)) (fun s => φ s.1) =
      monoMat σ φ ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  ext ⟨x, u⟩ ⟨y, v⟩
  simp only [monoMat_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : x = σ y <;> by_cases h2 : u = v <;> simp [h1, h2]

theorem monoMat_id_prod_kron {N a : ℕ} (φ : Reg N → ℂ) :
    monoMat id (fun s : Reg N × Reg a => φ s.1) =
      monoMat id φ ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  rw [← monoMat_prod_kron]
  rfl

theorem hMat_prod_kron {N a : ℕ} (b : Reg N → Bool) (f : Reg N → Reg N) :
    hMat (fun s : Reg N × Reg a => b s.1) (fun s => (f s.1, s.2)) =
      hMat b f ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  unfold hMat
  rw [Matrix.smul_kronecker, Matrix.add_kronecker, ← monoMat_prod_kron, ← monoMat_prod_kron]
  rfl

/-! ## Data-only gates -/

/-- `Qubit.get (.data i)` on the data register. -/
def getD {N : ℕ} (i : ℕ) (x : Reg N) : Bool := if h : i < N then x ⟨i, h⟩ else false

/-- `Qubit.flip (.data i)` on the data register. -/
def flipD {N : ℕ} (i : ℕ) (x : Reg N) : Reg N :=
  if h : i < N then Function.update x ⟨i, h⟩ (!x ⟨i, h⟩) else x

theorem get_data_eq (N a i : ℕ) :
    (Qubit.get (.data i) : Reg N × Reg a → Bool) = fun s => getD i s.1 := rfl

theorem flip_data_eq (N a i : ℕ) :
    (Qubit.flip (.data i) : Reg N × Reg a → Reg N × Reg a) = fun s => (flipD i s.1, s.2) := by
  funext ⟨x, u⟩
  by_cases h : i < N <;> simp [Qubit.flip, Qubit.set, Qubit.get, flipD, h]

/-- The CNOT permutation on the data register. -/
def cnotPermD {N : ℕ} (i j : ℕ) (x : Reg N) : Reg N := if getD i x then flipD j x else x

theorem cnotPerm_data_eq (N a i j : ℕ) :
    cnotPerm N a (.data i) (.data j) = fun s => (cnotPermD i j s.1, s.2) := by
  funext ⟨x, u⟩
  simp only [cnotPerm, get_data_eq, flip_data_eq, cnotPermD]
  split_ifs <;> rfl

/-- A unitary gate on data qubits only denotes `G ⊗ 1`, for a `G` independent of the ancilla
register. -/
theorem gateU_kron_of_dataOnly {N : ℕ} {g : Gate} (hu : g.isUnitary = true)
    (hd : g.dataOnly = true) :
    ∃ G : Matrix (Reg N) (Reg N) ℂ, ∀ a, gateU N a g = G ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  cases g with
  | h q =>
    cases q with
    | data i =>
      refine ⟨if i < N then hMat (getD i) (flipD i) else 1, fun a => ?_⟩
      by_cases hi : i < N
      · simp only [gateU, Qubit.inRange, hi, decide_true, ↓reduceIte, get_data_eq, flip_data_eq]
        exact hMat_prod_kron _ _
      · simp only [gateU, Qubit.inRange, hi, decide_false, Bool.false_eq_true, ↓reduceIte,
          Matrix.one_kronecker_one]
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | s q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then Complex.I else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then Complex.I else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | sdg q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then -Complex.I else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then -Complex.I else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | t q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then ω else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then ω else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | tdg q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then star ω else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then star ω else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | x q =>
    cases q with
    | data i =>
      exact ⟨monoMat (flipD i) (fun _ => 1), fun a => by
        simp only [gateU, flip_data_eq]
        exact monoMat_prod_kron (flipD i) (fun _ => 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | z q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then -1 else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then -1 else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cnot c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        refine ⟨if i = j then 1 else monoMat (cnotPermD i j) (fun _ => 1), fun a => ?_⟩
        by_cases hij : i = j
        · subst hij
          simp only [gateU, ↓reduceIte, Matrix.one_kronecker_one]
        · have hne : Qubit.data i ≠ Qubit.data j := fun e => hij (by cases e; rfl)
          simp only [gateU, hne, hij, ↓reduceIte, cnotPerm_data_eq]
          exact monoMat_prod_kron (cnotPermD i j) (fun _ => 1)
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cz p q =>
    cases p with
    | data i =>
      cases q with
      | data j =>
        exact ⟨monoMat id (fun x => if getD i x && getD j x then -1 else 1), fun a => by
          simp only [gateU, get_data_eq]
          exact monoMat_id_prod_kron (fun x => if getD i x && getD j x then -1 else 1)⟩
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | measure q c => simp [Gate.isUnitary] at hu
  | ifBit c g => simp [Gate.isUnitary] at hu
  | alloc q => exact ⟨1, fun a => by rw [Matrix.one_kronecker_one]; rfl⟩
  | free q => exact ⟨1, fun a => by rw [Matrix.one_kronecker_one]; rfl⟩
  | p m k q =>
    cases q with
    | data i =>
      exact ⟨monoMat id (fun x => if getD i x then phaseOf m k else 1), fun a => by
        simp only [gateU, phaseMat, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x then phaseOf m k else 1)⟩
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cp m k c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        exact ⟨monoMat id (fun x => if getD i x && getD j x then phaseOf m k else 1), fun a => by
          simp only [gateU, get_data_eq]
          exact monoMat_id_prod_kron (fun x => if getD i x && getD j x then phaseOf m k else 1)⟩
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd

/-- A unitary data-only gate list denotes `D ⊗ 1`, for a `D` independent of the ancilla
register. -/
theorem unitaryDenote_kron_of_dataOnly {N : ℕ} (gs : List Gate)
    (hu : gs.all Gate.isUnitary = true) (hd : gs.all Gate.dataOnly = true) :
    ∃ D : Matrix (Reg N) (Reg N) ℂ, ∀ a,
      unitaryDenote N a gs = D ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  induction gs with
  | nil => exact ⟨1, fun a => by rw [unitaryDenote_nil, Matrix.one_kronecker_one]⟩
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hu hd
    obtain ⟨D, hD⟩ := ih hu.2 hd.2
    obtain ⟨G, hG⟩ := gateU_kron_of_dataOnly (N := N) hu.1 hd.1
    exact ⟨D * G, fun a => by
      rw [unitaryDenote, hD a, hG a, ← Matrix.mul_kronecker_mul, Matrix.one_mul]⟩

/-! ## `dataMat` -/

/-- B4 — the data-register matrix of a gate list: `unitaryDenote N 0 gs` read on the (one-point)
ancilla register `Reg 0`. -/
noncomputable def dataMat (N : ℕ) (gs : List Gate) : Matrix (Reg N) (Reg N) ℂ :=
  Matrix.of fun x y => unitaryDenote N 0 gs (x, reg0) (y, reg0)

theorem dataMat_apply (N : ℕ) (gs : List Gate) (x y : Reg N) :
    dataMat N gs x y = unitaryDenote N 0 gs (x, reg0) (y, reg0) := rfl

/-- Every matrix on `Reg N × Reg 0` is its `Reg 0`-restriction tensored with `1`. -/
theorem eq_kron_one_reg0 {N : ℕ} (M : Matrix (Reg N × Reg 0) (Reg N × Reg 0) ℂ) :
    M = (Matrix.of fun x y => M (x, reg0) (y, reg0)) ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  ext ⟨x, u⟩ ⟨y, v⟩
  obtain rfl := reg0_unique u
  obtain rfl := reg0_unique v
  simp [Matrix.kroneckerMap_apply]

theorem unitaryDenote_zero_eq (N : ℕ) (gs : List Gate) :
    unitaryDenote N 0 gs = dataMat N gs ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ) :=
  eq_kron_one_reg0 _

/-- B4 — `dataMat` is unitary: `unitaryDenote N 0 gs = dataMat ⊗ 1` is, and `Reg 0` is a
point. -/
theorem dataMat_mem_unitaryGroup (N : ℕ) (gs : List Gate) : dataMat N gs ∈ 𝐔[Reg N] := by
  have h := unitaryDenote_mem_unitaryGroup N 0 gs
  rw [unitaryDenote_zero_eq, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, ← Matrix.one_kronecker_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact kron_one_inj reg0 h

/-- B4 — a unitary gate list on data qubits only denotes `dataMat N gs ⊗ 1` on every ancilla
register. (The register-range hypothesis of the task text is not needed; the data-only
hypothesis is, see the header.) -/
theorem unitaryDenote_dataOnly {N a : ℕ} (gs : List Gate) (hu : gs.all Gate.isUnitary = true)
    (hd : gs.all Gate.dataOnly = true) :
    unitaryDenote N a gs = dataMat N gs ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  obtain ⟨D, hD⟩ := unitaryDenote_kron_of_dataOnly (N := N) gs hu hd
  have h0 : dataMat N gs = D := kron_one_inj reg0 (by rw [← unitaryDenote_zero_eq, hD 0])
  rw [hD a, h0]

/-- The unitary of a data-only gate list. -/
noncomputable def dataMatU (N : ℕ) (gs : List Gate) : 𝐔[Reg N] :=
  ⟨dataMat N gs, dataMat_mem_unitaryGroup N gs⟩

/-! ## The first `k` Hadamards / `X` of a larger register -/

/-- B4 — the `key` of `unitaryDenote_hLayer` as a lemma: the first `k ≤ N` Hadamards denote
`hUpTo N k ⊗ 1`. -/
theorem unitaryDenote_hUpTo (N a k : ℕ) (hk : k ≤ N) :
    unitaryDenote N a ((List.range k).map fun i => Gate.h (.data i)) =
      hUpTo N k ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  induction k with
  | zero => simp [unitaryDenote, hUpTo_zero]
  | succ k ih =>
    rw [List.range_succ, List.map_append, CQRV.unitaryDenote_append, List.map_singleton,
      show unitaryDenote N a [Gate.h (.data k)] = gateU N a (.h (.data k)) from Matrix.one_mul _,
      ih (by omega), gateU_h_data_mul (by omega)]

/-- `X` on the first `k` data qubits, as a matrix on `Reg N`. -/
noncomputable def flipUpToMat (N k : ℕ) : Matrix (Reg N) (Reg N) ℂ :=
  monoMat (flipUpTo k) (fun _ => 1)

theorem flipUpTo_involutive (N k : ℕ) : Function.Involutive (flipUpTo (n := N) k) := fun x => by
  funext i
  simp only [flipUpTo]
  split_ifs <;> simp

theorem flipUpToMat_mem_unitaryGroup (N k : ℕ) : flipUpToMat N k ∈ 𝐔[Reg N] :=
  monoMat_mem_unitaryGroup (flipUpTo_involutive N k) (fun _ => by simp)

/-- B4 — the `key` of `unitaryDenote_xLayer` as a lemma: the first `k ≤ N` `X` gates denote
`flipUpToMat N k ⊗ 1`. -/
theorem unitaryDenote_xUpTo (N a k : ℕ) (hk : k ≤ N) :
    unitaryDenote N a ((List.range k).map fun i => Gate.x (.data i)) =
      flipUpToMat N k ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  rw [flipUpToMat, ← monoMat_prod_kron]
  induction k with
  | zero =>
    rw [List.range_zero, List.map_nil, unitaryDenote_nil, ← monoMat_id_one]
    congr 1
  | succ k ih =>
    rw [List.range_succ, List.map_append, CQRV.unitaryDenote_append, List.map_singleton,
      show unitaryDenote N a [Gate.x (.data k)] = gateU N a (.x (.data k)) from Matrix.one_mul _,
      ih (by omega), gateU, monoMat_mul]
    congr 1
    · funext ⟨x, u⟩
      simp only [Function.comp_apply, Qubit.flip, Qubit.set, Qubit.get,
        show k < N by omega, ↓reduceDIte]
      congr 1
      funext i
      by_cases hi : i.val = k
      · obtain rfl : i = ⟨k, Nat.lt_of_succ_le hk⟩ := Fin.ext hi
        simp [flipUpTo]
      · have hi' : i ≠ ⟨k, by omega⟩ := fun h => hi (by rw [h])
        have : (i.val < k + 1) = (i.val < k) := propext (by omega)
        simp [flipUpTo, Function.update_of_ne hi', this]
    · funext s
      simp

theorem hUpTo_mem_unitaryGroup (N k : ℕ) (hk : k ≤ N) : hUpTo N k ∈ 𝐔[Reg N] := by
  have h := unitaryDenote_hUpTo N 0 k hk
  rw [unitaryDenote_zero_eq] at h
  rw [← kron_one_inj reg0 h]
  exact dataMat_mem_unitaryGroup _ _

/-- The unitary `H^{⊗k} ⊗ I` on `Reg N`, `k ≤ N`. -/
noncomputable def hUpToU (N k : ℕ) (hk : k ≤ N) : 𝐔[Reg N] := ⟨hUpTo N k, hUpTo_mem_unitaryGroup N k hk⟩

/-- The unitary `X^{⊗k} ⊗ I` on `Reg N`. -/
noncomputable def flipUpToU (N k : ℕ) : 𝐔[Reg N] := ⟨flipUpToMat N k, flipUpToMat_mem_unitaryGroup N k⟩

/-! ## Blocks -/

/-- A block of the counting circuit on the data register `Reg n`: well formed, on `n` data
qubits, restoring its ancillae with `U` on every ancilla register at least its own. -/
def Block (n : ℕ) (C : Circuit) (U : 𝐔[Reg n]) : Prop :=
  C.nData = n ∧ C.WF ∧ ∀ a, C.nAnc ≤ a → AncRestore n a C U

/-- Report §6.2.4 — blocks compose by the shifted append, the unitaries in program order. -/
theorem Block.append {n : ℕ} {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]} (h₁ : Block n C₁ U₁)
    (h₂ : Block n C₂ U₂) : Block n (C₁.append C₂) (U₂ * U₁) :=
  ⟨h₁.1, Circuit.WF_append (h₁.1.trans h₂.1.symm) h₁.2.1 h₂.2.1, fun a ha => by
    rw [nAnc_append, max_le_iff] at ha
    exact AncRestore.comp h₁.2.1.bitsOk h₂.2.1.bitsOk (h₁.2.2 a ha.1) (h₂.2.2 a ha.2)⟩

theorem nData_foldl_replicate (init it : Circuit) :
    ∀ r, ((List.replicate r it).foldl Circuit.append init).nData = init.nData
  | 0 => rfl
  | r + 1 => by
    rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact nData_foldl_replicate init it r

theorem WF_foldl_replicate {init it : Circuit} (hn : init.nData = it.nData) (hi : init.WF)
    (ht : it.WF) : ∀ r, ((List.replicate r it).foldl Circuit.append init).WF
  | 0 => hi
  | r + 1 => by
    rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Circuit.WF_append (by rw [nData_foldl_replicate]; exact hn)
      (WF_foldl_replicate hn hi ht r) ht

theorem nAnc_foldl_replicate (init it : Circuit) :
    ∀ r, 0 < r → ((List.replicate r it).foldl Circuit.append init).nAnc = max init.nAnc it.nAnc
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | r + 1, _ => by
    rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil, nAnc_append]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · rw [nAnc_foldl_replicate init it r hr, max_assoc, max_self]

/-- Report §6.2.4 — `r ≥ 1` copies of a block after a block (`ancRestore_foldl`). -/
theorem Block.foldl_replicate {n : ℕ} {init it : Circuit} {U V : 𝐔[Reg n]} (hi : Block n init U)
    (ht : Block n it V) (r : ℕ) (hr : 0 < r) :
    Block n ((List.replicate r it).foldl Circuit.append init) (V ^ r * U) :=
  ⟨by rw [nData_foldl_replicate]; exact hi.1,
   WF_foldl_replicate (hi.1.trans ht.1.symm) hi.2.1 ht.2.1 r,
   fun a ha => by
     rw [nAnc_foldl_replicate init it r hr, max_le_iff] at ha
     exact (ancRestore_foldl init it U V hi.2.1.bitsOk ht.2.1.bitsOk (hi.2.2 a ha.1)
       (ht.2.2 a ha.2) r).2⟩

/-- A unitary data-only layer is a block with its `dataMat`. -/
theorem block_dataOnly {N : ℕ} (gs : List Gate) (hu : gs.all Gate.isUnitary = true)
    (hq : gs.all (Gate.qubitsOk N) = true) (hd : gs.all Gate.dataOnly = true) :
    Block N ⟨N, gs⟩ (dataMatU N gs) :=
  ⟨rfl, dataLayer_WF N gs hu (List.all_eq_true.mp hq),
   fun _ _ => ancRestore_of_dataLayer gs hu hq _ (unitaryDenote_dataOnly gs hu hd)⟩

/-! ## The layers of the counting circuit on `Reg (n + m)` -/

theorem h_qubitsOk {N i : ℕ} (hi : i < N) : (Gate.h (.data i)).qubitsOk N = true := by
  simp [Gate.qubitsOk, Gate.qubits, hi]

theorem x_qubitsOk {N i : ℕ} (hi : i < N) : (Gate.x (.data i)).qubitsOk N = true := by
  simp [Gate.qubitsOk, Gate.qubits, hi]

/-- One gate on each of `x[0..n)` passes `qubitsOk N` for `n ≤ N`. -/
theorem onAll_qubitsOk_of_le {N n : ℕ} (hn : n ≤ N) (g : Qubit → Gate)
    (hg : ∀ i, i < N → (g (.data i)).qubitsOk N = true) :
    ∀ x ∈ Diffusion.onAll g n, x.qubitsOk N = true := by
  intro x hx
  simp only [Diffusion.onAll, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact hg i (by omega)

theorem pre_qubitsOk (n m : ℕ) :
    (Diffusion.onAll .h n ++ Diffusion.onAll .x n).all (Gate.qubitsOk (n + m)) = true := by
  rw [List.all_append, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨onAll_qubitsOk_of_le (Nat.le_add_right n m) _ fun i hi => h_qubitsOk hi,
    onAll_qubitsOk_of_le (Nat.le_add_right n m) _ fun i hi => x_qubitsOk hi⟩

theorem post_qubitsOk (n m : ℕ) :
    (Diffusion.onAll .x n ++ Diffusion.onAll .h n).all (Gate.qubitsOk (n + m)) = true := by
  rw [List.all_append, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨onAll_qubitsOk_of_le (Nat.le_add_right n m) _ fun i hi => x_qubitsOk hi,
    onAll_qubitsOk_of_le (Nat.le_add_right n m) _ fun i hi => h_qubitsOk hi⟩

/-- The diffusion prefix `H^{⊗n} X^{⊗n}` on the search register of `Reg (n+m)`: `X H`. -/
noncomputable def preU (n m : ℕ) : 𝐔[Reg (n + m)] :=
  flipUpToU (n + m) n * hUpToU (n + m) n (Nat.le_add_right n m)

/-- The diffusion suffix `X^{⊗n} H^{⊗n}` on the search register of `Reg (n+m)`: `H X`. -/
noncomputable def postU (n m : ℕ) : 𝐔[Reg (n + m)] :=
  hUpToU (n + m) n (Nat.le_add_right n m) * flipUpToU (n + m) n

theorem block_pre (n m : ℕ) :
    Block (n + m) ⟨n + m, Diffusion.onAll .h n ++ Diffusion.onAll .x n⟩ (preU n m) :=
  ⟨rfl, dataLayer_WF _ _ (pre_unitary n) (List.all_eq_true.mp (pre_qubitsOk n m)),
   fun a _ => ancRestore_of_dataLayer _ (pre_unitary n) (pre_qubitsOk n m) _ (by
     rw [CQRV.unitaryDenote_append, Diffusion.onAll, Diffusion.onAll,
       unitaryDenote_hUpTo _ _ _ (Nat.le_add_right n m),
       unitaryDenote_xUpTo _ _ _ (Nat.le_add_right n m), ← Matrix.mul_kronecker_mul,
       Matrix.one_mul]
     rfl)⟩

theorem block_post (n m : ℕ) :
    Block (n + m) ⟨n + m, Diffusion.onAll .x n ++ Diffusion.onAll .h n⟩ (postU n m) :=
  ⟨rfl, dataLayer_WF _ _ (post_unitary n) (List.all_eq_true.mp (post_qubitsOk n m)),
   fun a _ => ancRestore_of_dataLayer _ (post_unitary n) (post_qubitsOk n m) _ (by
     rw [CQRV.unitaryDenote_append, Diffusion.onAll, Diffusion.onAll,
       unitaryDenote_hUpTo _ _ _ (Nat.le_add_right n m),
       unitaryDenote_xUpTo _ _ _ (Nat.le_add_right n m), ← Matrix.mul_kronecker_mul,
       Matrix.one_mul]
     rfl)⟩

/-- The Hadamard layer on all `n + m` data qubits (`ancRestore_hLayer`). -/
theorem block_hLayer (n m : ℕ) : Block (n + m) (countingHLayer n m) (hadamardU (n + m)) :=
  ⟨rfl, dataLayer_WF _ _ (onAll_h_unitary _) (onAll_qubitsOk _ _ fun _ hi => h_qubitsOk hi),
   fun a _ => ancRestore_hLayer (n + m) a⟩

/-- The phase fix `z (data (n+j))`, the exact matrix. -/
noncomputable def zU (n m j : ℕ) : 𝐔[Reg (n + m)] := dataMatU (n + m) [.z (.data (n + j))]

theorem block_z (n m j : ℕ) (hj : j < m) :
    Block (n + m) ⟨n + m, [.z (.data (n + j))]⟩ (zU n m j) :=
  block_dataOnly _ rfl (by simp [Gate.qubitsOk, Gate.qubits]; omega) rfl

/-- The inverse (A)QFT on the phase register, the exact matrix of its shifted gate list. -/
noncomputable def qftInvU (n m : ℕ) (kmax : Option ℕ) : 𝐔[Reg (n + m)] :=
  dataMatU (n + m) (countingInverse n m kmax).gates

theorem inverseGates_unitary (m : ℕ) (kmax : Option ℕ) :
    ∀ g ∈ inverseGates m kmax, g.isUnitary = true := by
  cases kmax with
  | none => exact qftGates_unitary m
  | some k => exact aqftGates_unitary m k

theorem inverseGates_qubitsOk (m : ℕ) (kmax : Option ℕ) :
    ∀ g ∈ inverseGates m kmax, g.qubitsOk m = true := by
  cases kmax with
  | none => exact fun _ hg => qftGates_qubitsOk hg
  | some k => exact fun _ hg => qftGates_qubitsOk (mem_aqftGates hg)

theorem inverseGates_dataOnly (m : ℕ) (kmax : Option ℕ) :
    ∀ g ∈ inverseGates m kmax, g.dataOnly = true := by
  cases kmax with
  | none => exact fun _ hg => qftGates_dataOnly hg
  | some k => exact fun _ hg => qftGates_dataOnly (mem_aqftGates hg)

theorem block_inverse (n m : ℕ) (kmax : Option ℕ) :
    Block (n + m) (countingInverse n m kmax) (qftInvU n m kmax) := by
  have hu := adjointGates_unitary (inverseGates_unitary m kmax)
  have hq := adjointGates_qubitsOk (inverseGates_qubitsOk m kmax)
  have hd : ∀ g ∈ adjointGates (inverseGates m kmax), g.dataOnly = true := by
    intro g hg
    rw [adjointGates, List.mem_reverse, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [Gate.dataOnly_adjoint]
    exact inverseGates_dataOnly m kmax g' hg'
  refine block_dataOnly _ ?_ ?_ ?_
  · rw [List.all_map, List.all_eq_true]
    intro g hg
    rw [Function.comp_apply, Gate.isUnitary_shiftData]
    exact hu g hg
  · rw [List.all_map, List.all_eq_true]
    intro g hg
    exact Gate.qubitsOk_shiftData n (hq g hg)
  · rw [List.all_map, List.all_eq_true]
    intro g hg
    rw [Function.comp_apply, Gate.dataOnly_shiftData]
    exact hd g hg

/-! ## The controlled blocks -/

/-- Lemma 6.3.2 (either mode) as a block: a synthesized oracle of a well-formed network on `n`
inputs restores with the phase oracle of its predicate. -/
theorem block_oracle {N : Network} {mode : UncomputeMode} {o : Circuit} (hN : N.WF)
    (ho : synthesizeOracle N mode = .ok o) {n : ℕ} (hn : N.nInputs = n) :
    Block n o (phaseOracle (N.pred n)) := by
  have hWF := synthesizeOracle_WF' mode hN ho
  have hnd : o.nData = n := by
    obtain ⟨_, _, _, _, _, _, hC⟩ := synthesizeOracle_okM ho
    rw [hC]
    exact hn
  refine ⟨hnd, hWF, fun a ha => ?_⟩
  have key : ∀ k, k = n → AncRestore k a o (phaseOracle (N.pred k)) →
      AncRestore n a o (phaseOracle (N.pred n)) := by
    rintro k rfl h
    exact h
  exact key _ hnd (lemma_6_3_2_mode_of_le mode N o ho hWF a ha)

/-- PHASE2_SPEC.md §A.3 — the unitary of `controlledDiffusion n m j shape`:
`post · U_{P_all ∧ c_j} · pre`. -/
noncomputable def cdiffU (n m j : ℕ) (shape : DiffusionShape) : 𝐔[Reg (n + m)] :=
  postU n m * phaseOracle (((diffusionNet shape n).withControl m j).pred (n + m)) * preU n m

theorem diffusionNet_outputs_length (shape : DiffusionShape) (n : ℕ) :
    (diffusionNet shape n).outputs.length = 1 := by
  cases shape <;> rfl

theorem controlledDiffusion_block {n m j : ℕ} {shape : DiffusionShape} {mode : UncomputeMode}
    {D : Circuit} (hD : controlledDiffusion n m j shape mode = .ok D) (hn : n ≠ 0) (hj : j < m) :
    Block (n + m) D (cdiffU n m j shape) := by
  obtain ⟨mcz, hmcz, rfl⟩ := controlledDiffusion_ok hD
  have hN' : ((diffusionNet shape n).withControl m j).WF :=
    Network.withControl_WF (diffusionNet_WF shape hn) (diffusionNet_outputs_length shape n) hj
  have hm := block_oracle hN' hmcz (n := n + m)
    (by rw [Network.withControl_nInputs, diffusionNet_nInputs])
  have h := ((block_pre n m).append hm).append (block_post n m)
  rw [cdiffU, mul_assoc]
  exact h

/-- B4 — `controlledDiffusion` is well formed and restores its ancillae with `cdiffU` on every
register at least its own (Lemma 6.3.2 for the `withControl` network, `ancRestore_of_dataLayer`
for the wrappers, `AncRestore.comp` twice). -/
theorem controlledDiffusion_ancRestore {n m j : ℕ} {shape : DiffusionShape}
    {mode : UncomputeMode} {D : Circuit} (hD : controlledDiffusion n m j shape mode = .ok D)
    (hn : n ≠ 0) (hj : j < m) :
    D.WF ∧ ∀ a, D.nAnc ≤ a → AncRestore (n + m) a D (cdiffU n m j shape) :=
  (controlledDiffusion_block hD hn hj).2

/-- PHASE2_SPEC.md §A.3 amendment (2) — the unitary of `controlledGrover N n m j shape`:
`zU · cdiffU · U_{P ∧ c_j}`. -/
noncomputable def cgU (N : Network) (n m j : ℕ) (shape : DiffusionShape) : 𝐔[Reg (n + m)] :=
  zU n m j * cdiffU n m j shape * phaseOracle ((N.withControl m j).pred (n + m))

theorem controlledGrover_block {N : Network} {n m j : ℕ} {shape : DiffusionShape}
    {mode : UncomputeMode} {G : Circuit} (hG : controlledGrover N n m j shape mode = .ok G)
    (hN : N.WF) : Block (n + m) G (cgU N n m j shape) := by
  obtain ⟨hn, h1, hj, hn0, o, d, ho, hd, rfl⟩ := controlledGrover_ok hG
  have hN' := Network.withControl_WF hN h1 hj
  have ho' := block_oracle hN' ho (n := n + m) (by rw [Network.withControl_nInputs, hn])
  have hd' := controlledDiffusion_block hd hn0 hj
  have h := (ho'.append hd').append (block_z n m j hj)
  rw [cgU, mul_assoc]
  exact h

/-- B4 — `controlledGrover` is well formed and restores its ancillae with `cgU` on every register
at least its own. -/
theorem controlledGrover_ancRestore {N : Network} {n m j : ℕ} {shape : DiffusionShape}
    {mode : UncomputeMode} {G : Circuit} (hG : controlledGrover N n m j shape mode = .ok G)
    (hN : N.WF) : G.WF ∧ ∀ a, G.nAnc ≤ a → AncRestore (n + m) a G (cgU N n m j shape) :=
  (controlledGrover_block hG hN).2

/-! ## The powers and the whole circuit -/

/-- The product, in program order, of `cgU i ^ (2^i)` for `i < j` (`cgU 0` rightmost). -/
noncomputable def powersUpTo (N : Network) (n m : ℕ) (shape : DiffusionShape) :
    ℕ → 𝐔[Reg (n + m)]
  | 0 => 1
  | j + 1 => cgU N n m j shape ^ (2 ^ j) * powersUpTo N n m shape j

/-- PHASE2_SPEC.md §A.3 — the unitary of the controlled iterates of `countingCircuit`:
`∏_{j<m} cgU j ^ (2^j)`, in program order. (It does not depend on the uncomputation mode.) -/
noncomputable def powersU (N : Network) (n m : ℕ) (shape : DiffusionShape) : 𝐔[Reg (n + m)] :=
  powersUpTo N n m shape m

theorem countingPowers_block {N : Network} {n m : ℕ} {shape : DiffusionShape}
    {mode : UncomputeMode} {init : Circuit} {U : 𝐔[Reg (n + m)]} (hN : N.WF)
    (hi : Block (n + m) init U) :
    ∀ {j : ℕ} {C : Circuit}, countingPowers N n m shape mode init j = .ok C →
      Block (n + m) C (powersUpTo N n m shape j * U)
  | 0, C, h => by
    rw [countingPowers_zero] at h
    cases h
    simpa [powersUpTo] using hi
  | j + 1, C, h => by
    obtain ⟨acc, b, ha, hb, rfl⟩ := countingPowers_succ_ok h
    have hacc := countingPowers_block hN hi ha
    have hbb := controlledGrover_block hb hN
    have := hacc.foldl_replicate hbb (2 ^ j) (Nat.two_pow_pos j)
    rw [powersUpTo, mul_assoc]
    exact this

/-- B4 (PHASE2_SPEC.md §A.3 amendment (5), the raw form) — the counting circuit is well formed and
restores its ancillae on its own register, applying `qftInvU · powersU · H^{⊗(n+m)}`, the exact
matrices of its blocks in program order. The hypotheses `hn`, `h1` are those of the task text;
they are implied by `hC` (`controlledGrover` refuses the other cases). -/
theorem countingCircuit_ancRestore_raw {N : Network} {n m : ℕ} {kmax : Option ℕ}
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N n m kmax shape mode = .ok C) (hN : N.WF) (_hn : N.nInputs = n)
    (_h1 : N.outputs.length = 1) :
    C.WF ∧ AncRestore (n + m) C.nAnc C
      (qftInvU n m kmax * powersU N n m shape * hadamardU (n + m)) := by
  obtain ⟨-, body, hb, rfl⟩ := countingCircuit_ok hC
  have hbody := countingPowers_block hN (block_hLayer n m) hb
  have h := hbody.append (block_inverse n m kmax)
  rw [mul_assoc]
  exact ⟨h.2.1, h.2.2 _ le_rfl⟩

end CQRV.Counting

end
