module

public import CQRV.Synthesis.Counting
public import CQRV.Grover.Restore
public import CQRV.Circuit.QFTCorrect

/-!
# CQRV.Grover.CountingCorrect

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

* Stage 19c (STAGE19_TASK.md C1–C5 with the notes of the 19b review; amendment (5)) — **the tensor
  form**, all proved. Coordinates `search x : Reg n`, `phase x : Reg m` of `x : Reg (n + m)`
  (`splitEquiv`, the `appendEquiv` of `Semantics`), and one block-diagonal form `blockD F x y =
  [phase x = phase y] · F (phase x) (search x) (search y)` — Mathlib's `Matrix.blockDiagonal` along
  `splitEquiv`, so products, powers and adjoints are `blockDiagonal_mul` / `_conjTranspose`.
  `liftS A = blockD (fun _ => A)`, `ctrlU j V = blockD (fun p => if p.bit j then V else 1)` (the
  control is bit `j` of the phase register through `Reg.bit`, a natural number: no `Fin.cast`),
  `ctrlPow V = blockD (fun p => V ^ p.toNatLE)`, and `liftP B x y = [search x = search y] · B (phase
  x) (phase y)` (`1 ⊗ B` along `splitEquiv`); all are functions on matrices, with their entry
  lemmas and unitary-group membership. C2: `hUpTo_eq_liftS`, `flipUpToMat_eq_liftS`, `zU_val`
  (`zU j = ctrlU j (−1)`), and the shift lemma `dataMat_shiftData : dataMat (n+m) (gs.map
  (Gate.shiftData n)) = liftP (dataMat m gs)` for a unitary data-only `gs`, through the explicit
  per-gate data matrix `gateD` (`gateD_shiftData` holds for every gate) and `dataMat_cons`. C3:
  `phaseOracle_withControl`, `phaseOracle_diffusion_withControl` (`ctrlU_phaseDiag`). C4:
  `ctrlU_mul`, `liftS_ctrlU_liftS`, `zU_mul_ctrlU_neg`, `ctrlU_pow`, `cdiffU_val` (`= ctrlU j
  (−U_s)`, by `diffusion_circuit_matrix`), `cgU_val` (`= ctrlU j G`), `powersUpTo_val` (the partial
  product of note (iii)) and `powersU_val` (`= ctrlPow G`). C5: `U_count P m kmax = liftP (star
  (dataMat m (inverseGates m kmax))) · ctrlPow (groverOp P) · hadamardMat (n + m)`,
  `raw_eq_U_count` (an equality of unitaries) and

  `countingCircuit_ancRestore : C.WF ∧ AncRestore (n+m) C.nAnc C (U_count (N.pred n) m kmax)`.
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

/-- Stage 19c — the data-register matrix of one gate on data qubits (the `G` of
`gateU_kron_of_dataOnly`, explicit): `H` as `hMat` on the lenses `getD` / `flipD`, the phase gates
and `cz` / `cp` as diagonal monomial matrices, `X` and `CNOT` as permutations; `1` for every other
gate (ancilla operands, `measure`, `ifBit`, `alloc`, `free`). -/
noncomputable def gateD (N : ℕ) : Gate → Matrix (Reg N) (Reg N) ℂ
  | .h (.data i) => if i < N then hMat (getD i) (flipD i) else 1
  | .s (.data i) => monoMat id (fun x => if getD i x then Complex.I else 1)
  | .sdg (.data i) => monoMat id (fun x => if getD i x then -Complex.I else 1)
  | .t (.data i) => monoMat id (fun x => if getD i x then ω else 1)
  | .tdg (.data i) => monoMat id (fun x => if getD i x then star ω else 1)
  | .x (.data i) => monoMat (flipD i) (fun _ => 1)
  | .z (.data i) => monoMat id (fun x => if getD i x then -1 else 1)
  | .cnot (.data i) (.data j) => if i = j then 1 else monoMat (cnotPermD i j) (fun _ => 1)
  | .cz (.data i) (.data j) => monoMat id (fun x => if getD i x && getD j x then -1 else 1)
  | .p a k (.data i) => monoMat id (fun x => if getD i x then phaseOf a k else 1)
  | .cp a k (.data i) (.data j) =>
    monoMat id (fun x => if getD i x && getD j x then phaseOf a k else 1)
  | _ => 1

/-- A unitary gate on data qubits only denotes `gateD N g ⊗ 1` on every ancilla register. -/
theorem gateU_eq_gateD_kron {N : ℕ} {g : Gate} (hu : g.isUnitary = true)
    (hd : g.dataOnly = true) (a : ℕ) :
    gateU N a g = gateD N g ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  cases g with
  | h q =>
    cases q with
    | data i =>
      show gateU N a _ = (if i < N then hMat (getD i) (flipD i) else 1) ⊗ₖ 1
      by_cases hi : i < N
      · simp only [gateU, Qubit.inRange, hi, decide_true, ↓reduceIte, get_data_eq, flip_data_eq]
        exact hMat_prod_kron _ _
      · simp only [gateU, Qubit.inRange, hi, decide_false, Bool.false_eq_true, ↓reduceIte,
          Matrix.one_kronecker_one]
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | s q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then Complex.I else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then Complex.I else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | sdg q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then -Complex.I else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then -Complex.I else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | t q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then ω else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then ω else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | tdg q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then star ω else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then star ω else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | x q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat (flipD i) (fun _ => 1) ⊗ₖ 1
      simp only [gateU, flip_data_eq]
      exact monoMat_prod_kron (flipD i) (fun _ => 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | z q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then -1 else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then -1 else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cnot c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        show gateU N a _ = (if i = j then 1 else monoMat (cnotPermD i j) (fun _ => 1)) ⊗ₖ 1
        by_cases hij : i = j
        · subst hij
          simp only [gateU, ↓reduceIte, Matrix.one_kronecker_one]
        · have hne : Qubit.data i ≠ Qubit.data j := fun e => hij (by cases e; rfl)
          simp only [gateU, hne, hij, ↓reduceIte, cnotPerm_data_eq]
          exact monoMat_prod_kron (cnotPermD i j) (fun _ => 1)
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cz c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        show gateU N a _ = monoMat id (fun x => if getD i x && getD j x then -1 else 1) ⊗ₖ 1
        simp only [gateU, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x && getD j x then -1 else 1)
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | measure q c => simp [Gate.isUnitary] at hu
  | ifBit c g => simp [Gate.isUnitary] at hu
  | alloc q =>
    show (1 : Matrix (Reg N × Reg a) (Reg N × Reg a) ℂ) = (1 : Matrix (Reg N) (Reg N) ℂ) ⊗ₖ 1
    rw [Matrix.one_kronecker_one]
  | free q =>
    show (1 : Matrix (Reg N × Reg a) (Reg N × Reg a) ℂ) = (1 : Matrix (Reg N) (Reg N) ℂ) ⊗ₖ 1
    rw [Matrix.one_kronecker_one]
  | p m k q =>
    cases q with
    | data i =>
      show gateU N a _ = monoMat id (fun x => if getD i x then phaseOf m k else 1) ⊗ₖ 1
      simp only [gateU, phaseMat, get_data_eq]
      exact monoMat_id_prod_kron (fun x => if getD i x then phaseOf m k else 1)
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd
  | cp m k c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        show gateU N a _ = monoMat id (fun x => if getD i x && getD j x then phaseOf m k else 1) ⊗ₖ 1
        simp only [gateU, get_data_eq]
        exact monoMat_id_prod_kron (fun x => if getD i x && getD j x then phaseOf m k else 1)
      | anc j => simp [Gate.dataOnly, Gate.qubits] at hd
    | anc i => simp [Gate.dataOnly, Gate.qubits] at hd

/-- A unitary gate on data qubits only denotes `G ⊗ 1`, for a `G` independent of the ancilla
register. -/
theorem gateU_kron_of_dataOnly {N : ℕ} {g : Gate} (hu : g.isUnitary = true)
    (hd : g.dataOnly = true) :
    ∃ G : Matrix (Reg N) (Reg N) ℂ, ∀ a, gateU N a g = G ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) :=
  ⟨gateD N g, gateU_eq_gateD_kron hu hd⟩

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

/-! ## Stage 19c — the tensor form of `U_count`

PHASE2_SPEC.md §A.3 amendment (5); docs/tasks/STAGE19_TASK.md C1–C5 with the notes of the 19b
review. Everything below is an equality of matrices (of unitaries, at the end); `AncRestore.congr`
is not used. -/

/-! ### C1 — coordinates and matrices -/

/-- PHASE2_SPEC.md §A.3 (5) — the search register of `x : Reg (n + m)`: its first `n` bits. -/
def search {n m : ℕ} (x : Reg (n + m)) : Reg n := fun i => x (Fin.castAdd m i)

/-- PHASE2_SPEC.md §A.3 (5) — the phase register of `x : Reg (n + m)`: its last `m` bits (phase
qubit `j` is `data (n + j)`). -/
def phase {n m : ℕ} (x : Reg (n + m)) : Reg m := fun j => x (Fin.natAdd n j)

/-- `Reg (n + m) ≃ Reg n × Reg m`, `x ↦ (search x, phase x)` (`appendEquiv` of `Semantics`). -/
def splitEquiv (n m : ℕ) : Reg (n + m) ≃ Reg n × Reg m := appendEquiv n m

theorem splitEquiv_apply {n m : ℕ} (x : Reg (n + m)) : splitEquiv n m x = (search x, phase x) :=
  rfl

theorem reg_ext_iff {n m : ℕ} {x y : Reg (n + m)} :
    x = y ↔ search x = search y ∧ phase x = phase y := by
  rw [← (splitEquiv n m).injective.eq_iff, splitEquiv_apply, splitEquiv_apply, Prod.mk.injEq]

theorem phase_bit {n m : ℕ} (x : Reg (n + m)) (j : ℕ) : (phase x).bit j = x.bit (n + j) := by
  by_cases hj : j < m
  · rw [Reg.bit_of_lt _ hj, Reg.bit_of_lt x (by omega : n + j < n + m)]
    rfl
  · rw [Reg.bit_of_le _ (by omega), Reg.bit_of_le x (by omega)]

theorem search_bit {n m : ℕ} (x : Reg (n + m)) (i : ℕ) :
    (search x).bit i = (decide (i < n) && x.bit i) := by
  by_cases hi : i < n
  · rw [Reg.bit_of_lt _ hi, Reg.bit_of_lt x (by omega : i < n + m)]
    simp only [hi, decide_true, Bool.true_and]
    rfl
  · rw [Reg.bit_of_le _ (by omega)]
    simp only [hi, decide_false, Bool.false_and]

/-- The block-diagonal matrix on `Reg (n + m)` with block `F p` on the search register where the
phase register reads `p`: `[phase x = phase y] · F (phase x) (search x) (search y)`. -/
noncomputable def blockD {n m : ℕ} (F : Reg m → Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + m)) (Reg (n + m)) ℂ :=
  Matrix.of fun x y => if phase x = phase y then F (phase x) (search x) (search y) else 0

theorem blockD_apply {n m : ℕ} (F : Reg m → Matrix (Reg n) (Reg n) ℂ) (x y : Reg (n + m)) :
    blockD F x y = if phase x = phase y then F (phase x) (search x) (search y) else 0 := rfl

/-- `blockD` is Mathlib's `Matrix.blockDiagonal` along `splitEquiv`. -/
theorem blockD_eq_submatrix {n m : ℕ} (F : Reg m → Matrix (Reg n) (Reg n) ℂ) :
    blockD F = (Matrix.blockDiagonal F).submatrix (splitEquiv n m) (splitEquiv n m) := by
  ext x y
  rw [Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
  rfl

theorem blockD_mul {n m : ℕ} (F G : Reg m → Matrix (Reg n) (Reg n) ℂ) :
    blockD F * blockD G = blockD (fun p => F p * G p) := by
  rw [blockD_eq_submatrix, blockD_eq_submatrix, blockD_eq_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.blockDiagonal_mul]

theorem blockD_one {n m : ℕ} :
    blockD (fun _ : Reg m => (1 : Matrix (Reg n) (Reg n) ℂ)) = 1 := by
  rw [blockD_eq_submatrix]
  show (Matrix.blockDiagonal (1 : Reg m → Matrix (Reg n) (Reg n) ℂ)).submatrix _ _ = 1
  rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

theorem blockD_conjTranspose {n m : ℕ} (F : Reg m → Matrix (Reg n) (Reg n) ℂ) :
    (blockD F)ᴴ = blockD (fun p => (F p)ᴴ) := by
  rw [blockD_eq_submatrix, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    ← blockD_eq_submatrix]

theorem blockD_pow {n m : ℕ} (F : Reg m → Matrix (Reg n) (Reg n) ℂ) (r : ℕ) :
    blockD F ^ r = blockD (fun p => F p ^ r) := by
  induction r with
  | zero =>
    simp only [pow_zero]
    exact blockD_one.symm
  | succ r ih =>
    rw [pow_succ, ih, blockD_mul]
    rfl

theorem blockD_mem {n m : ℕ} {F : Reg m → Matrix (Reg n) (Reg n) ℂ} (hF : ∀ p, F p ∈ 𝐔[Reg n]) :
    blockD F ∈ 𝐔[Reg (n + m)] := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, blockD_conjTranspose, blockD_mul,
    ← blockD_one]
  congr 1
  funext p
  have h := hF p
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

/-- C1 — `A` on the search register: `liftS A x y = [phase x = phase y] · A (search x) (search y)`. -/
noncomputable def liftS {n m : ℕ} (A : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + m)) (Reg (n + m)) ℂ :=
  blockD fun _ : Reg m => A

/-- C1 — `B` on the phase register: `liftP B x y = [search x = search y] · B (phase x) (phase y)`. -/
noncomputable def liftP {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) :
    Matrix (Reg (n + m)) (Reg (n + m)) ℂ :=
  Matrix.of fun x y => if search x = search y then B (phase x) (phase y) else 0

/-- C1 — `V` on the search register controlled by phase qubit `j` (bit `j` of the phase register,
`false` beyond it): `ctrlU j V x y = [phase x = phase y] · (if (phase x).bit j then V else 1)
(search x) (search y)`. -/
noncomputable def ctrlU {n m : ℕ} (j : ℕ) (V : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + m)) (Reg (n + m)) ℂ :=
  blockD fun p : Reg m => if p.bit j then V else 1

/-- C1 — the controlled powers: `ctrlPow V x y = [phase x = phase y] · (V ^ (phase x).toNatLE)
(search x) (search y)`; phase qubit `j` has weight `2^j`. -/
noncomputable def ctrlPow {n m : ℕ} (V : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + m)) (Reg (n + m)) ℂ :=
  blockD fun p : Reg m => V ^ p.toNatLE

theorem liftS_apply {n m : ℕ} (A : Matrix (Reg n) (Reg n) ℂ) (x y : Reg (n + m)) :
    liftS A x y = if phase x = phase y then A (search x) (search y) else 0 := rfl

theorem liftP_apply {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) (x y : Reg (n + m)) :
    liftP B x y = if search x = search y then B (phase x) (phase y) else 0 := rfl

theorem ctrlU_apply {n m : ℕ} (j : ℕ) (V : Matrix (Reg n) (Reg n) ℂ) (x y : Reg (n + m)) :
    ctrlU j V x y =
      if phase x = phase y then (if (phase x).bit j then V else 1) (search x) (search y) else 0 :=
  rfl

theorem ctrlPow_apply {n m : ℕ} (V : Matrix (Reg n) (Reg n) ℂ) (x y : Reg (n + m)) :
    ctrlPow V x y =
      if phase x = phase y then (V ^ (phase x).toNatLE) (search x) (search y) else 0 := rfl

theorem liftS_mem {n m : ℕ} {A : Matrix (Reg n) (Reg n) ℂ} (hA : A ∈ 𝐔[Reg n]) :
    (liftS A : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) ∈ 𝐔[Reg (n + m)] :=
  blockD_mem fun _ => hA

theorem ctrlU_mem {n m : ℕ} (j : ℕ) {V : Matrix (Reg n) (Reg n) ℂ} (hV : V ∈ 𝐔[Reg n]) :
    (ctrlU j V : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) ∈ 𝐔[Reg (n + m)] :=
  blockD_mem fun p => by
    cases p.bit j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact one_mem _
    · simp only [↓reduceIte]
      exact hV

theorem ctrlPow_mem {n m : ℕ} {V : Matrix (Reg n) (Reg n) ℂ} (hV : V ∈ 𝐔[Reg n]) :
    (ctrlPow V : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) ∈ 𝐔[Reg (n + m)] :=
  blockD_mem fun _ => pow_mem hV _

/-- `liftP B` is `1 ⊗ B` along `splitEquiv`. -/
theorem liftP_eq_submatrix {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) =
      ((1 : Matrix (Reg n) (Reg n) ℂ) ⊗ₖ B).submatrix (splitEquiv n m) (splitEquiv n m) := by
  ext x y
  simp only [liftP, Matrix.of_apply, Matrix.submatrix_apply, splitEquiv_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem liftP_mul {n m : ℕ} (A B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP A * liftP B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = liftP (A * B) := by
  rw [liftP_eq_submatrix, liftP_eq_submatrix, liftP_eq_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem liftP_one {n m : ℕ} :
    (liftP (1 : Matrix (Reg m) (Reg m) ℂ) : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = 1 := by
  rw [liftP_eq_submatrix, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem liftP_conjTranspose {n m : ℕ} (B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ)ᴴ = liftP Bᴴ := by
  rw [liftP_eq_submatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← liftP_eq_submatrix]

theorem liftP_add {n m : ℕ} (A B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP (A + B) : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = liftP A + liftP B := by
  ext x y
  simp only [liftP, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem liftP_smul {n m : ℕ} (c : ℂ) (B : Matrix (Reg m) (Reg m) ℂ) :
    (liftP (c • B) : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = c • liftP B := by
  ext x y
  simp only [liftP, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

theorem liftP_mem {n m : ℕ} {B : Matrix (Reg m) (Reg m) ℂ} (hB : B ∈ 𝐔[Reg m]) :
    (liftP B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) ∈ 𝐔[Reg (n + m)] := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hB ⊢
  rw [liftP_conjTranspose, liftP_mul, hB, liftP_one]

/-! ### C2 — the layers -/

/-- C2 — the Hadamards of the search register: `hUpTo (n + m) n = liftS (hadamardMat n)`. -/
theorem hUpTo_eq_liftS (n m : ℕ) : hUpTo (n + m) n = liftS (hadamardMat n) := by
  ext x y
  have hcond : (∀ i : Fin (n + m), n ≤ i.val → x i = y i) ↔ phase x = phase y := by
    rw [Fin.forall_fin_add]
    constructor
    · rintro ⟨-, h⟩
      funext j
      exact h j (Nat.le_add_right n j.val)
    · intro h
      exact ⟨fun i hi => absurd hi (Nat.not_le.mpr i.isLt), fun j _ => congrFun h j⟩
  have h1 : ∀ i : Fin n, ((Fin.castAdd m i).val < n) = True := fun i => eq_true i.isLt
  have h2 : ∀ j : Fin m, ((Fin.natAdd n j).val < n) = False := fun j =>
    eq_false (Nat.not_lt.mpr (Nat.le_add_right n j.val))
  simp only [hUpTo, Matrix.of_apply, liftS, blockD, hadamardMat, hcond]
  by_cases hp : phase x = phase y
  · simp only [hp, ↓reduceIte]
    rw [Fin.prod_univ_add]
    simp only [h1, h2, ↓reduceIte, Finset.prod_const_one, mul_one]
    rfl
  · simp only [hp, ↓reduceIte]

theorem search_flipUpTo {n m : ℕ} (y : Reg (n + m)) : search (flipUpTo n y) = notAll (search y) := by
  funext i
  have h : (Fin.castAdd m i).val < n := i.isLt
  simp only [search, flipUpTo, notAll, h, ↓reduceIte]

theorem phase_flipUpTo {n m : ℕ} (y : Reg (n + m)) : phase (flipUpTo n y) = phase y := by
  funext j
  have h : ¬ (Fin.natAdd n j).val < n := Nat.not_lt.mpr (Nat.le_add_right n j.val)
  simp only [phase, flipUpTo, h, ↓reduceIte]

/-- C2 — the `X` layer of the search register: `flipUpToMat (n + m) n = liftS (xAllMat n)`. -/
theorem flipUpToMat_eq_liftS (n m : ℕ) : flipUpToMat (n + m) n = liftS (xAllMat n) := by
  ext x y
  simp only [flipUpToMat, xAllMat, monoMat_apply, liftS, blockD, Matrix.of_apply,
    reg_ext_iff (x := x) (y := flipUpTo n y), search_flipUpTo, phase_flipUpTo]
  by_cases hp : phase x = phase y <;> by_cases hs : search x = notAll (search y) <;> simp [hp, hs]

theorem dataMat_nil (N : ℕ) : dataMat N [] = 1 :=
  kron_one_inj reg0 (by rw [← unitaryDenote_zero_eq, unitaryDenote_nil, Matrix.one_kronecker_one])

/-- `dataMat` is multiplicative (first gate applied first). -/
theorem dataMat_cons (N : ℕ) (g : Gate) (gs : List Gate) :
    dataMat N (g :: gs) = dataMat N gs * dataMat N [g] := by
  apply kron_one_inj reg0
  calc dataMat N (g :: gs) ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)
      = unitaryDenote N 0 (g :: gs) := (unitaryDenote_zero_eq N (g :: gs)).symm
    _ = unitaryDenote N 0 gs * unitaryDenote N 0 [g] := by
        simp only [unitaryDenote, Matrix.one_mul]
    _ = (dataMat N gs ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)) *
          (dataMat N [g] ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ)) := by
        rw [unitaryDenote_zero_eq N gs, unitaryDenote_zero_eq N [g]]
    _ = (dataMat N gs * dataMat N [g]) ⊗ₖ (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- The data matrix of one unitary data-only gate is `gateD`. -/
theorem dataMat_singleton {N : ℕ} {g : Gate} (hu : g.isUnitary = true) (hd : g.dataOnly = true) :
    dataMat N [g] = gateD N g := by
  apply kron_one_inj reg0
  rw [← unitaryDenote_zero_eq, ← gateU_eq_gateD_kron hu hd 0]
  simp only [unitaryDenote, Matrix.one_mul]

/-- C2 — the entry formula of the phase fix: `dataMat N [z (data i)]` is diagonal, `−1` where bit
`i` is set. -/
theorem dataMat_z (N i : ℕ) :
    dataMat N [.z (.data i)] = monoMat id (fun x : Reg N => if x.bit i then -1 else 1) :=
  dataMat_singleton rfl rfl

/-- C2 — the phase fix is the controlled sign: `zU j = ctrlU j (−1)` (diagonal, `−1` where phase
qubit `j` reads 1). -/
theorem zU_val (n m j : ℕ) : (zU n m j).val = ctrlU j (-1) := by
  show dataMat (n + m) [.z (.data (n + j))] = _
  rw [dataMat_z]
  ext x y
  rw [monoMat_apply, ctrlU_apply, id_eq, ← phase_bit]
  by_cases hxy : x = y
  · subst hxy
    rcases Bool.eq_false_or_eq_true ((phase x).bit j) with hb | hb <;> simp [hb]
  · by_cases hp : phase x = phase y
    · have hs : search x ≠ search y := fun hs => hxy (reg_ext_iff.mpr ⟨hs, hp⟩)
      rcases Bool.eq_false_or_eq_true ((phase y).bit j) with hb | hb <;>
        simp [hxy, hp, hb, Matrix.one_apply_ne hs]
    · simp [hxy, hp]

theorem getD_eq_bit {N : ℕ} (i : ℕ) (x : Reg N) : getD i x = x.bit i := rfl

/-- The bits of `flipD i x`: bit `i` flipped when it is in the register. -/
theorem flipD_bit {N : ℕ} (i l : ℕ) (x : Reg N) :
    (flipD i x).bit l = if l = i ∧ i < N then !x.bit l else x.bit l := by
  by_cases hi : i < N
  · by_cases hl : l < N
    · by_cases hli : l = i
      · subst hli
        simp [flipD, Reg.bit, hi]
      · simp [flipD, Reg.bit, hi, hl, hli, Fin.ext_iff]
    · have hli : l ≠ i := by omega
      simp [Reg.bit, hl, hli]
  · simp [flipD, hi]

theorem getD_shift {n m : ℕ} (i : ℕ) (x : Reg (n + m)) : getD (i + n) x = getD i (phase x) := by
  rw [getD_eq_bit, getD_eq_bit, phase_bit, Nat.add_comm i n]

theorem search_flipD_shift {n m : ℕ} (i : ℕ) (x : Reg (n + m)) :
    search (flipD (i + n) x) = search x := by
  refine Reg.ext_bit fun l => ?_
  rw [search_bit, search_bit, flipD_bit]
  by_cases hl : l < n
  · have h : ¬ (l = i + n ∧ i + n < n + m) := by omega
    simp only [h, ↓reduceIte]
  · simp only [hl, decide_false, Bool.false_and]

theorem phase_flipD_shift {n m : ℕ} (i : ℕ) (x : Reg (n + m)) :
    phase (flipD (i + n) x) = flipD i (phase x) := by
  refine Reg.ext_bit fun l => ?_
  rw [phase_bit, flipD_bit, flipD_bit, phase_bit]
  have h : (n + l = i + n ∧ i + n < n + m) ↔ (l = i ∧ i < m) := by omega
  simp only [h]

theorem search_cnotPermD_shift {n m : ℕ} (i j : ℕ) (x : Reg (n + m)) :
    search (cnotPermD (i + n) (j + n) x) = search x := by
  unfold cnotPermD
  cases getD (i + n) x <;> simp [search_flipD_shift]

theorem phase_cnotPermD_shift {n m : ℕ} (i j : ℕ) (x : Reg (n + m)) :
    phase (cnotPermD (i + n) (j + n) x) = cnotPermD i j (phase x) := by
  unfold cnotPermD
  rw [getD_shift]
  cases getD i (phase x) <;> simp [phase_flipD_shift]

/-- A monomial matrix on `Reg (n + m)` that fixes the search register and acts on the phase
register as `(σ, φ)` is `liftP` of that monomial matrix. -/
theorem monoMat_eq_liftP {n m : ℕ} {σ' : Reg (n + m) → Reg (n + m)} {σ : Reg m → Reg m}
    {φ' : Reg (n + m) → ℂ} {φ : Reg m → ℂ} (hs : ∀ x, search (σ' x) = search x)
    (hp : ∀ x, phase (σ' x) = σ (phase x)) (hφ : ∀ x, φ' x = φ (phase x)) :
    monoMat σ' φ' = liftP (monoMat σ φ) := by
  ext x y
  simp only [monoMat_apply, liftP, Matrix.of_apply, reg_ext_iff (x := x) (y := σ' y), hs, hp, hφ]
  by_cases h1 : search x = search y <;> by_cases h2 : phase x = σ (phase y) <;> simp [h1, h2]

theorem hMat_eq_liftP {n m : ℕ} {b' : Reg (n + m) → Bool} {f' : Reg (n + m) → Reg (n + m)}
    {b : Reg m → Bool} {f : Reg m → Reg m} (hs : ∀ x, search (f' x) = search x)
    (hp : ∀ x, phase (f' x) = f (phase x)) (hb : ∀ x, b' x = b (phase x)) :
    hMat b' f' = liftP (hMat b f) := by
  unfold hMat
  rw [liftP_smul, liftP_add,
    monoMat_eq_liftP (σ' := id) (σ := id) (φ' := fun j => if b' j then -1 else 1)
      (φ := fun p => if b p then -1 else 1) (fun _ => rfl) (fun _ => rfl)
      (fun x => by simp only [hb]),
    monoMat_eq_liftP (φ' := fun _ => 1) (φ := fun _ => 1) hs hp (fun _ => rfl)]

/-- The data matrix of a shifted gate is `liftP` of the gate's (every gate: both sides are `1`
for a gate that is not on data qubits). -/
theorem gateD_shiftData (n : ℕ) {m : ℕ} (g : Gate) :
    gateD (n + m) (g.shiftData n) = liftP (gateD m g) := by
  have hph : ∀ (i : ℕ) (p : ℂ),
      monoMat id (fun x : Reg (n + m) => if getD (i + n) x then p else 1) =
        liftP (monoMat id (fun x : Reg m => if getD i x then p else 1)) := fun i p =>
    monoMat_eq_liftP (fun _ => rfl) (fun _ => rfl) (fun x => by rw [getD_shift])
  have hph2 : ∀ (i j : ℕ) (p : ℂ),
      monoMat id (fun x : Reg (n + m) => if getD (i + n) x && getD (j + n) x then p else 1) =
        liftP (monoMat id (fun x : Reg m => if getD i x && getD j x then p else 1)) := fun i j p =>
    monoMat_eq_liftP (fun _ => rfl) (fun _ => rfl) (fun x => by rw [getD_shift, getD_shift])
  cases g with
  | h q =>
    cases q with
    | data i =>
      show (if i + n < n + m then hMat (getD (i + n)) (flipD (i + n)) else 1) =
        liftP (if i < m then hMat (getD i) (flipD i) else 1)
      by_cases hi : i < m
      · simp only [hi, show i + n < n + m by omega, ↓reduceIte]
        exact hMat_eq_liftP (search_flipD_shift i) (phase_flipD_shift i) (getD_shift i)
      · simp only [hi, show ¬ i + n < n + m by omega, ↓reduceIte]
        exact liftP_one.symm
    | anc i => exact liftP_one.symm
  | s q =>
    cases q with
    | data i => exact hph i Complex.I
    | anc i => exact liftP_one.symm
  | sdg q =>
    cases q with
    | data i => exact hph i (-Complex.I)
    | anc i => exact liftP_one.symm
  | t q =>
    cases q with
    | data i => exact hph i ω
    | anc i => exact liftP_one.symm
  | tdg q =>
    cases q with
    | data i => exact hph i (star ω)
    | anc i => exact liftP_one.symm
  | x q =>
    cases q with
    | data i =>
      show monoMat (flipD (i + n)) (fun _ => 1) = liftP (monoMat (flipD i) (fun _ => 1))
      exact monoMat_eq_liftP (search_flipD_shift i) (phase_flipD_shift i) (fun _ => rfl)
    | anc i => exact liftP_one.symm
  | z q =>
    cases q with
    | data i => exact hph i (-1)
    | anc i => exact liftP_one.symm
  | cnot c t =>
    cases c with
    | data i =>
      cases t with
      | data j =>
        show (if i + n = j + n then 1 else monoMat (cnotPermD (i + n) (j + n)) (fun _ => 1)) =
          liftP (if i = j then 1 else monoMat (cnotPermD i j) (fun _ => 1))
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte]
          exact liftP_one.symm
        · simp only [hij, show ¬ i + n = j + n by omega, ↓reduceIte]
          exact monoMat_eq_liftP (search_cnotPermD_shift i j) (phase_cnotPermD_shift i j)
            (fun _ => rfl)
      | anc j => exact liftP_one.symm
    | anc i =>
      cases t with
      | data j => exact liftP_one.symm
      | anc j => exact liftP_one.symm
  | cz c t =>
    cases c with
    | data i =>
      cases t with
      | data j => exact hph2 i j (-1)
      | anc j => exact liftP_one.symm
    | anc i =>
      cases t with
      | data j => exact liftP_one.symm
      | anc j => exact liftP_one.symm
  | measure q c => exact liftP_one.symm
  | ifBit c g => exact liftP_one.symm
  | alloc q => exact liftP_one.symm
  | free q => exact liftP_one.symm
  | p a k q =>
    cases q with
    | data i => exact hph i (phaseOf a k)
    | anc i => exact liftP_one.symm
  | cp a k c t =>
    cases c with
    | data i =>
      cases t with
      | data j => exact hph2 i j (phaseOf a k)
      | anc j => exact liftP_one.symm
    | anc i =>
      cases t with
      | data j => exact liftP_one.symm
      | anc j => exact liftP_one.symm

/-- C2 — the shift lemma: a unitary data-only gate list shifted onto the phase register denotes
`liftP` of its data matrix (gate by gate; the inverse (A)QFT is the client). The hypothesis is
`Gate.dataOnly` (note (ii) of the 19b review), not `qubitsOk m`. -/
theorem dataMat_shiftData (n : ℕ) {m : ℕ} (gs : List Gate) (hu : gs.all Gate.isUnitary = true)
    (hd : gs.all Gate.dataOnly = true) :
    dataMat (n + m) (gs.map (Gate.shiftData n)) = liftP (dataMat m gs) := by
  induction gs with
  | nil => rw [List.map_nil, dataMat_nil, dataMat_nil, liftP_one]
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hu hd
    rw [List.map_cons, dataMat_cons, dataMat_cons m, ih hu.2 hd.2,
      dataMat_singleton (by rw [Gate.isUnitary_shiftData]; exact hu.1)
        (by rw [Gate.dataOnly_shiftData]; exact hd.1),
      dataMat_singleton hu.1 hd.1, gateD_shiftData, liftP_mul]

/-- Note (iv) — the data matrix of the adjoint gate list is the adjoint. -/
theorem dataMat_adjointGates (N : ℕ) (gs : List Gate) (hu : ∀ g ∈ gs, g.isUnitary = true) :
    dataMat N (adjointGates gs) = star (dataMat N gs) := by
  apply kron_one_inj reg0
  rw [← unitaryDenote_zero_eq, unitaryDenote_adjoint N 0 gs hu, unitaryDenote_zero_eq,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.star_eq_conjTranspose]

theorem adjointGates_dataOnly {gs : List Gate} (h : ∀ g ∈ gs, g.dataOnly = true) :
    ∀ g ∈ adjointGates gs, g.dataOnly = true := by
  intro g hg
  rw [adjointGates, List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rw [Gate.dataOnly_adjoint]
  exact h g' hg'

/-- C2 / C5 — the inverse (A)QFT block is `liftP` of the adjoint of the (A)QFT's data matrix. -/
theorem qftInvU_val (n m : ℕ) (kmax : Option ℕ) :
    (qftInvU n m kmax).val = liftP (star (dataMat m (inverseGates m kmax))) := by
  show dataMat (n + m) ((adjointGates (inverseGates m kmax)).map (Gate.shiftData n)) = _
  rw [dataMat_shiftData n _
      (List.all_eq_true.mpr (adjointGates_unitary (inverseGates_unitary m kmax)))
      (List.all_eq_true.mpr (adjointGates_dataOnly (inverseGates_dataOnly m kmax))),
    dataMat_adjointGates m _ (inverseGates_unitary m kmax)]

/-! ### C3 — the oracles -/

/-- The predicate of `withControl` in the coordinates of `Reg (n + m)` (`subst` of
`N.nInputs = n`, then `withControl_pred`). -/
theorem withControl_pred_split {N : Network} {n m j : ℕ} (hN : N.WF) (hn : N.nInputs = n)
    (h1 : N.outputs.length = 1) (hj : j < m) (x : Reg (n + m)) :
    (N.withControl m j).pred (n + m) x = ((phase x).bit j && N.pred n (search x)) := by
  subst hn
  rw [Network.withControl_pred hN h1 hj, Reg.bit_of_lt _ hj]
  rfl

/-- A controlled phase oracle is the phase oracle of the conjunction with the control bit. -/
theorem ctrlU_phaseDiag {n m : ℕ} (j : ℕ) (P : Reg n → Bool) :
    (ctrlU j (phaseDiag P) : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) =
      phaseDiag (fun x => (phase x).bit j && P (search x)) := by
  ext x y
  rw [ctrlU_apply]
  show _ = Matrix.diagonal
    (fun x : Reg (n + m) => if ((phase x).bit j && P (search x)) = true then (-1 : ℂ) else 1) x y
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.diagonal_apply_eq]
    rcases Bool.eq_false_or_eq_true ((phase x).bit j) with hb | hb <;> simp [hb, phaseDiag]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hp : phase x = phase y
    · have hs : search x ≠ search y := fun hs => hxy (reg_ext_iff.mpr ⟨hs, hp⟩)
      rcases Bool.eq_false_or_eq_true ((phase y).bit j) with hb | hb <;>
        simp [hp, hb, phaseDiag, Matrix.one_apply_ne hs, Matrix.diagonal_apply_ne _ hs]
    · simp [hp]

/-- C3 — the oracle of `N.withControl m j` is the controlled oracle of `N`. -/
theorem phaseOracle_withControl {N : Network} {n m j : ℕ} (hN : N.WF) (hn : N.nInputs = n)
    (h1 : N.outputs.length = 1) (hj : j < m) :
    (phaseOracle ((N.withControl m j).pred (n + m))).val = ctrlU j (phaseOracle (N.pred n)).val := by
  show phaseDiag _ = ctrlU j (phaseDiag _)
  rw [ctrlU_phaseDiag]
  congr 1
  funext x
  exact withControl_pred_split hN hn h1 hj x

/-- C3 — the MCZ of the controlled diffusion is the controlled MCZ (either shape:
`diffusionNet_pred`, i.e. `treeNet_pred` / `allNet_pred`). -/
theorem phaseOracle_diffusion_withControl {n m j : ℕ} (shape : DiffusionShape) (hn0 : n ≠ 0)
    (hj : j < m) :
    (phaseOracle (((diffusionNet shape n).withControl m j).pred (n + m))).val =
      ctrlU j (phaseOracle (allOnes (n := n))).val := by
  rw [phaseOracle_withControl (diffusionNet_WF shape hn0) (diffusionNet_nInputs shape n)
    (diffusionNet_outputs_length shape n) hj, diffusionNet_pred shape hn0]

/-! ### C4 — the algebra -/

theorem liftS_mul {n m : ℕ} (A B : Matrix (Reg n) (Reg n) ℂ) :
    (liftS A * liftS B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = liftS (A * B) :=
  blockD_mul _ _

/-- C4 — controlled matrices multiply under the control. -/
theorem ctrlU_mul {n m : ℕ} (j : ℕ) (A B : Matrix (Reg n) (Reg n) ℂ) :
    (ctrlU j A * ctrlU j B : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = ctrlU j (A * B) := by
  rw [ctrlU, ctrlU, blockD_mul, ctrlU]
  congr 1
  funext p
  cases p.bit j <;> simp

/-- C4 — an uncontrolled conjugation `A · A' = 1` on the search register passes under the
control (the data layers of the controlled diffusion cancel when the control is 0). -/
theorem liftS_ctrlU_liftS {n m : ℕ} (j : ℕ) {A A' : Matrix (Reg n) (Reg n) ℂ}
    (B : Matrix (Reg n) (Reg n) ℂ) (h : A * A' = 1) :
    (liftS A * ctrlU j B * liftS A' : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) =
      ctrlU j (A * B * A') := by
  rw [liftS, liftS, ctrlU, blockD_mul, blockD_mul, ctrlU]
  congr 1
  funext p
  cases p.bit j <;> simp [h]

/-- C4 — the phase fix turns `ctrl_j(−V)` into `ctrl_j(V)` (PHASE2_SPEC §A.3 amendment (2)). -/
theorem zU_mul_ctrlU_neg (n m j : ℕ) (V : Matrix (Reg n) (Reg n) ℂ) :
    (zU n m j).val * ctrlU j (-V) = ctrlU j V := by
  rw [zU_val, ctrlU_mul, neg_mul_neg, Matrix.one_mul]

/-- C4 — powers pass under the control. -/
theorem ctrlU_pow {n m : ℕ} (j : ℕ) (V : Matrix (Reg n) (Reg n) ℂ) (r : ℕ) :
    (ctrlU j V : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) ^ r = ctrlU j (V ^ r) := by
  rw [ctrlU, blockD_pow, ctrlU]
  congr 1
  funext p
  cases p.bit j <;> simp

theorem xAllMat_mul_self (n : ℕ) : xAllMat n * xAllMat n = 1 := by
  rw [xAllMat, monoMat_mul, ← monoMat_id_one]
  congr 1
  · funext x
    exact notAll_involutive x
  · funext x
    simp

theorem preU_val (n m : ℕ) : (preU n m).val = liftS (xAllMat n * hadamardMat n) := by
  show flipUpToMat (n + m) n * hUpTo (n + m) n = _
  rw [flipUpToMat_eq_liftS, hUpTo_eq_liftS, liftS_mul]

theorem postU_val (n m : ℕ) : (postU n m).val = liftS (hadamardMat n * xAllMat n) := by
  show hUpTo (n + m) n * flipUpToMat (n + m) n = _
  rw [flipUpToMat_eq_liftS, hUpTo_eq_liftS, liftS_mul]

/-- C4 — the controlled diffusion block is `ctrl_j(−U_s)` (`diffusion_circuit_matrix`: the
circuit's diffusion is `−U_s`; under the control the sign is a relative phase). -/
theorem cdiffU_val {n m j : ℕ} (shape : DiffusionShape) (hn0 : n ≠ 0) (hj : j < m) :
    (cdiffU n m j shape).val = ctrlU j (-(diffU n).val) := by
  show (postU n m).val *
    (phaseOracle (((diffusionNet shape n).withControl m j).pred (n + m))).val * (preU n m).val = _
  have hinv : (hadamardMat n * xAllMat n) * (xAllMat n * hadamardMat n) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (xAllMat n), xAllMat_mul_self, Matrix.one_mul,
      hadamardMat_mul_self]
  rw [postU_val, preU_val, phaseOracle_diffusion_withControl shape hn0 hj,
    liftS_ctrlU_liftS j _ hinv, Matrix.mul_assoc, diffusion_circuit_matrix]

/-- C4 — the controlled Grover iterate is exactly `ctrl_j(G)`, `G = U_s U_P`. -/
theorem cgU_val {N : Network} {n m j : ℕ} (shape : DiffusionShape) (hN : N.WF)
    (hn : N.nInputs = n) (h1 : N.outputs.length = 1) (hj : j < m) (hn0 : n ≠ 0) :
    (cgU N n m j shape).val = ctrlU j (groverOp (N.pred n)).val := by
  show (zU n m j).val * (cdiffU n m j shape).val *
    (phaseOracle ((N.withControl m j).pred (n + m))).val = _
  rw [cdiffU_val shape hn0 hj, zU_mul_ctrlU_neg, phaseOracle_withControl hN hn h1 hj, ctrlU_mul]
  rfl

/-- C4, note (iii) — the partial product: for `j ≤ m`, the first `j` controlled powers are the
block-diagonal matrix with `G ^ (∑_{i<j} [phase bit i] 2^i)` on the search register. -/
theorem powersUpTo_val {N : Network} {n m : ℕ} (shape : DiffusionShape) (hN : N.WF)
    (hn : N.nInputs = n) (h1 : N.outputs.length = 1) (hn0 : n ≠ 0) :
    ∀ j, j ≤ m → (powersUpTo N n m shape j).val =
      blockD (fun p : Reg m => (groverOp (N.pred n)).val ^
        (∑ i ∈ Finset.range j, if p.bit i then 2 ^ i else 0))
  | 0, _ => by
    show (1 : Matrix (Reg (n + m)) (Reg (n + m)) ℂ) = _
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
    exact blockD_one.symm
  | j + 1, hj => by
    show (cgU N n m j shape).val ^ (2 ^ j) * (powersUpTo N n m shape j).val = _
    rw [cgU_val shape hN hn h1 (by omega) hn0, ctrlU_pow,
      powersUpTo_val shape hN hn h1 hn0 j (by omega), ctrlU, blockD_mul]
    congr 1
    funext p
    rw [Finset.sum_range_succ]
    cases p.bit j
    · simp
    · simp only [↓reduceIte]
      rw [← pow_add, Nat.add_comm]

/-- C4 — the product in program order of `ctrl_j(G) ^ (2^j)` over `j < m` is `ctrlPow G`
(`toNatLE_eq_sum_range`). -/
theorem powersU_val {N : Network} {n m : ℕ} (shape : DiffusionShape) (hN : N.WF)
    (hn : N.nInputs = n) (h1 : N.outputs.length = 1) (hn0 : n ≠ 0) :
    (powersU N n m shape).val = ctrlPow (groverOp (N.pred n)).val := by
  rw [powersU, powersUpTo_val shape hN hn h1 hn0 m le_rfl, ctrlPow]
  congr 1
  funext p
  rw [Reg.toNatLE_eq_sum_range]

/-! ### C5 — the theorem -/

/-- PHASE2_SPEC.md §A.3 amendment (5) — the unitary of the counting circuit:
`U_count = liftP (QFT†_m) · ctrlPow G · H^{⊗(n+m)}`, with `G = groverOp P = U_s U_P`,
`(ctrlPow G) x y = [phase x = phase y] · (G ^ (phase x).toNatLE) (search x) (search y)`, and
`QFT†_m` the adjoint of the data matrix of `qftGates m` (`kmax = none`) or of `aqftGates m k`
(`kmax = some k`): `inverseGates m kmax`. -/
noncomputable def U_count {n : ℕ} (P : Reg n → Bool) (m : ℕ) (kmax : Option ℕ) :
    𝐔[Reg (n + m)] :=
  ⟨liftP (star (dataMat m (inverseGates m kmax))) * ctrlPow (groverOp P).val * hadamardMat (n + m),
    mul_mem (mul_mem (liftP_mem (star (dataMatU m (inverseGates m kmax))).2)
      (ctrlPow_mem (groverOp P).2)) (hadamardMat_mem (n + m))⟩

/-- A counting circuit is built only on a non-empty search register (`controlledGrover` at
`j = 0` refuses `n = 0`, and `m ≥ 1`). -/
theorem countingCircuit_n_ne_zero {N : Network} {n m : ℕ} {kmax : Option ℕ}
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N n m kmax shape mode = .ok C) : n ≠ 0 := by
  obtain ⟨hm, body, hb, -⟩ := countingCircuit_ok hC
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨-, b, -, hb', -⟩ := countingPowers_succ_ok hb
  exact (controlledGrover_ok hb').2.2.2.1

/-- The factors of the raw theorem are the tensor form: an equality of unitaries. -/
theorem raw_eq_U_count {N : Network} {n m : ℕ} (kmax : Option ℕ) (shape : DiffusionShape)
    (hN : N.WF) (hn : N.nInputs = n) (h1 : N.outputs.length = 1) (hn0 : n ≠ 0) :
    qftInvU n m kmax * powersU N n m shape * hadamardU (n + m) = U_count (N.pred n) m kmax := by
  apply Subtype.ext
  show (qftInvU n m kmax).val * (powersU N n m shape).val * hadamardMat (n + m) = _
  rw [qftInvU_val, powersU_val shape hN hn h1 hn0]
  rfl

/-- PHASE2_SPEC.md §A.3 amendment (5) (Stage 19c) — **the counting circuit restores its ancillae
and applies `U_count`** on its own register: `countingCircuit_ancRestore_raw` with its factors
rewritten (`raw_eq_U_count`: equalities of unitaries, no `AncRestore.congr`). The form Stage 20a
starts from. -/
theorem countingCircuit_ancRestore {N : Network} {n m : ℕ} {kmax : Option ℕ}
    {shape : DiffusionShape} {mode : UncomputeMode} {C : Circuit}
    (hC : countingCircuit N n m kmax shape mode = .ok C) (hN : N.WF) (hn : N.nInputs = n)
    (h1 : N.outputs.length = 1) :
    C.WF ∧ AncRestore (n + m) C.nAnc C (U_count (N.pred n) m kmax) := by
  have h := countingCircuit_ancRestore_raw hC hN hn h1
  rw [raw_eq_U_count kmax shape hN hn h1 (countingCircuit_n_ne_zero hC)] at h
  exact h

end CQRV.Counting

end
