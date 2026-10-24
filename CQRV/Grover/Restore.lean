module

public import CQRV.Grover.Reflections
public import CQRV.Synthesis.Diffusion

/-!
# CQRV.Grover.Restore

Report §5.2.4 (revised sketch: `OracleCert`), §8.2.4 / §8.3.3 (the restoration conjunct),
§6.3.2 (Lemma 6.3.2, reused, not re-proved), §6.2.4 (restoration composes) — Stage 7a item 4:
the Grover circuit restores its ancillae and applies `G^r H^{⊗n}` on the data register.

* A data-only unitary layer (`H^{⊗n}`, `X^{⊗n}`) denotes `M ⊗ₖ 1` and restores the ancillae
  with `M` (`ancRestore_of_dataLayer`).
* The MCZ of the diffusion is the synthesized oracle of `allNet n` (Lemma 6.3.2 at the shared
  ancilla register, `lemma_6_3_2_of_le`), with predicate `P_all` (`allNet_pred`).
* The diffusion circuit restores with `2|s⟩⟨s| − I` (`AncRestore.comp` twice and decision 5);
  one iteration with `G = U_s U_P`; by induction the full circuit with `G^r H^{⊗n}`
  (`grover_ancRestore`, the restoration conjunct of `grover_parametric_lemma`).
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis Matrix
open scoped MState Kronecker

/-! ## Certificates (§5.2.4, adapted) -/

/-- Report §5.2.4 (revised `OracleCert`, adapted: DECISIONS.md 2026-10-24, Stage 7a) — a
certified oracle on `n` data qubits: a network `N` (AND/NOT/XOR, so also OR and `if`), its
synthesized circuit `C` (`synthesizeOracle N = .ok C`, well formed), and the restoration fact of
Lemma 6.3.2 at every ancilla register `a ≥ C.nAnc`. The last field is filled by the lemma
(`lemma_6_3_2_xor_of_le`), never assumed. Stage 9a: the field `hXor : N.xorFree = true` is gone
(Lemma 6.3.2 holds for XOR networks). The grade is not a field: it is computed from the circuit (Stage 7a decision 1). -/
structure OracleCert (n : ℕ) where
  /-- The Boolean network of the predicate (§6.1.2). -/
  N : Network
  /-- The synthesized oracle circuit (§6.1.4). -/
  C : Circuit
  hn : N.nInputs = n
  hC : synthesizeOracle N = .ok C
  hWF : C.WF
  /-- Lemma 6.3.2 (filled by the proof, §6.3.2). -/
  restore : ∀ a, C.nAnc ≤ a → AncRestore C.nData a C (phaseOracle (N.pred C.nData)) :=
    fun a ha => lemma_6_3_2_xor_of_le N C hC hWF a ha

/-- Report §5.2.4 — the predicate `P : Reg n → Bool` of a certified oracle. -/
def OracleCert.P {n : ℕ} (O : OracleCert n) : Reg n → Bool := O.N.pred n

/-- Report §6.1.4 — the synthesized circuit acts on the `N.nInputs = n` data qubits. -/
theorem OracleCert.nData_eq {n : ℕ} (O : OracleCert n) : O.C.nData = n := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := synthesizeOracle_ok O.hC
  rw [hC]
  exact O.hn

/-- Report §6.3.2 — Lemma 6.3.2 for a certified oracle, on the register `Reg n × Reg a`. -/
theorem OracleCert.ancRestore {n : ℕ} (O : OracleCert n) {a : ℕ} (ha : O.C.nAnc ≤ a) :
    AncRestore n a O.C (phaseOracle O.P) := by
  have key : ∀ m, m = n → AncRestore m a O.C (phaseOracle (O.N.pred m)) →
      AncRestore n a O.C (phaseOracle (O.N.pred n)) := by
    rintro m rfl h
    exact h
  exact key _ O.nData_eq (O.restore a ha)

/-- Report §6 (the `DiffusionCert(n)` of the Grover-iteration listing), §8.2 — the MCZ of the
V1 diffusion as a certified oracle: the synthesized oracle of `P_all` (`allNet n`). Its
well-formedness is a field of `OracleCert` (checked by `decide` at each instance). -/
structure DiffusionCert (n : ℕ) where
  mcz : OracleCert n
  hN : mcz.N = allNet n

/-! ## `P_all`: the predicate of `allNet n` -/

/-- After the input nodes `0..m−1`, the values are the input bits. -/
theorem foldl_inputs (x : ℕ → Bool) (m : ℕ) :
    (((List.range m).map Node.input).foldl (nodeStep x) #[]).size = m ∧
      ∀ i < m, (((List.range m).map Node.input).foldl (nodeStep x) #[]).getD i false = x i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, nodeStep, nodeVal,
      Array.size_push, ih.1, true_and]
    intro i hi
    rw [Array.getD_push_eq, ih.1]
    split_ifs with h
    · rw [h]
    · exact ih.2 i (by omega)

/-- The AND nodes of `allNet n`, in order: node `n + k` is `AND(y₀, y₁)` for `k = 0`, else
`AND(node n+k−1, y_{k+1})`. -/
def allAnds (n m : ℕ) : List Node :=
  (List.range m).map fun k => if k == 0 then Node.and 0 1 else Node.and (n + k - 1) (k + 1)

/-- After the first `m` AND nodes of the chain, node `n + j` holds `y₀ ∧ … ∧ y_{j+1}`. -/
theorem foldl_ands (x : ℕ → Bool) (n : ℕ) (vs : Array Bool) (hs : vs.size = n)
    (hv : ∀ i < n, vs.getD i false = x i) :
    ∀ m, m + 1 < n + 1 → m + 1 ≤ n →
      ((allAnds n m).foldl (nodeStep x) vs).size = n + m ∧
      (∀ i < n, ((allAnds n m).foldl (nodeStep x) vs).getD i false = x i) ∧
      ∀ j < m, ((allAnds n m).foldl (nodeStep x) vs).getD (n + j) false =
        (List.range (j + 2)).all x := by
  intro m
  induction m with
  | zero =>
    intro _ _
    refine ⟨by simp [allAnds, hs], fun i hi => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    simpa [allAnds] using hv i hi
  | succ m ih =>
    intro h1 h2
    obtain ⟨ihs, ihv, iha⟩ := ih (by omega) (by omega)
    rw [allAnds, List.range_succ, List.map_append, List.foldl_append, ← allAnds]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, nodeStep,
      Array.size_push, ihs]
    refine ⟨rfl, fun i hi => ?_, fun j hj => ?_⟩
    · rw [Array.getD_push_eq, ihs, ite_eq_right (by omega)]
      exact ihv i hi
    · rw [Array.getD_push_eq, ihs]
      by_cases hjm : j = m
      · subst hjm
        rw [ite_eq_left rfl]
        by_cases hj0 : j = 0
        · subst hj0
          simp only [beq_self_eq_true, ↓reduceIte, nodeVal, ihv 0 (by omega), ihv 1 (by omega)]
          simp [List.range_succ]
        · simp only [show (j == 0) = false from by simpa using hj0, Bool.false_eq_true,
            ↓reduceIte, nodeVal]
          rw [show n + j - 1 = n + (j - 1) by omega, iha (j - 1) (by omega),
            ihv (j + 1) (by omega), show j - 1 + 2 = j + 1 by omega,
            List.range_succ (n := j + 1), List.all_append]
          simp
      · rw [ite_eq_right (by omega)]
        exact iha j (by omega)

/-- Report §8.2 — the network `allNet n` computes `P_all(y) = y₀ ∧ … ∧ y_{n−1}` (`n ≥ 1`). -/
theorem allNet_pred {n : ℕ} (hn : n ≠ 0) : (allNet n).pred n = allOnes := by
  funext x
  have hnodes : (allNet n).nodes.toList = (List.range n).map Node.input ++ allAnds n (n - 1) := by
    simp [allNet, allAnds]
  have hv : (allNet n).values (inputOf x) =
      (allAnds n (n - 1)).foldl (nodeStep (inputOf x))
        (((List.range n).map Node.input).foldl (nodeStep (inputOf x)) #[]) := by
    rw [values_eq_valuesUpTo, valuesUpTo, List.take_of_length_le (by simp), hnodes,
      List.foldl_append]
  obtain ⟨hs, hi⟩ := foldl_inputs (inputOf x) n
  obtain ⟨-, hvi, hva⟩ := foldl_ands (inputOf x) n _ hs hi (n - 1) (by omega) (by omega)
  have hall : (List.range n).all (inputOf x) = allOnes x := by
    unfold allOnes
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    simp only [List.mem_range]
    exact ⟨fun h i => by simpa [inputOf] using h i.val i.isLt,
      fun h k hk => by simpa [inputOf, hk] using h ⟨k, hk⟩⟩
  have hout : (allNet n).outputs = [if n ≤ 1 then 0 else 2 * n - 2] := rfl
  unfold Network.pred Network.eval
  simp only [hout, List.map_cons, List.map_nil, List.headD_cons]
  change ((allNet n).values (inputOf x)).getD _ false = _
  rw [hv, ← hall]
  split_ifs with h1
  · obtain rfl : n = 1 := by omega
    rw [hvi 0 (by omega)]
    simp
  · rw [show 2 * n - 2 = n + (n - 2) by omega, hva (n - 2) (by omega),
      show n - 2 + 2 = n by omega]

/-- Report §8.2 — the MCZ certificate applies the phase oracle of `P_all`. -/
theorem DiffusionCert.P_eq {n : ℕ} (D : DiffusionCert n) (hn : n ≠ 0) : D.mcz.P = allOnes := by
  rw [OracleCert.P, D.hN, allNet_pred hn]

/-! ## Data-only layers -/

theorem unitaryDenote_append (n a : ℕ) (l₁ l₂ : List Gate) :
    unitaryDenote n a (l₁ ++ l₂) = unitaryDenote n a l₂ * unitaryDenote n a l₁ := by
  induction l₁ with
  | nil => simp [unitaryDenote]
  | cons g gs ih => simp [unitaryDenote, ih, Matrix.mul_assoc]

theorem hMat_mul_apply {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → Bool} {f : ι → ι}
    (hf : Function.Involutive f) (M : Matrix ι ι ℂ) (i j : ι) :
    (hMat b f * M) i j =
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if b i then -1 else 1) * M i j + M (f i) j) := by
  rw [Matrix.mul_apply]
  exact hMat_mulVec hf (fun s => M s j) i

/-- Report §8.2 — the first `k` Hadamards of `H^{⊗n}` on `Reg n` (identity on bits `≥ k`). -/
noncomputable def hUpTo (n k : ℕ) : Matrix (Reg n) (Reg n) ℂ := Matrix.of fun x y =>
  if ∀ i : Fin n, k ≤ i.val → x i = y i then
    ∏ i : Fin n, (if i.val < k then hEntry (x i) (y i) else 1)
  else 0

theorem hUpTo_zero (n : ℕ) : hUpTo n 0 = 1 := by
  ext x y
  simp [hUpTo, Matrix.one_apply, funext_iff]

theorem hUpTo_self (n : ℕ) : hUpTo n n = hadamardMat n := by
  ext x y
  have h1 : ∀ i : Fin n, ¬ n ≤ i.val := fun i => not_le.mpr i.isLt
  simp [hUpTo, hadamardMat, h1]

/-- One more Hadamard, on bit `k`, entrywise (`(H_k M)(x, y) = (1/√2)(±M(x, y) + M(x ⊕ eₖ, y))`). -/
theorem hUpTo_succ {n k : ℕ} (hk : k < n) (x y : Reg n) :
    ((Real.sqrt 2)⁻¹ : ℂ) * ((if x ⟨k, hk⟩ then -1 else 1) * hUpTo n k x y +
      hUpTo n k (Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩)) y) = hUpTo n (k + 1) x y := by
  have hprod : ∀ z : Reg n, (∏ i : Fin n, if i.val < k + 1 then hEntry (z i) (y i) else 1) =
      hEntry (z ⟨k, hk⟩) (y ⟨k, hk⟩) * ∏ i : Fin n, if i.val < k then hEntry (z i) (y i) else 1 := by
    intro z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ⟨k, hk⟩),
      ← Finset.mul_prod_erase Finset.univ (fun i : Fin n => if i.val < k then hEntry (z i) (y i)
        else 1) (Finset.mem_univ ⟨k, hk⟩)]
    simp only [Nat.lt_add_one, lt_self_iff_false, ↓reduceIte, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hik : i.val ≠ k := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    have : (i.val < k + 1) = (i.val < k) := propext (by omega)
    simp only [this]
  have hupd_ne : ∀ i : Fin n, i.val ≠ k →
      Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩) i = x i := fun i hi =>
    Function.update_of_ne (fun h => hi (by rw [h])) _ _
  have hcond : (∀ i : Fin n, k + 1 ≤ i.val → x i = y i) ↔
      (∀ i : Fin n, k + 1 ≤ i.val → Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩) i = y i) := by
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [hupd_ne i (by omega)]
  have hsplit : ∀ z : Reg n, (∀ i : Fin n, k ≤ i.val → z i = y i) ↔
      (z ⟨k, hk⟩ = y ⟨k, hk⟩ ∧ ∀ i : Fin n, k + 1 ≤ i.val → z i = y i) := by
    intro z
    constructor
    · intro h
      exact ⟨h _ le_rfl, fun i hi => h i (by omega)⟩
    · rintro ⟨h0, h⟩ i hi
      by_cases hik : i.val = k
      · rw [show i = ⟨k, hk⟩ from Fin.ext hik]
        exact h0
      · exact h i (by omega)
  have hprodu : (∏ i : Fin n, if i.val < k then
      hEntry (Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩) i) (y i) else 1) =
      ∏ i : Fin n, if i.val < k then hEntry (x i) (y i) else 1 :=
    Finset.prod_congr rfl fun i _ => by
      by_cases hi : i.val < k
      · rw [ite_eq_left hi, ite_eq_left hi, hupd_ne i (by omega)]
      · rw [ite_eq_right hi, ite_eq_right hi]
  simp only [hUpTo, Matrix.of_apply]
  simp only [hsplit x, hsplit (Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩)), ← hcond]
  rw [hprod x, hprodu]
  simp only [Function.update_self]
  generalize (∏ i : Fin n, if i.val < k then hEntry (x i) (y i) else 1) = p
  generalize x ⟨k, hk⟩ = b
  generalize y ⟨k, hk⟩ = c
  by_cases hR : ∀ i : Fin n, k < i.val → x i = y i
  · cases b <;> cases c <;> simp [hEntry]
  · simp [hR]

/-- `H` on data qubit `k` extends `hUpTo k ⊗ 1` to `hUpTo (k+1) ⊗ 1`. -/
theorem gateU_h_data_mul {n a k : ℕ} (hk : k < n) :
    gateU n a (.h (.data k)) * (hUpTo n k ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) =
      hUpTo n (k + 1) ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  have hq : (Qubit.data k).inRange n a = true := by simp [Qubit.inRange, hk]
  ext ⟨x, u⟩ ⟨y, v⟩
  simp only [gateU, hq, ↓reduceIte]
  rw [hMat_mul_apply (Qubit.flip_involutive _)]
  have hg : (Qubit.data k).get (x, u) = x ⟨k, hk⟩ := by simp [Qubit.get, hk]
  have hf : (Qubit.data k).flip (x, u) = (Function.update x ⟨k, hk⟩ (!x ⟨k, hk⟩), u) := by
    simp [Qubit.flip, Qubit.set, Qubit.get, hk]
  rw [hg, hf]
  simp only [Matrix.kroneckerMap_apply]
  rw [← hUpTo_succ hk x y]
  ring

/-- Report §8.2 — the layer `H^{⊗n}` (one `H` per data qubit) denotes `H^{⊗n} ⊗ 1`. -/
theorem unitaryDenote_hLayer (n a : ℕ) :
    unitaryDenote n a (Diffusion.onAll .h n) = hadamardMat n ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  have key : ∀ k ≤ n, unitaryDenote n a ((List.range k).map fun i => Gate.h (.data i)) =
      hUpTo n k ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
    intro k hk
    induction k with
    | zero => simp [unitaryDenote, hUpTo_zero]
    | succ k ih =>
      rw [List.range_succ, List.map_append, unitaryDenote_append, List.map_singleton,
        show unitaryDenote n a [Gate.h (.data k)] = gateU n a (.h (.data k)) from Matrix.one_mul _,
        ih (by omega), gateU_h_data_mul (by omega)]
  rw [Diffusion.onAll, key n le_rfl, hUpTo_self]

/-- Flip the first `k` bits. -/
def flipUpTo {n : ℕ} (k : ℕ) (x : Reg n) : Reg n := fun i => if i.val < k then !x i else x i

/-- Report §8.2 — the layer `X^{⊗n}` denotes `X^{⊗n} ⊗ 1`. -/
theorem unitaryDenote_xLayer (n a : ℕ) :
    unitaryDenote n a (Diffusion.onAll .x n) = xAllMat n ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) := by
  have key : ∀ k ≤ n, unitaryDenote n a ((List.range k).map fun i => Gate.x (.data i)) =
      monoMat (fun s : Reg n × Reg a => (flipUpTo k s.1, s.2)) (fun _ => 1) := by
    intro k hk
    induction k with
    | zero =>
      rw [List.range_zero, List.map_nil, unitaryDenote_nil, ← monoMat_id_one]
      congr 1
    | succ k ih =>
      rw [List.range_succ, List.map_append, unitaryDenote_append, List.map_singleton,
        show unitaryDenote n a [Gate.x (.data k)] = gateU n a (.x (.data k)) from Matrix.one_mul _,
        ih (by omega), gateU, monoMat_mul]
      congr 1
      · funext ⟨x, u⟩
        simp only [Function.comp_apply, Qubit.flip, Qubit.set, Qubit.get,
          show k < n by omega, ↓reduceDIte]
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
  rw [Diffusion.onAll, key n le_rfl]
  have hfl : ∀ y : Reg n, flipUpTo n y = notAll y := fun y => by
    funext i
    simp [flipUpTo, notAll, i.isLt]
  ext ⟨x, u⟩ ⟨y, v⟩
  simp only [monoMat_apply, xAllMat, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq,
    hfl]
  by_cases h1 : x = notAll y <;> by_cases h2 : u = v <;> simp [h1, h2]

theorem written_of_unitary {gs : List Gate} (h : gs.all Gate.isUnitary = true) :
    Circuit.written gs = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Circuit.written, List.flatMap_cons] at ih ⊢
    rw [ih h.2]
    cases g <;> simp_all [Gate.isUnitary, Gate.writes]

theorem bitsOkFrom_of_unitary (m : ℕ) (W : List ℕ) {gs : List Gate}
    (h : gs.all Gate.isUnitary = true) : Circuit.bitsOkFrom m W gs = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Circuit.bitsOkFrom, ih _ h.2, Bool.and_true]
    cases g <;> simp_all [Gate.isUnitary, Gate.bitOk]

/-- Report §6.2.4, §8.2 — a data-only unitary layer restores the ancillae: if the gate list is
unitary, on the data register, and denotes `U ⊗ 1`, then `AncRestore n a ⟨n, gs⟩ U`
(`ancRestore_of_kraus` with one branch and scalar 1). -/
theorem ancRestore_of_dataLayer {n a : ℕ} (gs : List Gate) (hu : gs.all Gate.isUnitary = true)
    (hq : gs.all (Gate.qubitsOk n) = true) (U : 𝐔[Reg n])
    (hU : unitaryDenote n a gs = U.val ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ)) :
    AncRestore n a ⟨n, gs⟩ U := by
  have hnb : (⟨n, gs⟩ : Circuit).nBits = 0 := by simp [Circuit.nBits, written_of_unitary hu]
  have hWF : (⟨n, gs⟩ : Circuit).WF := by
    simp only [Circuit.WF, Circuit.wf, Circuit.bitsOk, hq, bitsOkFrom_of_unitary _ _ hu,
      Bool.and_self]
  refine ancRestore_of_kraus hWF U (fun _ => 1) ?_ fun c => ?_
  · simp [hnb]
  · rw [krausOps_of_unitary n a _ gs hu, hU, ancProj, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, one_smul]

theorem onAll_unitary (g : Qubit → Gate) (hg : ∀ q, (g q).isUnitary = true) (n : ℕ) :
    (Diffusion.onAll g n).all Gate.isUnitary = true := by
  simp [Diffusion.onAll, hg]

theorem onAll_h_unitary (n : ℕ) : (Diffusion.onAll .h n).all Gate.isUnitary = true :=
  onAll_unitary Gate.h (fun _ => rfl) n

theorem onAll_x_unitary (n : ℕ) : (Diffusion.onAll .x n).all Gate.isUnitary = true :=
  onAll_unitary Gate.x (fun _ => rfl) n

/-- The wrappers `H^{⊗n} ; X^{⊗n}` and `X^{⊗n} ; H^{⊗n}` are unitary gate lists. -/
theorem pre_unitary (n : ℕ) :
    (Diffusion.onAll .h n ++ Diffusion.onAll .x n).all Gate.isUnitary = true := by
  rw [List.all_append, onAll_h_unitary, onAll_x_unitary]
  rfl

theorem post_unitary (n : ℕ) :
    (Diffusion.onAll .x n ++ Diffusion.onAll .h n).all Gate.isUnitary = true := by
  rw [List.all_append, onAll_h_unitary, onAll_x_unitary]
  rfl

theorem onAll_qubitsOk_h (n : ℕ) : (Diffusion.onAll .h n).all (Gate.qubitsOk n) = true := by
  simp [Diffusion.onAll, Gate.qubitsOk, Gate.qubits]

theorem onAll_qubitsOk_x (n : ℕ) : (Diffusion.onAll .x n).all (Gate.qubitsOk n) = true := by
  simp [Diffusion.onAll, Gate.qubitsOk, Gate.qubits]

/-- Report §8.2 — the initial layer `H^{⊗n}` restores the ancillae and applies `H^{⊗n}`. -/
theorem ancRestore_hLayer (n a : ℕ) :
    AncRestore n a ⟨n, Diffusion.onAll .h n⟩ (hadamardU n) :=
  ancRestore_of_dataLayer _ (onAll_h_unitary n) (onAll_qubitsOk_h n) _
    (unitaryDenote_hLayer n a)

/-- Report §8.2 — the diffusion prefix `H^{⊗n} ; X^{⊗n}` applies `X^{⊗n} H^{⊗n}`. -/
theorem ancRestore_pre (n a : ℕ) :
    AncRestore n a ⟨n, Diffusion.onAll .h n ++ Diffusion.onAll .x n⟩ (xAllU n * hadamardU n) := by
  refine ancRestore_of_dataLayer _ ?_ ?_ _ ?_
  · exact pre_unitary n
  · simp only [List.all_append, onAll_qubitsOk_h, onAll_qubitsOk_x, Bool.and_self]
  · rw [unitaryDenote_append, unitaryDenote_hLayer, unitaryDenote_xLayer,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rfl

/-- Report §8.2 — the diffusion suffix `X^{⊗n} ; H^{⊗n}` applies `H^{⊗n} X^{⊗n}`. -/
theorem ancRestore_post (n a : ℕ) :
    AncRestore n a ⟨n, Diffusion.onAll .x n ++ Diffusion.onAll .h n⟩ (hadamardU n * xAllU n) := by
  refine ancRestore_of_dataLayer _ ?_ ?_ _ ?_
  · exact post_unitary n
  · simp only [List.all_append, onAll_qubitsOk_h, onAll_qubitsOk_x, Bool.and_self]
  · rw [unitaryDenote_append, unitaryDenote_hLayer, unitaryDenote_xLayer,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rfl

theorem bitsOk_dataLayer (n : ℕ) (gs : List Gate) (hu : gs.all Gate.isUnitary = true) :
    (⟨n, gs⟩ : Circuit).bitsOk = true :=
  bitsOkFrom_of_unitary _ _ hu

/-! ## Diffusion, iteration, full circuit -/

/-- Report §6.2.4 — `AncRestore` only sees `U` through `U ρ Uᴴ`. -/
theorem _root_.CQRV.AncRestore.congr {n a : ℕ} {C : Circuit} {U V : 𝐔[Reg n]}
    (h : AncRestore n a C U) (hUV : ∀ ρ : MState (Reg n), U ◃ ρ = V ◃ ρ) : AncRestore n a C V :=
  fun ρ => by rw [h ρ, hUV]

/-- The V1 diffusion circuit (Stage 5b decision 1): `H X ; MCZ ; X H` by shifted appends. -/
def diffusionCircuit (n : ℕ) (mcz : Circuit) : Circuit :=
  ((⟨n, Diffusion.onAll .h n ++ Diffusion.onAll .x n⟩ : Circuit).append mcz).append
    ⟨n, Diffusion.onAll .x n ++ Diffusion.onAll .h n⟩

/-- Report §8.2, §6.2.4, decision 5 — the diffusion circuit restores the ancillae and applies
`U_s = 2|s⟩⟨s| − I`: the MCZ restores with `U_{P_all}` (Lemma 6.3.2), the wrappers with
`X H` and `H X`, `AncRestore.comp` twice, and the global sign of `−U_s` cancels. -/
theorem diffusion_ancRestore {n a : ℕ} (mcz : Circuit) (hb : mcz.bitsOk = true)
    (hmcz : AncRestore n a mcz (phaseOracle (allOnes (n := n)))) :
    AncRestore n a (diffusionCircuit n mcz) (diffU n) := by
  have hpre := bitsOk_dataLayer n (Diffusion.onAll .h n ++ Diffusion.onAll .x n)
    (pre_unitary n)
  have hpost := bitsOk_dataLayer n (Diffusion.onAll .x n ++ Diffusion.onAll .h n)
    (post_unitary n)
  have h := AncRestore.comp (Circuit.bitsOk_append hpre hb) hpost
    (AncRestore.comp hpre hb (ancRestore_pre n a) hmcz) (ancRestore_post n a)
  exact h.congr fun ρ => uConj_neg (diffusion_circuit_matrix n) ρ

/-- `diffusion n none` is the V1 diffusion circuit around the synthesized MCZ. -/
theorem diffusion_ok {n : ℕ} {D : Circuit} (h : diffusion n none = .ok D) :
    n ≠ 0 ∧ ∃ mcz, synthesizeOracle (allNet n) = .ok mcz ∧ D = diffusionCircuit n mcz := by
  unfold diffusion diffusionWith synthesizeWithBudget at h
  by_cases hn : n = 0
  · subst hn
    simp [Diffusion.fail, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map, bind,
      Except.bind] at h
  · refine ⟨hn, ?_⟩
    cases hs : synthesizeOracle (allNet n) with
    | error e =>
      simp [hs, hn, Functor.map, Except.map, bind, Except.bind] at h
    | ok mcz =>
      refine ⟨mcz, rfl, ?_⟩
      simp [hs, hn, Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at h
      exact h.symm

/-- `groverIteration P n` is the oracle of `P` appended with the diffusion. -/
theorem groverIteration_ok {P : Network} {n : ℕ} {it : Circuit}
    (h : groverIteration P n = .ok it) :
    ∃ oc d, synthesizeOracle P = .ok oc ∧ diffusion n none = .ok d ∧ it = oc.append d := by
  unfold groverIteration at h
  cases ho : synthesizeOracle P with
  | error e =>
    split_ifs at h <;> simp [ho, bind, Except.bind, Diffusion.fail, throw, throwThe,
      MonadExceptOf.throw] at h
  | ok oc =>
    cases hd : diffusion n none with
    | error e =>
      split_ifs at h <;> simp [ho, hd, bind, Except.bind, Diffusion.fail, throw, throwThe,
        MonadExceptOf.throw] at h
    | ok d =>
      refine ⟨oc, d, rfl, rfl, ?_⟩
      split_ifs at h <;> simp [ho, hd, bind, Except.bind, Diffusion.fail, throw, throwThe,
        MonadExceptOf.throw, pure, Except.pure] at h
      exact h.symm

/-- `groverCircuit P n r` is `H^{⊗n}` followed by `r` iterations. -/
theorem groverCircuit_ok {P : Network} {n r : ℕ} {C : Circuit}
    (h : groverCircuit P n r = .ok C) :
    ∃ it, groverIteration P n = .ok it ∧
      C = (List.replicate r it).foldl Circuit.append ⟨n, Diffusion.onAll .h n⟩ := by
  unfold groverCircuit at h
  rw [except_bind_eq_ok] at h
  obtain ⟨it, hit, h⟩ := h
  exact ⟨it, hit, (except_pure_eq_ok.mp h).symm⟩

/-! ### Ancilla count of a shifted append -/

/-- The step of `Circuit.nAnc`. -/
def ancStep (m : ℕ) (g : Gate) : ℕ :=
  g.qubits.foldl (fun m q => match q with | .anc i => Nat.max m (i + 1) | .data _ => m) m

theorem nAnc_eq (C : Circuit) : C.nAnc = C.gates.foldl ancStep 0 := rfl

theorem foldl_max_eq {α : Type} (F : ℕ → α → ℕ) (hF : ∀ m x, F m x = max m (F 0 x)) :
    ∀ (l : List α) (m : ℕ), l.foldl F m = max m (l.foldl F 0)
  | [], m => by simp
  | x :: l, m => by
    simp only [List.foldl_cons]
    rw [foldl_max_eq F hF l (F m x), foldl_max_eq F hF l (F 0 x), hF m x, max_assoc]

theorem ancStep_eq (m : ℕ) (g : Gate) : ancStep m g = max m (ancStep 0 g) := by
  unfold ancStep
  refine foldl_max_eq _ (fun m q => ?_) g.qubits m
  cases q <;> simp [max_def]

theorem Gate.qubits_shiftBits (k : ℕ) (g : Gate) : (g.shiftBits k).qubits = g.qubits := by
  cases g <;> rfl

theorem nAnc_append (C₁ C₂ : Circuit) : (C₁.append C₂).nAnc = max C₁.nAnc C₂.nAnc := by
  rw [nAnc_eq, nAnc_eq, nAnc_eq]
  change (C₁.gates ++ C₂.gates.map (Gate.shiftBits C₁.nBits)).foldl ancStep 0 = _
  have hs : (fun m g => ancStep m (Gate.shiftBits C₁.nBits g)) = ancStep := by
    funext m g
    unfold ancStep
    rw [Gate.qubits_shiftBits]
  rw [List.foldl_append, foldl_max_eq ancStep ancStep_eq, List.foldl_map, hs]

/-! ### The induction -/

/-- Report §8.2, §6.2.4 — one Grover iteration restores the ancillae and applies `G = U_s U_P`. -/
theorem iteration_ancRestore {n a : ℕ} (O : OracleCert n) (D : DiffusionCert n) (hn : n ≠ 0)
    (hO : O.C.nAnc ≤ a) (hD : D.mcz.C.nAnc ≤ a) :
    AncRestore n a (O.C.append (diffusionCircuit n D.mcz.C)) (groverOp O.P) := by
  have hmcz := D.mcz.ancRestore hD
  rw [D.P_eq hn] at hmcz
  have hdiff := diffusion_ancRestore D.mcz.C D.mcz.hWF.bitsOk hmcz
  refine AncRestore.comp O.hWF.bitsOk ?_ (O.ancRestore hO) hdiff
  exact Circuit.bitsOk_append (Circuit.bitsOk_append (bitsOk_dataLayer _ _
    (pre_unitary n))
    D.mcz.hWF.bitsOk) (bitsOk_dataLayer _ _
    (post_unitary n))

/-- Report §6.2.4 — restoration of `init` followed by `r` copies of `it`. -/
theorem ancRestore_foldl {n a : ℕ} (init it : Circuit) (U V : 𝐔[Reg n])
    (hi : init.bitsOk = true) (ht : it.bitsOk = true)
    (rinit : AncRestore n a init U) (rit : AncRestore n a it V) :
    ∀ r, ((List.replicate r it).foldl Circuit.append init).bitsOk = true ∧
      AncRestore n a ((List.replicate r it).foldl Circuit.append init) (V ^ r * U)
  | 0 => ⟨hi, by simpa using rinit⟩
  | r + 1 => by
    obtain ⟨hb, hr⟩ := ancRestore_foldl init it U V hi ht rinit rit r
    rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ',
      mul_assoc]
    exact ⟨Circuit.bitsOk_append hb ht, AncRestore.comp hb ht hr rit⟩

/-- Report §8.2.4, §8.3.3 — **the restoration conjunct of `grover_parametric_lemma`**: the
Grover circuit `H^{⊗n} ; (U_P ; D_n)^r` (V1 diffusion, synthesized by `groverCircuit`) on
`Reg n × Reg C.nAnc` restores its ancillae and applies `G^r H^{⊗n}` with `G = U_s U_P`. -/
theorem grover_ancRestore {n r : ℕ} (O : OracleCert n) (D : DiffusionCert n) {C : Circuit}
    (hC : groverCircuit O.N n r = .ok C) :
    AncRestore n C.nAnc C (groverOp O.P ^ r * hadamardU n) := by
  obtain ⟨it, hit, rfl⟩ := groverCircuit_ok hC
  obtain ⟨oc, d, hoc, hd, rfl⟩ := groverIteration_ok hit
  obtain rfl : oc = O.C := Except.ok.inj (hoc.symm.trans O.hC)
  obtain ⟨hn, mcz, hmcz, rfl⟩ := diffusion_ok hd
  obtain rfl : mcz = D.mcz.C := Except.ok.inj (hmcz.symm.trans (D.hN ▸ D.mcz.hC))
  cases r with
  | zero => simpa using ancRestore_hLayer n _
  | succ k =>
    set it := O.C.append (diffusionCircuit n D.mcz.C) with hit_def
    set Cf := (List.replicate (k + 1) it).foldl Circuit.append
      (⟨n, Diffusion.onAll .h n⟩ : Circuit) with hCf
    have hle : it.nAnc ≤ Cf.nAnc := by
      have hsplit : Cf = ((List.replicate k it).foldl Circuit.append
          (⟨n, Diffusion.onAll .h n⟩ : Circuit)).append it := by
        rw [hCf, List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsplit, nAnc_append _ it]
      exact Nat.le_max_right _ _
    have hO : O.C.nAnc ≤ Cf.nAnc := by
      refine le_trans ?_ hle
      rw [hit_def, nAnc_append]
      exact le_max_left _ _
    have hD : D.mcz.C.nAnc ≤ Cf.nAnc := by
      refine le_trans ?_ hle
      rw [hit_def, nAnc_append, diffusionCircuit, nAnc_append, nAnc_append]
      exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    have hitb : it.bitsOk = true :=
      Circuit.bitsOk_append O.hWF.bitsOk (Circuit.bitsOk_append (Circuit.bitsOk_append
        (bitsOk_dataLayer _ _ (pre_unitary n)) D.mcz.hWF.bitsOk)
        (bitsOk_dataLayer _ _ (post_unitary n)))
    exact (ancRestore_foldl _ _ _ _ (bitsOk_dataLayer _ _ (onAll_h_unitary n)) hitb
      (ancRestore_hLayer n _) (iteration_ancRestore O D hn hO hD) (k + 1)).2

end CQRV.Grover

end
