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
* Stage 11a: `allNet_WF` (`n ≥ 1`), `diffusion_WF`, and the constructors `OracleCert.ofNetwork`,
  `DiffusionCert.mk'`, whose `hWF` comes from `synthesizeOracle_WF` instead of `decide`.
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

/-- PHASE2_SPEC.md §A.0.1 (Stage 15b), report §5.2.4 — a certified oracle in uncomputation mode
`coherent`: as `OracleCert` (which is unchanged: the committed certificates construct it) with
`synthesizeOracle N .coherent = .ok C`; the restoration field is filled by Lemma 6.3.2 in mode
`coherent` (`lemma_6_3_2_coherent_of_le`), never assumed. -/
structure OracleCertCoh (n : ℕ) where
  /-- The Boolean network of the predicate (§6.1.2). -/
  N : Network
  /-- The synthesized oracle circuit in mode `coherent` (§6.1.4, PHASE2_SPEC.md §A.0.1). -/
  C : Circuit
  hn : N.nInputs = n
  hC : synthesizeOracle N .coherent = .ok C
  hWF : C.WF
  /-- Lemma 6.3.2 in mode `coherent` (filled by the proof). -/
  restore : ∀ a, C.nAnc ≤ a → AncRestore C.nData a C (phaseOracle (N.pred C.nData)) :=
    fun a ha => lemma_6_3_2_coherent_of_le N C hC hWF a ha

/-- The predicate `P : Reg n → Bool` of a coherent oracle certificate. -/
def OracleCertCoh.P {n : ℕ} (O : OracleCertCoh n) : Reg n → Bool := O.N.pred n

/-- The synthesized circuit acts on the `N.nInputs = n` data qubits. -/
theorem OracleCertCoh.nData_eq {n : ℕ} (O : OracleCertCoh n) : O.C.nData = n := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := synthesizeOracle_okM O.hC
  rw [hC]
  exact O.hn

/-- Lemma 6.3.2 in mode `coherent` for a coherent oracle certificate, on `Reg n × Reg a`. -/
theorem OracleCertCoh.ancRestore {n : ℕ} (O : OracleCertCoh n) {a : ℕ} (ha : O.C.nAnc ≤ a) :
    AncRestore n a O.C (phaseOracle O.P) := by
  have key : ∀ m, m = n → AncRestore m a O.C (phaseOracle (O.N.pred m)) →
      AncRestore n a O.C (phaseOracle (O.N.pred n)) := by
    rintro m rfl h
    exact h
  exact key _ O.nData_eq (O.restore a ha)

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

/-! ## Stage 12a — the balanced AND tree `treeNet n` -/

/-- Report §6.1.2 — node `k + i` of the list `ns` is an AND whose operands are below `k + i`
(the topological-order clause of `Network.wf` for appended AND nodes). -/
def AndsBelow : ℕ → List Node → Prop
  | _, [] => True
  | k, v :: ns => (match v with | .and i j => i < k ∧ j < k | _ => False) ∧ AndsBelow (k + 1) ns

theorem AndsBelow.append {k : ℕ} {a b : List Node} (ha : AndsBelow k a)
    (hb : AndsBelow (k + a.length) b) : AndsBelow k (a ++ b) := by
  induction a generalizing k with
  | nil => simpa using hb
  | cons v a ih =>
    simp only [AndsBelow, List.cons_append] at ha ⊢
    rw [List.length_cons, show k + (a.length + 1) = k + 1 + a.length by omega] at hb
    exact ⟨ha.1, ih ha.2 hb⟩

theorem AndsBelow.getElem? {k : ℕ} {ns : List Node} (h : AndsBelow k ns) {idx : ℕ}
    (hi : idx < ns.length) : ∃ i j, ns[idx]? = some (.and i j) ∧ i < k + idx ∧ j < k + idx := by
  induction ns generalizing k idx with
  | nil => simp at hi
  | cons v ns ih =>
    simp only [AndsBelow] at h
    cases idx with
    | zero =>
      cases v
      case and i j => exact ⟨i, j, rfl, by simpa using h.1.1, by simpa using h.1.2⟩
      all_goals exact False.elim h.1
    | succ idx =>
      obtain ⟨i, j, he, h1, h2⟩ := ih h.2 (by simpa using hi)
      exact ⟨i, j, by simpa using he, by omega, by omega⟩

/-- Pushing a value does not change the values at indices below the old size. -/
theorem all_getD_push {l : List ℕ} {vs : Array Bool} {b : Bool} (h : ∀ m ∈ l, m < vs.size) :
    l.all (fun m => (vs.push b).getD m false) = l.all (fun m => vs.getD m false) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [List.all_cons]
    rw [Array.getD_push_eq, ite_eq_right (by have := h m (by simp); omega),
      ih (fun m' hm' => h m' (by simp [hm']))]

/-- One level of the tree (`treeLevel l k`, new nodes from `k`) on values `vs` of the first `k`
nodes: the size grows by the new nodes, old values stay, the conjunction over the next level
equals the conjunction over `l`, the next level lies below the new size, the new nodes are ANDs
of earlier nodes, and the next level has `⌈|l| / 2⌉` entries. -/
theorem treeLevel_spec (x : ℕ → Bool) : ∀ (l : List ℕ) (k : ℕ) (vs : Array Bool),
    vs.size = k → (∀ i ∈ l, i < k) →
    ((treeLevel l k).1.foldl (nodeStep x) vs).size = k + (treeLevel l k).1.length ∧
    (∀ i < k, ((treeLevel l k).1.foldl (nodeStep x) vs).getD i false = vs.getD i false) ∧
    (treeLevel l k).2.all (fun i => ((treeLevel l k).1.foldl (nodeStep x) vs).getD i false) =
      l.all (fun i => vs.getD i false) ∧
    (∀ j ∈ (treeLevel l k).2, j < k + (treeLevel l k).1.length) ∧
    AndsBelow k (treeLevel l k).1 ∧
    (treeLevel l k).2.length = (l.length + 1) / 2
  | [], k, vs, hs, _ => by simp [treeLevel, hs, AndsBelow]
  | [i], k, vs, hs, hl => by
    simp [treeLevel, hs, AndsBelow, hl i (by simp)]
  | i :: j :: rest, k, vs, hs, hl => by
    have hi : i < k := hl i (by simp)
    have hj : j < k := hl j (by simp)
    have hs' : (vs.push (vs.getD i false && vs.getD j false)).size = k + 1 := by simp [hs]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := treeLevel_spec x rest (k + 1)
      (vs.push (vs.getD i false && vs.getD j false)) hs'
      (fun m hm => Nat.lt_succ_of_lt (hl m (by simp [hm])))
    have hstep : nodeStep x vs (.and i j) = vs.push (vs.getD i false && vs.getD j false) := rfl
    simp only [treeLevel, List.foldl_cons, hstep, List.length_cons]
    refine ⟨by rw [h1]; omega, fun m hm => ?_, ?_, fun m hm => ?_, ?_, by rw [h6]; omega⟩
    · rw [h2 m (by omega), Array.getD_push_eq, ite_eq_right (by omega)]
    · rw [List.all_cons, h3, h2 k (by omega), Array.getD_push_eq, ite_eq_left hs.symm,
        all_getD_push (fun m hm => hs ▸ hl m (by simp [hm]))]
      simp [Bool.and_assoc]
    · rcases List.mem_cons.mp hm with rfl | hm
      · omega
      · have := h4 m hm
        omega
    · simp only [AndsBelow]
      exact ⟨⟨hi, hj⟩, h5⟩

/-- The levels of the tree: for a non-empty level `l` below `k` with `|l| ≤ fuel + 1`, the root's
value after the new nodes is the conjunction over `l`; the root lies below the new size; the
new nodes are ANDs of earlier nodes. -/
theorem treeBuild_spec (x : ℕ → Bool) : ∀ (f : ℕ) (l : List ℕ) (k : ℕ) (vs : Array Bool),
    vs.size = k → (∀ i ∈ l, i < k) → l ≠ [] → l.length ≤ f + 1 →
    ((treeBuild f l k).1.foldl (nodeStep x) vs).getD (treeBuild f l k).2 false =
      l.all (fun i => vs.getD i false) ∧
    (treeBuild f l k).2 < k + (treeBuild f l k).1.length ∧
    AndsBelow k (treeBuild f l k).1 := by
  have single : ∀ (l : List ℕ) (k : ℕ) (vs : Array Bool), (∀ i ∈ l, i < k) → l ≠ [] →
      l.length ≤ 1 →
      (([] : List Node).foldl (nodeStep x) vs).getD (l.headD 0) false =
        l.all (fun i => vs.getD i false) ∧
      l.headD 0 < k + ([] : List Node).length ∧ AndsBelow k [] := by
    intro l k vs hl hne hlen
    match l, hne, hlen with
    | [i], _, _ => simp [AndsBelow, hl i (by simp)]
    | _ :: _ :: _, _, hlen => simp at hlen
  intro f
  induction f with
  | zero => exact fun l k vs _ hl hne hlen => single l k vs hl hne hlen
  | succ f ih =>
    intro l k vs hs hl hne hlen
    simp only [treeBuild]
    split_ifs with h1
    · exact single l k vs hl hne h1
    · obtain ⟨h1', -, h3', h4', h5', h6'⟩ := treeLevel_spec x l k vs hs hl
      have hne' : (treeLevel l k).2 ≠ [] := by
        intro h
        rw [h, List.length_nil] at h6'
        omega
      obtain ⟨g1, g2, g3⟩ := ih (treeLevel l k).2 (k + (treeLevel l k).1.length) _ h1' h4'
        hne' (by omega)
      refine ⟨?_, ?_, AndsBelow.append h5' g3⟩
      · rw [List.foldl_append, g1, h3']
      · rw [List.length_append]
        omega

/-- The values of the input nodes `0..n−1` of `treeNet n` (and of `allNet n`). -/
def inputValues (x : ℕ → Bool) (n : ℕ) : Array Bool :=
  ((List.range n).map Node.input).foldl (nodeStep x) #[]

/-- The root step of `treeNet n` over its inputs. -/
theorem treeNet_spec (x : ℕ → Bool) {n : ℕ} (hn : n ≠ 0) :
    ((treeBuild n (List.range n) n).1.foldl (nodeStep x) (inputValues x n)).getD
        (treeBuild n (List.range n) n).2 false =
      (List.range n).all (fun i => (inputValues x n).getD i false) ∧
    (treeBuild n (List.range n) n).2 < n + (treeBuild n (List.range n) n).1.length ∧
    AndsBelow n (treeBuild n (List.range n) n).1 :=
  treeBuild_spec x n (List.range n) n _ (foldl_inputs x n).1 (fun _ hi => List.mem_range.mp hi)
    (fun h => hn (by simpa using congrArg List.length h)) (by simp)

/-- Report §8.2 (Stage 12a decision 1) — the balanced tree `treeNet n` computes
`P_all(y) = y₀ ∧ … ∧ y_{n−1}` (`n ≥ 1`), as the chain does (`allNet_pred`). -/
theorem treeNet_pred {n : ℕ} (hn : n ≠ 0) : (treeNet n).pred n = allOnes := by
  funext x
  have hnodes : (treeNet n).nodes.toList =
      (List.range n).map Node.input ++ (treeBuild n (List.range n) n).1 := by
    simp [treeNet]
  have hv : (treeNet n).values (inputOf x) =
      (treeBuild n (List.range n) n).1.foldl (nodeStep (inputOf x)) (inputValues (inputOf x) n) := by
    rw [values_eq_valuesUpTo, valuesUpTo, List.take_of_length_le (by simp), hnodes,
      List.foldl_append, inputValues]
  obtain ⟨-, hi⟩ := foldl_inputs (inputOf x) n
  obtain ⟨h1, -, -⟩ := treeNet_spec (inputOf x) hn
  have hcongr : (List.range n).all (fun i => (inputValues (inputOf x) n).getD i false) =
      (List.range n).all (inputOf x) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range]
    exact ⟨fun h k hk => by rw [← hi k hk]; exact h k hk,
      fun h k hk => by rw [inputValues, hi k hk]; exact h k hk⟩
  have hall : (List.range n).all (inputOf x) = allOnes x := by
    unfold allOnes
    rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
    simp only [List.mem_range]
    exact ⟨fun h i => by simpa [inputOf] using h i.val i.isLt,
      fun h k hk => by simpa [inputOf, hk] using h ⟨k, hk⟩⟩
  have hout : (treeNet n).outputs = [(treeBuild n (List.range n) n).2] := rfl
  unfold Network.pred Network.eval
  simp only [hout, List.map_cons, List.map_nil, List.headD_cons]
  change ((treeNet n).values (inputOf x)).getD _ false = _
  rw [hv, h1, hcongr, hall]

/-- Report §8.2, §6.1.2 (Stage 12a decision 1) — `treeNet n` is well formed for `n ≥ 1` (for
`n = 0` it is not, as `allNet 0`: no nodes, output index `0`). -/
theorem treeNet_WF {n : ℕ} (hn : n ≠ 0) : (treeNet n).WF := by
  obtain ⟨-, ho, hA⟩ := treeNet_spec (fun _ => false) hn
  have hnodes : (treeNet n).nodes =
      ((List.range n).map Node.input ++ (treeBuild n (List.range n) n).1).toArray := by
    simp [treeNet]
  have hsize : (treeNet n).nodes.size = n + (treeBuild n (List.range n) n).1.length := by
    simp [hnodes]
  unfold Network.WF Network.wf
  rw [show (treeNet n).nInputs = n from rfl, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun k hk => ?_, fun o ho' => ?_⟩
  · rw [List.mem_range, hsize] at hk
    rw [hnodes, List.getElem?_toArray]
    by_cases hkn : k < n
    · rw [List.getElem?_append_left (by simpa using hkn), List.getElem?_map,
        List.getElem?_range hkn]
      simpa using hkn
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      obtain ⟨i, j, he, h1, h2⟩ := hA.getElem? (idx := k - n) (by omega)
      rw [he]
      simp [show i < k by omega, show j < k by omega]
  · have ho'' : o = (treeBuild n (List.range n) n).2 := by simpa [treeNet] using ho'
    rw [ho'', hsize]
    simpa using ho

/-- Report §6 (the `DiffusionCert(n)` of the Grover-iteration listing), §8.2 — the MCZ of the
V1 diffusion as a certified oracle: the synthesized oracle of a network `net` that computes
`P_all`. Stage 12a decision 2: `net` defaults to the chain `allNet n` and `hPred` is filled
automatically for `allNet` and `treeNet` at a numeral `n`, so `{ mcz := …, hN := rfl }` still
denotes the chain certificate (Stage 7a); the tree certificate sets `net := treeNet n`.
Well-formedness is a field of `OracleCert` (`decide` at each instance, or `synthesizeOracle_WF`). -/
structure DiffusionCert (n : ℕ) where
  /-- The network of the MCZ (§8.2): `allNet n` (default) or `treeNet n`. -/
  net : Network := allNet n
  mcz : OracleCert n
  hN : mcz.N = net
  /-- `net` computes `P_all` (`allNet_pred`, `treeNet_pred`). -/
  hPred : net.pred n = allOnes := by
    first
    | (with_reducible apply allNet_pred) <;> decide
    | (with_reducible apply treeNet_pred) <;> decide

/-- Report §8.2 — the MCZ certificate applies the phase oracle of `P_all` (Stage 12a: by the
field `hPred`; the hypothesis `n ≠ 0` is no longer used, the statement is unchanged). -/
theorem DiffusionCert.P_eq {n : ℕ} (D : DiffusionCert n) (_hn : n ≠ 0) : D.mcz.P = allOnes := by
  rw [OracleCert.P, D.hN, D.hPred]

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

/-- `diffusion n none s mode` is the V1 diffusion circuit around the MCZ of `diffusionNet s n`
synthesized in `mode` (Stage 12a, either shape; Stage 15b, either uncomputation mode). -/
theorem diffusion_ok_mode {n : ℕ} {s : DiffusionShape} {mode : UncomputeMode} {D : Circuit}
    (h : diffusion n none s mode = .ok D) :
    n ≠ 0 ∧ ∃ mcz, synthesizeOracle (diffusionNet s n) mode = .ok mcz ∧
      D = diffusionCircuit n mcz := by
  unfold diffusion diffusionWith synthesizeWithBudget at h
  by_cases hn : n = 0
  · subst hn
    simp [Diffusion.fail, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map, bind,
      Except.bind] at h
  · refine ⟨hn, ?_⟩
    cases hs : synthesizeOracle (diffusionNet s n) mode with
    | error e =>
      simp [hs, hn, Functor.map, Except.map, bind, Except.bind] at h
    | ok mcz =>
      refine ⟨mcz, rfl, ?_⟩
      simp [hs, hn, Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at h
      exact h.symm

/-- `diffusion n none s` is the V1 diffusion circuit around the synthesized MCZ of
`diffusionNet s n` (Stage 12a, either shape): `diffusion_ok_mode` in mode `mbu`. -/
theorem diffusion_ok_shape {n : ℕ} {s : DiffusionShape} {D : Circuit}
    (h : diffusion n none s = .ok D) :
    n ≠ 0 ∧ ∃ mcz, synthesizeOracle (diffusionNet s n) = .ok mcz ∧ D = diffusionCircuit n mcz :=
  diffusion_ok_mode h

/-- `diffusion n none .chain` is the V1 diffusion circuit around the synthesized MCZ of the
chain: the Stage 7a statement of `diffusion_ok`, kept for the chain (Stage 12a). -/
theorem diffusion_ok_chain {n : ℕ} {D : Circuit} (h : diffusion n none .chain = .ok D) :
    n ≠ 0 ∧ ∃ mcz, synthesizeOracle (allNet n) = .ok mcz ∧ D = diffusionCircuit n mcz :=
  diffusion_ok_shape h

/-- `diffusion n none` is the V1 diffusion circuit around the synthesized MCZ of the balanced
tree, the default shape since Stage 12a. -/
theorem diffusion_ok {n : ℕ} {D : Circuit} (h : diffusion n none = .ok D) :
    n ≠ 0 ∧ ∃ mcz, synthesizeOracle (treeNet n) = .ok mcz ∧ D = diffusionCircuit n mcz :=
  diffusion_ok_shape h

/-- `groverIteration P n none s mode` is the oracle of `P` (in `mode`) appended with the diffusion
of shape `s` (in `mode`). -/
theorem groverIteration_ok_mode {P : Network} {n : ℕ} {s : DiffusionShape}
    {mode : UncomputeMode} {it : Circuit} (h : groverIteration P n none s mode = .ok it) :
    ∃ oc d, synthesizeOracle P mode = .ok oc ∧ diffusion n none s mode = .ok d ∧
      it = oc.append d := by
  unfold groverIteration at h
  cases ho : synthesizeOracle P mode with
  | error e =>
    split_ifs at h <;> simp [ho, bind, Except.bind, Diffusion.fail, throw, throwThe,
      MonadExceptOf.throw] at h
  | ok oc =>
    cases hd : diffusion n none s mode with
    | error e =>
      split_ifs at h <;> simp [ho, hd, bind, Except.bind, Diffusion.fail, throw, throwThe,
        MonadExceptOf.throw] at h
    | ok d =>
      refine ⟨oc, d, rfl, rfl, ?_⟩
      split_ifs at h <;> simp [ho, hd, bind, Except.bind, Diffusion.fail, throw, throwThe,
        MonadExceptOf.throw, pure, Except.pure] at h
      exact h.symm

/-- `groverIteration P n none s` is the oracle of `P` appended with the diffusion of shape `s`:
`groverIteration_ok_mode` in mode `mbu`. -/
theorem groverIteration_ok_shape {P : Network} {n : ℕ} {s : DiffusionShape} {it : Circuit}
    (h : groverIteration P n none s = .ok it) :
    ∃ oc d, synthesizeOracle P = .ok oc ∧ diffusion n none s = .ok d ∧ it = oc.append d :=
  groverIteration_ok_mode h

/-- `groverIteration P n` is the oracle of `P` appended with the diffusion. -/
theorem groverIteration_ok {P : Network} {n : ℕ} {it : Circuit}
    (h : groverIteration P n = .ok it) :
    ∃ oc d, synthesizeOracle P = .ok oc ∧ diffusion n none = .ok d ∧ it = oc.append d :=
  groverIteration_ok_shape h

/-- `groverCircuit P n r none s mode` is `H^{⊗n}` followed by `r` iterations of shape `s` in
`mode`. -/
theorem groverCircuit_ok_mode {P : Network} {n r : ℕ} {s : DiffusionShape} {mode : UncomputeMode}
    {C : Circuit} (h : groverCircuit P n r none s mode = .ok C) :
    ∃ it, groverIteration P n none s mode = .ok it ∧
      C = (List.replicate r it).foldl Circuit.append ⟨n, Diffusion.onAll .h n⟩ := by
  unfold groverCircuit at h
  rw [except_bind_eq_ok] at h
  obtain ⟨it, hit, h⟩ := h
  exact ⟨it, hit, (except_pure_eq_ok.mp h).symm⟩

/-- `groverCircuit P n r none s` is `H^{⊗n}` followed by `r` iterations of shape `s`:
`groverCircuit_ok_mode` in mode `mbu`. -/
theorem groverCircuit_ok_shape {P : Network} {n r : ℕ} {s : DiffusionShape} {C : Circuit}
    (h : groverCircuit P n r none s = .ok C) :
    ∃ it, groverIteration P n none s = .ok it ∧
      C = (List.replicate r it).foldl Circuit.append ⟨n, Diffusion.onAll .h n⟩ :=
  groverCircuit_ok_mode h

/-- `groverCircuit P n r` is `H^{⊗n}` followed by `r` iterations. -/
theorem groverCircuit_ok {P : Network} {n r : ℕ} {C : Circuit}
    (h : groverCircuit P n r = .ok C) :
    ∃ it, groverIteration P n = .ok it ∧
      C = (List.replicate r it).foldl Circuit.append ⟨n, Diffusion.onAll .h n⟩ :=
  groverCircuit_ok_shape h

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


/-! ## Stage 11a — `allNet_WF`, the diffusion is well formed, constructors without `decide` -/

/-- Report §8.2, §6.1.2 (Stage 11a item 2) — the network of `P_all` is well formed for `n ≥ 1`.
For `n = 0` it is not: `allNet 0` has no nodes and the output index `0` (`diffusion 0 none`
fails, so the corollaries below need no case `n = 0`). -/
theorem allNet_WF {n : ℕ} (hn : n ≠ 0) : (allNet n).WF := by
  have hnodes : (allNet n).nodes =
      ((List.range n).map Node.input ++ allAnds n (n - 1)).toArray := by
    simp [allNet, allAnds]
  have hsize : (allNet n).nodes.size = n + (n - 1) := by simp [hnodes, allAnds]
  have hnI : (allNet n).nInputs = n := rfl
  unfold Network.WF Network.wf
  rw [hnI, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun k hk => ?_, fun o ho => ?_⟩
  · rw [List.mem_range, hsize] at hk
    rw [hnodes, List.getElem?_toArray]
    by_cases hkn : k < n
    · rw [List.getElem?_append_left (by simpa using hkn), List.getElem?_map,
        List.getElem?_range hkn]
      simpa using hkn
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range, allAnds, List.getElem?_map,
        List.getElem?_range (by omega : k - n < n - 1), Option.map_some]
      by_cases hk0 : k - n = 0
      · simp [hk0]; omega
      · simp [hk0]; omega
  · have ho' : o = if n ≤ 1 then 0 else 2 * n - 2 := by simpa [allNet] using ho
    rw [ho', hsize]
    split_ifs <;> simp <;> omega

/-- Report §9.1.1 — a unitary data-only layer on `x[0..n)` is well formed. -/
theorem dataLayer_WF (n : ℕ) (gs : List Gate) (hu : gs.all Gate.isUnitary = true)
    (hq : ∀ g ∈ gs, g.qubitsOk n = true) : (⟨n, gs⟩ : Circuit).WF := by
  unfold Circuit.WF Circuit.wf
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨hq, bitsOk_dataLayer n gs hu⟩

/-- One single-qubit gate on each of `x[0..n)` passes `qubitsOk n`. -/
theorem onAll_qubitsOk (g : Qubit → Gate) (n : ℕ)
    (hg : ∀ i, i < n → (g (.data i)).qubitsOk n = true) :
    ∀ x ∈ Diffusion.onAll g n, x.qubitsOk n = true := by
  intro x hx
  simp only [Diffusion.onAll, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact hg i hi

/-- Report §8.2 (Stage 12a) — the network of either shape has `n` inputs. -/
theorem diffusionNet_nInputs (s : DiffusionShape) (n : ℕ) : (diffusionNet s n).nInputs = n := by
  cases s <;> rfl

/-- Report §8.2 (Stage 12a) — the network of either shape computes `P_all` (`n ≥ 1`). -/
theorem diffusionNet_pred (s : DiffusionShape) {n : ℕ} (hn : n ≠ 0) :
    (diffusionNet s n).pred n = allOnes := by
  cases s
  · exact treeNet_pred hn
  · exact allNet_pred hn

/-- Report §8.2, §6.1.2 (Stage 12a) — the network of either shape is well formed (`n ≥ 1`). -/
theorem diffusionNet_WF (s : DiffusionShape) {n : ℕ} (hn : n ≠ 0) : (diffusionNet s n).WF := by
  cases s
  · exact treeNet_WF hn
  · exact allNet_WF hn

/-- Report §8.2, §9.1.1 (Stage 11a item 2; Stage 12a: either shape) — the V1 diffusion circuit is
well formed for every `n` for which it is synthesized: its MCZ by `synthesizeOracle_WF` and
`diffusionNet_WF`, the `H` / `X` layers directly, the pieces joined by `Circuit.WF_append`. -/
theorem diffusion_WF_shape {n : ℕ} {s : DiffusionShape} {D : Circuit}
    (h : diffusion n none s = .ok D) : D.WF := by
  obtain ⟨hn, mcz, hmcz, rfl⟩ := diffusion_ok_shape h
  have hm := synthesizeOracle_WF (diffusionNet_WF s hn) hmcz
  have hmd : mcz.nData = n := by
    obtain ⟨_, _, _, _, _, _, hC⟩ := synthesizeOracle_ok hmcz
    rw [hC]
    exact diffusionNet_nInputs s n
  have h1 : ∀ i, i < n → (Gate.h (.data i)).qubitsOk n = true := fun i hi => by
    simp [Gate.qubitsOk, Gate.qubits, hi]
  have h2 : ∀ i, i < n → (Gate.x (.data i)).qubitsOk n = true := fun i hi => by
    simp [Gate.qubitsOk, Gate.qubits, hi]
  have hpre : (⟨n, Diffusion.onAll .h n ++ Diffusion.onAll .x n⟩ : Circuit).WF :=
    dataLayer_WF n _ (pre_unitary n) (fun g hg => (List.mem_append.mp hg).elim
      (onAll_qubitsOk _ n h1 g) (onAll_qubitsOk _ n h2 g))
  have hpost : (⟨n, Diffusion.onAll .x n ++ Diffusion.onAll .h n⟩ : Circuit).WF :=
    dataLayer_WF n _ (post_unitary n) (fun g hg => (List.mem_append.mp hg).elim
      (onAll_qubitsOk _ n h2 g) (onAll_qubitsOk _ n h1 g))
  exact Circuit.WF_append rfl (Circuit.WF_append hmd.symm hpre hm) hpost

/-- Report §8.2, §9.1.1 (Stage 11a item 2) — the V1 diffusion circuit (default shape) is well
formed for every `n` for which it is synthesized (`diffusion_WF_shape`). -/
theorem diffusion_WF {n : ℕ} {D : Circuit} (h : diffusion n none = .ok D) : D.WF :=
  diffusion_WF_shape h

/-- Report §5.2.4, §6.3.2 (Stage 11a item 3) — the certified oracle of a well-formed network:
`hWF` is filled by `synthesizeOracle_WF`, not by a per-instance `decide`. -/
def OracleCert.ofNetwork (N : Network) {C : Circuit} (hN : N.WF)
    (hC : synthesizeOracle N = .ok C) : OracleCert N.nInputs where
  N := N
  C := C
  hn := rfl
  hC := hC
  hWF := synthesizeOracle_WF hN hC

/-- The MCZ of `P_all` is synthesized only for `n ≥ 1`. -/
theorem allNet_ok_ne_zero {n : ℕ} {C : Circuit} (hC : synthesizeOracle (allNet n) = .ok C) :
    n ≠ 0 := by
  rintro rfl
  have h : (synthesizeOracle (allNet 0)).toBool = false := by decide
  rw [hC] at h
  cases h

/-- Report §6 (`DiffusionCert(n)`), §8.2 (Stage 11a item 3) — the MCZ certificate for every `n`
whose MCZ is synthesized: `hWF` from `synthesizeOracle_WF` and `allNet_WF`. -/
def DiffusionCert.mk' (n : ℕ) {C : Circuit} (hC : synthesizeOracle (allNet n) = .ok C) :
    DiffusionCert n where
  mcz := { N := allNet n, C := C, hn := rfl, hC := hC,
           hWF := synthesizeOracle_WF (allNet_WF (allNet_ok_ne_zero hC)) hC }
  hN := rfl
  hPred := allNet_pred (allNet_ok_ne_zero hC)

/-- Report §5.2.4, §6.3.2 (Stage 13c) — the certified oracle of a well-formed one-output network,
with no synthesis hypothesis: `synthesizeOracle_succeeds` rules out the error branch. Computable
(a match on `synthesizeOracle N`, not `Classical.choose`). -/
def OracleCert.ofWF (N : Network) (hN : N.WF) (h1 : N.outputs.length = 1) :
    OracleCert N.nInputs :=
  match hC : synthesizeOracle N with
  | .ok _ => OracleCert.ofNetwork N hN hC
  | .error _ => False.elim <| by
    obtain ⟨C, h⟩ := synthesizeOracle_succeeds hN h1
    rw [h] at hC
    cases hC

/-- Report §6 (`DiffusionCert(n)`), §8.2 (Stage 13c) — the MCZ certificate for every `n ≥ 1`
without an `hC` argument: the MCZ of `P_all` is synthesized (`synthesizeOracle_succeeds` with
`allNet_WF`). -/
def DiffusionCert.ofN (n : ℕ) (hn : n ≠ 0) : DiffusionCert n :=
  match hC : synthesizeOracle (allNet n) with
  | .ok _ => DiffusionCert.mk' n hC
  | .error _ => False.elim <| by
    obtain ⟨C, h⟩ := synthesizeOracle_succeeds (allNet_WF hn) (by simp [allNet])
    rw [h] at hC
    cases hC

/-! ## Stage 12d — the Grover circuit over any certified diffusion -/

/-- Report §3.2.4, §8.2 (Stage 12d decision 2) — the Grover circuit built from an oracle circuit
`oc` and a diffusion circuit `Dc`: `H^{⊗n}` then `r` copies of `oc ; Dc`, by the shifted
`Circuit.append` (the shape of `groverCircuit` and `groverCircuitFew`). -/
def groverCircuitOf (oc Dc : Circuit) (n r : ℕ) : Circuit :=
  (List.replicate r (oc.append Dc)).foldl Circuit.append ⟨n, Diffusion.onAll .h n⟩

/-- Report §8.2, §6.2.4 (Stage 12d decision 2) — one Grover iteration over any diffusion circuit
`Dc` that restores its ancillae with `U_s`: the iteration restores them with `G = U_s U_P`. -/
theorem iteration_ancRestore_diff {n a : ℕ} (O : OracleCert n) (Dc : Circuit)
    (hDb : Dc.bitsOk = true) (hDr : AncRestore n a Dc (diffU n)) (hO : O.C.nAnc ≤ a) :
    AncRestore n a (O.C.append Dc) (groverOp O.P) :=
  AncRestore.comp O.hWF.bitsOk hDb (O.ancRestore hO) hDr

/-- PHASE2_SPEC.md §A.0.1 (Stage 15b) — `iteration_ancRestore_diff` with the oracle abstract: any
circuit `Oc` that respects the bit discipline and restores its ancillae with `phaseOracle P`. -/
theorem iteration_ancRestore_gen {n a : ℕ} (P : Reg n → Bool) (Oc : Circuit)
    (hOb : Oc.bitsOk = true) (hOr : ∀ a, Oc.nAnc ≤ a → AncRestore n a Oc (phaseOracle P))
    (Dc : Circuit) (hDb : Dc.bitsOk = true) (hDr : AncRestore n a Dc (diffU n))
    (hO : Oc.nAnc ≤ a) : AncRestore n a (Oc.append Dc) (groverOp P) :=
  AncRestore.comp hOb hDb (hOr a hO) hDr

/-- PHASE2_SPEC.md §A.0.1 (Stage 15b) — **the restoration conjunct with an abstract oracle**: the
7a / 12a / 12d proof of `grover_ancRestore_diff`, with the oracle's bit discipline and restoration
fact as parameters (`grover_ancRestore_diff` is its instance at an `OracleCert`). -/
theorem grover_ancRestore_gen {n r : ℕ} (P : Reg n → Bool) (Oc : Circuit) (hOb : Oc.bitsOk = true)
    (hOr : ∀ a, Oc.nAnc ≤ a → AncRestore n a Oc (phaseOracle P)) (Dc : Circuit)
    (hDb : Dc.bitsOk = true) (hDr : ∀ a, Dc.nAnc ≤ a → AncRestore n a Dc (diffU n))
    {C : Circuit} (hC : C = groverCircuitOf Oc Dc n r) :
    AncRestore n C.nAnc C (groverOp P ^ r * hadamardU n) := by
  subst hC
  cases r with
  | zero => simpa [groverCircuitOf] using ancRestore_hLayer n _
  | succ k =>
    set it := Oc.append Dc with hit_def
    set Cf := groverCircuitOf Oc Dc n (k + 1) with hCf
    have hle : it.nAnc ≤ Cf.nAnc := by
      have hsplit : Cf = ((List.replicate k it).foldl Circuit.append
          (⟨n, Diffusion.onAll .h n⟩ : Circuit)).append it := by
        rw [hCf, groverCircuitOf, List.replicate_succ', List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      rw [hsplit, nAnc_append _ it]
      exact Nat.le_max_right _ _
    have hO : Oc.nAnc ≤ Cf.nAnc := by
      refine le_trans ?_ hle
      rw [hit_def, nAnc_append]
      exact le_max_left _ _
    have hD : Dc.nAnc ≤ Cf.nAnc := by
      refine le_trans ?_ hle
      rw [hit_def, nAnc_append]
      exact le_max_right _ _
    have hitb : it.bitsOk = true := Circuit.bitsOk_append hOb hDb
    exact (ancRestore_foldl _ _ _ _ (bitsOk_dataLayer _ _ (onAll_h_unitary n)) hitb
      (ancRestore_hLayer n _) (iteration_ancRestore_gen P Oc hOb hOr Dc hDb (hDr _ hD) hO)
      (k + 1)).2

/-- Report §8.2.4, §8.3.3 (Stage 12d decision 2) — **the restoration conjunct over any certified
diffusion**: if `Dc` respects the bit discipline and restores its ancillae with `U_s` on every
register `a ≥ Dc.nAnc`, the Grover circuit `groverCircuitOf O.C Dc n r` on
`Reg n × Reg C.nAnc` restores its ancillae and applies `G^r H^{⊗n}`. The 7a / 12a proof of
`grover_ancRestore_shape`, with the diffusion's restoration fact as a parameter. -/
theorem grover_ancRestore_diff {n r : ℕ} (O : OracleCert n) (Dc : Circuit)
    (hDb : Dc.bitsOk = true) (hDr : ∀ a, Dc.nAnc ≤ a → AncRestore n a Dc (diffU n))
    {C : Circuit} (hC : C = groverCircuitOf O.C Dc n r) :
    AncRestore n C.nAnc C (groverOp O.P ^ r * hadamardU n) :=
  grover_ancRestore_gen O.P O.C O.hWF.bitsOk (fun _ ha => O.ancRestore ha) Dc hDb hDr hC

/-! ## Stage 12a — the diffusion shape: tree (default) and chain -/

/-- The MCZ of either shape is synthesized only for `n ≥ 1`. -/
theorem diffusionNet_ok_ne_zero {s : DiffusionShape} {n : ℕ} {C : Circuit}
    (hC : synthesizeOracle (diffusionNet s n) = .ok C) : n ≠ 0 := by
  rintro rfl
  have h : (synthesizeOracle (diffusionNet s 0)).toBool = false := by cases s <;> decide
  rw [hC] at h
  cases h

/-- Report §6 (`DiffusionCert(n)`), §8.2 (Stage 12a decision 2) — the MCZ certificate of either
shape whose MCZ is synthesized: `hWF` by `synthesizeOracle_WF`, `hPred` by `diffusionNet_pred`. -/
def DiffusionCert.ofShape (s : DiffusionShape) (n : ℕ) {C : Circuit}
    (hC : synthesizeOracle (diffusionNet s n) = .ok C) : DiffusionCert n where
  net := diffusionNet s n
  mcz := { N := diffusionNet s n, C := C, hn := diffusionNet_nInputs s n, hC := hC,
           hWF := synthesizeOracle_WF (diffusionNet_WF s (diffusionNet_ok_ne_zero hC)) hC }
  hN := rfl
  hPred := diffusionNet_pred s (diffusionNet_ok_ne_zero hC)

/-- Report §8.2.4, §8.3.3 (Stage 12a: either diffusion shape) — the Grover circuit
`H^{⊗n} ; (U_P ; D_n)^r` with the V1 diffusion of shape `s` on `Reg n × Reg C.nAnc` restores its
ancillae and applies `G^r H^{⊗n}`, `G = U_s U_P`. The MCZ certificate is built from the circuit
itself (`DiffusionCert.ofShape`); no `DiffusionCert` argument is needed. -/
theorem grover_ancRestore_shape {n r : ℕ} (O : OracleCert n) (s : DiffusionShape) {C : Circuit}
    (hC : groverCircuit O.N n r none s = .ok C) :
    AncRestore n C.nAnc C (groverOp O.P ^ r * hadamardU n) := by
  obtain ⟨it, hit, rfl⟩ := groverCircuit_ok_shape hC
  obtain ⟨oc, d, hoc, hd, rfl⟩ := groverIteration_ok_shape hit
  obtain rfl : oc = O.C := Except.ok.inj (hoc.symm.trans O.hC)
  obtain ⟨hn, mcz, hmcz, rfl⟩ := diffusion_ok_shape hd

  have hmb : mcz.bitsOk = true := (DiffusionCert.ofShape s n hmcz).mcz.hWF.bitsOk
  have hDb : (diffusionCircuit n mcz).bitsOk = true :=
    Circuit.bitsOk_append (Circuit.bitsOk_append (bitsOk_dataLayer _ _ (pre_unitary n)) hmb)
      (bitsOk_dataLayer _ _ (post_unitary n))
  refine grover_ancRestore_diff O _ hDb (fun a ha => ?_) rfl
  have hD : mcz.nAnc ≤ a := by
    refine le_trans ?_ ha
    rw [diffusionCircuit, nAnc_append, nAnc_append]
    exact le_max_of_le_left (le_max_right _ _)
  have hm := (DiffusionCert.ofShape s n hmcz).mcz.ancRestore hD
  rw [(DiffusionCert.ofShape s n hmcz).P_eq hn] at hm
  exact diffusion_ancRestore mcz hmb hm

/-- PHASE2_SPEC.md §A.0.1 (Stage 15b) — the balanced-tree diffusion whose MCZ is synthesized in
mode `coherent` respects the bit discipline and restores its ancillae with `U_s` on every register
`a ≥ nAnc`: the MCZ is a coherent oracle certificate of `treeNet n` (`synthesizeOracle_WF'`,
Lemma 6.3.2 in mode `coherent`), its predicate is `P_all` (`treeNet_pred`), then
`diffusion_ancRestore`. -/
theorem diffusionCoh_ancRestore {n : ℕ} {mcz : Circuit} (hn : n ≠ 0)
    (hmcz : synthesizeOracle (treeNet n) .coherent = .ok mcz) :
    (diffusionCircuit n mcz).bitsOk = true ∧
      ∀ a, (diffusionCircuit n mcz).nAnc ≤ a → AncRestore n a (diffusionCircuit n mcz) (diffU n) := by
  have hWF : mcz.WF := synthesizeOracle_WF' .coherent (treeNet_WF hn) hmcz
  have hmb : mcz.bitsOk = true := hWF.bitsOk
  refine ⟨Circuit.bitsOk_append (Circuit.bitsOk_append (bitsOk_dataLayer _ _ (pre_unitary n)) hmb)
    (bitsOk_dataLayer _ _ (post_unitary n)), fun a ha => ?_⟩
  have hD : mcz.nAnc ≤ a := by
    refine le_trans ?_ ha
    rw [diffusionCircuit, nAnc_append, nAnc_append]
    exact le_max_of_le_left (le_max_right _ _)
  have hm := ({ N := treeNet n, C := mcz, hn := rfl, hC := hmcz, hWF := hWF } :
    OracleCertCoh n).ancRestore hD
  rw [show ({ N := treeNet n, C := mcz, hn := rfl, hC := hmcz, hWF := hWF } :
    OracleCertCoh n).P = allOnes from treeNet_pred hn] at hm
  exact diffusion_ancRestore mcz hmb hm

/-- Report §8.2.4, §8.3.3 — **the restoration conjunct of `grover_parametric_lemma`**: the
Grover circuit `H^{⊗n} ; (U_P ; D_n)^r` (V1 diffusion, synthesized by `groverCircuit`) on
`Reg n × Reg C.nAnc` restores its ancillae and applies `G^r H^{⊗n}` with `G = U_s U_P`.
Statement unchanged; since Stage 12a the default diffusion is the balanced tree and the proof is
`grover_ancRestore_shape` (the MCZ certificate comes from the circuit, `_D` is not used). -/
theorem grover_ancRestore {n r : ℕ} (O : OracleCert n) (_D : DiffusionCert n) {C : Circuit}
    (hC : groverCircuit O.N n r = .ok C) :
    AncRestore n C.nAnc C (groverOp O.P ^ r * hadamardU n) :=
  grover_ancRestore_shape O .tree hC

end CQRV.Grover

end
