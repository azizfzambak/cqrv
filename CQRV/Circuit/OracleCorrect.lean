module

public import CQRV.Circuit.OracleBlocks

/-!
# CQRV.Circuit.OracleCorrect

Report §6.3.2 (Lemma 6.3.2), §6.2.4 (Layers 1–3), §6.1.1/§6.1.4 (Z on the qubit holding P(x)),
§6.2.2 (MBU) — Lemma 6.3.2 for xor-free networks, by induction over the synthesizer
(Stage 6b-3; basis-vector route of DECISIONS.md, Stage 6b-2):

* item 1 — `Aff.eval` (an affine form on a basis state) and `runC` (the basis state after the
  compute blocks: ancilla `j` holds the `j`-th non-folded AND);
* item 2 — the invariant `Inv` of the synthesizer's fold and `step_ok_inv`: every recorded
  value evaluates, on `runC`, to the node value of the network; the compute / uncompute blocks
  are those of a list of AND records (`AndRec`);
* item 3 — `cmp_kraus`: one compute block on a basis vector;
* item 4 — `phaseFlip_kraus`: the phase flip is `(−1)^{P}` (no gate for a constant `P`);
* item 5 — `unc_kraus`: one uncompute block, every branch, `(1/√2)` and the ancilla reset;
  `chain_kraus` nests compute blocks, phase, and uncompute blocks in reverse order;
* item 6 — `lemma_6_3_2` (moved here from `Restoration`, which this file imports), its traced
  form and the Grover instance.

The synthesizer is unchanged: the AND records exist only in the invariant (existentially).
-/

@[expose] public section

namespace CQRV

open CQRV.Synthesis

/-! ## Item 1 — atom semantics -/

/-- Report §6.1.2, §6.3.2 — the value of an affine form on a basis state: the XOR of its atoms
(each read on its home qubit) and its constant. -/
def Synthesis.Aff.eval {n a : ℕ} (u : Aff) (s : Reg n × Reg a) : Bool :=
  u.lin.foldr (fun q b => q.get s ^^ b) u.c

/-- Report §6.1.2, §6.2.2 — a non-folded AND of an xor-free network as the synthesizer emits it:
operand atoms `p`, `q` with the polarities `cu`, `cv` (the `X` gates of `prepare`). The `j`-th
such AND has the target `anc j`. -/
structure AndRec where
  p : Qubit
  cu : Bool
  q : Qubit
  cv : Bool

namespace AndRec

/-- Report §6.1.2 — the polarity gates of `prepare` (no `gather` CNOT: each operand is one
atom). -/
def pre (r : AndRec) : List Gate :=
  (if r.cu then [.x r.p] else []) ++ (if r.cv then [.x r.q] else [])

/-- Report §6.1.4, §6.2.2 — the compute block of the AND with target `anc j`. -/
def cmp (r : AndRec) (j : ℕ) : List Gate :=
  r.pre ++ [.alloc (.anc j)] ++ TempLogicalAND r.p r.q (.anc j) ++ r.pre.reverse

/-- Report §6.1.4, §6.2.2 — the uncompute (MBU) block of the AND with target `anc j`, measuring
into the classical bit `b`. -/
def unc (r : AndRec) (j b : ℕ) : List Gate :=
  r.pre ++ UncomputeTempLogicalAND r.p r.q (.anc j) b ++ [.free (.anc j)] ++ r.pre.reverse

/-- Report §6.1.2 — the value of the AND on a basis state: `(p ⊕ cu) ∧ (q ⊕ cv)`. -/
def val {n a : ℕ} (r : AndRec) (s : Reg n × Reg a) : Bool :=
  (r.p.get s ^^ r.cu) && (r.q.get s ^^ r.cv)

end AndRec

/-- Report §6.1.4 — the compute blocks of the ANDs `rs`, the first one with target `anc j`, in
order. -/
def cmpBlocks : List AndRec → ℕ → List Gate
  | [], _ => []
  | r :: rs, j => r.cmp j ++ cmpBlocks rs (j + 1)

/-- Report §6.1.4, §6.2.2 — the uncompute blocks of the ANDs `rs`, the first one with target
`anc j`, in reverse order; classical bits in measurement order (the last AND measures first). -/
def uncBlocks : List AndRec → ℕ → List Gate
  | [], _ => []
  | r :: rs, j => uncBlocks rs (j + 1) ++ r.unc j rs.length

/-- Report §6.3.2 (item 1) — the basis state after the compute blocks of `rs` (the first with
target `anc j`): ancilla `j + k` holds the value of the `k`-th AND. On `(x, 0…0)` from `j = 0`
this is the atom state of `x`. -/
def runC {n a : ℕ} : List AndRec → ℕ → Reg n × Reg a → Reg n × Reg a
  | [], _, s => s
  | r :: rs, j, s => runC rs (j + 1) ((Qubit.anc j).set (r.val s) s)

/-- Report §6.1.2 — flip `q` when `b` (the action of an optional polarity `X`). -/
def polFlip {n a : ℕ} (b : Bool) (q : Qubit) (s : Reg n × Reg a) : Reg n × Reg a :=
  if b then q.flip s else s

/-- Report §9.1.1 — the qubit discipline that `Circuit.WF` gives on a piece of the gate list:
qubits in the register, CNOT operands distinct. -/
def GatesOk (n a : ℕ) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (∀ q ∈ g.qubits, q.inRange n a = true) ∧ ∀ p t, g = .cnot p t → p ≠ t

theorem GatesOk.of_subset {n a : ℕ} {gs gs' : List Gate} (h : GatesOk n a gs) (hs : gs' ⊆ gs) :
    GatesOk n a gs' := fun g hg => h g (hs hg)

noncomputable section

open Matrix
open scoped MState Kronecker

variable {n a : ℕ}

/-! ## Lens lemmas for the polarity flips -/

theorem Qubit.flip_set_comm {q t : Qubit} (hqt : q ≠ t) (v : Bool) (s : Reg n × Reg a) :
    q.flip (t.set v s) = t.set v (q.flip s) := by
  rw [Qubit.flip, Qubit.flip, Qubit.get_set_ne hqt, Qubit.set_comm hqt]

theorem polFlip_set_comm {q t : Qubit} (hqt : q ≠ t) (b v : Bool) (s : Reg n × Reg a) :
    polFlip b q (t.set v s) = t.set v (polFlip b q s) := by
  cases b
  · rfl
  · exact Qubit.flip_set_comm hqt v s

theorem polFlip_polFlip (b : Bool) (q : Qubit) (s : Reg n × Reg a) :
    polFlip b q (polFlip b q s) = s := by
  cases b
  · rfl
  · exact Qubit.flip_involutive q s

theorem get_polFlip_self {q : Qubit} (hq : q.inRange n a = true) (b : Bool) (s : Reg n × Reg a) :
    q.get (polFlip b q s) = (q.get s ^^ b) := by
  cases b
  · simp [polFlip]
  · simp [polFlip, Qubit.get_flip_self q hq]

theorem get_polFlip_ne {p q : Qubit} (hpq : p ≠ q) (b : Bool) (s : Reg n × Reg a) :
    p.get (polFlip b q s) = p.get s := by
  cases b
  · rfl
  · exact Qubit.get_flip_ne hpq s

/-! ## Polarity gates, `alloc`, `free` on basis vectors -/

section Blocks

variable (nb : ℕ) (c : Fin nb → Bool)

theorem polX_kraus (b : Bool) (q : Qubit) (s : Reg n × Reg a) :
    krausOps n a nb (if b then [Gate.x q] else []) c *ᵥ basisVec s = basisVec (polFlip b q s) := by
  cases b
  · simp [polFlip, krausOps_nil]
  · simp only [↓reduceIte]
    rw [krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec]
    exact x_basis n a q s

theorem pre_kraus (r : AndRec) (s : Reg n × Reg a) :
    krausOps n a nb r.pre c *ᵥ basisVec s = basisVec (polFlip r.cv r.q (polFlip r.cu r.p s)) := by
  rw [AndRec.pre, krausOps_append_mulVec, polX_kraus, polX_kraus]

theorem preRev_kraus (r : AndRec) (s : Reg n × Reg a) :
    krausOps n a nb r.pre.reverse c *ᵥ basisVec s =
      basisVec (polFlip r.cu r.p (polFlip r.cv r.q s)) := by
  have hrev : ∀ (b : Bool) (q : Qubit),
      (if b then [Gate.x q] else []).reverse = (if b then [Gate.x q] else []) := by
    intro b q; cases b <;> rfl
  rw [AndRec.pre, List.reverse_append, hrev, hrev, krausOps_append_mulVec, polX_kraus, polX_kraus]

theorem single_kraus_one (g : Gate) (hg : gateK n a c g = 1) (v : Reg n × Reg a → ℂ) :
    krausOps n a nb [g] c *ᵥ v = v := by
  rw [krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec, hg, Matrix.one_mulVec]

/-! ## Items 3 and 5 — one compute block, one uncompute block -/

/-- The range and distinctness facts of one AND that `Circuit.WF` gives on its compute block. -/
theorem AndRec.ok_of_gatesOk {r : AndRec} {j : ℕ} (h : GatesOk n a (r.cmp j)) :
    r.p.inRange n a = true ∧ r.q.inRange n a = true ∧ (Qubit.anc j).inRange n a = true ∧
      r.p ≠ .anc j ∧ r.q ≠ .anc j := by
  have h1 := h (.cnot r.p (.anc j)) (by simp [AndRec.cmp, TempLogicalAND])
  have h2 := h (.cnot r.q (.anc j)) (by simp [AndRec.cmp, TempLogicalAND])
  exact ⟨h1.1 _ (by simp [Gate.qubits]), h2.1 _ (by simp [Gate.qubits]),
    h1.1 _ (by simp [Gate.qubits]), h1.2 _ _ rfl, h2.2 _ _ rfl⟩

/-- Report §6.2.2, §6.2.4 Layer 1 (item 3) — the compute block of one AND, in any branch: on a
basis state with `anc j = 0`, it sets `anc j` to the AND value and changes nothing else. -/
theorem cmp_kraus {r : AndRec} {j : ℕ} (hpq : r.p ≠ r.q) (hok : GatesOk n a (r.cmp j))
    (s : Reg n × Reg a) (hs : (Qubit.anc j).get s = false) :
    krausOps n a nb (r.cmp j) c *ᵥ basisVec s = basisVec ((Qubit.anc j).set (r.val s) s) := by
  obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hok
  have hqp : r.q ≠ r.p := Ne.symm hpq
  have hs1 : (Qubit.anc j).get (polFlip r.cv r.q (polFlip r.cu r.p s)) = false := by
    rw [get_polFlip_ne (Ne.symm hqt), get_polFlip_ne (Ne.symm hpt), hs]
  rw [AndRec.cmp, krausOps_append_mulVec, krausOps_append_mulVec, krausOps_append_mulVec,
    pre_kraus, single_kraus_one nb c _ rfl,
    tempLogicalAND_kraus_basis nb c r.p r.q _ hpq hpt hqt hp hq ht _ hs1, preRev_kraus,
    get_polFlip_ne hpq, get_polFlip_self hp, get_polFlip_self hq, get_polFlip_ne hqp,
    polFlip_set_comm hqt, polFlip_set_comm hpt, polFlip_polFlip, polFlip_polFlip]
  rfl

/-- Report §6.2.2, §6.2.4 Layer 2 (item 5) — the uncompute block of one AND, in every branch
`c` and for any classical bit `b`: on a basis state whose `anc j` holds the AND value, it resets
`anc j` with amplitude `1/√2` and no sign. -/
theorem unc_kraus {r : AndRec} {j : ℕ} (b : ℕ) (hpq : r.p ≠ r.q) (hok : GatesOk n a (r.cmp j))
    (s : Reg n × Reg a) (hs : (Qubit.anc j).get s = r.val s) :
    krausOps n a nb (r.unc j b) c *ᵥ basisVec s =
      ((Real.sqrt 2)⁻¹ : ℂ) • basisVec ((Qubit.anc j).set false s) := by
  obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hok
  have hqp : r.q ≠ r.p := Ne.symm hpq
  have hs1 : (Qubit.anc j).get (polFlip r.cv r.q (polFlip r.cu r.p s)) =
      (r.p.get (polFlip r.cv r.q (polFlip r.cu r.p s)) &&
        r.q.get (polFlip r.cv r.q (polFlip r.cu r.p s))) := by
    rw [get_polFlip_ne (Ne.symm hqt), get_polFlip_ne (Ne.symm hpt), hs, get_polFlip_ne hpq,
      get_polFlip_self hp, get_polFlip_self hq, get_polFlip_ne hqp]
    rfl
  rw [AndRec.unc, krausOps_append_mulVec, krausOps_append_mulVec, krausOps_append_mulVec,
    pre_kraus, mbu_branch_basis r.p r.q _ b hpt hqt ht c _ hs1, Matrix.mulVec_smul,
    single_kraus_one nb c _ rfl, Matrix.mulVec_smul, preRev_kraus,
    polFlip_set_comm hqt, polFlip_set_comm hpt, polFlip_polFlip, polFlip_polFlip]

/-! ## Item 5 — nesting: compute blocks, phase, uncompute blocks in reverse order -/

theorem runC_fst (rs : List AndRec) (j : ℕ) (s : Reg n × Reg a) : (runC rs j s).1 = s.1 := by
  induction rs generalizing j s with
  | nil => rfl
  | cons r rs ih =>
    rw [runC, ih]
    simp only [Qubit.set]
    split_ifs <;> rfl

/-- Report §6.2.4, §6.3.2 (items 3–5) — the nested brackets of the oracle on a basis vector, in
any branch: if the middle part `Φ` is diagonal on basis vectors (`φ`), the compute blocks of
`rs`, `Φ`, and the uncompute blocks in reverse order map `|s⟩` (ancillae `≥ j` at 0) to
`(1/√2)^{|rs|} · φ(runC rs j s) · |s⟩`. Induction on `rs`: the outermost compute block sets
`anc j`, the inner part acts as a scalar, the outermost uncompute block resets `anc j`. -/
theorem chain_kraus (Φ : List Gate) (φ : Reg n × Reg a → ℂ)
    (hΦ : ∀ s, krausOps n a nb Φ c *ᵥ basisVec s = φ s • basisVec s) :
    ∀ (rs : List AndRec) (j : ℕ) (s : Reg n × Reg a), GatesOk n a (cmpBlocks rs j) →
      (∀ r ∈ rs, r.p ≠ r.q) → (∀ i, j ≤ i → (Qubit.anc i).get s = false) →
      krausOps n a nb (cmpBlocks rs j ++ Φ ++ uncBlocks rs j) c *ᵥ basisVec s =
        (((Real.sqrt 2)⁻¹ : ℂ) ^ rs.length * φ (runC rs j s)) • basisVec s
  | [], j, s, _, _, _ => by
    simp only [cmpBlocks, uncBlocks, List.nil_append, List.append_nil, hΦ, runC, List.length_nil,
      pow_zero, one_mul]
  | r :: rs, j, s, hok, hpq, hs => by
    have hokr : GatesOk n a (r.cmp j) := hok.of_subset (by simp [cmpBlocks])
    have hokrs : GatesOk n a (cmpBlocks rs (j + 1)) := hok.of_subset (by simp [cmpBlocks])
    obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hokr
    have hpq₀ : r.p ≠ r.q := hpq r (by simp)
    set s' := (Qubit.anc j).set (r.val s) s with hs'
    have hs'' : ∀ i, j + 1 ≤ i → (Qubit.anc i).get s' = false := by
      intro i hi
      rw [hs', Qubit.get_set_ne (by simp; omega)]
      exact hs i (by omega)
    have ih := chain_kraus Φ φ hΦ rs (j + 1) s' hokrs (fun r' hr' => hpq r' (by simp [hr'])) hs''
    have hsplit : cmpBlocks (r :: rs) j ++ Φ ++ uncBlocks (r :: rs) j =
        r.cmp j ++ (cmpBlocks rs (j + 1) ++ Φ ++ uncBlocks rs (j + 1)) ++ r.unc j rs.length := by
      simp only [cmpBlocks, uncBlocks, List.append_assoc]
    have hval : (Qubit.anc j).get s' = r.val s' := by
      rw [hs', Qubit.get_set_self _ ht, AndRec.val, AndRec.val, Qubit.get_set_ne hpt,
        Qubit.get_set_ne hqt]
    have hback : (Qubit.anc j).set false s' = s := by
      rw [hs', Qubit.set_set, ← hs j le_rfl, Qubit.set_get]
    rw [hsplit, krausOps_append_mulVec, krausOps_append_mulVec, cmp_kraus nb c hpq₀ hokr s
      (hs j le_rfl), ← hs', ih, Matrix.mulVec_smul, unc_kraus nb c _ hpq₀ hokr s' hval, hback,
      smul_smul, runC, List.length_cons, pow_succ]
    congr 1
    ring

end Blocks

/-! ## Item 2 — the invariant of the synthesizer's fold -/

/-- Report §6.1.2 — the value of one node from the values `vs` of the earlier nodes (the body of
`Network.values`). -/
def nodeVal (x : ℕ → Bool) (vs : Array Bool) : Node → Bool
  | .input k => x k
  | .const b => b
  | .not i => !vs.getD i false
  | .and i j => vs.getD i false && vs.getD j false
  | .xor i j => vs.getD i false ^^ vs.getD j false

/-- Report §6.1.2 — one step of `Network.values`. -/
def nodeStep (x : ℕ → Bool) (vs : Array Bool) (v : Node) : Array Bool :=
  vs.push (nodeVal x vs v)

/-- Report §6.1.2 — the values of the first `k` nodes. -/
def valuesUpTo (N : Network) (x : ℕ → Bool) (k : ℕ) : Array Bool :=
  (N.nodes.toList.take k).foldl (nodeStep x) #[]

/-- Report §6.3.2 — input bit `k` of the predicate on `x : Reg n` (`false` beyond `n`), as in
`Network.pred`. -/
def inputOf {n : ℕ} (x : Reg n) (k : ℕ) : Bool := if h : k < n then x ⟨k, h⟩ else false

theorem values_eq_valuesUpTo (N : Network) (x : ℕ → Bool) :
    N.values x = valuesUpTo N x N.nodes.size := by
  rw [valuesUpTo, List.take_of_length_le (by simp), Array.foldl_toList]
  unfold Network.values nodeStep nodeVal
  rfl

theorem Array.getD_push_eq {α : Type} (xs : Array α) (v d : α) (i : ℕ) :
    (xs.push v).getD i d = if i = xs.size then v else xs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> rfl

theorem valuesUpTo_succ (N : Network) (x : ℕ → Bool) {k : ℕ} (hk : k < N.nodes.size) :
    valuesUpTo N x (k + 1) = nodeStep x (valuesUpTo N x k) N.nodes[k] := by
  rw [valuesUpTo, List.take_add_one, List.foldl_append, ← valuesUpTo]
  simp [hk]

theorem valuesUpTo_size (N : Network) (x : ℕ → Bool) {k : ℕ} (hk : k ≤ N.nodes.size) :
    (valuesUpTo N x k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [valuesUpTo_succ N x (by omega)]
    unfold nodeStep
    rw [Array.size_push, ih (by omega)]

/-! ### `Aff.eval` -/

theorem Synthesis.Aff.eval_split {n a : ℕ} (u : Aff) (s : Reg n × Reg a) :
    u.eval s = ((Aff.mk u.lin false).eval s ^^ u.c) := by
  obtain ⟨lin, c⟩ := u
  simp only [Aff.eval]
  induction lin with
  | nil => simp
  | cons q l ih => simp only [List.foldr_cons, ih, Bool.xor_assoc]

theorem Synthesis.Aff.eval_not {n a : ℕ} (u : Aff) (s : Reg n × Reg a) :
    ({ u with c := !u.c } : Aff).eval s = !u.eval s := by
  rw [Aff.eval_split, Aff.eval_split u, Bool.xor_not]

theorem Synthesis.Aff.eval_nil {n a : ℕ} (u : Aff) (h : u.lin = []) (s : Reg n × Reg a) :
    u.eval s = u.c := by
  simp [Aff.eval, h]

theorem Synthesis.Aff.eval_single {n a : ℕ} (p : Qubit) (c : Bool) (s : Reg n × Reg a) :
    (Aff.mk [p] c).eval s = (p.get s ^^ c) := rfl

/-- The atoms of `u` are data qubits or ancillae `anc j` with `j < K`. -/
def AtomsBelow (K : ℕ) (u : Aff) : Prop := ∀ q ∈ u.lin, ∀ j, q = .anc j → j < K

theorem Synthesis.Aff.eval_set_anc {n a K : ℕ} {u : Aff} (hu : AtomsBelow K u) (v : Bool)
    (s : Reg n × Reg a) : u.eval ((Qubit.anc K).set v s) = u.eval s := by
  obtain ⟨lin, c⟩ := u
  simp only [Aff.eval]
  induction lin with
  | nil => rfl
  | cons q l ih =>
    have hq : q ≠ .anc K := fun e => by
      have := hu q (by simp) K e; omega
    simp only [List.foldr_cons, Qubit.get_set_ne hq]
    rw [ih (fun q' hq' => hu q' (by simp [hq']))]

/-- Report §6.1.2 (item 2) — the folding identities are exact on every state:
`fold u v = some r → r = u ∧ v` (`1 ∧ v = v`, `0 ∧ v = 0`, `u ∧ u = u`, `u ∧ ¬u = 0`). -/
theorem fold_eval {n a : ℕ} {u v r : Aff} (h : Oracle.fold u v = some r) (s : Reg n × Reg a) :
    r.eval s = (u.eval s && v.eval s) := by
  unfold Oracle.fold at h
  split at h
  · rename_i h1
    rw [u.eval_nil (List.isEmpty_iff.mp h1) s]
    split at h <;> rename_i hc <;> cases Option.some.inj h
    · simp [hc]
    · simp [hc, Aff.eval]
  split at h
  · rename_i h2
    rw [v.eval_nil (List.isEmpty_iff.mp h2) s]
    split at h <;> rename_i hc <;> cases Option.some.inj h
    · simp [hc]
    · simp [hc, Aff.eval]
  split at h
  · rename_i h3
    have eu := u.eval_split s
    have ev := v.eval_split s
    rw [← beq_iff_eq.mp h3] at ev
    split at h <;> rename_i hc <;> cases Option.some.inj h
    · rw [eu, ev, beq_iff_eq.mp hc, Bool.and_self]
    · have hne : u.c ≠ v.c := fun e => hc (beq_iff_eq.mpr e)
      rw [eu, ev]
      generalize (Aff.mk u.lin false).eval s = L
      cases L <;> cases hu : u.c <;> cases hv : v.c <;> simp_all [Aff.eval]
  · cases h

/-- `fold` returns one of its operands or the constant 0. -/
theorem fold_cases {u v r : Aff} (h : Oracle.fold u v = some r) :
    r = u ∨ r = v ∨ r = ⟨[], false⟩ := by
  unfold Oracle.fold at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

/-- Report §6.1.2 — `prepare` on two single-atom operands with distinct atoms: no `gather`
CNOT, only the polarity `X` gates; the operand qubits are the atoms. -/
theorem prepare_single (p q : Qubit) (cu cv : Bool) (hpq : p ≠ q) :
    Oracle.prepare ⟨[p], cu⟩ ⟨[q], cv⟩ = .ok ((⟨p, cu, q, cv⟩ : AndRec).pre, p, q) := by
  have h1 : [q].contains p = false := by simp [hpq]
  have h2 : [q].filter (· != p) = [q] := by simp [Ne.symm hpq]
  have h3 : ∀ r : Qubit, [r].filter (· != r) = [] := by simp
  simp only [Oracle.prepare, pure_bind, h1, Bool.false_eq_true, ↓reduceIte, h2, Oracle.gather, h3,
    List.map_nil, List.nil_append]
  rfl

/-- Report §6.3.2 (item 2) — what the invariant asks of the recorded value `u` of node `i`
after the nodes `< k`, the non-folded ANDs so far being `recs`: at most one atom, atoms below
`anc recs.length`, and on the atom state `runC recs 0 (x, 0…0)` the value of node `i` on `x`. -/
def Good (N : Network) (n k : ℕ) (recs : List AndRec) (i : ℕ) (u : Aff) : Prop :=
  u.lin.length ≤ 1 ∧ AtomsBelow recs.length u ∧
    ∀ a, recs.length ≤ a → ∀ x : Reg n,
      u.eval (runC (a := a) recs 0 (x, fun _ => false)) =
        (valuesUpTo N (inputOf x) k).getD i false

/-- Report §6.3.2 (item 2) — the invariant of the synthesizer's fold after the nodes `< k` of
an xor-free network: the non-folded ANDs so far are the records `recs` (the `j`-th has target
`anc j`; its operands are distinct atoms below `anc j`), the compute / uncompute blocks are
theirs, and every recorded value is `Good`. -/
def Inv (N : Network) (n k : ℕ) (st : Oracle.St) : Prop :=
  ∃ recs : List AndRec,
    st.vals.size = k ∧ st.nextAnc = recs.length ∧
    st.compute.toList = recs.mapIdx (fun j r => r.cmp j) ∧
    st.uncompute.toList = recs.mapIdx (fun j r => r.unc j 0) ∧
    (∀ r ∈ recs, r.p ≠ r.q) ∧
    (∀ j (h : j < recs.length) i, (recs[j].p = .anc i ∨ recs[j].q = .anc i) → i < j) ∧
    ∀ i u, st.vals.getD i none = some u → Good N n k recs i u

theorem runC_append (rs : List AndRec) (r : AndRec) (j : ℕ) (s : Reg n × Reg a) :
    runC (rs ++ [r]) j s =
      (Qubit.anc (j + rs.length)).set (r.val (runC rs j s)) (runC rs j s) := by
  induction rs generalizing j s with
  | nil => simp [runC]
  | cons r' rs ih =>
    rw [List.cons_append, runC, runC, ih, List.length_cons]
    congr 2
    omega

theorem good_lift_k {N : Network} {n k : ℕ} {recs : List AndRec} {i : ℕ} {u : Aff}
    (hk : k < N.nodes.size) (hi : i < k) (h : Good N n k recs i u) :
    Good N n (k + 1) recs i u := by
  refine ⟨h.1, h.2.1, fun a ha x => ?_⟩
  rw [h.2.2 a ha x, valuesUpTo_succ N _ hk, nodeStep, Array.getD_push_eq,
    valuesUpTo_size N _ hk.le]
  simp only [show i ≠ k by omega, ↓reduceIte]

theorem good_lift_recs {N : Network} {n k : ℕ} {recs : List AndRec} (r : AndRec) {i : ℕ}
    {u : Aff} (h : Good N n k recs i u) : Good N n k (recs ++ [r]) i u := by
  refine ⟨h.1, fun q hq j hj => by have := h.2.1 q hq j hj; simp; omega, fun a ha x => ?_⟩
  rw [runC_append, Nat.zero_add, Aff.eval_set_anc h.2.1]
  exact h.2.2 a (by simp at ha; omega) x

/-- The vals clause of `Inv` after pushing the value `e` of node `k`. -/
theorem vals_push {N : Network} {n k : ℕ} {recs : List AndRec} {vals : Array (Option Aff)}
    (hk : k < N.nodes.size) (hsize : vals.size = k)
    (hvals : ∀ i u, vals.getD i none = some u → Good N n k recs i u) (e : Option Aff)
    (he : ∀ u, e = some u → Good N n (k + 1) recs k u) :
    ∀ i u, (vals.push e).getD i none = some u → Good N n (k + 1) recs i u := by
  intro i u hu
  rw [Array.getD_push_eq, hsize] at hu
  split_ifs at hu with hik
  · subst hik; exact he u hu
  · have hi : i < k := by
      by_contra hc
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hu
      cases hu
    exact good_lift_k hk hi (hvals i u hu)

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem except_pure_eq_ok {ε α : Type} {x y : α} : (pure x : Except ε α) = .ok y ↔ x = y := by
  simp [pure, Except.pure]

theorem fail_ne_ok {α : Type} (msg : String) (y : α) : Oracle.fail msg ≠ .ok y := by
  intro h; cases h

/-- Report §6.1.2, §6.3.2 (item 2) — one step of the synthesizer preserves the invariant
(xor-free network, node `k` in range, the step succeeded). -/
theorem step_ok_inv {N : Network} (hN : N.xorFree = true) (mark : Array Bool) {n k : ℕ}
    (hk : k < N.nodes.size) {st st' : Oracle.St} (h : Oracle.step N mark st k = .ok st')
    (hinv : Inv N n k st) : Inv N n (k + 1) st' := by
  obtain ⟨recs, hsize, hnext, hcmp, hunc, hpq, hbelow, hvals⟩ := hinv
  have hval : ∀ x : Reg n, (valuesUpTo N (inputOf x) (k + 1)).getD k false =
      nodeVal (inputOf x) (valuesUpTo N (inputOf x) k) N.nodes[k] := fun x => by
    rw [valuesUpTo_succ N _ hk, nodeStep, Array.getD_push_eq, valuesUpTo_size N _ hk.le]
    simp
  -- a value pushed with unchanged records
  have keep : ∀ e : Option Aff, (∀ u, e = some u → Good N n (k + 1) recs k u) →
      Inv N n (k + 1) { st with vals := st.vals.push e } := fun e he =>
    ⟨recs, by simp [hsize], hnext, hcmp, hunc, hpq, hbelow, vals_push hk hsize hvals e he⟩
  have hmem := List.all_eq_true.mp hN N.nodes[k] (Array.getElem_mem_toList hk)
  unfold Oracle.step at h
  split at h
  · rw [except_pure_eq_ok] at h
    subst h
    exact keep none (fun u hu => by cases hu)
  rw [Array.getElem?_eq_getElem hk] at h
  generalize hnd : N.nodes[k] = nd at h hval hmem
  cases nd with
  | input i =>
    rw [except_pure_eq_ok] at h
    subst h
    refine keep _ (fun u hu => ?_)
    cases hu
    refine ⟨by simp, fun q hq j hj => ?_, fun a _ x => ?_⟩
    · simp only [List.mem_singleton] at hq
      subst hq
      cases hj
    · rw [hval x, nodeVal, Aff.eval_single, Bool.xor_false]
      simp only [Qubit.get, runC_fst, inputOf]
  | const b =>
    rw [except_pure_eq_ok] at h
    subst h
    refine keep _ (fun u hu => ?_)
    cases hu
    refine ⟨by simp, fun q hq => by simp at hq, fun a _ x => ?_⟩
    rw [hval x, nodeVal]
    rfl
  | not i =>
    rw [except_bind_eq_ok] at h
    obtain ⟨u, hu, h⟩ := h
    beta_reduce at hu
    split at hu
    · rename_i u' hu'
      rw [except_pure_eq_ok] at hu h
      subst hu h
      refine keep _ (fun w hw => ?_)
      cases hw
      obtain ⟨h1, h2, h3⟩ := hvals i u' hu'
      refine ⟨h1, h2, fun a ha x => ?_⟩
      rw [Aff.eval_not, h3 a ha x, hval x, nodeVal]
    · exact absurd hu (fail_ne_ok _ _)
  | xor i j => exact absurd hmem (by simp)
  | and i j =>
    rw [except_bind_eq_ok] at h
    obtain ⟨u, hu, h⟩ := h
    rw [except_bind_eq_ok] at h
    obtain ⟨v, hv, h⟩ := h
    beta_reduce at hu hv
    split at hu
    swap; · exact absurd hu (fail_ne_ok _ _)
    rename_i u' hu'
    rw [except_pure_eq_ok] at hu
    subst hu
    split at hv
    swap; · exact absurd hv (fail_ne_ok _ _)
    rename_i v' hv'
    rw [except_pure_eq_ok] at hv
    subst hv
    have gu := hvals i u' hu'
    have gv := hvals j v' hv'
    split at h
    · -- folded AND
      rename_i r hr
      rw [except_pure_eq_ok] at h
      subst h
      refine keep _ (fun w hw => ?_)
      cases hw
      refine ⟨?_, ?_, fun a ha x => ?_⟩
      · rcases fold_cases hr with rfl | rfl | rfl
        exacts [gu.1, gv.1, by simp]
      · rcases fold_cases hr with rfl | rfl | rfl
        exacts [gu.2.1, gv.2.1, fun q hq => by simp at hq]
      · rw [fold_eval hr, gu.2.2 a ha x, gv.2.2 a ha x, hval x, nodeVal]
    · -- a new ancilla
      rename_i hnone
      rw [except_bind_eq_ok] at h
      obtain ⟨⟨pre, pu, pv⟩, hprep, h⟩ := h
      rw [except_pure_eq_ok] at h
      subst h
      -- the operands are single atoms (`fold` did not apply), distinct
      obtain ⟨p, hp⟩ : ∃ p, u'.lin = [p] := by
        rcases hl : u'.lin with _ | ⟨p, _ | ⟨p', l⟩⟩
        · exact absurd (by simp [Oracle.fold, hl]) (hnone (if u'.c then v' else ⟨[], false⟩))
        · exact ⟨p, rfl⟩
        · have := gu.1; rw [hl] at this; simp at this
      obtain ⟨q, hq⟩ : ∃ q, v'.lin = [q] := by
        rcases hl : v'.lin with _ | ⟨q, _ | ⟨q', l⟩⟩
        · exact absurd (by simp [Oracle.fold, hp, hl]) (hnone (if v'.c then u' else ⟨[], false⟩))
        · exact ⟨q, rfl⟩
        · have := gv.1; rw [hl] at this; simp at this
      have hpq' : p ≠ q := by
        rintro rfl
        exact hnone (if u'.c == v'.c then u' else ⟨[], false⟩) (by simp [Oracle.fold, hp, hq])
      have hu'' : u' = ⟨[p], u'.c⟩ := by obtain ⟨l, c⟩ := u'; simp only at hp; subst hp; rfl
      have hv'' : v' = ⟨[q], v'.c⟩ := by obtain ⟨l, c⟩ := v'; simp only at hq; subst hq; rfl
      have eu : ∀ {a : ℕ} (S : Reg n × Reg a), u'.eval S = (p.get S ^^ u'.c) := fun S => by
        simp [Aff.eval, hp]
      have ev : ∀ {a : ℕ} (S : Reg n × Reg a), v'.eval S = (q.get S ^^ v'.c) := fun S => by
        simp [Aff.eval, hq]
      rw [hu'', hv'', prepare_single p q _ _ hpq'] at hprep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
      obtain ⟨rfl, rfl, rfl⟩ := hprep
      refine ⟨recs ++ [⟨p, u'.c, q, v'.c⟩], by simp [hsize], by simp [hnext], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Array.toList_push, hcmp, List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
          hnext, Nat.zero_add]
        rfl
      · simp only [Array.toList_push, hunc, List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
          hnext, Nat.zero_add]
        rfl
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        exacts [hpq r hr, hpq']
      · intro j hj i hi
        by_cases hjl : j < recs.length
        · rw [List.getElem_append_left hjl] at hi
          exact hbelow j hjl i hi
        · have hjeq : j = recs.length := by simp at hj; omega
          rw [List.getElem_concat_length hjeq] at hi
          rw [hjeq]
          rcases hi with hi | hi
          · exact gu.2.1 p (by simp [hp]) i hi
          · exact gv.2.1 q (by simp [hq]) i hi
      · refine vals_push hk hsize (fun i w hw => good_lift_recs _ (hvals i w hw)) _ (fun w hw => ?_)
        cases hw
        refine ⟨by simp, fun q' hq' j' hj' => ?_, fun a ha x => ?_⟩
        · simp only [List.mem_singleton] at hq'
          subst hq'
          cases hj'
          simp [hnext]
        · have ha' : recs.length < a := by simp at ha; omega
          rw [Aff.eval_single, Bool.xor_false, hnext, runC_append, Nat.zero_add,
            Qubit.get_set_self _ (by simp [Qubit.inRange, ha']), hval x, nodeVal, AndRec.val,
            ← gu.2.2 a ha'.le x, ← gv.2.2 a ha'.le x, eu, ev]

/-- Report §6.3.2 (item 2) — the invariant holds after the synthesizer's fold over the first `m`
nodes (`List.foldlM` induction; every `step` returned `.ok`). -/
theorem fold_inv {N : Network} (hN : N.xorFree = true) (mark : Array Bool) (n : ℕ) :
    ∀ m, m ≤ N.nodes.size → ∀ st,
      (List.range m).foldlM (Oracle.step N mark) ({ vals := #[] } : Oracle.St) = .ok st →
        Inv N n m st
  | 0, _, st, h => by
    rw [List.range_zero, List.foldlM_nil, except_pure_eq_ok] at h
    subst h
    exact ⟨[], rfl, rfl, rfl, rfl, by simp, by simp, fun i u hu => by simp at hu⟩
  | m + 1, hm, st, h => by
    rw [List.range_succ, List.foldlM_append, except_bind_eq_ok] at h
    obtain ⟨st₁, h₁, h⟩ := h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    exact step_ok_inv hN mark (by omega) h (fold_inv hN mark n m (by omega) st₁ h₁)

/-! ## Item 6 — ranges, bits, and the gate list of the synthesized oracle -/

theorem foldl_mono_le {α : Type} (F : ℕ → α → ℕ) (hF : ∀ m x, m ≤ F m x) :
    ∀ (l : List α) (m : ℕ), m ≤ l.foldl F m
  | [], _ => le_rfl
  | x :: l, m => le_trans (hF m x) (foldl_mono_le F hF l (F m x))

theorem lt_foldl_of_mem {α : Type} (F : ℕ → α → ℕ) (hF : ∀ m x, m ≤ F m x) {i : ℕ} {x : α}
    (hx : ∀ m, i < F m x) : ∀ (l : List α) (m : ℕ), x ∈ l → i < l.foldl F m
  | [], _, h => by simp at h
  | y :: l, m, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact lt_of_lt_of_le (hx m) (foldl_mono_le F hF l _)
    · exact lt_foldl_of_mem F hF hx l (F m y) h

/-- Report §9.1.1 — every ancilla index of a circuit is below `nAnc` (by definition of `nAnc`). -/
theorem Circuit.anc_lt_nAnc {C : Circuit} {g : Gate} (hg : g ∈ C.gates) {i : ℕ}
    (hi : Qubit.anc i ∈ g.qubits) : i < C.nAnc := by
  unfold Circuit.nAnc
  have hF : ∀ (m : ℕ) (q : Qubit), m ≤ (match q with | .anc i => Nat.max m (i + 1) | .data _ => m) := by
    intro m q; cases q <;> simp
  refine lt_foldl_of_mem _ (fun m g' => foldl_mono_le _ hF g'.qubits m) (fun m => ?_) _ _ hg
  exact lt_foldl_of_mem _ hF (fun m => by simp) _ _ hi

/-- Report §9.1.1 — `Circuit.WF` gives the qubit discipline on the whole gate list, with the
ancilla register `Reg C.nAnc`. -/
theorem Circuit.WF.gatesOk {C : Circuit} (h : C.WF) : GatesOk C.nData C.nAnc C.gates := by
  intro g hg
  unfold Circuit.WF Circuit.wf at h
  rw [Bool.and_eq_true] at h
  have hq := List.all_eq_true.mp h.1 g hg
  unfold Gate.qubitsOk at hq
  rw [Bool.and_eq_true] at hq
  refine ⟨fun q hqm => ?_, ?_⟩
  · cases q with
    | data i => simpa [Qubit.inRange] using List.all_eq_true.mp hq.1 _ hqm
    | anc i => simp [Qubit.inRange, Circuit.anc_lt_nAnc hg hqm]
  · rintro p t rfl
    simpa using hq.2

theorem cmpBlocks_length_le {rs : List AndRec} {j : ℕ} (h : GatesOk n a (cmpBlocks rs j)) :
    rs = [] ∨ j + rs.length ≤ a := by
  induction rs generalizing j with
  | nil => exact Or.inl rfl
  | cons r rs ih =>
    right
    have ht := (AndRec.ok_of_gatesOk (r := r) (j := j) (h.of_subset (by simp [cmpBlocks]))).2.2.1
    simp only [Qubit.inRange, decide_eq_true_eq] at ht
    rcases ih (j := j + 1) (h.of_subset (by simp [cmpBlocks])) with rfl | hle
    · simp; omega
    · simp; omega

theorem written_cmp (r : AndRec) (j : ℕ) : Circuit.written (r.cmp j) = [] := by
  obtain ⟨p, cu, q, cv⟩ := r
  cases cu <;> cases cv <;>
    simp [Circuit.written, AndRec.cmp, AndRec.pre, TempLogicalAND, Gate.writes]

theorem written_unc (r : AndRec) (j b : ℕ) : Circuit.written (r.unc j b) = [b] := by
  obtain ⟨p, cu, q, cv⟩ := r
  cases cu <;> cases cv <;>
    simp [Circuit.written, AndRec.unc, AndRec.pre, UncomputeTempLogicalAND, Gate.writes]

theorem written_cmpBlocks (rs : List AndRec) (j : ℕ) : Circuit.written (cmpBlocks rs j) = [] := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [cmpBlocks, Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
      written_cmp, ih]
    rfl

theorem written_uncBlocks_length (rs : List AndRec) (j : ℕ) :
    (Circuit.written (uncBlocks rs j)).length = rs.length := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [uncBlocks, Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
      written_unc, List.length_append, ih]
    rfl

theorem written_phaseFlip (pp : Aff) : Circuit.written (Oracle.phaseFlip pp) = [] := by
  unfold Oracle.phaseFlip
  split
  · rfl
  · cases pp.c <;> simp [Circuit.written, Oracle.gather, Gate.writes] <;>
      (intro g _ _ _ hg; subst hg; rfl)

theorem unc_map_shift (r : AndRec) (j b k : ℕ) :
    (r.unc j b).map (Gate.shiftBits k) = r.unc j (b + k) := by
  obtain ⟨p, cu, q, cv⟩ := r
  cases cu <;> cases cv <;>
    simp [AndRec.unc, AndRec.pre, UncomputeTempLogicalAND, Gate.shiftBits]

/-- The synthesizer's compute list (`st.compute.toList.flatten`) is `cmpBlocks`. -/
theorem flatten_mapIdx_cmp (rs : List AndRec) (j : ℕ) :
    (rs.mapIdx (fun i r => r.cmp (j + i))).flatten = cmpBlocks rs j := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [List.mapIdx_cons, List.flatten_cons, cmpBlocks, Nat.add_zero, ← ih (j + 1)]
    congr 3
    funext i r'
    congr 1
    omega

/-- The synthesizer's uncompute list (reversed, each block shifted to its measurement-order
bit) is `uncBlocks`. -/
theorem flatten_mapIdx_unc (rs : List AndRec) (j : ℕ) :
    ((rs.mapIdx (fun i r => r.unc (j + i) 0)).reverse.mapIdx
      (fun i blk => blk.map (Gate.shiftBits i))).flatten = uncBlocks rs j := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    have hf : (fun i r => AndRec.unc r (j + (i + 1)) 0) = (fun i r => r.unc (j + 1 + i) 0) := by
      funext i r'; congr 1; omega
    rw [List.mapIdx_cons, hf, List.reverse_cons, List.mapIdx_append, List.flatten_append, ih,
      uncBlocks, Nat.add_zero]
    simp [unc_map_shift]

/-- Report §6.1.4 — what `synthesizeOracle N = .ok C` means: one output `out`, the fold over
the nodes succeeded with final state `st`, `out` has the value `pp`, and `C` is the compute
blocks, the phase flip of `pp`, and the shifted uncompute blocks in reverse order. -/
theorem synthesizeOracle_ok {N : Network} {C : Circuit} (hC : synthesizeOracle N = .ok C) :
    ∃ out st pp, N.outputs = [out] ∧
      (List.range N.nodes.size).foldlM (Oracle.step N (Oracle.cone N out))
        ({ vals := #[] } : Oracle.St) = .ok st ∧
      st.vals.getD out none = some pp ∧
      C = { nData := N.nInputs,
            gates := st.compute.toList.flatten ++ Oracle.phaseFlip pp ++
              (st.uncompute.toList.reverse.mapIdx
                fun i blk => blk.map (Gate.shiftBits i)).flatten } := by
  unfold synthesizeOracle at hC
  split at hC
  · rename_i o hout
    simp only [pure_bind] at hC
    rw [except_bind_eq_ok] at hC
    obtain ⟨st, hst, hC⟩ := hC
    split at hC
    · rename_i pp hpp
      simp only [except_pure_eq_ok] at hC
      exact ⟨o, st, pp, hout, hst, hpp, hC.symm⟩
    · rw [except_bind_eq_ok] at hC
      obtain ⟨_, hf, _⟩ := hC
      exact absurd hf (fail_ne_ok _ _)
  · rw [except_bind_eq_ok] at hC
    obtain ⟨_, hf, _⟩ := hC
    exact absurd hf (fail_ne_ok _ _)

/-! ## Item 4 — the phase flip -/

/-- Report §6.1.1, §6.1.4 — the scalar of the phase flip on a basis state: `(−1)^{P}` when `P`
has an atom; `1` for a constant `P` (no gate is emitted). -/
def phaseVal {n a : ℕ} (pp : Aff) (s : Reg n × Reg a) : ℂ :=
  if pp.lin = [] then 1 else if pp.eval s then -1 else 1

section Phase

variable (nb : ℕ) (c : Fin nb → Bool)

/-- Report §6.1.1, §6.1.4 Step 3 (item 4) — on a single-atom (or constant) `P`, the phase flip
`[X q]? ++ [Z q] ++ [X q]?` maps `|s⟩` to `phaseVal P s · |s⟩` in every branch. -/
theorem phaseFlip_kraus (pp : Aff) (hlen : pp.lin.length ≤ 1)
    (hok : GatesOk n a (Oracle.phaseFlip pp)) (s : Reg n × Reg a) :
    krausOps n a nb (Oracle.phaseFlip pp) c *ᵥ basisVec s = phaseVal pp s • basisVec s := by
  rcases hl : pp.lin with _ | ⟨q, _ | ⟨q', l⟩⟩
  · have hpf : Oracle.phaseFlip pp = [] := by unfold Oracle.phaseFlip; rw [hl]
    rw [hpf, krausOps_nil, Matrix.one_mulVec]
    simp [phaseVal, hl]
  · have hpf : Oracle.phaseFlip pp = (if pp.c then [Gate.x q] else []) ++ [Gate.z q] ++
        (if pp.c then [Gate.x q] else []) := by
      unfold Oracle.phaseFlip
      rw [hl]
      cases pp.c <;> simp [Oracle.gather]
    have hq : q.inRange n a = true :=
      (hok (.z q) (by rw [hpf]; simp)).1 q (by simp [Gate.qubits])
    rw [hpf, krausOps_append_mulVec, krausOps_append_mulVec, polX_kraus, krausOps_cons_mulVec,
      krausOps_nil, Matrix.one_mulVec]
    change krausOps n a nb _ c *ᵥ (gateU n a (.z q) *ᵥ _) = _
    rw [z_basis, Matrix.mulVec_smul, polX_kraus, polFlip_polFlip, get_polFlip_self hq,
      phaseVal, Aff.eval_split, hl]
    simp [Aff.eval]
  · rw [hl] at hlen
    simp at hlen

end Phase

/-! ## Item 6 — assembly: Lemma 6.3.2 -/

/-- Report §6.2.4 Layer 3 (item 6) — a Kraus operator that maps every `|x, 0…0⟩` to
`l · (−1)^{P(x)} · |x, 0…0⟩` satisfies the hypothesis of `ancRestore_of_kraus`: checked column
by column; a column `(x, y)` with `y ≠ 0…0` is killed by the projector (as in `mbu_kraus`). -/
theorem kraus_mul_ancProj (M : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ) (P : Reg n → Bool)
    (l : ℂ) (hM : ∀ x, M *ᵥ basisVec (x, fun _ => false) =
      (l * (if P x then -1 else 1)) • basisVec (x, fun _ => false)) :
    M * ancProj n a = l • ((phaseOracle P).val ⊗ₖ (ancZero a).m) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  rw [← mulVec_basisVec (M * ancProj n a), ← Matrix.mulVec_mulVec, ancProj_mulVec_basisVec]
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, ancZero_m_apply, phaseOracle,
    phaseDiag, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hj : j2 = fun _ => false
  · subst hj
    simp only [↓reduceIte, hM, Pi.smul_apply, smul_eq_mul, basisVec, Prod.mk.injEq]
    by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = fun _ => false <;> simp [h1, h2]
  · simp [hj]

/-- Report §6.3.2, Lemma 6.3.2 — parametric over the Stage 5 synthesizer: for an AND/NOT/OR
network `N` whose oracle `C` is synthesized and well formed, `C` restores its ancillae and
applies the phase oracle of `N`'s predicate. The statement is on density operators, not on
basis states (§6.2.4: on basis states the phase cancels); Theorem 3.3a is not used inside the
oracle (§6.3.2). Proof (Stage 6b-3, basis-vector route): the synthesizer's fold keeps `Inv`
(`fold_inv`), so the gate list is `cmpBlocks ++ phaseFlip ++ uncBlocks` of the AND records;
in every branch `c` it maps `|x, 0…0⟩` to `(1/√2)^K · ε · (−1)^{P(x)} |x, 0…0⟩` (`chain_kraus`,
`phaseFlip_kraus`; `ε = ±1` is the global sign of a constant `P`, whose phase flip has no
gate), there are `K` classical bits, and `ancRestore_of_kraus` concludes. -/
theorem lemma_6_3_2 (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hN : N.xorFree = true) (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData)) := by
  obtain ⟨out, st, pp, hout, hst, hpp, hCeq⟩ := synthesizeOracle_ok hC
  obtain ⟨recs, -, -, hcmp, hunc, hpq, -, hvals⟩ :=
    fold_inv hN (Oracle.cone N out) C.nData N.nodes.size le_rfl st hst
  have hgates : C.gates = cmpBlocks recs 0 ++ Oracle.phaseFlip pp ++ uncBlocks recs 0 := by
    have h1 := flatten_mapIdx_cmp recs 0
    have h2 := flatten_mapIdx_unc recs 0
    simp only [Nat.zero_add] at h1 h2
    rw [hCeq, hcmp, hunc, h1, h2]
  have hok := hWF.gatesOk
  rw [hgates] at hok
  have hokc : GatesOk C.nData C.nAnc (cmpBlocks recs 0) :=
    hok.of_subset (fun g hg => by simp [hg])
  have hokp : GatesOk C.nData C.nAnc (Oracle.phaseFlip pp) :=
    hok.of_subset (fun g hg => by simp [hg])
  have hKa : recs.length ≤ C.nAnc := by
    rcases cmpBlocks_length_le hokc with h | h
    · simp [h]
    · omega
  have hnb : C.nBits = recs.length := by
    rw [Circuit.nBits, hgates, Circuit.written, List.flatMap_append, List.flatMap_append,
      ← Circuit.written, ← Circuit.written, ← Circuit.written, written_cmpBlocks,
      written_phaseFlip, List.nil_append, List.nil_append, written_uncBlocks_length]
  have gp := hvals out pp hpp
  -- the predicate is the value of the output on the atom state
  have hpred : ∀ x, N.pred C.nData x =
      pp.eval (runC (a := C.nAnc) recs 0 (x, fun _ => false)) := by
    intro x
    rw [gp.2.2 _ hKa x, ← values_eq_valuesUpTo]
    simp only [Network.pred, Network.eval, hout, List.map_cons, List.map_nil, List.headD_cons]
    rfl
  -- the global sign of a constant predicate
  set ε : ℂ := if pp.lin = [] then (if pp.c then -1 else 1) else 1 with hε
  have hphase : ∀ x, phaseVal pp (runC (a := C.nAnc) recs 0 (x, fun _ => false)) =
      ε * (if N.pred C.nData x then -1 else 1) := by
    intro x
    rw [hpred]
    unfold phaseVal
    by_cases hl : pp.lin = []
    · rw [Aff.eval_nil pp hl]
      simp only [hl, ↓reduceIte, hε]
      cases pp.c <;> norm_num
    · simp [hl, hε]
  refine ancRestore_of_kraus hWF _ (fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ recs.length * ε) ?_
    (fun c => ?_)
  · have hεn : ‖ε‖ = 1 := by
      rw [hε]
      split_ifs <;> simp
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, hnb, norm_mul, hεn, mul_one, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), nsmul_eq_mul]
    rw [← pow_mul, mul_comm recs.length 2, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    rw [← mul_pow]
    norm_num
  · apply kraus_mul_ancProj
    intro x
    rw [hgates, chain_kraus C.nBits c (Oracle.phaseFlip pp) (phaseVal pp)
      (fun s => phaseFlip_kraus C.nBits c pp gp.1 hokp s) recs 0 _ hokc hpq
      (fun i _ => by simp [Qubit.get]), hphase, mul_assoc]

/-- Report §6.3.2, Lemma 6.3.2 in the report's traced form:
`Tr_anc (⟦C⟧ (ρ ⊗ |0…0⟩⟨0…0|)) = U_P ρ U_Pᴴ`. Proved from `lemma_6_3_2`. -/
theorem lemma_6_3_2_traced (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hN : N.xorFree = true) (hWF : C.WF) (ρ : MState (Reg C.nData)) :
    (channelDenote C.nData C.nAnc C (ρ ⊗ᴹ ancZero C.nAnc)).traceRight =
      phaseOracle (N.pred C.nData) ◃ ρ :=
  (lemma_6_3_2 N C hC hN hWF).traced ρ

/-- Report §8, §6.3.2 — the `grover_pred_037` instance of Lemma 6.3.2: the synthesized Grover
oracle on `x[0..8) × anc[0..2)` restores its ancillae and applies `(−1)^(x0 ∧ x3 ∧ x7)`.
Derived from `lemma_6_3_2`; the side conditions (`synthesizeOracle groverNet = .ok
groverOracle`, AND/NOT/OR, `WF`, the predicate) are checked by the kernel (`decide`, `rfl`). -/
theorem grover_pred_037_ancRestore : AncRestore 8 2 groverOracle (phaseOracle groverPred) := by
  have hC : synthesizeOracle groverNet = .ok groverOracle := by rfl
  have hN : groverNet.xorFree = true := by decide
  have hWF : groverOracle.WF := by decide
  have hP : groverNet.pred groverOracle.nData = groverPred := by funext x; rfl
  have h := lemma_6_3_2 groverNet groverOracle hC hN hWF
  rw [hP] at h
  exact h

end

end CQRV

end
