module

public import CQRV.Circuit.OracleCorrectXor

/-!
# CQRV.Circuit.OracleCorrect

Report §6.3.2 (Lemma 6.3.2), §6.2.4 (Layers 1–3), §6.1.1/§6.1.4 (Z on the qubit holding P(x)),
§6.1.2 (in-place XOR), §6.2.2 (MBU) — Lemma 6.3.2 for every network the synthesizer accepts,
with or without XOR nodes, by induction over the synthesizer (Stage 6b-3 for xor-free networks,
generalized in Stage 9a; basis-vector route of DECISIONS.md, Stage 6b-2):

* atoms — `Aff.eval` (`OracleCorrectXor`) and `runC` (the basis state after the compute blocks:
  ancilla `j` holds the `j`-th non-folded AND);
* the invariant `Inv` of the synthesizer's fold and `step_ok_inv`: every recorded value has
  distinct atoms (any number of them) and evaluates, on `runC`, to the node value of the
  network; the compute / uncompute blocks are those of a list of AND records (`AndRec`: the
  `prepare` gates, the two operand qubits, the two operands), each satisfying `AndRec.Ok`
  (`prepare_ok`, `OracleCorrectXor`);
* `cmp_kraus`: one compute block on a basis vector (`pre`, `TempLogicalAND`, `preᴿ`);
* `phaseFlip_kraus`: the phase flip (gather, `X`, `Z`, `X`, ungather) is `(−1)^{P}` (no gate for
  a constant `P`);
* `unc_kraus`: one uncompute block, every branch, `(1/√2)` and the ancilla reset;
  `chain_kraus` nests compute blocks, phase, and uncompute blocks in reverse order;
* `lemma_6_3_2_xor` (Stage 9a) and `lemma_6_3_2` (its corollary, statement of Stage 6a), the
  traced form and the Grover instance;
* `synthesizeOracle_WF` (Stage 11a): `N.WF → synthesizeOracle N = .ok C → C.WF`, by the qubit
  invariant `InvQ` carried alongside `Inv` and the bit discipline of the uncompute blocks
  (`bitsOk_uncBlocks`); so `C.WF` no longer needs a per-instance check.

The synthesizer is unchanged: the AND records exist only in the invariant (existentially).
-/

@[expose] public section

namespace CQRV

open CQRV.Synthesis

/-! ## AND records -/

/-- Report §6.1.2, §6.2.2 — a non-folded AND as the synthesizer emits it: the preparation gates
`pre` of `prepare` (gather CNOTs and polarity `X`), the operand qubits `p`, `q` and the operands
`u`, `v` (affine forms over atoms). The `j`-th such AND has the target `anc j`. -/
structure AndRec where
  pre : List Gate
  p : Qubit
  q : Qubit
  u : Aff
  v : Aff

namespace AndRec

/-- Report §6.1.4, §6.2.2 — the compute block of the AND with target `anc j`. -/
def cmp (r : AndRec) (j : ℕ) : List Gate :=
  r.pre ++ [.alloc (.anc j)] ++ TempLogicalAND r.p r.q (.anc j) ++ r.pre.reverse

/-- Report §6.1.4, §6.2.2 — the uncompute (MBU) block of the AND with target `anc j`, measuring
into the classical bit `b`. -/
def unc (r : AndRec) (j b : ℕ) : List Gate :=
  r.pre ++ UncomputeTempLogicalAND r.p r.q (.anc j) b ++ [.free (.anc j)] ++ r.pre.reverse

/-- Report §6.1.2 — the value of the AND on a basis state: `u ∧ v`. -/
def val {n a : ℕ} (r : AndRec) (s : Reg n × Reg a) : Bool :=
  r.u.eval s && r.v.eval s

end AndRec

/-- The atoms of `u` are data qubits or ancillae `anc j` with `j < K`. -/
def AtomsBelow (K : ℕ) (u : Aff) : Prop := ∀ q ∈ u.lin, ∀ j, q = .anc j → j < K

/-- Report §6.1.2, §6.3.2 — what the invariant records about the AND with target `anc j`:
distinct operand qubits; operand atoms below `anc j`; `pre` is a list of `X` / `CNOT` gates on
qubits below `anc j`; and on every basis state (operand qubits in range), after `pre` the qubit
`p` holds `u` and `q` holds `v` (`prepare_ok`). -/
def AndRec.Ok (r : AndRec) (j : ℕ) : Prop :=
  r.p ≠ r.q ∧ AtomsBelow j r.u ∧ AtomsBelow j r.v ∧ (∀ g ∈ r.pre, g.isPerm = true) ∧
    (∀ g ∈ r.pre, ∀ q ∈ g.qubits, ∀ i, q = .anc i → i < j) ∧
    ∀ {n a : ℕ} (s : Reg n × Reg a), r.p.inRange n a = true → r.q.inRange n a = true →
      r.p.get (permRun r.pre s) = r.u.eval s ∧ r.q.get (permRun r.pre s) = r.v.eval s

/-- `AndRec.Ok` for every record, the first one with target `anc j`. -/
def RecsOk : List AndRec → ℕ → Prop
  | [], _ => True
  | r :: rs, j => r.Ok j ∧ RecsOk rs (j + 1)

theorem RecsOk.append_singleton {rs : List AndRec} {r : AndRec} {j : ℕ} (h : RecsOk rs j)
    (hr : r.Ok (j + rs.length)) : RecsOk (rs ++ [r]) j := by
  induction rs generalizing j with
  | nil => exact ⟨by simpa using hr, trivial⟩
  | cons r' rs ih =>
    refine ⟨h.1, ih h.2 ?_⟩
    rw [List.length_cons] at hr
    rwa [show j + 1 + rs.length = j + (rs.length + 1) by omega]

theorem RecsOk.isPerm {rs : List AndRec} {j : ℕ} (h : RecsOk rs j) :
    ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true := by
  induction rs generalizing j with
  | nil => simp
  | cons r' rs ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    exacts [h.1.2.2.2.1, ih h.2 r hr]

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

/-- Report §6.3.2 — the basis state after the compute blocks of `rs` (the first with target
`anc j`): ancilla `j + k` holds the value of the `k`-th AND. On `(x, 0…0)` from `j = 0` this is
the atom state of `x`. -/
def runC {n a : ℕ} : List AndRec → ℕ → Reg n × Reg a → Reg n × Reg a
  | [], _, s => s
  | r :: rs, j, s => runC rs (j + 1) ((Qubit.anc j).set (r.val s) s)

/-- Report §9.1.1 — the qubit discipline that `Circuit.WF` gives on a piece of the gate list:
qubits in the register, CNOT operands distinct. -/
def GatesOk (n a : ℕ) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (∀ q ∈ g.qubits, q.inRange n a = true) ∧ ∀ p t, g = .cnot p t → p ≠ t

theorem GatesOk.of_subset {n a : ℕ} {gs gs' : List Gate} (h : GatesOk n a gs) (hs : gs' ⊆ gs) :
    GatesOk n a gs' := fun g hg => h g (hs hg)

/-- A larger ancilla register keeps every qubit in range. -/
theorem GatesOk.mono {n a a' : ℕ} {gs : List Gate} (h : GatesOk n a gs) (ha : a ≤ a') :
    GatesOk n a' gs := fun g hg => ⟨fun q hq => by
      have := (h g hg).1 q hq
      cases q <;> simp_all [Qubit.inRange]; omega, (h g hg).2⟩

noncomputable section

open Matrix
open scoped MState Kronecker

variable {n a : ℕ}

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

/-! ## Compute and uncompute blocks on basis vectors -/

section Blocks

variable (nb : ℕ) (c : Fin nb → Bool)

theorem single_kraus_one (g : Gate) (hg : gateK n a c g = 1) (v : Reg n × Reg a → ℂ) :
    krausOps n a nb [g] c *ᵥ v = v := by
  rw [krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec, hg, Matrix.one_mulVec]

/-- The range and distinctness facts of one AND that `Circuit.WF` gives on its compute block. -/
theorem AndRec.ok_of_gatesOk {r : AndRec} {j : ℕ} (h : GatesOk n a (r.cmp j)) :
    r.p.inRange n a = true ∧ r.q.inRange n a = true ∧ (Qubit.anc j).inRange n a = true ∧
      r.p ≠ .anc j ∧ r.q ≠ .anc j := by
  have h1 := h (.cnot r.p (.anc j)) (by simp [AndRec.cmp, TempLogicalAND])
  have h2 := h (.cnot r.q (.anc j)) (by simp [AndRec.cmp, TempLogicalAND])
  exact ⟨h1.1 _ (by simp [Gate.qubits]), h2.1 _ (by simp [Gate.qubits]),
    h1.1 _ (by simp [Gate.qubits]), h1.2 _ _ rfl, h2.2 _ _ rfl⟩

/-- `pre` and `preᴿ` do not touch the target `anc j`. -/
theorem AndRec.Ok.avoid {r : AndRec} {j : ℕ} (hr : r.Ok j) :
    ∀ g ∈ r.pre, Qubit.anc j ∉ g.qubits :=
  fun g hg hm => by have := hr.2.2.2.2.1 g hg _ hm j rfl; omega

theorem AndRec.Ok.avoid_rev {r : AndRec} {j : ℕ} (hr : r.Ok j) :
    ∀ g ∈ r.pre.reverse, Qubit.anc j ∉ g.qubits :=
  fun g hg => hr.avoid g (List.mem_reverse.mp hg)

theorem AndRec.Ok.isPerm_rev {r : AndRec} {j : ℕ} (hr : r.Ok j) :
    ∀ g ∈ r.pre.reverse, g.isPerm = true :=
  fun g hg => hr.2.2.2.1 g (List.mem_reverse.mp hg)

/-- Report §6.1.2, §6.2.2, §6.2.4 Layer 1 — the compute block of one AND, in any branch: on a
basis state with `anc j = 0`, it sets `anc j` to the AND value `u ∧ v` and changes nothing else
(`pre` puts `u`, `v` on `p`, `q`; `TempLogicalAND` writes `anc j`; `preᴿ` restores the atoms). -/
theorem cmp_kraus {r : AndRec} {j : ℕ} (hr : r.Ok j) (hok : GatesOk n a (r.cmp j))
    (s : Reg n × Reg a) (hs : (Qubit.anc j).get s = false) :
    krausOps n a nb (r.cmp j) c *ᵥ basisVec s = basisVec ((Qubit.anc j).set (r.val s) s) := by
  obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hok
  have hs1 : (Qubit.anc j).get (permRun r.pre s) = false := by
    rw [get_permRun_of_avoid hr.avoid, hs]
  have hsem := hr.2.2.2.2.2 s hp hq
  rw [AndRec.cmp, krausOps_append_mulVec, krausOps_append_mulVec, krausOps_append_mulVec,
    perm_kraus nb c hr.2.2.2.1, single_kraus_one nb c _ rfl,
    tempLogicalAND_kraus_basis nb c r.p r.q _ hr.1 hpt hqt hp hq ht _ hs1,
    perm_kraus nb c hr.isPerm_rev, permRun_set_comm hr.avoid_rev,
    permRun_reverse hr.2.2.2.1, hsem.1, hsem.2]
  rfl

/-- Report §6.2.2, §6.2.4 Layer 2 — the uncompute block of one AND, in every branch `c` and for
any classical bit `b`: on a basis state whose `anc j` holds the AND value, it resets `anc j`
with amplitude `1/√2` and no sign. -/
theorem unc_kraus {r : AndRec} {j : ℕ} (b : ℕ) (hr : r.Ok j) (hok : GatesOk n a (r.cmp j))
    (s : Reg n × Reg a) (hs : (Qubit.anc j).get s = r.val s) :
    krausOps n a nb (r.unc j b) c *ᵥ basisVec s =
      ((Real.sqrt 2)⁻¹ : ℂ) • basisVec ((Qubit.anc j).set false s) := by
  obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hok
  have hsem := hr.2.2.2.2.2 s hp hq
  have hs1 : (Qubit.anc j).get (permRun r.pre s) =
      (r.p.get (permRun r.pre s) && r.q.get (permRun r.pre s)) := by
    rw [get_permRun_of_avoid hr.avoid, hs, hsem.1, hsem.2]
    rfl
  rw [AndRec.unc, krausOps_append_mulVec, krausOps_append_mulVec, krausOps_append_mulVec,
    perm_kraus nb c hr.2.2.2.1, mbu_branch_basis r.p r.q _ b hpt hqt ht c _ hs1,
    Matrix.mulVec_smul, single_kraus_one nb c _ rfl, Matrix.mulVec_smul,
    perm_kraus nb c hr.isPerm_rev, permRun_set_comm hr.avoid_rev, permRun_reverse hr.2.2.2.1]

/-! ## Nesting: compute blocks, phase, uncompute blocks in reverse order -/

theorem runC_fst (rs : List AndRec) (j : ℕ) (s : Reg n × Reg a) : (runC rs j s).1 = s.1 := by
  induction rs generalizing j s with
  | nil => rfl
  | cons r rs ih =>
    rw [runC, ih]
    simp only [Qubit.set]
    split_ifs <;> rfl

/-- Report §6.2.4, §6.3.2 — the nested brackets of the oracle on a basis vector, in any branch:
if the middle part `Φ` is diagonal on basis vectors (`φ`), the compute blocks of `rs`, `Φ`, and
the uncompute blocks in reverse order map `|s⟩` (ancillae `≥ j` at 0) to
`(1/√2)^{|rs|} · φ(runC rs j s) · |s⟩`. Induction on `rs`: the outermost compute block sets
`anc j`, the inner part acts as a scalar, the outermost uncompute block resets `anc j`. -/
theorem chain_kraus (Φ : List Gate) (φ : Reg n × Reg a → ℂ)
    (hΦ : ∀ s, krausOps n a nb Φ c *ᵥ basisVec s = φ s • basisVec s) :
    ∀ (rs : List AndRec) (j : ℕ) (s : Reg n × Reg a), GatesOk n a (cmpBlocks rs j) →
      RecsOk rs j → (∀ i, j ≤ i → (Qubit.anc i).get s = false) →
      krausOps n a nb (cmpBlocks rs j ++ Φ ++ uncBlocks rs j) c *ᵥ basisVec s =
        (((Real.sqrt 2)⁻¹ : ℂ) ^ rs.length * φ (runC rs j s)) • basisVec s
  | [], j, s, _, _, _ => by
    simp only [cmpBlocks, uncBlocks, List.nil_append, List.append_nil, hΦ, runC, List.length_nil,
      pow_zero, one_mul]
  | r :: rs, j, s, hok, hrs, hs => by
    have hokr : GatesOk n a (r.cmp j) := hok.of_subset (by simp [cmpBlocks])
    have hokrs : GatesOk n a (cmpBlocks rs (j + 1)) := hok.of_subset (by simp [cmpBlocks])
    obtain ⟨hp, hq, ht, hpt, hqt⟩ := AndRec.ok_of_gatesOk hokr
    have hr : r.Ok j := hrs.1
    set s' := (Qubit.anc j).set (r.val s) s with hs'
    have hs'' : ∀ i, j + 1 ≤ i → (Qubit.anc i).get s' = false := by
      intro i hi
      rw [hs', Qubit.get_set_ne (by simp; omega)]
      exact hs i (by omega)
    have ih := chain_kraus Φ φ hΦ rs (j + 1) s' hokrs hrs.2 hs''
    have hsplit : cmpBlocks (r :: rs) j ++ Φ ++ uncBlocks (r :: rs) j =
        r.cmp j ++ (cmpBlocks rs (j + 1) ++ Φ ++ uncBlocks rs (j + 1)) ++ r.unc j rs.length := by
      simp only [cmpBlocks, uncBlocks, List.append_assoc]
    have hval : (Qubit.anc j).get s' = r.val s' := by
      rw [hs', Qubit.get_set_self _ ht, AndRec.val, AndRec.val, Aff.eval_set_anc hr.2.1,
        Aff.eval_set_anc hr.2.2.1]
    have hback : (Qubit.anc j).set false s' = s := by
      rw [hs', Qubit.set_set, ← hs j le_rfl, Qubit.set_get]
    rw [hsplit, krausOps_append_mulVec, krausOps_append_mulVec, cmp_kraus nb c hr hokr s
      (hs j le_rfl), ← hs', ih, Matrix.mulVec_smul, unc_kraus nb c _ hr hokr s' hval, hback,
      smul_smul, runC, List.length_cons, pow_succ]
    congr 1
    ring

end Blocks

/-! ## The invariant of the synthesizer's fold -/

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

/-- Report §6.1.2 — the folding identities are exact on every state:
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

/-- Report §6.3.2 — what the invariant asks of the recorded value `u` of node `i` after the
nodes `< k`, the non-folded ANDs so far being `recs`: distinct atoms (any number: XOR nodes
have several), atoms below `anc recs.length`, and on the atom state `runC recs 0 (x, 0…0)` the
value of node `i` on `x`. (Stage 6b-3 had `u.lin.length ≤ 1` in place of `u.lin.Nodup`.) -/
def Good (N : Network) (n k : ℕ) (recs : List AndRec) (i : ℕ) (u : Aff) : Prop :=
  u.lin.Nodup ∧ AtomsBelow recs.length u ∧
    ∀ a, recs.length ≤ a → ∀ x : Reg n,
      u.eval (runC (a := a) recs 0 (x, fun _ => false)) =
        (valuesUpTo N (inputOf x) k).getD i false

/-- Report §6.3.2 — the invariant of the synthesizer's fold after the nodes `< k`: the non-folded
ANDs so far are the records `recs` (the `j`-th has target `anc j` and satisfies `AndRec.Ok`),
the compute / uncompute blocks are theirs, and every recorded value is `Good`. -/
def Inv (N : Network) (n k : ℕ) (st : Oracle.St) : Prop :=
  ∃ recs : List AndRec,
    st.vals.size = k ∧ st.nextAnc = recs.length ∧
    st.compute.toList = recs.mapIdx (fun j r => r.cmp j) ∧
    st.uncompute.toList = recs.mapIdx (fun j r => r.unc j 0) ∧
    RecsOk recs 0 ∧
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

/-- Report §6.1.2, §6.3.2 (Stage 9a item 3) — one step of the synthesizer preserves the
invariant, for every node kind (XOR included; node `k` in range, the step succeeded). -/
theorem step_ok_inv {N : Network} (mark : Array Bool) {n k : ℕ}
    (hk : k < N.nodes.size) {st st' : Oracle.St} (h : Oracle.step N mark st k = .ok st')
    (hinv : Inv N n k st) : Inv N n (k + 1) st' := by
  obtain ⟨recs, hsize, hnext, hcmp, hunc, hrecs, hvals⟩ := hinv
  have hval : ∀ x : Reg n, (valuesUpTo N (inputOf x) (k + 1)).getD k false =
      nodeVal (inputOf x) (valuesUpTo N (inputOf x) k) N.nodes[k] := fun x => by
    rw [valuesUpTo_succ N _ hk, nodeStep, Array.getD_push_eq, valuesUpTo_size N _ hk.le]
    simp
  -- a value pushed with unchanged records
  have keep : ∀ e : Option Aff, (∀ u, e = some u → Good N n (k + 1) recs k u) →
      Inv N n (k + 1) { st with vals := st.vals.push e } := fun e he =>
    ⟨recs, by simp [hsize], hnext, hcmp, hunc, hrecs, vals_push hk hsize hvals e he⟩
  unfold Oracle.step at h
  split at h
  · rw [except_pure_eq_ok] at h
    subst h
    exact keep none (fun u hu => by cases hu)
  rw [Array.getElem?_eq_getElem hk] at h
  generalize hnd : N.nodes[k] = nd at h hval
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
  | xor i j =>
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
    rw [except_pure_eq_ok] at h
    subst h
    have gu := hvals i u' hu'
    have gv := hvals j v' hv'
    refine keep _ (fun w hw => ?_)
    cases hw
    refine ⟨symDiff_nodup gu.1 gv.1, fun q hq => ?_, fun a ha x => ?_⟩
    · rcases mem_symDiff hq with hq | hq
      exacts [gu.2.1 q hq, gv.2.1 q hq]
    · rw [Aff.eval_symDiff gu.1 gv.1, gu.2.2 a ha x, gv.2.2 a ha x, hval x, nodeVal]
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
    · -- a new ancilla: the record of `prepare`
      rw [except_bind_eq_ok] at h
      obtain ⟨⟨pre, pu, pv⟩, hprep, h⟩ := h
      rw [except_pure_eq_ok] at h
      subst h
      obtain ⟨hpq, hperm, hqub, hsem⟩ := prepare_ok hprep gu.1 gv.1
      have hrok : (AndRec.mk pre pu pv u' v').Ok (0 + recs.length) := by
        rw [Nat.zero_add]
        refine ⟨hpq, gu.2.1, gv.2.1, hperm, fun g hg q hq i hi => ?_, fun s hp hq => hsem s hp hq⟩
        rcases hqub g hg q hq with hq | hq
        exacts [gu.2.1 q hq i hi, gv.2.1 q hq i hi]
      refine ⟨recs ++ [⟨pre, pu, pv, u', v'⟩], by simp [hsize], by simp [hnext], ?_, ?_,
        hrecs.append_singleton hrok, ?_⟩
      · simp only [Array.toList_push, hcmp, List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
          hnext, Nat.zero_add]
        rfl
      · simp only [Array.toList_push, hunc, List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
          hnext, Nat.zero_add]
        rfl
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
            ← gu.2.2 a ha'.le x, ← gv.2.2 a ha'.le x]

/-- Report §6.3.2 — the invariant holds after the synthesizer's fold over the first `m` nodes
(`List.foldlM` induction; every `step` returned `.ok`). -/
theorem fold_inv {N : Network} (mark : Array Bool) (n : ℕ) :
    ∀ m, m ≤ N.nodes.size → ∀ st,
      (List.range m).foldlM (Oracle.step N mark) ({ vals := #[] } : Oracle.St) = .ok st →
        Inv N n m st
  | 0, _, st, h => by
    rw [List.range_zero, List.foldlM_nil, except_pure_eq_ok] at h
    subst h
    exact ⟨[], rfl, rfl, rfl, rfl, trivial, fun i u hu => by simp at hu⟩
  | m + 1, hm, st, h => by
    rw [List.range_succ, List.foldlM_append, except_bind_eq_ok] at h
    obtain ⟨st₁, h₁, h⟩ := h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    exact step_ok_inv mark (by omega) h (fold_inv mark n m (by omega) st₁ h₁)

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

theorem Gate.writes_of_isPerm {g : Gate} (hg : g.isPerm = true) : g.writes = [] := by
  cases g <;> simp_all [Gate.isPerm, Gate.writes]

theorem Gate.shiftBits_of_isPerm {g : Gate} (hg : g.isPerm = true) (k : ℕ) : g.shiftBits k = g := by
  cases g <;> simp_all [Gate.isPerm, Gate.shiftBits]

/-- `X` / `CNOT` gates write no classical bit. -/
theorem written_perm {gs : List Gate} (h : ∀ g ∈ gs, g.isPerm = true) :
    gs.flatMap Gate.writes = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, Gate.writes_of_isPerm (h g (by simp)),
      ih (fun g' hg' => h g' (by simp [hg']))]
    rfl

theorem map_shift_perm {gs : List Gate} (h : ∀ g ∈ gs, g.isPerm = true) (k : ℕ) :
    gs.map (Gate.shiftBits k) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, Gate.shiftBits_of_isPerm (h g (by simp)),
      ih (fun g' hg' => h g' (by simp [hg']))]

theorem written_cmp {r : AndRec} (hp : ∀ g ∈ r.pre, g.isPerm = true) (j : ℕ) :
    Circuit.written (r.cmp j) = [] := by
  have h2 : r.pre.reverse.flatMap Gate.writes = [] :=
    written_perm (fun g hg => hp g (List.mem_reverse.mp hg))
  simp [Circuit.written, AndRec.cmp, TempLogicalAND, Gate.writes, written_perm hp, h2]

theorem written_unc {r : AndRec} (hp : ∀ g ∈ r.pre, g.isPerm = true) (j b : ℕ) :
    Circuit.written (r.unc j b) = [b] := by
  have h2 : r.pre.reverse.flatMap Gate.writes = [] :=
    written_perm (fun g hg => hp g (List.mem_reverse.mp hg))
  simp [Circuit.written, AndRec.unc, UncomputeTempLogicalAND, Gate.writes, written_perm hp, h2]

theorem written_cmpBlocks {rs : List AndRec} (hp : ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true)
    (j : ℕ) : Circuit.written (cmpBlocks rs j) = [] := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [cmpBlocks, Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
      written_cmp (hp r (by simp)), ih (fun r' hr' => hp r' (by simp [hr']))]
    rfl

theorem written_uncBlocks_length {rs : List AndRec}
    (hp : ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true) (j : ℕ) :
    (Circuit.written (uncBlocks rs j)).length = rs.length := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    rw [uncBlocks, Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
      written_unc (hp r (by simp)), List.length_append, ih (fun r' hr' => hp r' (by simp [hr']))]
    rfl

theorem written_phaseFlip (pp : Aff) : Circuit.written (Oracle.phaseFlip pp) = [] := by
  unfold Oracle.phaseFlip
  split
  · rfl
  · cases pp.c <;> simp [Circuit.written, Oracle.gather, Gate.writes] <;>
      (intro g _ _ _ hg; subst hg; rfl)

theorem unc_map_shift {r : AndRec} (hp : ∀ g ∈ r.pre, g.isPerm = true) (j b k : ℕ) :
    (r.unc j b).map (Gate.shiftBits k) = r.unc j (b + k) := by
  have h2 := map_shift_perm (fun g hg => hp g (List.mem_reverse.mp hg)) k
  simp [AndRec.unc, UncomputeTempLogicalAND, Gate.shiftBits, map_shift_perm hp, h2]

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
theorem flatten_mapIdx_unc {rs : List AndRec} (hp : ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true)
    (j : ℕ) :
    ((rs.mapIdx (fun i r => r.unc (j + i) 0)).reverse.mapIdx
      (fun i blk => blk.map (Gate.shiftBits i))).flatten = uncBlocks rs j := by
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih =>
    have hf : (fun i r => AndRec.unc r (j + (i + 1)) 0) = (fun i r => r.unc (j + 1 + i) 0) := by
      funext i r'; congr 1; omega
    rw [List.mapIdx_cons, hf, List.reverse_cons, List.mapIdx_append, List.flatten_append,
      ih (fun r' hr' => hp r' (by simp [hr'])), uncBlocks, Nat.add_zero]
    simp [unc_map_shift (hp r (by simp))]

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

/-- Report §6.1.1, §6.1.4 Step 3 (Stage 9a item 4) — for `P` with distinct atoms, the phase
flip (gather `P.lin` onto its first atom `q`, `X q` if `P.c`, `Z q`, then the reverse) maps
`|s⟩` to `phaseVal P s · |s⟩` in every branch: after the gather and the `X`, `q` holds
`P.eval s`; `Z` gives the sign; the reversed gates undo the permutation (`permRun_reverse`). -/
theorem phaseFlip_kraus (pp : Aff) (hnd : pp.lin.Nodup)
    (hok : GatesOk n a (Oracle.phaseFlip pp)) (s : Reg n × Reg a) :
    krausOps n a nb (Oracle.phaseFlip pp) c *ᵥ basisVec s = phaseVal pp s • basisVec s := by
  rcases hl : pp.lin with _ | ⟨q, l⟩
  · have hpf : Oracle.phaseFlip pp = [] := by unfold Oracle.phaseFlip; rw [hl]
    rw [hpf, krausOps_nil, Matrix.one_mulVec]
    simp [phaseVal, hl]
  · set P := Oracle.gather (q :: l) q ++ (if pp.c then [Gate.x q] else []) with hPdef
    have hpf : Oracle.phaseFlip pp = P ++ [Gate.z q] ++ P.reverse := by
      unfold Oracle.phaseFlip
      rw [hl]
    have hP : ∀ g ∈ P, g.isPerm = true := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      exacts [gather_isPerm _ _ g hg, polGates_isPerm _ _ g hg]
    have hPr : ∀ g ∈ P.reverse, g.isPerm = true := fun g hg => hP g (List.mem_reverse.mp hg)
    have hq : q.inRange n a = true :=
      (hok (.z q) (by rw [hpf]; simp)).1 q (by simp [Gate.qubits])
    rw [hl] at hnd
    rw [hpf, krausOps_append_mulVec, krausOps_append_mulVec, perm_kraus nb c hP,
      krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec]
    change krausOps n a nb _ c *ᵥ (gateU n a (.z q) *ᵥ _) = _
    rw [z_basis, Matrix.mulVec_smul, perm_kraus nb c hPr, permRun_reverse hP, hPdef,
      get_permRun_gather_pol hnd List.mem_cons_self hq, phaseVal, Aff.eval_eq_xorL, hl]
    simp

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

/-- Report §6.3.2, Lemma 6.3.2 — parametric over the Stage 5 synthesizer: for every network
`N` (AND/NOT/XOR, hence also OR and `if`; Stage 9a) whose oracle `C` is synthesized and well
formed, `C` restores its ancillae and
applies the phase oracle of `N`'s predicate, on any ancilla register `a ≥ C.nAnc` (the ancillae
`≥ C.nAnc` are never touched; Stage 7a: the Grover circuit shares one register between the
oracle and the larger MCZ of the diffusion). The statement is on density operators, not on
basis states (§6.2.4: on basis states the phase cancels); Theorem 3.3a is not used inside the
oracle (§6.3.2). Proof (Stage 6b-3 basis-vector route, Stage 9a for XOR: in-place `gather`
CNOTs, `prepare_ok`): the synthesizer's fold keeps `Inv`
(`fold_inv`), so the gate list is `cmpBlocks ++ phaseFlip ++ uncBlocks` of the AND records;
in every branch `c` it maps `|x, 0…0⟩` to `(1/√2)^K · ε · (−1)^{P(x)} |x, 0…0⟩` (`chain_kraus`,
`phaseFlip_kraus`; `ε = ±1` is the global sign of a constant `P`, whose phase flip has no
gate), there are `K` classical bits, and `ancRestore_of_kraus` concludes. -/
theorem lemma_6_3_2_xor_of_le (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hWF : C.WF) (a : ℕ) (ha : C.nAnc ≤ a) :
    AncRestore C.nData a C (phaseOracle (N.pred C.nData)) := by
  obtain ⟨out, st, pp, hout, hst, hpp, hCeq⟩ := synthesizeOracle_ok hC
  obtain ⟨recs, -, -, hcmp, hunc, hrecs, hvals⟩ :=
    fold_inv (Oracle.cone N out) C.nData N.nodes.size le_rfl st hst
  have hperm := hrecs.isPerm
  have hgates : C.gates = cmpBlocks recs 0 ++ Oracle.phaseFlip pp ++ uncBlocks recs 0 := by
    have h1 := flatten_mapIdx_cmp recs 0
    have h2 := flatten_mapIdx_unc hperm 0
    simp only [Nat.zero_add] at h1 h2
    rw [hCeq, hcmp, hunc, h1, h2]
  have hok := hWF.gatesOk.mono ha
  rw [hgates] at hok
  have hokc : GatesOk C.nData a (cmpBlocks recs 0) :=
    hok.of_subset (fun g hg => by simp [hg])
  have hokp : GatesOk C.nData a (Oracle.phaseFlip pp) :=
    hok.of_subset (fun g hg => by simp [hg])
  have hKa : recs.length ≤ a := by
    rcases cmpBlocks_length_le hokc with h | h
    · simp [h]
    · omega
  have hnb : C.nBits = recs.length := by
    rw [Circuit.nBits, hgates, Circuit.written, List.flatMap_append, List.flatMap_append,
      ← Circuit.written, ← Circuit.written, ← Circuit.written, written_cmpBlocks hperm,
      written_phaseFlip, List.nil_append, List.nil_append, written_uncBlocks_length hperm]
  have gp := hvals out pp hpp
  -- the predicate is the value of the output on the atom state
  have hpred : ∀ x, N.pred C.nData x =
      pp.eval (runC (a := a) recs 0 (x, fun _ => false)) := by
    intro x
    rw [gp.2.2 _ hKa x, ← values_eq_valuesUpTo]
    simp only [Network.pred, Network.eval, hout, List.map_cons, List.map_nil, List.headD_cons]
    rfl
  -- the global sign of a constant predicate
  set ε : ℂ := if pp.lin = [] then (if pp.c then -1 else 1) else 1 with hε
  have hphase : ∀ x, phaseVal pp (runC (a := a) recs 0 (x, fun _ => false)) =
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
      (fun s => phaseFlip_kraus C.nBits c pp gp.1 hokp s) recs 0 _ hokc hrecs
      (fun i _ => by simp [Qubit.get]), hphase, mul_assoc]

/-- Report §6.3.2, Lemma 6.3.2 for networks with XOR nodes (Stage 9a; SORRIES.md row
`lemma_6_3_2_xor`): `lemma_6_3_2` without `N.xorFree`, at the circuit's own ancilla register. -/
theorem lemma_6_3_2_xor (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData)) :=
  lemma_6_3_2_xor_of_le N C hC hWF C.nAnc le_rfl

/-- Report §6.3.2, Lemma 6.3.2 at a register `a ≥ C.nAnc` — superseded by
`lemma_6_3_2_xor_of_le` (Stage 9a). Kept for compatibility with its Stage 7a statement: the
hypothesis `N.xorFree` of Stage 6a is unused; a corollary of `lemma_6_3_2_xor_of_le`. -/
theorem lemma_6_3_2_of_le (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (_hN : N.xorFree = true) (hWF : C.WF) (a : ℕ) (ha : C.nAnc ≤ a) :
    AncRestore C.nData a C (phaseOracle (N.pred C.nData)) :=
  lemma_6_3_2_xor_of_le N C hC hWF a ha

/-- Report §6.3.2, Lemma 6.3.2 — superseded by `lemma_6_3_2_xor` (Stage 9a). Kept for
compatibility with its Stage 6a statement (AND/NOT/OR networks; the hypothesis `N.xorFree` is
unused): a corollary of `lemma_6_3_2_xor`. -/
theorem lemma_6_3_2 (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (_hN : N.xorFree = true) (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData)) :=
  lemma_6_3_2_xor N C hC hWF

/-- Report §6.3.2, Lemma 6.3.2 in the report's traced form:
`Tr_anc (⟦C⟧ (ρ ⊗ |0…0⟩⟨0…0|)) = U_P ρ U_Pᴴ`. Proved from `lemma_6_3_2`. -/
theorem lemma_6_3_2_traced (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hN : N.xorFree = true) (hWF : C.WF) (ρ : MState (Reg C.nData)) :
    (channelDenote C.nData C.nAnc C (ρ ⊗ᴹ ancZero C.nAnc)).traceRight =
      phaseOracle (N.pred C.nData) ◃ ρ :=
  (lemma_6_3_2 N C hC hN hWF).traced ρ

/-! ## Stage 11a — well-formedness of every synthesized oracle (`synthesizeOracle_WF`) -/

/-- Report §9.1.1 (Stage 11a) — the data atoms of `u` lie in the register `x[0..nI)`. -/
def DataBelow (nI : ℕ) (u : Aff) : Prop := ∀ q ∈ u.lin, ∀ d, q = .data d → d < nI

/-- Report §6.3.2, §9.1.1 (Stage 11a) — the qubit part of the well-formedness invariant of the
synthesizer's fold: every recorded value has its data atoms below `nI`, and every gate of the
compute and uncompute blocks passes `Gate.qubitsOk nI`. Carried alongside `Inv`, which supplies
the distinct atoms and the ancilla atoms below `anc nextAnc`. -/
def InvQ (nI : ℕ) (st : Oracle.St) : Prop :=
  (∀ i u, st.vals.getD i none = some u → DataBelow nI u) ∧
  (∀ blk ∈ st.compute.toList, ∀ g ∈ blk, g.qubitsOk nI = true) ∧
  (∀ blk ∈ st.uncompute.toList, ∀ g ∈ blk, g.qubitsOk nI = true)

/-- The vals clause of `InvQ` after pushing the value `e`. -/
theorem vals_push_data {nI : ℕ} {vals : Array (Option Aff)}
    (hv : ∀ i u, vals.getD i none = some u → DataBelow nI u) (e : Option Aff)
    (he : ∀ u, e = some u → DataBelow nI u) :
    ∀ i u, (vals.push e).getD i none = some u → DataBelow nI u := by
  intro i u hu
  rw [Array.getD_push_eq] at hu
  split_ifs at hu
  exacts [he u hu, hv i u hu]

/-- Report §6.1.2 — the CNOTs of `gather` have distinct operands (the pivot is filtered out). -/
theorem gather_cnot_ne {S : List Qubit} {p : Qubit} {g : Gate} (hg : g ∈ Oracle.gather S p)
    {a b : Qubit} (he : g = .cnot a b) : a ≠ b := by
  simp only [Oracle.gather, List.mem_map] at hg
  obtain ⟨s, hs, rfl⟩ := hg
  cases he
  simpa using (List.mem_filter.mp hs).2

/-- Report §6.1.2 (Stage 11a) — the operand qubits of `prepare` are atoms of the operands, and its
CNOTs have distinct operands. -/
theorem prepare_wf {u v : Aff} {pre : List Gate} {pu pv : Qubit}
    (h : Oracle.prepare u v = .ok (pre, pu, pv)) :
    (pu ∈ u.lin ∨ pu ∈ v.lin) ∧ (pv ∈ u.lin ∨ pv ∈ v.lin) ∧
      ∀ g ∈ pre, ∀ a b, g = .cnot a b → a ≠ b := by
  unfold Oracle.prepare at h
  dsimp only at h
  split at h
  swap
  · rw [except_bind_eq_ok] at h
    obtain ⟨_, hf, _⟩ := h
    exact absurd hf (fail_ne_ok _ _)
  rename_i p₀ us hul
  simp only [pure_bind] at h
  split at h
  swap
  · rw [except_bind_eq_ok] at h
    obtain ⟨_, hf, _⟩ := h
    exact absurd hf (fail_ne_ok _ _)
  rename_i q₀ vs hvl
  simp only [except_pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hq₀f : q₀ ∈ (if v.lin.contains p₀ = true then
      p₀ :: symDiff (u.lin.erase p₀) (v.lin.erase p₀) else v.lin).filter (· != p₀) := by
    rw [hvl]; exact List.mem_cons_self
  refine ⟨Or.inl (by rw [hul]; exact List.mem_cons_self), ?_, ?_⟩
  · obtain ⟨hS, hne⟩ := List.mem_filter.mp hq₀f
    split_ifs at hS
    · rcases List.mem_cons.mp hS with rfl | hS
      · simp at hne
      · rcases mem_symDiff hS with hS | hS
        exacts [Or.inl (List.mem_of_mem_erase hS), Or.inr (List.mem_of_mem_erase hS)]
    · exact Or.inr hS
  · intro g hg a b he
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      exacts [gather_cnot_ne hg he, gather_cnot_ne hg he]
    · subst he
      split_ifs at hg <;> simp at hg

/-- Report §9.1.1 — an `X` / `CNOT` gate on data qubits below `nI`, with distinct CNOT operands,
passes `qubitsOk`. -/
theorem Gate.qubitsOk_of_isPerm {nI : ℕ} {g : Gate} (hp : g.isPerm = true)
    (hq : ∀ q ∈ g.qubits, ∀ d, q = .data d → d < nI) (hd : ∀ a b, g = .cnot a b → a ≠ b) :
    g.qubitsOk nI = true := by
  cases g with
  | x q => cases q <;> simp_all [Gate.qubitsOk, Gate.qubits]
  | cnot a b => cases a <;> cases b <;> simp_all [Gate.qubitsOk, Gate.qubits]
  | _ => simp [Gate.isPerm] at hp

/-- Report §6.2.2, §9.1.1 — the compute and uncompute blocks of one AND with target `anc j` pass
`qubitsOk` when `pre` does and the operand qubits are distinct, in range, and not the target. -/
theorem and_blocks_qubitsOk {nI j : ℕ} {pre : List Gate} {p q : Qubit}
    (hpre : ∀ g ∈ pre, g.qubitsOk nI = true)
    (hp : ∀ d, p = .data d → d < nI) (hq : ∀ d, q = .data d → d < nI)
    (hpq : p ≠ q) (hpt : p ≠ .anc j) (hqt : q ≠ .anc j) :
    (∀ g ∈ pre ++ [.alloc (.anc j)] ++ TempLogicalAND p q (.anc j) ++ pre.reverse,
        g.qubitsOk nI = true) ∧
      ∀ g ∈ pre ++ UncomputeTempLogicalAND p q (.anc j) 0 ++ [.free (.anc j)] ++ pre.reverse,
        g.qubitsOk nI = true := by
  have hand : ∀ g ∈ TempLogicalAND p q (.anc j), g.qubitsOk nI = true := by
    intro g hg
    clear hpre
    have hpt' := hpt.symm
    have hqt' := hqt.symm
    simp only [TempLogicalAND, List.mem_cons, List.not_mem_nil, or_false] at hg
    cases p <;> cases q <;>
      rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [Gate.qubitsOk, Gate.qubits]
  have hunc : ∀ g ∈ UncomputeTempLogicalAND p q (.anc j) 0, g.qubitsOk nI = true := by
    intro g hg
    clear hpre
    have hpt' := hpt.symm
    have hqt' := hqt.symm
    simp only [UncomputeTempLogicalAND, List.mem_cons, List.not_mem_nil, or_false] at hg
    cases p <;> cases q <;> rcases hg with rfl|rfl|rfl|rfl <;>
      simp_all [Gate.qubitsOk, Gate.qubits]
  constructor
  · intro g hg
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | hg) | hg
    exacts [hpre g hg, rfl, hand g hg, hpre g hg]
  · intro g hg
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | rfl) | hg
    exacts [hpre g hg, hunc g hg, rfl, hpre g hg]

/-- Report §6.1.2 — in a well-formed network every `input i` node has `i < nInputs`. -/
theorem Network.WF.input_lt {N : Network} (hN : N.WF) {k i : ℕ}
    (h : N.nodes[k]? = some (.input i)) : i < N.nInputs := by
  have hk : k < N.nodes.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at h
    cases h
  unfold Network.WF Network.wf at hN
  rw [Bool.and_eq_true] at hN
  have := List.all_eq_true.mp hN.1 k (List.mem_range.mpr hk)
  rw [h] at this
  simpa using this

/-- Report §6.1.2, §9.1.1 (Stage 11a) — one step of the synthesizer preserves `InvQ`, given `Inv`
before the step and `N.WF` (for the `input` nodes). -/
theorem step_ok_invQ {N : Network} (hN : N.WF) (mark : Array Bool) {n k : ℕ}
    (hk : k < N.nodes.size) {st st' : Oracle.St} (h : Oracle.step N mark st k = .ok st')
    (hinv : Inv N n k st) (hq : InvQ N.nInputs st) : InvQ N.nInputs st' := by
  obtain ⟨recs, -, hnext, -, -, -, hvals⟩ := hinv
  obtain ⟨hd, hcq, huq⟩ := hq
  have keep : ∀ e : Option Aff, (∀ u, e = some u → DataBelow N.nInputs u) →
      InvQ N.nInputs { st with vals := st.vals.push e } := fun e he =>
    ⟨vals_push_data hd e he, hcq, huq⟩
  unfold Oracle.step at h
  split at h
  · rw [except_pure_eq_ok] at h
    subst h
    exact keep none (fun u hu => by cases hu)
  have hnk := Array.getElem?_eq_getElem hk
  rw [hnk] at h
  generalize hnd : N.nodes[k] = nd at h hnk
  cases nd with
  | input i =>
    rw [except_pure_eq_ok] at h
    subst h
    refine keep _ (fun u hu => ?_)
    cases hu
    intro q hq d hdq
    simp only [List.mem_singleton] at hq
    subst hq
    cases hdq
    exact Network.WF.input_lt hN hnk
  | const b =>
    rw [except_pure_eq_ok] at h
    subst h
    exact keep _ (fun u hu q hq => by cases hu; simp at hq)
  | not i =>
    rw [except_bind_eq_ok] at h
    obtain ⟨u, hu, h⟩ := h
    beta_reduce at hu
    split at hu
    · rename_i u' hu'
      rw [except_pure_eq_ok] at hu h
      subst hu h
      exact keep _ (fun w hw => by cases hw; exact hd i u' hu')
    · exact absurd hu (fail_ne_ok _ _)
  | xor i j =>
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
    rw [except_pure_eq_ok] at h
    subst h
    refine keep _ (fun w hw q hq => ?_)
    cases hw
    rcases mem_symDiff hq with hq | hq
    exacts [hd i u' hu' q hq, hd j v' hv' q hq]
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
    have du := hd i u' hu'
    have dv := hd j v' hv'
    split at h
    · -- folded AND
      rename_i r hr
      rw [except_pure_eq_ok] at h
      subst h
      refine keep _ (fun w hw => ?_)
      cases hw
      rcases fold_cases hr with rfl | rfl | rfl
      exacts [du, dv, fun q hq => by simp at hq]
    · -- a new ancilla
      rw [except_bind_eq_ok] at h
      obtain ⟨⟨pre, pu, pv⟩, hprep, h⟩ := h
      rw [except_pure_eq_ok] at h
      subst h
      have gu := hvals i u' hu'
      have gv := hvals j v' hv'
      obtain ⟨hpq, hperm, hqub, -⟩ := prepare_ok hprep gu.1 gv.1
      obtain ⟨hpu, hpv, hcn⟩ := prepare_wf hprep
      -- atoms of the operands: data below `nInputs`, ancillae below `anc nextAnc`
      have atomD : ∀ q, (q ∈ u'.lin ∨ q ∈ v'.lin) → ∀ d, q = .data d → d < N.nInputs :=
        fun q hq => hq.elim (du q) (dv q)
      have atomA : ∀ q, (q ∈ u'.lin ∨ q ∈ v'.lin) → q ≠ .anc st.nextAnc := by
        rintro q hq rfl
        rcases hq with hq | hq
        · have := gu.2.1 _ hq _ rfl; omega
        · have := gv.2.1 _ hq _ rfl; omega
      have hpre : ∀ g ∈ pre, g.qubitsOk N.nInputs = true := fun g hg =>
        Gate.qubitsOk_of_isPerm (hperm g hg) (fun q hq => atomD q (hqub g hg q hq)) (hcn g hg)
      obtain ⟨hc, hu⟩ := and_blocks_qubitsOk hpre (atomD pu hpu) (atomD pv hpv) hpq
        (atomA pu hpu) (atomA pv hpv)
      refine ⟨vals_push_data hd _ (fun w hw q hq d hdq => ?_), ?_, ?_⟩
      · cases hw
        simp only [List.mem_singleton] at hq
        subst hq
        cases hdq
      · intro blk hblk
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hblk
        rcases hblk with hblk | rfl
        exacts [hcq blk hblk, hc]
      · intro blk hblk
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hblk
        rcases hblk with hblk | rfl
        exacts [huq blk hblk, hu]

/-- Report §9.1.1 (Stage 11a) — `InvQ` after the synthesizer's fold over the first `m` nodes. -/
theorem fold_invQ {N : Network} (hN : N.WF) (mark : Array Bool) :
    ∀ m, m ≤ N.nodes.size → ∀ st,
      (List.range m).foldlM (Oracle.step N mark) ({ vals := #[] } : Oracle.St) = .ok st →
        InvQ N.nInputs st
  | 0, _, st, h => by
    rw [List.range_zero, List.foldlM_nil, except_pure_eq_ok] at h
    subst h
    exact ⟨fun i u hu => by simp at hu, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | m + 1, hm, st, h => by
    rw [List.range_succ, List.foldlM_append, except_bind_eq_ok] at h
    obtain ⟨st₁, h₁, h⟩ := h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    exact step_ok_invQ hN mark (by omega) h (fold_inv mark 0 m (by omega) st₁ h₁)
      (fold_invQ hN mark m (by omega) st₁ h₁)

/-- Report §6.1.1, §9.1.1 — the phase flip passes `qubitsOk` when the data atoms of `P` are in
range. -/
theorem phaseFlip_qubitsOk {nI : ℕ} {pp : Aff} (hD : DataBelow nI pp) :
    ∀ g ∈ Oracle.phaseFlip pp, g.qubitsOk nI = true := by
  rcases hl : pp.lin with _ | ⟨q, l⟩
  · have hpf : Oracle.phaseFlip pp = [] := by unfold Oracle.phaseFlip; rw [hl]
    simp [hpf]
  · set P := Oracle.gather (q :: l) q ++ (if pp.c then [Gate.x q] else []) with hPdef
    have hpf : Oracle.phaseFlip pp = P ++ [Gate.z q] ++ P.reverse := by
      unfold Oracle.phaseFlip
      rw [hl]
    have hqD : ∀ d, q = .data d → d < nI := hD q (by rw [hl]; exact List.mem_cons_self)
    have hP : ∀ g ∈ P, g.qubitsOk nI = true := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · refine Gate.qubitsOk_of_isPerm (gather_isPerm _ _ g hg) (fun w hw => ?_)
          (fun a b he => gather_cnot_ne hg he)
        rcases gather_qubits hg hw with hw | rfl
        exacts [hD w (by rw [hl]; exact hw), hqD]
      · split_ifs at hg
        · simp only [List.mem_singleton] at hg
          subst hg
          cases q <;> simp_all [Gate.qubitsOk, Gate.qubits]
        · simp at hg
    rw [hpf]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact hP g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        cases q <;> simp_all [Gate.qubitsOk, Gate.qubits]
    · exact hP g (List.mem_reverse.mp hg)

/-- Report §9.1.1 — a gate that neither measures nor reads a classical bit. -/
def Gate.quiet : Gate → Bool
  | .measure _ _ | .ifBit _ _ => false
  | _ => true

/-- `X` / `CNOT` gates are quiet. -/
theorem Gate.quiet_of_isPerm {g : Gate} (h : g.isPerm = true) : g.quiet = true := by
  cases g <;> simp_all [Gate.isPerm, Gate.quiet]

/-- Quiet gates satisfy the classical-bit discipline after any written bits. -/
theorem bitsOkFrom_quiet {m : ℕ} {gs : List Gate} (h : ∀ g ∈ gs, g.quiet = true) (W : List ℕ) :
    Circuit.bitsOkFrom m W gs = true := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    simp only [Circuit.bitsOkFrom, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      Bool.and_true]
    cases g <;> simp_all [Gate.quiet, Gate.bitOk]

/-- The compute blocks are quiet: no measurement, no classically controlled gate. -/
theorem cmpBlocks_quiet {rs : List AndRec} (hp : ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true)
    (j : ℕ) : ∀ g ∈ cmpBlocks rs j, g.quiet = true := by
  induction rs generalizing j with
  | nil => simp [cmpBlocks]
  | cons r rs ih =>
    intro g hg
    rw [cmpBlocks, List.mem_append] at hg
    rcases hg with hg | hg
    · have ht : ∀ g ∈ TempLogicalAND r.p r.q (.anc j), g.quiet = true := by
        simp [TempLogicalAND, Gate.quiet]
      simp only [AndRec.cmp, List.mem_append, List.mem_reverse, List.mem_singleton] at hg
      rcases hg with ((hg | rfl) | hg) | hg
      exacts [Gate.quiet_of_isPerm (hp r (by simp) g hg), rfl, ht g hg,
        Gate.quiet_of_isPerm (hp r (by simp) g hg)]
    · exact ih (fun r' hr' => hp r' (by simp [hr'])) (j + 1) g hg

/-- The phase flip is quiet. -/
theorem phaseFlip_quiet (pp : Aff) : ∀ g ∈ Oracle.phaseFlip pp, g.quiet = true := by
  rcases hl : pp.lin with _ | ⟨q, l⟩
  · have hpf : Oracle.phaseFlip pp = [] := by unfold Oracle.phaseFlip; rw [hl]
    simp [hpf]
  · set P := Oracle.gather (q :: l) q ++ (if pp.c then [Gate.x q] else []) with hPdef
    have hpf : Oracle.phaseFlip pp = P ++ [Gate.z q] ++ P.reverse := by
      unfold Oracle.phaseFlip
      rw [hl]
    have hP : ∀ g ∈ P, g.quiet = true := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      exacts [Gate.quiet_of_isPerm (gather_isPerm _ _ g hg),
        Gate.quiet_of_isPerm (polGates_isPerm _ _ g hg)]
    rw [hpf]
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact hP g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        rfl
    · exact hP g (List.mem_reverse.mp hg)

/-- Report §6.2.2, §9.1.1 — the uncompute blocks of `rs`, run in reverse order, measure into the
bits `0, 1, …, |rs| − 1` in that order (each fresh and below `K`), and each `ifBit` reads the bit
just measured. -/
theorem bitsOk_uncBlocks {rs : List AndRec} (hp : ∀ r ∈ rs, ∀ g ∈ r.pre, g.isPerm = true)
    (j K : ℕ) (hK : rs.length ≤ K) :
    Circuit.bitsOkFrom K [] (uncBlocks rs j) = true ∧
      Circuit.written (uncBlocks rs j) = List.range rs.length := by
  induction rs generalizing j with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    obtain ⟨h1, h2⟩ := ih (fun r' hr' => hp r' (by simp [hr'])) (j + 1)
      (by simp at hK; omega)
    have hpr := hp r (by simp)
    have hq : ∀ W, Circuit.bitsOkFrom K W r.pre = true := bitsOkFrom_quiet
      (fun g hg => Gate.quiet_of_isPerm (hpr g hg))
    have hqr : ∀ W, Circuit.bitsOkFrom K W r.pre.reverse = true := bitsOkFrom_quiet
      (fun g hg => Gate.quiet_of_isPerm (hpr g (List.mem_reverse.mp hg)))
    have hw : r.pre.flatMap Gate.writes = [] := written_perm hpr
    have hL : rs.length < K := by simp at hK; omega
    refine ⟨?_, ?_⟩
    · rw [uncBlocks, bitsOkFrom_append_list, h1, Bool.true_and, h2, List.nil_append]
      simp [AndRec.unc, UncomputeTempLogicalAND, bitsOkFrom_append_list, Circuit.bitsOkFrom,
        Gate.bitOk, Gate.writes, Gate.isClifford, Circuit.written, hq, hqr, hw, hL]
    · rw [uncBlocks, Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
        h2, written_unc hpr, List.length_cons, List.range_succ]

/-- Report §6.3.2 (side condition `C.WF` of Lemma 6.3.2), §8.3.4 (Figure 8.1, restoration side),
§9.1.1 (Stage 11a) — **every oracle synthesized from a well-formed network is well formed**: data
qubits below `nInputs` (the `input` atoms, `N.WF`), distinct CNOT / CZ operands (`prepare`, the
`gather` CNOTs, the AND records `p ≠ q`, ancilla atoms below the target), and the classical-bit
discipline (the uncompute blocks measure into `0, 1, …` in execution order). The hypothesis
`N.WF` is needed: `⟨0, #[.input 5], [0]⟩` synthesizes to `Z x[5]` (Stage 9a). -/
theorem synthesizeOracle_WF {N : Network} {C : Circuit} (hN : N.WF)
    (hC : synthesizeOracle N = .ok C) : C.WF := by
  obtain ⟨out, st, pp, hout, hst, hpp, hCeq⟩ := synthesizeOracle_ok hC
  obtain ⟨recs, -, -, hcmp, hunc, hrecs, -⟩ :=
    fold_inv (Oracle.cone N out) 0 N.nodes.size le_rfl st hst
  obtain ⟨hd, hcq, huq⟩ := fold_invQ hN (Oracle.cone N out) N.nodes.size le_rfl st hst
  have hperm := hrecs.isPerm
  have hgates : C.gates = cmpBlocks recs 0 ++ Oracle.phaseFlip pp ++ uncBlocks recs 0 := by
    have h1 := flatten_mapIdx_cmp recs 0
    have h2 := flatten_mapIdx_unc hperm 0
    simp only [Nat.zero_add] at h1 h2
    rw [hCeq, hcmp, hunc, h1, h2]
  have hnb : C.nBits = recs.length := by
    rw [Circuit.nBits, hgates, Circuit.written, List.flatMap_append, List.flatMap_append,
      ← Circuit.written, ← Circuit.written, ← Circuit.written, written_cmpBlocks hperm,
      written_phaseFlip, List.nil_append, List.nil_append, written_uncBlocks_length hperm]
  unfold Circuit.WF Circuit.wf
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro g hg
    rw [hCeq] at hg ⊢
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨blk, hblk, hg⟩ := List.mem_flatten.mp hg
        exact hcq blk hblk g hg
      · exact phaseFlip_qubitsOk (hd out pp hpp) g hg
    · obtain ⟨blk, hblk, hg⟩ := List.mem_flatten.mp hg
      obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hblk
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [Gate.qubitsOk_shiftBits]
      exact huq _ (List.mem_reverse.mp (List.getElem_mem hi)) g' hg'
  · have hw : Circuit.written (cmpBlocks recs 0 ++ Oracle.phaseFlip pp) = [] := by
      rw [Circuit.written, List.flatMap_append, ← Circuit.written, ← Circuit.written,
        written_cmpBlocks hperm, written_phaseFlip]
      rfl
    unfold Circuit.bitsOk
    rw [hnb, hgates, bitsOkFrom_append_list, bitsOkFrom_append_list,
      bitsOkFrom_quiet (cmpBlocks_quiet hperm 0), bitsOkFrom_quiet (phaseFlip_quiet pp), hw]
    simpa using (bitsOk_uncBlocks hperm 0 recs.length le_rfl).1

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
