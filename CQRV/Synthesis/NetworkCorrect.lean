module

public import CQRV.DSL.Scope
public import CQRV.Synthesis.Network

/-!
# CQRV.Synthesis.NetworkCorrect

Report §7.2–7.4 (ℰ as a total compiler on typing derivations), §6.1.2 (the Boolean network),
§5.3.3 (declared trust boundaries), §8.4.1 (what the certificate states); docs/tasks/
STAGE16_TASK.md (Stage 16a) — **the front end proved**: for a scoped typed program (`CQRV.DSL.Scope`),
`toNetwork` succeeds (when there is no `loop … while`), its network is well formed, and its
predicate is the reference evaluator's:

```
toNetwork_succeeds : tp.hasLoop = false → tp.scoped = true → ∃ N, toNetwork tp = .ok N
toNetwork_WF       : toNetwork tp = .ok N → tp.scoped = true → N.WF
toNetwork_pred     : toNetwork tp = .ok N → tp.scoped = true →
                       ∀ x : Fin tp.arity → Bool, N.pred tp.arity x = evalProgram tp x
```

`evalExpr`, `evalProgram`, `ToNetwork.build`, `toNetwork`, `Network.pred`, `Network.wf` are
unchanged (the evaluator is the reference semantics, the builder produces the committed `net`
literals); everything here is an invariant *about* them.

* `ValOk τ v`: the value has the type's shape; `nodeVals` / `nodeVal`: the node values of a node
  array (`Network.values` is `nodeVals N.nodes`), stable under `push` below the old size;
  `WfPrefix nIn ns`: every node of the array satisfies the clause of `Network.wf` at its index.
* `Ext x ns ns'` (the builder only appends): size, stability of node values, `WfPrefix`.
* `Bits x ns bs τ v`: the node indices `bs` carry the bits of `v : τ` (length `τ.width`, indices in
  range, `bs.map (nodeVal ns x) = v.bitsAt τ`, `ValOk τ v`).
* `EnvOk x ns ctx envV envN`: **lookup-based** (shadowing comes for free): every value binding of
  `ctx` is bound in both environments to a value and to its bits; every loop binding to the same
  index `k < m`.
* `build_ok` — correctness given success, by induction on the term, generalizing the context,
  both environments and the node array: `e.scoped ctx = true → EnvOk … → (build e envN).run ns
  = .ok (bs, ns') → Ext x ns ns' ∧ Bits x ns' bs τ (evalExpr e envV)`. It takes no `hasLoop`
  hypothesis: a `loopE` the builder reaches makes it fail, and one it does not reach (a `for` with
  bound 0) is not evaluated either; this is what `toNetwork_pred` needs.
  `build_succeeds` — every `fail` of `build` is excluded by scoping and `ValOk` when the term has
  no `loop`: `e.hasLoop = false → ∃ bs ns', (build e envN).run ns = .ok (bs, ns')` (it uses
  `build_ok` for the lengths and environments of the sub-terms). `build_spec` is both in one
  statement.
* The initial environment: `params_ok` runs the three parameter folds (`ctx`, `evalProgram`,
  `toNetwork`) in lockstep; a `Nat m` parameter needs `testBit_natOfBits` (bit `j` of
  `∑_{i<w} [b i] 2^i` is `b j`), proved by induction on `w` splitting the top summand with
  `Nat.testBit_two_pow_add_eq`, `Nat.testBit_two_pow_add_gt` and `Nat.testBit_lt_two_pow`.
-/

@[expose] public section

namespace CQRV.Synthesis

open CQRV.DSL ToNetwork

/-! ## Values -/

/-- Report §7.1.4 (Stage 16a) — a value has the shape of its type. `Nat m` carries no bound: both
`Val.bitsAt` and the builder read the bits `j < Ty.width (.nat m)` of `k`. -/
def ValOk : Ty → Val → Prop
  | .bool, .bool _ => True
  | .vec m, .vec bs => bs.length = m
  | .nat _, .nat _ => True
  | .unit, .unit => True
  | _, _ => False

theorem ValOk.bitsAt_length {τ : Ty} {v : Val} (h : ValOk τ v) :
    (v.bitsAt τ).length = τ.width := by
  cases τ <;> cases v <;> simp_all [ValOk, Val.bitsAt, Ty.width]

theorem ValOk.bool {v : Val} (h : ValOk .bool v) : ∃ b, v = .bool b := by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | vec _ => exact (h : False).elim
  | nat _ => exact (h : False).elim
  | unit => exact (h : False).elim

theorem ValOk.vec {m : Nat} {v : Val} (h : ValOk (.vec m) v) : ∃ bl, v = .vec bl ∧ bl.length = m := by
  cases v with
  | vec bs => exact ⟨bs, rfl, h⟩
  | bool _ => exact (h : False).elim
  | nat _ => exact (h : False).elim
  | unit => exact (h : False).elim

/-! ## Node values of a node array -/

/-- Report §6.1.2 — one node evaluated on the values of the earlier nodes (the step of
`Network.values`). -/
def nodeStep (x : Nat → Bool) (vs : Array Bool) (v : Node) : Array Bool :=
  vs.push <| match v with
    | .input k => x k
    | .const b => b
    | .not i => !vs.getD i false
    | .and i j => vs.getD i false && vs.getD j false
    | .xor i j => vs.getD i false ^^ vs.getD j false

/-- Report §6.1.2 — the node values of a node array, independent of a `Network`. -/
def nodeVals (ns : Array Node) (x : Nat → Bool) : Array Bool := ns.foldl (nodeStep x) #[]

theorem Network.values_eq_nodeVals (N : Network) (x : Nat → Bool) :
    N.values x = nodeVals N.nodes x := rfl

/-- The value of node `i` (`false` beyond the array, as `Network.eval` reads). -/
def nodeVal (ns : Array Node) (x : Nat → Bool) (i : Nat) : Bool := (nodeVals ns x).getD i false

theorem nodeVals_push (ns : Array Node) (v : Node) (x : Nat → Bool) :
    nodeVals (ns.push v) x = nodeStep x (nodeVals ns x) v := Array.foldl_push

theorem foldl_nodeStep_size (x : Nat → Bool) :
    ∀ (l : List Node) (acc : Array Bool), (l.foldl (nodeStep x) acc).size = acc.size + l.length
  | [], acc => by simp
  | v :: l, acc => by
    rw [List.foldl_cons, foldl_nodeStep_size x l]
    unfold nodeStep
    rw [Array.size_push, List.length_cons]
    omega

theorem nodeVals_size (ns : Array Node) (x : Nat → Bool) : (nodeVals ns x).size = ns.size := by
  rw [nodeVals, ← Array.foldl_toList, foldl_nodeStep_size]
  simp

theorem Array.getD_push' {α : Type} (xs : Array α) (v d : α) (i : Nat) :
    (xs.push v).getD i d = if i = xs.size then v else xs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

/-- Stability: pushing a node does not change the values below the old size. -/
theorem nodeVal_push_lt {ns : Array Node} {i : Nat} (hi : i < ns.size) (v : Node)
    (x : Nat → Bool) : nodeVal (ns.push v) x i = nodeVal ns x i := by
  unfold nodeVal
  rw [nodeVals_push]
  unfold nodeStep
  rw [Array.getD_push', ite_eq_right (by rw [nodeVals_size]; omega)]

theorem nodeVal_push_self (ns : Array Node) (v : Node) (x : Nat → Bool) :
    nodeVal (ns.push v) x ns.size = (match v with
      | .input k => x k
      | .const b => b
      | .not i => !nodeVal ns x i
      | .and i j => nodeVal ns x i && nodeVal ns x j
      | .xor i j => nodeVal ns x i ^^ nodeVal ns x j) := by
  unfold nodeVal
  rw [nodeVals_push]
  unfold nodeStep
  rw [Array.getD_push', ite_eq_left (nodeVals_size ns x).symm]

theorem nodeVal_push_const (ns : Array Node) (b : Bool) (x : Nat → Bool) :
    nodeVal (ns.push (.const b)) x ns.size = b := by rw [nodeVal_push_self]

theorem nodeVal_push_not (ns : Array Node) (i : Nat) (x : Nat → Bool) :
    nodeVal (ns.push (.not i)) x ns.size = !nodeVal ns x i := by rw [nodeVal_push_self]

theorem nodeVal_push_and (ns : Array Node) (i j : Nat) (x : Nat → Bool) :
    nodeVal (ns.push (.and i j)) x ns.size = (nodeVal ns x i && nodeVal ns x j) := by
  rw [nodeVal_push_self]

theorem nodeVal_push_xor (ns : Array Node) (i j : Nat) (x : Nat → Bool) :
    nodeVal (ns.push (.xor i j)) x ns.size = (nodeVal ns x i ^^ nodeVal ns x j) := by
  rw [nodeVal_push_self]

/-! ## Well-formed prefixes -/

/-- Report §6.1.2, §6.3.2 — the clause of `Network.wf` for the node at index `k`. -/
def NodeOk (nIn k : Nat) : Node → Prop
  | .input i => i < nIn
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k
  | .xor i j => i < k ∧ j < k

/-- Report §6.1.2, §6.3.2 — every node of the array satisfies its clause of `Network.wf`. -/
def WfPrefix (nIn : Nat) (ns : Array Node) : Prop :=
  ∀ (k : Nat) (h : k < ns.size), NodeOk nIn k ns[k]

theorem WfPrefix.push {nIn : Nat} {ns : Array Node} (h : WfPrefix nIn ns) {v : Node}
    (hv : NodeOk nIn ns.size v) : WfPrefix nIn (ns.push v) := by
  intro k hk
  rw [Array.getElem_push]
  split
  · exact h k ‹_›
  · have hks : k = ns.size := by rw [Array.size_push] at hk; omega
    subst hks
    exact hv

/-- Report §6.1.2, §6.3.2 — a well-formed prefix with outputs among its nodes is a well-formed
network. -/
theorem WfPrefix.wf {nIn : Nat} {ns : Array Node} (h : WfPrefix nIn ns) {outs : List Nat}
    (houts : ∀ o ∈ outs, o < ns.size) : (Network.mk nIn ns outs).wf = true := by
  unfold Network.wf
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun k hk => ?_, fun o ho => by simpa using houts o ho⟩
  rw [Array.getElem?_eq_getElem hk]
  have := h k hk
  cases hv : ns[k] <;> simp_all [NodeOk]

/-- Report §6.1.2 — the input nodes `input 0, …, input (n − 1)`, as `toNetwork` lays them out. -/
def inputNodes (n : Nat) : Array Node := (Array.range n).map .input

theorem inputNodes_size (n : Nat) : (inputNodes n).size = n := by simp [inputNodes]

theorem inputNodes_wfPrefix (n : Nat) : WfPrefix n (inputNodes n) := by
  intro k hk
  have hk' : k < n := by rw [inputNodes_size] at hk; exact hk
  simp only [inputNodes, Array.getElem_map, Array.getElem_range]
  exact hk'

theorem foldl_inputs (x : Nat → Bool) (m : Nat) :
    (((List.range m).map Node.input).foldl (nodeStep x) #[]).size = m ∧
      ∀ i < m, (((List.range m).map Node.input).foldl (nodeStep x) #[]).getD i false = x i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, nodeStep,
      Array.size_push, ih.1, true_and]
    intro i hi
    rw [Array.getD_push', ih.1]
    split
    · rename_i h
      rw [h]
    · exact ih.2 i (by omega)

/-- Report §6.1.2 — input node `k < n` evaluates to input bit `k`. -/
theorem nodeVal_inputNodes (n : Nat) (x : Nat → Bool) {k : Nat} (hk : k < n) :
    nodeVal (inputNodes n) x k = x k := by
  unfold nodeVal nodeVals inputNodes
  rw [← Array.foldl_toList, Array.toList_map, Array.toList_range]
  exact (foldl_inputs x n).2 k hk

/-! ## Extension of the node array, bits of a value, the environment invariant -/

/-- The builder only appends: the array grows, old node values are stable, well-formed prefixes
stay well formed (for every `nIn`: the builder never pushes an `input`). -/
def Ext (x : Nat → Bool) (ns ns' : Array Node) : Prop :=
  ns.size ≤ ns'.size ∧ (∀ i, i < ns.size → nodeVal ns' x i = nodeVal ns x i) ∧
    ∀ nIn, WfPrefix nIn ns → WfPrefix nIn ns'

theorem Ext.refl (x : Nat → Bool) (ns : Array Node) : Ext x ns ns :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h⟩

theorem Ext.trans {x : Nat → Bool} {ns₁ ns₂ ns₃ : Array Node} (h₁ : Ext x ns₁ ns₂)
    (h₂ : Ext x ns₂ ns₃) : Ext x ns₁ ns₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1,
   fun i hi => (h₂.2.1 i (Nat.lt_of_lt_of_le hi h₁.1)).trans (h₁.2.1 i hi),
   fun nIn h => h₂.2.2 nIn (h₁.2.2 nIn h)⟩

theorem Ext.push {x : Nat → Bool} {ns : Array Node} (v : Node)
    (hv : ∀ nIn, NodeOk nIn ns.size v) : Ext x ns (ns.push v) :=
  ⟨by simp only [Array.size_push]; omega, fun i hi => nodeVal_push_lt hi v x,
   fun nIn h => h.push (hv nIn)⟩

/-- Report §6.1.2, §7.2 — the node indices `bs` carry the bits of the value `v : τ`. -/
def Bits (x : Nat → Bool) (ns : Array Node) (bs : List Nat) (τ : Ty) (v : Val) : Prop :=
  bs.length = τ.width ∧ (∀ i ∈ bs, i < ns.size) ∧ bs.map (nodeVal ns x) = v.bitsAt τ ∧ ValOk τ v

theorem Bits.mono {x : Nat → Bool} {ns ns' : Array Node} {bs : List Nat} {τ : Ty} {v : Val}
    (hext : Ext x ns ns') (h : Bits x ns bs τ v) : Bits x ns' bs τ v :=
  ⟨h.1, fun i hi => Nat.lt_of_lt_of_le (h.2.1 i hi) hext.1, by
    rw [← h.2.2.1]
    exact List.map_congr_left fun i hi => hext.2.1 i (h.2.1 i hi), h.2.2.2⟩

theorem Bits.single {x : Nat → Bool} {ns : Array Node} {bs : List Nat} {v : Val}
    (h : Bits x ns bs .bool v) : ∃ i, bs = [i] :=
  List.length_eq_one_iff.mp h.1

theorem Bits.bool {x : Nat → Bool} {ns : Array Node} {i : Nat} {v : Val}
    (h : Bits x ns [i] .bool v) : i < ns.size ∧ nodeVal ns x i = v.toBool :=
  ⟨h.2.1 i (List.mem_singleton.mpr rfl), by
    have := h.2.2.1
    simp only [List.map_cons, List.map_nil, Val.bitsAt, List.cons.injEq, and_true] at this
    exact this⟩

theorem Bits.bool_intro {x : Nat → Bool} {ns : Array Node} {i : Nat} (hi : i < ns.size)
    (b : Bool) (h : nodeVal ns x i = b) : Bits x ns [i] .bool (.bool b) :=
  ⟨rfl, fun j hj => by rw [List.mem_singleton] at hj; subst hj; exact hi,
   by simp [Val.bitsAt, Val.toBool, h], trivial⟩

/-- Report §7.2 (Stage 16a) — the environment invariant, lookup-based: a value binding of the
context is bound in the evaluator's environment to a value and in the builder's to its bits; a
loop binding to the same index `k < m` in both. -/
def EnvOk (x : Nat → Bool) (ns : Array Node) (ctx : Ctx) (envV : List (String × Val))
    (envN : List (String × NVal)) : Prop :=
  (∀ y τ, ctx.lookup y = some (.val τ) →
    ∃ v bs, envV.lookup y = some v ∧ envN.lookup y = some (.bits bs) ∧ Bits x ns bs τ v) ∧
  (∀ y m, ctx.lookup y = some (.loop m) →
    ∃ k, k < m ∧ envV.lookup y = some (.nat k) ∧ envN.lookup y = some (.index k))

theorem EnvOk.nil (x : Nat → Bool) (ns : Array Node) : EnvOk x ns [] [] [] :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem EnvOk.mono {x : Nat → Bool} {ns ns' : Array Node} {ctx : Ctx} {envV : List (String × Val)}
    {envN : List (String × NVal)} (hext : Ext x ns ns') (h : EnvOk x ns ctx envV envN) :
    EnvOk x ns' ctx envV envN :=
  ⟨fun y τ hy =>
    let ⟨v, bs, h1, h2, h3⟩ := h.1 y τ hy
    ⟨v, bs, h1, h2, h3.mono hext⟩, h.2⟩

theorem lookup_cons_ne {β : Type} {y y' : String} (h : y' ≠ y) (b : β) (l : List (String × β)) :
    ((y, b) :: l).lookup y' = l.lookup y' := by
  simp [List.lookup_cons, beq_eq_false_iff_ne.mpr h]

theorem EnvOk.consVal {x : Nat → Bool} {ns : Array Node} {ctx : Ctx} {envV : List (String × Val)}
    {envN : List (String × NVal)} (h : EnvOk x ns ctx envV envN) {y : String} {τ : Ty} {v : Val}
    {bs : List Nat} (hb : Bits x ns bs τ v) :
    EnvOk x ns ((y, .val τ) :: ctx) ((y, v) :: envV) ((y, .bits bs) :: envN) := by
  refine ⟨fun y' τ' hy => ?_, fun y' m hy => ?_⟩
  · by_cases hyy : y' = y
    · subst hyy
      rw [List.lookup_cons_self] at hy
      cases hy
      exact ⟨v, bs, List.lookup_cons_self, List.lookup_cons_self, hb⟩
    · rw [lookup_cons_ne hyy] at hy
      obtain ⟨v', bs', h1, h2, h3⟩ := h.1 y' τ' hy
      exact ⟨v', bs', by rw [lookup_cons_ne hyy]; exact h1, by rw [lookup_cons_ne hyy]; exact h2, h3⟩
  · by_cases hyy : y' = y
    · subst hyy
      rw [List.lookup_cons_self] at hy
      cases hy
    · rw [lookup_cons_ne hyy] at hy
      obtain ⟨k, hk, h1, h2⟩ := h.2 y' m hy
      exact ⟨k, hk, by rw [lookup_cons_ne hyy]; exact h1, by rw [lookup_cons_ne hyy]; exact h2⟩

theorem EnvOk.consLoop {x : Nat → Bool} {ns : Array Node} {ctx : Ctx} {envV : List (String × Val)}
    {envN : List (String × NVal)} (h : EnvOk x ns ctx envV envN) {y : String} {m k : Nat}
    (hk : k < m) : EnvOk x ns ((y, .loop m) :: ctx) ((y, .nat k) :: envV) ((y, .index k) :: envN) := by
  refine ⟨fun y' τ' hy => ?_, fun y' m' hy => ?_⟩
  · by_cases hyy : y' = y
    · subst hyy
      rw [List.lookup_cons_self] at hy
      cases hy
    · rw [lookup_cons_ne hyy] at hy
      obtain ⟨v', bs', h1, h2, h3⟩ := h.1 y' τ' hy
      exact ⟨v', bs', by rw [lookup_cons_ne hyy]; exact h1, by rw [lookup_cons_ne hyy]; exact h2, h3⟩
  · by_cases hyy : y' = y
    · subst hyy
      rw [List.lookup_cons_self] at hy
      cases hy
      exact ⟨k, hk, List.lookup_cons_self, List.lookup_cons_self⟩
    · rw [lookup_cons_ne hyy] at hy
      obtain ⟨k', hk', h1, h2⟩ := h.2 y' m' hy
      exact ⟨k', hk', by rw [lookup_cons_ne hyy]; exact h1, by rw [lookup_cons_ne hyy]; exact h2⟩

/-! ## The builder monad on `.ok` results -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem run_bind_ok {α β : Type} {m : NM α} {f : α → NM β} {ns : Array Node}
    {r : β × Array Node} :
    (m >>= f).run ns = .ok r ↔ ∃ a ns₁, m.run ns = .ok (a, ns₁) ∧ (f a).run ns₁ = .ok r := by
  rw [StateT.run_bind]
  constructor
  · intro h
    obtain ⟨⟨a, ns₁⟩, h1, h2⟩ := except_bind_ok.mp h
    exact ⟨a, ns₁, h1, h2⟩
  · rintro ⟨a, ns₁, h1, h2⟩
    exact except_bind_ok.mpr ⟨(a, ns₁), h1, h2⟩

theorem run_fail_ne {α : Type} (c : Code) (msg : String) (ns : Array Node) (r : α × Array Node) :
    (fail c msg : NM α).run ns ≠ .ok r := fun h => by cases h

/-- `mapM` of constant pushes (`natBits`): fresh consecutive nodes carrying the constants. -/
theorem mapM_const_spec (x : Nat → Bool) (c : Nat → Bool) :
    ∀ (js : List Nat) (ns : Array Node), ∃ bs ns',
      ((js.mapM fun j => push (.const (c j))).run ns = .ok (bs, ns')) ∧ Ext x ns ns' ∧
        bs.length = js.length ∧ (∀ i ∈ bs, i < ns'.size) ∧ bs.map (nodeVal ns' x) = js.map c
  | [], ns => ⟨[], ns, rfl, Ext.refl x ns, rfl, fun _ h => by simp at h, rfl⟩
  | j :: js, ns => by
    obtain ⟨bs, ns', hrun, hext, hlen, hlt, hmap⟩ :=
      mapM_const_spec x c js (ns.push (.const (c j)))
    have hpush : Ext x ns (ns.push (.const (c j))) := Ext.push _ fun _ => trivial
    refine ⟨ns.size :: bs, ns', ?_, hpush.trans hext, by simp [hlen], ?_, ?_⟩
    · rw [List.mapM_cons]
      exact run_bind_ok.mpr ⟨ns.size, ns.push (.const (c j)), rfl,
        run_bind_ok.mpr ⟨bs, ns', hrun, rfl⟩⟩
    · intro i hi
      rw [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact Nat.lt_of_lt_of_le (by simp only [Array.size_push]; omega) hext.1
      · exact hlt i hi
    · rw [List.map_cons, List.map_cons, hmap, hext.2.1 ns.size (by simp only [Array.size_push]; omega),
        nodeVal_push_const]

/-- `b ⊕ (c ∧ (a ⊕ b)) = if c then a else b` (the Stage 3 mux rule). -/
theorem mux_bool (c a b : Bool) : (b ^^ (c && (a ^^ b))) = (if c then a else b) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `¬(¬a ∧ ¬b) = a ∨ b` (De Morgan, the `or` of the builder). -/
theorem or_bool (a b : Bool) : (!(!a && !b)) = (a || b) := by
  cases a <;> cases b <;> rfl

/-- Report §6.1.2 — one mux: three pushes, the new node holds `if c then a else b`. -/
theorem mux_spec (x : Nat → Bool) {ns : Array Node} {c a b : Nat} (hc : c < ns.size)
    (ha : a < ns.size) (hb : b < ns.size) :
    ∃ r ns', (mux c a b).run ns = .ok (r, ns') ∧ Ext x ns ns' ∧ r < ns'.size ∧
      nodeVal ns' x r = (if nodeVal ns x c then nodeVal ns x a else nodeVal ns x b) := by
  have h1 : Ext x ns (ns.push (.xor a b)) := Ext.push _ fun _ => ⟨ha, hb⟩
  have h2 : Ext x (ns.push (.xor a b)) ((ns.push (.xor a b)).push (.and c ns.size)) :=
    Ext.push _ fun _ => ⟨Nat.lt_of_lt_of_le hc h1.1, by simp only [Array.size_push]; omega⟩
  have h3 : Ext x ((ns.push (.xor a b)).push (.and c ns.size))
      (((ns.push (.xor a b)).push (.and c ns.size)).push (.xor b (ns.push (.xor a b)).size)) :=
    Ext.push _ fun _ => ⟨Nat.lt_of_lt_of_le hb (h1.trans h2).1, by simp only [Array.size_push]; omega⟩
  refine ⟨_, _, rfl, (h1.trans h2).trans h3, by simp only [Array.size_push]; omega, ?_⟩
  rw [nodeVal_push_xor, nodeVal_push_and, nodeVal_push_lt (Nat.lt_of_lt_of_le hb h1.1),
    nodeVal_push_lt hb, nodeVal_push_lt hc, nodeVal_push_xor, mux_bool]

/-- `mapM` of muxes over index pairs (the `ite` of the builder), relative to a reference array
`ns` whose values are stable in the current array `ns₀`. -/
theorem mapM_mux_spec (x : Nat → Bool) {ns : Array Node} {c : Nat} (hc : c < ns.size)
    (f : Nat × Nat → NM Nat) (hf : ∀ p, f p = mux c p.1 p.2) :
    ∀ (ps : List (Nat × Nat)) (ns₀ : Array Node), Ext x ns ns₀ →
      (∀ p ∈ ps, p.1 < ns.size ∧ p.2 < ns.size) →
      ∃ bs ns', ((ps.mapM f).run ns₀ = .ok (bs, ns')) ∧ Ext x ns₀ ns' ∧ bs.length = ps.length ∧
        (∀ i ∈ bs, i < ns'.size) ∧
        bs.map (nodeVal ns' x) =
          ps.map fun p => if nodeVal ns x c then nodeVal ns x p.1 else nodeVal ns x p.2
  | [], ns₀, _, _ => ⟨[], ns₀, rfl, Ext.refl x ns₀, rfl, fun _ h => by simp at h, rfl⟩
  | p :: ps, ns₀, hext₀, hmem => by
    have hp := hmem p (List.mem_cons_self ..)
    obtain ⟨r, ns₁, hrun₁, hext₁, hr, hval⟩ := mux_spec x (Nat.lt_of_lt_of_le hc hext₀.1)
      (Nat.lt_of_lt_of_le hp.1 hext₀.1) (Nat.lt_of_lt_of_le hp.2 hext₀.1)
    obtain ⟨bs, ns', hrun, hext, hlen, hlt, hmap⟩ := mapM_mux_spec x hc f hf ps ns₁
      (hext₀.trans hext₁) (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
    refine ⟨r :: bs, ns', ?_, hext₁.trans hext, by simp [hlen], ?_, ?_⟩
    · rw [List.mapM_cons]
      exact run_bind_ok.mpr ⟨r, ns₁, by rw [hf]; exact hrun₁, run_bind_ok.mpr ⟨bs, ns', hrun, rfl⟩⟩
    · intro i hi
      rw [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact Nat.lt_of_lt_of_le hr hext.1
      · exact hlt i hi
    · rw [List.map_cons, List.map_cons, hmap, hext.2.1 r hr, hval, hext₀.2.1 c hc,
        hext₀.2.1 p.1 hp.1, hext₀.2.1 p.2 hp.2]

theorem map_zip_ite {α β : Type} (f : α → β) :
    ∀ (as bs : List α), as.length = bs.length → ∀ (c : Bool),
      (as.zip bs).map (fun p => if c then f p.1 else f p.2) = if c then as.map f else bs.map f
  | [], [], _, c => by cases c <;> rfl
  | a :: as, b :: bs, h, c => by
    rw [List.zip_cons_cons, List.map_cons, map_zip_ite f as bs (by simpa using h) c]
    cases c <;> rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

/-! ## The main lemma: correctness of `build` given success -/

/-- The `forE` fold of the builder against the `forE` fold of the evaluator (correctness given
success); `IH` is the induction hypothesis for the body. -/
theorem fold_ok (x : Nat → Bool) {σ : Ty} (body : TExpr σ) (i acc : String) (ctx : Ctx) (n : Nat)
    (IH : ∀ (ctx' : Ctx) (envV : List (String × Val)) (envN : List (String × NVal))
      (ns : Array Node) (bs : List Nat) (ns' : Array Node), body.scoped ctx' = true →
      EnvOk x ns ctx' envV envN → (build body envN).run ns = .ok (bs, ns') →
      Ext x ns ns' ∧ Bits x ns' bs σ (evalExpr body envV))
    (hsc : body.scoped ((acc, .val σ) :: (i, .loop n) :: ctx) = true) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < n) → ∀ (envV : List (String × Val))
      (envN : List (String × NVal)) (v : Val) (bs : List Nat) (ns ns' : Array Node) (bs' : List Nat),
      EnvOk x ns ctx envV envN → Bits x ns bs σ v →
      (ks.foldlM (fun v k => build body ((acc, .bits v) :: (i, .index k) :: envN)) bs).run ns =
        .ok (bs', ns') →
      Ext x ns ns' ∧
        Bits x ns' bs' σ (ks.foldl (fun v k => evalExpr body ((acc, v) :: (i, .nat k) :: envV)) v)
  | [], _, envV, envN, v, bs, ns, ns', bs', _, hb, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨Ext.refl x ns, hb⟩
  | k :: ks, hks, envV, envN, v, bs, ns, ns', bs', henv, hb, h => by
    obtain ⟨bs₁, ns₁, h₁, h⟩ := run_bind_ok.mp h
    have hk : k < n := hks k (List.mem_cons_self ..)
    obtain ⟨hext, hb₁⟩ := IH _ _ _ _ _ _ hsc ((henv.consLoop hk).consVal hb) h₁
    rw [List.foldl_cons]
    obtain ⟨hext', hb'⟩ := fold_ok x body i acc ctx n IH hsc ks
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) envV envN _ bs₁ ns₁ ns' bs'
      (henv.mono hext) hb₁ h
    exact ⟨hext.trans hext', hb'⟩

/-- Report §7.2, §6.1.2 (Stage 16a) — **correctness of the builder given success**: on a scoped
term, under the environment invariant, a successful `build` extends the node array (`Ext`) and
returns the bits of the evaluator's value (`Bits`). No `hasLoop` hypothesis: a reached `loopE`
fails. -/
theorem build_ok (x : Nat → Bool) : ∀ {τ : Ty} (e : TExpr τ) (ctx : Ctx)
    (envV : List (String × Val)) (envN : List (String × NVal)) (ns : Array Node) (bs : List Nat)
    (ns' : Array Node), e.scoped ctx = true → EnvOk x ns ctx envV envN →
    (build e envN).run ns = .ok (bs, ns') → Ext x ns ns' ∧ Bits x ns' bs τ (evalExpr e envV) := by
  intro τ e
  induction e with
  | var y τ =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped] at hsc
    split at hsc
    · rename_i σ hy
      have hστ : σ = τ := beq_iff_eq.mp hsc
      subst hστ
      obtain ⟨v, vbs, hV, hN, hb⟩ := henv.1 y σ hy
      simp only [build, hN] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨Ext.refl x ns, ?_⟩
      simp only [evalExpr, hV, Option.getD_some]
      exact hb
    · rename_i m hy
      have hτ : τ = .nat m := beq_iff_eq.mp hsc
      subst hτ
      obtain ⟨k, _, hV, hN⟩ := henv.2 y m hy
      simp only [build, hN] at h
      obtain ⟨cbs, cns, hrun, hext, hlen, hlt, hmap⟩ := mapM_const_spec x
        (fun j => (k >>> j) % 2 == 1) (List.range (Ty.width (.nat m))) ns
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hrun.symm.trans h))
      refine ⟨hext, ?_⟩
      simp only [evalExpr, hV, Option.getD_some]
      exact ⟨by rw [hlen, List.length_range], hlt, hmap, trivial⟩
    · simp at hsc
  | lit b =>
    intro ctx envV envN ns bs ns' _ _ h
    obtain ⟨i, ns₁, hp, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    refine ⟨Ext.push (.const b) fun _ => trivial, ?_⟩
    simp only [evalExpr]
    exact Bits.bool_intro (by simp only [Array.size_push]; omega) b (nodeVal_push_const ns b x)
  | not a iha =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped] at hsc
    obtain ⟨bsa, nsa, ha, h⟩ := run_bind_ok.mp h
    obtain ⟨hexta, hba⟩ := iha _ _ _ _ _ _ hsc henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨k, nsk, hp, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hi := hba.bool
    refine ⟨hexta.trans (Ext.push (.not i) fun _ => hi.1), ?_⟩
    simp only [evalExpr]
    refine Bits.bool_intro (by simp only [Array.size_push]; omega) _ ?_
    rw [nodeVal_push_not, hi.2]
  | and a b iha ihb =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨bsa, nsa, ha, h⟩ := run_bind_ok.mp h
    obtain ⟨hexta, hba⟩ := iha _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb, h⟩ := run_bind_ok.mp h
    obtain ⟨hextb, hbb⟩ := ihb _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    obtain ⟨k, nsk, hp, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hi := hba.bool
    have hj := hbb.bool
    refine ⟨(hexta.trans hextb).trans
      (Ext.push (.and i j) fun _ => ⟨Nat.lt_of_lt_of_le hi.1 hextb.1, hj.1⟩), ?_⟩
    simp only [evalExpr]
    refine Bits.bool_intro (by simp only [Array.size_push]; omega) _ ?_
    rw [nodeVal_push_and, hextb.2.1 i hi.1, hi.2, hj.2]
  | or a b iha ihb =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨bsa, nsa, ha, h⟩ := run_bind_ok.mp h
    obtain ⟨hexta, hba⟩ := iha _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb, h⟩ := run_bind_ok.mp h
    obtain ⟨hextb, hbb⟩ := ihb _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    obtain ⟨ni, ns₁, hp₁, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp₁)
    obtain ⟨nj, ns₂, hp₂, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp₂)
    obtain ⟨c, ns₃, hp₃, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp₃)
    obtain ⟨k, ns₄, hp₄, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp₄)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hi := hba.bool
    have hj := hbb.bool
    have hi' : i < nsb.size := Nat.lt_of_lt_of_le hi.1 hextb.1
    have e₁ : Ext x nsb (nsb.push (.not i)) := Ext.push _ fun _ => hi'
    have e₂ : Ext x (nsb.push (.not i)) ((nsb.push (.not i)).push (.not j)) :=
      Ext.push _ fun _ => Nat.lt_of_lt_of_le hj.1 e₁.1
    have e₃ : Ext x ((nsb.push (.not i)).push (.not j))
        (((nsb.push (.not i)).push (.not j)).push (.and nsb.size (nsb.push (.not i)).size)) :=
      Ext.push _ fun _ => ⟨Nat.lt_of_lt_of_le
        (show nsb.size < (nsb.push (.not i)).size by simp only [Array.size_push]; omega) e₂.1,
        by simp only [Array.size_push]; omega⟩
    have e₄ : Ext x (((nsb.push (.not i)).push (.not j)).push (.and nsb.size (nsb.push (.not i)).size))
        ((((nsb.push (.not i)).push (.not j)).push (.and nsb.size (nsb.push (.not i)).size)).push
          (.not ((nsb.push (.not i)).push (.not j)).size)) :=
      Ext.push _ fun _ => by simp only [NodeOk, Array.size_push]; omega
    refine ⟨(((hexta.trans hextb).trans e₁).trans e₂).trans (e₃.trans e₄), ?_⟩
    simp only [evalExpr]
    refine Bits.bool_intro (by simp only [Array.size_push]; omega) _ ?_
    rw [nodeVal_push_not, nodeVal_push_and, nodeVal_push_lt (by simp only [Array.size_push]; omega),
      nodeVal_push_not, nodeVal_push_not, nodeVal_push_lt hj.1, hextb.2.1 i hi.1, hi.2, hj.2,
      or_bool]
  | xor a b iha ihb =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨bsa, nsa, ha, h⟩ := run_bind_ok.mp h
    obtain ⟨hexta, hba⟩ := iha _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb, h⟩ := run_bind_ok.mp h
    obtain ⟨hextb, hbb⟩ := ihb _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    obtain ⟨k, nsk, hp, h⟩ := run_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    have hi := hba.bool
    have hj := hbb.bool
    refine ⟨(hexta.trans hextb).trans
      (Ext.push (.xor i j) fun _ => ⟨Nat.lt_of_lt_of_le hi.1 hextb.1, hj.1⟩), ?_⟩
    simp only [evalExpr]
    refine Bits.bool_intro (by simp only [Array.size_push]; omega) _ ?_
    rw [nodeVal_push_xor, hextb.2.1 i hi.1, hi.2, hj.2]
  | idx v k ihv =>
    intro ctx envV envN ns bs ns' hsc henv h
    cases k with
    | lit kf =>
      simp only [TExpr.scoped] at hsc
      obtain ⟨bsv, nsv, hv, h⟩ := run_bind_ok.mp h
      obtain ⟨hextv, hbv⟩ := ihv _ _ _ _ _ _ hsc henv hv
      obtain ⟨pos, ns₂, hpos, h⟩ := run_bind_ok.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hpos)
      obtain ⟨bl, hev, hbl⟩ := hbv.2.2.2.vec
      have hlt : kf.val < bsv.length := by rw [hbv.1]; exact kf.isLt
      dsimp only at h
      rw [List.getElem?_eq_getElem hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨hextv, ?_⟩
      simp only [evalExpr, hev]
      refine Bits.bool_intro (hbv.2.1 _ (List.getElem_mem hlt)) _ ?_
      have hmap := hbv.2.2.1
      rw [hev] at hmap
      simp only [Val.bitsAt] at hmap
      rw [List.getD_eq_getElem?_getD, ← hmap, List.getElem?_map, List.getElem?_eq_getElem hlt]
      rfl
    | loopVar y m hm =>
      simp only [TExpr.scoped, Bool.and_eq_true] at hsc
      obtain ⟨hy, hscv⟩ := hsc
      have hy' : ctx.lookup y = some (.loop m) := beq_iff_eq.mp hy
      obtain ⟨kk, hkk, hV, hN⟩ := henv.2 y m hy'
      obtain ⟨bsv, nsv, hv, h⟩ := run_bind_ok.mp h
      obtain ⟨hextv, hbv⟩ := ihv _ _ _ _ _ _ hscv henv hv
      simp only [hN] at h
      obtain ⟨pos, ns₂, hpos, h⟩ := run_bind_ok.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hpos)
      obtain ⟨bl, hev, hbl⟩ := hbv.2.2.2.vec
      have hlt : kk < bsv.length := by rw [hbv.1]; exact Nat.lt_of_lt_of_le hkk hm
      simp only [List.getElem?_eq_getElem hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨hextv, ?_⟩
      simp only [evalExpr, hev, hV]
      refine Bits.bool_intro (hbv.2.1 _ (List.getElem_mem hlt)) _ ?_
      have hmap := hbv.2.2.1
      rw [hev] at hmap
      simp only [Val.bitsAt] at hmap
      rw [List.getD_eq_getElem?_getD, ← hmap, List.getElem?_map, List.getElem?_eq_getElem hlt]
      rfl
  | ite c a b ihc iha ihb =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨⟨hscc, hsca⟩, hscb⟩ := hsc
    obtain ⟨bsc, nsc, hc, h⟩ := run_bind_ok.mp h
    obtain ⟨hextc, hbc⟩ := ihc _ _ _ _ _ _ hscc henv hc
    obtain ⟨ic, rfl⟩ := hbc.single
    obtain ⟨bsa, nsa, ha, h⟩ := run_bind_ok.mp h
    obtain ⟨hexta, hba⟩ := iha _ _ _ _ _ _ hsca (henv.mono hextc) ha
    obtain ⟨bsb, nsb, hb, h⟩ := run_bind_ok.mp h
    obtain ⟨hextb, hbb⟩ := ihb _ _ _ _ _ _ hscb (henv.mono (hextc.trans hexta)) hb
    have hcv := hbc.bool
    have hic : ic < nsb.size := Nat.lt_of_lt_of_le hcv.1 (hexta.trans hextb).1
    have hab : bsa.length = bsb.length := hba.1.trans hbb.1.symm
    have hmem : ∀ p ∈ bsa.zip bsb, p.1 < nsb.size ∧ p.2 < nsb.size := by
      rintro ⟨p1, p2⟩ hp
      obtain ⟨h1, h2⟩ := List.of_mem_zip hp
      exact ⟨Nat.lt_of_lt_of_le (hba.2.1 _ h1) hextb.1, hbb.2.1 _ h2⟩
    obtain ⟨rbs, rns, hrun, hext, hlen, hlt, hmap⟩ := mapM_mux_spec x hic _ (fun _ => rfl)
      (bsa.zip bsb) nsb (Ext.refl x nsb) hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hrun.symm.trans h))
    have hcv' : nodeVal nsb x ic = (evalExpr c envV).toBool := by
      rw [hextb.2.1 ic (Nat.lt_of_lt_of_le hcv.1 hexta.1), hexta.2.1 ic hcv.1, hcv.2]
    refine ⟨hextc.trans (hexta.trans (hextb.trans hext)), ?_, hlt, ?_, ?_⟩
    · rw [hlen, List.length_zip, hab, Nat.min_self, hbb.1]
    · rw [hmap, hcv', map_zip_ite (nodeVal nsb x) bsa bsb hab]
      simp only [evalExpr]
      cases (evalExpr c envV).toBool
      · simpa using hbb.2.2.1
      · simpa using (hba.mono hextb).2.2.1
    · simp only [evalExpr]
      cases (evalExpr c envV).toBool
      · simpa using hbb.2.2.2
      · simpa using hba.2.2.2
  | letE y e₁ e₂ ih₁ ih₂ =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨bs₁, ns₁, h₁, h⟩ := run_bind_ok.mp h
    obtain ⟨hext₁, hb₁⟩ := ih₁ _ _ _ _ _ _ hsc.1 henv h₁
    obtain ⟨hext₂, hb₂⟩ := ih₂ _ _ _ _ _ _ hsc.2 ((henv.mono hext₁).consVal hb₁) h
    exact ⟨hext₁.trans hext₂, hb₂⟩
  | forE i n acc init body ih₀ ihb =>
    intro ctx envV envN ns bs ns' hsc henv h
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    obtain ⟨bs₀, ns₀, h₀, h⟩ := run_bind_ok.mp h
    obtain ⟨hext₀, hb₀⟩ := ih₀ _ _ _ _ _ _ hsc.1 henv h₀
    obtain ⟨hext, hb⟩ := fold_ok x body i acc ctx n ihb hsc.2 (List.range n)
      (fun k hk => List.mem_range.mp hk) envV envN _ bs₀ ns₀ ns' bs (henv.mono hext₀) hb₀ h
    exact ⟨hext₀.trans hext, hb⟩
  | loopE acc init cond body _ _ _ =>
    intro ctx envV envN ns bs ns' _ _ h
    cases h

/-! ## Success -/

/-- The `forE` fold of the builder succeeds (and is correct) when the body does. -/
theorem fold_ex (x : Nat → Bool) {σ : Ty} (body : TExpr σ) (i acc : String) (ctx : Ctx) (n : Nat)
    (IH : ∀ (ctx' : Ctx) (envV : List (String × Val)) (envN : List (String × NVal))
      (ns : Array Node), body.scoped ctx' = true → EnvOk x ns ctx' envV envN →
      ∃ bs ns', (build body envN).run ns = .ok (bs, ns') ∧ Ext x ns ns' ∧
        Bits x ns' bs σ (evalExpr body envV))
    (hsc : body.scoped ((acc, .val σ) :: (i, .loop n) :: ctx) = true) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < n) → ∀ (envV : List (String × Val))
      (envN : List (String × NVal)) (v : Val) (bs : List Nat) (ns : Array Node),
      EnvOk x ns ctx envV envN → Bits x ns bs σ v →
      ∃ bs' ns', (ks.foldlM (fun v k => build body ((acc, .bits v) :: (i, .index k) :: envN)) bs).run ns
          = .ok (bs', ns') ∧ Ext x ns ns' ∧
        Bits x ns' bs' σ (ks.foldl (fun v k => evalExpr body ((acc, v) :: (i, .nat k) :: envV)) v)
  | [], _, envV, envN, v, bs, ns, _, hb => ⟨bs, ns, rfl, Ext.refl x ns, hb⟩
  | k :: ks, hks, envV, envN, v, bs, ns, henv, hb => by
    obtain ⟨bs₁, ns₁, h₁, hext, hb₁⟩ :=
      IH _ _ _ _ hsc ((henv.consLoop (hks k (List.mem_cons_self ..))).consVal hb)
    obtain ⟨bs', ns', h, hext', hb'⟩ := fold_ex x body i acc ctx n IH hsc ks
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) envV envN _ bs₁ ns₁ (henv.mono hext) hb₁
    refine ⟨bs', ns', ?_, hext.trans hext', by rw [List.foldl_cons]; exact hb'⟩
    rw [List.foldlM_cons]
    exact run_bind_ok.mpr ⟨bs₁, ns₁, h₁, h⟩

/-- Report §7.2, §6.1.2 (Stage 16a) — **the builder succeeds** on a scoped term without
`loop … while`: every `fail` of `build` is excluded (a `not`/`and`/`or`/`xor`/`if` on a value of
width 1, `idx` in range, every variable bound with bits or as a fixed loop index). -/
theorem build_succeeds (x : Nat → Bool) : ∀ {τ : Ty} (e : TExpr τ) (ctx : Ctx)
    (envV : List (String × Val)) (envN : List (String × NVal)) (ns : Array Node),
    e.scoped ctx = true → e.hasLoop = false → EnvOk x ns ctx envV envN →
    ∃ bs ns', (build e envN).run ns = .ok (bs, ns') := by
  intro τ e
  induction e with
  | var y τ =>
    intro ctx envV envN ns hsc _ henv
    simp only [TExpr.scoped] at hsc
    split at hsc
    · rename_i σ hy
      obtain ⟨v, vbs, -, hN, -⟩ := henv.1 y σ hy
      exact ⟨vbs, ns, by simp only [build, hN]; rfl⟩
    · rename_i m hy
      have hτ : τ = .nat m := beq_iff_eq.mp hsc
      subst hτ
      obtain ⟨k, -, -, hN⟩ := henv.2 y m hy
      obtain ⟨cbs, cns, hrun, -⟩ := mapM_const_spec x (fun j => (k >>> j) % 2 == 1)
        (List.range (Ty.width (.nat m))) ns
      exact ⟨cbs, cns, by simp only [build, hN]; exact hrun⟩
    · simp at hsc
  | lit b => intro ctx envV envN ns _ _ _; exact ⟨_, _, rfl⟩
  | not a ih =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped] at hsc
    simp only [TExpr.hasLoop] at hl
    obtain ⟨bsa, nsa, ha⟩ := ih _ _ _ _ hsc hl henv
    obtain ⟨-, hba⟩ := build_ok x a _ _ _ _ _ _ hsc henv ha
    obtain ⟨i, rfl⟩ := hba.single
    exact ⟨_, _, run_bind_ok.mpr ⟨[i], nsa, ha, rfl⟩⟩
  | and a b iha ihb =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨bsa, nsa, ha⟩ := iha _ _ _ _ hsc.1 hl.1 henv
    obtain ⟨hexta, hba⟩ := build_ok x a _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb⟩ := ihb _ _ _ _ hsc.2 hl.2 (henv.mono hexta)
    obtain ⟨-, hbb⟩ := build_ok x b _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    exact ⟨_, _, run_bind_ok.mpr ⟨[i], nsa, ha, run_bind_ok.mpr ⟨[j], nsb, hb, rfl⟩⟩⟩
  | or a b iha ihb =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨bsa, nsa, ha⟩ := iha _ _ _ _ hsc.1 hl.1 henv
    obtain ⟨hexta, hba⟩ := build_ok x a _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb⟩ := ihb _ _ _ _ hsc.2 hl.2 (henv.mono hexta)
    obtain ⟨-, hbb⟩ := build_ok x b _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    exact ⟨_, _, run_bind_ok.mpr ⟨[i], nsa, ha, run_bind_ok.mpr ⟨[j], nsb, hb, rfl⟩⟩⟩
  | xor a b iha ihb =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨bsa, nsa, ha⟩ := iha _ _ _ _ hsc.1 hl.1 henv
    obtain ⟨hexta, hba⟩ := build_ok x a _ _ _ _ _ _ hsc.1 henv ha
    obtain ⟨i, rfl⟩ := hba.single
    obtain ⟨bsb, nsb, hb⟩ := ihb _ _ _ _ hsc.2 hl.2 (henv.mono hexta)
    obtain ⟨-, hbb⟩ := build_ok x b _ _ _ _ _ _ hsc.2 (henv.mono hexta) hb
    obtain ⟨j, rfl⟩ := hbb.single
    exact ⟨_, _, run_bind_ok.mpr ⟨[i], nsa, ha, run_bind_ok.mpr ⟨[j], nsb, hb, rfl⟩⟩⟩
  | idx v k ihv =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.hasLoop] at hl
    cases k with
    | lit kf =>
      simp only [TExpr.scoped] at hsc
      obtain ⟨bsv, nsv, hv⟩ := ihv _ _ _ _ hsc hl henv
      obtain ⟨-, hbv⟩ := build_ok x v _ _ _ _ _ _ hsc henv hv
      have hlt : kf.val < bsv.length := by rw [hbv.1]; exact kf.isLt
      refine ⟨[bsv[kf.val]], nsv, run_bind_ok.mpr ⟨bsv, nsv, hv, run_bind_ok.mpr ⟨kf.val, nsv, rfl, ?_⟩⟩⟩
      try dsimp only
      rw [List.getElem?_eq_getElem hlt]
      rfl
    | loopVar y m hm =>
      simp only [TExpr.scoped, Bool.and_eq_true] at hsc
      obtain ⟨hy, hscv⟩ := hsc
      obtain ⟨kk, hkk, -, hN⟩ := henv.2 y m (beq_iff_eq.mp hy)
      obtain ⟨bsv, nsv, hv⟩ := ihv _ _ _ _ hscv hl henv
      obtain ⟨-, hbv⟩ := build_ok x v _ _ _ _ _ _ hscv henv hv
      have hlt : kk < bsv.length := by rw [hbv.1]; exact Nat.lt_of_lt_of_le hkk hm
      refine ⟨[bsv[kk]], nsv, run_bind_ok.mpr ⟨bsv, nsv, hv, ?_⟩⟩
      simp only [hN]
      exact run_bind_ok.mpr ⟨kk, nsv, rfl, by simp only [List.getElem?_eq_getElem hlt]; rfl⟩
  | ite c a b ihc iha ihb =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨⟨hscc, hsca⟩, hscb⟩ := hsc
    obtain ⟨⟨hlc, hla⟩, hlb⟩ := hl
    obtain ⟨bsc, nsc, hc⟩ := ihc _ _ _ _ hscc hlc henv
    obtain ⟨hextc, hbc⟩ := build_ok x c _ _ _ _ _ _ hscc henv hc
    obtain ⟨ic, rfl⟩ := hbc.single
    obtain ⟨bsa, nsa, ha⟩ := iha _ _ _ _ hsca hla (henv.mono hextc)
    obtain ⟨hexta, hba⟩ := build_ok x a _ _ _ _ _ _ hsca (henv.mono hextc) ha
    obtain ⟨bsb, nsb, hb⟩ := ihb _ _ _ _ hscb hlb (henv.mono (hextc.trans hexta))
    obtain ⟨hextb, hbb⟩ := build_ok x b _ _ _ _ _ _ hscb (henv.mono (hextc.trans hexta)) hb
    have hcv := hbc.bool
    have hic : ic < nsb.size := Nat.lt_of_lt_of_le hcv.1 (hexta.trans hextb).1
    have hmem : ∀ p ∈ bsa.zip bsb, p.1 < nsb.size ∧ p.2 < nsb.size := by
      rintro ⟨p1, p2⟩ hp
      obtain ⟨h1, h2⟩ := List.of_mem_zip hp
      exact ⟨Nat.lt_of_lt_of_le (hba.2.1 _ h1) hextb.1, hbb.2.1 _ h2⟩
    obtain ⟨rbs, rns, hrun, -⟩ := mapM_mux_spec x hic (fun p => mux ic p.1 p.2) (fun _ => rfl)
      (bsa.zip bsb) nsb (Ext.refl x nsb) hmem
    exact ⟨rbs, rns, run_bind_ok.mpr ⟨[ic], nsc, hc,
      run_bind_ok.mpr ⟨bsa, nsa, ha, run_bind_ok.mpr ⟨bsb, nsb, hb, hrun⟩⟩⟩⟩
  | letE y e₁ e₂ ih₁ ih₂ =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨bs₁, ns₁, h₁⟩ := ih₁ _ _ _ _ hsc.1 hl.1 henv
    obtain ⟨hext₁, hb₁⟩ := build_ok x e₁ _ _ _ _ _ _ hsc.1 henv h₁
    obtain ⟨bs₂, ns₂, h₂⟩ := ih₂ _ _ _ _ hsc.2 hl.2 ((henv.mono hext₁).consVal hb₁)
    exact ⟨bs₂, ns₂, run_bind_ok.mpr ⟨bs₁, ns₁, h₁, h₂⟩⟩
  | forE i n acc init body ih₀ ihb =>
    intro ctx envV envN ns hsc hl henv
    simp only [TExpr.scoped, Bool.and_eq_true] at hsc
    simp only [TExpr.hasLoop, Bool.or_eq_false_iff] at hl
    obtain ⟨bs₀, ns₀, h₀⟩ := ih₀ _ _ _ _ hsc.1 hl.1 henv
    obtain ⟨hext₀, hb₀⟩ := build_ok x init _ _ _ _ _ _ hsc.1 henv h₀
    have IH : ∀ (ctx' : Ctx) (envV : List (String × Val)) (envN : List (String × NVal))
        (ns : Array Node), body.scoped ctx' = true → EnvOk x ns ctx' envV envN →
        ∃ bs ns', (build body envN).run ns = .ok (bs, ns') ∧ Ext x ns ns' ∧
          Bits x ns' bs _ (evalExpr body envV) := fun ctx' envV envN ns hs he =>
      let ⟨bs, ns', h⟩ := ihb ctx' envV envN ns hs hl.2 he
      ⟨bs, ns', h, build_ok x body ctx' envV envN ns bs ns' hs he h⟩
    obtain ⟨bs', ns', h, -, -⟩ := fold_ex x body i acc ctx n IH hsc.2 (List.range n)
      (fun k hk => List.mem_range.mp hk) envV envN _ bs₀ ns₀ (henv.mono hext₀) hb₀
    exact ⟨bs', ns', run_bind_ok.mpr ⟨bs₀, ns₀, h₀, h⟩⟩
  | loopE acc init cond body _ _ _ =>
    intro ctx envV envN ns _ hl _
    simp [TExpr.hasLoop] at hl

/-- Report §7.2, §6.1.2 (Stage 16a) — **`build_spec`: success and correctness in one statement**
(`build_succeeds` and `build_ok`). -/
theorem build_spec (x : Nat → Bool) {τ : Ty} (e : TExpr τ) (ctx : Ctx)
    (envV : List (String × Val)) (envN : List (String × NVal)) (ns : Array Node)
    (hsc : e.scoped ctx = true) (hl : e.hasLoop = false) (henv : EnvOk x ns ctx envV envN) :
    ∃ bs ns', (build e envN).run ns = .ok (bs, ns') ∧ Ext x ns ns' ∧
      Bits x ns' bs τ (evalExpr e envV) :=
  let ⟨bs, ns', h⟩ := build_succeeds x e ctx envV envN ns hsc hl henv
  ⟨bs, ns', h, build_ok x e ctx envV envN ns bs ns' hsc henv h⟩

/-! ## The initial environment -/

/-- `∑_{i<w} [b i] · 2^i`, the number `Val.ofInput` reads for a `Nat m` parameter. -/
def natOfBits (b : Nat → Bool) (w : Nat) : Nat :=
  ((List.range w).map fun j => if b j then 2 ^ j else 0).sum

theorem natOfBits_succ (b : Nat → Bool) (w : Nat) :
    natOfBits b (w + 1) = natOfBits b w + (if b w then 2 ^ w else 0) := by
  unfold natOfBits
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem natOfBits_lt (b : Nat → Bool) : ∀ w, natOfBits b w < 2 ^ w
  | 0 => by simp [natOfBits]
  | w + 1 => by
    rw [natOfBits_succ, Nat.pow_succ]
    have := natOfBits_lt b w
    split <;> omega

/-- Report §7.2.2 — bit `j` of `∑_{i<w} [b i] 2^i` is `b j` (`j < w`): induction on `w`, the top
summand through `Nat.testBit_two_pow_add_eq` / `_gt` and `Nat.testBit_lt_two_pow`. -/
theorem testBit_natOfBits (b : Nat → Bool) : ∀ w j, j < w → (natOfBits b w).testBit j = b j
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | w + 1, j, h => by
    rw [natOfBits_succ]
    have hlt := natOfBits_lt b w
    by_cases hj : j = w
    · subst hj
      split
      · rename_i hb
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hb]
        rfl
      · rename_i hb
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
        simp only [Bool.not_eq_true] at hb
        exact hb.symm
    · have hj' : j < w := by omega
      split
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hj', testBit_natOfBits b w j hj']
      · rw [Nat.add_zero, testBit_natOfBits b w j hj']

/-- `(k >>> j) % 2 == 1` (the builder's and the evaluator's bit `j`) is `k.testBit j`. -/
theorem shift_mod_eq_testBit (k j : Nat) : ((k >>> j) % 2 == 1) = k.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ j) with h | h <;> simp [h]

/-- Report §7.2.2 — a parameter of type `τ` at offset `o`: the input nodes `o, …, o + width − 1`
carry the bits of `Val.ofInput bit o τ`. -/
theorem param_bits (x : Nat → Bool) (n : Nat) (bit : Nat → Bool)
    (hbit : ∀ k, k < n → nodeVal (inputNodes n) x k = bit k) (o : Nat) (τ : Ty)
    (ho : o + τ.width ≤ n) :
    Bits x (inputNodes n) (List.range' o τ.width) τ (Val.ofInput bit o τ) := by
  cases τ with
  | bool =>
    refine ⟨List.length_range', ?_, ?_, trivial⟩
    · intro i hi
      rw [List.mem_range'] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      rw [inputNodes_size]
      simp only [Ty.width] at ht ho
      omega
    · show [nodeVal (inputNodes n) x o] = [bit o]
      rw [hbit o (by simp only [Ty.width] at ho; omega)]
  | vec m =>
    refine ⟨List.length_range', ?_, ?_, by simp [Val.ofInput, ValOk]⟩
    · intro i hi
      rw [List.mem_range'] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      rw [inputNodes_size]
      simp only [Ty.width] at ht ho
      omega
    · show (List.range' o m).map (nodeVal (inputNodes n) x) = (List.range m).map fun j => bit (o + j)
      rw [List.range'_eq_map_range, List.map_map]
      refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      show nodeVal (inputNodes n) x (o + j) = bit (o + j)
      exact hbit _ (by simp only [Ty.width] at ho; omega)
  | nat m =>
    refine ⟨List.length_range', ?_, ?_, trivial⟩
    · intro i hi
      rw [List.mem_range'] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      rw [inputNodes_size]
      omega
    · show (List.range' o (Ty.width (.nat m))).map (nodeVal (inputNodes n) x) =
        (List.range (Ty.width (.nat m))).map fun j =>
          ((natOfBits (fun j => bit (o + j)) (Ty.width (.nat m)) >>> j) % 2 == 1)
      rw [List.range'_eq_map_range, List.map_map]
      refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      show nodeVal (inputNodes n) x (o + j) = _
      rw [hbit _ (by omega), shift_mod_eq_testBit, testBit_natOfBits _ _ _ hj]
  | unit =>
    exact ⟨rfl, fun i hi => by simp [Ty.width] at hi, rfl, trivial⟩

/-- Report §7.2.2 (Stage 16a) — the three parameter folds (`TypedProgram.ctx`, `evalProgram`,
`toNetwork`) in lockstep keep `EnvOk` on the input nodes. -/
theorem params_ok (x : Nat → Bool) (n : Nat) (bit : Nat → Bool)
    (hbit : ∀ k, k < n → nodeVal (inputNodes n) x k = bit k) :
    ∀ (ps : List (String × Ty)) (o : Nat) (ctx : Ctx) (envV : List (String × Val))
      (envN : List (String × NVal)),
      o + (ps.map (·.2.width)).sum ≤ n → EnvOk x (inputNodes n) ctx envV envN →
      EnvOk x (inputNodes n)
        (ps.foldl (fun (o, ctx) (p, τ) => (o + τ.width, (p, Scope.val τ) :: ctx)) (o, ctx)).2
        (ps.foldl (fun (o, env) (p, τ) => (o + τ.width, (p, Val.ofInput bit o τ) :: env))
          (o, envV)).2
        (ps.foldl (fun (o, env) (x, τ) =>
          (o + τ.width, (x, NVal.bits (List.range' o τ.width)) :: env)) (o, envN)).2
  | [], _, _, _, _, _, h => h
  | (p, τ) :: ps, o, ctx, envV, envN, hle, h => by
    simp only [List.map_cons, List.sum_cons] at hle
    exact params_ok x n bit hbit ps (o + τ.width) _ _ _ (by omega)
      (h.consVal (param_bits x n bit hbit o τ (by omega)))

/-- The input nodes of a program (`toNetwork`). -/
def _root_.CQRV.DSL.TypedProgram.inputs (tp : TypedProgram) : Array Node := inputNodes tp.arity

/-- The builder's initial environment (`toNetwork`). -/
def _root_.CQRV.DSL.TypedProgram.envN (tp : TypedProgram) : List (String × NVal) :=
  (tp.params.foldl (fun (o, env) (x, τ) =>
    (o + τ.width, (x, NVal.bits (List.range' o τ.width)) :: env)) (0, [])).2

/-- The evaluator's initial environment on the input bits `bit` (`evalProgram`). -/
def _root_.CQRV.DSL.TypedProgram.envV (tp : TypedProgram) (bit : Nat → Bool) : List (String × Val) :=
  (tp.params.foldl (fun (o, env) (p, τ) => (o + τ.width, (p, Val.ofInput bit o τ) :: env))
    (0, [])).2

theorem envOk_params (x : Nat → Bool) (tp : TypedProgram) (bit : Nat → Bool)
    (hbit : ∀ k, k < tp.arity → nodeVal (inputNodes tp.arity) x k = bit k) :
    EnvOk x tp.inputs tp.ctx (tp.envV bit) tp.envN :=
  params_ok x tp.arity bit hbit tp.params 0 [] [] [] (Nat.le_of_eq (Nat.zero_add _))
    (EnvOk.nil x _)

/-! ## The theorems -/

/-- `toNetwork` is the builder's run on the input nodes, wrapped. -/
theorem toNetwork_eq (tp : TypedProgram) :
    toNetwork tp = ((build tp.body tp.envN).run tp.inputs >>= fun r =>
      pure ⟨tp.arity, r.2, r.1⟩) := rfl

/-- `evalProgram` is the evaluator on the initial environment of the input bits. -/
theorem evalProgram_eq (tp : TypedProgram) {n : Nat} (x : Fin n → Bool) :
    evalProgram tp x = ((evalExpr tp.body
      (tp.envV fun k => if h : k < n then x ⟨k, h⟩ else false)).bitsAt tp.ret).headD false := rfl

theorem toNetwork_ok {tp : TypedProgram} {N : Network} (h : toNetwork tp = .ok N) :
    ∃ outs nodes, (build tp.body tp.envN).run tp.inputs = .ok (outs, nodes) ∧
      N = ⟨tp.arity, nodes, outs⟩ := by
  rw [toNetwork_eq] at h
  obtain ⟨⟨outs, nodes⟩, hrun, hr⟩ := except_bind_ok.mp h
  exact ⟨outs, nodes, hrun, (Except.ok.inj hr).symm⟩

/-- Report §7.2.2 — the network of a program has `tp.arity` inputs. -/
theorem toNetwork_nInputs {tp : TypedProgram} {N : Network} (h : toNetwork tp = .ok N) :
    N.nInputs = tp.arity := by
  obtain ⟨_, _, _, rfl⟩ := toNetwork_ok h
  rfl

/-- Report §7.2, §6.1.2 (Stage 16a) — **`toNetwork` succeeds** on a scoped program without
`loop … while`. -/
theorem toNetwork_succeeds (tp : TypedProgram) (hl : tp.hasLoop = false) (hsc : tp.scoped = true) :
    ∃ N, toNetwork tp = .ok N := by
  obtain ⟨outs, nodes, hrun⟩ := build_succeeds (fun _ => false) tp.body tp.ctx
    (tp.envV fun _ => false) tp.envN tp.inputs hsc hl
    (envOk_params _ tp _ fun k hk => nodeVal_inputNodes _ _ hk)
  exact ⟨⟨tp.arity, nodes, outs⟩, by rw [toNetwork_eq]; exact except_bind_ok.mpr ⟨_, hrun, rfl⟩⟩

/-- Report §6.1.2, §6.3.2 (Stage 16a) — **the network of a scoped program is well formed**
(the side condition of `synthesizeOracle_WF` and `synthesizeOracle_succeeds`). -/
theorem toNetwork_WF (tp : TypedProgram) (N : Network) (hN : toNetwork tp = .ok N)
    (hsc : tp.scoped = true) : N.WF := by
  obtain ⟨outs, nodes, hrun, rfl⟩ := toNetwork_ok hN
  obtain ⟨hext, hbits⟩ := build_ok (fun _ => false) tp.body tp.ctx (tp.envV fun _ => false)
    tp.envN tp.inputs outs nodes hsc (envOk_params _ tp _ fun k hk => nodeVal_inputNodes _ _ hk)
    hrun
  exact hext.2.2 tp.arity (inputNodes_wfPrefix tp.arity) |>.wf hbits.2.1

/-- Report §7.2–7.4, §5.3.3, §8.4.1 (Stage 16a) — **the front end is correct**: the predicate of
the network of a scoped program is the reference evaluator's, on every input assignment (both
read `false` beyond `n` and take the first output bit). No `hasLoop` hypothesis: a reached
`loopE` makes `toNetwork` fail, an unreached one is not evaluated either. -/
theorem toNetwork_pred (tp : TypedProgram) (N : Network) (hN : toNetwork tp = .ok N)
    (hsc : tp.scoped = true) :
    ∀ x : Fin tp.arity → Bool, N.pred tp.arity x = evalProgram tp x := by
  intro x
  obtain ⟨outs, nodes, hrun, rfl⟩ := toNetwork_ok hN
  obtain ⟨-, hbits⟩ := build_ok (fun k => if h : k < tp.arity then x ⟨k, h⟩ else false) tp.body
    tp.ctx (tp.envV fun k => if h : k < tp.arity then x ⟨k, h⟩ else false) tp.envN tp.inputs outs
    nodes hsc (envOk_params _ tp _ fun k hk => nodeVal_inputNodes _ _ hk) hrun
  rw [evalProgram_eq, ← hbits.2.2.1]
  rfl

end CQRV.Synthesis

end
