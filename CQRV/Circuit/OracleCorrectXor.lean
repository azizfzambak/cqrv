module

public import CQRV.Circuit.OracleBlocks

/-!
# CQRV.Circuit.OracleCorrectXor

Report §6.1.2 (in-place XOR: CNOTs onto an operand qubit, no T, no ancilla), §6.3.2
(Lemma 6.3.2), §7.3.2 (`if` via the mux `b ⊕ (c ∧ (a ⊕ b))`) — the XOR part of the proof of
Lemma 6.3.2 on basis vectors (Stage 9a, items 1–3):

* `permRun` — the basis action of a list of `X` / `CNOT` gates; `perm_kraus` (every Kraus
  operator maps `|s⟩` to `|permRun gs s⟩`), `permRun_reverse` (the reversed list undoes it:
  every such gate is an involution — proved, not assumed), `permRun_set_comm` /
  `get_permRun_of_avoid` (a qubit no gate touches is left alone);
* item 1 — `permRun_gather`: for distinct atoms `S` with pivot `p ∈ S` in range, `gather S p`
  maps `s` to `s[p ↦ ⊕_{q ∈ S} q(s)]`; with `permRun_reverse`, `(gather S p)ᴿ` undoes it;
* item 3 — `xorL_symDiff`: the insertion-sort `symDiff` of Stage 8b is the XOR of linear parts
  (`Aff.eval_symDiff`), `symDiff_nodup`, `mem_symDiff`;
* item 2 — `prepare_ok`: after `pre`, qubit `pu` holds `u.eval s` and `pv` holds `v.eval s`
  (both cases of `pu ∈ v.lin`, and the `X` polarity), only `pu`, `pv` change; `pu ≠ pv`;
  `pre` consists of `X`/`CNOT` gates on atoms of `u` and `v`.

The synthesizer is unchanged.
-/

@[expose] public section

namespace CQRV

open CQRV.Synthesis

/-! ## Atom semantics -/

/-- Report §6.1.2, §6.3.2 — the value of an affine form on a basis state: the XOR of its atoms
(each read on its home qubit) and its constant. -/
def Synthesis.Aff.eval {n a : ℕ} (u : Aff) (s : Reg n × Reg a) : Bool :=
  u.lin.foldr (fun q b => q.get s ^^ b) u.c

/-- Report §6.1.2 — the XOR of the qubits `L` on a basis state. -/
def xorL {n a : ℕ} (L : List Qubit) (s : Reg n × Reg a) : Bool :=
  L.foldr (fun q b => q.get s ^^ b) false

variable {n a : ℕ}

theorem xorL_nil (s : Reg n × Reg a) : xorL [] s = false := rfl

theorem xorL_cons (q : Qubit) (L : List Qubit) (s : Reg n × Reg a) :
    xorL (q :: L) s = (q.get s ^^ xorL L s) := rfl

theorem Synthesis.Aff.eval_eq_xorL (u : Aff) (s : Reg n × Reg a) :
    u.eval s = (xorL u.lin s ^^ u.c) := by
  obtain ⟨lin, c⟩ := u
  simp only [Aff.eval, xorL]
  induction lin with
  | nil => simp
  | cons q l ih => simp only [List.foldr_cons, ih, Bool.xor_assoc]

theorem xorL_append (L₁ L₂ : List Qubit) (s : Reg n × Reg a) :
    xorL (L₁ ++ L₂) s = (xorL L₁ s ^^ xorL L₂ s) := by
  induction L₁ with
  | nil => simp [xorL_nil]
  | cons q l ih => rw [List.cons_append, xorL_cons, xorL_cons, ih, Bool.xor_assoc]

theorem xorL_perm {L₁ L₂ : List Qubit} (h : L₁.Perm L₂) (s : Reg n × Reg a) :
    xorL L₁ s = xorL L₂ s := by
  induction h with
  | nil => rfl
  | cons q _ ih => rw [xorL_cons, xorL_cons, ih]
  | swap q₁ q₂ l => rw [xorL_cons, xorL_cons, xorL_cons, xorL_cons, Bool.xor_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- The XOR over `L` splits along a filter. -/
theorem xorL_filter_split (f : Qubit → Bool) (L : List Qubit) (s : Reg n × Reg a) :
    xorL L s = (xorL (L.filter f) s ^^ xorL (L.filter (fun q => !f q)) s) := by
  induction L with
  | nil => rfl
  | cons q l ih =>
    rw [xorL_cons, ih]
    cases hf : f q <;> simp [hf, xorL_cons, Bool.xor_left_comm]

theorem xorL_erase {p : Qubit} {L : List Qubit} (hp : p ∈ L) (s : Reg n × Reg a) :
    xorL L s = (p.get s ^^ xorL (L.erase p) s) :=
  xorL_perm (List.perm_cons_erase hp) s

/-- For distinct atoms with `p ∈ S`: `⊕ S = p ⊕ ⊕ (S \ {p})`, the second sum being the controls
of `gather S p`. -/
theorem xorL_filter_ne {p : Qubit} {S : List Qubit} (hnd : S.Nodup) (hp : p ∈ S)
    (s : Reg n × Reg a) : xorL S s = (p.get s ^^ xorL (S.filter (· != p)) s) := by
  rw [xorL_erase hp s, List.Nodup.erase_eq_filter hnd]

theorem xorL_set_of_not_mem {p : Qubit} {L : List Qubit} (hp : p ∉ L) (v : Bool)
    (s : Reg n × Reg a) : xorL L (p.set v s) = xorL L s := by
  induction L with
  | nil => rfl
  | cons q l ih =>
    have hqp : q ≠ p := fun e => hp (e ▸ List.mem_cons_self)
    rw [xorL_cons, xorL_cons, Qubit.get_set_ne hqp, ih (fun h => hp (List.mem_cons_of_mem _ h))]

/-! ## Permutation gates (`X`, `CNOT`) on basis vectors -/

/-- Report §6.1.2 — the gates of `prepare` and of the phase flip's gather: `X` and `CNOT`. -/
def Gate.isPerm : Gate → Bool
  | .x _ | .cnot _ _ => true
  | _ => false

/-- Report §6.1.2, §9.1.1 — the basis permutation of an `X` or `CNOT` gate (a `CNOT` with a
repeated operand is the identity, as in `gateU`); other gates: the identity (not used). -/
def Gate.basisPerm (g : Gate) (s : Reg n × Reg a) : Reg n × Reg a :=
  match g with
  | .x q => q.flip s
  | .cnot c₁ t₁ => if c₁ = t₁ then s else cnotPerm n a c₁ t₁ s
  | _ => s

/-- Report §6.1.2 — the basis action of a list of `X` / `CNOT` gates (first gate first). -/
def permRun : List Gate → Reg n × Reg a → Reg n × Reg a
  | [], s => s
  | g :: gs, s => permRun gs (g.basisPerm s)

theorem permRun_append (gs₁ gs₂ : List Gate) (s : Reg n × Reg a) :
    permRun (gs₁ ++ gs₂) s = permRun gs₂ (permRun gs₁ s) := by
  induction gs₁ generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem Gate.basisPerm_involutive {g : Gate} (hg : g.isPerm = true) (s : Reg n × Reg a) :
    g.basisPerm (g.basisPerm s) = s := by
  cases g with
  | x q => exact Qubit.flip_involutive q s
  | cnot c₁ t₁ =>
    by_cases hct : c₁ = t₁
    · simp [Gate.basisPerm, hct]
    · simp only [Gate.basisPerm, hct, ↓reduceIte]
      exact cnotPerm_involutive n a hct s
  | _ => simp [Gate.isPerm] at hg

/-- Report §6.1.2 (items 1, 2) — the reversed list of `X` / `CNOT` gates undoes the list on
basis states: every such gate is an involution. This is the `preᴿ ∘ pre = id` of `prepare`
and the `(gather S p)ᴿ` of the phase flip, proved for any order of the gates. -/
theorem permRun_reverse {gs : List Gate} (h : ∀ g ∈ gs, g.isPerm = true) (s : Reg n × Reg a) :
    permRun gs.reverse (permRun gs s) = s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.reverse_cons, permRun_append,
      show permRun (g :: gs) s = permRun gs (g.basisPerm s) from rfl,
      ih (fun g' hg' => h g' (by simp [hg']))]
    exact Gate.basisPerm_involutive (h g (by simp)) s

theorem Gate.get_basisPerm_of_not_mem {g : Gate} {w : Qubit} (hw : w ∉ g.qubits)
    (s : Reg n × Reg a) : w.get (g.basisPerm s) = w.get s := by
  cases g with
  | x q =>
    have hne : w ≠ q := fun e => hw (by simp [Gate.qubits, e])
    exact Qubit.get_flip_ne hne s
  | cnot c₁ t₁ =>
    have hne : w ≠ t₁ := fun e => hw (by simp [Gate.qubits, e])
    simp only [Gate.basisPerm]
    split_ifs
    · rfl
    · unfold cnotPerm
      split_ifs
      · exact Qubit.get_flip_ne hne s
      · rfl
  | _ => rfl

theorem Qubit.flip_set_comm {q w : Qubit} (hqw : q ≠ w) (v : Bool) (s : Reg n × Reg a) :
    q.flip (w.set v s) = w.set v (q.flip s) := by
  rw [Qubit.flip, Qubit.flip, Qubit.get_set_ne hqw, Qubit.set_comm hqw]

theorem Gate.basisPerm_set_comm {g : Gate} {w : Qubit} (hw : w ∉ g.qubits) (v : Bool)
    (s : Reg n × Reg a) : g.basisPerm (w.set v s) = w.set v (g.basisPerm s) := by
  cases g with
  | x q =>
    have hne : q ≠ w := fun e => hw (by simp [Gate.qubits, e])
    exact Qubit.flip_set_comm hne v s
  | cnot c₁ t₁ =>
    have hc : c₁ ≠ w := fun e => hw (by simp [Gate.qubits, e])
    have ht : t₁ ≠ w := fun e => hw (by simp [Gate.qubits, e])
    simp only [Gate.basisPerm]
    split_ifs
    · rfl
    · unfold cnotPerm
      rw [Qubit.get_set_ne hc]
      split_ifs
      · exact Qubit.flip_set_comm ht v s
      · rfl
  | _ => rfl

/-- A qubit that no gate of `gs` touches keeps its value. -/
theorem get_permRun_of_avoid {gs : List Gate} {w : Qubit} (hw : ∀ g ∈ gs, w ∉ g.qubits)
    (s : Reg n × Reg a) : w.get (permRun gs s) = w.get s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [permRun, ih (fun g' hg' => hw g' (by simp [hg'])),
      Gate.get_basisPerm_of_not_mem (hw g (by simp))]

/-- Setting a qubit that no gate of `gs` touches commutes with `gs`. -/
theorem permRun_set_comm {gs : List Gate} {w : Qubit} (hw : ∀ g ∈ gs, w ∉ g.qubits) (v : Bool)
    (s : Reg n × Reg a) : permRun gs (w.set v s) = w.set v (permRun gs s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [permRun, permRun, Gate.basisPerm_set_comm (hw g (by simp)),
      ih (fun g' hg' => hw g' (by simp [hg']))]

section Kraus

open Matrix

variable (nb : ℕ) (c : Fin nb → Bool)

/-- Report §6.1.2, §9.1.1 — a list of `X` / `CNOT` gates acts, in every branch, as its basis
permutation. -/
theorem perm_kraus {gs : List Gate} (h : ∀ g ∈ gs, g.isPerm = true) (s : Reg n × Reg a) :
    krausOps n a nb gs c *ᵥ basisVec s = basisVec (permRun gs s) := by
  induction gs generalizing s with
  | nil => rw [krausOps_nil, Matrix.one_mulVec]; rfl
  | cons g gs ih =>
    rw [krausOps_cons_mulVec, permRun, ← ih (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    have hg := h g (by simp)
    cases g with
    | x q => exact x_basis n a q s
    | cnot c₁ t₁ =>
      change gateU n a _ *ᵥ _ = _
      by_cases hct : c₁ = t₁
      · simp [gateU, hct, Gate.basisPerm]
      · rw [cnot_basis n a hct]
        simp [Gate.basisPerm, hct]
    | _ => simp [Gate.isPerm] at hg

end Kraus

/-! ## Item 1 — `gather` on basis vectors -/

/-- CNOTs from the controls `L` (none equal to `p`) onto `p`: `p` accumulates their XOR. -/
theorem permRun_cnots {p : Qubit} (hp : p.inRange n a = true) :
    ∀ (L : List Qubit), (∀ q ∈ L, q ≠ p) → ∀ s : Reg n × Reg a,
      permRun (L.map fun q => Gate.cnot q p) s = p.set (p.get s ^^ xorL L s) s
  | [], _, s => by simp [permRun, xorL_nil, Qubit.set_get]
  | q :: L, hL, s => by
    have hqp : q ≠ p := hL q (by simp)
    have h1 : (Gate.cnot q p).basisPerm s = p.set (p.get s ^^ q.get s) s := by
      simp only [Gate.basisPerm, hqp, ↓reduceIte, cnotPerm, Qubit.flip]
      cases q.get s
      · simp [Qubit.set_get]
      · simp
    rw [List.map_cons, permRun, h1, permRun_cnots hp L (fun q' hq' => hL q' (by simp [hq'])),
      Qubit.get_set_self _ hp, Qubit.set_set,
      xorL_set_of_not_mem (fun h => hL p (by simp [h]) rfl), xorL_cons, Bool.xor_assoc]

/-- Report §6.1.2 (item 1) — for distinct atoms `S` with pivot `p ∈ S` in range, `gather S p`
maps `|s⟩` to `|s[p ↦ ⊕_{q ∈ S} q(s)]⟩`; every other qubit is unchanged. Its reverse undoes it
(`permRun_reverse`, `gather_isPerm`). -/
theorem permRun_gather {S : List Qubit} {p : Qubit} (hnd : S.Nodup) (hpS : p ∈ S)
    (hp : p.inRange n a = true) (s : Reg n × Reg a) :
    permRun (Oracle.gather S p) s = p.set (xorL S s) s := by
  rw [Oracle.gather, permRun_cnots hp _ (fun q hq => by simpa using (List.mem_filter.mp hq).2),
    ← xorL_filter_ne hnd hpS]

theorem gather_isPerm (S : List Qubit) (p : Qubit) : ∀ g ∈ Oracle.gather S p, g.isPerm = true := by
  intro g hg
  simp only [Oracle.gather, List.mem_map] at hg
  obtain ⟨_, _, rfl⟩ := hg
  rfl

theorem gather_qubits {S : List Qubit} {p : Qubit} {g : Gate} (hg : g ∈ Oracle.gather S p)
    {q : Qubit} (hq : q ∈ g.qubits) : q ∈ S ∨ q = p := by
  simp only [Oracle.gather, List.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  simp only [Gate.qubits, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Or.inl (List.mem_filter.mp hc).1
  · exact Or.inr rfl

/-! ## Item 3 — `symDiff` is the XOR of linear parts -/

theorem perm_insertBy {α : Type} (le : α → α → Bool) (x : α) :
    ∀ l : List α, (insertBy le x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertBy
    split
    · exact List.Perm.refl _
    · exact ((perm_insertBy le x ys).cons y).trans (List.Perm.swap x y ys)

theorem perm_foldr_insertBy {α : Type} (le : α → α → Bool) :
    ∀ l : List α, (l.foldr (insertBy le) []).Perm l
  | [] => List.Perm.refl _
  | x :: l => by
    rw [List.foldr_cons]
    exact (perm_insertBy le x _).trans ((perm_foldr_insertBy le l).cons x)

theorem symDiff_perm (A B : List Qubit) :
    (symDiff A B).Perm (A.filter (!B.contains ·) ++ B.filter (!A.contains ·)) :=
  perm_foldr_insertBy _ _

theorem mem_symDiff {A B : List Qubit} {q : Qubit} (h : q ∈ symDiff A B) : q ∈ A ∨ q ∈ B := by
  rcases List.mem_append.mp ((symDiff_perm A B).mem_iff.mp h) with h | h
  · exact Or.inl (List.mem_filter.mp h).1
  · exact Or.inr (List.mem_filter.mp h).1

theorem symDiff_nodup {A B : List Qubit} (hA : A.Nodup) (hB : B.Nodup) : (symDiff A B).Nodup := by
  rw [(symDiff_perm A B).nodup_iff, List.nodup_append]
  refine ⟨hA.filter _, hB.filter _, fun x hx y hy hxy => ?_⟩
  subst hxy
  have h1 := (List.mem_filter.mp hx).2
  have h2 := (List.mem_filter.mp hy).1
  simp [h2] at h1

/-- Report §6.1.2 (item 3) — on distinct atoms, the insertion-sort `symDiff` of Stage 8b is the
XOR of the two linear parts: atoms in both cancel. -/
theorem xorL_symDiff {A B : List Qubit} (hA : A.Nodup) (hB : B.Nodup) (s : Reg n × Reg a) :
    xorL (symDiff A B) s = (xorL A s ^^ xorL B s) := by
  have hcap : (A.filter (B.contains ·)).Perm (B.filter (A.contains ·)) := by
    rw [List.perm_ext_iff_of_nodup (hA.filter _) (hB.filter _)]
    intro x
    simp only [List.mem_filter, List.contains_iff_mem]
    tauto
  rw [xorL_perm (symDiff_perm A B), xorL_append, xorL_filter_split (B.contains ·) A,
    xorL_filter_split (A.contains ·) B, xorL_perm hcap]
  generalize xorL (B.filter (A.contains ·)) s = X
  generalize xorL (A.filter fun q => !B.contains q) s = Y
  generalize xorL (B.filter fun q => !A.contains q) s = Z
  cases X <;> cases Y <;> cases Z <;> rfl

/-- Report §6.1.2, §7.3.2 (item 3) — the value of an XOR node: `(u ⊕ v).eval = u.eval ⊕ v.eval`
for the synthesizer's `⟨symDiff u.lin v.lin, u.c ⊕ v.c⟩`. -/
theorem Synthesis.Aff.eval_symDiff {u v : Aff} (hu : u.lin.Nodup) (hv : v.lin.Nodup)
    (s : Reg n × Reg a) :
    (Aff.mk (symDiff u.lin v.lin) (u.c ^^ v.c)).eval s = (u.eval s ^^ v.eval s) := by
  rw [Aff.eval_eq_xorL, Aff.eval_eq_xorL u, Aff.eval_eq_xorL v, xorL_symDiff hu hv]
  generalize xorL u.lin s = X
  generalize xorL v.lin s = Y
  cases X <;> cases Y <;> cases u.c <;> cases v.c <;> rfl

/-! ## `Except` helpers -/

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem except_pure_eq_ok {ε α : Type} {x y : α} : (pure x : Except ε α) = .ok y ↔ x = y := by
  simp [pure, Except.pure]

theorem fail_ne_ok {α : Type} (msg : String) (y : α) : Oracle.fail msg ≠ .ok y := by
  intro h; cases h

/-! ## Item 2 — `prepare` on basis vectors -/

/-- The polarity gates of `prepare`. -/
theorem polGates_isPerm (b : Bool) (q : Qubit) :
    ∀ g ∈ (if b then [Gate.x q] else []), g.isPerm = true := by
  cases b <;> simp [Gate.isPerm]

theorem permRun_pol (b : Bool) (q : Qubit) (s : Reg n × Reg a) :
    permRun (if b then [Gate.x q] else []) s = if b then q.flip s else s := by
  cases b <;> rfl

theorem get_permRun_pol_self {q : Qubit} (hq : q.inRange n a = true) (b : Bool)
    (s : Reg n × Reg a) : q.get (permRun (if b then [Gate.x q] else []) s) = (q.get s ^^ b) := by
  cases b
  · simp [permRun]
  · simp [permRun, Gate.basisPerm, Qubit.get_flip_self q hq]

theorem get_permRun_pol_ne {p q : Qubit} (hpq : p ≠ q) (b : Bool) (s : Reg n × Reg a) :
    p.get (permRun (if b then [Gate.x q] else []) s) = p.get s := by
  cases b
  · rfl
  · exact Qubit.get_flip_ne hpq s

/-- Report §6.1.2, §6.1.4 Step 3 — the gate block before `Z` in the phase flip of `P`: with a
nonempty linear part `q :: l` of distinct atoms and `q` in range, it puts `P.eval s` on `q`. -/
theorem get_permRun_gather_pol {S : List Qubit} {q : Qubit} (hnd : S.Nodup) (hqS : q ∈ S)
    (hq : q.inRange n a = true) (b : Bool) (s : Reg n × Reg a) :
    q.get (permRun (Oracle.gather S q ++ (if b then [Gate.x q] else [])) s) = (xorL S s ^^ b) := by
  rw [permRun_append, get_permRun_pol_self hq, permRun_gather hnd hqS hq, Qubit.get_set_self _ hq]

/-- Report §6.1.2, §6.2.2 (item 2) — what a successful `prepare u v = .ok (pre, pu, pv)` gives
for operands with distinct atoms: `pu ≠ pv`; `pre` is a list of `X` / `CNOT` gates whose qubits
are atoms of `u` or `v`; and on every basis state (with `pu`, `pv` in range), after `pre` the
qubit `pu` holds `u.eval s` and `pv` holds `v.eval s` — both when `pu ∈ v.lin` (then `Sv` is
`pu :: symDiff (u.lin \ pu) (v.lin \ pu)`, whose XOR after the first gather is `v`) and when
not. Only `pu` and `pv` are written, so `preᴿ` restores the atoms (`permRun_reverse`). -/
theorem prepare_ok {u v : Aff} {pre : List Gate} {pu pv : Qubit}
    (h : Oracle.prepare u v = .ok (pre, pu, pv)) (hu : u.lin.Nodup) (hv : v.lin.Nodup) :
    pu ≠ pv ∧ (∀ g ∈ pre, g.isPerm = true) ∧
      (∀ g ∈ pre, ∀ q ∈ g.qubits, q ∈ u.lin ∨ q ∈ v.lin) ∧
      ∀ {n a : ℕ} (s : Reg n × Reg a), pu.inRange n a = true → pv.inRange n a = true →
        pu.get (permRun pre s) = u.eval s ∧ pv.get (permRun pre s) = v.eval s := by
  unfold Oracle.prepare at h
  dsimp only at h
  split at h
  swap
  · rw [except_bind_eq_ok] at h
    obtain ⟨_, hf, _⟩ := h
    exact absurd hf (fail_ne_ok _ _)
  rename_i p₀ us hul
  simp only [pure_bind] at h
  have hp₀u : p₀ ∈ u.lin := by rw [hul]; exact List.mem_cons_self
  -- the second operand's qubit set after the first gather
  set Sv := if v.lin.contains p₀ = true then
    p₀ :: symDiff (u.lin.erase p₀) (v.lin.erase p₀) else v.lin with hSv
  split at h
  swap
  · rw [except_bind_eq_ok] at h
    obtain ⟨_, hf, _⟩ := h
    exact absurd hf (fail_ne_ok _ _)
  rename_i q₀ vs hvl
  simp only [except_pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hq₀f : q₀ ∈ Sv.filter (· != p₀) := by rw [hvl]; exact List.mem_cons_self
  have hq₀S : q₀ ∈ Sv := (List.mem_filter.mp hq₀f).1
  have hpq : p₀ ≠ q₀ := fun e => by simpa [e] using (List.mem_filter.mp hq₀f).2
  -- `Sv` is a set of atoms of `u`, `v`, with no repeats, whose XOR after the first gather is `v`
  have hSvmem : ∀ q ∈ Sv, q ∈ u.lin ∨ q ∈ v.lin := by
    intro q hq
    rw [hSv] at hq
    split at hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl hp₀u
      · rcases mem_symDiff hq with hq | hq
        exacts [Or.inl (List.mem_of_mem_erase hq), Or.inr (List.mem_of_mem_erase hq)]
    · exact Or.inr hq
  have hSvnd : Sv.Nodup := by
    rw [hSv]
    split
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, symDiff_nodup (hu.erase _) (hv.erase _)⟩
      rcases mem_symDiff hm with hm | hm
      exacts [hu.not_mem_erase hm, hv.not_mem_erase hm]
    · exact hv
  have hSvval : ∀ {n a : ℕ} (s : Reg n × Reg a), p₀.inRange n a = true →
      xorL Sv (p₀.set (xorL u.lin s) s) = xorL v.lin s := by
    intro n a s hp
    rw [hSv]
    split
    · rename_i hc
      have hpv : p₀ ∈ v.lin := List.contains_iff_mem.mp hc
      have hnot : p₀ ∉ symDiff (u.lin.erase p₀) (v.lin.erase p₀) := fun hm => by
        rcases mem_symDiff hm with hm | hm
        exacts [hu.not_mem_erase hm, hv.not_mem_erase hm]
      rw [xorL_cons, Qubit.get_set_self _ hp, xorL_set_of_not_mem hnot,
        xorL_symDiff (hu.erase _) (hv.erase _), xorL_erase hp₀u s, xorL_erase hpv s]
      generalize p₀.get s = X
      generalize xorL (u.lin.erase p₀) s = Y
      generalize xorL (v.lin.erase p₀) s = Z
      cases X <;> cases Y <;> cases Z <;> rfl
    · rename_i hc
      have hpv : p₀ ∉ v.lin := fun hm => hc (List.contains_iff_mem.mpr hm)
      exact xorL_set_of_not_mem hpv _ s
  refine ⟨hpq, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg | hg
    · exact gather_isPerm _ _ g hg
    · exact gather_isPerm _ _ g hg
    · exact polGates_isPerm _ _ g hg
    · exact polGates_isPerm _ _ g hg
  · intro g hg q hq
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg | hg
    · rcases gather_qubits hg hq with hq | rfl
      exacts [Or.inl hq, Or.inl hp₀u]
    · rcases gather_qubits hg hq with hq | rfl
      exacts [hSvmem q hq, hSvmem _ hq₀S]
    · cases hc : u.c <;> simp only [hc, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil,
        List.mem_singleton] at hg
      subst hg
      simp only [Gate.qubits, List.mem_singleton] at hq
      subst hq
      exact Or.inl hp₀u
    · cases hc : v.c <;> simp only [hc, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil,
        List.mem_singleton] at hg
      subst hg
      simp only [Gate.qubits, List.mem_singleton] at hq
      subst hq
      exact hSvmem _ hq₀S
  · intro n a s hp hq
    have hs1 := permRun_gather hu hp₀u hp s
    have hs2 := permRun_gather hSvnd hq₀S hq (p₀.set (xorL u.lin s) s)
    rw [hSvval s hp] at hs2
    simp only [permRun_append, hs1, hs2]
    rw [get_permRun_pol_ne hpq, get_permRun_pol_self hp, get_permRun_pol_self hq,
      get_permRun_pol_ne (Ne.symm hpq), Qubit.get_set_ne hpq, Qubit.get_set_self _ hp,
      Qubit.get_set_self _ hq, Aff.eval_eq_xorL, Aff.eval_eq_xorL v]
    exact ⟨rfl, rfl⟩

end CQRV

end
