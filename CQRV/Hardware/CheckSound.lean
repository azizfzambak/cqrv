module

public import CQRV.Hardware.Check
public import CQRV.Hardware.WitnessSound

/-!
# CQRV.Hardware.CheckSound

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 (Stage 26c1, Track C) — **`applyWitnessQ_ok`**: the linear
reconstruction check implies `applyWitness`, so `applyWitness_sound` applies to it unchanged.

The queue fold is simulated against the fold of `applyWitness` (`SimInv`): the queues are those
of the remaining indexed elements (`queuesOf W rem`), the layout and the steps are the same (the
steps accumulated in reverse), and taking an element at the head of every queue of its wires is
exactly `validReorder`'s step — nothing before it in the remaining list shares a wire with it
(`indep`), and popping its queues leaves the queues of the remaining list without it
(`popAll_queuesOf`). At the end, empty queues mean no element remains (every element has a wire).
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV

/-! ## Wires -/

theorem mem_dedup {x : ℕ} {l : List ℕ} : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons y ys ih =>
    simp only [dedup, List.mem_cons]
    split_ifs with h
    · rw [ih]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact ih.mp h
        · exact hx
    · simp [ih]

theorem nodup_dedup (l : List ℕ) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons y ys ih =>
    simp only [dedup]
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h, ih⟩

theorem BasisGate.qubits_ne_nil (bg : BasisGate) : bg.qubits ≠ [] := by
  induction bg with
  | ifBit j g ih => simpa [BasisGate.qubits] using ih
  | _ => simp [BasisGate.qubits]

theorem Elem.wires_ne_nil (n k : ℕ) (T : List BasisGate) (e : Elem) : Elem.wires n k T e ≠ [] := by
  intro h
  have hno : ∀ x, x ∉ Elem.wires n k T e := by simp [h]
  cases e with
  | plain i =>
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (BasisGate.qubits_ne_nil (T.getD i default))
    exact hno (canonPos n q)
      (mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))
  | block j ms =>
    exact hno (j + k) (mem_dedup.mpr (List.mem_append_right _ (by simp [Elem.bits])))

/-- Disjoint wires give independence. -/
theorem indep_of_wires_disjoint (n k : ℕ) (T : List BasisGate) (e e' : Elem)
    (h : ∀ x ∈ Elem.wires n k T e, x ∉ Elem.wires n k T e') :
    indep (Elem.qubits T) (Elem.bits T) e e' = true := by
  simp only [indep, disjointL, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro q hq hq'
    exact h (canonPos n q) (mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))
      (mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨q, hq', rfl⟩)))
  · intro j hj hj'
    exact h (j + k) (mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩)))
      (mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj', rfl⟩)))

/-! ## Indexed elements -/

theorem indexedWires_map_fst (n k : ℕ) (es : List Elem) (T : List BasisGate) (i : ℕ) :
    (indexedWires n k es T i).map (·.1) = List.range' i es.length := by
  induction es generalizing T i with
  | nil => rfl
  | cons e es ih => simp [indexedWires, List.range'_succ, ih]

theorem indexedWires_map_el (n k : ℕ) (es : List Elem) (T : List BasisGate) (i : ℕ) :
    (indexedWires n k es T i).map (·.2.1) = es := by
  induction es generalizing T i with
  | nil => rfl
  | cons e es ih => simp [indexedWires, ih]

theorem indexedWires_idx (n k : ℕ) (es : List Elem) (T : List BasisGate) (i : ℕ) {p : QEntry}
    (h : p ∈ indexedWires n k es T i) : es[p.1 - i]? = some p.2.1 ∧ i ≤ p.1 := by
  induction es generalizing T i with
  | nil => simp [indexedWires] at h
  | cons e es ih =>
    simp only [indexedWires, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h2, h3⟩ := ih _ (i + 1) h
      refine ⟨?_, by omega⟩
      have : p.1 - i = (p.1 - (i + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact h2

/-- The number of translated gates of a list of elements. -/
def Elem.sizes (es : List Elem) : ℕ := (es.map Elem.size).sum

theorem indexedWires_append (n k : ℕ) (l₁ l₂ : List Elem) (T : List BasisGate) (i : ℕ) :
    indexedWires n k (l₁ ++ l₂) T i =
      indexedWires n k l₁ T i ++ indexedWires n k l₂ (T.drop (Elem.sizes l₁)) (i + l₁.length) := by
  induction l₁ generalizing T i with
  | nil => simp [indexedWires, Elem.sizes]
  | cons e l₁ ih =>
    simp only [List.cons_append, indexedWires, ih, Elem.sizes, List.map_cons, List.sum_cons, List.drop_drop,
      List.length_cons]
    rw [Nat.add_comm e.size, Nat.add_assoc i 1, Nat.add_comm 1]

/-- The wires from the gates are the wires from the translation when the gates are the element's. -/
theorem wiresOf_eq (n k : ℕ) (T : List BasisGate) (e : Elem) {gs : List BasisGate} (hg : Elem.gates T e = gs)
    (hb : Elem.bits T e = Elem.bitsOf e gs) : wiresOf n k e gs = Elem.wires n k T e := by
  simp only [wiresOf, Elem.wires, Elem.qubits_eq, hg, hb]

theorem bits_plain (T : List BasisGate) (k : ℕ) :
    Elem.bits T (.plain k) = Elem.bitsOf (.plain k) [T.getD k default] := by
  simp only [Elem.bits, Elem.bitsOf]
  cases T.getD k default <;> rfl

/-- The lockstep pass over the plain elements of one gate: each takes the next translated gate. -/
theorem indexedWires_plains (n k : ℕ) (E rest : List BasisGate) (k₀ i₀ : ℕ) (T₀ : List BasisGate)
    (hk : T₀.length = k₀) {p : QEntry}
    (h : p ∈ indexedWires n k ((List.range E.length).map fun i => Elem.plain (i + k₀)) (E ++ rest) i₀) :
    p.2.2.1 = Elem.wires n k (T₀ ++ (E ++ rest)) p.2.1 ∧ p.2.2.2 = Elem.gates (T₀ ++ (E ++ rest)) p.2.1 ∧
      ∀ k', p.2.1 = .plain k' → k' < (T₀ ++ (E ++ rest)).length := by
  induction E generalizing k₀ i₀ T₀ with
  | nil => simp [indexedWires] at h
  | cons e E ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map] at h
    simp only [indexedWires, List.cons_append, List.mem_cons, Elem.size, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero] at h
    rcases h with rfl | h
    · have hget : (T₀ ++ e :: (E ++ rest)).getD k₀ default = e := by
        have := getD_append_offset T₀ (e :: (E ++ rest)) hk 0 default
        simpa using this
      refine ⟨?_, ?_, ?_⟩
      · dsimp only
        exact wiresOf_eq n k (T₀ ++ e :: (E ++ rest)) (Elem.plain (0 + k₀))
          (by simp only [Elem.gates, Nat.zero_add, hget]) (by rw [bits_plain, Nat.zero_add, hget])
      · exact (show Elem.gates (T₀ ++ e :: (E ++ rest)) (Elem.plain (0 + k₀)) = [e] by
          simp only [Elem.gates, Nat.zero_add, hget]).symm
      · intro k' hk'
        simp only [Elem.plain.injEq] at hk'
        subst hk'
        simp [hk]
    · have hT : (T₀ ++ [e]).length = k₀ + 1 := by simp [hk]
      have h' : p ∈ indexedWires n k ((List.range E.length).map fun i => Elem.plain (i + (k₀ + 1))) (E ++ rest) (i₀ + 1) := by
        convert h using 3
        funext i; simp [Nat.add_assoc, Nat.add_comm 1 k₀]
      obtain ⟨h1, h2, h3⟩ := ih (k₀ + 1) (i₀ + 1) (T₀ ++ [e]) hT h'
      simp only [List.append_assoc, List.singleton_append] at h1 h2 h3
      exact ⟨h1, h2, h3⟩

/-- The lockstep pass over a block: it takes its members' gates. -/
theorem indexedWires_block (n k : ℕ) (E rest : List BasisGate) (j k₀ i₀ : ℕ) (T₀ : List BasisGate)
    (hk : T₀.length = k₀) {p : QEntry}
    (h : p ∈ indexedWires n k [Elem.block j ((List.range E.length).map (· + k₀))] (E ++ rest) i₀) :
    p.2.2.1 = Elem.wires n k (T₀ ++ (E ++ rest)) p.2.1 ∧ p.2.2.2 = Elem.gates (T₀ ++ (E ++ rest)) p.2.1 ∧
      ∀ k', p.2.1 = .plain k' → k' < (T₀ ++ (E ++ rest)).length := by
  simp only [indexedWires, List.mem_singleton] at h
  subst h
  have hgates : Elem.gates (T₀ ++ (E ++ rest)) (Elem.block j ((List.range E.length).map (· + k₀))) = E := by
    simp only [Elem.gates, List.map_map]
    have : ((List.range E.length).map fun i => (T₀ ++ (E ++ rest)).getD (i + k₀) default) = E := by
      rw [List.map_congr_left (fun i hi => by
        rw [getD_append_offset T₀ _ hk, List.getD_eq_getElem?_getD, List.getElem?_append_left (List.mem_range.mp hi),
          ← List.getD_eq_getElem?_getD]), map_getD_range]
    simpa [Function.comp_def] using this
  have htake : (E ++ rest).take (Elem.block j ((List.range E.length).map (· + k₀))).size = E := by
    simp [Elem.size]
  refine ⟨?_, ?_, fun _ h => by cases h⟩
  · dsimp only
    rw [htake]
    exact wiresOf_eq n k (T₀ ++ (E ++ rest)) _ hgates rfl
  · dsimp only; rw [htake, hgates]

/-- The specification of the lockstep pass over `elements.go`: every entry carries the wires and
the gates of its element, and a plain element's index is inside the translation. -/
theorem indexedWires_go_spec (b : TargetBasis) (n k : ℕ) (gs : List Gate) (k₀ i₀ : ℕ) (T₀ : List BasisGate)
    (hk : T₀.length = k₀) {p : QEntry}
    (h : p ∈ indexedWires n k (elements.go b gs k₀) (gs.flatMap fun g => (decompTable b g).gates) i₀) :
    p.2.2.1 = Elem.wires n k (T₀ ++ gs.flatMap fun g => (decompTable b g).gates) p.2.1 ∧
      p.2.2.2 = Elem.gates (T₀ ++ gs.flatMap fun g => (decompTable b g).gates) p.2.1 ∧
      ∀ k', p.2.1 = .plain k' → k' < (T₀ ++ gs.flatMap fun g => (decompTable b g).gates).length := by
  induction gs generalizing k₀ i₀ T₀ with
  | nil => simp [elements.go, indexedWires] at h
  | cons g gs ih =>
    rw [elements_go_cons, indexedWires_append, List.flatMap_cons] at h
    set E := (decompTable b g).gates with hE
    have hsz : Elem.sizes (elemsOf b g k₀) = E.length := by
      cases g <;> simp [elemsOf, Elem.sizes, Elem.size, hE, Function.comp_def, List.map_const', List.sum_replicate]
    rcases List.mem_append.mp h with h | h
    · cases g with
      | ifBit j g' => exact indexedWires_block n k E _ j k₀ i₀ T₀ hk h
      | _ => exact indexedWires_plains n k E _ k₀ i₀ T₀ hk h
    · rw [hsz, List.drop_left' rfl] at h
      have hT : (T₀ ++ E).length = k₀ + E.length := by simp [hk]
      obtain ⟨h1, h2, h3⟩ := ih (k₀ + E.length) _ (T₀ ++ E) hT h
      simp only [List.append_assoc] at h1 h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Queues -/

theorem queuesOf_length (W : ℕ) (ents : List QEntry) : (queuesOf W ents).length = W := by
  simp [queuesOf]

theorem queuesOf_getD (W : ℕ) (ents : List QEntry) {x : ℕ} (hx : x < W) :
    (queuesOf W ents).getD x [] = ents.filter fun p => decide (x ∈ p.2.2.1) := by
  simp [queuesOf, List.getD_eq_getElem?_getD, hx]

theorem queuesOf_getD_ge (W : ℕ) (ents : List QEntry) {x : ℕ} (hx : W ≤ x) :
    (queuesOf W ents).getD x [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [queuesOf_length])]
  rfl

theorem mem_queuesOf {W : ℕ} {ents : List QEntry} {q : List QEntry} (h : q ∈ queuesOf W ents) :
    ∃ x, x < W ∧ q = ents.filter fun p => decide (x ∈ p.2.2.1) := by
  simp only [queuesOf, List.mem_map, List.mem_range] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

theorem length_modifyAt {α : Type} (f : α → α) (i : ℕ) (l : List α) :
    (modifyAt f i l).length = l.length := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [modifyAt, ih]

theorem getD_modifyAt_self {α : Type} (f : α → α) {i : ℕ} {l : List α} (h : i < l.length) (d : α) :
    (modifyAt f i l).getD i d = f (l.getD i d) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [modifyAt, List.getD_cons_succ]; exact ih (by simpa using h)

theorem getD_modifyAt_ne {α : Type} (f : α → α) {i j : ℕ} (h : i ≠ j) (l : List α) (d : α) :
    (modifyAt f i l).getD j d = l.getD j d := by
  induction l generalizing i j with
  | nil => simp [modifyAt]
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j => simp only [modifyAt, List.getD_cons_succ]; exact ih (fun e => h (by rw [e]))

theorem getD_of_length_le {α : Type} {l : List α} {i : ℕ} (h : l.length ≤ i) (d : α) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem length_popAll (ws : List ℕ) (Q : List (List QEntry)) : (popAll ws Q).length = Q.length := by
  induction ws generalizing Q with
  | nil => rfl
  | cons v vs ih => simp only [popAll, List.foldl_cons] at ih ⊢; rw [ih, length_modifyAt]

theorem getD_popAll (ws : List ℕ) (hws : ws.Nodup) (Q : List (List QEntry)) (x : ℕ) :
    (popAll ws Q).getD x [] = if x ∈ ws then (Q.getD x []).tail else Q.getD x [] := by
  induction ws generalizing Q with
  | nil => simp [popAll]
  | cons v vs ih =>
    have hv : v ∉ vs := (List.nodup_cons.mp hws).1
    have hvs : vs.Nodup := (List.nodup_cons.mp hws).2
    simp only [popAll, List.foldl_cons] at ih ⊢
    rw [ih hvs]
    by_cases hxv : x = v
    · subst hxv
      simp only [hv, List.mem_cons, true_or, ↓reduceIte]
      by_cases hl : x < Q.length
      · rw [getD_modifyAt_self _ hl]
      · rw [getD_of_length_le (by simpa [length_modifyAt] using hl), getD_of_length_le (by simpa using hl)]
        rfl
    · rw [getD_modifyAt_ne _ (Ne.symm hxv)]
      simp [List.mem_cons, hxv]

theorem findHead_some {Q : List (List QEntry)} {i : ℕ} {p : QEntry} (h : findHead Q i = some p) :
    p.1 = i ∧ ∃ rest, (p :: rest) ∈ Q := by
  induction Q with
  | nil => simp [findHead] at h
  | cons q Q ih =>
    cases q with
    | nil =>
      simp only [findHead, List.findSome?_cons] at h
      obtain ⟨h1, rest, hmem⟩ := ih (by simpa [findHead] using h)
      exact ⟨h1, rest, List.mem_cons_of_mem _ hmem⟩
    | cons p' rest' =>
      simp only [findHead, List.findSome?_cons] at h
      by_cases hpi : p'.1 = i
      · simp only [hpi, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨hpi, rest', List.mem_cons_self ..⟩
      · simp only [hpi, ↓reduceIte] at h
        obtain ⟨h1, rest, hmem⟩ := ih (by simpa [findHead] using h)
        exact ⟨h1, rest, List.mem_cons_of_mem _ hmem⟩

theorem headsAre_true {Q : List (List QEntry)} {i : ℕ} {ws : List ℕ} (h : headsAre Q i ws = true)
    {x : ℕ} (hx : x ∈ ws) : ∃ p rest, Q.getD x [] = p :: rest ∧ p.1 = i := by
  simp only [headsAre, List.all_eq_true] at h
  have := h x hx
  cases hq : Q.getD x [] with
  | nil => rw [hq] at this; simp at this
  | cons p rest => rw [hq] at this; exact ⟨p, rest, rfl, by simpa using this⟩

theorem ext_of_getD {α : Type} {l l' : List α} (d : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i d = l'.getD i d) : l = l' := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] at this

/-- Entries of a list with no repeated index are determined by their index. -/
theorem eq_of_idx {rem : List QEntry} (hnd : (rem.map (·.1)).Nodup) {p p' : QEntry} (hp : p ∈ rem)
    (hp' : p' ∈ rem) (h : p.1 = p'.1) : p = p' :=
  List.inj_on_of_nodup_map hnd hp hp' h

/-- **Taking an element**: the entry `p` found at the head of its queues splits the remaining list
as `pre ++ p :: post` with nothing in `pre` on a wire of `p`, and popping gives the queues of
`pre ++ post`. -/
theorem take_spec (W : ℕ) (rem : List QEntry) (hnd : (rem.map (·.1)).Nodup) {i : ℕ} {p : QEntry}
    (hfind : findHead (queuesOf W rem) i = some p) (hheads : headsAre (queuesOf W rem) i p.2.2.1 = true)
    (hnodup : p.2.2.1.Nodup) :
    ∃ pre post, rem = pre ++ p :: post ∧ (∀ p' ∈ pre, ∀ x ∈ p.2.2.1, x ∉ p'.2.2.1) ∧
      popAll p.2.2.1 (queuesOf W rem) = queuesOf W (pre ++ post) := by
  obtain ⟨hpi, rest, hmem⟩ := findHead_some hfind
  obtain ⟨x₀, _, hq⟩ := mem_queuesOf hmem
  have hp : p ∈ rem := List.mem_of_mem_filter (by rw [← hq]; exact List.mem_cons_self ..)
  obtain ⟨pre, post, hrem⟩ := List.append_of_mem hp
  -- on every wire of `p`, the queue starts with `p`
  have hpre : ∀ x ∈ p.2.2.1, ∀ p' ∈ pre, x ∉ p'.2.2.1 := by
    intro x hx p' hp' hx'
    obtain ⟨px, restx, hqx, hpx⟩ := headsAre_true hheads hx
    by_cases hxW : x < W
    · rw [queuesOf_getD W rem hxW, hrem, List.filter_append, List.filter_cons_of_pos (by simpa using hx)]
        at hqx
      -- the head is an entry of `rem` with the index of `p`, so it is `p`; but `p'` comes first
      have hpx_mem : px ∈ rem := by
        have : px ∈ (pre.filter fun p => decide (x ∈ p.2.2.1)) ++ p :: (post.filter fun p => decide (x ∈ p.2.2.1)) := by
          rw [hqx]; exact List.mem_cons_self ..
        rcases List.mem_append.mp this with h | h
        · exact hrem ▸ List.mem_append_left _ (List.mem_of_mem_filter h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact hp
          · exact hrem ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_mem_filter h))
      have hpxp : px = p := eq_of_idx hnd hpx_mem hp (hpx.trans hpi.symm)
      rw [hpxp] at hqx
      -- `pre.filter` is not empty: it contains `p'`
      have hp'f : p' ∈ pre.filter fun p => decide (x ∈ p.2.2.1) := List.mem_filter.mpr ⟨hp', by simpa using hx'⟩
      cases hpf : pre.filter fun p => decide (x ∈ p.2.2.1) with
      | nil => rw [hpf] at hp'f; simp at hp'f
      | cons p₀ l₀ =>
        rw [hpf] at hqx
        simp only [List.cons_append, List.cons.injEq] at hqx
        -- `p₀ = px = p` lies in `pre`: its index repeats in `rem`
        have hp₀ : p₀ ∈ pre := List.mem_of_mem_filter (by rw [hpf]; exact List.mem_cons_self ..)
        have : (rem.map (·.1)).Nodup := hnd
        rw [hrem, List.map_append, List.map_cons] at this
        have hn := (List.nodup_cons.mp (List.nodup_middle.mp this)).1
        exact hn (List.mem_append_left _ (List.mem_map.mpr ⟨p₀, hp₀, by rw [hqx.1]⟩))
    · rw [queuesOf_getD_ge W rem (by omega)] at hqx
      simp at hqx
  refine ⟨pre, post, hrem, fun p' hp' x hx => hpre x hx p' hp', ?_⟩
  apply ext_of_getD []
  · rw [length_popAll, queuesOf_length, queuesOf_length]
  · intro x hx
    rw [length_popAll, queuesOf_length] at hx
    rw [getD_popAll _ hnodup, queuesOf_getD W rem hx, queuesOf_getD W (pre ++ post) hx, hrem,
      List.filter_append, List.filter_append]
    by_cases hxp : x ∈ p.2.2.1
    · have hpf : pre.filter (fun p => decide (x ∈ p.2.2.1)) = [] :=
        List.filter_eq_nil_iff.mpr fun p' hp' => by simpa using hpre x hxp p' hp'
      simp [hxp, hpf, List.filter_cons_of_pos]
    · simp only [hxp, ↓reduceIte]
      rw [List.filter_cons_of_neg (by simpa using hxp)]

/-! ## The simulation -/

section Sim

variable (b : TargetBasis) (C : Circuit) (w : Witness) {N : ℕ}

/-- The invariant between the fold of `applyWitness` (state `st`) and the queue fold (state `q`),
with the remaining indexed elements `rem`. -/
structure SimInv (st : ApplyState) (q : QState) (rem : List QEntry) : Prop where
  lay : q.lay = st.lay
  steps : q.stepsRev.reverse = st.steps
  Q : q.Q = queuesOf (C.nData + C.nAnc + C.nBits) rem
  wires : ∀ p ∈ rem, p.2.2.1 = Elem.wires C.nData (C.nData + C.nAnc) (translate b C) p.2.1 ∧
    ∀ x ∈ p.2.2.1, x < C.nData + C.nAnc + C.nBits
  gates : ∀ p ∈ rem, p.2.2.2 = Elem.gates (translate b C) p.2.1
  plainLt : ∀ p ∈ rem, ∀ k, p.2.1 = .plain k → k < (translate b C).length
  idx : ∀ p ∈ rem, (elements b C)[p.1]? = some p.2.1
  nodupIdx : (rem.map (·.1)).Nodup
  nodupEl : (rem.map (·.2.1)).Nodup
  valid : ∀ future, validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (rem.map (·.2.1))
      future = true →
    validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C) (st.taken ++ future) = true
  fresh : ∀ e ∈ st.taken, e ∉ rem.map (·.2.1)

theorem splitFirst_of_not_mem {α : Type} [DecidableEq α] {x : α} {pre post : List α} (h : x ∉ pre) :
    splitFirst x (pre ++ x :: post) = some (pre, post) := by
  induction pre with
  | nil => simp [splitFirst]
  | cons y ys ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitFirst, Ne.symm h.1, ih h.2]

/-- One `order` entry of the queue fold, simulated. -/
theorem orderStepQ_sim (st : ApplyState) (q q' : QState) (rem : List QEntry) (e : OrderEntry)
    (hinv : SimInv b C st q rem)
    (h : orderStepQ b C.nData N (translate b C) w q e = .ok q') :
    ∃ st' rem', orderStep b C.nData N (translate b C) (elements b C) w st e = .ok st' ∧
      SimInv b C st' q' rem' := by
  cases e with
  | swap p₁ p₂ =>
    simp only [orderStepQ] at h
    by_cases hpq : p₁ = p₂
    · simp only [hpq, ↓reduceIte] at h; simp at h
    · simp only [hpq, ↓reduceIte] at h
      by_cases hr : p₁ < N ∧ p₂ < N
      · simp only [hr, and_self, ↓reduceIte] at h
        rw [← exceptPure_ok h]
        refine ⟨{ st with lay := swapLay st.lay p₁ p₂, steps := st.steps ++ [.swap p₁ p₂] }, rem, ?_, ?_⟩
        · simp [orderStep, hpq, hr, pure, Except.pure]
        · exact { hinv with lay := by simp [hinv.lay], steps := by simp [hinv.steps] }
      · simp only [hr, ↓reduceIte] at h; simp at h
  | elem i =>
    simp only [orderStepQ] at h
    cases hfind : findHead q.Q i with
    | none => rw [hfind] at h; simp at h
    | some p =>
      rw [hfind] at h
      obtain ⟨i', el, ws, gs⟩ := p
      dsimp only at h
      by_cases hheads : headsAre q.Q i ws = true
      · simp only [hheads, ↓reduceIte] at h
        -- the entry is in `rem`, at the head of its queues
        have hQ := hinv.Q
        rw [hQ] at hfind hheads
        have hp_mem : (i', el, ws, gs) ∈ rem := by
          obtain ⟨_, rest, hmem⟩ := findHead_some hfind
          obtain ⟨x₀, _, hq⟩ := mem_queuesOf hmem
          exact List.mem_of_mem_filter (by rw [← hq]; exact List.mem_cons_self ..)
        obtain ⟨hws, hwsW⟩ := hinv.wires _ hp_mem
        have hgs := hinv.gates _ hp_mem
        have hplt := hinv.plainLt _ hp_mem
        dsimp only at hws hwsW hgs hplt
        have hwsnd : ws.Nodup := by rw [hws]; exact nodup_dedup _
        obtain ⟨pre, post, hrem, hpre, hpop⟩ := take_spec _ rem hinv.nodupIdx hfind hheads hwsnd
        have hi : i' = i := (findHead_some hfind).1
        subst hi
        have hel : (elements b C)[i']? = some el := hinv.idx _ hp_mem
        -- `el` is not among the taken elements, and not in `pre`
        have hfresh : el ∉ st.taken := fun h => hinv.fresh el h (List.mem_map.mpr ⟨_, hp_mem, rfl⟩)
        have hnotpre : el ∉ pre.map (·.2.1) := by
          intro hin
          obtain ⟨p', hp', hp'el⟩ := List.mem_map.mp hin
          obtain ⟨hws', _⟩ := hinv.wires p' (hrem ▸ List.mem_append_left _ hp')
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (Elem.wires_ne_nil C.nData (C.nData + C.nAnc) (translate b C) el)
          exact hpre p' hp' x (hws ▸ hx) (by rw [hws', hp'el]; exact hx)
        -- the new remaining list
        have hrem' : (pre ++ post).map (·.2.1) = pre.map (·.2.1) ++ post.map (·.2.1) := List.map_append ..
        have hsub : ∀ p' ∈ pre ++ post, p' ∈ rem := fun p' hp' => by
          rw [hrem]; rcases List.mem_append.mp hp' with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        have hnd' : ((pre ++ post).map (·.1)).Nodup := by
          have := hinv.nodupIdx; rw [hrem, List.map_append, List.map_cons] at this
          rw [List.map_append]; exact (List.nodup_cons.mp (List.nodup_middle.mp this)).2
        have hndel' : ((pre ++ post).map (·.2.1)).Nodup := by
          have := hinv.nodupEl; rw [hrem, List.map_append, List.map_cons] at this
          rw [List.map_append]; exact (List.nodup_cons.mp (List.nodup_middle.mp this)).2
        have hel_notpost : el ∉ post.map (·.2.1) := by
          have := hinv.nodupEl; rw [hrem, List.map_append, List.map_cons] at this
          exact fun h => (List.nodup_cons.mp (List.nodup_middle.mp this)).1 (List.mem_append_right _ h)
        -- the validity step
        have hvalid' : ∀ future, validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C))
            ((pre ++ post).map (·.2.1)) future = true →
            validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C)
              ((st.taken ++ [el]) ++ future) = true := by
          intro future hf
          rw [List.append_assoc, List.singleton_append]
          apply hinv.valid (el :: future)
          rw [hrem, List.map_append, List.map_cons]
          simp only [validReorder, splitFirst_of_not_mem hnotpre, Bool.and_eq_true]
          refine ⟨?_, by rw [← List.map_append]; exact hf⟩
          rw [List.all_eq_true]
          intro e' he'
          obtain ⟨p', hp', rfl⟩ := List.mem_map.mp he'
          obtain ⟨hws', _⟩ := hinv.wires p' (hrem ▸ List.mem_append_left _ hp')
          apply indep_of_wires_disjoint
          intro x hx hx'
          exact hpre p' hp' x (hws ▸ hx) (hws' ▸ hx')
        have hfresh' : ∀ e ∈ st.taken ++ [el], e ∉ (pre ++ post).map (·.2.1) := by
          intro e he hin
          rw [List.map_append, List.mem_append] at hin
          rcases List.mem_append.mp he with he | he
          · refine hinv.fresh e he ?_
            rw [hrem, List.map_append, List.map_cons]
            rcases hin with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          · simp only [List.mem_singleton] at he; subst he
            rcases hin with h | h
            · exact hnotpre h
            · exact hel_notpost h
        -- the original step
        have hcontains : st.taken.contains el = false := by
          rw [Bool.eq_false_iff]; intro hc; exact hfresh (by simpa using hc)
        cases el with
        | plain k =>
          dsimp only at h
          rw [← exceptPure_ok h]
          have hk : k < (translate b C).length := hplt k rfl
          have hTk : (translate b C)[k]? = some ((translate b C).getD k default) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
          have hgs' : gs = [(translate b C).getD k default] := hgs
          refine ⟨{ st with taken := st.taken ++ [.plain k], steps := st.steps ++ [.place gs] },
            pre ++ post, ?_, ?_⟩
          · simp only [orderStep, hel, hcontains, Bool.false_eq_true, ↓reduceIte]
            rw [hTk, hgs']
            rfl
          · exact { lay := by simpa using hinv.lay, steps := by simp [hinv.steps],
                    Q := by simpa [hQ] using hpop,
                    wires := fun p' hp' => hinv.wires p' (hsub p' hp'),
                    gates := fun p' hp' => hinv.gates p' (hsub p' hp'),
                    plainLt := fun p' hp' => hinv.plainLt p' (hsub p' hp'),
                    idx := fun p' hp' => hinv.idx p' (hsub p' hp'),
                    nodupIdx := hnd', nodupEl := hndel', valid := hvalid', fresh := hfresh' }
        | block j members =>
          dsimp only at h
          cases hbody : w.blocks.lookup i' with
          | none => rw [hbody] at h; simp at h
          | some body =>
            rw [hbody] at h
            obtain ⟨LP, hLP, h⟩ := exceptBind_ok h
            rw [← exceptPure_ok h]
            refine ⟨{ st with taken := st.taken ++ [.block j members], steps := st.steps ++ [.block LP.1 LP.2] },
              pre ++ post, ?_, ?_⟩
            · simp only [orderStep, hel, hcontains, Bool.false_eq_true, ↓reduceIte, hbody]
              rw [← hinv.lay, hLP]
              rfl
            · exact { lay := by simpa using hinv.lay, steps := by simp [hinv.steps],
                      Q := by simpa [hQ] using hpop,
                      wires := fun p' hp' => hinv.wires p' (hsub p' hp'),
                      gates := fun p' hp' => hinv.gates p' (hsub p' hp'),
                      plainLt := fun p' hp' => hinv.plainLt p' (hsub p' hp'),
                      idx := fun p' hp' => hinv.idx p' (hsub p' hp'),
                      nodupIdx := hnd', nodupEl := hndel', valid := hvalid', fresh := hfresh' }
      · simp only [hheads, Bool.false_eq_true, ↓reduceIte] at h; simp at h

theorem foldlM_sim (l : List OrderEntry) (st : ApplyState) (q q' : QState) (rem : List QEntry)
    (hinv : SimInv b C st q rem)
    (h : l.foldlM (orderStepQ b C.nData N (translate b C) w) q = .ok q') :
    ∃ st' rem', l.foldlM (orderStep b C.nData N (translate b C) (elements b C) w) st = .ok st' ∧
      SimInv b C st' q' rem' := by
  induction l generalizing st q rem with
  | nil => simp only [List.foldlM] at h; rw [← exceptPure_ok h]; exact ⟨st, rem, rfl, hinv⟩
  | cons e l ih =>
    simp only [List.foldlM] at h
    obtain ⟨q₁, h₁, h⟩ := exceptBind_ok h
    obtain ⟨st₁, rem₁, hst₁, hinv₁⟩ := orderStepQ_sim b C w st q q₁ rem e hinv h₁
    obtain ⟨st', rem', hst', hinv'⟩ := ih st₁ q₁ rem₁ hinv₁ h
    exact ⟨st', rem', by simp only [List.foldlM]; rw [hst₁]; exact hst', hinv'⟩

/-- Empty queues: no element remains (every element has a wire inside the register). -/
theorem rem_nil_of_empty (st : ApplyState) (q : QState) (rem : List QEntry) (hinv : SimInv b C st q rem)
    (h : q.Q.all List.isEmpty = true) : rem = [] := by
  cases hr : rem with
  | nil => rfl
  | cons p rest =>
    exfalso
    have hp : p ∈ rem := by rw [hr]; exact List.mem_cons_self ..
    obtain ⟨hws, hW⟩ := hinv.wires p hp
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hws ▸ Elem.wires_ne_nil C.nData (C.nData + C.nAnc) (translate b C) p.2.1 : p.2.2.1 ≠ [])
    have hxW := hW x hx
    have hmem : q.Q.getD x [] ∈ q.Q := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hinv.Q, queuesOf_length]; exact hxW)]
      exact List.getElem_mem _
    have hempty := List.all_eq_true.mp h _ hmem
    rw [hinv.Q, queuesOf_getD _ _ hxW] at hempty
    have : p ∈ rem.filter fun p => decide (x ∈ p.2.2.1) := List.mem_filter.mpr ⟨hp, by simpa using hx⟩
    rw [List.isEmpty_iff.mp hempty] at this
    simp at this

end Sim

/-! ## The elements are distinct -/

section Nodup

variable (b : TargetBasis)

/-- The index of an element: its gate, or a block's first member. -/
def Elem.idx : Elem → ℕ
  | .plain k => k
  | .block _ ms => ms.headD 0

theorem decompTable_gates_ne_nil {g : Gate} (h : g.isClifford = true) : (decompTable b g).gates ≠ [] := by
  cases g <;> cases b <;> simp_all [Gate.isClifford, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry]

theorem elements_go_idx (gs : List Gate) (k : ℕ)
    (hcl : ∀ g ∈ gs, ∀ j g', g = .ifBit j g' → g'.isClifford = true) :
    (elements.go b gs k).Pairwise (fun e e' => Elem.idx e < Elem.idx e') ∧
      ∀ e ∈ elements.go b gs k, k ≤ Elem.idx e := by
  induction gs generalizing k with
  | nil => simp [elements.go]
  | cons g gs ih =>
    rw [elements_go_cons]
    obtain ⟨ih1, ih2⟩ := ih (k + (decompTable b g).gates.length) fun g' hg' => hcl g' (List.mem_cons_of_mem _ hg')
    -- the elements of `g`: indices in `[k, k + m)`, increasing
    have hg : (elemsOf b g k).Pairwise (fun e e' => Elem.idx e < Elem.idx e') ∧
        ∀ e ∈ elemsOf b g k, k ≤ Elem.idx e ∧ Elem.idx e < k + (decompTable b g).gates.length := by
      cases g with
      | ifBit j g' =>
        have hne := decompTable_gates_ne_nil b (hcl _ (List.mem_cons_self ..) j g' rfl)
        have hm : 0 < (decompTable b (.ifBit j g')).gates.length := by
          simp only [decompTable, List.length_map]; exact List.length_pos_of_ne_nil hne
        refine ⟨List.pairwise_singleton _ _, ?_⟩
        intro e he
        simp only [elemsOf, List.mem_singleton] at he
        subst he
        simp only [Elem.idx]
        obtain ⟨m, hm'⟩ : ∃ m, (decompTable b (.ifBit j g')).gates.length = m + 1 :=
          Nat.exists_eq_succ_of_ne_zero (by omega)
        rw [hm']
        simp [List.range_succ_eq_map]
      | _ =>
        simp only [elemsOf]
        refine ⟨?_, ?_⟩
        · rw [List.pairwise_map]
          exact (List.pairwise_lt_range).imp fun h => by simpa [Elem.idx] using h
        · intro e he
          simp only [List.mem_map, List.mem_range] at he
          obtain ⟨i, hi, rfl⟩ := he
          simp [Elem.idx]; omega
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hg.1, ih1, fun e he e' he' => ?_⟩
      have := (hg.2 e he).2
      have := ih2 e' he'
      omega
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact (hg.2 e he).1
      · have := ih2 e he; omega

theorem elements_nodup (C : Circuit) (hC : C.WF) : (elements b C).Nodup := by
  have := (elements_go_idx b C.gates 0 hC.clifford).1
  exact this.imp fun h => ne_of_apply_ne Elem.idx (Nat.ne_of_lt h)

end Nodup

/-! ## The theorem -/

/-- **The simulation of a successful queue fold**: the fold of `applyWitness` succeeds with a state
of the same layout and steps, whose taken elements are a valid reordering. -/
theorem applyWitnessQ'_sim (b : TargetBasis) (C : Circuit) (hC : C.WF) (w : Witness) (N : ℕ)
    (q : QState) (h : applyWitnessQ' b C w N = .ok q) :
    ∃ st : ApplyState,
      w.order.foldlM (orderStep b C.nData N (translate b C) (elements b C) w) ⟨w.initial, [], []⟩ = .ok st ∧
      st.lay = w.final ∧
      validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C) st.taken = true ∧
      st.steps = q.stepsRev.reverse := by
  simp only [applyWitnessQ'] at h
  obtain ⟨_, h1, h⟩ := exceptBind_ok h
  obtain ⟨_, h2, h⟩ := exceptBind_ok h
  obtain ⟨_, h3, h⟩ := exceptBind_ok h
  obtain ⟨_, h4, h⟩ := exceptBind_ok h
  obtain ⟨_, h5, h⟩ := exceptBind_ok h
  obtain ⟨q', hfold, h⟩ := exceptBind_ok h
  obtain ⟨_, hempty, h⟩ := exceptBind_ok h
  obtain ⟨_, hfinal, h⟩ := exceptBind_ok h
  have hq := exceptPure_ok h
  subst hq
  -- the initial invariant
  set ents := indexedWires C.nData (C.nData + C.nAnc) (elements b C) (translate b C) 0 with hents
  have hW := ensure_ok h5
  have hspec : ∀ p ∈ ents, p.2.2.1 = Elem.wires C.nData (C.nData + C.nAnc) (translate b C) p.2.1 ∧
      p.2.2.2 = Elem.gates (translate b C) p.2.1 ∧ ∀ k', p.2.1 = .plain k' → k' < (translate b C).length := by
    intro p hp
    have := indexedWires_go_spec b C.nData (C.nData + C.nAnc) C.gates 0 0 [] rfl (p := p)
      (by simpa [hents, elements, translate] using hp)
    simpa [translate] using this
  have hinv₀ : SimInv b C ⟨w.initial, [], []⟩ ⟨w.initial, queuesOf (C.nData + C.nAnc + C.nBits) ents, []⟩ ents :=
    { lay := rfl, steps := rfl, Q := rfl,
      wires := fun p hp => ⟨(hspec p hp).1, fun x hx => by
        have := List.all_eq_true.mp hW p hp
        simpa using List.all_eq_true.mp this x hx⟩,
      gates := fun p hp => (hspec p hp).2.1,
      plainLt := fun p hp => (hspec p hp).2.2,
      idx := fun p hp => by have := (indexedWires_idx _ _ _ _ _ hp).1; simpa using this,
      nodupIdx := by rw [hents, indexedWires_map_fst]; exact List.nodup_range' ..,
      nodupEl := by rw [hents, indexedWires_map_el]; exact elements_nodup b C hC,
      valid := fun future hf => by rw [hents, indexedWires_map_el] at hf; simpa using hf,
      fresh := fun e he => by simp at he }
  obtain ⟨st, rem, hst, hinv⟩ := foldlM_sim b C w w.order _ _ q' ents hinv₀ hfold
  have hrem : rem = [] := rem_nil_of_empty b C st q' rem hinv (ensure_ok hempty)
  subst hrem
  have hvalid : validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C) st.taken = true := by
    have := hinv.valid [] (by simp [validReorder])
    simpa using this
  have hlen : st.taken.length = (elements b C).length := (validReorder_perm _ _ _ _ hvalid).length_eq
  have hlay : st.lay = w.final := by rw [← hinv.lay]; exact beq_iff_eq.mp (ensure_ok hfinal)
  exact ⟨st, hst, hlay, hvalid, hinv.steps.symm⟩

/-- The checks of `applyWitness` that precede its fold hold when those of `applyWitnessQ'` do. -/
theorem applyWitnessQ'_checks (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ)
    (q : QState) (h : applyWitnessQ' b C w N = .ok q) :
    ensure (w.basis == b) "witness: basis differs from the table's" = .ok () ∧
    ensure (w.initial.length == C.nData + C.nAnc && w.nLogical == C.nData + C.nAnc)
      "witness: initial layout length differs from the logical register" = .ok () ∧
    ensure (w.initial.all (· < N) && w.final.all (· < N)) "witness: a layout position outside the register" = .ok () ∧
    ensure (decide w.initial.Nodup) "witness: the initial layout is not injective" = .ok () := by
  simp only [applyWitnessQ'] at h
  obtain ⟨u1, h1, h⟩ := exceptBind_ok h
  obtain ⟨u2, h2, h⟩ := exceptBind_ok h
  obtain ⟨u3, h3, h⟩ := exceptBind_ok h
  obtain ⟨u4, h4, _⟩ := exceptBind_ok h
  exact ⟨h1, h2, h3, h4⟩

/-- PHASE2_SPEC §C.3 (26c1 L1) — **`applyWitnessQ_ok`**: the linear check implies the
reconstruction, so `applyWitness_sound` applies to its output unchanged. -/
theorem applyWitnessQ_ok (b : TargetBasis) (C : Circuit) (hC : C.WF) (w : Witness) (N : ℕ)
    (G : List BasisGate) (h : applyWitnessQ b C w N = .ok G) : applyWitness b C w N = .ok G := by
  simp only [applyWitnessQ] at h
  obtain ⟨q, hq, hG⟩ := exceptBind_ok h
  have hG := exceptPure_ok hG
  obtain ⟨st, hst, hlay, hvalid, hsteps⟩ := applyWitnessQ'_sim b C hC w N q hq
  obtain ⟨h1, h2, h3, h4⟩ := applyWitnessQ'_checks b C w N q hq
  have hlen : st.taken.length = (elements b C).length := (validReorder_perm _ _ _ _ hvalid).length_eq
  simp only [applyWitness]
  rw [h1, h2, h3, h4]
  simp only [bind, Except.bind]
  rw [hst]
  have e1 : ensure (st.taken.length == (elements b C).length) "order: not every element is executed" = .ok () := by
    simp [ensure, hlen, pure, Except.pure]
  have e2 : ensure (st.lay == w.final) "order: the final layout differs from the witness" = .ok () := by
    simp [ensure, hlay, pure, Except.pure]
  have e3 : ensure (validReorder (Elem.qubits (translate b C)) (Elem.bits (translate b C)) (elements b C) st.taken)
      "order: not a valid reordering of the dependency queues" = .ok () := by
    simp [ensure, hvalid, pure, Except.pure]
  dsimp only
  rw [e1]
  dsimp only
  rw [e2]
  dsimp only
  rw [e3]
  dsimp only
  rw [hsteps, hG]
  rfl

/-- PHASE2_SPEC §C.3 (26c1b) — the final layout permutation of a reconstruction, explicit:
the SWAPs of the steps applied to `σ₀`. -/
noncomputable def finalPerm (b : TargetBasis) (C : Circuit) (w : Witness) (N : ℕ)
    (σ₀ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N) :=
  irPerm N (stepsOf b C w N) * σ₀

/-- **`applyWitnessQ_sound`**: `applyWitness_sound` for the linear check, with `σ_f = finalPerm …`
a closed term (`layOf … (finalPerm …) = w.final` is then the kernel's). -/
theorem applyWitnessQ_sound (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ) (hC : C.WF)
    (G : List BasisGate) (hG : applyWitnessQ b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀) :
    w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) (finalPerm b C w _ σ₀) ∧
      ∀ ρ : MState (Reg C.nData × Reg C.nAnc),
        channelDenote (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G) (embed bb σ₀ ρ) =
          embed bb (finalPerm b C w _ σ₀) (channelDenote C.nData C.nAnc C ρ) := by
  have h := hG
  simp only [applyWitnessQ] at h
  obtain ⟨q, hq, hG'⟩ := exceptBind_ok h
  have hG' := exceptPure_ok hG'
  obtain ⟨st, hst, hlay, hvalid, hsteps⟩ := applyWitnessQ'_sim b C hC w _ q hq
  have hfp : finalPerm b C w _ σ₀ = irPerm _ st.steps * σ₀ := by
    simp only [finalPerm, stepsOf, hq, hsteps]
  rw [hfp]
  exact applyWitness_sound_core b C w bb hC G st hst hlay hvalid (by rw [hsteps]; exact hG') hWF hM σ₀ h₀

/-! ## L2: the layout as a permutation, the embedded |0⟩ -/

section LayPerm

/-- The layout list completed by the missing positions, in increasing order. -/
def fullOf (N : ℕ) (l : List ℕ) : List ℕ := l ++ (List.range N).filter (· ∉ l)

/-- A layout: injective, of length `k ≤ N`, inside the register. -/
def IsLayout (N k : ℕ) (l : List ℕ) : Prop := l.Nodup ∧ l.length = k ∧ k ≤ N ∧ ∀ x ∈ l, x < N

instance (N k : ℕ) (l : List ℕ) : Decidable (IsLayout N k l) := by unfold IsLayout; infer_instance

theorem fullOf_nodup (N : ℕ) (l : List ℕ) (hl : l.Nodup) : (fullOf N l).Nodup := by
  refine List.Nodup.append hl (List.Nodup.filter _ (List.nodup_range)) ?_
  intro x hx hx'
  exact (of_decide_eq_true (List.mem_filter.mp hx').2) hx

theorem fullOf_perm (N k : ℕ) (l : List ℕ) (h : IsLayout N k l) : (fullOf N l).Perm (List.range N) := by
  rw [List.perm_ext_iff_of_nodup (fullOf_nodup N l h.1) List.nodup_range]
  intro x
  simp only [fullOf, List.mem_append, List.mem_filter, List.mem_range]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · exact h.2.2.2 x hx
    · exact hx
  · intro hx
    by_cases hxl : x ∈ l
    · exact Or.inl hxl
    · exact Or.inr ⟨hx, by simpa using hxl⟩

theorem fullOf_length (N k : ℕ) (l : List ℕ) (h : IsLayout N k l) : (fullOf N l).length = N := by
  rw [(fullOf_perm N k l h).length_eq, List.length_range]

theorem fullOf_lt (N k : ℕ) (l : List ℕ) (h : IsLayout N k l) {x : ℕ} (hx : x ∈ fullOf N l) : x < N :=
  List.mem_range.mp ((fullOf_perm N k l h).subset hx)

/-- PHASE2_SPEC §C.3 (26c1 L2) — **`layPerm`**: the permutation of `Fin N` extending a layout list
(the layout on the first `k` positions, the missing positions after them in increasing order); `1`
when the list is not a layout. -/
noncomputable def layPerm (N k : ℕ) (l : List ℕ) : Equiv.Perm (Fin N) :=
  if h : IsLayout N k l then
    Equiv.ofBijective
      (fun i : Fin N => ⟨(fullOf N l)[i.val]'(by rw [fullOf_length N k l h]; exact i.isLt),
        fullOf_lt N k l h (List.getElem_mem _)⟩)
      (Finite.injective_iff_bijective.mp fun i j hij => by
        have := congrArg Fin.val hij
        simp only at this
        exact Fin.ext ((fullOf_nodup N l h.1).getElem_inj_iff.mp this))
  else 1

theorem layPerm_apply (N k : ℕ) (l : List ℕ) (h : IsLayout N k l) (i : Fin N) :
    ((layPerm N k l) i).val = (fullOf N l)[i.val]'(by rw [fullOf_length N k l h]; exact i.isLt) := by
  simp [layPerm, h]

/-- **`layOf_layPerm`**: the permutation extends the layout. -/
theorem layOf_layPerm (N k : ℕ) (l : List ℕ) (h : IsLayout N k l) : layOf N k (layPerm N k l) = l := by
  apply List.ext_getElem (by simp [layOf, h.2.1])
  intro i h1 h2
  simp only [layOf, List.getElem_map, List.getElem_range]
  have hi : i < N := by have := h.2.2.1; simp [layOf] at h1; omega
  rw [permFn_lt _ hi, layPerm_apply N k l h]
  simp only [fullOf]
  rw [List.getElem_append_left h2]

end LayPerm

section EmbedZero

open scoped MState

theorem Ket.basis_prod {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (i : d₁) (j : d₂) : Ket.basis i ⊗ᵠ Ket.basis j = Ket.basis (i, j) := by
  apply Ket.ext
  rintro ⟨x, y⟩
  simp only [Ket.apply, Ket.prod, Ket.basis, Prod.mk.injEq]
  by_cases hx : i = x <;> by_cases hy : j = y <;> simp [hx, hy]

theorem Ket.basis_relabel {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (e : d₂ ≃ d₁) (i : d₁) : (Ket.basis i).relabel e = Ket.basis (e.symm i) := by
  apply Ket.ext
  intro x
  rw [Ket.relabel_apply]
  simp [Ket.apply, Ket.basis, Equiv.symm_apply_eq]

/-- The all-|0⟩ state of a register. -/
theorem ancZero_eq (k : ℕ) : ancZero k = MState.pure (Ket.basis fun _ => false) := rfl

theorem embedEquiv_zero {n a : ℕ} (bb : ℕ) (σ : Equiv.Perm (Fin (n + (a + bb)))) :
    embedEquiv bb σ ((fun _ => false, fun _ => false) : Reg (n + (a + bb)) × Reg 0) =
      (((fun _ => false, fun _ => false), fun _ => false) : (Reg n × Reg a) × Reg bb) := rfl

/-- PHASE2_SPEC §C.3 (26c1 L2) — **`embed_zero`**: the embedded |0⟩ is the all-|0⟩ state of the
physical register, whatever the layout. -/
theorem embed_zero {n a : ℕ} (bb : ℕ) (σ : Equiv.Perm (Fin (n + (a + bb)))) :
    embed bb σ (ancZero n ⊗ᴹ ancZero a) = ancZero (n + (a + bb)) ⊗ᴹ ancZero 0 := by
  rw [embed_eq_relabel, ancZero_eq, ancZero_eq, ancZero_eq, ancZero_eq, ancZero_eq, ← MState.pure_prod_pure,
    ← MState.pure_prod_pure, ← MState.pure_prod_pure, MState.relabel_pure, Ket.basis_prod, Ket.basis_prod,
    Ket.basis_prod, Ket.basis_relabel]
  congr 2
  rw [Equiv.symm_apply_eq]
  exact (embedEquiv_zero bb σ).symm

end EmbedZero

end CQRV.Hardware
