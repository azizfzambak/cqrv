module

public import CQRV.Matching.Library

/-!
# CQRV.Matching.Complete

Report §4.2.1, Proposition 5.1 (i)–(ii), for the implemented fragment; PHASE2_SPEC.md §A.5
amendment (4) (Stage 21a2). The statements are about the existing algorithm — `millerMatch`,
`assign`, `matchAt`, `matchList`, `matchPrecondition` and `matchLibrary` are unchanged — on
normal forms, as `millerMatch_sound` is.

* **The fragment** (`MillerFragment`): `isMillerPattern`, and every metavariable occurs with one
  argument count (`uniformArity`). The second condition is necessary: `subst` ignores a binding's
  arity, so φ = `c(λ. F x₀, λλ. F x₀ x₁)` is solved by `F ↦ λ. x₀` although `millerMatch` builds
  the bindings `⟨1, x₀⟩` and `⟨2, x₀⟩` and fails (the `#guard` in `tests/CQRVTests/Matching.lean`).
* **The substitutions** (`Binding.WF`, `Subst.WFFor`): the binding of every metavariable has the
  arity of its occurrences, a body without metavariables whose free variables are below that
  arity, and a body its sort admits.
* (i) `millerMatch_complete` (the converse of `millerMatch_sound`) and `millerMatch_wf`;
  (i′) `matchers_agree` and `matchPrecondition_complete`; (ii) `library_match_unique`;
  (iii) `matchLibrary_noMatch` and `matchLibrary_matched`, collected for `library` as
  `matchLibrary_spec`. The cost bound (Proposition 5.1 (3)) is not formalized.

No Physlib import; Lean core and Mathlib list lemmas only.
-/

@[expose] public section

namespace CQRV.Matching

open Term

/-! ## E1 — the fragment, well-formed substitutions, side conditions, `Matches` -/

namespace Term

/-- PHASE2_SPEC §A.5 (4) — a ground term: no metavariable. -/
def Ground (t : Term) : Prop := t.hasAnyMVar = false

mutual
/-- PHASE2_SPEC §A.5 (4) — the metavariable occurrences of a term with their argument counts,
in left-to-right order (with repetitions; `mvars` is the first projection). -/
def mvarArities : Term → List (MVar × Nat)
  | .const _ args | .acSet args => mvarAritiesList args
  | .mvar m args => (m, args.length) :: mvarAritiesList args
  | .nat _ | .bvar _ => []
  | .lam b => mvarArities b
/-- `mvarArities` on a list. -/
def mvarAritiesList : List Term → List (MVar × Nat)
  | [] => []
  | t :: ts => mvarArities t ++ mvarAritiesList ts
end

/-- PHASE2_SPEC §A.5 (4) — every metavariable occurs with one argument count. -/
def uniformArity (φ : Term) : Bool :=
  φ.mvarArities.all fun p => φ.mvarArities.all fun q => p.1 != q.1 || p.2 == q.2

/-- PHASE2_SPEC §A.5 (4) — the argument count of `m` in `φ` (its first occurrence; under
`uniformArity` the count of every occurrence). -/
def arityIn (φ : Term) (m : MVar) : Nat := (φ.mvarArities.lookup m).getD 0

mutual
/-- PHASE2_SPEC §A.5 (4) — every free bound variable of the term is `< k`. -/
def closedBelow (k : Nat) : Term → Bool
  | .const _ args | .acSet args | .mvar _ args => closedBelowList k args
  | .nat _ => true
  | .bvar i => decide (i < k)
  | .lam b => closedBelow (k + 1) b
/-- `closedBelow` on a list. -/
def closedBelowList (k : Nat) : List Term → Bool
  | [] => true
  | t :: ts => closedBelow k t && closedBelowList k ts
end

end Term

instance (t : Term) : Decidable t.Ground := inferInstanceAs (Decidable (t.hasAnyMVar = false))

/-- PHASE2_SPEC §A.5 (4) — the fragment of Proposition 5.1: a Miller pattern with uniform arity. -/
def MillerFragment (φ : Term) : Prop := φ.isMillerPattern = true ∧ φ.uniformArity = true

instance (φ : Term) : Decidable (MillerFragment φ) :=
  inferInstanceAs (Decidable (φ.isMillerPattern = true ∧ φ.uniformArity = true))

/-- PHASE2_SPEC §A.5 (4) — a well-formed binding for a metavariable of sort `s` whose occurrences
have `k` arguments: arity `k`, a body without metavariables, free variables below `k`, a body the
sort admits. -/
def Binding.WF (k : Nat) (s : MSort) (b : Binding) : Prop :=
  b.arity = k ∧ b.body.hasAnyMVar = false ∧ b.body.closedBelow k = true ∧ s.admits b.body = true

instance (k : Nat) (s : MSort) (b : Binding) : Decidable (b.WF k s) := by
  unfold Binding.WF; infer_instance

/-- PHASE2_SPEC §A.5 (4) — `σ` is well formed for `φ`: every metavariable of `φ` has a binding
that is well formed for its arity in `φ` and its sort. -/
def Subst.WFFor (φ : Term) (σ : Subst) : Prop :=
  ∀ m ∈ φ.mvars, ∃ b, σ.lookup m = some b ∧ b.WF (φ.arityIn m) m.sort

/-- The same, occurrence by occurrence (the invariant of the inductions below). -/
def Subst.WFOcc (σ : Subst) (ps : List (MVar × Nat)) : Prop :=
  ∀ p ∈ ps, ∃ b, σ.lookup p.1 = some b ∧ b.WF p.2 p.1.sort

/-- Report §4.1.4 — the metavariables of a side condition. -/
def SideCond.mvars : SideCond → List MVar
  | .ge l r => l.mvars ++ r.mvars

/-- Report §4.1.4 — a side condition holds under `σ`: both sides are literals after
substitution and the inequality is true. -/
def SideCond.Holds (σ : Subst) : SideCond → Prop
  | .ge l r => ∃ a b, l.subst σ = .nat a ∧ r.subst σ = .nat b ∧ b ≤ a

/-- PHASE2_SPEC §A.5 (4) — the entry `e` matches `t`: a well-formed matcher of its normalized
precondition under which every side condition holds. -/
def Matches (e : LibEntry) (t : Term) : Prop :=
  ∃ σ : Subst, σ.WFFor (normalize e.precondition) ∧ (normalize e.precondition).subst σ = t ∧
    ∀ c ∈ e.sides, c.Holds σ

/-- Report §4.2.4 — is the result of Algorithm 2 a match? -/
def LibResult.isMatched : LibResult → Bool
  | .matched .. => true
  | _ => false

/-! ## Occurrences and arities -/

namespace Term

mutual
/-- `mvars` is the first projection of `mvarArities`. -/
theorem mvars_eq_map_fst : (t : Term) → t.mvars = t.mvarArities.map Prod.fst
  | .const _ as => by simp only [mvars, mvarArities]; exact mvarsList_eq_map_fst as
  | .acSet as => by simp only [mvars, mvarArities]; exact mvarsList_eq_map_fst as
  | .mvar m as => by simp only [mvars, mvarArities, List.map_cons]; rw [mvarsList_eq_map_fst as]
  | .nat _ | .bvar _ => rfl
  | .lam b => by simp only [mvars, mvarArities]; exact mvars_eq_map_fst b
/-- `mvars_eq_map_fst` on lists. -/
theorem mvarsList_eq_map_fst : (ts : List Term) → mvarsList ts = (mvarAritiesList ts).map Prod.fst
  | [] => rfl
  | t :: ts => by
    simp only [mvarsList, mvarAritiesList, List.map_append]
    rw [mvars_eq_map_fst t, mvarsList_eq_map_fst ts]
end

/-- Under `uniformArity`, `lookup` finds the count of every occurrence. -/
theorem lookup_eq_of_uniform {φ : Term} (hu : φ.uniformArity = true) {m : MVar} {k : Nat}
    (hmk : (m, k) ∈ φ.mvarArities) : φ.mvarArities.lookup m = some k := by
  have hall : ∀ p ∈ φ.mvarArities, p.1 = m → p.2 = k := by
    intro p hp hpm
    have h := (List.all_eq_true.1 hu) p hp
    have h' := (List.all_eq_true.1 h) (m, k) hmk
    simp only [hpm, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h'
    exact h'
  clear hu
  generalize φ.mvarArities = l at hmk hall ⊢
  revert hmk hall
  induction l with
  | nil => intro hmk _; exact absurd hmk List.not_mem_nil
  | cons p rest ih =>
    intro hmk hall
    obtain ⟨m', k'⟩ := p
    simp only [List.lookup_cons]
    split
    · rename_i h
      have := hall (m', k') List.mem_cons_self (beq_iff_eq.1 h).symm
      simp only at this; rw [this]
    · rename_i h
      have hne : m ≠ m' := beq_eq_false_iff_ne.1 h
      have hmem : (m, k) ∈ rest := by
        rcases List.mem_cons.1 hmk with h' | h'
        · exact absurd (congrArg Prod.fst h') hne
        · exact h'
      exact ih hmem fun q hq hqm => hall q (List.mem_cons_of_mem _ hq) hqm

/-- Under `uniformArity`, `arityIn` is the count of every occurrence. -/
theorem arityIn_eq {φ : Term} (hu : φ.uniformArity = true) {m : MVar} {k : Nat}
    (hmk : (m, k) ∈ φ.mvarArities) : φ.arityIn m = k := by
  simp only [arityIn, lookup_eq_of_uniform hu hmk, Option.getD_some]

end Term

/-- `WFFor` on a pattern of the fragment gives the occurrence-wise invariant. -/
theorem Subst.WFOcc_of_WFFor {φ : Term} {σ : Subst} (hf : MillerFragment φ) (hσ : σ.WFFor φ) :
    σ.WFOcc φ.mvarArities := by
  intro p hp
  have hm : p.1 ∈ φ.mvars := by
    rw [Term.mvars_eq_map_fst]; exact List.mem_map.2 ⟨p, hp, rfl⟩
  obtain ⟨b, hb, hwf⟩ := hσ p.1 hm
  refine ⟨b, hb, ?_⟩
  rwa [Term.arityIn_eq hf.2 (m := p.1) (k := p.2) hp] at hwf

/-- `Extends` preserves the occurrence-wise invariant. -/
theorem Subst.WFOcc.mono {σ σ' : Subst} {ps : List (MVar × Nat)} (h : σ.WFOcc ps)
    (hext : σ.Extends σ') : σ'.WFOcc ps := by
  intro p hp
  obtain ⟨b, hb, hwf⟩ := h p hp
  exact ⟨b, hext _ _ hb, hwf⟩

/-! ## Renaming and abstraction: the converse of `rename_abstr` -/

theorem liftO_liftR_inv {α : Nat → Option Nat} {ρ : Nat → Nat} {k : Nat}
    (h : ∀ j, j < k → α (ρ j) = some j) : ∀ j, j < k + 1 → liftO α (liftR ρ j) = some j := by
  intro j hj
  cases j with
  | zero => rfl
  | succ n => simp only [liftR, liftO, h n (Nat.lt_of_succ_lt_succ hj), Option.map_some]

theorem liftO_lt {α : Nat → Option Nat} {k : Nat} (h : ∀ i j, α i = some j → j < k) :
    ∀ i j, liftO α i = some j → j < k + 1 := by
  intro i j hij
  cases i with
  | zero => simp only [liftO, Option.some.injEq] at hij; subst hij; exact Nat.zero_lt_succ k
  | succ n =>
    simp only [liftO, Option.map_eq_some_iff] at hij
    obtain ⟨j', hj', rfl⟩ := hij
    exact Nat.succ_lt_succ (h n j' hj')

namespace Term

mutual
/-- The converse of `rename_abstr`: abstraction undoes renaming on a term whose free variables
are below `k`, when `α` inverts `ρ` below `k`. -/
theorem abstr_rename : (b : Term) → (α : Nat → Option Nat) → (ρ : Nat → Nat) → (k : Nat) →
    (∀ j, j < k → α (ρ j) = some j) → closedBelow k b = true → abstr α (rename ρ b) = some b
  | .const c as, α, ρ, k, h, hc => by
    simp only [rename, abstr, abstrList_renameList as α ρ k h hc, Option.map_some]
  | .nat n, α, ρ, k, h, hc => rfl
  | .bvar i, α, ρ, k, h, hc => by
    simp only [closedBelow, decide_eq_true_eq] at hc
    simp only [rename, abstr, h i hc, Option.map_some]
  | .lam b, α, ρ, k, h, hc => by
    simp only [closedBelow] at hc
    simp only [rename, abstr, abstr_rename b (liftO α) (liftR ρ) (k + 1) (liftO_liftR_inv h) hc,
      Option.map_some]
  | .mvar m as, α, ρ, k, h, hc => by
    simp only [rename, abstr, abstrList_renameList as α ρ k h hc, Option.map_some]
  | .acSet as, α, ρ, k, h, hc => by
    simp only [rename, abstr, abstrList_renameList as α ρ k h hc, Option.map_some]
/-- `abstr_rename` on lists. -/
theorem abstrList_renameList : (bs : List Term) → (α : Nat → Option Nat) → (ρ : Nat → Nat) →
    (k : Nat) → (∀ j, j < k → α (ρ j) = some j) → closedBelowList k bs = true →
    abstrList α (renameList ρ bs) = some bs
  | [], α, ρ, k, h, hc => rfl
  | b :: bs, α, ρ, k, h, hc => by
    simp only [closedBelowList, Bool.and_eq_true] at hc
    simp only [renameList, abstrList, abstr_rename b α ρ k h hc.1,
      abstrList_renameList bs α ρ k h hc.2]
end

mutual
/-- The result of `abstr` has its free variables below `k` when `α` maps into `[0, k)`. -/
theorem closedBelow_abstr : (t : Term) → (α : Nat → Option Nat) → (k : Nat) →
    (∀ i j, α i = some j → j < k) → ∀ b, abstr α t = some b → closedBelow k b = true
  | .const c as, α, k, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [closedBelow]; exact closedBelowList_abstrList as α k h as' h'
  | .nat n, α, k, h, b, hb => by
    simp only [abstr, Option.some.injEq] at hb; subst hb; rfl
  | .bvar i, α, k, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp only [closedBelow, decide_eq_true_eq]; exact h i j hj
  | .lam t, α, k, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨b', h', rfl⟩ := hb
    simp only [closedBelow]; exact closedBelow_abstr t (liftO α) (k + 1) (liftO_lt h) b' h'
  | .mvar m as, α, k, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [closedBelow]; exact closedBelowList_abstrList as α k h as' h'
  | .acSet as, α, k, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [closedBelow]; exact closedBelowList_abstrList as α k h as' h'
/-- `closedBelow_abstr` on lists. -/
theorem closedBelowList_abstrList : (ts : List Term) → (α : Nat → Option Nat) → (k : Nat) →
    (∀ i j, α i = some j → j < k) → ∀ bs, abstrList α ts = some bs → closedBelowList k bs = true
  | [], α, k, h, bs, hb => by
    simp only [abstrList, Option.some.injEq] at hb; subst hb; rfl
  | t :: ts, α, k, h, bs, hb => by
    simp only [abstrList] at hb
    split at hb
    · rename_i t' ts' e1 e2
      simp only [Option.some.injEq] at hb; subst hb
      simp only [closedBelowList, Bool.and_eq_true]
      exact ⟨closedBelow_abstr t α k h t' e1, closedBelowList_abstrList ts α k h ts' e2⟩
    · simp at hb
end

mutual
/-- Renaming does not change the metavariables. -/
theorem hasAnyMVar_rename : (t : Term) → (ρ : Nat → Nat) → hasAnyMVar (rename ρ t) = hasAnyMVar t
  | .const c as, ρ => by simp only [rename, hasAnyMVar]; exact hasAnyMVarList_renameList as ρ
  | .nat n, ρ => rfl
  | .bvar i, ρ => rfl
  | .lam b, ρ => by simp only [rename, hasAnyMVar]; exact hasAnyMVar_rename b (liftR ρ)
  | .mvar m as, ρ => rfl
  | .acSet as, ρ => by simp only [rename, hasAnyMVar]; exact hasAnyMVarList_renameList as ρ
/-- `hasAnyMVar_rename` on lists. -/
theorem hasAnyMVarList_renameList : (ts : List Term) → (ρ : Nat → Nat) →
    hasAnyMVarList (renameList ρ ts) = hasAnyMVarList ts
  | [], ρ => rfl
  | t :: ts, ρ => by
    simp only [renameList, hasAnyMVarList]
    rw [hasAnyMVar_rename t ρ, hasAnyMVarList_renameList ts ρ]
end

mutual
/-- Abstraction does not change the metavariables. -/
theorem hasAnyMVar_abstr : (t : Term) → (α : Nat → Option Nat) → ∀ b, abstr α t = some b →
    hasAnyMVar b = hasAnyMVar t
  | .const c as, α, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [hasAnyMVar]; exact hasAnyMVarList_abstrList as α as' h'
  | .nat n, α, b, hb => by
    simp only [abstr, Option.some.injEq] at hb; subst hb; rfl
  | .bvar i, α, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨j, _, rfl⟩ := hb; rfl
  | .lam t, α, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨b', h', rfl⟩ := hb
    simp only [hasAnyMVar]; exact hasAnyMVar_abstr t (liftO α) b' h'
  | .mvar m as, α, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', _, rfl⟩ := hb; rfl
  | .acSet as, α, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [hasAnyMVar]; exact hasAnyMVarList_abstrList as α as' h'
/-- `hasAnyMVar_abstr` on lists. -/
theorem hasAnyMVarList_abstrList : (ts : List Term) → (α : Nat → Option Nat) → ∀ bs,
    abstrList α ts = some bs → hasAnyMVarList bs = hasAnyMVarList ts
  | [], α, bs, hb => by
    simp only [abstrList, Option.some.injEq] at hb; subst hb; rfl
  | t :: ts, α, bs, hb => by
    simp only [abstrList] at hb
    split at hb
    · rename_i t' ts' e1 e2
      simp only [Option.some.injEq] at hb; subst hb
      simp only [hasAnyMVarList]
      rw [hasAnyMVar_abstr t α t' e1, hasAnyMVarList_abstrList ts α ts' e2]
    · simp at hb
end

mutual
/-- A ground term has no particular metavariable. -/
theorem hasMVar_eq_false_of_ground : (t : Term) → (m : MVar) → hasAnyMVar t = false →
    hasMVar m t = false
  | .const c as, m, h => by
    simp only [hasAnyMVar] at h; simp only [hasMVar]; exact hasMVarList_eq_false_of_ground as m h
  | .nat n, m, h => rfl
  | .bvar i, m, h => rfl
  | .lam b, m, h => by
    simp only [hasAnyMVar] at h; simp only [hasMVar]; exact hasMVar_eq_false_of_ground b m h
  | .mvar m' as, m, h => by simp [hasAnyMVar] at h
  | .acSet as, m, h => by
    simp only [hasAnyMVar] at h; simp only [hasMVar]; exact hasMVarList_eq_false_of_ground as m h
/-- `hasMVar_eq_false_of_ground` on lists. -/
theorem hasMVarList_eq_false_of_ground : (ts : List Term) → (m : MVar) →
    hasAnyMVarList ts = false → hasMVarList m ts = false
  | [], m, h => rfl
  | t :: ts, m, h => by
    simp only [hasAnyMVarList, Bool.or_eq_false_iff] at h
    simp only [hasMVarList, Bool.or_eq_false_iff]
    exact ⟨hasMVar_eq_false_of_ground t m h.1, hasMVarList_eq_false_of_ground ts m h.2⟩
end

/-- Renaming preserves "a list of literals". -/
theorem all_isNat_renameList (ρ : Nat → Nat) : (as : List Term) →
    (as.all fun | .nat _ => true | _ => false) = true →
    ((renameList ρ as).all fun | .nat _ => true | _ => false) = true
  | [], _ => rfl
  | a :: as, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [renameList, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, all_isNat_renameList ρ as h.2⟩
    cases a <;> simp_all [rename]

/-- Renaming preserves the sort test. -/
theorem admits_rename {s : MSort} {t : Term} (ρ : Nat → Nat) (h : s.admits t = true) :
    s.admits (rename ρ t) = true := by
  cases s with
  | any => cases t <;> rfl
  | nat =>
    cases t <;> try (exfalso; simp [MSort.admits] at h; done)
    rfl
  | natSet =>
    cases t <;> try (exfalso; simp [MSort.admits] at h; done)
    exact all_isNat_renameList ρ _ h

/-- Abstraction preserves "a list of literals". -/
theorem all_isNat_abstrList (α : Nat → Option Nat) : (as bs : List Term) →
    abstrList α as = some bs → (as.all fun | .nat _ => true | _ => false) = true →
    (bs.all fun | .nat _ => true | _ => false) = true
  | [], bs, hb, _ => by
    simp only [abstrList, Option.some.injEq] at hb; subst hb; rfl
  | a :: as, bs, hb, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    simp only [abstrList] at hb
    split at hb
    · rename_i a' as' e1 e2
      simp only [Option.some.injEq] at hb; subst hb
      rw [List.all_cons, Bool.and_eq_true]
      refine ⟨?_, all_isNat_abstrList α as as' e2 h.2⟩
      cases a <;> try (exfalso; simp at h; done)
      simp only [abstr, Option.some.injEq] at e1; subst e1; rfl
    · simp at hb

/-- Abstraction preserves the sort test. -/
theorem admits_abstr {s : MSort} {t b : Term} {α : Nat → Option Nat} (hb : abstr α t = some b)
    (h : s.admits t = true) : s.admits b = true := by
  cases s with
  | any => cases b <;> rfl
  | nat =>
    cases t <;> try (exfalso; simp [MSort.admits] at h; done)
    simp only [abstr, Option.some.injEq] at hb; subst hb; rfl
  | natSet =>
    cases t <;> try (exfalso; simp [MSort.admits] at h; done)
    rename_i as
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨bs, hbs, rfl⟩ := hb
    exact all_isNat_abstrList α as bs hbs h

/-- `substList` preserves the length. -/
theorem substList_length (σ : Subst) : (as : List Term) → (substList σ as).length = as.length
  | [] => rfl
  | a :: as => by simp only [substList, List.length_cons, substList_length σ as]

mutual
/-- Two substitutions that agree on the metavariables of `t` give the same instance. -/
theorem subst_congr : (t : Term) → (σ τ : Subst) → (∀ m ∈ t.mvars, σ.lookup m = τ.lookup m) →
    t.subst σ = t.subst τ
  | .const c as, σ, τ, h => by
    simp only [subst]; rw [substList_congr as σ τ h]
  | .nat n, σ, τ, h => rfl
  | .bvar i, σ, τ, h => rfl
  | .lam b, σ, τ, h => by simp only [subst]; rw [subst_congr b σ τ h]
  | .mvar m as, σ, τ, h => by
    have hm := h m (by simp [mvars])
    simp only [subst, hm]
    split
    · rfl
    · rw [substList_congr as σ τ fun m' hm' => h m' (by simp only [mvars]; exact List.mem_cons_of_mem _ hm')]
  | .acSet as, σ, τ, h => by
    simp only [subst]; rw [substList_congr as σ τ h]
/-- `subst_congr` on lists. -/
theorem substList_congr : (ts : List Term) → (σ τ : Subst) →
    (∀ m ∈ mvarsList ts, σ.lookup m = τ.lookup m) → substList σ ts = substList τ ts
  | [], σ, τ, h => rfl
  | t :: ts, σ, τ, h => by
    simp only [substList]
    rw [subst_congr t σ τ fun m hm => h m (by simp only [mvarsList]; exact List.mem_append_left _ hm),
      substList_congr ts σ τ fun m hm => h m (by simp only [mvarsList]; exact List.mem_append_right _ hm)]
end

mutual
/-- The instance of a pattern under a well-formed substitution is ground. -/
theorem subst_ground : (t : Term) → (σ : Subst) → σ.WFOcc t.mvarArities →
    hasAnyMVar (t.subst σ) = false
  | .const c as, σ, h => by
    simp only [subst, hasAnyMVar]; exact substList_ground as σ h
  | .nat n, σ, h => rfl
  | .bvar i, σ, h => rfl
  | .lam b, σ, h => by simp only [subst, hasAnyMVar]; exact subst_ground b σ h
  | .mvar m as, σ, h => by
    obtain ⟨b, hb, hwf⟩ := h (m, as.length) (by simp [mvarArities])
    simp only [subst, hb, hasAnyMVar_rename]
    exact hwf.2.1
  | .acSet as, σ, h => by
    simp only [subst, hasAnyMVar]; exact substList_ground as σ h
/-- `subst_ground` on lists. -/
theorem substList_ground : (ts : List Term) → (σ : Subst) → σ.WFOcc (mvarAritiesList ts) →
    hasAnyMVarList (substList σ ts) = false
  | [], σ, h => rfl
  | t :: ts, σ, h => by
    simp only [substList, hasAnyMVarList, Bool.or_eq_false_iff]
    exact ⟨subst_ground t σ fun p hp => h p (by simp only [mvarAritiesList]; exact List.mem_append_left _ hp),
      substList_ground ts σ fun p hp => h p (by simp only [mvarAritiesList]; exact List.mem_append_right _ hp)⟩
end

end Term

/-! ## Bound-variable argument lists -/

/-- In a `Nodup` list, `indexOf?` inverts `getD`. -/
theorem indexOf?_getD_of_nodup : (is : List Nat) → is.Nodup → ∀ j, j < is.length →
    indexOf? is (is.getD j 0) = some j
  | [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | x :: xs, hnd, j, hj => by
    have hnd' := List.nodup_cons.1 hnd
    cases j with
    | zero => simp [indexOf?]
    | succ n =>
      have hn : n < xs.length := Nat.lt_of_succ_lt_succ hj
      have hmem : xs.getD n 0 ∈ xs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
        exact List.getElem_mem hn
      have hne : x ≠ xs.getD n 0 := fun h => hnd'.1 (h ▸ hmem)
      simp only [List.getD_cons_succ, indexOf?, hne, ↓reduceIte,
        indexOf?_getD_of_nodup xs hnd'.2 n hn, Option.map_some]

/-- `indexOf?` returns a position. -/
theorem indexOf?_lt : (is : List Nat) → ∀ i j, indexOf? is i = some j → j < is.length
  | [], i, j, h => by simp [indexOf?] at h
  | x :: xs, i, j, h => by
    simp only [indexOf?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Nat.zero_lt_succ _
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact Nat.succ_lt_succ (indexOf?_lt xs i k hk)

/-- The index list of a metavariable application has the arguments' length. -/
theorem mapM_bvarIdx?_length {as : List Term} {is : List Nat} (h : as.mapM bvarIdx? = some is) :
    is.length = as.length := by
  rw [← mapM_bvarIdx? as is h, List.length_map]

/-- Bound-variable arguments carry no metavariable occurrence. -/
theorem mvarAritiesList_eq_nil_of_bvars : (as : List Term) → (is : List Nat) →
    as.mapM bvarIdx? = some is → mvarAritiesList as = []
  | [], _, _ => rfl
  | a :: as, is, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    cases a <;> simp only [bvarIdx?] at hx <;> try simp at hx
    simp only [mvarAritiesList, mvarArities, List.nil_append]
    exact mvarAritiesList_eq_nil_of_bvars as xs hxs

/-- A Miller-pattern metavariable application: distinct bound variables. -/
theorem isMillerAt_mvar {c : Nat} {inAC : Bool} {m : MVar} {args : List Term}
    (h : isMillerAt c inAC (.mvar m args) = true) :
    ∃ is, args.mapM bvarIdx? = some is ∧ is.Nodup := by
  simp only [isMillerAt, Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  split at h
  · rename_i is his
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨is, his, h.2⟩
  · simp at h

/-! ## Completeness of `assign` and Algorithm 1 -/

/-- Report §4.1.2, steps 2–4 — `assign` succeeds on the instance of `F args` under a
well-formed binding of `F`, and its result stays inside the given matcher. -/
theorem assign_complete {path : Path} {m : MVar} {args : List Term} {is : List Nat}
    {σ σ₀ : Subst} {b : Binding} (his : args.mapM bvarIdx? = some is) (hnd : is.Nodup)
    (hb : σ.lookup m = some b) (hwf : b.WF args.length m.sort)
    (hg : ((Term.mvar m args).subst σ).Ground) (hext : σ₀.Extends σ) :
    ∃ σ₁, assign path m args ((Term.mvar m args).subst σ) σ₀ = .ok σ₁ ∧ σ₁.Extends σ := by
  obtain ⟨harity, hgb, hclosed, hadm⟩ := hwf
  have hlen := mapM_bvarIdx?_length his
  have ht : (Term.mvar m args).subst σ = b.body.rename fun j => is.getD j 0 := by
    simp only [Term.subst, hb, mapM_bvarIdx? args is his]
  rw [ht] at hg ⊢
  have habs : abstr (indexOf? is) (b.body.rename fun j => is.getD j 0) = some b.body :=
    Term.abstr_rename b.body _ _ is.length (indexOf?_getD_of_nodup is hnd) (hlen ▸ harity ▸ hclosed)
  have hmv : (b.body.rename fun j => is.getD j 0).hasMVar m = false :=
    Term.hasMVar_eq_false_of_ground _ m hg
  have heta : b = ⟨is.length, b.body⟩ := by cases b; simp_all
  unfold assign
  simp only [his, Term.admits_rename _ hadm, habs, hmv, Bool.false_eq_true, ↓reduceIte]
  split
  · refine ⟨_, rfl, ?_⟩
    intro m' b' hb'
    simp only [Subst.lookup] at hb'
    split at hb'
    · subst_vars; simp only [Option.some.injEq] at hb'; subst hb'; rw [← heta]; exact hb
    · exact hext m' b' hb'
  · rename_i b'' hb''
    have : b'' = b := by
      have := hext m b'' hb''; rw [hb] at this; exact Option.some.inj this.symm
    subst this
    simp only [eq_true heta, ↓reduceIte]
    exact ⟨σ₀, rfl, hext⟩

mutual
/-- Report §4.2.1, Proposition 5.1 (i) — Algorithm 1 succeeds on the instance of a pattern of
the fragment under a well-formed matcher, from any partial result inside that matcher, and its
result stays inside it. -/
theorem matchAt_complete : (path : Path) → (p : Term) → (c : Nat) → (inAC : Bool) →
    (σ σ₀ : Subst) → isMillerAt c inAC p = true → σ.WFOcc p.mvarArities →
    (p.subst σ).Ground → σ₀.Extends σ →
    ∃ σ₁, matchAt path p (p.subst σ) σ₀ = .ok σ₁ ∧ σ₁.Extends σ
  | path, .mvar m args, c, inAC, σ, σ₀, hmil, hocc, hg, hext => by
    obtain ⟨is, his, hnd⟩ := isMillerAt_mvar hmil
    obtain ⟨b, hb, hwf⟩ := hocc (m, args.length) (by simp [mvarArities])
    simp only [matchAt]
    exact assign_complete his hnd hb hwf hg hext
  | path, .const c as, d, inAC, σ, σ₀, hmil, hocc, hg, hext => by
    simp only [Term.subst, matchAt, Term.substList_length, and_self, ↓reduceIte]
    exact matchList_complete path 0 as d inAC σ σ₀ hmil hocc hg hext
  | path, .nat a, c, inAC, σ, σ₀, _, _, _, hext => ⟨σ₀, by simp [Term.subst, matchAt], hext⟩
  | path, .bvar i, c, inAC, σ, σ₀, _, _, _, hext => ⟨σ₀, by simp [Term.subst, matchAt], hext⟩
  | path, .lam a, c, inAC, σ, σ₀, hmil, hocc, hg, hext => by
    simp only [Term.subst, matchAt]
    exact matchAt_complete (path ++ [0]) a (c + 1) inAC σ σ₀ hmil hocc hg hext
  | path, .acSet as, c, inAC, σ, σ₀, hmil, hocc, hg, hext => by
    simp only [Term.subst, matchAt, Term.substList_length, ↓reduceIte]
    exact matchList_complete path 0 as c true σ σ₀ hmil hocc hg hext
/-- `matchAt_complete` on argument lists. -/
theorem matchList_complete : (path : Path) → (k : Nat) → (ps : List Term) → (c : Nat) →
    (inAC : Bool) → (σ σ₀ : Subst) → isMillerList c inAC ps = true →
    σ.WFOcc (mvarAritiesList ps) → hasAnyMVarList (substList σ ps) = false → σ₀.Extends σ →
    ∃ σ₁, matchList path k ps (substList σ ps) σ₀ = .ok σ₁ ∧ σ₁.Extends σ
  | path, k, [], c, inAC, σ, σ₀, _, _, _, hext => ⟨σ₀, rfl, hext⟩
  | path, k, p :: ps, c, inAC, σ, σ₀, hmil, hocc, hg, hext => by
    simp only [isMillerList, Bool.and_eq_true] at hmil
    simp only [substList, hasAnyMVarList, Bool.or_eq_false_iff] at hg
    obtain ⟨σ₁, h₁, hext₁⟩ := matchAt_complete (path ++ [k]) p c inAC σ σ₀ hmil.1
      (fun q hq => hocc q (by simp only [mvarAritiesList]; exact List.mem_append_left _ hq)) hg.1 hext
    obtain ⟨σ₂, h₂, hext₂⟩ := matchList_complete path (k + 1) ps c inAC σ σ₁ hmil.2
      (fun q hq => hocc q (by simp only [mvarAritiesList]; exact List.mem_append_right _ hq)) hg.2 hext₁
    refine ⟨σ₂, ?_, hext₂⟩
    simp only [substList, matchList, h₁, h₂]
end

/-- Report §4.2.1, Proposition 5.1 (i), the converse of `millerMatch_sound` (PHASE2_SPEC §A.5
(4)): for φ in the fragment and a ground `t`, a well-formed matcher of φ against `t` makes
`millerMatch φ t` succeed, with a result inside that matcher. -/
theorem millerMatch_complete_extends {φ t : Term} {σ : Subst} (hf : MillerFragment φ)
    (ht : t.Ground) (hσ : σ.WFFor φ) (he : φ.subst σ = t) :
    ∃ σ', millerMatch φ t = .ok σ' ∧ σ'.Extends σ := by
  subst he
  have hmil : isMillerAt 0 false φ = true := by
    have := hf.1; simp only [isMillerPattern, Bool.and_eq_true] at this; exact this.1
  exact matchAt_complete [] φ 0 false σ [] hmil (Subst.WFOcc_of_WFFor hf hσ) ht
    (fun _ _ h => by simp [Subst.lookup] at h)

/-- Report §4.2.1, Proposition 5.1 (i) — `millerMatch_complete`: the match set is non-empty
only if Algorithm 1 succeeds. -/
theorem millerMatch_complete {φ t : Term} {σ : Subst} (hf : MillerFragment φ) (ht : t.Ground)
    (hσ : σ.WFFor φ) (he : φ.subst σ = t) : ∃ σ', millerMatch φ t = .ok σ' :=
  let ⟨σ', h, _⟩ := millerMatch_complete_extends hf ht hσ he
  ⟨σ', h⟩

/-! ## Well-formedness of the matcher's own result -/

/-- Report §4.1.2, steps 2–4 — a successful `assign` binds `F` to a well-formed binding, with
bound-variable arguments. -/
theorem assign_wf {path : Path} {m : MVar} {args : List Term} {t : Term} {σ₀ σ₁ : Subst}
    (h : assign path m args t σ₀ = .ok σ₁) (ht : t.Ground) :
    (∃ is, args.mapM bvarIdx? = some is) ∧
      ∃ b, σ₁.lookup m = some b ∧ b.WF args.length m.sort := by
  unfold assign at h
  split at h
  · simp at h
  · rename_i is his
    refine ⟨⟨is, his⟩, ?_⟩
    have hlen := mapM_bvarIdx?_length his
    split at h
    · rename_i hadm
      split at h
      · simp at h
      · rename_i body hbody
        split at h
        · simp at h
        · have hwf : Binding.WF args.length m.sort ⟨is.length, body⟩ :=
            ⟨hlen, by rw [Term.hasAnyMVar_abstr t _ body hbody]; exact ht,
              hlen ▸ Term.closedBelow_abstr t _ is.length (indexOf?_lt is) body hbody,
              Term.admits_abstr hbody hadm⟩
          split at h
          · simp only [Except.ok.injEq] at h; subst h
            exact ⟨_, by simp [Subst.lookup], hwf⟩
          · rename_i b hb
            split at h
            · simp only [Except.ok.injEq] at h; subst h
              rename_i heq; subst heq
              exact ⟨_, hb, hwf⟩
            · simp at h
    · simp at h

mutual
/-- Report §4.2.1 — the result of Algorithm 1 on a ground term is well formed at every
metavariable occurrence of the pattern. -/
theorem matchAt_wf : (path : Path) → (p t : Term) → (σ₀ σ₁ : Subst) →
    matchAt path p t σ₀ = .ok σ₁ → t.Ground → σ₁.WFOcc p.mvarArities
  | path, .mvar m args, t, σ₀, σ₁, h, ht => by
    simp only [matchAt] at h
    obtain ⟨⟨is, his⟩, b, hb, hwf⟩ := assign_wf h ht
    intro q hq
    simp only [mvarArities, mvarAritiesList_eq_nil_of_bvars args is his, List.mem_singleton] at hq
    subst hq
    exact ⟨b, hb, hwf⟩
  | path, .const c as, t, σ₀, σ₁, h, ht => by
    cases t with
    | const d bs =>
      simp only [matchAt] at h
      split at h
      · exact matchList_wf path 0 as bs σ₀ σ₁ h ht
      · simp at h
    | _ => simp [matchAt] at h
  | path, .nat a, t, σ₀, σ₁, h, ht => fun q hq => by simp [mvarArities] at hq
  | path, .bvar i, t, σ₀, σ₁, h, ht => fun q hq => by simp [mvarArities] at hq
  | path, .lam a, t, σ₀, σ₁, h, ht => by
    cases t with
    | lam b => simp only [matchAt] at h; exact matchAt_wf _ a b σ₀ σ₁ h ht
    | _ => simp [matchAt] at h
  | path, .acSet as, t, σ₀, σ₁, h, ht => by
    cases t with
    | acSet bs =>
      simp only [matchAt] at h
      split at h
      · exact matchList_wf path 0 as bs σ₀ σ₁ h ht
      · simp at h
    | _ => simp [matchAt] at h
/-- `matchAt_wf` on argument lists. -/
theorem matchList_wf : (path : Path) → (k : Nat) → (ps ts : List Term) → (σ₀ σ₁ : Subst) →
    matchList path k ps ts σ₀ = .ok σ₁ → hasAnyMVarList ts = false →
    σ₁.WFOcc (mvarAritiesList ps)
  | path, k, [], ts, σ₀, σ₁, h, ht => fun q hq => by simp [mvarAritiesList] at hq
  | path, k, p :: ps, ts, σ₀, σ₁, h, ht => by
    cases ts with
    | nil => simp [matchList] at h
    | cons t ts =>
      simp only [hasAnyMVarList, Bool.or_eq_false_iff] at ht
      simp only [matchList] at h
      split at h
      · rename_i σ' h'
        have h₁ := (matchAt_wf _ p t σ₀ σ' h' ht.1).mono (matchList_extends path (k + 1) ps ts σ' σ₁ h)
        have h₂ := matchList_wf path (k + 1) ps ts σ' σ₁ h ht.2
        intro q hq
        simp only [mvarAritiesList] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact h₁ q hq
        · exact h₂ q hq
      · simp at h
end

/-- Report §4.2.1, Proposition 5.1 (i) (PHASE2_SPEC §A.5 (4)) — the matcher's own result is in
the match set: it is well formed for φ. -/
theorem millerMatch_wf {φ t : Term} {σ' : Subst} (hf : MillerFragment φ) (ht : t.Ground)
    (h : millerMatch φ t = .ok σ') : σ'.WFFor φ := by
  intro m hm
  rw [Term.mvars_eq_map_fst] at hm
  obtain ⟨⟨m', k⟩, hmk, hm'⟩ := List.mem_map.1 hm
  simp only at hm'; subst hm'
  obtain ⟨b, hb, hwf⟩ := matchAt_wf [] φ t [] σ' h ht (m', k) hmk
  exact ⟨b, hb, by rw [Term.arityIn_eq hf.2 hmk]; exact hwf⟩

/-- Report §4.2.1, Proposition 5.1 (i′) (PHASE2_SPEC §A.5 (4)) — two well-formed matchers of a
pattern of the fragment agree on its metavariables: the match set of one entry is a singleton. -/
theorem matchers_agree {φ t : Term} {σ τ : Subst} (hf : MillerFragment φ) (hσ : σ.WFFor φ)
    (hτ : τ.WFFor φ) (heσ : φ.subst σ = t) (heτ : φ.subst τ = t) :
    ∀ m ∈ φ.mvars, σ.lookup m = τ.lookup m := by
  have ht : t.Ground := heσ ▸ Term.subst_ground φ σ (Subst.WFOcc_of_WFFor hf hσ)
  obtain ⟨σ', h₁, hext₁⟩ := millerMatch_complete_extends hf ht hσ heσ
  obtain ⟨σ'', h₂, hext₂⟩ := millerMatch_complete_extends hf ht hτ heτ
  rw [h₁] at h₂
  have := Except.ok.inj h₂; subst this
  have hwf := millerMatch_wf hf ht h₁
  intro m hm
  obtain ⟨b, hb, _⟩ := hwf m hm
  rw [hext₁ m b hb, hext₂ m b hb]

/-! ## Side conditions and `matchPrecondition` -/

/-- An Except-valued `mapM` succeeds when every element does. -/
theorem mapM_ok_of_forall {α β ε : Type} (f : α → Except ε β) : (cs : List α) →
    (∀ c ∈ cs, ∃ d, f c = .ok d) → ∃ ds, cs.mapM f = .ok ds
  | [], _ => ⟨[], rfl⟩
  | c :: cs, h => by
    obtain ⟨d, hd⟩ := h c List.mem_cons_self
    obtain ⟨ds, hds⟩ := mapM_ok_of_forall f cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    exact ⟨d :: ds, by rw [List.mapM_cons, hd, hds]; rfl⟩

/-- An Except-valued `mapM` that succeeds succeeded on every element. -/
theorem forall_ok_of_mapM {α β ε : Type} (f : α → Except ε β) : (cs : List α) → (ds : List β) →
    cs.mapM f = .ok ds → ∀ c ∈ cs, ∃ d, f c = .ok d
  | [], _, _, c, hc => absurd hc List.not_mem_nil
  | c :: cs, ds, h, c', hc' => by
    rw [List.mapM_cons] at h
    change Except.bind (f c) _ = _ at h
    cases hfc : f c with
    | error e => rw [hfc] at h; simp [Except.bind] at h
    | ok d =>
      rw [hfc] at h
      simp only [Except.bind] at h
      change Except.bind (cs.mapM f) _ = _ at h
      cases hm : cs.mapM f with
      | error e => rw [hm] at h; simp [Except.bind] at h
      | ok ds' =>
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨d, hfc⟩
        · exact forall_ok_of_mapM f cs ds' hm c' hc'

/-- Report §4.1.4 — a side condition that holds is discharged. -/
theorem discharge_ok_of_holds {φ : Term} {σ : Subst} {c : SideCond} (h : c.Holds σ) :
    ∃ d, c.discharge φ σ = .ok d := by
  obtain ⟨l, r⟩ := c
  obtain ⟨a, b, hl, hr, hab⟩ := h
  simp only [SideCond.discharge, hl, hr, hab, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- Report §4.1.4 — a discharged side condition holds. -/
theorem holds_of_discharge_ok {φ : Term} {σ : Subst} {c : SideCond} {d : Discharged}
    (h : c.discharge φ σ = .ok d) : c.Holds σ := by
  obtain ⟨l, r⟩ := c
  simp only [SideCond.discharge] at h
  split at h
  · rename_i a b hl hr
    split at h
    · exact ⟨a, b, hl, hr, by assumption⟩
    · simp at h
  · simp at h

/-- Report §4.1.4, Proposition 5.1 (i′) — with side conditions over φ's metavariables that hold
under a well-formed matcher, `matchPrecondition` succeeds: the matcher's result agrees with
that matcher on every metavariable of the conditions. -/
theorem matchPrecondition_complete {φ t : Term} {σ : Subst} {sides : List SideCond}
    (hf : MillerFragment φ) (ht : t.Ground) (hσ : σ.WFFor φ) (he : φ.subst σ = t)
    (hsub : ∀ c ∈ sides, c.mvars ⊆ φ.mvars) (hholds : ∀ c ∈ sides, c.Holds σ) :
    ∃ r, matchPrecondition φ sides t = .ok r := by
  obtain ⟨σ', h₁, hext⟩ := millerMatch_complete_extends hf ht hσ he
  have hwf := millerMatch_wf hf ht h₁
  have hagree : ∀ m ∈ φ.mvars, σ'.lookup m = σ.lookup m := by
    intro m hm
    obtain ⟨b, hb, _⟩ := hwf m hm
    rw [hb, hext m b hb]
  have hholds' : ∀ c ∈ sides, c.Holds σ' := by
    intro c hc
    obtain ⟨l, r⟩ := c
    obtain ⟨a, b, hl, hr, hab⟩ := hholds _ hc
    have hsub' := hsub _ hc
    simp only [SideCond.mvars] at hsub'
    refine ⟨a, b, ?_, ?_, hab⟩
    · rw [Term.subst_congr l σ' σ fun m hm => hagree m (hsub' (List.mem_append_left _ hm))]; exact hl
    · rw [Term.subst_congr r σ' σ fun m hm => hagree m (hsub' (List.mem_append_right _ hm))]; exact hr
  obtain ⟨ds, hds⟩ := mapM_ok_of_forall (SideCond.discharge φ σ') sides
    fun c hc => discharge_ok_of_holds (hholds' c hc)
  refine ⟨(σ', ds), ?_⟩
  unfold matchPrecondition
  rw [h₁]
  show (sides.mapM (SideCond.discharge φ σ') >>= fun ds => pure (σ', ds)) = _
  rw [hds]
  rfl

/-- Report §4.1.4 — a successful `matchPrecondition` is a successful `millerMatch` whose
substitution discharges every side condition. -/
theorem matchPrecondition_ok {φ t : Term} {sides : List SideCond} {σ : Subst}
    {ds : List Discharged} (h : matchPrecondition φ sides t = .ok (σ, ds)) :
    millerMatch φ t = .ok σ ∧ ∀ c ∈ sides, c.Holds σ := by
  unfold matchPrecondition at h
  change Except.bind (millerMatch φ t) _ = _ at h
  cases hm : millerMatch φ t with
  | error e => rw [hm] at h; simp [Except.bind] at h
  | ok σ' =>
    rw [hm] at h
    simp only [Except.bind] at h
    change Except.bind (sides.mapM _) _ = _ at h
    cases hds : sides.mapM (SideCond.discharge φ σ') with
    | error e => rw [hds] at h; simp [Except.bind] at h
    | ok ds' =>
      rw [hds] at h
      simp only [Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun c hc => ?_⟩
      obtain ⟨d, hd⟩ := forall_ok_of_mapM _ sides ds' hds c hc
      exact holds_of_discharge_ok hd

/-! ## Algorithm 2 -/

/-- The hypothesis of Proposition 5.1 (iii) on a library: every precondition is in the fragment
and every side condition is over its metavariables. -/
def LibFragment (lib : List LibEntry) : Prop :=
  ∀ e ∈ lib, MillerFragment (normalize e.precondition) ∧
    ∀ c ∈ e.sides, c.mvars ⊆ (normalize e.precondition).mvars

instance (lib : List LibEntry) : Decidable (LibFragment lib) :=
  inferInstanceAs (Decidable (∀ e ∈ lib, MillerFragment (normalize e.precondition) ∧
    ∀ c ∈ e.sides, c.mvars ⊆ (normalize e.precondition).mvars))

/-- The entry test of `matchLibrary`, as a function. -/
def matchEntry (t : Term) (e : LibEntry) : Option LibResult :=
  match matchPrecondition (normalize e.precondition) e.sides t with
  | .ok (σ, ds) => some (LibResult.matched e σ ds)
  | .error _ => none

theorem matchEntry_eq_some {t : Term} {e : LibEntry} {r : LibResult}
    (h : matchEntry t e = some r) :
    ∃ σ ds, matchPrecondition (normalize e.precondition) e.sides t = .ok (σ, ds) ∧
      r = .matched e σ ds := by
  unfold matchEntry at h
  split at h
  · rename_i σ ds hok
    simp only [Option.some.injEq] at h; subst h
    exact ⟨σ, ds, hok, rfl⟩
  · simp at h

theorem matchEntry_eq_none {t : Term} {e : LibEntry} (h : matchEntry t e = none) :
    ∀ r, matchPrecondition (normalize e.precondition) e.sides t ≠ .ok r := by
  intro r hr
  unfold matchEntry at h
  rw [hr] at h
  simp at h

/-- A near-miss record is never a match. -/
theorem nearMiss_ne_matched (e : LibEntry) (f : MatchFailure) (t : Term) (e' : LibEntry)
    (σ : Subst) (ds : List Discharged) : nearMiss e f t ≠ .matched e' σ ds := by
  intro h
  unfold nearMiss at h
  dsimp only at h
  cases h

/-- The scan `go` returns a match only from its accumulator or from an entry it matched. -/
theorem go_matched (t : Term) : (es : List LibEntry) → (best : LibResult) → (e : LibEntry) →
    (σ : Subst) → (ds : List Discharged) → matchLibrary.go t es best = .matched e σ ds →
    best = .matched e σ ds ∨
      ∃ e' ∈ es, matchPrecondition (normalize e'.precondition) e'.sides t = .ok (σ, ds) ∧ e' = e
  | [], best, e, σ, ds, h => by simp only [matchLibrary.go] at h; exact Or.inl h
  | e₀ :: es, best, e, σ, ds, h => by
    simp only [matchLibrary.go] at h
    split at h
    · rename_i σ' ds' hok
      simp only [LibResult.matched.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨e₀, List.mem_cons_self, hok, rfl⟩
    · rename_i f hf
      have step : ∀ best', (best' = nearMiss e₀ f t ∨ best' = best) →
          matchLibrary.go t es best' = .matched e σ ds →
          best = .matched e σ ds ∨
            ∃ e' ∈ e₀ :: es, matchPrecondition (normalize e'.precondition) e'.sides t = .ok (σ, ds) ∧ e' = e := by
        intro best' hb h'
        rcases go_matched t es best' e σ ds h' with h'' | ⟨e', he', hok, rfl⟩
        · rcases hb with rfl | rfl
          · exact absurd h'' (nearMiss_ne_matched _ _ _ _ _ _)
          · exact Or.inl h''
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hok, rfl⟩
      split at h
      · rename_i d d' _ _
        split at h
        · exact step _ (Or.inl rfl) h
        · exact step _ (Or.inr rfl) h
      · exact step _ (Or.inl rfl) h

/-- The sorted library of `matchLibrary`. -/
theorem mem_sorted {lib : List LibEntry} {e : LibEntry} :
    e ∈ lib.mergeSort (fun a b => a.priority ≤ b.priority) ↔ e ∈ lib := List.mem_mergeSort

/-- Report §4.2.4, Proposition 5.1 (iii) — a matching entry makes Algorithm 2 return a match. -/
theorem matchLibrary_isMatched_of_matches {lib : List LibEntry} {t : Term} (hlib : LibFragment lib)
    (ht : t.Ground) {e : LibEntry} (he : e ∈ lib) (hm : Matches e t) :
    (matchLibrary lib t).isMatched = true := by
  obtain ⟨σ, hσ, hsub, hholds⟩ := hm
  obtain ⟨hf, hsides⟩ := hlib e he
  obtain ⟨r, hr⟩ := matchPrecondition_complete hf ht hσ hsub hsides hholds
  unfold matchLibrary
  dsimp only
  split
  · rename_i r' hr'
    obtain ⟨a, _, ha⟩ := List.exists_of_findSome?_eq_some hr'
    obtain ⟨σ', ds', _, rfl⟩ := matchEntry_eq_some (r := r') (e := a) (t := t) ha
    rfl
  · rename_i hn
    have := (List.findSome?_eq_none_iff.1 hn) e (mem_sorted.2 he)
    exact absurd hr (matchEntry_eq_none this r)

/-- Report §4.2.4, Proposition 5.1 (iii) (PHASE2_SPEC §A.5 (4)) — `matchLibrary_noMatch`: a
non-`matched` result means that no entry matches. -/
theorem matchLibrary_noMatch {lib : List LibEntry} {t : Term} (hlib : LibFragment lib)
    (ht : t.Ground) (h : (matchLibrary lib t).isMatched = false) :
    ∀ e ∈ lib, ¬ Matches e t := by
  intro e he hm
  rw [matchLibrary_isMatched_of_matches hlib ht he hm] at h
  exact Bool.noConfusion h

/-- Report §4.2.4, Proposition 5.1 (iii) (PHASE2_SPEC §A.5 (4)) — `matchLibrary_matched`: a
`matched e σ ds` result names an entry of the library that `t` matches, witnessed by σ itself,
and every well-formed matcher of that entry agrees with σ on its metavariables. -/
theorem matchLibrary_matched {lib : List LibEntry} {t : Term} (hlib : LibFragment lib)
    (ht : t.Ground) {e : LibEntry} {σ : Subst} {ds : List Discharged}
    (h : matchLibrary lib t = .matched e σ ds) :
    e ∈ lib ∧ Matches e t ∧
      ∀ τ : Subst, τ.WFFor (normalize e.precondition) → (normalize e.precondition).subst τ = t →
        ∀ m ∈ (normalize e.precondition).mvars, τ.lookup m = σ.lookup m := by
  have key : e ∈ lib ∧ matchPrecondition (normalize e.precondition) e.sides t = .ok (σ, ds) := by
    unfold matchLibrary at h
    dsimp only at h
    split at h
    · rename_i r' hr'
      subst h
      obtain ⟨a, ha, hae⟩ := List.exists_of_findSome?_eq_some hr'
      obtain ⟨σ', ds', hok, heq⟩ := matchEntry_eq_some (t := t) (e := a) hae
      simp only [LibResult.matched.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨mem_sorted.1 ha, hok⟩
    · rename_i hn
      rcases go_matched t _ _ e σ ds h with h' | ⟨e', he', hok, rfl⟩
      · cases h'
      · have hmem : e' ∈ lib.mergeSort fun a b => a.priority ≤ b.priority := by
          split at he'
          · exact he'
          · exact (List.mem_filter.1 he').1
        have := (List.findSome?_eq_none_iff.1 hn) e' hmem
        exact absurd hok (matchEntry_eq_none this _)
  obtain ⟨he, hok⟩ := key
  obtain ⟨hf, _⟩ := hlib e he
  obtain ⟨hmm, hholds⟩ := matchPrecondition_ok hok
  have hwf := millerMatch_wf hf ht hmm
  refine ⟨he, ⟨σ, hwf, millerMatch_sound hmm, hholds⟩, ?_⟩
  intro τ hτ heτ m hm
  exact (matchers_agree hf hwf hτ (millerMatch_sound hmm) heτ m hm).symm

/-! ## The library -/

/-- PHASE2_SPEC §A.5 (4) — both entries satisfy the hypothesis of `matchLibrary_noMatch`. -/
theorem library_fragment : LibFragment library := by decide

/-- Two entries whose normalized preconditions are `sig` applications with different class
constants or different argument counts are never both matched by one term. -/
theorem not_matches_both {e₁ e₂ : LibEntry} {t : Term} {c k₁ k₂ : String} {as bs : List Term}
    (h₁ : normalize e₁.precondition = .const c (.const k₁ [] :: as))
    (h₂ : normalize e₂.precondition = .const c (.const k₂ [] :: bs))
    (hne : k₁ ≠ k₂ ∨ as.length ≠ bs.length) (m₁ : Matches e₁ t) (m₂ : Matches e₂ t) : False := by
  obtain ⟨σ, _, hσ, _⟩ := m₁
  obtain ⟨τ, _, hτ, _⟩ := m₂
  rw [h₁] at hσ; rw [h₂] at hτ
  rw [← hτ] at hσ
  simp only [Term.subst, Term.substList, Term.const.injEq, List.cons.injEq, true_and, and_true] at hσ
  obtain ⟨hk, hl⟩ := hσ
  have hlen := congrArg List.length hl
  rw [Term.substList_length, Term.substList_length] at hlen
  rcases hne with hne | hne
  · exact hne hk
  · exact hne hlen

/-- Report §4.2.1, Proposition 5.1 (ii) (PHASE2_SPEC §A.5 (4)) — two entries of `library` never
both match: the class constant and the argument count separate them. -/
theorem library_match_unique {t : Term} : ∀ e₁ ∈ library, ∀ e₂ ∈ library,
    Matches e₁ t → Matches e₂ t → e₁ = e₂ := by
  have hG : normalize groverEntry.precondition =
      .const "sig" (.const "Search" [] ::
        [.mvar F₁ [], .mvar F₂ [], .const "→" [.const "Bool^" [.mvar F₁ []], .const "Bool" []],
         .const "bounded" [.mvar F₃ []],
         .const "PhaseKickback" [.const "Multiplicative" [], .mvar F₄ []]]) := by decide
  have hC : normalize countEntry.precondition =
      .const "sig" (.const "Count" [] ::
        [.mvar F₁ [], .mvar F₆ [], .const "→" [.const "Bool^" [.mvar F₁ []], .const "Bool" []],
         .const "bounded" [.mvar F₃ []],
         .const "PhaseKickback" [.const "Multiplicative" [], .mvar F₄ []], .mvar F₅ []]) := by decide
  intro e₁ h₁ e₂ h₂ m₁ m₂
  simp only [library, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · rfl
  · exact (not_matches_both hG hC (Or.inl (by decide)) m₁ m₂).elim
  · exact (not_matches_both hC hG (Or.inl (by decide)) m₁ m₂).elim
  · rfl

/-! ## The CLI's terms are ground -/

namespace Term

theorem hasAnyMVarList_append : (l₁ l₂ : List Term) →
    hasAnyMVarList (l₁ ++ l₂) = (hasAnyMVarList l₁ || hasAnyMVarList l₂)
  | [], l₂ => by simp [hasAnyMVarList]
  | t :: l₁, l₂ => by
    simp only [List.cons_append, hasAnyMVarList, hasAnyMVarList_append l₁ l₂, Bool.or_assoc]

theorem hasAnyMVarList_eq_false_iff : (l : List Term) →
    (hasAnyMVarList l = false ↔ ∀ t ∈ l, hasAnyMVar t = false)
  | [] => by simp [hasAnyMVarList]
  | t :: l => by
    simp only [hasAnyMVarList, Bool.or_eq_false_iff, List.mem_cons, forall_eq_or_imp]
    rw [hasAnyMVarList_eq_false_iff l]

theorem mem_dedupAdj : (l : List Term) → ∀ x ∈ dedupAdj l, x ∈ l
  | [], x, h => by simp [dedupAdj] at h
  | [a], x, h => by simpa [dedupAdj] using h
  | a :: b :: rest, x, h => by
    simp only [dedupAdj] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedupAdj (b :: rest) x h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupAdj (b :: rest) x h)

theorem hasAnyMVarList_flattenAC : (l : List Term) → hasAnyMVarList l = false →
    hasAnyMVarList (flattenAC l) = false
  | [], _ => rfl
  | t :: rest, h => by
    simp only [hasAnyMVarList, Bool.or_eq_false_iff] at h
    cases t with
    | acSet bs =>
      simp only [flattenAC, hasAnyMVarList_append, Bool.or_eq_false_iff]
      exact ⟨h.1, hasAnyMVarList_flattenAC rest h.2⟩
    | _ =>
      simp only [flattenAC, hasAnyMVarList, Bool.or_eq_false_iff]
      exact ⟨h.1, hasAnyMVarList_flattenAC rest h.2⟩

theorem hasAnyMVarList_canonAC {l : List Term} (h : hasAnyMVarList l = false) :
    hasAnyMVarList (canonAC l) = false := by
  rw [hasAnyMVarList_eq_false_iff]
  intro x hx
  have hx' : x ∈ l := List.mem_mergeSort.1 (mem_dedupAdj _ x hx)
  exact (hasAnyMVarList_eq_false_iff l).1 h x hx'

mutual
/-- Normalization preserves groundness. -/
theorem hasAnyMVar_normalize : (t : Term) → hasAnyMVar t = false → hasAnyMVar (normalize t) = false
  | .const c as, h => by
    simp only [normalize, hasAnyMVar] at *; exact hasAnyMVarList_normalizeList as h
  | .acSet as, h => by
    simp only [normalize, hasAnyMVar] at *
    exact hasAnyMVarList_canonAC (hasAnyMVarList_flattenAC _ (hasAnyMVarList_normalizeList as h))
  | .lam b, h => by simp only [normalize, hasAnyMVar] at *; exact hasAnyMVar_normalize b h
  | .mvar m as, h => by simp [hasAnyMVar] at h
  | .nat n, _ => rfl
  | .bvar i, _ => rfl
/-- `hasAnyMVar_normalize` on lists. -/
theorem hasAnyMVarList_normalizeList : (ts : List Term) → hasAnyMVarList ts = false →
    hasAnyMVarList (normalizeList ts) = false
  | [], _ => rfl
  | t :: ts, h => by
    simp only [normalizeList, hasAnyMVarList, Bool.or_eq_false_iff] at h ⊢
    exact ⟨hasAnyMVar_normalize t h.1, hasAnyMVarList_normalizeList ts h.2⟩
end

end Term

/-- A list of literals is ground. -/
theorem hasAnyMVarList_map_nat : (s : List Nat) → hasAnyMVarList (s.map Term.nat) = false
  | [] => rfl
  | _ :: s => by simp only [List.map_cons, hasAnyMVarList, hasAnyMVar, Bool.false_or]; exact hasAnyMVarList_map_nat s

/-- A surface type is a ground term. -/
theorem tyTerm_ground (τ : CQRV.DSL.Ty) : hasAnyMVar (tyTerm τ) = false := by
  cases τ <;> rfl

/-- The domain is a ground term. -/
theorem domTerm_ground : (τs : List CQRV.DSL.Ty) → hasAnyMVar (domTerm τs) = false
  | [] => rfl
  | [τ] => tyTerm_ground τ
  | τ₁ :: τ₂ :: τs => by
    simp only [domTerm, hasAnyMVar]
    rw [Term.hasAnyMVarList_eq_false_iff]
    intro t ht
    obtain ⟨τ, _, rfl⟩ := List.mem_map.1 ht
    exact tyTerm_ground τ

/-- Report §7.2.2, Proposition 5.1 (iii) — the CLI's terms are ground: σ_in has no metavariable,
and normalization adds none. So `matchLibrary_spec` applies to every term `cqr` matches. -/
theorem _root_.CQRV.DSL.SigmaIn.toTerm_ground (s : CQRV.DSL.SigmaIn) : s.toTerm.normalize.Ground := by
  apply Term.hasAnyMVar_normalize
  unfold CQRV.DSL.SigmaIn.toTerm
  simp only [hasAnyMVar, Term.hasAnyMVarList_append, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · simp only [hasAnyMVarList, hasAnyMVar, Bool.false_or, Bool.or_eq_false_iff, domTerm_ground,
      tyTerm_ground, and_true]
    refine ⟨?_, ?_, ?_⟩
    · split <;> rfl
    · cases s.iter <;> rfl
    · cases s.oracle with
      | phaseKickback a sup =>
        cases a
        simp only [CQRV.DSL.OracleStructure.toTerm, hasAnyMVar, hasAnyMVarList, Bool.false_or,
          Bool.or_false]
        exact hasAnyMVarList_map_nat sup
      | block => rfl
      | blackBox => rfl
  · split <;> rfl

/-! ## Proposition 5.1 for the library -/

/-- Report §4.2.1, Proposition 5.1 (i)–(ii) for the implemented fragment (PHASE2_SPEC §A.5 (4)),
collected for `library` and a ground `t`: on `matched e σ _`, `e` is an entry of the library, `t`
matches it (σ is a witness), no other entry matches, and every well-formed matcher of `e` agrees
with σ on its metavariables; otherwise no entry matches. The cost bound (Proposition 5.1 (3)) is
documented, not formalized. -/
theorem matchLibrary_spec (t : Term) (ht : t.Ground) :
    (∀ e σ ds, matchLibrary library t = .matched e σ ds →
      e ∈ library ∧ Matches e t ∧ (∀ e' ∈ library, Matches e' t → e' = e) ∧
        ∀ τ : Subst, τ.WFFor (normalize e.precondition) → (normalize e.precondition).subst τ = t →
          ∀ m ∈ (normalize e.precondition).mvars, τ.lookup m = σ.lookup m) ∧
    ((matchLibrary library t).isMatched = false → ∀ e ∈ library, ¬ Matches e t) := by
  refine ⟨fun e σ ds h => ?_, matchLibrary_noMatch library_fragment ht⟩
  obtain ⟨he, hm, hagree⟩ := matchLibrary_matched library_fragment ht h
  exact ⟨he, hm, fun e' he' hm' => library_match_unique e' he' e he hm' hm, hagree⟩

end CQRV.Matching

end
