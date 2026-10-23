module

public import CQRV.Matching.Normalize

/-!
# CQRV.Matching.Miller

Report §4.1.2, Algorithm 1 (Miller-pattern unification, revised steps) and §4.1.4 (arithmetic
side conditions evaluated after substitution), §4.2.1 (Proposition 5.1: the match set is empty
or a singleton). `millerMatch φ t` matches a pattern φ against a term t (the ground signature
σ_in in practice), both in normal form:

1. rigid decomposition (`matchAt`, `matchList`);
2. flexible-rigid assignment with the scope check (`assign`: `abstr` fails on a bound variable
   that is not among the metavariable's arguments) and the sort check of the multi-sorted
   signature (§4.1.1, Table 1);
3. occurs check;
4. consistency of repeated metavariables (syntactic equality of the bindings);
5. no equational reasoning: both sides were normalized before step 1 (`Normalize.lean`).

The result type `Except MatchFailure Subst` is itself "empty or singleton": there is no
backtracking and no list of matchers.
-/

@[expose] public section

namespace CQRV.Matching

open Term

/-- Report §4.1.2 — the binding of a metavariable `F` applied to `arity` bound variables:
`F ↦ λx₁…x_arity. body`, where the free variable `j` of `body` stands for the `j`-th
argument. A nullary binding (`arity = 0`) is a plain term, e.g. `F₁ ↦ 8`. -/
structure Binding where
  arity : Nat
  body : Term
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.2 — a substitution: an association list of bindings (most recent first). -/
abbrev Subst := List (MVar × Binding)

/-- Report §4.1.2 — the binding of `m` in `σ`, if any. -/
def Subst.lookup : Subst → MVar → Option Binding
  | [], _ => none
  | (m', b) :: σ, m => if m' = m then some b else Subst.lookup σ m

/-- Report §4.1.2 — `σ'` extends `σ`: every binding of `σ` is a binding of `σ'`. -/
def Subst.Extends (σ σ' : Subst) : Prop :=
  ∀ m b, σ.lookup m = some b → σ'.lookup m = some b

/-! ## Renaming and abstraction of bound variables -/

/-- Lift a renaming of free bound variables under one binder. -/
def liftR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Lift a partial renaming of free bound variables under one binder. -/
def liftO (α : Nat → Option Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => (α n).map (· + 1)

namespace Term

mutual
/-- Rename the free bound variables of a term by `ρ`. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .const c as => .const c (renameList ρ as)
  | .nat n => .nat n
  | .bvar i => .bvar (ρ i)
  | .lam b => .lam (rename (liftR ρ) b)
  | .mvar m as => .mvar m (renameList ρ as)
  | .acSet as => .acSet (renameList ρ as)
/-- `rename` on a list. -/
def renameList (ρ : Nat → Nat) : List Term → List Term
  | [] => []
  | t :: ts => rename ρ t :: renameList ρ ts
end

mutual
/-- Report §4.1.2, step 2 (scope check) — rename the free bound variables of a term by the
partial map `α`; `none` when a free bound variable is outside the domain of `α`. -/
def abstr (α : Nat → Option Nat) : Term → Option Term
  | .const c as => (abstrList α as).map (.const c)
  | .nat n => some (.nat n)
  | .bvar i => (α i).map .bvar
  | .lam b => (abstr (liftO α) b).map .lam
  | .mvar m as => (abstrList α as).map (.mvar m)
  | .acSet as => (abstrList α as).map .acSet
/-- `abstr` on a list. -/
def abstrList (α : Nat → Option Nat) : List Term → Option (List Term)
  | [] => some []
  | t :: ts =>
    match abstr α t, abstrList α ts with
    | some t', some ts' => some (t' :: ts')
    | _, _ => none
end

mutual
/-- Report §4.1.2 — apply a substitution: `F x_{i₁} … x_{i_k}` with `F ↦ λ^k. b` becomes `b`
with its free variable `j` renamed to `i_j`. -/
def subst (σ : Subst) : Term → Term
  | .const c as => .const c (substList σ as)
  | .nat n => .nat n
  | .bvar i => .bvar i
  | .lam b => .lam (subst σ b)
  | .mvar m as =>
    match σ.lookup m with
    | some b => b.body.rename fun j => (as.map bvarIdx).getD j 0
    | none => .mvar m (substList σ as)
  | .acSet as => .acSet (substList σ as)
/-- `subst` on a list. -/
def substList (σ : Subst) : List Term → List Term
  | [] => []
  | t :: ts => subst σ t :: substList σ ts
end

end Term

/-- Position of `i` in a list of bound-variable indices. -/
def indexOf? : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, i => if x = i then some 0 else (indexOf? xs i).map (· + 1)

/-- Report §4.1.1, Table 1 — does a metavariable of sort `s` range over `t`? -/
def MSort.admits : MSort → Term → Bool
  | .nat, .nat _ => true
  | .natSet, .acSet as => as.all fun | .nat _ => true | _ => false
  | .any, _ => true
  | _, _ => false

/-! ## Failures and side conditions -/

/-- Report §4.1.4 — an arithmetic side condition, evaluated after substitution. -/
inductive SideCond where
  /-- `lhs ≥ rhs` on natural numbers -/
  | ge (lhs rhs : Term)
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.4 — rendering, e.g. `F₂ ≥ 1`. -/
def SideCond.render : SideCond → String
  | .ge l r => l.render ++ " ≥ " ++ r.render

/-- Report §4.1.2 — why Algorithm 1 failed. -/
inductive Reason where
  /-- step 1: different rigid symbols (or a value outside the metavariable's sort) -/
  | clash
  /-- step 2: a bound variable outside the metavariable's arguments -/
  | scope
  /-- step 3: the metavariable occurs in the candidate binding -/
  | occurs
  /-- step 4: a repeated metavariable receives two different bindings -/
  | inconsistent
  /-- §4.1.4: a side condition is false (or not a ground arithmetic fact) after substitution -/
  | sideCondition
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.2 — JSON / text name of a failure reason. -/
def Reason.name : Reason → String
  | .clash => "clash"
  | .scope => "scope"
  | .occurs => "occurs"
  | .inconsistent => "inconsistent"
  | .sideCondition => "side_condition"

/-- Report §4.1.2, §4.3.2 — a match failure: the failing position in φ, the reason, the
pattern subterm and the subterm of t found there, and the failed side condition, if any. -/
structure MatchFailure where
  path : Path
  reason : Reason
  expected : Term
  found : Term
  cond : Option SideCond := none
  deriving Repr, DecidableEq, Inhabited

/-! ## Algorithm 1 -/

/-- Report §4.1.2, steps 2–4 — assign `t` to the metavariable application `F args`. -/
def assign (path : Path) (m : MVar) (args : List Term) (t : Term) (σ : Subst) :
    Except MatchFailure Subst :=
  match args.mapM bvarIdx? with
  | none => .error ⟨path, .scope, .mvar m args, t, none⟩
  | some is =>
    if m.sort.admits t then
      match abstr (indexOf? is) t with
      | none => .error ⟨path, .scope, .mvar m args, t, none⟩
      | some body =>
        if t.hasMVar m then .error ⟨path, .occurs, .mvar m args, t, none⟩
        else
          match σ.lookup m with
          | none => .ok ((m, ⟨is.length, body⟩) :: σ)
          | some b =>
            if b = ⟨is.length, body⟩ then .ok σ
            else .error ⟨path, .inconsistent, .mvar m args, t, none⟩
    else .error ⟨path, .clash, .mvar m args, t, none⟩

mutual
/-- Report §4.1.2, step 1 — rigid decomposition; metavariable positions go to `assign`. -/
def matchAt (path : Path) : Term → Term → Subst → Except MatchFailure Subst
  | .mvar m args, t, σ => assign path m args t σ
  | .const c as, .const d bs, σ =>
    if c = d ∧ as.length = bs.length then matchList path 0 as bs σ
    else .error ⟨path, .clash, .const c as, .const d bs, none⟩
  | .nat a, .nat b, σ => if a = b then .ok σ else .error ⟨path, .clash, .nat a, .nat b, none⟩
  | .bvar i, .bvar j, σ => if i = j then .ok σ else .error ⟨path, .clash, .bvar i, .bvar j, none⟩
  | .lam a, .lam b, σ => matchAt (path ++ [0]) a b σ
  | .acSet as, .acSet bs, σ =>
    if as.length = bs.length then matchList path 0 as bs σ
    else .error ⟨path, .clash, .acSet as, .acSet bs, none⟩
  | p, t, _ => .error ⟨path, .clash, p, t, none⟩
/-- Report §4.1.2, step 1 — decomposition of argument lists; `k` is the index of the head. -/
def matchList (path : Path) (k : Nat) : List Term → List Term → Subst → Except MatchFailure Subst
  | [], [], σ => .ok σ
  | a :: as, b :: bs, σ =>
    match matchAt (path ++ [k]) a b σ with
    | .ok σ₁ => matchList path (k + 1) as bs σ₁
    | .error e => .error e
  | as, bs, _ => .error ⟨path, .clash, .acSet as, .acSet bs, none⟩
end

/-- Report §4.1.2, Algorithm 1 — Miller-pattern matching of φ against t (both normalized). -/
def millerMatch (φ : Term) (t : Term) : Except MatchFailure Subst :=
  matchAt [] φ t []

/-- Report §4.1.4 — a side condition discharged after substitution, with its proof (recorded
in the certificate). -/
structure Discharged where
  cond : SideCond
  lhs : Nat
  rhs : Nat
  holds : rhs ≤ lhs

/-- Report §4.1.4 — the ground fact, e.g. `32 ≥ 1`. -/
def Discharged.render (d : Discharged) : String := s!"{d.lhs} ≥ {d.rhs}"

/-- Report §4.1.4 — evaluate a side condition after substitution: both sides must be ground
literals, then `rhs ≤ lhs` is decided. On failure: the path of the condition's first
metavariable in φ. -/
def SideCond.discharge (φ : Term) (σ : Subst) : SideCond → Except MatchFailure Discharged
  | .ge l r =>
    let path := match l.mvars ++ r.mvars with
      | m :: _ => ((φ.mvarPaths []).lookup m).getD []
      | [] => []
    match l.subst σ, r.subst σ with
    | .nat a, .nat b =>
      if h : b ≤ a then .ok ⟨.ge l r, a, b, h⟩
      else .error ⟨path, .sideCondition, l, .nat a, some (.ge l r)⟩
    | l', _ => .error ⟨path, .sideCondition, l, l', some (.ge l r)⟩

/-- Report §4.1.2 + §4.1.4 — Algorithm 1, then the side conditions after substitution. -/
def matchPrecondition (φ : Term) (sides : List SideCond) (t : Term) :
    Except MatchFailure (Subst × List Discharged) := do
  let σ ← millerMatch φ t
  let ds ← sides.mapM (SideCond.discharge φ σ)
  return (σ, ds)

/-! ## Soundness (report §4.1.2: a returned substitution is a matcher) -/

theorem liftO_liftR {α : Nat → Option Nat} {ρ : Nat → Nat}
    (h : ∀ i j, α i = some j → ρ j = i) : ∀ i j, liftO α i = some j → liftR ρ j = i := by
  intro i j hij
  cases i with
  | zero => simp only [liftO, Option.some.injEq] at hij; subst hij; rfl
  | succ n =>
    simp only [liftO, Option.map_eq_some_iff] at hij
    obtain ⟨k, hk, rfl⟩ := hij
    simp [liftR, h n k hk]

namespace Term

mutual
/-- Renaming undoes abstraction when `ρ` inverts `α`. -/
theorem rename_abstr : (t : Term) → (α : Nat → Option Nat) → (ρ : Nat → Nat) →
    (∀ i j, α i = some j → ρ j = i) → ∀ b, abstr α t = some b → rename ρ b = t
  | .const c as, α, ρ, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [rename, renameList_abstrList as α ρ h as' h']
  | .nat n, α, ρ, h, b, hb => by
    simp only [abstr, Option.some.injEq] at hb; subst hb; rfl
  | .bvar i, α, ρ, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp [rename, h i j hj]
  | .lam t, α, ρ, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨b', h', rfl⟩ := hb
    simp only [rename, rename_abstr t (liftO α) (liftR ρ) (liftO_liftR h) b' h']
  | .mvar m as, α, ρ, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [rename, renameList_abstrList as α ρ h as' h']
  | .acSet as, α, ρ, h, b, hb => by
    simp only [abstr, Option.map_eq_some_iff] at hb
    obtain ⟨as', h', rfl⟩ := hb
    simp only [rename, renameList_abstrList as α ρ h as' h']
/-- `rename_abstr` on lists. -/
theorem renameList_abstrList : (ts : List Term) → (α : Nat → Option Nat) → (ρ : Nat → Nat) →
    (∀ i j, α i = some j → ρ j = i) → ∀ bs, abstrList α ts = some bs → renameList ρ bs = ts
  | [], α, ρ, h, bs, hb => by
    simp only [abstrList, Option.some.injEq] at hb; subst hb; rfl
  | t :: ts, α, ρ, h, bs, hb => by
    simp only [abstrList] at hb
    split at hb
    · rename_i t' ts' e1 e2
      simp only [Option.some.injEq] at hb; subst hb
      simp only [renameList, rename_abstr t α ρ h t' e1, renameList_abstrList ts α ρ h ts' e2]
    · simp at hb
end

end Term

theorem indexOf?_getD : ∀ (is : List Nat) (i j : Nat), indexOf? is i = some j → is.getD j 0 = i
  | [], _, _, h => by simp [indexOf?] at h
  | x :: xs, i, j, h => by
    simp only [indexOf?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simpa
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      simpa using indexOf?_getD xs i k hk

theorem mapM_bvarIdx? : ∀ (as : List Term) (is : List Nat),
    as.mapM bvarIdx? = some is → as.map bvarIdx = is
  | [], is, h => by simp_all
  | a :: as, is, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp [bvarIdx, hx, mapM_bvarIdx? as xs hxs]

theorem Subst.Extends.refl (σ : Subst) : σ.Extends σ := fun _ _ h => h

theorem Subst.Extends.trans {σ₁ σ₂ σ₃ : Subst} (h₁ : σ₁.Extends σ₂) (h₂ : σ₂.Extends σ₃) :
    σ₁.Extends σ₃ := fun m b h => h₂ m b (h₁ m b h)

/-- Report §4.1.2, step 4 — `assign` only adds bindings. -/
theorem assign_extends {path m args t σ σ'} (h : assign path m args t σ = .ok σ') :
    σ.Extends σ' := by
  unfold assign at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · rename_i hnone
            simp only [Except.ok.injEq] at h; subst h
            intro m' b' hb'
            simp only [Subst.lookup]
            split
            · subst_vars; simp_all
            · exact hb'
          · split at h
            · simp only [Except.ok.injEq] at h; subst h; exact Subst.Extends.refl _
            · simp at h
    · simp at h

/-- Report §4.1.2, steps 2–4 — after `assign`, every extension maps `F args` to `t`. -/
theorem assign_sound {path m args t σ σ'} (h : assign path m args t σ = .ok σ') :
    ∀ τ, σ'.Extends τ → (Term.mvar m args).subst τ = t := by
  intro τ hτ
  unfold assign at h
  split at h
  · simp at h
  · rename_i is his
    split at h
    · split at h
      · simp at h
      · rename_i body hbody
        split at h
        · simp at h
        · have key : τ.lookup m = some ⟨is.length, body⟩ := by
            split at h
            · simp only [Except.ok.injEq] at h; subst h
              exact hτ m _ (by simp [Subst.lookup])
            · rename_i b hb
              split at h
              · simp only [Except.ok.injEq] at h; subst h
                rename_i heq; subst heq
                exact hτ m _ hb
              · simp at h
          simp only [Term.subst, key, mapM_bvarIdx? args is his]
          exact Term.rename_abstr t _ _ (indexOf?_getD is) body hbody
    · simp at h

mutual
/-- Report §4.1.2 — Algorithm 1 only adds bindings. -/
theorem matchAt_extends : (path : Path) → (p t : Term) → (σ σ' : Subst) →
    matchAt path p t σ = .ok σ' → σ.Extends σ'
  | path, .mvar m args, t, σ, σ', h => by
    simp only [matchAt] at h; exact assign_extends h
  | path, .const c as, t, σ, σ', h => by
    cases t with
    | const d bs =>
      simp only [matchAt] at h
      split at h
      · exact matchList_extends path 0 as bs σ σ' h
      · simp at h
    | _ => simp [matchAt] at h
  | path, .nat a, t, σ, σ', h => by
    cases t with
    | nat b =>
      simp only [matchAt] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact Subst.Extends.refl _
      · simp at h
    | _ => simp [matchAt] at h
  | path, .bvar i, t, σ, σ', h => by
    cases t with
    | bvar j =>
      simp only [matchAt] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact Subst.Extends.refl _
      · simp at h
    | _ => simp [matchAt] at h
  | path, .lam a, t, σ, σ', h => by
    cases t with
    | lam b => simp only [matchAt] at h; exact matchAt_extends _ a b σ σ' h
    | _ => simp [matchAt] at h
  | path, .acSet as, t, σ, σ', h => by
    cases t with
    | acSet bs =>
      simp only [matchAt] at h
      split at h
      · exact matchList_extends path 0 as bs σ σ' h
      · simp at h
    | _ => simp [matchAt] at h
/-- `matchAt_extends` on lists. -/
theorem matchList_extends : (path : Path) → (k : Nat) → (ps ts : List Term) → (σ σ' : Subst) →
    matchList path k ps ts σ = .ok σ' → σ.Extends σ'
  | path, k, [], ts, σ, σ', h => by
    cases ts with
    | nil => simp only [matchList, Except.ok.injEq] at h; subst h; exact Subst.Extends.refl _
    | cons _ _ => simp [matchList] at h
  | path, k, p :: ps, ts, σ, σ', h => by
    cases ts with
    | nil => simp [matchList] at h
    | cons t ts =>
      simp only [matchList] at h
      split at h
      · rename_i σ₁ h₁
        exact (matchAt_extends _ p t σ σ₁ h₁).trans (matchList_extends path (k + 1) ps ts σ₁ σ' h)
      · simp at h
end

mutual
/-- Report §4.1.2 — soundness of Algorithm 1 under every extension of its result. -/
theorem matchAt_sound : (path : Path) → (p t : Term) → (σ σ' : Subst) →
    matchAt path p t σ = .ok σ' → ∀ τ, σ'.Extends τ → p.subst τ = t
  | path, .mvar m args, t, σ, σ', h => by
    simp only [matchAt] at h; exact assign_sound h
  | path, .const c as, t, σ, σ', h => by
    cases t with
    | const d bs =>
      simp only [matchAt] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, -⟩ := hc
        intro τ hτ
        simp only [Term.subst, matchList_sound path 0 as bs σ σ' h τ hτ]
      · simp at h
    | _ => simp [matchAt] at h
  | path, .nat a, t, σ, σ', h => by
    cases t with
    | nat b =>
      simp only [matchAt] at h
      split at h
      · rename_i hab; subst hab; intro τ _; rfl
      · simp at h
    | _ => simp [matchAt] at h
  | path, .bvar i, t, σ, σ', h => by
    cases t with
    | bvar j =>
      simp only [matchAt] at h
      split at h
      · rename_i hij; subst hij; intro τ _; rfl
      · simp at h
    | _ => simp [matchAt] at h
  | path, .lam a, t, σ, σ', h => by
    cases t with
    | lam b =>
      simp only [matchAt] at h
      intro τ hτ
      simp only [Term.subst, matchAt_sound _ a b σ σ' h τ hτ]
    | _ => simp [matchAt] at h
  | path, .acSet as, t, σ, σ', h => by
    cases t with
    | acSet bs =>
      simp only [matchAt] at h
      split at h
      · intro τ hτ
        simp only [Term.subst, matchList_sound path 0 as bs σ σ' h τ hτ]
      · simp at h
    | _ => simp [matchAt] at h
/-- `matchAt_sound` on lists. -/
theorem matchList_sound : (path : Path) → (k : Nat) → (ps ts : List Term) → (σ σ' : Subst) →
    matchList path k ps ts σ = .ok σ' → ∀ τ, σ'.Extends τ → Term.substList τ ps = ts
  | path, k, [], ts, σ, σ', h => by
    cases ts with
    | nil => intro τ _; rfl
    | cons _ _ => simp [matchList] at h
  | path, k, p :: ps, ts, σ, σ', h => by
    cases ts with
    | nil => simp [matchList] at h
    | cons t ts =>
      simp only [matchList] at h
      split at h
      · rename_i σ₁ h₁
        intro τ hτ
        have h₂ := matchList_extends path (k + 1) ps ts σ₁ σ' h
        simp only [Term.substList, matchAt_sound _ p t σ σ₁ h₁ τ (h₂.trans hτ),
          matchList_sound path (k + 1) ps ts σ₁ σ' h τ hτ]
      · simp at h
end

/-- Report §4.1.2 — soundness of Algorithm 1: a returned substitution is a matcher,
`φσ = t` (syntactically; on normal forms this is matching modulo the AC theory, §4.1.1). -/
theorem millerMatch_sound {φ t : Term} {σ : Subst} (h : millerMatch φ t = .ok σ) :
    φ.subst σ = t :=
  matchAt_sound [] φ t [] σ h σ (Subst.Extends.refl σ)

end CQRV.Matching

end
