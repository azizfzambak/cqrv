module

public import Lean.Data.Json
public import CQRV.DSL.Signature

/-!
# CQRV.Matching.Term

Report §4.1.1 (Table 1, precondition language) and §4.1.2 (the Miller-pattern fragment) —
Σ-terms over the multi-sorted signature of spec signatures: rigid constructors with argument
lists, natural-number literals, de Bruijn bound variables, λ-binders, metavariable
applications `F x₁ … x_k`, and one AC symbol `acSet` (sets such as `support`, §7.2.3).
`SigmaIn.toTerm` turns the ground signature of ℰ into a closed term with a fixed field order.
-/

@[expose] public section

namespace CQRV.Matching

open CQRV.DSL

/-- Report §4.3.1 — metavariable namespaces: `F` for pattern metavariables of the library,
`G` for the fresh metavariables of `lgg` (DECISIONS.md 2026-10-23, Stage 4 decision 1). -/
inductive MNs where
  | F
  | G
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.1, Table 1 ("metavariables over sorts"), §4.1.4 ("metavariables ranging over
natural numbers") — the sort a metavariable ranges over. `nat`: a literal; `natSet`: an
`acSet` of literals (a whole AC list, never a sub-multiset); `any`: any term. -/
inductive MSort where
  | nat
  | natSet
  | any
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.1 — a metavariable: namespace, index (`F₁`, `G₁`, …) and sort. -/
structure MVar where
  ns : MNs
  idx : Nat
  sort : MSort
  deriving Repr, DecidableEq, Inhabited

/-- Report §4.1.1–4.1.2 — Σ-terms. -/
inductive Term where
  /-- rigid constructor `c(t₁, …, tₙ)` (constants are `c()`) -/
  | const (c : String) (args : List Term)
  /-- natural-number literal -/
  | nat (n : Nat)
  /-- bound variable, de Bruijn index -/
  | bvar (i : Nat)
  /-- λ-binder -/
  | lam (body : Term)
  /-- metavariable application `F t₁ … t_k`; in a Miller pattern each `tᵢ` is a distinct
  bound variable (`isMillerPattern`) -/
  | mvar (m : MVar) (args : List Term)
  /-- the AC symbol: a finite set, normalized by flattening, sorting and deduplication -/
  | acSet (args : List Term)
  deriving Repr, Inhabited

namespace Term

/-! The `DecidableEq` deriving handler does not apply to this nested inductive in the pinned
toolchain; equality is decided by a structural Boolean test `beq` with its correctness proof. -/

mutual
/-- Report §4.1.2, step 4 — syntactic equality of terms (Boolean). -/
def beq : Term → Term → Bool
  | .const c as, .const d bs => c == d && beqList as bs
  | .nat a, .nat b => a == b
  | .bvar i, .bvar j => i == j
  | .lam a, .lam b => beq a b
  | .mvar m as, .mvar n bs => m == n && beqList as bs
  | .acSet as, .acSet bs => beqList as bs
  | _, _ => false
/-- `beq` on lists. -/
def beqList : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

mutual
/-- `beq` is reflexive. -/
theorem beq_refl : (a : Term) → beq a a = true
  | .const c as => by simp only [beq, beq_self_eq_true, Bool.true_and]; exact beqList_refl as
  | .nat _ | .bvar _ => by simp [beq]
  | .lam a => by simp only [beq]; exact beq_refl a
  | .mvar m as => by simp only [beq, beq_self_eq_true, Bool.true_and]; exact beqList_refl as
  | .acSet as => by simp only [beq]; exact beqList_refl as
/-- `beqList` is reflexive. -/
theorem beqList_refl : (as : List Term) → beqList as as = true
  | [] => by simp [beqList]
  | a :: as => by simp only [beqList, Bool.and_eq_true]; exact ⟨beq_refl a, beqList_refl as⟩
end

mutual
/-- `beq` implies equality. -/
theorem eq_of_beq : (a b : Term) → beq a b = true → a = b
  | .const c as, b, h => by
    cases b with
    | const d bs =>
      simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_beqList as bs h]
    | _ => simp [beq] at h
  | .nat n, b, h => by cases b <;> simp_all [beq]
  | .bvar n, b, h => by cases b <;> simp_all [beq]
  | .lam a, b, h => by
    cases b with
    | lam b => simp only [beq] at h; rw [eq_of_beq a b h]
    | _ => simp [beq] at h
  | .mvar m as, b, h => by
    cases b with
    | mvar n bs =>
      simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_beqList as bs h]
    | _ => simp [beq] at h
  | .acSet as, b, h => by
    cases b with
    | acSet bs => simp only [beq] at h; rw [eq_of_beqList as bs h]
    | _ => simp [beq] at h
/-- `beqList` implies equality. -/
theorem eq_of_beqList : (as bs : List Term) → beqList as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [beqList]
  | a :: as, bs, h => by
    cases bs with
    | nil => simp [beqList] at h
    | cons b bs =>
      simp only [beqList, Bool.and_eq_true] at h
      rw [eq_of_beq a b h.1, eq_of_beqList as bs h.2]
end

/-- Report §4.1.2, step 4 — decidable syntactic equality of terms. -/
instance : DecidableEq Term := fun a b =>
  if h : beq a b = true then isTrue (eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ beq_refl a))

end Term

/-- Report §4.1.2 — a path to a subterm: the argument index taken at each node
(`lam` has the single child 0). -/
abbrev Path := List Nat

/-- Subscript digits for metavariable names (`F₁`, `G₁₂`). -/
def subscript (n : Nat) : String :=
  String.map (fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080)) (toString n)

/-- Report §4.3.2 — the printed name of a metavariable, `F₁` or `G₁`. -/
def MVar.name (m : MVar) : String :=
  (match m.ns with | .F => "F" | .G => "G") ++ subscript m.idx

/-- Report §4.1.4 — pattern metavariable `Fᵢ` of sort `s`. -/
def MVar.f (i : Nat) (s : MSort) : MVar := ⟨.F, i, s⟩

/-- Report §7.2.2 — field names of the signature constructor `sig` (the field order of
`SigmaIn.toTerm`); PHASE2_SPEC.md §A.5 (amendments before Stage 21, (2)): `m`, the precision, is
the seventh field of a Count term. -/
def sigFields : List String := ["class", "n", "M", "P", "iter", "oracle", "m"]

namespace Term

mutual
/-- Report §4.3.2 — concrete rendering of a term (hint fields Expected / Found). -/
def render : Term → String
  | .const "sig" args =>
    "⟨" ++ ", ".intercalate ((sigFields.zip (renderList args)).map fun (f, s) => s!"{f}: {s}") ++
      "⟩"
  | .const "→" [a, b] => render a ++ " → " ++ render b
  | .const "Bool^" [n] => "Bool^" ++ render n
  | .const c [] => c
  | .const c args => c ++ "(" ++ ", ".intercalate (renderList args) ++ ")"
  | .nat n => toString n
  | .bvar i => s!"#{i}"
  | .lam b => "λ. " ++ render b
  | .mvar m [] => m.name
  | .mvar m args => m.name ++ " " ++ " ".intercalate (renderList args)
  | .acSet args => "{" ++ ", ".intercalate (renderList args) ++ "}"
/-- `render` on a list. -/
def renderList : List Term → List String
  | [] => []
  | t :: ts => render t :: renderList ts
end

mutual
/-- Report §4.3.1 — term size (number of nodes), used for the `dist` tie-break. -/
def size : Term → Nat
  | .const _ args | .acSet args | .mvar _ args => 1 + sizeList args
  | .nat _ | .bvar _ => 1
  | .lam b => 1 + size b
/-- `size` on a list. -/
def sizeList : List Term → Nat
  | [] => 0
  | t :: ts => size t + sizeList ts
end

mutual
/-- Report §4.1.2, step 3 (occurs check) — does metavariable `m` occur in the term? -/
def hasMVar (m : MVar) : Term → Bool
  | .const _ args | .acSet args => hasMVarList m args
  | .mvar m' args => m' == m || hasMVarList m args
  | .nat _ | .bvar _ => false
  | .lam b => hasMVar m b
/-- `hasMVar` on a list. -/
def hasMVarList (m : MVar) : List Term → Bool
  | [] => false
  | t :: ts => hasMVar m t || hasMVarList m ts
end

mutual
/-- Report §4.1.1 — does the term contain a metavariable (is it not ground)? -/
def hasAnyMVar : Term → Bool
  | .const _ args | .acSet args => hasAnyMVarList args
  | .mvar _ _ => true
  | .nat _ | .bvar _ => false
  | .lam b => hasAnyMVar b
/-- `hasAnyMVar` on a list. -/
def hasAnyMVarList : List Term → Bool
  | [] => false
  | t :: ts => hasAnyMVar t || hasAnyMVarList ts
end

/-- Report §4.1.2 — the index of a bound-variable argument of a metavariable application. -/
def bvarIdx? : Term → Option Nat
  | .bvar i => some i
  | _ => none

/-- Report §4.1.2 — the index of a bound-variable argument; `0` on a non-variable (unreachable
on Miller patterns, which `millerMatch` checks). -/
def bvarIdx (t : Term) : Nat := (bvarIdx? t).getD 0

mutual
/-- Report §4.1.1–4.1.2 — Miller-pattern check at binder depth `c`: every metavariable is
applied to distinct bound variables in scope; no metavariable inside an `acSet` (a
metavariable may stand for a whole AC list, never for a proper sub-multiset or an element of
one — DECISIONS.md 2026-10-23, Stage 4 interpretations). -/
def isMillerAt (c : Nat) (inAC : Bool) : Term → Bool
  | .const _ args => isMillerList c inAC args
  | .acSet args => isMillerList c true args
  | .nat _ | .bvar _ => true
  | .lam b => isMillerAt (c + 1) inAC b
  | .mvar _ args =>
    !inAC &&
      match args.mapM bvarIdx? with
      | some is => is.all (· < c) && is.Nodup
      | none => false
/-- `isMillerAt` on a list. -/
def isMillerList (c : Nat) (inAC : Bool) : List Term → Bool
  | [] => true
  | t :: ts => isMillerAt c inAC t && isMillerList c inAC ts
end

mutual
/-- All metavariables of a term, in left-to-right order (with repetitions). -/
def mvars : Term → List MVar
  | .const _ args | .acSet args => mvarsList args
  | .mvar m args => m :: mvarsList args
  | .nat _ | .bvar _ => []
  | .lam b => mvars b
/-- `mvars` on a list. -/
def mvarsList : List Term → List MVar
  | [] => []
  | t :: ts => mvars t ++ mvarsList ts
end

/-- Report §4.1.1–4.1.2 — `φ` lies in the Miller-pattern fragment: `isMillerAt 0 false`, and
each metavariable name (namespace, index) is used with one sort only. -/
def isMillerPattern (φ : Term) : Bool :=
  isMillerAt 0 false φ &&
    (φ.mvars.all fun m => φ.mvars.all fun m' => !(m.ns == m'.ns && m.idx == m'.idx) || m == m')

mutual
/-- Report §4.3.1 — paths of the metavariable occurrences of a term (left to right). -/
def mvarPaths (p : Path) : Term → List (MVar × Path)
  | .const _ args | .acSet args => mvarPathsList p 0 args
  | .mvar m args => (m, p) :: mvarPathsList p 0 args
  | .nat _ | .bvar _ => []
  | .lam b => mvarPaths (p ++ [0]) b
/-- `mvarPaths` on a list; `k` is the index of the head. -/
def mvarPathsList (p : Path) (k : Nat) : List Term → List (MVar × Path)
  | [] => []
  | t :: ts => mvarPaths (p ++ [k]) t ++ mvarPathsList p (k + 1) ts
end

/-- Report §4.3.2 (Location) — a path rendered for the user: the signature field name of the
first step (`sigFields`, when the root is `sig`), then the remaining indices. -/
def pathLabel (root : Term) (p : Path) : String :=
  match root, p with
  | .const "sig" _, i :: rest =>
    let f := (sigFields[i]?).getD s!"#{i}"
    if rest.isEmpty then f else f ++ " (position " ++ ".".intercalate (rest.map toString) ++ ")"
  | _, [] => "root"
  | _, _ => "position " ++ ".".intercalate (p.map toString)

end Term

/-! ## The ground signature as a term (report §7.2.2, §4.1.4) -/

/-- Report §7.1.4 — a surface type as a Σ-term: `Bool`, `Bool^n`, `Nat(n)`, `Unit`. -/
def tyTerm : Ty → Term
  | .bool => .const "Bool" []
  | .vec n => .const "Bool^" [.nat n]
  | .nat n => .const "Nat" [.nat n]
  | .unit => .const "Unit" []

/-- Report §7.2.2 — the domain: the single parameter type, or the product `×(τ₁, …)`. -/
def domTerm : List Ty → Term
  | [τ] => tyTerm τ
  | τs => .const "×" (τs.map tyTerm)

/-- Report §4.3.3 — the iteration field. -/
def _root_.CQRV.DSL.IterBound.toTerm : IterBound → Term
  | .bounded k => .const "bounded" [.nat k]
  | .unbounded => .const "unbounded" []

/-- Report §7.2.2–7.2.3 — the oracle field; the support is an `acSet`. -/
def _root_.CQRV.DSL.OracleStructure.toTerm : OracleStructure → Term
  | .phaseKickback .multiplicative s =>
    .const "PhaseKickback" [.const "Multiplicative" [], .acSet (s.map Term.nat)]
  | .block => .const "Block" []
  | .blackBox => .const "BlackBox" []

/-- Report §4.1.4, §7.2.2 — σ_in as a closed Σ-term
`sig(class, n, M, P, iter, oracle)` with a fixed field order (`sigFields`). An unknown
solution count is the rigid constant `unknown` (DECISIONS.md 2026-10-23, Stage 4 decision 3).
ĉ∧, the AND-depth, the ancilla budget and the algebra are not matched (they feed the grade,
Chapter 3), so they are not part of the term. PHASE2_SPEC.md §A.5 (amendments before Stage 21,
(2)): a Count request appends its precision `m` as a seventh argument, exactly when
`precision = some m`; a search term keeps its six arguments. -/
def _root_.CQRV.DSL.SigmaIn.toTerm (s : SigmaIn) : Term :=
  .const "sig"
    ([.const s.problemClass.name [],
      .nat s.arity,
      match s.solutionCount with | some m => .nat m | none => .const "unknown" [],
      .const "→" [domTerm s.domain, tyTerm s.codomain],
      s.iter.toTerm,
      s.oracle.toTerm] ++
     match s.precision with | some m => [.nat m] | none => [])

end CQRV.Matching

end
