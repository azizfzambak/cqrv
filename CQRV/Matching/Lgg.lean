module

public import CQRV.Matching.Miller

/-!
# CQRV.Matching.Lgg

Report §4.1.3 (anti-unification, the lgg gap as diagnostic) and §4.3.1 (computing the least
general generalization) — `lgg t₁ t₂ = (g, σ₁, σ₂)` with `g σ₁ = t₁`, `g σ₂ = t₂`. Common
structure is kept; every disagreement position gets a fresh metavariable `Gᵢ` (namespace `G`,
DECISIONS.md 2026-10-23, Stage 4 decision 1), and an identical disagreement pair reuses the
same `Gᵢ`. Pattern metavariables (`F`) are rigid symbols here. `dist` is the number of fresh
metavariables, ties broken by the total size of the two substitutions.
-/

@[expose] public section

namespace CQRV.Matching

open Term

namespace Term

mutual
/-- Free bound variables of a term (indices relative to the term's root), with repetitions. -/
def freeBvars (c : Nat) : Term → List Nat
  | .const _ as | .acSet as | .mvar _ as => freeBvarsList c as
  | .nat _ => []
  | .bvar i => if i < c then [] else [i - c]
  | .lam b => freeBvars (c + 1) b
/-- `freeBvars` on a list. -/
def freeBvarsList (c : Nat) : List Term → List Nat
  | [] => []
  | t :: ts => freeBvars c t ++ freeBvarsList c ts
end

end Term

/-- Report §4.3.1 — state of the lgg traversal: the disagreement pairs met so far, each with
its fresh metavariable and that metavariable's bound-variable arguments (newest first). -/
structure LggState where
  pairs : List ((Term × Term) × (MVar × List Nat))
  next : Nat
  deriving Inhabited

/-- Report §4.3.1 — the generalization of a disagreement pair `(a, b)`: the metavariable
already assigned to that exact pair (reuse), or a fresh `G_{next+1}` applied to the bound
variables free in `a` or `b` (pattern lgg). -/
def LggState.fresh (a b : Term) (s : LggState) : Term × LggState :=
  match s.pairs.lookup (a, b) with
  | some (g, vs) => (.mvar g (vs.map .bvar), s)
  | none =>
    let vs := ((a.freeBvars 0 ++ b.freeBvars 0).mergeSort (· ≤ ·)).eraseDups
    let g : MVar := ⟨.G, s.next + 1, .any⟩
    (.mvar g (vs.map .bvar), { pairs := ((a, b), (g, vs)) :: s.pairs, next := s.next + 1 })

mutual
/-- Report §4.3.1 — parallel traversal: keep common structure, generalize disagreements. -/
def lggAt : Term → Term → LggState → Term × LggState
  | .const c as, .const d bs, s =>
    if c = d ∧ as.length = bs.length then
      let (cs, s) := lggList as bs s
      (.const c cs, s)
    else s.fresh (.const c as) (.const d bs)
  | .nat a, .nat b, s => if a = b then (.nat a, s) else s.fresh (.nat a) (.nat b)
  | .bvar i, .bvar j, s => if i = j then (.bvar i, s) else s.fresh (.bvar i) (.bvar j)
  | .lam a, .lam b, s =>
    let (c, s) := lggAt a b s
    (.lam c, s)
  | .mvar m as, .mvar n bs, s =>
    if m = n ∧ as = bs then (.mvar m as, s) else s.fresh (.mvar m as) (.mvar n bs)
  | .acSet as, .acSet bs, s =>
    if as.length = bs.length then
      let (cs, s) := lggList as bs s
      (.acSet cs, s)
    else s.fresh (.acSet as) (.acSet bs)
  | a, b, s => s.fresh a b
/-- `lggAt` on argument lists of equal length. -/
def lggList : List Term → List Term → LggState → List Term × LggState
  | a :: as, b :: bs, s =>
    let (c, s) := lggAt a b s
    let (cs, s) := lggList as bs s
    (c :: cs, s)
  | _, _, s => ([], s)
end

/-- Report §4.3.1 — `lgg t₁ t₂ = (g, σ₁, σ₂)`; `σᵢ` binds each fresh `G` to its side of the
disagreement pair (abstracted over `G`'s bound-variable arguments), in order `G₁, G₂, …`. -/
def lgg (t₁ t₂ : Term) : Term × Subst × Subst :=
  let (g, s) := lggAt t₁ t₂ ⟨[], 0⟩
  let side (pick : Term × Term → Term) : Subst :=
    s.pairs.reverse.map fun (ab, (m, vs)) =>
      (m, ⟨vs.length, (abstr (indexOf? vs) (pick ab)).getD (pick ab)⟩)
  (g, side Prod.fst, side Prod.snd)

/-- Report §4.3.1 — total size of the bodies of a substitution. -/
def Subst.size (σ : Subst) : Nat := (σ.map fun (_, b) => b.body.size).sum

/-- Report §4.3.1 — anti-unification distance: (number of fresh metavariables, total size of
the two witnessing substitutions), compared lexicographically. -/
def dist (t₁ t₂ : Term) : Nat × Nat :=
  let (_, σ₁, σ₂) := lgg t₁ t₂
  (σ₁.length, σ₁.size + σ₂.size)

/-- Report §4.3.1 — lexicographic order on distances. -/
def distLt (d e : Nat × Nat) : Bool := d.1 < e.1 || (d.1 == e.1 && d.2 < e.2)

end CQRV.Matching

end
