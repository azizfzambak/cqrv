module

public import CQRV.Matching.Term

/-!
# CQRV.Matching.Normalize

Report §4.1.1 ("equational theories are handled by normalization, not by E-unification") and
§4.1.2, Algorithm 1 step 5 (normal-form invariant) — the canonical normal form: nested `acSet`s
are flattened, their arguments sorted under a fixed total order on terms and deduplicated
(`acSet` is a set). `normalize` is applied to both φ and σ_in before matching.
-/

@[expose] public section

namespace CQRV.Matching

namespace Term

/-- Report §4.1.1 — rank of the head symbol in the fixed total order. -/
def tag : Term → Nat
  | .nat _ => 0
  | .bvar _ => 1
  | .const .. => 2
  | .lam _ => 3
  | .mvar .. => 4
  | .acSet _ => 5

/-- Report §4.1.1 — fixed total order on metavariables (namespace, index, sort). -/
def MVar.cmp (m n : MVar) : Ordering :=
  let ns : MNs → Nat := fun | .F => 0 | .G => 1
  let so : MSort → Nat := fun | .nat => 0 | .natSet => 1 | .any => 2
  (compare (ns m.ns) (ns n.ns)).then ((compare m.idx n.idx).then (compare (so m.sort) (so n.sort)))

mutual
/-- Report §4.1.1 — the fixed total order on terms: head rank, then the head's data, then
the arguments lexicographically. -/
def cmp : Term → Term → Ordering
  | .nat a, .nat b => compare a b
  | .bvar i, .bvar j => compare i j
  | .const c as, .const d bs => (compare c d).then (cmpList as bs)
  | .lam a, .lam b => cmp a b
  | .mvar m as, .mvar n bs => (MVar.cmp m n).then (cmpList as bs)
  | .acSet as, .acSet bs => cmpList as bs
  | a, b => compare a.tag b.tag
/-- Lexicographic extension of `cmp` to lists (a proper prefix is smaller). -/
def cmpList : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmp a b).then (cmpList as bs)
end

/-- Report §4.1.1 — splice the arguments of nested `acSet`s (one level; the arguments are
already normalized, hence flat). -/
def flattenAC : List Term → List Term
  | [] => []
  | .acSet bs :: rest => bs ++ flattenAC rest
  | t :: rest => t :: flattenAC rest

/-- Report §4.1.1 — remove adjacent duplicates (after sorting: all duplicates). -/
def dedupAdj : List Term → List Term
  | a :: b :: rest => if cmp a b == .eq then dedupAdj (b :: rest) else a :: dedupAdj (b :: rest)
  | l => l

/-- Report §4.1.1 — canonical argument list of an AC set: sort under `cmp`, deduplicate. -/
def canonAC (ts : List Term) : List Term :=
  dedupAdj (ts.mergeSort fun a b => cmp a b != .gt)

mutual
/-- Report §4.1.1, Algorithm 1 step 5 — the canonical normal form. -/
def normalize : Term → Term
  | .const c args => .const c (normalizeList args)
  | .acSet args => .acSet (canonAC (flattenAC (normalizeList args)))
  | .lam b => .lam (normalize b)
  | .mvar m args => .mvar m (normalizeList args)
  | t => t
/-- `normalize` on a list. -/
def normalizeList : List Term → List Term
  | [] => []
  | t :: ts => normalize t :: normalizeList ts
end

end Term

end CQRV.Matching

end
