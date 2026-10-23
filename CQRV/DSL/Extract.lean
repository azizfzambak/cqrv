module

public import CQRV.DSL.Check
public import CQRV.DSL.Signature

/-!
# CQRV.DSL.Extract

Report §7.2 (ℰ as a total compiler), §7.3.2 Table 3 (construct → feature) — the extractor
`ℰ : {D : Γ ⊢ e : τ} → Σ-Term`, here `extract : TypedProgram → SigmaIn`. It is a plain
structurally recursive function on the typed term `TExpr τ`: no `partial`, no `Except`, no
`panic!` (§7.2.1, §4.2.2 "ℰ is total on surface-typed derivations").

Counting rules (Table 3 as fixed by the reviewer, DECISIONS.md 2026-10-23, decision 3):
* `and`, `or` (De Morgan, one AND): ĉ∧ = ĉ₁ + ĉ₂ + 1, depth = max + 1;
* `not`, `xor`, literals, `idx`: no AND (linear over GF(2)); depth = max of subterms;
* `if c then a else b`: mux `b ⊕ (c ∧ (a ⊕ b))`, one AND per bit of the result type;
* `let x = e₁ in e₂`: ĉ∧(e₁) + ĉ∧(e₂), uses of `x` are shared (free), depth of `x` = depth e₁;
* `for` with bound n: ĉ∧(init) + n·ĉ∧(body), depth(init) + n·depth(body);
* `loop … while`: init, condition and body counted once, `iter = unbounded`.
The ancilla budget is ĉ∧ (decision 4). ĉ∧ is a syntactic upper bound, never a minimum.
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §4.3.3 — combine the iteration structure of two sub-computations (siblings):
the larger bound; `unbounded` absorbs. -/
def IterBound.max : IterBound → IterBound → IterBound
  | .bounded a, .bounded b => .bounded (Nat.max a b)
  | _, _ => .unbounded

/-- Report §4.3.3 — `n` nested repetitions of a computation: static bounds multiply. -/
def IterBound.mul (n : Nat) : IterBound → IterBound
  | .bounded k => .bounded (n * k)
  | .unbounded => .unbounded

/-- Report §7.3.2 — the features ℰ tracks for one sub-term (an abstract value). -/
structure AVal where
  /-- ĉ∧ of the sub-term -/
  ands : Nat
  /-- AND-depth of the sub-term -/
  depth : Nat
  /-- input bit positions it reads (unsorted, may repeat) -/
  support : List Nat
  /-- `some o`: the value *is* the input slice starting at bit `o` (an input vector) -/
  base : Option Nat
  /-- `some ls`: the value is the conjunction of the literals `ls` (bit, polarity) -/
  lits : Option (List (Nat × Bool))
  iter : IterBound
  deriving Repr, Inhabited

/-- A value with no cost and no input dependence. -/
def AVal.zero : AVal := ⟨0, 0, [], none, none, .bounded 1⟩

/-- A bound variable: its cost was counted at the binder (sharing). -/
def AVal.share (a : AVal) : AVal := { a with ands := 0, iter := .bounded 1 }

/-- Two sub-terms side by side, no gate of their own. -/
def AVal.join (a b : AVal) : AVal :=
  ⟨a.ands + b.ands, Nat.max a.depth b.depth, a.support ++ b.support, none, none,
   a.iter.max b.iter⟩

/-- One AND gate on top of `j`. -/
def AVal.andGate (j : AVal) : AVal := { j with ands := j.ands + 1, depth := j.depth + 1 }

namespace Extract

/-- Bit positions `[o, o + m)`. -/
def slice (o m : Nat) : List Nat := (List.range m).map (o + ·)

/-- ℰ on a typed term, structurally recursive (§7.2.2: "E is structurally recursive on D"). -/
def extractE : {τ : Ty} → TExpr τ → List (String × AVal) → AVal
  | _, .var x _, env => (env.lookup x).getD AVal.zero
  | _, .lit b, _ => { AVal.zero with lits := if b then some [] else none }
  | _, .not a, env =>
    let v := extractE a env
    { v with base := none,
             lits := match v.lits with | some [(k, s)] => some [(k, !s)] | _ => none }
  | _, .and a b, env =>
    let va := extractE a env
    let vb := extractE b env
    { (va.join vb).andGate with lits := do pure ((← va.lits) ++ (← vb.lits)) }
  | _, .or a b, env => (AVal.join (extractE a env) (extractE b env)).andGate
  | _, .xor a b, env => AVal.join (extractE a env) (extractE b env)
  | _, .idx v k, env =>
    let a := extractE v env
    match a.base, k with
    | some o, .lit k =>
      { a with support := [o + k.val], base := none, lits := some [(o + k.val, true)] }
    | some o, .loopVar _ m _ => { a with support := slice o m, base := none, lits := none }
    | none, _ => { a with base := none, lits := none }
  | τ, .ite c a b, env =>
    let j := ((extractE c env).join (extractE a env)).join (extractE b env)
    if τ.width = 0 then j else { j with ands := j.ands + τ.width, depth := j.depth + 1 }
  | _, .letE x e₁ e₂, env =>
    let a₁ := extractE e₁ env
    let a₂ := extractE e₂ ((x, a₁.share) :: env)
    { a₂ with ands := a₁.ands + a₂.ands, iter := a₁.iter.max a₂.iter }
  | _, .forE i n acc init body, env =>
    let a₀ := extractE init env
    let accV := { AVal.zero with support := a₀.support }
    let ab := extractE body ((acc, accV) :: (i, AVal.zero) :: env)
    ⟨a₀.ands + n * ab.ands, a₀.depth + n * ab.depth, a₀.support ++ ab.support, none, none,
     a₀.iter.max (ab.iter.mul n)⟩
  | _, .loopE acc init cond body, env =>
    let a₀ := extractE init env
    let env' := (acc, { AVal.zero with support := a₀.support }) :: env
    let ac := extractE cond env'
    let ab := extractE body env'
    ⟨a₀.ands + ac.ands + ab.ands, a₀.depth + Nat.max ac.depth ab.depth,
     a₀.support ++ ac.support ++ ab.support, none, none, .unbounded⟩

/-- Abstract values of the entry parameters, laid out consecutively from input bit 0. -/
def paramVals : List (String × Ty) → Nat → List (String × AVal)
  | [], _ => []
  | (x, τ) :: ps, o =>
    let v : AVal := match τ with
      | .vec _ => { AVal.zero with support := slice o τ.width, base := some o }
      | .bool => { AVal.zero with support := [o], lits := some [(o, true)] }
      | _ => { AVal.zero with support := slice o τ.width }
    (x, v) :: paramVals ps (o + τ.width)

/-- Report §4.1.4, DECISIONS.md decision 5 — M = 2^(n − |literals|) when the predicate is a
conjunction of literals on distinct bits of an n-bit input; otherwise `none`. -/
def solutionCountOf (n : Nat) (lits : Option (List (Nat × Bool))) : Option Nat :=
  match lits with
  | some ls =>
    let bits := ls.map (·.1)
    if bits.eraseDups.length = bits.length ∧ ls.length ≤ n then some (2 ^ (n - ls.length))
    else none
  | none => none

end Extract

open Extract in
/-- Report §7.2.2, §7.2.3 — `ℰ : TypedProgram → SigmaIn`, total. -/
def extract (tp : TypedProgram) : SigmaIn :=
  let a := extractE tp.body (paramVals tp.params 0)
  let n := (tp.params.map (·.2.width)).sum
  let isSearch := match tp.params, tp.ret with
    | [(_, .vec _)], .bool => true
    | _, _ => false
  { problemClass := if isSearch then .search else .decision
    arity := n
    solutionCount := if isSearch then solutionCountOf n a.lits else none
    andComplexity := a.ands
    andDepth := a.depth
    ancillaBudget := a.ands
    oracle := if tp.ret = .bool then .phaseKickback .multiplicative (a.support.mergeSort.eraseDups)
              else .blackBox
    algebra := .boolAlg
    domain := tp.params.map (·.2)
    codomain := tp.ret
    iter := a.iter }

end CQRV.DSL

end
