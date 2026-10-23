module

/-!
# CQRV.DSL.Syntax

Report §7.1.4 — abstract syntax of the input DSL (BNF of §7.1.4, `for` as a bounded fold),
plus the two surface forms added by the reviewer (docs/DECISIONS.md, 2026-10-23, Stage 3):
the functional while `loop <var> = <expr> while <expr> do <expr>` and calls `f(e₁, …)` to
top-level `fn`s. Every node carries its source position for diagnostics.
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.4 — a source position, 1-based line and column. -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.1.4, `<type>` — `Bool | Vec Bool n | Nat n | Unit`. `Nat n` is `{0, …, n−1}`. -/
inductive Ty where
  | bool
  | vec (n : Nat)
  | nat (n : Nat)
  | unit
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.1.4 — concrete syntax of a type (used in diagnostics and in the signature JSON). -/
def Ty.render : Ty → String
  | .bool => "Bool"
  | .vec n => s!"Vec Bool {n}"
  | .nat n => s!"Nat {n}"
  | .unit => "Unit"

/-- Report §7.2.2 — number of input bits of a value of type `τ` (input arity). `Nat n` takes
⌈log₂ n⌉ bits. -/
def Ty.width : Ty → Nat
  | .bool => 1
  | .vec n => n
  | .nat n => if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1
  | .unit => 0

/-- Report §7.1.4, second argument of `idx(<expr>, <nat>)`: a literal, or a variable (which
`check` accepts only when it is a `for`-bound loop variable, DECISIONS.md 2026-10-23). -/
inductive IdxRef where
  | lit (p : Pos) (k : Nat)
  | var (p : Pos) (x : String)
  deriving Repr, Inhabited

/-- Report §7.1.4, `<expr>`, plus `loop … while` and calls (reviewer additions, Stage 3). -/
inductive Expr where
  /-- `<var>` -/
  | var (p : Pos) (x : String)
  /-- `true | false` -/
  | lit (p : Pos) (b : Bool)
  /-- `not e` -/
  | not (p : Pos) (e : Expr)
  /-- `e₁ and e₂` -/
  | and (p : Pos) (a b : Expr)
  /-- `e₁ or e₂` -/
  | or (p : Pos) (a b : Expr)
  /-- `e₁ xor e₂` -/
  | xor (p : Pos) (a b : Expr)
  /-- `idx(e, k)` — vector indexing. -/
  | idx (p : Pos) (e : Expr) (k : IdxRef)
  /-- `for i in [0 ..< n] with acc = init do body` — bounded fold. -/
  | forE (p : Pos) (i : String) (n : Nat) (acc : String) (init body : Expr)
  /-- `loop acc = init while cond do body` — functional while (reviewer addition). -/
  | loopE (p : Pos) (acc : String) (init cond body : Expr)
  /-- `if c then a else b` -/
  | ite (p : Pos) (c a b : Expr)
  /-- `let x = e₁ in e₂` -/
  | letE (p : Pos) (x : String) (e₁ e₂ : Expr)
  /-- `f(e₁, …, eₖ)` — call to a top-level `fn` (reviewer addition). -/
  | call (p : Pos) (f : String) (args : List Expr)
  deriving Repr, Inhabited

/-- Report §7.1.4 — the source position of an expression node. -/
def Expr.pos : Expr → Pos
  | .var p _ | .lit p _ | .not p _ | .and p _ _ | .or p _ _ | .xor p _ _ | .idx p _ _
  | .forE p _ _ _ _ _ | .loopE p _ _ _ _ | .ite p _ _ _ | .letE p _ _ _ | .call p _ _ => p

/-- Report §7.1.4 — a parameter `x : τ` of a `fn`. -/
structure Param where
  pos : Pos
  name : String
  ty : Ty
  deriving Repr, Inhabited

/-- Report §7.1.4, `fn <var>(<var>: <type>, …) -> <type> { <expr> }`. -/
structure FnDecl where
  pos : Pos
  name : String
  params : List Param
  ret : Ty
  body : Expr
  deriving Repr, Inhabited

/-- Report §7.1.4 — a source file: a list of top-level `fn`s. The entry point is the last one
(DECISIONS.md 2026-10-23, Stage 3 interpretations). -/
structure Program where
  fns : List FnDecl
  deriving Repr, Inhabited

end CQRV.DSL

end
