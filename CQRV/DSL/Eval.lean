module

public import CQRV.DSL.Check

/-!
# CQRV.DSL.Eval

Report §5.3.3, §7.2, §9.5.1 — a reference evaluator of the DSL (Stage 9b, reviewer decision 1;
DECISIONS.md 2026-10-25): the meaning of a typed program on an input assignment, computed
directly on values (Booleans, bit vectors, numbers), independently of `toNetwork`. It is the
other side of the exhaustive front-end validation (`CQRV.Certify.FrontEnd`): for `n ≤ 16`,
`evalProgram` and `Network.pred (toNetwork …)` must agree on all `2ⁿ` inputs.

* Total and structural on `TExpr` (no fuel): `let` binds the value, `if` selects a branch,
  `for` is a fold over `[0 ..< n]` with the loop variable bound to its number, calls are already
  inlined by the surface checker (as `let`s of fresh names).
* `loop … while` has no finite meaning here; `TypedProgram.hasLoop` rejects such programs before
  evaluation. `evalExpr` maps a `loop` to its initial value only to stay total; the validator
  never reaches that clause.
* Inputs are laid out from bit 0 in parameter order (§7.2.2, as ℰ): `Bool` reads one bit,
  `Vec Bool m` reads `m` bits, `Nat m` reads `Ty.width (.nat m)` bits little-endian. Bits at or
  beyond `n` read `false` (as `Network.pred`).
* The result is the first bit of the returned value (`Bool`: the value; `Nat m`: bit 0,
  little-endian), the bit `Network.pred` reads.
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.4 — a run-time value of the DSL: a Boolean, a bit vector, a number (`Nat m`,
also a `for` loop variable), or `()`. -/
inductive Val where
  | bool (b : Bool)
  | vec (bs : List Bool)
  | nat (k : Nat)
  | unit
  deriving Repr, Inhabited

/-- The Boolean of a value (`false` for any other value; never reached on well-typed terms). -/
def Val.toBool : Val → Bool
  | .bool b => b
  | _ => false

/-- The bits of a value of type `τ`, in the network's output order (`Nat m` little-endian, as
`toNetwork`). -/
def Val.bitsAt : Ty → Val → List Bool
  | .bool, v => [v.toBool]
  | .vec _, .vec bs => bs
  | .nat m, .nat k => (List.range (Ty.width (.nat m))).map fun j => (k >>> j) % 2 == 1
  | _, _ => []

/-- Report §7.1.4 — whether a typed term contains `loop … while`. -/
def TExpr.hasLoop : {τ : Ty} → TExpr τ → Bool
  | _, .var .. | _, .lit _ => false
  | _, .not a | _, .idx a _ => a.hasLoop
  | _, .and a b | _, .or a b | _, .xor a b | _, .letE _ a b | _, .forE _ _ _ a b =>
    a.hasLoop || b.hasLoop
  | _, .ite c a b => c.hasLoop || a.hasLoop || b.hasLoop
  | _, .loopE .. => true

/-- Report §7.1.4 — whether the entry `fn` contains `loop … while` (rejected before
evaluation). -/
def TypedProgram.hasLoop (tp : TypedProgram) : Bool := tp.body.hasLoop

/-- Report §7.1.4, §7.2 — the value of a typed term in an environment (innermost binding
first). Structural on the term. -/
def evalExpr : {τ : Ty} → TExpr τ → List (String × Val) → Val
  | _, .var x _, env => (env.lookup x).getD .unit
  | _, .lit b, _ => .bool b
  | _, .not a, env => .bool !(evalExpr a env).toBool
  | _, .and a b, env => .bool ((evalExpr a env).toBool && (evalExpr b env).toBool)
  | _, .or a b, env => .bool ((evalExpr a env).toBool || (evalExpr b env).toBool)
  | _, .xor a b, env => .bool ((evalExpr a env).toBool ^^ (evalExpr b env).toBool)
  | _, .idx v k, env =>
    let i := match k with
      | .lit k => k.val
      | .loopVar x _ _ => match env.lookup x with | some (.nat i) => i | _ => 0
    match evalExpr v env with
    | .vec bs => .bool (bs.getD i false)
    | _ => .bool false
  | _, .ite c a b, env => if (evalExpr c env).toBool then evalExpr a env else evalExpr b env
  | _, .letE x e₁ e₂, env => evalExpr e₂ ((x, evalExpr e₁ env) :: env)
  | _, .forE i n acc init body, env =>
    (List.range n).foldl (fun v k => evalExpr body ((acc, v) :: (i, .nat k) :: env))
      (evalExpr init env)
  | _, .loopE _ init _ _, env => evalExpr init env

/-- Report §7.2.2 — the value of a parameter of type `τ` read from input bits `o, o+1, …`. -/
def Val.ofInput (x : Nat → Bool) (o : Nat) : Ty → Val
  | .bool => .bool (x o)
  | .vec m => .vec ((List.range m).map fun j => x (o + j))
  | .nat m => .nat (((List.range (Ty.width (.nat m))).map fun j =>
      if x (o + j) then 2 ^ j else 0).sum)
  | .unit => .unit

/-- Report §5.3.3, §7.2 (Stage 9b, decision 1) — the reference meaning of a typed program as a
predicate `Reg n → Bool` (`Reg n = Fin n → Bool`): the first bit of the entry `fn`'s value, input
bit `k` being `x[k]` (`false` beyond `n`). Programs with `loop … while` are rejected before
evaluation (`TypedProgram.hasLoop`). -/
def evalProgram (tp : TypedProgram) {n : Nat} (x : Fin n → Bool) : Bool :=
  let bit (k : Nat) : Bool := if h : k < n then x ⟨k, h⟩ else false
  let (_, env) := tp.params.foldl (fun (o, env) (p, τ) =>
    (o + τ.width, (p, Val.ofInput bit o τ) :: env)) (0, [])
  ((evalExpr tp.body env).bitsAt tp.ret).headD false

end CQRV.DSL

end
