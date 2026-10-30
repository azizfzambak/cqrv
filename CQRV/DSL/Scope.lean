module

public import CQRV.DSL.Eval

/-!
# CQRV.DSL.Scope

Report §7.2–7.4 (the extractor ℰ as a total compiler on typing derivations), §5.3.3 (declared
trust boundaries); docs/tasks/STAGE16_TASK.md A1 (Stage 16a) — the **scoping predicate** of a
typed term.

`TExpr τ` is intrinsically typed except for variables: `.var x τ` and `.idx _ (.loopVar x m _)`
carry a name, and nothing in the term ties the name to its binder's type. `evalExpr (.var x _) env`
returns `(env.lookup x).getD .unit`; `ToNetwork.build (.var x _) env` fails unless `x` has bits (or
is a loop index of type `Nat m`). The surface checker guarantees the discipline, but that is not
a theorem about `TExpr`. So the front-end theorems (`CQRV.Synthesis.NetworkCorrect`) take the
decidable hypothesis `tp.scoped = true`: checked by `decide` in every certificate (Stage 16b) and
by `#guard` on the corpus (Stage 16a). That `check` produces scoped terms is **not** proved
(parser and surface checker remain unverified).

* `Scope`: what a name denotes — a value of type `τ` or a `for` index over `[0 ..< m]`;
  `Ctx`: innermost binding first, like `Env` and the environments of `evalExpr` / `build`.
* `TExpr.scoped e ctx`: every variable is bound at its type (a `for` index may be read as a
  value of type `Nat m`, as `evalExpr` / `build` allow), structural, total, `decide`-able.
* `TypedProgram.ctx`: the parameters' context, built by the **same** `foldl` shape as
  `evalProgram` and `toNetwork` build their environments (a repeated parameter name shadows
  identically); `TypedProgram.scoped`, `TypedProgram.arity` (the `n` of `toNetwork`).
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.4 (Stage 16a) — what a name in scope denotes: a value of type `τ` (parameter,
`let`, accumulator) or a `for` loop variable over `[0 ..< m]`. -/
inductive Scope where
  | val (τ : Ty)
  | loop (m : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.1.4 (Stage 16a) — a scoping context, innermost binding first (like `Env`). -/
abbrev Ctx := List (String × Scope)

/-- Report §7.2 (Stage 16a) — the scoping predicate: every `var x τ` is bound to a value of type
`τ`, or `τ = Nat m` and `x` is a `for` index over `[0 ..< m]`; every `idx _ (loopVar x m _)` reads
a `for` index over `[0 ..< m]`; binders extend the context as `evalExpr` / `build` extend their
environments. Structural and total. -/
def TExpr.scoped : {τ : Ty} → TExpr τ → Ctx → Bool
  | τ, .var x _, ctx =>
    match ctx.lookup x with
    | some (.val σ) => σ == τ
    | some (.loop m) => τ == .nat m
    | none => false
  | _, .lit _, _ => true
  | _, .not a, ctx => a.scoped ctx
  | _, .and a b, ctx => a.scoped ctx && b.scoped ctx
  | _, .or a b, ctx => a.scoped ctx && b.scoped ctx
  | _, .xor a b, ctx => a.scoped ctx && b.scoped ctx
  | _, .idx v (.lit _), ctx => v.scoped ctx
  | _, .idx v (.loopVar x m _), ctx => (ctx.lookup x == some (.loop m)) && v.scoped ctx
  | _, .ite c a b, ctx => c.scoped ctx && a.scoped ctx && b.scoped ctx
  | _, @TExpr.letE σ _ x e₁ e₂, ctx => e₁.scoped ctx && e₂.scoped ((x, .val σ) :: ctx)
  | _, @TExpr.forE σ i n acc init body, ctx =>
    init.scoped ctx && body.scoped ((acc, .val σ) :: (i, .loop n) :: ctx)
  | _, @TExpr.loopE σ acc init cond body, ctx =>
    init.scoped ctx && cond.scoped ((acc, .val σ) :: ctx) && body.scoped ((acc, .val σ) :: ctx)

/-- Report §7.2.2 (Stage 16a) — the parameters' context, by the `foldl` shape of `evalProgram`
and `toNetwork` (parameters laid out from bit 0; the offset is carried but unused here). -/
def TypedProgram.ctx (tp : TypedProgram) : Ctx :=
  (tp.params.foldl (fun (o, ctx) (p, τ) => (o + τ.width, (p, Scope.val τ) :: ctx)) (0, [])).2

/-- Report §7.2 (Stage 16a) — the entry `fn` is scoped: its body under the parameters'
context. Decidable; the hypothesis of `toNetwork_pred` / `toNetwork_WF` / `toNetwork_succeeds`. -/
def TypedProgram.scoped (tp : TypedProgram) : Bool := tp.body.scoped tp.ctx

/-- Report §7.2.2 — the input arity of a program: the `n` of `toNetwork` and of the certificate
(`Reg n`). -/
def TypedProgram.arity (tp : TypedProgram) : Nat := (tp.params.map (·.2.width)).sum

end CQRV.DSL

end
