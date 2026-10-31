module

public import CQRV.DSL.Check

/-!
# CQRV.DSL.Render

Report §7.2.2, §8.4.4, §5.3.3 (Stage 16b; docs/tasks/STAGE16_TASK.md B1) — the Lean literal of a
typed program, written into every generated `Cert.lean` as `def prog : DSL.TypedProgram := …` so
that the certificate states the front-end theorem at its instance: `prog_scoped` by `decide`,
`net_ok : toNetwork prog = .ok net` by `decide +kernel` (the kernel re-runs the translation on the
literal and compares with the committed network), `front_end` from `toNetwork_pred` (Stage 16a).

The printer is structural, one equation per constructor, and **unverified**: a wrong literal gives
a different network and fails `net_ok` in the kernel; a literal that happened to give the same
network would state the theorem about that other term. This is why the printer belongs to the
declared trust boundary together with the parser and the surface checker (report §5.3.3, schema
1.8.0 wording). Implicit type arguments are written out (`(n := 8)`, `(σ := .bool)`), so the
literal elaborates without inference across sub-terms; `Fin` literals and loop bounds carry
`by decide`; strings go through `String.quote`.
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.1 — a type as a Lean term of type `Ty`. -/
def Ty.renderLean : Ty → String
  | .bool => ".bool"
  | .vec n => s!"(.vec {n})"
  | .nat n => s!"(.nat {n})"
  | .unit => ".unit"

/-- Report §7.1.4 — an `idx` argument as a Lean term of type `IdxArg n`. -/
def IdxArg.renderLean {n : Nat} : IdxArg n → String
  | .lit k => s!"(.lit ⟨{k.val}, by decide⟩)"
  | .loopVar x m _ => s!"(.loopVar {x.quote} {m} (by decide))"

/-- Report §7.2.2 — a typed term as a Lean term of type `TExpr τ`. -/
def TExpr.renderLean : {τ : Ty} → TExpr τ → String
  | _, .var x τ => s!"(.var {x.quote} {τ.renderLean})"
  | _, .lit b => s!"(.lit {b})"
  | _, .not a => s!"(.not {a.renderLean})"
  | _, .and a b => s!"(.and {a.renderLean} {b.renderLean})"
  | _, .or a b => s!"(.or {a.renderLean} {b.renderLean})"
  | _, .xor a b => s!"(.xor {a.renderLean} {b.renderLean})"
  | _, @TExpr.idx n v k => s!"(.idx (n := {n}) {v.renderLean} {k.renderLean})"
  | _, .ite c a b => s!"(.ite {c.renderLean} {a.renderLean} {b.renderLean})"
  | _, @TExpr.letE σ _ x e₁ e₂ =>
    s!"(.letE (σ := {σ.renderLean}) {x.quote} {e₁.renderLean} {e₂.renderLean})"
  | _, @TExpr.forE σ i n acc init body =>
    s!"(.forE (σ := {σ.renderLean}) {i.quote} {n} {acc.quote} {init.renderLean} {body.renderLean})"
  | _, @TExpr.loopE σ acc init cond body =>
    s!"(.loopE (σ := {σ.renderLean}) {acc.quote} {init.renderLean} {cond.renderLean} \
      {body.renderLean})"

/-- Report §7.2.2, §8.4.4 — a typed program as a Lean structure instance of `TypedProgram`
(the `prog` of `Cert.lean`; the body on one line). -/
def TypedProgram.renderLean (tp : TypedProgram) : String :=
  let params := ", ".intercalate (tp.params.map fun (p, τ) => s!"({p.quote}, {τ.renderLean})")
  s!"\{ name := {tp.name.quote}, params := [{params}], ret := {tp.ret.renderLean},\n    \
    body := {tp.body.renderLean} }"

end CQRV.DSL

end
