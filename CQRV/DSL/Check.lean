module

public import CQRV.DSL.Diagnostic

/-!
# CQRV.DSL.Check

Report §4.2.2 ("two layers of acceptance"), §7.1.1–7.1.4 — the permissive *surface* type
checker (the report's "Stage 1" elaborator). It rejects ill-formed programs (types, `idx`
bounds, branch types, the fold discipline of `for`/`loop`, unbound names) and non-structural
recursion (any cycle in the call graph, direct or mutual), then inlines every call and returns
a `TypedProgram` whose body is an intrinsically typed term `TExpr τ` — the typing derivation
`D : Γ ⊢ e : τ` on which ℰ is defined (§7.2.2). A `loop … while` passes this checker; it is
rejected later by the matcher (§4.2.2).
-/

@[expose] public section

namespace CQRV.DSL

/-- Report §7.1.4, `idx(e, k)` — the index of a well-typed `idx` into `Vec Bool n`: a literal
`k < n`, or a `for`-bound loop variable ranging over `[0 ..< m]` with `m ≤ n`
(DECISIONS.md 2026-10-23, decision 2). -/
inductive IdxArg (n : Nat) where
  | lit (k : Fin n)
  | loopVar (x : String) (m : Nat) (h : m ≤ n)

/-- Report §7.2.2, the typing derivation `D : Γ ⊢ e : τ` — surface terms after checking and
call inlining, indexed by their type. Variables carry their (core) name; calls are gone. -/
inductive TExpr : Ty → Type where
  | var (x : String) (τ : Ty) : TExpr τ
  | lit (b : Bool) : TExpr .bool
  | not : TExpr .bool → TExpr .bool
  | and : TExpr .bool → TExpr .bool → TExpr .bool
  | or : TExpr .bool → TExpr .bool → TExpr .bool
  | xor : TExpr .bool → TExpr .bool → TExpr .bool
  | idx {n : Nat} : TExpr (.vec n) → IdxArg n → TExpr .bool
  | ite {τ : Ty} : TExpr .bool → TExpr τ → TExpr τ → TExpr τ
  | letE {σ τ : Ty} (x : String) : TExpr σ → TExpr τ → TExpr τ
  /-- `for i in [0 ..< n] with acc = init do body`; `i : Nat n`, `acc : σ` in `body`. -/
  | forE {σ : Ty} (i : String) (n : Nat) (acc : String) : TExpr σ → TExpr σ → TExpr σ
  /-- `loop acc = init while cond do body`; `acc : σ` in `cond` and `body`. -/
  | loopE {σ : Ty} (acc : String) : TExpr σ → TExpr .bool → TExpr σ → TExpr σ

/-- Report §7.2.2 — a typed term together with its type. -/
structure Typed where
  ty : Ty
  e : TExpr ty

/-- Report §4.2.2 — output of the surface checker: the entry `fn` (the last one in the file)
with all calls inlined. -/
structure TypedProgram where
  name : String
  params : List (String × Ty)
  ret : Ty
  body : TExpr ret

/-- Report §7.1.4 — what a name in scope denotes: a value of type `τ` (parameter, `let`,
accumulator) or a `for` loop variable over `[0 ..< m]`. Both carry the core name. -/
inductive Binding where
  | val (core : String) (τ : Ty)
  | loopVar (core : String) (m : Nat)

/-- Report §7.1.4 — typing context Γ, innermost binding first. -/
abbrev Env := List (String × Binding)

/-- Checker monad: a counter for fresh names of inlined parameters. -/
abbrev CM := StateT Nat (Except Diagnostic)

namespace Check

/-- Raise a surface diagnostic. -/
def err {α : Type} (code : Code) (p : Pos) (msg : String) : CM α :=
  throw (Diagnostic.at .surface code p msg)

/-- Require type `σ`, else a diagnostic with `code`. -/
def expectTy (code : Code) (p : Pos) (what : String) (t : Typed) (σ : Ty) : CM (TExpr σ) :=
  if h : t.ty = σ then pure (h ▸ t.e)
  else err code p s!"{what}: expected {σ.render}, found {t.ty.render}"

mutual
/-- Report §7.1.4 — calls `(f, position)` occurring in an expression. -/
def callsOf : Expr → List (String × Pos)
  | .var .. | .lit .. => []
  | .not _ e | .idx _ e _ => callsOf e
  | .and _ a b | .or _ a b | .xor _ a b | .letE _ _ a b => callsOf a ++ callsOf b
  | .forE _ _ _ _ a b => callsOf a ++ callsOf b
  | .loopE _ _ a b c | .ite _ a b c => callsOf a ++ callsOf b ++ callsOf c
  | .call p f args => (f, p) :: callsOfList args
/-- `callsOf` on a list of arguments. -/
def callsOfList : List Expr → List (String × Pos)
  | [] => []
  | e :: es => callsOf e ++ callsOfList es
end

mutual
/-- Number of nodes of an expression (bounds the elaboration depth). -/
def sizeOfExpr : Expr → Nat
  | .var .. | .lit .. => 1
  | .not _ e | .idx _ e _ => sizeOfExpr e + 1
  | .and _ a b | .or _ a b | .xor _ a b | .letE _ _ a b => sizeOfExpr a + sizeOfExpr b + 1
  | .forE _ _ _ _ a b => sizeOfExpr a + sizeOfExpr b + 1
  | .loopE _ _ a b c | .ite _ a b c => sizeOfExpr a + sizeOfExpr b + sizeOfExpr c + 1
  | .call _ _ args => sizeOfList args + 1
/-- `sizeOfExpr` on a list of arguments. -/
def sizeOfList : List Expr → Nat
  | [] => 0
  | e :: es => sizeOfExpr e + sizeOfList es
end

/-- Report §7.1.2 — the first `fn` (in source order) that lies on a cycle of the call graph,
with the position of its first call into the cycle. `reach` is iterated `fns.length` times,
which saturates. -/
def findCycle (fns : List FnDecl) : Option (FnDecl × String × Pos) :=
  let callees (f : String) : List String :=
    match fns.find? (·.name == f) with
    | some d => (callsOf d.body).map (·.1)
    | none => []
  let reach (start : List String) : List String :=
    (List.range fns.length).foldl
      (fun acc _ => (acc ++ acc.flatMap callees).eraseDups) start.eraseDups
  fns.findSome? fun d =>
    (callsOf d.body).find? (fun (c, _) => c == d.name || (reach [c]).contains d.name)
      |>.map fun (c, p) => (d, c, p)

/-- Report §7.1.4, §4.2.2 — surface typing of one expression, inlining calls. `fuel` bounds
the recursion depth; `checkProgram` passes the total program size, which suffices once the
call graph is acyclic. -/
def checkExpr (fns : List FnDecl) : Nat → Env → Expr → CM Typed
  | 0, _, e => err .typeError e.pos "internal: elaboration depth limit reached"
  | fuel + 1, env, e =>
    let go := checkExpr fns fuel
    let bool (env : Env) (e : Expr) (what : String) : CM (TExpr .bool) := do
      expectTy .typeError e.pos what (← go env e) .bool
    match e with
    | .var p x =>
      match env.lookup x with
      | some (.val c τ) => pure ⟨τ, .var c τ⟩
      | some (.loopVar c m) => pure ⟨.nat m, .var c (.nat m)⟩
      | none => err .unboundVariable p s!"unbound variable `{x}`"
    | .lit _ b => pure ⟨.bool, .lit b⟩
    | .not _ a => return ⟨.bool, .not (← bool env a "operand of `not`")⟩
    | .and _ a b =>
      return ⟨.bool, .and (← bool env a "operand of `and`") (← bool env b "operand of `and`")⟩
    | .or _ a b =>
      return ⟨.bool, .or (← bool env a "operand of `or`") (← bool env b "operand of `or`")⟩
    | .xor _ a b =>
      return ⟨.bool, .xor (← bool env a "operand of `xor`") (← bool env b "operand of `xor`")⟩
    | .idx _ v r => do
      let tv ← go env v
      match tv with
      | ⟨.vec n, ev⟩ =>
        match r with
        | .lit q k =>
          if h : k < n then return ⟨.bool, .idx ev (.lit ⟨k, h⟩)⟩
          else err .indexOutOfBounds q s!"index {k} out of bounds for Vec Bool {n}"
        | .var q x =>
          match env.lookup x with
          | some (.loopVar c m) =>
            if h : m ≤ n then return ⟨.bool, .idx ev (.loopVar c m h)⟩
            else
              let msg := s!"loop variable `{x}` ranges over [0 ..< {m}], \
                out of bounds for Vec Bool {n}"
              err .indexOutOfBounds q msg
          | some (.val ..) =>
            let msg := s!"index `{x}` of `idx` must be a literal or a `for`-bound loop variable"
            err .typeError q msg
          | none => err .unboundVariable q s!"unbound variable `{x}`"
      | ⟨τ, _⟩ => err .typeError v.pos s!"`idx` expects Vec Bool n, found {τ.render}"
    | .forE p i n acc init body => do
      if i == acc then
        err .foldDiscipline p s!"loop variable and accumulator must differ (both `{i}`)"
      let ti ← go env init
      let tb ← go ((acc, .val acc ti.ty) :: (i, .loopVar i n) :: env) body
      let eb ← expectTy .foldDiscipline body.pos
        "the body of a `for` returns the next accumulator" tb ti.ty
      return ⟨ti.ty, .forE i n acc ti.e eb⟩
    | .loopE _ acc init cond body => do
      let ti ← go env init
      let env' := (acc, .val acc ti.ty) :: env
      let ec ← bool env' cond "condition of `loop … while`"
      let eb ← expectTy .foldDiscipline body.pos
        "the body of a `loop` returns the next accumulator" (← go env' body) ti.ty
      return ⟨ti.ty, .loopE acc ti.e ec eb⟩
    | .ite _ c a b => do
      let ec ← bool env c "condition of `if`"
      let ta ← go env a
      let eb ← expectTy .typeError b.pos "branches of `if` must have the same type"
        (← go env b) ta.ty
      return ⟨ta.ty, .ite ec ta.e eb⟩
    | .letE _ x e₁ e₂ => do
      let t₁ ← go env e₁
      let t₂ ← go ((x, .val x t₁.ty) :: env) e₂
      return ⟨t₂.ty, .letE x t₁.e t₂.e⟩
    | .call p f args => do
      let some d := fns.find? (·.name == f)
        | err .unboundVariable p s!"unknown function `{f}`"
      if d.params.length != args.length then
        err .typeError p s!"`{f}` expects {d.params.length} argument(s), got {args.length}"
      -- Arguments are checked in the caller's scope, then bound to fresh names (`f.x#k`,
      -- not a user identifier, so no capture) by nested `let`s around the callee body.
      let mut binds : Array (String × Typed) := #[]
      let mut calleeEnv : Env := []
      for (q, a) in d.params.zip args do
        let ta ← go env a
        let ea ← expectTy .typeError a.pos s!"argument `{q.name}` of `{f}`" ta q.ty
        let k ← modifyGet fun k => (k, k + 1)
        let c := s!"{f}.{q.name}#{k}"
        binds := binds.push (c, ⟨q.ty, ea⟩)
        calleeEnv := (q.name, .val c q.ty) :: calleeEnv
      let tb ← go calleeEnv d.body
      let eb ← expectTy .typeError d.body.pos s!"body of `{f}`" tb d.ret
      return ⟨d.ret, binds.foldr (fun (c, ta) acc => .letE c ta.e acc) eb⟩

/-- Report §4.2.2 — `check : Program → Except Diagnostic TypedProgram`: duplicate names,
call-graph cycles (`non_structural_recursion`), then surface typing of every `fn`; the entry
point is the last `fn`. -/
def checkProgram (prog : Program) : Except Diagnostic TypedProgram := do
  let fns := prog.fns
  let run {α : Type} (m : CM α) : Except Diagnostic α := (·.1) <$> m.run 0
  -- duplicate function / parameter names
  for (d, k) in fns.zipIdx do
    if (fns.take k).any (·.name == d.name) then
      run (err .typeError d.pos s!"duplicate function `{d.name}`")
    for (q, j) in d.params.zipIdx do
      if (d.params.take j).any (·.name == q.name) then
        run (err .typeError q.pos s!"duplicate parameter `{q.name}` of `{d.name}`")
  if let some (d, c, p) := findCycle fns then
    run (err .nonStructuralRecursion p
      s!"`{d.name}` is recursive (call to `{c}` closes a cycle in the call graph); only \
        structurally bounded recursion is admitted and the DSL has no inductive types \
        (report §7.1.2, §4.2.2)")
  let fuel := (fns.map (sizeOfExpr ·.body)).sum + fns.length + 1
  let mut entry : Option TypedProgram := none
  for d in fns do
    let env : Env := d.params.reverse.map fun q => (q.name, .val q.name q.ty)
    let body ← run do
      let t ← checkExpr fns fuel env d.body
      expectTy .typeError d.body.pos s!"body of `{d.name}`" t d.ret
    entry := some { name := d.name, params := d.params.map (fun q => (q.name, q.ty)),
                    ret := d.ret, body }
  match entry with
  | some tp => pure tp
  | none => throw (Diagnostic.at .parse .syntaxError ⟨1, 1⟩ "expected at least one `fn`")

end Check

/-- Report §4.2.2 — `check : Program → Except Diagnostic TypedProgram` (stage `surface`). -/
def check (prog : Program) : Except Diagnostic TypedProgram := Check.checkProgram prog

end CQRV.DSL

end
