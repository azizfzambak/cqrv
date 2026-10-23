module

import CQRV.DSL.Basic
meta import CQRV.DSL.Basic

/-!
# Tests for `CQRV.DSL` (report §4.2.2–4.2.3, §7.1.4, §7.2.2–7.2.3, §7.3.2)

The corpus files of `examples/` are read at elaboration time with `include_str`. All checks are
`#guard` (compiled evaluation); one `example … := by decide` shows that `extract` reduces in
the kernel on a hand-built typed term (it is a total, structurally recursive function).
-/

namespace CQRV.Tests.DSL

open CQRV.DSL

/-- §7.1.4, verbatim. -/
def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
/-- §4.2.3 Table 2, row 2. -/
def whileSrc : String := include_str "../../examples/search_while.cqr"
/-- §4.2.3 Table 2, row 3. -/
def treeSrc : String := include_str "../../examples/allocate_tree.cqr"

/-- Front end + ℰ. -/
def sig (src : String) : Except Diagnostic SigmaIn := extract <$> (parse src >>= check)

/-- Diagnostic of a rejected program, if any. -/
def diag (src : String) : Option Diagnostic :=
  match parse src >>= check with
  | .ok _ => none
  | .error d => some d

/-! ## Parser round-trip on the corpus: parse succeeds, positions are present -/

mutual
/-- Every node has a 1-based position. -/
def posOk : Expr → Bool
  | .var p _ | .lit p _ => p.line ≥ 1 && p.col ≥ 1
  | .not p e | .idx p e _ => p.line ≥ 1 && p.col ≥ 1 && posOk e
  | .and p a b | .or p a b | .xor p a b | .letE p _ a b | .forE p _ _ _ a b =>
    p.line ≥ 1 && p.col ≥ 1 && posOk a && posOk b
  | .loopE p _ a b c | .ite p a b c => p.line ≥ 1 && p.col ≥ 1 && posOk a && posOk b && posOk c
  | .call p _ args => p.line ≥ 1 && p.col ≥ 1 && posOkList args
/-- `posOk` on a list. -/
def posOkList : List Expr → Bool
  | [] => true
  | e :: es => posOk e && posOkList es
end

/-- Parse a source and return `(fn name, fn position, body position, all positions ok)`. -/
def shape (src : String) : Option (String × Pos × Pos × Bool) :=
  match parse src with
  | .ok { fns := [d] } => some (d.name, d.pos, d.body.pos, posOk d.body)
  | _ => none

#guard shape groverSrc == some ("grover_pred_037", ⟨1, 1⟩, ⟨2, 3⟩, true)
#guard shape whileSrc == some ("search_while", ⟨3, 1⟩, ⟨4, 3⟩, true)
#guard shape treeSrc == some ("allocate_tree", ⟨3, 1⟩, ⟨3, 63⟩, true)

-- `b0 and b3 and b7` associates to the left: `(b0 and b3) and b7` (§7.2.3 comment).
#guard match parse "fn f(x: Vec Bool 8) -> Bool { a and b and c }" with
  | .ok { fns := [{ body := .and _ (.and _ (.var _ "a") (.var _ "b")) (.var _ "c"), .. }] } => true
  | _ => false

-- A syntax error is reported by stage `parse` with its position.
#guard (diag "fn f(x: Vec Bool 4) -> Bool { idx(x, 0) and }").map
  (fun d => (d.stage, d.code, d.line, d.col)) == some (.parse, .syntaxError, 1, 45)

/-! ## §7.2.3 — the Grover signature

§7.2.2's Table 2 writes the complexity tuple as "8, 2, 3" while its own text and §7.2.3 give
AND-depth 2; the test follows §7.2.3 (open question to the reviewer). -/

#guard (sig groverSrc).toOption == some
  { problemClass := .search, arity := 8, solutionCount := some 32, andComplexity := 2,
    andDepth := 2, ancillaBudget := 2, oracle := .phaseKickback .multiplicative [0, 3, 7],
    algebra := .boolAlg, domain := [.vec 8], codomain := .bool, iter := .bounded 1 }

/-! ## §4.2.2–4.2.3, Table 2 — the frontier rows -/

-- Row 2: the `while` program passes `check` and extracts with `iter = unbounded`.
#guard diag whileSrc == none
#guard (sig whileSrc).toOption.map (·.iter) == some .unbounded

-- Row 3: `allocate_tree` stops at the surface checker with `non_structural_recursion`.
#guard (diag treeSrc).map (fun d => (d.stage, d.code)) == some (.surface, .nonStructuralRecursion)

-- Mutual recursion is caught as well.
#guard (diag "fn a(x: Bool) -> Bool { b(x) }\nfn b(y: Bool) -> Bool { a(y) }").map (·.code)
  == some .nonStructuralRecursion

/-! ## §7.3.2, Table 3 — counting rules (reviewer decision 3) -/

-- `or`: De Morgan, exactly one AND; depth max + 1.
#guard (sig "fn f(x: Vec Bool 4) -> Bool { idx(x, 0) or idx(x, 1) }").toOption.map
  (fun s => (s.andComplexity, s.andDepth, s.ancillaBudget)) == some (1, 1, 1)

-- `if`: mux `b ⊕ (c ∧ (a ⊕ b))` — ĉ∧ = ĉc + ĉa + ĉb + 1 = 0 + 1 + 0 + 1; depth = max + 1.
#guard (sig "fn f(x: Vec Bool 4) -> Bool \
    { if idx(x, 0) then idx(x, 1) and idx(x, 2) else idx(x, 3) }").toOption.map
  (fun s => (s.andComplexity, s.andDepth)) == some (2, 2)

-- `for` with `idx(x, i)`: support = [0, n), ĉ∧ = n · ĉ∧(body), iter = bounded n.
#guard (sig "fn f(x: Vec Bool 6) -> Bool \
    { for i in [0 ..< 6] with acc = true do acc and idx(x, i) }").toOption.map
  (fun s => (s.andComplexity, s.andDepth, s.oracle, s.iter, s.solutionCount))
  == some (6, 6, .phaseKickback .multiplicative [0, 1, 2, 3, 4, 5], .bounded 6, none)

-- `not`, `xor`: no AND.
#guard (sig "fn f(x: Vec Bool 4) -> Bool { not idx(x, 0) xor idx(x, 1) }").toOption.map
  (·.andComplexity) == some 0

-- `let`: uses of the bound name are shared (one AND, used twice → ĉ∧ = 1 + 1).
#guard (sig "fn f(x: Vec Bool 4) -> Bool \
    { let y = idx(x, 0) and idx(x, 1) in y and y }").toOption.map
  (fun s => (s.andComplexity, s.andDepth)) == some (2, 2)

-- Calls are inlined like `let`s: `g` contributes one AND per call.
#guard (sig "fn g(a: Bool, b: Bool) -> Bool { a and b }\n\
    fn f(x: Vec Bool 4) -> Bool { g(idx(x, 1), g(idx(x, 2), not idx(x, 0))) }").toOption.map
  (fun s => (s.andComplexity, s.andDepth, s.solutionCount)) == some (2, 2, some 2)

/-! ## §4.1.4, decision 5 — symbolic solution count -/

-- Repeated bit: not a conjunction of literals on distinct bits → `none`.
#guard (sig "fn f(x: Vec Bool 4) -> Bool { idx(x, 0) and not idx(x, 0) }").toOption.map
  (·.solutionCount) == some none
-- Not of type `Vec Bool n → Bool`: Decision class, no solution count.
#guard (sig "fn f(a: Bool, b: Bool) -> Bool { a and b }").toOption.map
  (fun s => (s.problemClass, s.arity, s.solutionCount)) == some (.decision, 2, none)

/-! ## Surface diagnostics -/

#guard (diag "fn f(x: Vec Bool 4) -> Bool { idx(x, 4) }").map (·.code) == some .indexOutOfBounds
#guard (diag "fn f(x: Vec Bool 4) -> Bool \
    { for i in [0 ..< 5] with acc = true do acc and idx(x, i) }").map (·.code)
  == some .indexOutOfBounds
#guard (diag "fn f(x: Vec Bool 4) -> Bool { y }").map (·.code) == some .unboundVariable
#guard (diag "fn f(x: Vec Bool 4) -> Bool { not x }").map (·.code) == some .typeError
#guard (diag "fn f(x: Vec Bool 4) -> Bool { let k = idx(x, 0) in idx(x, k) }").map (·.code)
  == some .typeError
#guard (diag "fn f(x: Vec Bool 4) -> Bool { if true then x else idx(x, 0) }").map (·.code)
  == some .typeError
#guard (diag "fn f(x: Vec Bool 4) -> Bool \
    { for i in [0 ..< 2] with acc = true do x }").map (·.code) == some .foldDiscipline
#guard (diag "fn f(x: Vec Bool 4) -> Bool \
    { for i in [0 ..< 2] with i = true do i }").map (·.code) == some .foldDiscipline
#guard (diag "fn f(x: Vec Bool 4) -> Bool { g(x) }").map (·.code) == some .unboundVariable

/-! ## ℰ reduces in the kernel (`decide`), on a hand-built typed term -/

/-- `x : Vec Bool 2 ⊢ idx(x, 0) or idx(x, 1) : Bool`. -/
def tpOr : TypedProgram :=
  { name := "f", params := [("x", .vec 2)], ret := .bool,
    body := .or (.idx (.var "x" (.vec 2)) (.lit 0)) (.idx (.var "x" (.vec 2)) (.lit 1)) }

example : (extract tpOr).andComplexity = 1 ∧ (extract tpOr).iter = .bounded 1 := by decide

end CQRV.Tests.DSL
