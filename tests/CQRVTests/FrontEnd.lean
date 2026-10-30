module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
import CQRV.Certify.Basic
import CQRV.Certify.Specialize
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic
meta import CQRV.Certify.Basic
meta import CQRV.Certify.Specialize

/-!
# Tests for the front-end theorems (report §7.2–7.4, §5.3.3; Stage 16a)

* `TypedProgram.scoped` holds on the corpus (every example and test predicate, the `mixSrc` /
  `natSrc` programs of `tests/CQRVTests/Eval.lean`) and fails on a free variable and on a
  variable at the wrong type.
* `toNetwork_pred` instantiated on `grover_pred_037` (typed term written out, the network of
  `toNetwork` by `decide +kernel`): the theorem agrees with `validateFrontEnd`, which is now a
  regression test of the executable path.
* The axioms of `toNetwork_succeeds`, `toNetwork_WF`, `toNetwork_pred`: the standard three.
-/

namespace CQRV.Tests.FrontEnd

open CQRV CQRV.DSL CQRV.Synthesis CQRV.Certify

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
def chainSrc : String := include_str "../../examples/and_chain_8.cqr"
def orSrc : String := include_str "../../examples/search_or.cqr"
def aluSrc : String := include_str "../../examples/simple_alu_x0_1.cqr"
def xorSrc : String := include_str "../../tests/certify/xor_pred.cqr"
def ifSrc : String := include_str "../../tests/certify/if_pred.cqr"

/-- `for`, `let`, a call and `if` on `Vec Bool 2` (tests/CQRVTests/Eval.lean). -/
def mixSrc : String :=
  "fn f(a: Bool, b: Bool) -> Bool { a xor b }\n\
   fn mix(x: Vec Bool 4) -> Bool {\n\
     let p = for i in [0 ..< 4] with acc = false do acc xor idx(x, i) in\n\
     let v = if idx(x, 0) then x else x in\n\
     f(p, idx(v, 1))\n\
   }"

/-- A `Nat 3` parameter returned as the result (tests/CQRVTests/Eval.lean). -/
def natSrc : String := "fn g(k: Nat 3, b: Bool) -> Nat 3 { if b then k else k }"

/-- `tp.scoped` of a source after the front end. -/
def scopedOf (src : String) : Option Bool :=
  ((parse src >>= check).map TypedProgram.scoped).toOption

/-! ## The corpus is scoped -/

#guard scopedOf groverSrc == some true
#guard scopedOf chainSrc == some true
#guard scopedOf orSrc == some true
#guard scopedOf aluSrc == some true
#guard scopedOf xorSrc == some true
#guard scopedOf ifSrc == some true
#guard scopedOf mixSrc == some true
#guard scopedOf natSrc == some true

/-! ## Hand-built terms: a free variable, a variable at the wrong type -/

#guard (TExpr.var "x" .bool).scoped [] == false
#guard (TExpr.var "x" .bool).scoped [("x", .val (.vec 2))] == false
#guard (TExpr.var "x" .bool).scoped [("x", .val .bool)] == true
-- a `for` index may be read as a value of type `Nat m`, and only at that `m`
#guard (TExpr.var "i" (.nat 4)).scoped [("i", .loop 4)] == true
#guard (TExpr.var "i" (.nat 3)).scoped [("i", .loop 4)] == false
-- `idx` by an unbound loop variable; the inner binding shadows the outer one
#guard (TExpr.idx (.var "x" (.vec 4)) (.loopVar "i" 4 (Nat.le_refl 4))).scoped
  [("x", .val (.vec 4))] == false
#guard (TExpr.var "x" .bool).scoped [("x", .val .bool), ("x", .val (.vec 2))] == true
#guard (TExpr.var "x" .bool).scoped [("x", .val (.vec 2)), ("x", .val .bool)] == false

/-! ## `toNetwork_pred` on `grover_pred_037` -/

/-- The typed term of `examples/grover_pred_037.cqr` (`let b0 = idx(x, 0) in let b3 = idx(x, 3)
in let b7 = idx(x, 7) in b0 and b3 and b7`). -/
def groverProg : TypedProgram :=
  { name := "grover_pred_037", params := [("x", .vec 8)], ret := .bool,
    body := .letE "b0" (.idx (.var "x" (.vec 8)) (.lit ⟨0, by decide⟩))
      (.letE "b3" (.idx (.var "x" (.vec 8)) (.lit ⟨3, by decide⟩))
        (.letE "b7" (.idx (.var "x" (.vec 8)) (.lit ⟨7, by decide⟩))
          (.and (.and (.var "b0" .bool) (.var "b3" .bool)) (.var "b7" .bool)))) }

#guard groverProg.scoped
#guard groverProg.arity == 8
#guard !groverProg.hasLoop

/-- Its network, as `toNetwork` builds it (the `net` literal of the committed certificate). -/
def groverN : Network := okPayload (toNetwork groverProg)

theorem groverN_ok : toNetwork groverProg = .ok groverN :=
  except_eq_ok_okPayload _ (by decide +kernel)

/-- The front-end theorem at this instance. -/
theorem grover_front_end : ∀ x : Fin 8 → Bool, groverN.pred 8 x = evalProgram groverProg x :=
  toNetwork_pred groverProg groverN groverN_ok (by decide)

theorem grover_net_WF : groverN.WF := toNetwork_WF groverProg groverN groverN_ok (by decide)

-- the executable path agrees with the theorem's instance, on all 2^8 inputs
#guard (List.range 256).all fun k =>
  groverN.pred 8 (inputBits 8 k) == evalProgram groverProg (inputBits 8 k)
#guard validateFrontEnd groverProg groverN 8 == .validated 8
-- the hand-written term builds the same network as the parsed source
#guard match parse groverSrc >>= check >>= toNetwork with
  | .ok N => N.nodes.toList == groverN.nodes.toList && N.outputs == groverN.outputs &&
      N.nInputs == groverN.nInputs
  | .error _ => false
#guard groverN.nInputs == 8 && groverN.andCount == 2

/-! ## Axioms -/

/-- info: 'CQRV.Synthesis.toNetwork_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toNetwork_succeeds

/-- info: 'CQRV.Synthesis.toNetwork_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toNetwork_WF

/-- info: 'CQRV.Synthesis.toNetwork_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toNetwork_pred

end CQRV.Tests.FrontEnd
