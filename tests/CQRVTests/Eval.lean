module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
import CQRV.Certify.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic
meta import CQRV.Certify.Basic

/-!
# Tests for `CQRV.DSL.Eval` and `CQRV.Certify.FrontEnd` (report §5.3.3, §7.2; Stage 9b, task 1)

The reference evaluator `evalProgram` against `Network.pred (toNetwork …)` on all `2ⁿ` inputs
(`validateFrontEnd`) for every corpus file with a network, the evaluator on hand-checked values
(`for`, `let`, `if` on `Vec`, calls, `Nat` parameters), and the negative cases: a wrong network is
a `mismatch` with the first bad input, `loop … while` is `unbounded`, `n > 16` keeps the Stage 8b
wording. The 100 random predicates are in `tests/diff/frontend_diff.py`.
-/

namespace CQRV.Tests.Eval

open CQRV CQRV.DSL CQRV.Synthesis CQRV.Certify

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"
def chainSrc : String := include_str "../../examples/and_chain_8.cqr"
def orSrc : String := include_str "../../examples/search_or.cqr"
def aluSrc : String := include_str "../../examples/simple_alu_x0_1.cqr"
def whileSrc : String := include_str "../../examples/search_while.cqr"
def xorSrc : String := include_str "../../tests/certify/xor_pred.cqr"
def ifSrc : String := include_str "../../tests/certify/if_pred.cqr"

/-- Front end. -/
def typed (src : String) : Except Diagnostic TypedProgram := parse src >>= check

/-- Validation outcome of a source (front end, `toNetwork`, then `validateFrontEnd`). -/
def validate (src : String) : Option FrontEndCheck :=
  (do let tp ← typed src; let N ← toNetwork tp; return validateFrontEnd tp N N.nInputs).toOption

/-- The evaluator's value on input number `x`. -/
def evalAt (src : String) (n x : Nat) : Option Bool :=
  ((typed src).map fun tp => evalProgram tp (inputBits n x)).toOption

/-! ## The corpus: evaluator = network on all 2ⁿ inputs -/

#guard validate groverSrc == some (.validated 8)
#guard validate chainSrc == some (.validated 9)
#guard validate orSrc == some (.validated 4)
#guard validate aluSrc == some (.validated 6)
#guard validate xorSrc == some (.validated 4)
#guard validate ifSrc == some (.validated 6)
#guard ((typed whileSrc).map TypedProgram.hasLoop).toOption == some true
#guard ((typed whileSrc).map fun tp => validateFrontEnd tp default 8).toOption ==
  some .unbounded

/-! ## The evaluator on hand-checked values -/

-- grover_pred_037: x0 ∧ x3 ∧ x7 (input 137 = bits 0, 3, 7)
#guard evalAt groverSrc 8 137 == some true
#guard evalAt groverSrc 8 9 == some false
-- simple_alu_x0_1 (bit 1 of the RevLib Simple ALU): op = 0 (add), x1 = 1, x2 = 1 → 2, bit 1 = 1
-- input bits: op.0 op.1 x1.0 x1.1 x2.0 x2.1 = 0 0 1 0 1 0 → x = 4 + 16
#guard evalAt aluSrc 6 20 == some true
-- op = 3 (xor), x1 = 3, x2 = 1 → 2, bit 1 = 1; op = 2 (mul), x1 = 3, x2 = 3 → 9 mod 4 = 1, bit 1 = 0
#guard evalAt aluSrc 6 (3 + 4 + 8 + 16) == some true
#guard evalAt aluSrc 6 (2 + 4 + 8 + 16 + 32) == some false

/-- `for`, `let`, a call and `if` on `Vec Bool 2`. -/
def mixSrc : String :=
  "fn f(a: Bool, b: Bool) -> Bool { a xor b }\n\
   fn mix(x: Vec Bool 4) -> Bool {\n\
     let p = for i in [0 ..< 4] with acc = false do acc xor idx(x, i) in\n\
     let v = if idx(x, 0) then x else x in\n\
     f(p, idx(v, 1))\n\
   }"
-- parity(x0, x1, x2, x3) xor x1 = x0 xor x2 xor x3
#guard (List.range 16).all fun x =>
  evalAt mixSrc 4 x == some ((x % 2 + x / 4 % 2 + x / 8 % 2) % 2 == 1)
#guard validate mixSrc == some (.validated 4)

/-- A `Nat 3` parameter (2 bits, little-endian) returned as the result: the result bit is bit 0
of the number, as `Network.pred` reads the first output bit. -/
def natSrc : String := "fn g(k: Nat 3, b: Bool) -> Nat 3 { if b then k else k }"
#guard (List.range 8).all fun x => evalAt natSrc 3 x == some (x % 2 == 1)
#guard validate natSrc == some (.validated 3)

/-! ## Negative cases -/

/-- The network of `search_or` with the output moved to the first input node: it computes
`x0`, not `x0 ∨ x1`; the first disagreement is input 2 (x1 = 1). -/
def wrongOr : Option FrontEndCheck :=
  (do let tp ← typed orSrc; let N ← toNetwork tp
      return validateFrontEnd tp { N with outputs := [0] } 4).toOption
#guard wrongOr == some (.mismatch 4 2 true false)
#guard (wrongOr.bind (·.trustText)) == none
#guard ((wrongOr.bind fun c => c.diagnostic? "search_or" ⟨1, 1⟩).map (·.code.name)) ==
  some "front_end_mismatch"
#guard ((wrongOr.bind fun c => c.diagnostic? "search_or" ⟨1, 1⟩).map (·.stage.name)) ==
  some "validate"
#guard bitString 4 2 == "0100"

-- `n > 16`: no enumeration, the Stage 8b wording.
#guard ((typed orSrc).map fun tp => validateFrontEnd tp default 17).toOption == some (.tooLarge 17)
#guard (FrontEndCheck.tooLarge 17).trustText == some frontEndTrust
#guard (FrontEndCheck.validated 6).trustText == some
  "DSL → network: exhaustively validated (2^6 inputs) by the unverified evaluator; not kernel-checked"

/-! ## Truth tables (the format of `cqr check --truth-table`) -/

#guard ((typed orSrc).map fun tp => truthTable 4 (evalProgram tp)).toOption ==
  some "0111011101110111"

end CQRV.Tests.Eval
