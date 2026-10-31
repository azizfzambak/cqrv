module

public import CQRV.DSL.Eval
public import CQRV.Synthesis.Network

/-!
# CQRV.Certify.FrontEnd

Report §5.3.3 (declared trust boundaries), §7.2–7.4, §9.5.1 — the front-end boundary of a
certificate.

Stage 16b (docs/tasks/STAGE16_TASK.md B1–B2): the translation typed term → network is **proved**
(`toNetwork_pred`, `CQRV/Synthesis/NetworkCorrect.lean`, Stage 16a) and every `Cert.lean` states
it at its instance (`prog`, `prog_scoped`, `net_ok`, `front_end`, kernel-checked;
`CertRequest.progBlock`); `cqr certify` declares `frontEndProvedText` in `trust_boundary.front_end`
(schema 1.8.0) and no longer runs the validation below. The parser, the surface checker and the
typed-term printer (`TypedProgram.renderLean`) remain outside the kernel; `predicate_hash` binds
the source.

Stages 9b–16a (reviewer decision 1; DECISIONS.md 2026-10-25): for `n ≤ 16` inputs, `cqr certify`
compared the reference evaluator `evalProgram` with `Network.pred (toNetwork …)` on all `2ⁿ`
inputs (`validateFrontEnd`) and declared the outcome; for `n > 16` the Stage 8b wording stayed.
The validation, its wordings and the diagnostic `front_end_mismatch` stay here as the regression
test of the executable path against the Python reference (`cqr check --truth-table`,
`tests/diff/frontend_diff.py`, `tests/CQRVTests/Eval.lean`); `front_end_mismatch` is unreachable
from `cqr certify` since Stage 16b.
-/

@[expose] public section

namespace CQRV.Certify

open CQRV.DSL CQRV.Synthesis

/-- Report §5.3.3 — the largest input arity for which the front end is validated exhaustively
(decision 1: `2¹⁶` evaluations of each side). -/
def frontEndLimit : Nat := 16

/-- Report §5.3.3 — outcome of the front-end validation. `mismatch x`: the first input (bit `k`
of `x` = input bit `k`) on which the evaluator and the network disagree, with both values. -/
inductive FrontEndCheck where
  | validated (n : Nat)
  | tooLarge (n : Nat)
  | unbounded
  | mismatch (n x : Nat) (evaluator network : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- Report §7.2.2 — the input assignment numbered `x` (bit `k` of `x` = input bit `k`). -/
def inputBits (n x : Nat) : Fin n → Bool := fun k => (x >>> k.val) % 2 == 1

/-- Report §5.3.3, §9.5.1 (decision 1) — compare `evalProgram tp` with `Network.pred N n` on all
`2ⁿ` inputs (`n ≤ frontEndLimit`), in increasing order of `x`. -/
def validateFrontEnd (tp : TypedProgram) (N : Network) (n : Nat) : FrontEndCheck :=
  if tp.hasLoop then .unbounded
  else if n > frontEndLimit then .tooLarge n
  else
    let bad := (List.range (2 ^ n)).find? fun x =>
      evalProgram tp (inputBits n x) != N.pred n (inputBits n x)
    match bad with
    | some x => .mismatch n x (evalProgram tp (inputBits n x)) (N.pred n (inputBits n x))
    | none => .validated n

/-- Report §5.3.3, §9.5.1 — the front-end trust boundary of Stage 8b (still used for `n > 16`):
the certificate is about the network `net` of `Cert.lean`; the translation DSL → network
(`toNetwork`) is not verified, and `predicate_hash` binds the source it was computed from. -/
def frontEndTrust : String :=
  "DSL → network (toNetwork) unverified; predicate_hash binds the source"

/-- Report §5.3.3 (decision 1) — the declared front-end boundary after an exhaustive validation
of `2ⁿ` inputs. -/
def frontEndValidatedText (n : Nat) : String :=
  s!"DSL → network: exhaustively validated (2^{n} inputs) by the unverified evaluator; \
    not kernel-checked"

/-- Report §5.3.3, §7.2–7.4 (Stage 16b) — the declared front-end boundary of every certificate
since schema 1.8.0: the step typed term → network is proved (`toNetwork_pred`) and kernel-checked
at the instance (`net_ok`, `front_end` in `Cert.lean`); what stays unverified is named. -/
def frontEndProvedText : String :=
  "DSL typed term → network: proved (toNetwork_pred; kernel-checked net_ok and front_end in \
    Cert.lean); parser, surface checker and the typed-term printer unverified; predicate_hash \
    binds the source"

/-- Report §5.3.3 — the text of `trust_boundary.front_end` for a validation outcome (`none` when
there is no certificate to write: a mismatch or a `loop`). -/
def FrontEndCheck.trustText : FrontEndCheck → Option String
  | .validated n => some (frontEndValidatedText n)
  | .tooLarge _ => some frontEndTrust
  | .unbounded | .mismatch .. => none

/-- Report §5.3.3 — the input of a mismatch as bits `x[0] … x[n−1]`. -/
def bitString (n x : Nat) : String :=
  String.ofList ((List.range n).map fun k => if (x >>> k) % 2 == 1 then '1' else '0')

/-- Report §5.3.3 — the diagnostic of a failed validation (stage `validate`, code
`front_end_mismatch`; unreachable from `cqr certify` since Stage 16b, kept for the regression
tests). -/
def FrontEndCheck.diagnostic? (c : FrontEndCheck) (name : String) (p : Pos) :
    Option Diagnostic :=
  match c with
  | .mismatch n x e v => some (Diagnostic.at .validation .frontEndMismatch p
      s!"front-end validation of `{name}`: the DSL evaluator gives {e} and the network \
        (toNetwork) gives {v} on input x = {bitString n x} (x[0] … x[{n - 1}]); the front end \
        (parser, checker or toNetwork) is wrong on this input (report §5.3.3)")
  | .unbounded => some (Diagnostic.at .validation .unboundedLoop p
      s!"`{name}` contains `loop … while`: no finite meaning to validate (report §4.2.2)")
  | _ => none

/-- Report §5.3.3 — the truth table of a predicate as a string over `0`/`1`, character `x` being
the value on input `x` (bit `k` of `x` = input bit `k`); used by `cqr check --truth-table` and the
Python harness. -/
def truthTable (n : Nat) (f : (Fin n → Bool) → Bool) : String :=
  String.ofList ((List.range (2 ^ n)).map fun x => if f (inputBits n x) then '1' else '0')

end CQRV.Certify

end
