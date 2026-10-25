module

public import CQRV.DSL.Syntax
public import CQRV.DSL.Diagnostic
public import CQRV.DSL.Parser
public import CQRV.DSL.Check
public import CQRV.DSL.Signature
public import CQRV.DSL.Extract
public import CQRV.DSL.Eval

/-!
# CQRV.DSL

Report §7 — syntax, parser, surface typing, extractor ℰ. Pipeline (report §4.2.2, §7.2.1):

```
parse   : String       → Except Diagnostic Program       -- syntax errors
check   : Program      → Except Diagnostic TypedProgram  -- surface checker
extract : TypedProgram → SigmaIn                         -- ℰ, total
evalProgram : TypedProgram → (Reg n → Bool)              -- reference evaluator (Stage 9b)
```
The Cl♭ judgment itself is decided on the extracted signature by the matcher (Stage 4).
-/
