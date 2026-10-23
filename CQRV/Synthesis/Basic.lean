module

public import CQRV.Synthesis.Network
public import CQRV.Synthesis.TempAnd
public import CQRV.Synthesis.Oracle
public import CQRV.Synthesis.Bennett

/-!
# CQRV.Synthesis

Report §6.1 — Boolean network → oracle circuit, Bennett schedule, grade computation:

```
toNetwork        : TypedProgram → Except Diagnostic Network   -- decision 1
synthesizeOracle : Network → Except Diagnostic Circuit         -- decision 2, straight-line
pebbleChain      : Nat → Nat → Except String (List Move)       -- decision 3, AND chains
grade            : Circuit → Grade                             -- decision 4 scheduler
```
-/
