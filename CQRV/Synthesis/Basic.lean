module

public import CQRV.Synthesis.Network
public import CQRV.Synthesis.NetworkCorrect
public import CQRV.Synthesis.TempAnd
public import CQRV.Synthesis.Oracle
public import CQRV.Synthesis.Bennett
public import CQRV.Synthesis.Diffusion
public import CQRV.Synthesis.MczFew
public import CQRV.Synthesis.QFT

/-!
# CQRV.Synthesis

Report §6.1 — Boolean network → oracle circuit, Bennett schedule, grade computation:

```
toNetwork        : TypedProgram → Except Diagnostic Network   -- decision 1
synthesizeOracle : Network → Except Diagnostic Circuit         -- decision 2, straight-line
pebbleChain      : Nat → Nat → Except String (List Move)       -- decision 3, AND chains
grade            : Circuit → Grade                             -- decision 4 scheduler
diffusion        : Nat → Option Nat → Except Diagnostic Circuit -- §8.2, Stage 5b
groverCircuit    : Network → Nat → Nat → … → Except Diagnostic Circuit -- §3.2.4, Stage 5b
mczFew           : Nat → MczVariant → Except Diagnostic Circuit   -- §6.1.4, Stage 12b; status per variant (12d)
```
-/
