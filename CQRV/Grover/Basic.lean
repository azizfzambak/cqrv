module

public import CQRV.Grover.Reflections
public import CQRV.Grover.Restore
public import CQRV.Grover.Lemma
public import CQRV.Grover.Instance
public import CQRV.Grover.MczFew
public import CQRV.Grover.MczFewAll
public import CQRV.Grover.QPEBound
public import CQRV.Grover.Counting
public import CQRV.Grover.AmplitudeEstimation

/-!
# CQRV.Grover

Report §8 — the vertical slice: the Grover parametric lemma (Stage 7a). `Reflections`: `H^{⊗n}`,
`|s⟩`, the oracle and diffusion reflections (§8.2, §8.3.2); `Restore`: `OracleCert`,
`DiffusionCert` and the restoration conjunct `grover_ancRestore` (§5.2.4, §8.3.3); `Lemma`:
`GroverParams`, the search spec, the basis POVM, the Grover channel and the statements of
Figure 8.1 (§8.3.4); `Instance`: `grover_pred_037` (§8.4.1); `MczFew`: the restoration proof of
the few-ancilla MCZ, candidate B, for n = 8 (§6.2, §8.2; Stage 12c); `MczFewAll`: the same for
every n, Khattar–Gidney Theorem 5.1 (Stage 13a).
-/
