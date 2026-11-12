module

public import CQRV.Certify.SHA3
public import CQRV.Certify.Certificate
public import CQRV.Certify.Generate
public import CQRV.Certify.Audit
public import CQRV.Certify.FrontEnd
public import CQRV.Certify.RunReport
public import CQRV.Certify.Profile
public import CQRV.Certify.Count
public import CQRV.Certify.CountCert

/-!
# CQRV.Certify

Report §5, §8.4 — parametric lemmas, specialization, certificate record, sorry audit.

Stage 8a: `SHA3` (SHA3-256 in Lean, §9.5.3) and `Certificate` (the record, its JSON envelope
schema, the exact δ, the hashes; §8.4.2, §8.4.4, §9.5.3). Stage 8b: `Generate` (the text of a
specialized certificate `Cert.lean`, §5.1.3, §8.4.1) and `Audit` (kernel check by `lake env lean`,
`#print axioms`, `auditAxioms`, §9.5.1, §9.5.3). `CQRV.Certify.Specialize` (the lemmas a
certificate instantiates) imports the Grover proof and Physlib; it is imported by `CQRV`, not by
this module, so that the CLI does not link Physlib. Stage 9b: `FrontEnd` (exhaustive validation
of the front end, `evalProgram` vs `Network.pred` on all `2ⁿ` inputs, §5.3.3) and `RunReport`
(one row per pipeline stage in the shape of Table 8.5.2, §8.5.2). Stage 11b: `Profile` (reading
a declared hardware profile for `cqr certify --profile`, §3.3.2–3.3.3). Stage 14a: `Count`
(`Network.countSat` and `Network.countSat_eq_card`: the solution count decided by the kernel for
`n ≤ --count-limit`, §8.2). Stage 20b3: `CountCert` (the counting certificate's request,
renderer, JSON record and run report, PHASE2_SPEC.md §A.4 "Amendments before Stage 20b3"; called by
`scripts/CertifyTool.lean count-certify`, wired to `cqr certify --problem count` in Stage 21).
-/
