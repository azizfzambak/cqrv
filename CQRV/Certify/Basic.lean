module

public import CQRV.Certify.SHA3
public import CQRV.Certify.Certificate

/-!
# CQRV.Certify

Report §5, §8.4 — parametric lemmas, specialization, certificate record, sorry audit.

Stage 8a: `SHA3` (SHA3-256 in Lean, §9.5.3) and `Certificate` (the record, its JSON envelope
schema v1.0.0, the exact δ, the hashes; §8.4.2, §8.4.4, §9.5.3). Kernel checking and the axiom
audit of generated certificates are Stage 8b.
-/
