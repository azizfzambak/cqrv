module

public import CQRV.Circuit.IR
public import CQRV.Circuit.Schedule
public import CQRV.Circuit.Semantics
public import CQRV.Circuit.Restoration

/-!
# CQRV.Circuit

Report §6, §9.1.1 — gate-level IR (`IR`), the depth scheduler (`Schedule`), the denotational
semantics into Physlib channels (`Semantics`: unitary fragment, Kraus channel, `Circuit.WF`)
and ancilla restoration (`Restoration`: TempLogicalAND, MBU, `AncRestore`, Lemma 6.3.2).
-/
