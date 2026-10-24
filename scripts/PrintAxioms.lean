import Lean
import CQRV

/-!
# Axiom audit of `CQRV.Certify` (report §9.5.1, §9.5.3, CLAUDE.md rule 10)

Run via `scripts/print_axioms.sh`. Prints the axioms of every **named** theorem declared in a
module under `CQRV.Certify` — a theorem with a source range; the auto-generated `inj`, `injEq`,
`sizeOf_spec`, `eq_*` lemmas of structures and definitions have none and are skipped (Stage 8b
review note, DECISIONS.md 2026-10-25) — and audits each list with `CQRV.Certify.auditAxioms`
(no `sorryAx`; only `propext`, `Classical.choice`, `Quot.sound` or the trust-boundary table).
Blocking since Stage 8b: an audit failure, or no named theorem at all, is an error, so
`lake env lean` exits 1.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    if (`CQRV.Certify).isPrefixOf mod then
      for n in env.header.moduleData[i]!.constNames do
        if let some (.thmInfo _) := env.find? n then
          if !n.isInternalDetail && (← liftCoreM (findDeclarationRanges? n)).isSome then
            thms := thms.push n
  if thms.isEmpty then
    logError "no named theorems in CQRV.Certify"
    return
  let mut failed : Array Name := #[]
  for n in thms.qsort Name.lt do
    let axs := (← liftCoreM (collectAxioms n)).toList.map toString
    let verdict := match CQRV.Certify.auditAxioms axs with
      | .pass => "ok"
      | .fail bad => s!"FAILED ({", ".intercalate bad})"
    if verdict != "ok" then failed := failed.push n
    logInfo m!"{n}: {if axs.isEmpty then "no axioms" else ", ".intercalate axs} [{verdict}]"
  if failed.isEmpty then
    logInfo m!"axiom audit: {thms.size} named theorems in CQRV.Certify pass"
  else
    logError m!"axiom audit FAILED for {failed.size} theorem(s): {failed.toList}"
