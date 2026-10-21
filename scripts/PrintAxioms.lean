import Lean
import CQRV

/-!
# Axiom printout for `CQRV.Certify` (report §9.5.1, CLAUDE.md rule 10)

Run via `scripts/print_axioms.sh`. Prints the axioms of every theorem declared in a module
under `CQRV.Certify`, or "no theorems in CQRV.Certify" when there are none.
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
          unless n.isInternalDetail do thms := thms.push n
  if thms.isEmpty then
    logInfo "no theorems in CQRV.Certify"
  else
    for n in thms.qsort Name.lt do
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"{n}: {if axs.isEmpty then "no axioms" else ", ".intercalate (axs.toList.map toString)}"
