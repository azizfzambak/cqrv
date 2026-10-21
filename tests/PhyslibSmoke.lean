import QuantumInfo.Channels.CPTP
import QuantumInfo.States.Mixed.MState

/-!
# Physlib smoke test

Report §9.1.1, Table 9.5 (dependency-drift row). Compiles on every CI build (via
`CQRVTests`) to confirm that the pinned Physlib still builds against the pinned Mathlib and
exposes the channel/state API Stage 2 builds on (docs/DECISIONS.md, 2026-10-21).
-/

example : Type := MState (Fin 2)

example : Type := CPTPMap (Fin 2) (Fin 4)

noncomputable example (Λ₁ : CPTPMap (Fin 2) (Fin 4)) (Λ₂ : CPTPMap (Fin 4) (Fin 2)) :
    CPTPMap (Fin 2) (Fin 2) :=
  CPTPMap.compose Λ₂ Λ₁
