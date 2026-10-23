import Lake
open Lake DSL

/-! CQRV — Certified Quantum Realization (report §9.1, §9.5.3).
One Lake package with one top-level module tree per chapter-level component
(see docs/DECISIONS.md, 2026-10-21). Pins: `lean-toolchain`, `lake-manifest.json`
(CLAUDE.md rule 4 — never bump ad hoc). -/

package cqrv where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

-- Physlib (includes Lean-QuantumInfo since March 2026), pinned to the commit tested against
-- the Mathlib pin above (docs/DECISIONS.md, 2026-10-21). It requires the same Mathlib commit.
require Physlib from git
  "https://github.com/leanprover-community/physlib.git" @ "96a6bc5e3c50a2856c64a6c9951c0a1c23790b58"

@[default_target]
lean_lib CQRV

@[default_target]
lean_lib CQRVTests where
  srcDir := "tests"
  roots := #[`CQRVTests, `PhyslibSmoke]
  globs := #[.one `CQRVTests, .one `PhyslibSmoke, .submodules `CQRVTests]

@[default_target]
lean_exe cqr where
  root := `Apps.cqr.Main
