module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic

/-!
# Tests for `CQRV.Synthesis.Diffusion` (report §8.2, §3.1.4 Table 3.3, §6.1.4 Table 3, §3.2.4)

The measured grades of the diffusion (V1, V2), one Grover iteration and the full Grover
circuit of `grover_pred_037` become regression values (Stage 5b task 4). The report's claims
are recorded next to them; DECISIONS.md (2026-10-24, Stage 5b) records the deviations.
Semantic correctness is checked by `tests/diff/grover_diff.py` (every measurement branch).
-/

namespace CQRV.Tests.Diffusion

open CQRV CQRV.DSL CQRV.Synthesis

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"

/-- The network of grover_pred_037. -/
def groverNet : Except Diagnostic Network := parse groverSrc >>= check >>= toNetwork

/-- The grade of a synthesized circuit, if it was synthesized. -/
def gradeOf (c : Except Diagnostic Circuit) : Option Grade := (c.map grade).toOption

/-! ## `P_all` and the MCZ -/

-- `allNet n` is the AND chain over x[0..n): `n − 1` ANDs, true only on all-ones.
#guard (allNet 8).andCount == 7
#guard (List.range 256).all fun k => (allNet 8).eval (fun i => (k >>> i) % 2 == 1) == [k == 255]
#guard (allNet 1).eval (fun _ => true) == [true] && (allNet 1).eval (fun _ => false) == [false]
#guard Bennett.chainOf (allNet 8) == some (List.range 8)
-- The V1 MCZ is the straight-line oracle of `P_all` (Lemma 6.3.2 applies: xor-free).
#guard ((diffusion 8 none).map (·.gates)).toOption == ((synthesizeOracle (allNet 8)).map fun o =>
  Diffusion.onAll .h 8 ++ Diffusion.onAll .x 8 ++ o.gates ++
  Diffusion.onAll .x 8 ++ Diffusion.onAll .h 8).toOption
#guard ((diffusion 8 none).map (·.validate.isOk)).toOption == some true
#guard ((diffusion 8 (some 3)).map (·.validate.isOk)).toOption == some true
#guard match diffusion 0 none with
  | .error d => d.code == .unsupportedNetwork
  | .ok _ => false

/-! ## Measured grades (Stage 5b table) -/

-- D₈, V1. Report (Table 3.3, Table 3): (10, 16, 28, 2 reused). Measured: t = 28 = 4(n − 1)
-- holds; a = n − 1 = 7 (one ancilla per AND of the chain), w = 8 + 7, d = 89.
#guard gradeOf (diffusion 8 none) == some ⟨15, 89, 28, 7⟩
-- D₈, V2 (Bennett, a_max = 3, the smallest feasible budget for 7 nodes).
#guard gradeOf (diffusion 8 (some 3)) == some ⟨11, 157, 52, 3⟩
#guard (diffusion 8 (some 2)).toOption.isNone  -- infeasible: 2 pebbles reach node 3
-- V1 over n: (2n − 1, 12n − 7, 4(n − 1), n − 1) for 2 ≤ n ≤ 10 (harness range).
#guard (List.range 9).all fun k => let n := k + 2
  gradeOf (diffusion n none) == some ⟨2 * n - 1, 12 * n - 7, 4 * (n - 1), n - 1⟩
#guard gradeOf (diffusion 1 none) == some ⟨1, 5, 0, 0⟩

-- One iteration (oracle ⊕ D₈, V1). Report (Table 3): (10, 37, 36, 2). Measured (15, 116, 36, 7),
-- equal to the ⊕ of the two measured parts (no layer overlap across the boundary).
#guard gradeOf (groverNet >>= (groverIteration · 8)) == some ⟨15, 116, 36, 7⟩
#guard ((groverNet >>= synthesizeOracle).map grade).toOption.bind (fun o =>
  (gradeOf (diffusion 8 none)).map (o + ·)) == some ⟨15, 116, 36, 7⟩

-- Full Grover, r⋆ = 2 (V1). Report (Table 3.3, Chapter 8): (10, 74, 72, 2). Measured
-- (15, 230, 72, 7): t = 72 holds; d = 230 < 1 + 2 · 116 = 233 (the scheduler overlaps layers
-- across the H^{⊗n} / iteration boundaries), so the whole is not the ⊕ of its parts in d.
#guard gradeOf (groverNet >>= (groverCircuit · 8 2)) == some ⟨15, 230, 72, 7⟩
#guard (⟨8, 1, 0, 0⟩ + (2 • (⟨15, 116, 36, 7⟩ : Grade))) == (⟨15, 233, 72, 7⟩ : Grade)
#guard ((groverNet >>= (groverCircuit · 8 2)).map (·.validate.isOk)).toOption == some true
#guard ((groverNet >>= (groverCircuit · 8 2)).map (·.nBits)).toOption == some 18

-- r⋆ = ⌊π / (4θ)⌋, sin²θ = M / 2ⁿ: 2 for M = 32, N = 256 (§8); 12 for M = 1, N = 256.
#guard rStar 8 32 == some 2
#guard rStar 8 1 == some 12
#guard rStar 8 0 == none && rStar 8 257 == none

end CQRV.Tests.Diffusion
