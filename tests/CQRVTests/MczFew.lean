module

import CQRV.DSL.Basic
import CQRV.Synthesis.Basic
meta import CQRV.DSL.Basic
meta import CQRV.Synthesis.Basic

/-!
# Tests for `CQRV.Synthesis.MczFew` (report §3.1.4 Table 3.3, §6.1.4, §8.2; Stage 12b)

These are regression values of the few-ancilla MCZ's schedule and measured grades; the
restoration proof is `CQRV.Grover.MczFew` (Stage 12c / 12d, tests in `MczFewCorrect.lean`) and the
independent semantic check `tests/diff/mcz_diff.py` (every measurement branch, n = 1..10). DECISIONS.md 2026-10-26 (Stage 12b) records the table and the citations.
-/

namespace CQRV.Tests.MczFew

open CQRV CQRV.DSL CQRV.Synthesis CQRV.Synthesis.MczFew

def groverSrc : String := include_str "../../examples/grover_pred_037.cqr"

def groverNet : Except Diagnostic Network := parse groverSrc >>= check >>= toNetwork

def gradeOf (c : Except Diagnostic Circuit) : Option Grade := (c.map grade).toOption

/-! ## KG Problem 1 schedules -/

-- KG §5.2 greedy, n = 8 (array A[0..8], A[0] = anc[0]): n − 2 = 6 operations, K = 2 left.
#guard (greedy 9 (true :: List.replicate 8 false)) ==
  ([(0, 1, 2), (2, 3, 4), (4, 5, 6), (6, 7, 8), (3, 4, 6), (1, 2, 3)],
   [false, false, true, true, true, true, true, true, true])
-- KG §5.3 doubling: timesteps 0, 1 fit n = 8; timestep 2 needs n ≥ 10. The n = 36 arrays of
-- the paper: after step i, `0^i 1^{2^i} 0…`.
#guard doubling 8 == [(0, 1, 2), (2, 4, 5), (1, 2, 3)]
#guard doubling 10 == [(0, 1, 2), (2, 4, 5), (1, 2, 3), (5, 7, 8), (4, 9, 10), (3, 5, 6), (2, 3, 4)]
#guard (doubling 36).foldl applyOp (true :: List.replicate 36 false) ==
  List.replicate 5 false ++ List.replicate 32 true  -- five timesteps fit n = 36: the paper's i = 5
-- Every operation is valid for Problem 1 (t < x < y, A[t] = 1, A[x] = A[y] = 0): `MczFew.valid`,
-- moved to `CQRV.Synthesis.MczFew` in Stage 13a and proved for every n in `CQRV.Grover.MczFewAll`.
#guard (List.range 40).all fun n => valid (true :: List.replicate n false) (doubling n)
-- Plans: D₈ ladder = 1 AND + 5 rtof, CZ(anc[0], x[0]); log = 2 ANDs + 4 rtof, CZ(anc[1], x[3]).
#guard ((plan 8 .ladder).1.map (·.2.2.2), (plan 8 .ladder).2) ==
  ([true, false, false, false, false, false], [.anc 0, .data 0])
#guard ((plan 8 .logDepth).1.map (·.2.2.2), (plan 8 .logDepth).2) ==
  ([true, false, false, false, false, true], [.anc 1, .data 3])
-- Two qubits or fewer are left for every n ≤ 40, both variants (`mczFew` never fails for n ≥ 1).
#guard (List.range 40).all fun k => [MczVariant.ladder, .logDepth].all fun v =>
  (mczFew (k + 1) v).toOption.isSome
#guard (mczFew 0 .ladder).toOption.isNone
-- The relative-phase Toffoli is self-inverse as a gate list (reverse, then T ↔ T†).
#guard (rtof (.data 0) (.data 1) (.data 2)).reverse.map (fun
  | .t q => .tdg q | .tdg q => .t q | g => g) == rtof (.data 0) (.data 1) (.data 2)

/-! ## Measured grades (scheduler of decision 4, unchanged) -/

-- D₈. Report v2 (Table 3.3, Table 3): (10, 16, 28, 2). Measured: ladder (9, 93, 44, 1),
-- log (10, 60, 40, 2); V1 tree (12a) (15, 41, 28, 7).
#guard gradeOf (diffusionFew 8 .ladder) == some ⟨9, 93, 44, 1⟩
#guard gradeOf (diffusionFew 8 .logDepth) == some ⟨10, 60, 40, 2⟩
-- T-count: ladder 8n − 20 (1 AND, n − 3 rtof pairs), log 8n − 24 for n ≥ 6 (2 ANDs, n − 4
-- pairs); a ≤ 2 throughout; w = n + a.
#guard (List.range 10).all fun k => let n := k + 3
  (gradeOf (diffusionFew n .ladder)).map (fun g => (g.t, g.a, g.w)) == some (8 * n - 20, 1, n + 1)
#guard (List.range 7).all fun k => let n := k + 6
  (gradeOf (diffusionFew n .logDepth)).map (fun g => (g.t, g.a, g.w)) == some (8 * n - 24, 2, n + 2)
#guard (List.range 3).all fun k => let n := k + 3
  gradeOf (diffusionFew n .logDepth) == gradeOf (diffusionFew n .ladder)
#guard (List.range 12).all fun k => [MczVariant.ladder, .logDepth].all fun v =>
  ((diffusionFew (k + 1) v).map (·.validate.isOk)).toOption == some true
-- Grover slice (grover_pred_037; the oracle's a = 2 dominates the iteration).
#guard gradeOf (groverNet >>= (groverIterationFew · 8 .ladder)) == some ⟨10, 120, 52, 2⟩
#guard gradeOf (groverNet >>= (groverIterationFew · 8 .logDepth)) == some ⟨10, 87, 48, 2⟩
#guard gradeOf (groverNet >>= (groverCircuitFew · 8 2 .ladder)) == some ⟨10, 238, 104, 2⟩
#guard gradeOf (groverNet >>= (groverCircuitFew · 8 2 .logDepth)) == some ⟨10, 172, 96, 2⟩
#guard ((groverNet >>= (groverCircuitFew · 8 2 .logDepth)).map (·.validate.isOk)).toOption ==
  some true
-- The proved default is unchanged (12a): certify still uses the tree.
#guard gradeOf (groverNet >>= (groverCircuit · 8 2)) == some ⟨15, 134, 72, 7⟩
#guard MczVariant.ladder.status == "classical step checked at n = 8, restoration not certified"
#guard MczVariant.logDepth.status ==
  "restoration proved for every n (Stage 13a); certified via `cqr certify --shape few:log`"

end CQRV.Tests.MczFew
