module

import CQRV.DSL.Basic
import CQRV.Patterns.Select
meta import CQRV.DSL.Basic
meta import CQRV.Patterns.Select

/-!
# Tests for `CQRV.Patterns.Select` (Stage 21a4; PHASE2_SPEC §A.6 (8), (8′); report §3.1.2)

The key of a grade for each preference; `select` on the three `grover_pred_037` grades under a
generous budget and under the committed budget ⟨12, 200, 100, 8⟩; a budget that fits nothing; equal
grades (the first in the list); the axioms of `select_spec`; `Candidate.build` against
`groverInstance` on a four-input program, for each candidate.
-/

namespace CQRV.Tests.Select

open CQRV CQRV.DSL CQRV.Patterns CQRV.Synthesis CQRV.Certify

/-! ## The key and the order -/

def gTree : Grade := ⟨15, 134, 72, 7⟩
def gCoh : Grade := ⟨15, 200, 144, 7⟩
def gFew : Grade := ⟨10, 172, 96, 2⟩

#guard Grade.key .width gTree == [15, 134, 72, 7]
#guard Grade.key .depth gTree == [134, 15, 72, 7]
#guard Grade.key .t gTree == [72, 15, 134, 7]
#guard Grade.key .anc gTree == [7, 15, 134, 72]
#guard [Pref.width, .depth, .t, .anc].map Pref.order == ["wdta", "dwta", "twda", "awdt"]
#guard lexLt [1, 2, 3, 4] [1, 2, 4, 0] && !lexLt [1, 2, 3, 4] [1, 2, 3, 4] && !lexLt [2, 0, 0, 0] [1, 9, 9, 9]
#guard ([Pref.width, .depth, .t, .anc].map fun p => Pref.parse? p.name) == [some .width, some .depth, some .t, some .anc]
#guard Pref.parse? "size" == none

/-! ## `select` on the three grades of `grover_pred_037` (PHASE2_SPEC §A.6 (8′)) -/

/-- The candidates with their grades, in list order. -/
def pool : List (Candidate × Grade) := [(.treeMbu, gTree), (.treeCoherent, gCoh), (.fewLogMbu, gFew)]

def generous : Grade := ⟨20, 300, 200, 8⟩

#guard (select generous .depth pool).map (·.1) == some .treeMbu
#guard (select generous .width pool).map (·.1) == some .fewLogMbu
#guard (select generous .t pool).map (·.1) == some .treeMbu
#guard (select generous .anc pool).map (·.1) == some .fewLogMbu
-- the committed budget: depth alone would pick treeMbu, but its w = 15 exceeds 12
#guard (select ⟨12, 200, 100, 8⟩ .depth pool).map (·.1) == some .fewLogMbu
-- nothing fits
#guard (select ⟨9, 300, 300, 9⟩ .depth pool).isNone
-- equal grades: the first in the list
#guard (select generous .depth [(Candidate.treeCoherent, gTree), (.treeMbu, gTree)]).map (·.1) ==
  some .treeCoherent
-- the dominated candidate is never selected
#guard [Pref.width, .depth, .t, .anc].all fun p => (select generous p pool).map (·.1) != some .treeCoherent
#guard candidates.map (·.shape) == [.tree, .tree, .fewLog]
#guard candidates.map (·.mode) == [.mbu, .coherent, .mbu]

-- `select_spec` is sorry-free (the standard axioms at most).
/-- info: 'CQRV.Patterns.select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms select_spec

/-! ## `Candidate.build` agrees with `groverInstance` (a four-input program, each candidate) -/

def src4 : String :=
  "fn pred4(x: Vec Bool 4) -> Bool {\n  let b0 = idx(x, 0) in\n  let b3 = idx(x, 3) in\n  b0 and b3\n}\n"

/-- The circuit `groverInstance` builds at the candidate's shape and mode (r = 1). -/
def viaInstance (c : Candidate) : Option Circuit :=
  match parse src4 >>= check with
  | .ok tp =>
    match groverInstance tp (extract tp) (some 1) c.shape c.mode with
    | .ok gi => some gi.circuit
    | .error _ => none
  | .error _ => none

/-- The circuit of `Candidate.build` on the program's network (r = 1). -/
def viaBuild (c : Candidate) : Option Circuit :=
  match parse src4 >>= check with
  | .ok tp =>
    match toNetwork tp with
    | .ok N => (c.build N 4 1).toOption
    | .error _ => none
  | .error _ => none

#guard candidates.all fun c => (viaInstance c).isSome && viaInstance c == viaBuild c
#guard (candidates.map fun c => (viaBuild c).map (·.grade)).all (·.isSome)

end CQRV.Tests.Select
