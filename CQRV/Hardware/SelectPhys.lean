module

public import CQRV.Hardware.PhysGrade
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# CQRV.Hardware.SelectPhys

Report §3.1.3, §5.3; PHASE2_SPEC §C.3 (Stage 26c2b, P4) — selection by the physical grade,
Physlib-free, as `Patterns/Select.lean` selects by the logical grade (§A.6):

* the candidates are a request's artifacts on one target (tree mbu, tree coherent, fewlog mbu),
  each with its uncomputation mode and its `PhysGrade` at a stated feed-forward latency;
* **admissibility**: an mbu candidate needs the target's feed-forward (§A.9 (5): on a target
  without it only coherent is admissible), and the component must be within the budget when one is
  given;
* **the preference** is one component — the two-qubit count, the depth (at the stated latency) or
  the physical bound (`PhysPref.key`);
* **`selectPhys`** returns the first minimal admissible candidate, or `none`; **`selectPhys_spec`**:
  the chosen one is admissible and minimal for the component among the admissible ones, and `none`
  exactly when no candidate is admissible.

Selection relies on each candidate's committed `Check.lean` (the reconstruction, the edges, the
channel theorem) through the hash of its `physical.json`; a `Select.lean` does not repeat it. A
budget that admits no candidate is the honest answer, not an error.
-/

@[expose] public section

namespace CQRV.Hardware

/-- A candidate: the artifact's name, whether its uncomputation is mbu (needs feed-forward), and its
physical grade at the stated latency. -/
structure PhysCand where
  name : String
  mbu : Bool
  grade : PhysGrade
  deriving Repr, DecidableEq

/-- The component `--prefer` names. -/
inductive PhysPref where
  | twoq
  | depth
  | bound
  deriving Repr, DecidableEq, Inhabited

def PhysPref.name : PhysPref → String
  | .twoq => "twoq"
  | .depth => "depth"
  | .bound => "bound"

def PhysPref.parse? : String → Option PhysPref
  | "twoq" => some .twoq
  | "depth" => some .depth
  | "bound" => some .bound
  | _ => none

/-- The component of a grade, as a rational. -/
def PhysPref.key : PhysPref → PhysGrade → Rat
  | .twoq, g => (g.twoQubit : Rat)
  | .depth, g => g.depth
  | .bound, g => g.bound

/-- Admissible on a target with feed-forward `ff`, under an optional budget on the component. -/
def admissible (ff : Bool) (budget : Option Rat) (p : PhysPref) (c : PhysCand) : Bool :=
  (!c.mbu || ff) && (match budget with | some b => decide (p.key c.grade ≤ b) | none => true)

/-- PHASE2_SPEC §C.3 (P4) — **`selectPhys`**: the first admissible candidate with the least
component; among admissible candidates with equal components the first in the list. -/
def selectPhys (ff : Bool) (budget : Option Rat) (p : PhysPref) : List PhysCand → Option PhysCand
  | [] => none
  | c :: cs =>
    match selectPhys ff budget p cs with
    | none => if admissible ff budget p c then some c else none
    | some a => if admissible ff budget p c ∧ ¬ p.key a.grade < p.key c.grade then some c else some a

/-- PHASE2_SPEC §C.3 (P4) — **`selectPhys_spec`**: a result is in the list, is admissible, and no
admissible candidate has a smaller component; the result is `none` exactly when no candidate is
admissible. -/
theorem selectPhys_spec (ff : Bool) (budget : Option Rat) (p : PhysPref) : (cs : List PhysCand) →
    (∀ x, selectPhys ff budget p cs = some x →
      x ∈ cs ∧ admissible ff budget p x = true ∧
        ∀ y ∈ cs, admissible ff budget p y = true → p.key x.grade ≤ p.key y.grade) ∧
    (selectPhys ff budget p cs = none ↔ ∀ y ∈ cs, admissible ff budget p y = false)
  | [] => by simp [selectPhys]
  | c :: cs => by
    obtain ⟨ih_some, ih_none⟩ := selectPhys_spec ff budget p cs
    simp only [selectPhys]
    split
    · rename_i hnone
      have hrest := ih_none.1 hnone
      refine ⟨?_, ?_⟩
      · intro x h
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_self .., hc, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · exact le_rfl
          · rw [hrest y hy] at hyb; cases hyb
        · simp at h
      · constructor
        · intro h y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · by_cases hc : admissible ff budget p y = true
            · simp [hc] at h
            · simpa using hc
          · exact hrest y hy
        · intro h; simp [h c (List.mem_cons_self ..)]
    · rename_i a ha
      obtain ⟨hmem, hab, hbest⟩ := ih_some a ha
      refine ⟨?_, ?_⟩
      · intro x h
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_self .., hc.1, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · exact le_rfl
          · exact le_trans (not_lt.mp hc.2) (hbest y hy hyb)
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_of_mem _ hmem, hab, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · by_cases hlt : p.key a.grade < p.key y.grade
            · exact le_of_lt hlt
            · exact absurd ⟨hyb, hlt⟩ hc
          · exact hbest y hy hyb
      · constructor
        · intro h; split at h <;> simp at h
        · intro h
          have := h a (List.mem_cons_of_mem _ hmem)
          rw [this] at hab; cases hab

/-- The CLI / JSON form of a choice. -/
def PhysCand.toJson (c : PhysCand) (L : Rat) : Lean.Json :=
  Lean.Json.mkObj [("artifact", c.name), ("uncompute", if c.mbu then "mbu" else "coherent"),
    ("phys_grade", c.grade.toJson L)]

end CQRV.Hardware
