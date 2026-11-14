module

public import CQRV.Certify.Basic

/-!
# CQRV.Patterns.Select

PHASE2_SPEC.md §A.6 amendment (8) and its refinement (8′) (Stage 21a4), report §3.1.2 (the budget
order), §6.1.3 — **certified selection under a budget**, Physlib-free (the `cqr` closure stays Lean
core + Mathlib):

* the preference `Pref` (`--prefer width|depth|t|anc`), the key of a grade (the preferred
  component, then the others in the order (w, d, t, a)) and the strict lexicographic order
  `lexLt` on keys (the list order of Mathlib's `LinearOrder (List ℕ)`, decided);
* the three named candidates `treeMbu`, `treeCoherent`, `fewLogMbu` in this order, each with its
  shape, its mode and its builder — exactly the builder whose output the `emitted_ok` theorem of
  the corresponding committed Grover certificate checks;
* `select`: the first admissible element with the least key, proved once for any list
  (`select_spec`: the result is in the list, is admissible, and no admissible element lies
  strictly below it; it is `none` exactly when nothing is admissible);
* the selection record `SelectionInfo` with its JSON (`selection` of schema 1.11.0), its report
  row and its status line, and the renderer of the selection block of `Cert.lean` (G2): `budget`,
  `cand_grade_c` for every candidate, `chosen_fits`, and `selected` quantified over the builders'
  outputs.
-/

@[expose] public section

namespace CQRV.Patterns

open CQRV.Synthesis CQRV.Certify Lean

/-! ## The preference and the key -/

/-- PHASE2_SPEC §A.6 (8′) — the component `--prefer` names first. -/
inductive Pref where
  | width
  | depth
  | t
  | anc
  deriving Repr, DecidableEq, Inhabited

/-- The CLI / JSON word of a preference. -/
def Pref.name : Pref → String
  | .width => "width"
  | .depth => "depth"
  | .t => "t"
  | .anc => "anc"

/-- Parse a `--prefer` value. -/
def Pref.parse? : String → Option Pref
  | "width" => some .width
  | "depth" => some .depth
  | "t" => some .t
  | "anc" => some .anc
  | _ => none

/-- The four letters in key order (`order` of the JSON). -/
def Pref.order : Pref → String
  | .width => "wdta"
  | .depth => "dwta"
  | .t => "twda"
  | .anc => "awdt"

/-- The Lean literal of a preference, as `Cert.lean` writes it. -/
def Pref.lit (p : Pref) : String := s!"Patterns.Pref.{p.name}"

/-- PHASE2_SPEC §A.6 (8′) — the key of a grade: the preferred component, then the others in the
order (w, d, t, a). -/
def Grade.key (p : Pref) (g : Grade) : List ℕ :=
  match p with
  | .width => [g.w, g.d, g.t, g.a]
  | .depth => [g.d, g.w, g.t, g.a]
  | .t => [g.t, g.w, g.d, g.a]
  | .anc => [g.a, g.w, g.d, g.t]

/-- PHASE2_SPEC §A.6 (8′) — the strict lexicographic order on keys: the list order of
`LinearOrder (List ℕ)` (Mathlib), decided. -/
def lexLt (x y : List ℕ) : Bool := decide (x < y)

theorem lexLt_iff {x y : List ℕ} : lexLt x y = true ↔ x < y := decide_eq_true_iff

theorem lexLt_self (x : List ℕ) : lexLt x x = false := by simp [lexLt]

/-! ## The candidates -/

/-- PHASE2_SPEC §A.6 (8′) — the three certified pairs, in the order that breaks ties. -/
inductive Candidate where
  | treeMbu
  | treeCoherent
  | fewLogMbu
  deriving Repr, DecidableEq, Inhabited

/-- The candidate space of Stage 21, in order. -/
def candidates : List Candidate := [.treeMbu, .treeCoherent, .fewLogMbu]

theorem mem_candidates (c : Candidate) : c ∈ candidates := by cases c <;> simp [candidates]

/-- The name of a candidate (the suffix of its `cand_grade_` theorem). -/
def Candidate.name : Candidate → String
  | .treeMbu => "treeMbu"
  | .treeCoherent => "treeCoherent"
  | .fewLogMbu => "fewLogMbu"

/-- The Lean literal of a candidate, as `Cert.lean` writes it. -/
def Candidate.lit (c : Candidate) : String := s!"Patterns.Candidate.{c.name}"

/-- The diffusion of a candidate (`--shape`). -/
def Candidate.shape : Candidate → CertDiffusion
  | .fewLogMbu => .fewLog
  | _ => .tree

/-- The uncomputation mode of a candidate (`--uncompute`). -/
def Candidate.mode : Candidate → UncomputeMode
  | .treeCoherent => .coherent
  | _ => .mbu

/-- PHASE2_SPEC §A.6 (8′) — the builder of a candidate: the function whose output the `emitted_ok`
theorem of the corresponding committed Grover certificate checks. -/
def Candidate.build : Candidate → Network → ℕ → ℕ → Except DSL.Diagnostic Circuit
  | .treeMbu, N, n, r => groverCircuit N n r
  | .treeCoherent, N, n, r => groverCircuit N n r none .tree .coherent
  | .fewLogMbu, N, n, r => groverCircuitFew N n r .logDepth

/-! ## The selection function and its specification -/

/-- PHASE2_SPEC §A.6 (8), (8′) — the first admissible element with the least key: an element is
admissible when its grade is `≤ b` in the component-wise order of §3.1.2; among admissible
elements with equal keys the first in the list is chosen. -/
def select {α : Type} (b : Grade) (p : Pref) : List (α × Grade) → Option (α × Grade)
  | [] => none
  | c :: cs =>
    match select b p cs with
    | none => if c.2 ≤ b then some c else none
    | some a => if c.2 ≤ b ∧ ¬ lexLt (Grade.key p a.2) (Grade.key p c.2) then some c else some a

/-- PHASE2_SPEC §A.6 (8′) — the specification of `select`, for any list: a result is in the list,
is admissible, and no admissible element of the list lies strictly below it in the key order; the
result is `none` exactly when no element is admissible. -/
theorem select_spec {α : Type} (b : Grade) (p : Pref) : (cs : List (α × Grade)) →
    (∀ x, select b p cs = some x →
      x ∈ cs ∧ x.2 ≤ b ∧ ∀ y ∈ cs, y.2 ≤ b → ¬ lexLt (Grade.key p y.2) (Grade.key p x.2)) ∧
    (select b p cs = none ↔ ∀ y ∈ cs, ¬ y.2 ≤ b)
  | [] => by simp [select]
  | c :: cs => by
    obtain ⟨ih_some, ih_none⟩ := select_spec b p cs
    simp only [select]
    split
    · rename_i hnone
      have hrest := ih_none.1 hnone
      refine ⟨?_, ?_⟩
      · intro x h
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_self, hc, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · simp [lexLt_self]
          · exact absurd hyb (hrest y hy)
        · simp at h
      · constructor
        · intro h y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · intro hc; simp [hc] at h
          · exact hrest y hy
        · intro h; simp [h c List.mem_cons_self]
    · rename_i a ha
      obtain ⟨hmem, hab, hbest⟩ := ih_some a ha
      refine ⟨?_, ?_⟩
      · intro x h
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_self, hc.1, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · simp [lexLt_self]
          · intro hlt
            have h1 := hbest y hy hyb
            have h2 := hc.2
            simp only [lexLt, decide_eq_true_eq] at hlt h1 h2
            exact h1 (lt_of_lt_of_le hlt (not_lt.1 h2))
        · rename_i hc
          simp only [Option.some.injEq] at h; subst h
          refine ⟨List.mem_cons_of_mem _ hmem, hab, ?_⟩
          intro y hy hyb
          rcases List.mem_cons.1 hy with rfl | hy
          · intro hlt
            simp only [lexLt, decide_eq_true_eq, not_and, not_not] at hlt hc
            exact lt_asymm hlt (hc hyb)
          · exact hbest y hy hyb
      · constructor
        · intro h; split at h <;> simp at h
        · intro h; exact absurd hab (h a (List.mem_cons_of_mem _ hmem))

/-! ## The selection record (JSON, report, status line) -/

/-- One candidate's result: its grade, or `none` when the builder failed at the instance. -/
structure CandidateResult where
  cand : Candidate
  grade : Option Grade
  deriving Repr, Inhabited

/-- Admissible: built, and the grade fits the budget. -/
def CandidateResult.admissible (b : Grade) (c : CandidateResult) : Bool :=
  match c.grade with
  | some g => decide (g ≤ b)
  | none => false

/-- PHASE2_SPEC §A.6 (8′) — what `cqr certify --budget … --prefer …` selected: the budget, the
preference, every candidate's result in list order, and the chosen candidate. -/
structure SelectionInfo where
  budget : Grade
  pref : Pref
  results : List CandidateResult
  chosen : Candidate
  deriving Repr

/-- The number of admissible candidates. -/
def SelectionInfo.admissibleCount (s : SelectionInfo) : Nat :=
  (s.results.filter (·.admissible s.budget)).length

/-- `(w, d, t, a)` of a grade. -/
def gradeTuple (g : Grade) : String := s!"({g.w}, {g.d}, {g.t}, {g.a})"

/-- The result of the chosen candidate. -/
def SelectionInfo.chosenResult (s : SelectionInfo) : Option CandidateResult :=
  s.results.find? (·.cand == s.chosen)

/-- The extra line of `cqr certify` after the status line (G3). -/
def SelectionInfo.statusLine (s : SelectionInfo) : String :=
  s!"selection: {s.chosen.shape.name} + {s.chosen.mode} (prefer {s.pref.name}; budget \
    {gradeTuple s.budget}; {s.admissibleCount} of {s.results.length} candidates admissible)"

/-- One candidate as text: `treeMbu (tree + mbu): grade (…), admissible`. -/
def CandidateResult.text (b : Grade) (c : CandidateResult) : String :=
  s!"{c.cand.name} ({c.cand.shape.name} + {c.cand.mode}): " ++
    (match c.grade with
      | some g => s!"grade {gradeTuple g}, {if c.admissible b then "admissible" else "not admissible"}"
      | none => "the builder failed, not admissible")

/-- The grade JSON `{w, d, t, a}`. -/
def gradeJsonOf (g : Grade) : Json :=
  Json.mkObj [("w", g.w), ("d", g.d), ("t", g.t), ("a", g.a)]

/-- PHASE2_SPEC §A.6 (8′) — the `selection` object of schema 1.11.0; `theoremName` is the fully
qualified name of `selected`. -/
def SelectionInfo.toJson (s : SelectionInfo) (theoremName : String) : Json :=
  Json.mkObj
    [("budget", gradeJsonOf s.budget), ("prefer", Json.str s.pref.name),
     ("order", Json.str s.pref.order),
     ("candidates", Json.arr (s.results.map fun c => Json.mkObj
        [("shape", Json.str c.cand.shape.name), ("uncompute", Json.str c.cand.mode.toString),
         ("grade", match c.grade with | some g => gradeJsonOf g | none => Json.null),
         ("admissible", Json.bool (c.admissible s.budget))]).toArray),
     ("selected", Json.mkObj [("shape", Json.str s.chosen.shape.name),
       ("uncompute", Json.str s.chosen.mode.toString)]),
     ("theorem", Json.str theoremName)]

/-- The certificate envelope of a selection run: the ordinary JSON with `schema_version "1.11.0"`
and the `selection` object (the keys of a `Json` object are sorted on output). -/
def SelectionInfo.addTo (s : SelectionInfo) (j : Json) (theoremName : String) : Json :=
  (j.setObjVal! "schema_version" "1.11.0").setObjVal! "selection" (s.toJson theoremName)

/-- The report row of the selection (after the Table 8.5.2 rows). -/
def SelectionInfo.reportRow (s : SelectionInfo) : ReportRow :=
  { stage := "4b. Certified selection",
    input := s!"--budget {gradeTuple s.budget} --prefer {s.pref.name} (key order {s.pref.order}); \
      candidates {", ".intercalate (s.results.map (·.cand.name))}",
    output := s!"selected {s.chosen.name} ({s.chosen.shape.name} + {s.chosen.mode}): the ordinary \
      certificate of that candidate, plus budget, cand_grade_*, chosen_fits, selected",
    verification := .kernelChecked,
    resources := "; ".intercalate (s.results.map (·.text s.budget)),
    note := s!"PHASE2_SPEC §A.6 (8), (8′): every candidate's grade by `decide +kernel` on its \
      builder (the chosen one from emitted_ok and grade_eq); `chosen_fits` and `selected` — no \
      candidate whose builder succeeds and whose grade fits the budget has a key strictly below \
      the chosen one — kernel-checked in Cert.lean; the selection function the CLI ran is proved \
      once in the library (`select_spec`); {s.admissibleCount} of {s.results.length} candidates \
      admissible" }

/-- The report header line of the selection. -/
def SelectionInfo.headerLine (s : SelectionInfo) : String :=
  s!"selection: budget {gradeTuple s.budget}, prefer {s.pref.name} → {s.chosen.name} \
    ({s.chosen.shape.name} + {s.chosen.mode}); {s.admissibleCount} of {s.results.length} \
    candidates admissible"

/-! ## The selection block of `Cert.lean` (G2) -/

/-- The `cand_grade_c` (or `cand_fail_c`) theorem of one candidate: the chosen one from
`emitted_ok` and `grade_eq` (no second evaluation); `treeMbu` and `treeCoherent` by `decide +kernel`
on the builder through `except_ok_of_check`; `fewLogMbu` through `groverCircuitFew_ok_of` as a
few:log certificate does (the MCZ plan of `mczFew` sorts, which the kernel does not evaluate
directly: `mczFew_eq_K`), with its own oracle and MCZ literals `sel_fewOracle`, `sel_fewMcz`; a
builder that fails at the instance is stated as such. -/
def CandidateResult.decl (c : CandidateResult) (chosen : Candidate) (n r : Nat) : String :=
  let b := s!"{c.cand.lit}.build net {n} {r}"
  match c.grade with
  | none =>
    s!"/-- The builder of `{c.cand.name}` fails at this instance (not admissible). -/
theorem cand_fail_{c.cand.name} : ({b}).toBool = false := by decide +kernel
"
  | some g =>
    if c.cand == .fewLogMbu && c.cand != chosen then
      s!"/-- The MBU oracle and the few-ancilla MCZ of candidate `fewLogMbu` (as a few:log certificate
states them; `groverCircuitFew` is linked through `groverCircuitFew_ok_of`, since the MCZ plan sorts
and is not evaluated by the kernel directly: `mczFew_eq_K`). -/
def sel_fewOracle : Circuit := okPayload (synthesizeOracle net)

theorem sel_fewOracle_ok : synthesizeOracle net = .ok sel_fewOracle :=
  except_eq_ok_okPayload (synthesizeOracle net) (by decide +kernel)

def sel_fewMcz : Circuit := okPayload (mczFewK {n} .logDepth)

theorem sel_fewMcz_ok : mczFew {n} .logDepth = .ok sel_fewMcz := by
  rw [mczFew_eq_K]
  exact except_eq_ok_okPayload (mczFewK {n} .logDepth) (by decide +kernel)

/-- The grade of candidate `fewLogMbu`: the kernel evaluates the circuit of `groverCircuitFew_ok_of`. -/
theorem cand_grade_fewLogMbu : Synthesis.grade <$> {b} = .ok {gradeLit g} := by
  show Synthesis.grade <$> groverCircuitFew net {n} {r} .logDepth = _
  rw [groverCircuitFew_ok_of (n := {n}) (r := {r}) (rfl : net.nInputs = {n}) sel_fewOracle_ok sel_fewMcz_ok,
    Except.map_ok]
  exact congrArg Except.ok (by decide +kernel)
"
    else if c.cand == chosen then
      let builder := match c.cand with
        | .treeMbu => s!"groverCircuit net {n} {r}"
        | .treeCoherent => s!"groverCircuit net {n} {r} none .tree .coherent"
        | .fewLogMbu => s!"groverCircuitFew net {n} {r} .logDepth"
      s!"/-- The grade of the chosen candidate `{c.cand.name}`: from `emitted_ok` and `grade_eq`. -/
theorem cand_grade_{c.cand.name} : Synthesis.grade <$> {b} = .ok {gradeLit g} := by
  show Synthesis.grade <$> {builder} = _
  rw [emitted_ok, Except.map_ok, grade_eq]
"
    else
      s!"/-- The grade of candidate `{c.cand.name}`: one kernel evaluation of its builder. -/
theorem cand_grade_{c.cand.name} : Synthesis.grade <$> {b} = .ok {gradeLit g} :=
  except_ok_of_check _ _ (by decide +kernel)
"

/-- The arm of `selected` for one candidate. -/
def CandidateResult.arm (c : CandidateResult) : String :=
  match c.grade with
  | none => s!"  · have h := cand_fail_{c.cand.name}
    rw [hC] at h
    simp [Except.toBool] at h
"
  | some _ => s!"  · have h := cand_grade_{c.cand.name}
    rw [hC, Except.map_ok, Except.ok.injEq] at h
    rw [h] at hle ⊢
    revert hle
    decide
"

/-- PHASE2_SPEC §A.6 (8), (8′) — the selection block appended before the final `end` of the chosen
candidate's ordinary `Cert.lean`: `budget`, the candidate grades, `chosen_fits`, `selected`, and
their audit lines. -/
def renderSelection (q : CertRequest) (s : SelectionInfo) : String :=
  let n := q.n
  let r := q.r
  let budgetArg := s!"{s.budget.w},{s.budget.d},{s.budget.t},{s.budget.a}"
  s!"/-! ## Certified selection (PHASE2_SPEC §A.6 (8), (8′)) — generated by `cqr certify --budget {budgetArg} --prefer {s.pref.name}` -/

/-- The budget `--budget {budgetArg}` (the component-wise order of report §3.1.2). -/
def budget : Grade := {gradeLit s.budget}

{String.join (s.results.map fun c => c.decl s.chosen n r ++ "\n")}/-- The chosen candidate fits the budget. -/
theorem chosen_fits : Synthesis.grade emitted ≤ budget := by
  rw [grade_eq]
  decide

/-- PHASE2_SPEC §A.6 (8′) — **the selection is certified against the builders**: no candidate whose
builder succeeds at this instance and whose grade fits the budget has a key (prefer {s.pref.name}:
{s.pref.order}) strictly below the key of the emitted circuit. -/
theorem selected : ∀ c ∈ Patterns.candidates, ∀ C, c.build net {n} {r} = .ok C →
    Synthesis.grade C ≤ budget →
    ¬ Patterns.lexLt (Patterns.Grade.key {s.pref.lit} (Synthesis.grade C))
      (Patterns.Grade.key {s.pref.lit} (Synthesis.grade emitted)) := by
  intro c hc C hC hle
  rw [grade_eq]
  simp only [Patterns.candidates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
{String.join (s.results.map (·.arm))}
#print axioms chosen_fits

#print axioms selected
"

/-- Insert the selection block before the final `end` line of an ordinary `Cert.lean` text, so that
removing the block gives the ordinary file back byte for byte. -/
def insertSelection (text block : String) : String :=
  match text.splitOn "\nend " with
  | [] => text ++ block
  | parts =>
    let last := parts.getLast!
    let front := "\nend ".intercalate (parts.dropLast)
    front ++ "\n" ++ block ++ "\nend " ++ last

end CQRV.Patterns

end
