module

public import CQRV.Grover.MczFew

/-!
# CQRV.Grover.MczFewAll

Report §6.2 (restoration co-equal), §6.3.2, §8.2, §9.5.2 — Stage 13a: Khattar–Gidney Theorem 5.1
(Quantum 9, 1752 (2025), §5.1–5.3) for **every** `n`: the few-ancilla MCZ `mczFew n .logDepth`
restores its two clean ancillae and is the phase oracle of `x₀ ∧ … ∧ x_{n−1}`, with no per-instance
check (DECISIONS.md 2026-10-27, Stage 13a). The definitions of `CQRV.Synthesis.MczFew` are not
changed; the Stage 12d theorem `mczFew_ancRestore_of_classical` is applied with its hypotheses
proved for all `n`.

* **L1** (`KG.inv_step`, `KG.sim`) — the schedule-independent invariant of KG §5.1 on an index
  model (marks `M`, values `v`, `F` the product of the initial unmarked values), preserved by every
  valid operation `(t, x, y)` (`t < x < y`, `M t`, `¬M x`, `¬M y`):
  (a) the product of the unmarked values is `F`;
  (b) every marked `t > 0` holding 0 has a 0 among the unmarked values left of it (conditionally
      clean);
  (c) a marked index 0 holds 0.
  `sim` transports it through `stepRun` for a duplicate-free qubit array, with `stepsPre` and
  `stepOk` on the way.
* **L2** (`KG.greedy_spec`, `KG.doubling_spec`) — validity of the schedule: `greedy` by
  construction; `doubling n` from `true :: replicate n false` with the closed form
  `0^{i+1} 1^{2^{i+1}} 0…` after timestep `i` (each sub-step works on the intervals
  `P = [a, a + 2^f)`, `Q = [a + 2^f, a + 2^{f+1}]`).
* **L3** — `stepOk`, `inRange`, `C.WF`, `C.nBits = nAnd`, for every `n`.
* **L4** — `mczFew n .logDepth` succeeds for every `n ≥ 1`.
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis CQRV.Synthesis.MczFew

namespace KG

/-! ## L1 — the invariant of KG §5.1 on the index model -/

/-- The marks of an array (`false` past its end). -/
def mk (A : List Bool) (i : ℕ) : Bool := A.getD i false

/-- `applyOp` on marks: `M t = 0`, `M x = M y = 1`. -/
def applyF (M : ℕ → Bool) (o : Op) : ℕ → Bool :=
  Function.update (Function.update (Function.update M o.1 false) o.2.1 true) o.2.2 true

/-- The value an operation writes on `t`: `x ∧ y` on the clean index 0 (Gidney's AND),
`¬(t ⊕ x ∧ y)` elsewhere (`rtof; X t`). -/
def newVal (v : ℕ → Bool) (o : Op) : Bool :=
  if o.1 = 0 then v o.2.1 && v o.2.2 else !(v o.1 ^^ (v o.2.1 && v o.2.2))

/-- An operation on values. -/
def opV (v : ℕ → Bool) (o : Op) : ℕ → Bool := Function.update v o.1 (newVal v o)

/-- The product of the unmarked values below `s` is 1. -/
def Clear (M v : ℕ → Bool) (s : ℕ) : Prop := ∀ i < s, M i = true ∨ v i = true

/-- Report §6.1.4, KG §5.1 (Stage 13a L1) — the invariant on an array of length `L`. -/
structure Inv (L : ℕ) (M v : ℕ → Bool) (F : Bool) : Prop where
  /-- (a) the product of the unmarked values is `F`. -/
  prod : Clear M v L ↔ F = true
  /-- (b) a marked `t > 0` holding 0 is conditionally clean. -/
  cond : ∀ t < L, 0 < t → M t = true → v t = false → ¬ Clear M v t
  /-- (c) a marked index 0 is clean. -/
  clean : M 0 = true → v 0 = false

theorem not_clear {M v : ℕ → Bool} {s : ℕ} :
    ¬ Clear M v s ↔ ∃ i < s, M i = false ∧ v i = false := by
  simp only [Clear, not_forall, not_or, Bool.not_eq_true, exists_prop]

/-- Report §6.1.4, KG §5.1, Theorem 5.1 (Stage 13a L1) — **every valid operation preserves the
invariant**. -/
theorem inv_step {L : ℕ} {M v : ℕ → Bool} {F : Bool} {t x y : ℕ} (htx : t < x) (hxy : x < y)
    (hyL : y < L) (hMt : M t = true) (hMx : M x = false) (hMy : M y = false)
    (h : Inv L M v F) : Inv L (applyF M (t, x, y)) (opV v (t, x, y)) F := by
  have hM' : ∀ i, applyF M (t, x, y) i =
      if i = y then true else if i = x then true else if i = t then false else M i := by
    intro i; simp only [applyF, Function.update_apply]
  have hv' : ∀ i, opV v (t, x, y) i = if i = t then newVal v (t, x, y) else v i := by
    intro i; simp only [opV, Function.update_apply]
  have hty : t ≠ y := by omega
  have htx' : t ≠ x := by omega
  have hM't : applyF M (t, x, y) t = false := by rw [hM', ite_eq_right hty, ite_eq_right htx', ite_eq_left rfl]
  have hv't : opV v (t, x, y) t = newVal v (t, x, y) := by rw [hv', ite_eq_left rfl]
  have other : ∀ s, (∃ i < s, i ≠ t ∧ i ≠ x ∧ i ≠ y ∧ M i = false ∧ v i = false) →
      ¬ Clear (applyF M (t, x, y)) (opV v (t, x, y)) s := by
    rintro s ⟨i, his, hit, hix, hiy, hMi, hvi⟩
    rw [not_clear]
    exact ⟨i, his, by rw [hM', ite_eq_right hiy, ite_eq_right hix, ite_eq_right hit, hMi],
      by rw [hv', ite_eq_right hit, hvi]⟩
  -- a zero of `x ∧ y`, or an old zero away from `t, x, y`, is a zero of the new product
  have H1 : ∀ s, t < s → ((v x && v y) = false ∨
      ∃ i < s, i ≠ t ∧ i ≠ x ∧ i ≠ y ∧ M i = false ∧ v i = false) →
      ¬ Clear (applyF M (t, x, y)) (opV v (t, x, y)) s := by
    intro s hts hz
    rcases hz with hz | hz
    · have hzero : newVal v (t, x, y) = false ∨
          ∃ i < s, i ≠ t ∧ i ≠ x ∧ i ≠ y ∧ M i = false ∧ v i = false := by
        by_cases ht0 : t = 0
        · left; simp only [newVal, ite_eq_left ht0, hz]
        · cases hvt : v t
          · right
            have := h.cond t (by omega) (Nat.pos_of_ne_zero ht0) hMt hvt
            rw [not_clear] at this
            obtain ⟨i, hit, hMi, hvi⟩ := this
            exact ⟨i, by omega, by omega, by omega, by omega, hMi, hvi⟩
          · left; simp only [newVal, ite_eq_right ht0, hz, hvt, Bool.xor_false, Bool.not_true]
      rcases hzero with hzero | hzero
      · rw [not_clear]
        exact ⟨t, hts, hM't, hv't.trans hzero⟩
      · exact other s hzero
    · exact other s hz
  -- an old zero below `s > t` gives one of the two cases of `H1`
  have old : ∀ s, t < s → ¬ Clear M v s → ¬ Clear (applyF M (t, x, y)) (opV v (t, x, y)) s := by
    intro s hts hn
    rw [not_clear] at hn
    obtain ⟨i, his, hMi, hvi⟩ := hn
    have hit : i ≠ t := by rintro rfl; rw [hMt] at hMi; exact absurd hMi (by decide)
    apply H1 s hts
    by_cases hix : i = x
    · left; rw [← hix, hvi, Bool.false_and]
    · by_cases hiy : i = y
      · left; rw [← hiy, hvi, Bool.and_false]
      · right; exact ⟨i, his, hit, hix, hiy, hMi, hvi⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    rw [← h.prod]
    constructor
    · intro hc
      by_contra hn
      exact old L (by omega) hn hc
    · intro hc i hi
      rw [hM', hv']
      by_cases hiy : i = y
      · left; rw [ite_eq_left hiy]
      by_cases hix : i = x
      · left; rw [ite_eq_right hiy, ite_eq_left hix]
      by_cases hit : i = t
      · right
        rw [ite_eq_left hit]
        have hxv : v x = true := (hc x (by omega)).resolve_left (by rw [hMx]; decide)
        have hyv : v y = true := (hc y hyL).resolve_left (by rw [hMy]; decide)
        by_cases ht0 : t = 0
        · simp only [newVal, ite_eq_left ht0, hxv, hyv, Bool.and_self]
        · cases hvt : v t
          · exact absurd (fun j hj => hc j (by omega))
              (h.cond t (by omega) (Nat.pos_of_ne_zero ht0) hMt hvt)
          · simp only [newVal, ite_eq_right ht0, hxv, hyv, hvt, Bool.and_self, Bool.xor_self,
              Bool.not_false]
      · rw [ite_eq_right hiy, ite_eq_right hix, ite_eq_right hit, ite_eq_right hit]
        exact hc i hi
  · -- (b)
    intro s hsL hs0 hMs hvs
    rw [hM'] at hMs
    by_cases hsy : s = y
    · rw [hv', ite_eq_right (by omega), hsy] at hvs
      exact H1 s (by omega) (Or.inl (by rw [hvs, Bool.and_false]))
    by_cases hsx : s = x
    · rw [hv', ite_eq_right (by omega), hsx] at hvs
      exact H1 s (by omega) (Or.inl (by rw [hvs, Bool.false_and]))
    by_cases hst : s = t
    · rw [ite_eq_right hsy, ite_eq_right hsx, ite_eq_left hst] at hMs
      exact absurd hMs (by decide)
    rw [ite_eq_right hsy, ite_eq_right hsx, ite_eq_right hst] at hMs
    rw [hv', ite_eq_right hst] at hvs
    have hold := h.cond s hsL hs0 hMs hvs
    by_cases hlt : s < t
    · intro hc
      apply hold
      intro i hi
      have := hc i hi
      rwa [hM', hv', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)] at this
    · exact old s (by omega) hold
  · -- (c)
    intro h0
    rw [hM', ite_eq_right (by omega), ite_eq_right (by omega)] at h0
    by_cases h0t : (0 : ℕ) = t
    · rw [ite_eq_left h0t] at h0; exact absurd h0 (by decide)
    · rw [ite_eq_right h0t] at h0
      rw [hv', ite_eq_right h0t]
      exact h.clean h0

/-! ## Arrays and valid operation lists -/

theorem getD_lt {α : Type} {l : List α} {i : ℕ} (h : i < l.length) {d : α} : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem applyF_apply (M : ℕ → Bool) (t x y j : ℕ) : applyF M (t, x, y) j =
    if j = y then true else if j = x then true else if j = t then false else M j := by
  simp only [applyF, Function.update_apply]

theorem applyOp_length (A : List Bool) (o : Op) : (applyOp A o).length = A.length := by
  simp [applyOp]

theorem foldl_applyOp_length :
    ∀ (ops : List Op) (A : List Bool), (ops.foldl applyOp A).length = A.length
  | [], _ => rfl
  | o :: ops, A => by rw [List.foldl_cons, foldl_applyOp_length ops, applyOp_length]

theorem mk_of_lt {A : List Bool} {i : ℕ} (h : i < A.length) (d : Bool) : A.getD i d = mk A i := by
  simp only [mk, getD_lt h]

theorem lt_of_mk {A : List Bool} {i : ℕ} (h : mk A i = true) : i < A.length := by
  by_contra hi
  rw [mk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show A.length ≤ i by omega)] at h
  cases h

theorem validOp_spec {A : List Bool} {o : Op} (h : validOp A o = true) :
    o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 < A.length ∧ mk A o.1 = true ∧ mk A o.2.1 = false ∧
      mk A o.2.2 = false := by
  obtain ⟨t, x, y⟩ := o
  simp only [validOp, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨htx, hxy⟩, hMt⟩, hMx⟩, hMy⟩ := h
  have hyL : y < A.length := by
    by_contra hy
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show A.length ≤ y by omega)] at hMy
    cases hMy
  refine ⟨htx, hxy, hyL, hMt, ?_, ?_⟩
  · rwa [mk_of_lt (by omega)] at hMx
  · rwa [mk_of_lt hyL] at hMy

theorem validOp_of {A : List Bool} {t x y : ℕ} (htx : t < x) (hxy : x < y) (hyL : y < A.length)
    (hMt : mk A t = true) (hMx : mk A x = false) (hMy : mk A y = false) :
    validOp A (t, x, y) = true := by
  simp only [validOp, mk_of_lt (show t < A.length by omega), mk_of_lt (show x < A.length by omega),
    mk_of_lt hyL, hMt, hMx, hMy, htx, hxy, decide_true, Bool.and_self, Bool.not_false]

theorem mk_applyOp {A : List Bool} {o : Op} (ht : o.1 < A.length) (hx : o.2.1 < A.length)
    (hy : o.2.2 < A.length) : mk (applyOp A o) = applyF (mk A) o := by
  obtain ⟨t, x, y⟩ := o
  funext i
  rw [applyF_apply]
  simp only [mk, applyOp, List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set]
  simp only at ht hx hy
  by_cases hiy : i = y
  · subst hiy; simp [hy]
  by_cases hix : i = x
  · subst hix; simp [hx, Ne.symm hiy]
  by_cases hit : i = t
  · subst hit; simp [ht, Ne.symm hiy, Ne.symm hix, hiy, hix]
  simp [Ne.symm hiy, Ne.symm hix, Ne.symm hit, hiy, hix, hit]

theorem valid_append (A : List Bool) (l₁ l₂ : List Op) :
    valid A (l₁ ++ l₂) = (valid A l₁ && valid (l₁.foldl applyOp A) l₂) := by
  induction l₁ generalizing A with
  | nil => simp [valid]
  | cons o l ih => simp only [List.cons_append, valid, ih, List.foldl_cons, Bool.and_assoc]

theorem valid_bounds : ∀ (ops : List Op) (A : List Bool), valid A ops = true →
    ∀ o ∈ ops, o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 < A.length
  | [], _, _, o, ho => by simp at ho
  | o' :: ops, A, h, o, ho => by
    simp only [valid, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ho with rfl | ho
    · obtain ⟨h1, h2, h3, -⟩ := validOp_spec h.1
      exact ⟨h1, h2, h3⟩
    · have := valid_bounds ops _ h.2 o ho
      rwa [applyOp_length] at this

/-! ## The simulation through `stepRun` -/

/-- The values of the qubit array `qs` in the basis state `s` (`false` past its end). -/
def vals {n m : ℕ} (qs : List Qubit) (s : Reg n × Reg m) (i : ℕ) : Bool :=
  if h : i < qs.length then qs[i].get s else false

theorem vals_lt {n m : ℕ} {qs : List Qubit} (s : Reg n × Reg m) {i : ℕ} (h : i < qs.length) :
    vals qs s i = qs[i].get s := by
  simp only [vals, h, dite_true]

/-- One element of `stepsOf`: the compute step of an operation over `qs`. -/
def stepOf (qs : List Qubit) (o : Op) : Step :=
  (qs.getD o.2.1 default, qs.getD o.2.2 default, qs.getD o.1 default, o.1 == 0)

theorem stepsOf_cons (qs : List Qubit) (o : Op) (ops : List Op) :
    stepsOf qs (o :: ops) = stepOf qs o :: stepsOf qs ops := rfl

theorem stepsOf_append (qs : List Qubit) (l₁ l₂ : List Op) :
    stepsOf qs (l₁ ++ l₂) = stepsOf qs l₁ ++ stepsOf qs l₂ := List.map_append

theorem runSteps_append {n m : ℕ} (l₁ l₂ : List Step) (s : Reg n × Reg m) :
    runSteps (l₁ ++ l₂) s = runSteps l₂ (runSteps l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons st l ih => exact ih _

theorem stepsPre_append {n m : ℕ} (l₁ l₂ : List Step) (s : Reg n × Reg m) :
    stepsPre (l₁ ++ l₂) s = (stepsPre l₁ s && stepsPre l₂ (runSteps l₁ s)) := by
  induction l₁ generalizing s with
  | nil => simp [stepsPre, runSteps]
  | cons st l ih => simp only [List.cons_append, stepsPre, ih, runSteps, Bool.and_assoc]

theorem stepRun_stepOf {n m : ℕ} (qs : List Qubit) {t x y : ℕ} (ht : t < qs.length)
    (hx : x < qs.length) (hy : y < qs.length) (s : Reg n × Reg m) :
    stepRun (stepOf qs (t, x, y)) s = qs[t].set (newVal (vals qs s) (t, x, y)) s := by
  simp only [stepOf, getD_lt ht, getD_lt hx,
    getD_lt hy]
  by_cases h0 : t = 0
  · subst h0
    simp [stepRun, newVal, vals_lt s hx, vals_lt s hy]
  · have h0' : (t == 0) = false := by simpa using h0
    simp only [h0', stepRun, newVal, h0, ite_false, vals_lt s ht, vals_lt s hx, vals_lt s hy]

/-- Report §6.1.4 (Stage 13a) — one compute step on the qubit array `qs` is the operation on the
index model. -/
theorem vals_stepRun {n m : ℕ} {qs : List Qubit} (hnd : qs.Nodup)
    (hr : ∀ q ∈ qs, q.inRange n m = true) {t x y : ℕ} (ht : t < qs.length) (hx : x < qs.length)
    (hy : y < qs.length) (s : Reg n × Reg m) :
    vals qs (stepRun (stepOf qs (t, x, y)) s) = opV (vals qs s) (t, x, y) := by
  have hqt : (qs[t]).inRange n m = true := hr _ (List.getElem_mem _)
  funext i
  rw [opV, Function.update_apply, stepRun_stepOf qs ht hx hy]
  by_cases hi : i < qs.length
  · rw [vals_lt _ hi]
    by_cases hit : i = t
    · subst hit; rw [Qubit.get_set_self _ hqt, ite_eq_left rfl]
    · rw [Qubit.get_set_ne (fun e => hit ((hnd.getElem_inj_iff).mp e)), ite_eq_right hit,
        vals_lt _ hi]
  · rw [ite_eq_right (by omega)]
    simp only [vals, hi, dite_false]

theorem stepOk_stepOf {n m : ℕ} {qs : List Qubit} (hnd : qs.Nodup)
    (hr : ∀ q ∈ qs, q.inRange n m = true) {t x y : ℕ} (htx : t < x) (hxy : x < y)
    (hy : y < qs.length) : stepOk n m (stepOf qs (t, x, y)) = true := by
  simp only [stepOf, getD_lt (show t < qs.length by omega),
    getD_lt (show x < qs.length by omega), getD_lt hy, stepOk,
    Bool.and_eq_true, bne_iff_ne, ne_eq, hnd.getElem_inj_iff]
  refine ⟨⟨⟨⟨⟨hr _ (List.getElem_mem _), hr _ (List.getElem_mem _)⟩, hr _ (List.getElem_mem _)⟩,
    by omega⟩, by omega⟩, by omega⟩

/-- Report §6.1.4, KG Theorem 5.1 (Stage 13a L1) — **the simulation lemma**: over a duplicate-free
qubit array in the register, valid operations keep the invariant on the basis state reached by
`runSteps`, every AND target is clean when it is computed (`stepsPre`), and every step passes
the qubit checks. -/
theorem sim {n m : ℕ} {qs : List Qubit} (hnd : qs.Nodup) (hr : ∀ q ∈ qs, q.inRange n m = true)
    {F : Bool} : ∀ (ops : List Op) (A : List Bool) (s : Reg n × Reg m), A.length = qs.length →
      valid A ops = true → Inv qs.length (mk A) (vals qs s) F →
      stepsPre (stepsOf qs ops) s = true ∧ (stepsOf qs ops).all (stepOk n m) = true ∧
        Inv qs.length (mk (ops.foldl applyOp A)) (vals qs (runSteps (stepsOf qs ops) s)) F
  | [], _, _, _, _, hI => ⟨rfl, rfl, hI⟩
  | ⟨t, x, y⟩ :: ops, A, s, hL, hv, hI => by
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨htx, hxy, hyL, hMt, hMx, hMy⟩ := validOp_spec hv.1
    simp only at htx hxy hyL hMt hMx hMy
    have hyq : y < qs.length := hL ▸ hyL
    have hI' := inv_step htx hxy hyq hMt hMx hMy hI
    rw [← mk_applyOp (A := A) (o := (t, x, y)) (by simp only; omega) (by simp only; omega) hyL,
      ← vals_stepRun hnd hr (by omega) (by omega) hyq s] at hI'
    obtain ⟨h1, h2, h3⟩ := sim hnd hr ops (applyOp A (t, x, y)) _ (by rw [applyOp_length, hL])
      hv.2 hI'
    refine ⟨?_, ?_, h3⟩
    · rw [stepsOf_cons, stepsPre, h1, Bool.and_true]
      by_cases ht0 : t = 0
      · subst ht0
        have h0 := hI.clean hMt
        rw [vals_lt s (by omega)] at h0
        rw [stepOf, getD_lt (show 0 < qs.length by omega)]
        simp [stepPre, h0]
      · have h0' : (t == 0) = false := by simpa using ht0
        simp [stepOf, stepPre, h0']
    · rw [stepsOf_cons, List.all_cons, h2, Bool.and_true]
      exact stepOk_stepOf hnd hr htx hxy hyq

/-- The steps over `qs` touch only the qubits of `qs`. -/
theorem get_runSteps_not_mem {n m : ℕ} {qs : List Qubit} {q : Qubit} (hq : q ∉ qs) :
    ∀ (ops : List Op) (s : Reg n × Reg m), (∀ o ∈ ops, o.1 < qs.length) →
      q.get (runSteps (stepsOf qs ops) s) = q.get s
  | [], _, _ => rfl
  | ⟨t, x, y⟩ :: ops, s, h => by
    rw [stepsOf_cons, runSteps,
      get_runSteps_not_mem hq ops _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
    have ht : t < qs.length := h _ List.mem_cons_self
    have hne : q ≠ qs.getD t default := by
      rw [getD_lt ht]; rintro rfl; exact hq (List.getElem_mem _)
    simp only [stepOf]
    generalize (t == 0) = b
    cases b <;> exact Qubit.get_set_ne hne _ _

/-! ## Initial arrays and the product of the unmarked qubits -/

theorem mk_init (k : ℕ) : mk (true :: List.replicate k false) = fun i => decide (i = 0) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [mk, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate]
    split <;> rfl

/-- The invariant on a fresh array `c :: us` (`c` clean): `F` is the product of `us`. -/
theorem inv_init {n m : ℕ} (c : Qubit) (us : List Qubit) (s : Reg n × Reg m)
    (hc : c.get s = false) :
    Inv (c :: us).length (mk (true :: List.replicate us.length false)) (vals (c :: us) s)
      (us.all (·.get s)) := by
  rw [mk_init]
  refine ⟨?_, ?_, fun _ => by rw [vals_lt s (by simp)]; exact hc⟩
  · simp only [List.length_cons, Clear, List.all_eq_true, List.mem_iff_getElem]
    constructor
    · rintro h q ⟨i, hi, rfl⟩
      have := (h (i + 1) (by omega)).resolve_left (by simp)
      rwa [vals_lt s (by simp; omega)] at this
    · intro h i hi
      cases i with
      | zero => left; rfl
      | succ i =>
        right
        rw [vals_lt s (by simp; omega)]
        exact h _ ⟨i, by omega, rfl⟩
  · intro t _ ht0 hMt
    simp only [decide_eq_true_eq] at hMt
    omega

theorem all_unmarked {n m : ℕ} (qs : List Qubit) (A : List Bool) (hL : A.length = qs.length)
    (s : Reg n × Reg m) :
    (unmarkedQubits qs A).all (·.get s) = true ↔ Clear (mk A) (vals qs s) qs.length := by
  simp only [unmarkedQubits, List.all_map, List.all_filter, List.all_eq_true, List.mem_range,
    Function.comp_apply, Clear]
  constructor
  · intro h i hi
    have hiA : i < A.length := by omega
    have := h i hiA
    rw [mk_of_lt hiA, getD_lt hi] at this
    rw [vals_lt s hi]
    cases hm : mk A i <;> simp_all
  · intro h i hiA
    have hi : i < qs.length := by omega
    rw [mk_of_lt hiA, getD_lt hi]
    have := h i hi
    rw [vals_lt s hi] at this
    cases hm : mk A i <;> simp_all

theorem unmarkedQubits_nodup {qs : List Qubit} (hnd : qs.Nodup) {A : List Bool}
    (hL : A.length = qs.length) : (unmarkedQubits qs A).Nodup := by
  unfold unmarkedQubits
  refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro i hi j hj hij
  simp only [List.mem_filter, List.mem_range] at hi hj
  rw [getD_lt (by omega), getD_lt (by omega)] at hij
  exact (hnd.getElem_inj_iff).mp hij

theorem mem_unmarkedQubits {qs : List Qubit} {A : List Bool} (hL : A.length = qs.length)
    {q : Qubit} (hq : q ∈ unmarkedQubits qs A) : q ∈ qs := by
  simp only [unmarkedQubits, List.mem_map, List.mem_filter, List.mem_range] at hq
  obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hq
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

/-- Report §6.1.4, KG §5.1 (Stage 13a L1) — one array `c :: us` with a clean `c`: valid
operations from `1 0…0` compute with clean AND targets, pass the qubit checks, and leave the
product of the unmarked qubits equal to the product of `us`. -/
theorem array_spec {n m : ℕ} (c : Qubit) (us : List Qubit) (hnd : (c :: us).Nodup)
    (hr : ∀ q ∈ c :: us, q.inRange n m = true) (s : Reg n × Reg m) (hc : c.get s = false)
    (ops : List Op) (hv : valid (true :: List.replicate us.length false) ops = true) :
    stepsPre (stepsOf (c :: us) ops) s = true ∧ (stepsOf (c :: us) ops).all (stepOk n m) = true ∧
      (unmarkedQubits (c :: us) (ops.foldl applyOp (true :: List.replicate us.length false))).all
        (·.get (runSteps (stepsOf (c :: us) ops) s)) = us.all (·.get s) := by
  have hL : (true :: List.replicate us.length false).length = (c :: us).length := by simp
  obtain ⟨h1, h2, h3⟩ := sim hnd hr ops _ s hL hv (inv_init c us s hc)
  refine ⟨h1, h2, ?_⟩
  rw [Bool.eq_iff_iff, all_unmarked _ _ (by rw [foldl_applyOp_length, hL])]
  exact h3.prod

/-! ## L2 — the greedy schedule is valid (KG §5.2) -/

theorem greedyStep_valid {A : List Bool} {o : Op} (h : greedyStep A = some o) :
    validOp A o = true := by
  simp only [greedyStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, hf, h⟩ := h
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true] at hp
  split at h
  · rename_i x y rest hu
    cases h
    have hpw : (unmarkedAbove A t).Pairwise (· < ·) := List.pairwise_lt_range.filter _
    rw [hu] at hpw
    have hxy : x < y := (List.pairwise_cons.mp hpw).1 y (by simp)
    have hxm : x ∈ unmarkedAbove A t := by rw [hu]; simp
    have hym : y ∈ unmarkedAbove A t := by rw [hu]; simp
    simp only [unmarkedAbove, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true'] at hxm hym
    simp only [validOp, hxm.2.1, hxy, hp.1, hxm.2.2, hym.2.2, decide_true, Bool.and_self,
      Bool.not_false]
  · cases h

/-- Report §6.1.4, KG §5.2 (Stage 13a L2) — `greedy` returns valid operations and the array
they produce. -/
theorem greedy_spec : ∀ (f : ℕ) (A : List Bool),
    valid A (greedy f A).1 = true ∧ (greedy f A).2 = (greedy f A).1.foldl applyOp A
  | 0, _ => ⟨rfl, rfl⟩
  | f + 1, A => by
    cases hg : greedyStep A with
    | none => simp only [greedy, hg]; exact ⟨rfl, rfl⟩
    | some o =>
      obtain ⟨h1, h2⟩ := greedy_spec f (applyOp A o)
      simp only [greedy, hg, valid, greedyStep_valid hg, h1, h2, List.foldl_cons, Bool.and_self,
        and_self]

/-! ## L2 — the doubling schedule is valid (KG §5.3)

Every sub-step of timestep `i` works on two intervals: `P = [a, a + 2^f)` (marked) and
`Q = [a + 2^f, a + 2^{f+1}]` (unmarked), `a = i`. Its operations are `(c − 1 − k, c + 2k + 1,
c + 2k + 2)` for `k < 2^{f−1}`, `c = a + 2^f` (`subOps`); the next sub-step works on
`[a, a + 2^{f−1})` and `[a + 2^{f−1}, a + 2^f]` (`substeps_succ_interval`, through the
`mergeSort` of `MczFew.substeps`). -/

/-- A batch of operations whose targets are pairwise distinct and marked, and whose controls are
pairwise distinct and unmarked, is valid in any order; it unmarks the targets and marks the
controls. -/
theorem batch : ∀ (ops : List Op) (A : List Bool),
    (∀ o ∈ ops, o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 < A.length ∧ mk A o.1 = true ∧
      mk A o.2.1 = false ∧ mk A o.2.2 = false) →
    (ops.map (·.1)).Nodup → (ops.flatMap fun o => [o.2.1, o.2.2]).Nodup →
    valid A ops = true ∧ ∀ j, mk (ops.foldl applyOp A) j =
      if j ∈ ops.flatMap (fun o => [o.2.1, o.2.2]) then true
      else if j ∈ ops.map (·.1) then false else mk A j
  | [], _, _, _, _ => ⟨rfl, fun j => by simp⟩
  | ⟨t, x, y⟩ :: ops, A, h, hn1, hn2 => by
    obtain ⟨htx, hxy, hyL, hMt, hMx, hMy⟩ := h _ List.mem_cons_self
    simp only at htx hxy hyL hMt hMx hMy
    have hmk := mk_applyOp (A := A) (o := (t, x, y)) (by simp only; omega) (by simp only; omega)
      hyL
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn1
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hn2
    obtain ⟨⟨hxy', hx'⟩, hy', hn2⟩ := hn2
    -- the marks of the rest of the batch survive the first operation
    have hts : ∀ o ∈ ops, mk A o.1 = true := fun o ho => (h o (List.mem_cons_of_mem _ ho)).2.2.2.1
    have hxs : ∀ o ∈ ops, mk A o.2.1 = false ∧ mk A o.2.2 = false := fun o ho =>
      ⟨(h o (List.mem_cons_of_mem _ ho)).2.2.2.2.1, (h o (List.mem_cons_of_mem _ ho)).2.2.2.2.2⟩
    have h' : ∀ o ∈ ops, o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 < (applyOp A (t, x, y)).length ∧
        mk (applyOp A (t, x, y)) o.1 = true ∧ mk (applyOp A (t, x, y)) o.2.1 = false ∧
        mk (applyOp A (t, x, y)) o.2.2 = false := by
      intro o ho
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h o (List.mem_cons_of_mem _ ho)
      rw [applyOp_length, hmk, applyF_apply, applyF_apply, applyF_apply]
      have n1 : o.1 ≠ t := fun e => hn1.1 ⟨o, ho, e⟩
      have n2 : o.1 ≠ x := fun e => by rw [e, hMx] at a4; exact absurd a4 (by decide)
      have n3 : o.1 ≠ y := fun e => by rw [e, hMy] at a4; exact absurd a4 (by decide)
      have n4 : o.2.1 ≠ x := fun e => (hx' o ho).1 e.symm
      have n5 : o.2.1 ≠ y := fun e => (hy' o ho).1 e.symm
      have n6 : o.2.2 ≠ x := fun e => (hx' o ho).2.1 e.symm
      have n7 : o.2.2 ≠ y := fun e => (hy' o ho).2.1 e.symm
      refine ⟨a1, a2, a3, ?_, ?_, ?_⟩
      · rw [ite_eq_right n3, ite_eq_right n2, ite_eq_right n1, a4]
      · rw [ite_eq_right n5, ite_eq_right n4]; split_ifs <;> simp [a5]
      · rw [ite_eq_right n7, ite_eq_right n6]; split_ifs <;> simp [a6]
    obtain ⟨hv, hf⟩ := batch ops _ h' hn1.2 hn2
    refine ⟨by simp only [valid, validOp_of htx hxy hyL hMt hMx hMy, hv, Bool.and_self], fun j => ?_⟩
    rw [List.foldl_cons, hf j, hmk, applyF_apply]
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.mem_cons, List.map_cons]
    have hb : j ∈ ops.map (·.1) → mk A j = true := by
      intro hj
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hj
      exact hts o ho
    by_cases a : j ∈ ops.flatMap (fun o => [o.2.1, o.2.2])
    · simp only [a, ite_true, or_true]
    · by_cases c : j = y
      · subst c
        by_cases b : j ∈ ops.map (·.1)
        · rw [hb b] at hMy; exact absurd hMy (by decide)
        · simp [a, b]
      · by_cases d : j = x
        · subst d
          by_cases b : j ∈ ops.map (·.1)
          · rw [hb b] at hMx; exact absurd hMx (by decide)
          · simp [a, b, c]
        · by_cases b : j ∈ ops.map (·.1)
          · simp [a, b, c, d]
          · simp [a, b, c, d]

/-- The operations of one sub-step: `(c − 1 − k, c + 2k + 1, c + 2k + 2)`, `k < m`. -/
def subOps (c m : ℕ) : List Op :=
  (List.range m).map fun k => (c - 1 - k, c + 2 * k + 1, c + 2 * k + 2)

theorem subOps_succ (c m : ℕ) :
    subOps c (m + 1) = subOps c m ++ [(c - 1 - m, c + 2 * m + 1, c + 2 * m + 2)] := by
  simp [subOps, List.range_succ]

/-- The marked-to-be indices of a sub-step are the interval `(c, c + 2m]`. -/
theorem used_eq (c : ℕ) : ∀ m,
    (subOps c m).flatMap (fun o => [o.2.1, o.2.2]) = List.range' (c + 1) (2 * m)
  | 0 => rfl
  | m + 1 => by
    rw [subOps_succ, List.flatMap_append, used_eq c m, show 2 * (m + 1) = 2 * m + 2 by ring,
      ← List.range'_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.range'_succ,
      List.range'_zero, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> omega

theorem mem_ts {c m z : ℕ} (hm : m ≤ c) :
    z ∈ (subOps c m).map (·.1) ↔ c - m ≤ z ∧ z < c := by
  simp only [subOps, List.map_map, List.mem_map, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨c - 1 - z, by omega, by omega⟩

/-- The `mergeSort` of `MczFew.substeps` on one sub-step: the new unmarked list is
`[c − m, c]`. -/
theorem nextQ_eq (c m : ℕ) (hm : m ≤ c) :
    ((List.range' c (2 * m + 1)).filter
        (fun z => !((subOps c m).flatMap (fun o => [o.2.1, o.2.2])).contains z) ++
      (subOps c m).map (·.1)).mergeSort (fun x1 x2 => decide (x1 ≤ x2)) =
      List.range' (c - m) (m + 1) := by
  rw [used_eq]
  have hfilt : (List.range' c (2 * m + 1)).filter
      (fun z => !(List.range' (c + 1) (2 * m)).contains z) = [c] := by
    rw [List.range'_succ, List.filter_cons]
    have hc : (!(List.range' (c + 1) (2 * m)).contains c) = true := by
      simp [List.mem_range']
      intro x _
      omega
    rw [ite_eq_left hc, List.filter_eq_nil_iff.mpr]
    intro z hz
    simp [hz]
  rw [hfilt]
  have hnd : ([c] ++ (subOps c m).map (·.1)).Nodup := by
    rw [List.singleton_append, List.nodup_cons]
    refine ⟨fun h => by rw [mem_ts hm] at h; omega, ?_⟩
    simp only [subOps, List.map_map]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro k hk k' hk' h
    simp only [List.mem_range, Function.comp_apply] at hk hk' h
    omega
  have hperm : ([c] ++ (subOps c m).map (·.1)).Perm (List.range' (c - m) (m + 1)) := by
    rw [List.perm_ext_iff_of_nodup hnd List.nodup_range']
    intro z
    rw [List.singleton_append, List.mem_cons, mem_ts hm, List.mem_range']
    constructor
    · rintro (rfl | h)
      · exact ⟨m, by omega, by omega⟩
      · exact ⟨z - (c - m), by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases him : i = m
      · left; omega
      · right; omega
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => le_antisymm h1 h2) ?_
    ((List.pairwise_lt_range').imp le_of_lt) ((List.mergeSort_perm _ _).trans hperm)
  exact (List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
    (fun h => by simpa using h)

/-- KG §5.3 — one sub-step of `MczFew.substeps` on the intervals `[a, a + 2^{f+1})`,
`[a + 2^{f+1}, a + 2^{f+2}]`: the operations `subOps`, then the sub-steps on the halved
intervals. -/
theorem substeps_succ_interval (f a : ℕ) :
    substeps (f + 1) (List.range' a (2 ^ (f + 1))) (List.range' (a + 2 ^ (f + 1)) (2 ^ (f + 1) + 1)) =
      subOps (a + 2 ^ (f + 1)) (2 ^ f) ++
        substeps f (List.range' a (2 ^ f)) (List.range' (a + 2 ^ f) (2 ^ f + 1)) := by
  have hN : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
  rw [substeps]
  simp only [List.length_range']
  rw [hN]
  generalize 2 ^ f = m
  have hdiv : 2 * m / 2 = m := by omega
  have hops : (List.range m).map (fun k =>
      ((List.range' a (2 * m)).getD (2 * m - 1 - k) 0,
        (List.range' (a + 2 * m) (2 * m + 1)).getD (2 * k + 1) 0,
        (List.range' (a + 2 * m) (2 * m + 1)).getD (2 * k + 2) 0)) = subOps (a + 2 * m) m := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [getD_lt (by simp; omega), getD_lt (by simp; omega), getD_lt (by simp; omega)]
    simp only [List.getElem_range', Prod.mk.injEq]
    omega
  have htake : (List.range' a (2 * m)).take (2 * m - m) = List.range' a m := by
    rw [show 2 * m = m + m by ring, ← List.range'_append, show m + m - m = m by omega]
    exact List.take_left' (by simp)
  rw [hdiv, hops, htake, nextQ_eq _ _ (by omega), show a + 2 * m - m = a + m by omega]

/-- Report §6.1.4, KG §5.3 (Stage 13a L2) — the sub-steps `f, …, 0` of a timestep on
`[a, a + 2^f)` (marked) and `[a + 2^f, a + 2^{f+1}]` (unmarked) are valid, and they leave `a`
unmarked and `(a, a + 2^{f+1}]` marked. -/
theorem substeps_spec : ∀ (f a : ℕ) (A : List Bool), a + 2 ^ (f + 1) < A.length →
    (∀ j, a ≤ j → j < a + 2 ^ f → mk A j = true) →
    (∀ j, a + 2 ^ f ≤ j → j ≤ a + 2 ^ (f + 1) → mk A j = false) →
    valid A (substeps f (List.range' a (2 ^ f)) (List.range' (a + 2 ^ f) (2 ^ f + 1))) = true ∧
    ∀ j, mk ((substeps f (List.range' a (2 ^ f))
        (List.range' (a + 2 ^ f) (2 ^ f + 1))).foldl applyOp A) j =
      if j = a then false else if a < j ∧ j ≤ a + 2 ^ (f + 1) then true else mk A j
  | 0, a, A, hL, hP, hQ => by
    have h0 : substeps 0 (List.range' a (2 ^ 0)) (List.range' (a + 2 ^ 0) (2 ^ 0 + 1)) =
        [(a, a + 1, a + 2)] := by simp [substeps, List.range']
    rw [h0]
    simp only [zero_add, pow_zero, pow_one] at hL hP hQ ⊢
    have hMt := hP a le_rfl (by omega)
    have hMx := hQ (a + 1) le_rfl (by omega)
    have hMy := hQ (a + 2) (by omega) le_rfl
    refine ⟨by simp only [valid, validOp_of (by omega) (by omega) (by omega) hMt hMx hMy,
      Bool.and_true], fun j => ?_⟩
    rw [List.foldl_cons, List.foldl_nil, mk_applyOp (by simp only; omega) (by simp only; omega)
      (by simp only; omega), applyF_apply]
    split_ifs <;> first | rfl | omega
  | f + 1, a, A, hL, hP, hQ => by
    have e1 : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    have e2 : 2 ^ (f + 1 + 1) = 4 * 2 ^ f := by ring
    have hm0 : 0 < 2 ^ f := by positivity
    rw [substeps_succ_interval, valid_append, List.foldl_append]
    rw [e1] at hP hQ ⊢
    rw [e2] at hL hQ ⊢
    have hc : 2 ^ f ≤ a + 2 * 2 ^ f := by omega
    obtain ⟨hb1, hb2⟩ := batch (subOps (a + 2 * 2 ^ f) (2 ^ f)) A
      (by
        intro o ho
        simp only [subOps, List.mem_map, List.mem_range] at ho
        obtain ⟨k, hk, rfl⟩ := ho
        refine ⟨by simp only; omega, by simp only; omega, by simp only; omega, ?_, ?_, ?_⟩
        · exact hP _ (by omega) (by omega)
        · exact hQ (a + 2 * 2 ^ f + 2 * k + 1) (by omega) (by omega)
        · exact hQ (a + 2 * 2 ^ f + 2 * k + 2) (by omega) (by omega))
      (by
        simp only [subOps, List.map_map]
        refine List.Nodup.map_on ?_ List.nodup_range
        intro k hk k' hk' h
        simp only [List.mem_range, Function.comp_apply] at hk hk' h
        omega)
      (by rw [used_eq]; exact List.nodup_range')
    have hlen : ((subOps (a + 2 * 2 ^ f) (2 ^ f)).foldl applyOp A).length = A.length :=
      foldl_applyOp_length _ _
    have ih := substeps_spec f a ((subOps (a + 2 * 2 ^ f) (2 ^ f)).foldl applyOp A)
      (by rw [hlen, e1]; omega)
      (by
        intro j h1 h2
        rw [hb2, used_eq, ite_eq_right (by rw [List.mem_range']; omega), ite_eq_right (by rw [mem_ts hc]; omega)]
        exact hP j h1 (by omega))
      (by
        intro j h1 h2
        rw [e1] at h2
        rw [hb2, used_eq, ite_eq_right (by rw [List.mem_range']; omega)]
        by_cases hj : j < a + 2 * 2 ^ f
        · rw [ite_eq_left (by rw [mem_ts hc]; omega)]
        · rw [ite_eq_right (by rw [mem_ts hc]; omega)]
          exact hQ j (by omega) (by omega))
    rw [e1] at ih
    refine ⟨by rw [hb1, ih.1, Bool.true_and], fun j => ?_⟩
    rw [ih.2 j, hb2 j, used_eq]
    simp only [mem_ts hc, List.mem_range'_1]
    generalize 2 ^ f = m at *
    split_ifs <;> first | rfl | omega

/-- Report §6.1.4, KG §5.3 — timestep `i` on the intervals `[i, i + 2^i)`, `[i + 2^i, i + 2^{i+1}]`. -/
theorem timestep_eq (i : ℕ) :
    timestep i = substeps i (List.range' i (2 ^ i)) (List.range' (i + 2 ^ i) (2 ^ i + 1)) := by
  simp only [timestep, List.range'_eq_map_range]

/-- Report §6.1.4, KG §5.3 (Stage 13a L2) — the first `k` timesteps (all fitting `n`) are valid
from `1 0^n`, and after them the array is `0^k 1^{2^k} 0…` (the closed form of the paper's
`n = 36` figure). -/
theorem timesteps_spec (n : ℕ) : ∀ k, (∀ i < k, i + 2 ^ (i + 1) ≤ n) →
    valid (true :: List.replicate n false) ((List.range k).flatMap timestep) = true ∧
    ∀ j, mk (((List.range k).flatMap timestep).foldl applyOp (true :: List.replicate n false)) j =
      decide (k ≤ j ∧ j < k + 2 ^ k)
  | 0, _ => ⟨rfl, fun j => by simp [mk_init]⟩
  | k + 1, h => by
    obtain ⟨ih1, ih2⟩ := timesteps_spec n k (fun i hi => h i (by omega))
    have hk := h k (by omega)
    have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      valid_append, List.foldl_append, ih1, Bool.true_and, timestep_eq]
    have hlen : (((List.range k).flatMap timestep).foldl applyOp
        (true :: List.replicate n false)).length = n + 1 := by
      rw [foldl_applyOp_length]; simp
    obtain ⟨h1, h2⟩ := substeps_spec k k _ (by rw [hlen]; omega)
      (fun j h1 h2 => by rw [ih2]; simp only [decide_eq_true_eq]; omega)
      (fun j h1 h2 => by rw [ih2]; simp only [decide_eq_false_iff_not]; omega)
    refine ⟨h1, fun j => ?_⟩
    rw [h2, ih2, e1]
    rw [e1] at hk
    generalize 2 ^ k = m at *
    split_ifs <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq,
      Bool.true_eq, decide_eq_decide] <;> omega

theorem filter_range_downward (p : ℕ → Bool) (hp : ∀ i j, i ≤ j → p j = true → p i = true) :
    ∀ N, ∃ k, (List.range N).filter p = List.range k ∧ ∀ i < k, p i = true
  | 0 => ⟨0, rfl, by simp⟩
  | N + 1 => by
    obtain ⟨k, hk, hpk⟩ := filter_range_downward p hp N
    rw [List.range_succ, List.filter_append, hk]
    by_cases hN : p N = true
    · have hkN : k = N := by
        have h1 : (List.range N).filter p = List.range N :=
          List.filter_eq_self.mpr (fun i hi => hp i N (by rw [List.mem_range] at hi; omega) hN)
        rw [hk] at h1
        simpa using congrArg List.length h1
      subst hkN
      exact ⟨k + 1, by simp [hN, List.range_succ], fun i _ => hp i k (by omega) hN⟩
    · exact ⟨k, by simp [hN], hpk⟩

/-- Report §6.1.4, KG §5.3 (Stage 13a L2) — **`doubling n` is valid from `1 0^n`** for every `n`,
and leaves `0^k 1^{2^k} 0…` for `k` the number of full timesteps. -/
theorem doubling_spec (n : ℕ) : ∃ k,
    valid (true :: List.replicate n false) (doubling n) = true ∧
    ∀ j, mk ((doubling n).foldl applyOp (true :: List.replicate n false)) j =
      decide (k ≤ j ∧ j < k + 2 ^ k) := by
  obtain ⟨k, hk, hpk⟩ := filter_range_downward (fun i => decide (i + 2 ^ (i + 1) ≤ n))
    (fun i j hij h => by
      simp only [decide_eq_true_eq] at h ⊢
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show i + 1 ≤ j + 1 by omega)
      omega) n
  refine ⟨k, ?_⟩
  rw [doubling, hk]
  exact timesteps_spec n k (fun i hi => by simpa using hpk i hi)

/-! ## The two arrays of candidate B -/

theorem data_all {n : ℕ} (x : Reg n) :
    ((List.range n).map Qubit.data).all (·.get ((x, fun _ => false) : Reg n × Reg 2)) =
      allOnes x := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply, allOnes,
    decide_eq_true_eq, Qubit.get]
  constructor
  · intro h i
    have := h i i.2
    simpa [i.2] using this
  · intro h i hi
    simp [hi, h]

theorem qs0_nodup (n : ℕ) : (Qubit.anc 0 :: (List.range n).map Qubit.data).Nodup := by
  rw [List.nodup_cons]
  exact ⟨by simp, List.Nodup.map (fun i j h => Qubit.data.inj h) List.nodup_range⟩

theorem qs0_inRange (n : ℕ) :
    ∀ q ∈ Qubit.anc 0 :: (List.range n).map Qubit.data, q.inRange n 2 = true := by
  intro q hq
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hq
  rcases hq with rfl | ⟨i, hi, rfl⟩ <;> simp [Qubit.inRange, *]

theorem anc1_not_mem (n : ℕ) : Qubit.anc 1 ∉ Qubit.anc 0 :: (List.range n).map Qubit.data := by
  simp

/-- Report §6.1.4, KG §5.2 (Stage 13a L1, L2) — `accumulate` over a clean qubit `c`: clean AND
targets, the qubit checks, and the product of the qubits it leaves unmarked is the product of
`us`; those qubits are among `c :: us`, without repetition. -/
theorem accumulate_spec {n m : ℕ} (c : Qubit) (us : List Qubit) (hnd : (c :: us).Nodup)
    (hr : ∀ q ∈ c :: us, q.inRange n m = true) (s : Reg n × Reg m) (hc : c.get s = false) :
    stepsPre (accumulate c us).1 s = true ∧ (accumulate c us).1.all (stepOk n m) = true ∧
      (accumulate c us).2.all (·.get (runSteps (accumulate c us).1 s)) = us.all (·.get s) ∧
      (∀ q ∈ (accumulate c us).2, q ∈ c :: us) ∧ (accumulate c us).2.Nodup := by
  unfold accumulate
  split_ifs with h
  · exact ⟨rfl, rfl, rfl, fun q hq => List.mem_cons_of_mem _ hq, (List.nodup_cons.mp hnd).2⟩
  · obtain ⟨hv, hA⟩ := greedy_spec (c :: us).length (true :: List.replicate us.length false)
    obtain ⟨h1, h2, h3⟩ := array_spec c us hnd hr s hc _ hv
    rw [← hA] at h3
    have hlen : (greedy (c :: us).length (true :: List.replicate us.length false)).2.length =
        (c :: us).length := by
      rw [hA, foldl_applyOp_length]; simp
    exact ⟨h1, h2, h3, fun q hq => mem_unmarkedQubits hlen hq, unmarkedQubits_nodup hnd hlen⟩

/-- Report §6.1.4, KG Theorem 5.1 for every `n` (Stage 13a L1–L3) — **the classical KG fact for
candidate B**: on `Reg n × Reg 2`, every step of `plan n .logDepth` passes the qubit checks, the
qubits of the final phase are in the register and distinct, every AND target is clean when it is
computed from `|x, 0, 0⟩`, and the qubits of the final phase multiply to `x₀ ∧ … ∧ x_{n−1}`. -/
theorem logDepth_classical (n : ℕ) (x : Reg n) :
    (plan n .logDepth).1.all (stepOk n 2) = true ∧
      (plan n .logDepth).2.all (·.inRange n 2) = true ∧ (plan n .logDepth).2.Nodup ∧
      stepsPre (plan n .logDepth).1 ((x, fun _ => false) : Reg n × Reg 2) = true ∧
      phaseBit 2 n .logDepth x = allOnes x := by
  simp only [phaseBit, mid]
  by_cases hn : n ≤ 2
  · have hplan : plan n .logDepth = ([], (List.range n).map Qubit.data) := by
      simp only [plan, ite_eq_left hn]
    rw [hplan]
    refine ⟨rfl, ?_, List.Nodup.map (fun i j h => Qubit.data.inj h) List.nodup_range, rfl,
      data_all x⟩
    simp [Qubit.inRange]
  · have hplan : plan n .logDepth =
        (stepsOf (Qubit.anc 0 :: (List.range n).map Qubit.data)
            (doubling n ++ (greedy (n + 1)
              ((doubling n).foldl applyOp (true :: List.replicate n false))).1) ++
          (accumulate (.anc 1) (unmarkedQubits (Qubit.anc 0 :: (List.range n).map Qubit.data)
            (greedy (n + 1) ((doubling n).foldl applyOp (true :: List.replicate n false))).2)).1,
        (accumulate (.anc 1) (unmarkedQubits (Qubit.anc 0 :: (List.range n).map Qubit.data)
            (greedy (n + 1) ((doubling n).foldl applyOp (true :: List.replicate n false))).2)).2) := by
      simp only [plan, ite_eq_right hn, List.length_cons, List.length_map, List.length_range]
    rw [hplan]
    generalize hG : greedy (n + 1) ((doubling n).foldl applyOp (true :: List.replicate n false)) = G
    obtain ⟨k, hvd, -⟩ := doubling_spec n
    obtain ⟨hvg, hG2⟩ := greedy_spec (n + 1)
      ((doubling n).foldl applyOp (true :: List.replicate n false))
    rw [hG] at hvg hG2
    have hdl : ((List.range n).map Qubit.data).length = n := by simp
    have hv : valid (true :: List.replicate ((List.range n).map Qubit.data).length false)
        (doubling n ++ G.1) = true := by
      rw [hdl, valid_append, hvd, hvg, Bool.and_self]
    obtain ⟨p1, p2, p3⟩ := array_spec (Qubit.anc 0) ((List.range n).map Qubit.data) (qs0_nodup n)
      (qs0_inRange n) ((x, fun _ => false) : Reg n × Reg 2) (by simp [Qubit.get]) _ hv
    have hA₂ : (doubling n ++ G.1).foldl applyOp
        (true :: List.replicate ((List.range n).map Qubit.data).length false) = G.2 := by
      rw [hdl, List.foldl_append, hG2]
    rw [hA₂] at p3
    generalize hs₁ : runSteps (stepsOf (Qubit.anc 0 :: (List.range n).map Qubit.data)
      (doubling n ++ G.1)) ((x, fun _ => false) : Reg n × Reg 2) = s₁ at p3
    have hlen₂ : G.2.length = (Qubit.anc 0 :: (List.range n).map Qubit.data).length := by
      rw [hG2, foldl_applyOp_length, foldl_applyOp_length]; simp
    have hnd₁ : (Qubit.anc 1 :: unmarkedQubits (Qubit.anc 0 :: (List.range n).map Qubit.data)
        G.2).Nodup :=
      List.nodup_cons.mpr ⟨fun h => anc1_not_mem n (mem_unmarkedQubits hlen₂ h),
        unmarkedQubits_nodup (qs0_nodup n) hlen₂⟩
    have hr₁ : ∀ q ∈ Qubit.anc 1 :: unmarkedQubits (Qubit.anc 0 :: (List.range n).map Qubit.data)
        G.2, q.inRange n 2 = true := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact qs0_inRange n q (mem_unmarkedQubits hlen₂ hq)
    have hc₁ : (Qubit.anc 1).get s₁ = false := by
      rw [← hs₁, get_runSteps_not_mem (anc1_not_mem n)]
      · simp [Qubit.get]
      · intro o ho
        have := valid_bounds _ _ hv o ho
        simp only [List.length_cons, List.length_replicate] at this ⊢
        omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := accumulate_spec (Qubit.anc 1) _ hnd₁ hr₁ s₁ hc₁
    refine ⟨?_, ?_, a5, ?_, ?_⟩
    · rw [List.all_append, p2, a2, Bool.and_self]
    · rw [List.all_eq_true]
      intro q hq
      exact hr₁ q (a4 q hq)
    · rw [stepsPre_append, p1, hs₁, a1, Bool.and_self]
    · rw [runSteps_append, hs₁, a3, p3, data_all]

/-! ## L3 — well-formedness and the bit count for every `n` -/

/-- Gates that neither measure nor read a classical bit. -/
def plain : Gate → Bool
  | .measure _ _ | .ifBit _ _ => false
  | _ => true

theorem bitsOkFrom_plain (N : ℕ) : ∀ (W : List ℕ) (gs : List Gate), gs.all plain = true →
    Circuit.bitsOkFrom N W gs = true ∧ Circuit.written gs = []
  | _, [], _ => ⟨rfl, rfl⟩
  | W, g :: gs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := bitsOkFrom_plain N (W ++ g.writes) gs h.2
    have hw : g.writes = [] := by cases g <;> simp_all [plain, Gate.writes]
    have hb : g.bitOk N W = true := by cases g <;> simp_all [plain, Gate.bitOk]
    refine ⟨by rw [Circuit.bitsOkFrom, hb, h1, Bool.and_self], ?_⟩
    rw [Circuit.written, List.flatMap_cons, hw, List.nil_append]
    exact h2

theorem compute_plain (steps : List Step) : (steps.flatMap computeGates).all plain = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨⟨x, y, t, cl⟩, -, hg⟩ := List.mem_flatMap.mp hg
  cases cl <;> simp only [computeGates, rtof, TempLogicalAND, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> rfl

theorem phase_plain (us : List Qubit) : (phase us).all plain = true := by
  unfold phase
  split <;> rfl

theorem nAnd_reverse (l : List Step) : nAnd l.reverse = nAnd l := List.countP_reverse

/-- The uncompute phase measures one fresh bit per AND, numbered in order, and reads it only
after its measurement. -/
theorem uncomputeAll_bits (N : ℕ) : ∀ (l : List Step) (j : ℕ), j + nAnd l ≤ N →
    Circuit.bitsOkFrom N (List.range j) (uncomputeAll j l) = true ∧
      Circuit.written (uncomputeAll j l) = List.range' j (nAnd l)
  | [], _, _ => ⟨rfl, rfl⟩
  | (x, y, t, true) :: l, j, h => by
    have hn : nAnd ((x, y, t, true) :: l) = nAnd l + 1 := by simp [nAnd]
    rw [hn] at h ⊢
    obtain ⟨h1, h2⟩ := uncomputeAll_bits N l (j + 1) (by omega)
    simp only [uncomputeAll, ↓reduceIte]
    rw [bitsOkFrom_append_list, written_append_list, h2]
    have hW : Circuit.written (uncomputeGates j (x, y, t, true)) = [j] := rfl
    rw [hW, ← List.range_succ, h1, Bool.and_true]
    refine ⟨?_, by simp [List.range'_succ]⟩
    simp [uncomputeGates, UncomputeTempLogicalAND, Circuit.bitsOkFrom, Gate.bitOk, Gate.writes,
      Gate.isClifford]
    omega
  | (x, y, t, false) :: l, j, h => by
    have hn : nAnd ((x, y, t, false) :: l) = nAnd l := by simp [nAnd]
    rw [hn] at h ⊢
    obtain ⟨h1, h2⟩ := uncomputeAll_bits N l j h
    simp only [uncomputeAll, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b1, b2⟩ := bitsOkFrom_plain N (List.range j) (uncomputeGates j (x, y, t, false)) rfl
    rw [bitsOkFrom_append_list, written_append_list, b1, b2, List.append_nil, List.nil_append, h1,
      h2, Bool.and_self]
    exact ⟨rfl, rfl⟩

theorem step_qubitsOk {n m : ℕ} {st : Step} (h : stepOk n m st = true) :
    (computeGates st).all (Gate.qubitsOk n) = true ∧
      ∀ j, (uncomputeGates j st).all (Gate.qubitsOk n) = true := by
  obtain ⟨x, y, t, cl⟩ := st
  obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec h
  have := hxy.symm
  have := hxt.symm
  have := hyt.symm
  cases x <;> cases y <;> cases t <;> cases cl <;>
    simp_all [computeGates, uncomputeGates, rtof, TempLogicalAND, UncomputeTempLogicalAND,
      Gate.qubitsOk, Gate.qubits, Qubit.inRange]

theorem uncomputeAll_qubitsOk {n m : ℕ} : ∀ (l : List Step) (j : ℕ), l.all (stepOk n m) = true →
    (uncomputeAll j l).all (Gate.qubitsOk n) = true
  | [], _, _ => rfl
  | st :: l, j, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [uncomputeAll, List.all_append, (step_qubitsOk h.1).2 j, uncomputeAll_qubitsOk l _ h.2,
      Bool.and_self]

theorem phase_qubitsOk {n m : ℕ} {us : List Qubit} (hnd : us.Nodup)
    (hr : us.all (·.inRange n m) = true) : (phase us).all (Gate.qubitsOk n) = true := by
  rcases us with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · rfl
  · cases p <;> simp_all [phase, Gate.qubitsOk, Gate.qubits, Qubit.inRange]
  · have hpq : p ≠ q := by simpa using hnd
    cases p <;> cases q <;> simp_all [phase, Gate.qubitsOk, Gate.qubits, Qubit.inRange]
  · rfl

/-- Report §9.1.1 (Stage 13a L3) — **`mczFew n .logDepth` is well formed and measures one bit per
AND, for every `n`**. -/
theorem mczFew_logDepth_WF {n : ℕ} {C : Circuit} (hC : mczFew n .logDepth = .ok C) :
    C.WF ∧ C.nBits = nAnd (plan n .logDepth).1 := by
  obtain ⟨hCeq, -⟩ := mczFew_ok hC
  obtain ⟨hok, hr, hnd, -, -⟩ := logDepth_classical n (fun _ => false)
  subst hCeq
  generalize (plan n .logDepth).1 = steps at hok ⊢
  generalize (plan n .logDepth).2 = us at hr hnd ⊢
  have hc := bitsOkFrom_plain (nAnd steps) [] (steps.flatMap computeGates ++ phase us)
    (by rw [List.all_append, compute_plain, phase_plain, Bool.and_self])
  have hu := uncomputeAll_bits (nAnd steps) steps.reverse 0 (by rw [nAnd_reverse]; omega)
  have hnb : Circuit.nBits ⟨n, steps.flatMap computeGates ++ phase us ++
      uncomputeAll 0 steps.reverse⟩ = nAnd steps := by
    simp only [Circuit.nBits, written_append_list, hc.2, hu.2, List.nil_append,
      List.length_range', nAnd_reverse]
  refine ⟨?_, hnb⟩
  unfold Circuit.WF Circuit.wf Circuit.bitsOk
  rw [hnb, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, phase_qubitsOk hnd hr⟩, uncomputeAll_qubitsOk _ _ (by
      rw [List.all_reverse]; exact hok)⟩
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨st, hst, hg⟩ := List.mem_flatMap.mp hg
    exact List.all_eq_true.mp (step_qubitsOk (List.all_eq_true.mp hok st hst)).1 g hg
  · rw [bitsOkFrom_append_list, hc.1, hc.2, List.nil_append, Bool.true_and]
    exact hu.1

/-! ## L4 — the greedy schedule from `1 0^k` ends with two unmarked indices (KG §5.2)

From `1 0^k` (`k ≥ 3`) the greedy run passes through two families of arrays only:
`F(j, r) = 0 (10)^j 1 1 0^r` (the forward chain `(2j + 2, 2j + 3, 2j + 4)`) and
`B(j, r) = 0 (10)^j 0 1^r` (the backward chain `(2j − 1, 2j, 2j + 1)`); the turn from `F` to `B`
is `(2j − 1, 2j, 2j + 3)` at `F(j, 1)` and `(2j − 3, 2j − 2, 2j)` at `F(j, 0)`. It stops at
`B(0, r)`, `F(0, 1)` or `F(1, 0)`, each with exactly two unmarked indices. The invariant that
rules out three or more unmarked indices with no valid operation is this shape. -/

theorem find?_range_reverse (p : ℕ → Bool) {t : ℕ} (hp : p t = true)
    (hmax : ∀ t', t < t' → p t' = true → False) :
    ∀ L, t < L → (List.range L).reverse.find? p = some t
  | 0, h => absurd h (by omega)
  | L + 1, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    by_cases hL : t = L
    · subst hL; simp only [hp]
    · have hpL : p L = false := by
        cases h' : p L
        · rfl
        · exact absurd (hmax L (by omega) h') id
      simp only [hpL]
      exact find?_range_reverse p hp hmax L (by omega)

theorem filter_range_two (q : ℕ → Bool) {L x y : ℕ} (hxy : x < y) (hyL : y < L)
    (hx : q x = true) (hy : q y = true) (h1 : ∀ i < x, q i = false)
    (h2 : ∀ i, x < i → i < y → q i = false) :
    ∃ rest, (List.range L).filter q = x :: y :: rest := by
  have e1 : List.range L = List.range x ++ List.range' x (L - x) := by
    conv_lhs => rw [show L = x + (L - x) by omega]
    rw [List.range_add, ← List.range'_eq_map_range]
  have e2 : ∀ s n, 0 < n → List.range' s n = s :: List.range' (s + 1) (n - 1) := by
    intro s n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [List.range'_succ]
  have e3 : List.range' (x + 1) (L - x - 1) =
      List.range' (x + 1) (y - x - 1) ++ List.range' y (L - y) := by
    have := @List.range'_append (x + 1) (y - x - 1) (L - y) 1
    rw [show x + 1 + 1 * (y - x - 1) = y by omega, show y - x - 1 + (L - y) = L - x - 1 by omega]
      at this
    exact this.symm
  refine ⟨(List.range' (y + 1) (L - y - 1)).filter q, ?_⟩
  rw [e1, e2 x (L - x) (by omega), e3, e2 y (L - y) (by omega), List.filter_append,
    List.filter_eq_nil_iff.mpr (fun i hi => by rw [h1 i (List.mem_range.mp hi)]; decide),
    List.nil_append, List.filter_cons_of_pos hx, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun i hi => by
      rw [List.mem_range'_1] at hi; rw [h2 i (by omega) (by omega)]; decide),
    List.nil_append, List.filter_cons_of_pos hy]

/-- No marked index has two unmarked indices above it. -/
def Stuck (A : List Bool) : Prop :=
  ∀ t' i j, t' < i → i < j → j < A.length → mk A t' = true → mk A i = false → mk A j = false →
    False

theorem not_two_above {A : List Bool} {t' : ℕ} (hS : ∀ i j, t' < i → i < j → j < A.length →
    mk A i = false → mk A j = false → False) : ¬ (unmarkedAbove A t').length ≥ 2 := by
  intro hl
  have hpw : (unmarkedAbove A t').Pairwise (· < ·) := List.pairwise_lt_range.filter _
  rcases hu : unmarkedAbove A t' with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [hu] at hl; simp at hl
  · rw [hu] at hl; simp at hl
  · rw [hu] at hpw
    have hab : a < b := (List.pairwise_cons.mp hpw).1 b (by simp)
    have ha : a ∈ unmarkedAbove A t' := by rw [hu]; simp
    have hb : b ∈ unmarkedAbove A t' := by rw [hu]; simp
    simp only [unmarkedAbove, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true'] at ha hb
    exact hS a b ha.2.1 hab hb.1 (by rw [← mk_of_lt ha.1 true]; exact ha.2.2)
      (by rw [← mk_of_lt hb.1 true]; exact hb.2.2)

/-- KG §5.2 — the greedy choice, characterized: the marked `t` with no marked index above it
that has two unmarked indices above it, and the first two unmarked indices `x < y` above `t`. -/
theorem greedyStep_eq_some {A : List Bool} {t x y : ℕ} (htx : t < x) (hxy : x < y)
    (hyL : y < A.length) (hMt : mk A t = true) (hMx : mk A x = false) (hMy : mk A y = false)
    (h1 : ∀ i, t < i → i < x → mk A i = true) (h2 : ∀ i, x < i → i < y → mk A i = true)
    (hno : ∀ t' i j, t < t' → t' < i → i < j → j < A.length → mk A t' = true →
      mk A i = false → mk A j = false → False) :
    greedyStep A = some (t, x, y) := by
  obtain ⟨rest, hu⟩ := filter_range_two (L := A.length)
    (fun i => decide (t < i) && !A.getD i true) hxy hyL
    (by rw [mk_of_lt (show x < A.length by omega), hMx]; simp [htx])
    (by rw [mk_of_lt hyL, hMy]; simp [htx.trans hxy])
    (fun i hi => by
      by_cases hti : t < i
      · rw [mk_of_lt (show i < A.length by omega), h1 i hti hi]; simp
      · simp [hti])
    (fun i hxi hiy => by
      rw [mk_of_lt (show i < A.length by omega), h2 i hxi hiy]; simp)
  have hu' : unmarkedAbove A t = x :: y :: rest := hu
  have hfind : (List.range A.length).reverse.find?
      (fun t => A.getD t false && decide ((unmarkedAbove A t).length ≥ 2)) = some t := by
    refine find?_range_reverse _ ?_ (fun t' htt' hp => ?_) _ (by omega)
    · rw [mk_of_lt (show t < A.length by omega), hMt, hu']; simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      have ht'L : t' < A.length := by
        by_contra h; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hp
        exact absurd hp.1 (by decide)
      rw [mk_of_lt ht'L] at hp
      exact not_two_above (fun i j h3 h4 h5 h6 h7 => hno t' i j htt' h3 h4 h5 hp.1 h6 h7) hp.2
  simp only [greedyStep, Option.bind_eq_bind, hfind, Option.bind_some, hu']

theorem greedyStep_eq_none {A : List Bool} (hS : Stuck A) : greedyStep A = none := by
  have hfind : (List.range A.length).reverse.find?
      (fun t => A.getD t false && decide ((unmarkedAbove A t).length ≥ 2)) = none := by
    rw [List.find?_eq_none]
    intro t' ht' hp
    simp only [List.mem_reverse, List.mem_range] at ht'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [mk_of_lt ht'] at hp
    exact not_two_above (fun i j h3 h4 h5 h6 h7 => hS t' i j h3 h4 h5 hp.1 h6 h7) hp.2
  simp only [greedyStep, Option.bind_eq_bind, hfind, Option.bind_none]

theorem greedy_of_none {A : List Bool} (h : greedyStep A = none) (f : ℕ) : (greedy f A).2 = A := by
  cases f <;> simp [greedy, h]

theorem greedy_of_some {A : List Bool} {o : Op} (h : greedyStep A = some o) (f : ℕ) :
    (greedy (f + 1) A).2 = (greedy f (applyOp A o)).2 := by
  simp [greedy, h]

/-- An array given by its marks. -/
def arr (L : ℕ) (g : ℕ → Bool) : List Bool := (List.range L).map g

theorem arr_length (L : ℕ) (g : ℕ → Bool) : (arr L g).length = L := by simp [arr]

theorem mk_arr (L : ℕ) (g : ℕ → Bool) (i : ℕ) : mk (arr L g) i = (decide (i < L) && g i) := by
  by_cases h : i < L
  · rw [mk, getD_lt (by rw [arr_length]; exact h)]; simp [arr, h]
  · rw [mk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [arr_length]; omega)]
    simp [h]

theorem list_eq_of_mk {A B : List Bool} (hl : A.length = B.length) (h : ∀ i, mk A i = mk B i) :
    A = B := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  rwa [mk, mk, getD_lt h1, getD_lt h2] at this

theorem applyOp_arr {L t x y : ℕ} {g g' : ℕ → Bool} (ht : t < L) (hx : x < L) (hy : y < L)
    (hgg : ∀ i < L, applyF g (t, x, y) i = g' i) : applyOp (arr L g) (t, x, y) = arr L g' := by
  apply list_eq_of_mk (by rw [applyOp_length, arr_length, arr_length])
  intro i
  rw [mk_applyOp (by rw [arr_length]; exact ht) (by rw [arr_length]; exact hx)
    (by rw [arr_length]; exact hy), mk_arr]
  by_cases hi : i < L
  · rw [← hgg i hi, applyF_apply, applyF_apply, mk_arr]
    simp [hi]
  · rw [applyF_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      mk_arr]
    simp [hi]

/-- `F(j, ·) = 0 (10)^j 1 1 0…`. -/
def fF (j i : ℕ) : Bool := decide ((i % 2 = 1 ∧ i < 2 * j) ∨ i = 2 * j + 1 ∨ i = 2 * j + 2)

/-- `B(j, ·) = 0 (10)^j 0 1…`. -/
def fB (j i : ℕ) : Bool := decide ((i % 2 = 1 ∧ i < 2 * j) ∨ 2 * j + 2 ≤ i)

/-- Exactly two unmarked indices. -/
def Two (A : List Bool) : Prop :=
  ((List.range A.length).filter (fun i => !A.getD i true)).length = 2

theorem two_B0 (r : ℕ) : Two (arr (2 * 0 + 2 + r) (fB 0)) := by
  unfold Two
  rw [arr_length, List.filter_congr (q := fun i => !fB 0 i) (fun i hi => by
    rw [mk_of_lt (by rw [arr_length]; exact List.mem_range.mp hi), mk_arr,
      decide_eq_true (List.mem_range.mp hi), Bool.true_and])]
  rw [show 2 * 0 + 2 + r = 2 + r by ring, List.range_add, List.filter_append,
    (List.filter_eq_nil_iff (l := List.map (fun x => 2 + x) (List.range r))).mpr (fun i hi => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hi; simp [fB])]
  rfl

theorem greedy_B : ∀ j r f, j ≤ f → Two (greedy f (arr (2 * j + 2 + r) (fB j))).2
  | 0, r, f, _ => by
    rw [greedy_of_none (greedyStep_eq_none fun t' i j h1 h2 h3 h4 h5 h6 => by
      simp only [mk_arr, fB, arr_length, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at h3 h4 h5 h6
      omega)]
    exact two_B0 r
  | j + 1, r, f + 1, hf => by
    have hL : 2 * (j + 1) + 2 + r = 2 * j + 2 + (r + 2) := by ring
    rw [greedy_of_some (o := (2 * j + 1, 2 * j + 2, 2 * j + 3)), hL,
      applyOp_arr (g' := fB j) (by omega) (by omega) (by omega) (fun i hi => by
        rw [applyF_apply]; simp only [fB]; split_ifs <;>
          first | (simp only [decide_eq_decide]; omega) | (simp; omega))]
    · exact greedy_B j (r + 2) f (by omega)
    · apply greedyStep_eq_some (by omega) (by omega) <;>
        simp only [mk_arr, fB, arr_length, Bool.and_eq_true, decide_eq_true_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not] <;> omega

theorem two_F01 : Two (arr (2 * 0 + 3 + 1) (fF 0)) := by unfold Two; decide

theorem two_F10 : Two (arr (2 * 1 + 3 + 0) (fF 1)) := by unfold Two; decide

/-- KG §5.2 (Stage 13a L4) — from `F(j, r)` (not `F(0, 0)`), with enough fuel, greedy ends with
exactly two unmarked indices. -/
theorem greedy_F : ∀ r j f, j + r ≤ f → (j ≠ 0 ∨ r ≠ 0) →
    Two (greedy f (arr (2 * j + 3 + r) (fF j))).2
  | 0, 0, _, _, h => by simp at h
  | 0, 1, f, _, _ => by
    rw [greedy_of_none (by decide)]
    exact two_F10
  | 0, j + 2, f + 1, hf, _ => by
    have hL : 2 * (j + 2) + 3 + 0 = 2 * j + 2 + 5 := by ring
    rw [greedy_of_some (o := (2 * j + 1, 2 * j + 2, 2 * j + 4)), hL,
      applyOp_arr (g' := fB j) (by omega) (by omega) (by omega) (fun i hi => by
        rw [applyF_apply]; simp only [fF, fB]; split_ifs <;>
          first | (simp only [decide_eq_decide]; omega) | (simp; omega))]
    · exact greedy_B j 5 f (by omega)
    · apply greedyStep_eq_some (by omega) (by omega) <;>
        simp only [mk_arr, fF, arr_length, Bool.and_eq_true, decide_eq_true_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not] <;> omega
  | 1, 0, f, _, _ => by
    rw [greedy_of_none (by decide)]
    exact two_F01
  | 1, j + 1, f + 1, hf, _ => by
    have hL : 2 * (j + 1) + 3 + 1 = 2 * j + 2 + 4 := by ring
    rw [greedy_of_some (o := (2 * j + 1, 2 * j + 2, 2 * j + 5)), hL,
      applyOp_arr (g' := fB j) (by omega) (by omega) (by omega) (fun i hi => by
        rw [applyF_apply]; simp only [fF, fB]; split_ifs <;>
          first | (simp only [decide_eq_decide]; omega) | (simp; omega))]
    · exact greedy_B j 4 f (by omega)
    · apply greedyStep_eq_some (by omega) (by omega) <;>
        simp only [mk_arr, fF, arr_length, Bool.and_eq_true, decide_eq_true_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not] <;> omega
  | r + 2, j, f + 1, hf, _ => by
    have hL : 2 * j + 3 + (r + 2) = 2 * j + 2 + 3 + r := by ring
    rw [greedy_of_some (o := (2 * j + 2, 2 * j + 3, 2 * j + 4)), hL,
      applyOp_arr (g' := fF (j + 1)) (by omega) (by omega) (by omega) (fun i hi => by
        rw [applyF_apply]; simp only [fF]; split_ifs <;>
          first | (simp only [decide_eq_decide]; omega) | (simp; omega)),
      show 2 * j + 2 + 3 + r = 2 * (j + 1) + 3 + r by ring]
    · exact greedy_F r (j + 1) f (by omega) (Or.inl (by omega))
    · apply greedyStep_eq_some (by omega) (by omega) <;>
        simp only [mk_arr, fF, arr_length, Bool.and_eq_true, decide_eq_true_eq,
          Bool.and_eq_false_iff, decide_eq_false_iff_not, and_true, or_true] <;> omega
  | 0, _ + 2, 0, hf, _ => by omega
  | 1, _ + 1, 0, hf, _ => by omega
  | _ + 2, _, 0, hf, _ => by omega

/-- Report §6.1.4, KG §5.2 (Stage 13a L4) — **greedy from `1 0^k`, `k ≥ 3`, ends with exactly two
unmarked indices** (`k + 1` operations of fuel suffice; it uses `k − 2`). -/
theorem greedy_init_two {k : ℕ} (hk : 3 ≤ k) :
    Two (greedy (k + 1) (true :: List.replicate k false)).2 := by
  have hA : true :: List.replicate k false = arr (k + 1) (fun i => decide (i = 0)) := by
    apply list_eq_of_mk (by simp [arr_length])
    intro i
    rw [mk_init, mk_arr]
    by_cases h : i = 0 <;> simp [h]
  rw [hA, greedy_of_some (o := (0, 1, 2)),
    applyOp_arr (g' := fF 0) (by omega) (by omega) (by omega) (fun i hi => by
      rw [applyF_apply]; simp only [fF]; split_ifs <;>
          first | (simp only [decide_eq_decide]; omega) | (simp; omega)),
    show k + 1 = 2 * 0 + 3 + (k - 2) by omega]
  · exact greedy_F (k - 2) 0 k (by omega) (Or.inr (by omega))
  · apply greedyStep_eq_some (by omega) (by omega) <;>
      simp only [mk_arr, arr_length, Bool.and_eq_true, decide_eq_true_eq,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, and_true] <;> omega

/-- A valid list of operations keeps an unmarked index (the last operation unmarks its target). -/
theorem exists_unmarked : ∀ (ops : List Op) (A : List Bool), valid A ops = true →
    (∃ i < A.length, mk A i = false) → ∃ i < A.length, mk (ops.foldl applyOp A) i = false
  | [], _, _, h => h
  | ⟨t, x, y⟩ :: ops, A, hv, _ => by
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨htx, hxy, hyL, -⟩ := validOp_spec hv.1
    simp only at htx hxy hyL
    have := exists_unmarked ops (applyOp A (t, x, y)) hv.2 ⟨t, by rw [applyOp_length]; omega, by
      rw [mk_applyOp (by simp only; omega) (by simp only; omega) hyL, applyF_apply,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]⟩
    rwa [applyOp_length] at this

theorem accumulate_length (c : Qubit) (us : List Qubit) (h : us ≠ []) :
    (accumulate c us).2.length = 1 ∨ (accumulate c us).2.length = 2 := by
  unfold accumulate
  split_ifs with hk
  · have := List.length_pos_of_ne_nil h
    simp only; omega
  · right
    simp only [unmarkedQubits, List.length_map, List.length_cons]
    have := greedy_init_two (k := us.length) (by omega)
    exact this

/-- Report §6.1.4 (Stage 13a L4) — `plan n .logDepth` leaves one or two qubits for the final
phase, for every `n ≥ 1`. -/
theorem plan_length {n : ℕ} (hn : n ≠ 0) :
    (plan n .logDepth).2.length = 1 ∨ (plan n .logDepth).2.length = 2 := by
  by_cases h2 : n ≤ 2
  · simp only [plan, ite_eq_left h2, List.length_map, List.length_range]
    omega
  · simp only [plan, ite_eq_right h2, List.length_cons, List.length_map, List.length_range]
    apply accumulate_length
    obtain ⟨k, hvd, -⟩ := doubling_spec n
    obtain ⟨hvg, hG2⟩ := greedy_spec (n + 1)
      ((doubling n).foldl applyOp (true :: List.replicate n false))
    have hv : valid (true :: List.replicate n false) (doubling n ++
        (greedy (n + 1) ((doubling n).foldl applyOp (true :: List.replicate n false))).1) = true := by
      rw [valid_append, hvd, hvg, Bool.and_self]
    obtain ⟨i, hi, hmi⟩ := exists_unmarked _ _ hv ⟨1, by simp; omega, by
      rw [mk_init]; simp⟩
    rw [List.foldl_append, ← hG2] at hmi
    intro he
    have hmem : (Qubit.anc 0 :: (List.range n).map Qubit.data).getD i default ∈
        unmarkedQubits (Qubit.anc 0 :: (List.range n).map Qubit.data)
          (greedy (n + 1) ((doubling n).foldl applyOp (true :: List.replicate n false))).2 := by
      have hlen : (greedy (n + 1) ((doubling n).foldl applyOp
          (true :: List.replicate n false))).2.length = n + 1 := by
        rw [hG2, foldl_applyOp_length, foldl_applyOp_length]; simp
      simp only [unmarkedQubits, List.mem_map, List.mem_filter, List.mem_range]
      refine ⟨i, ⟨by rw [hlen]; simpa using hi, ?_⟩, rfl⟩
      rw [mk_of_lt (by rw [hlen]; simpa using hi), hmi]; rfl
    rw [he] at hmem
    simp at hmem

end KG

open KG

/-! ## The targets -/

/-- Report §6.2.1, §6.3.2, §8.2, §9.5.2, KG 2025 Theorem 5.1 (Stage 13a) —
**`mczFew_logDepth_ancRestore`**: for every `n`, the few-ancilla MCZ candidate B restores its two
clean ancillae and applies the phase oracle of `P_all = x₀ ∧ … ∧ x_{n−1}`, on density operators.
No per-instance hypothesis: `mczFew_ancRestore_of_classical` (Stage 12d) with `C.WF`, the bit
count and the classical KG fact proved for every `n` (`mczFew_logDepth_WF`,
`logDepth_classical`). -/
theorem mczFew_logDepth_ancRestore {n : ℕ} {C : Circuit} (hC : mczFew n .logDepth = .ok C) :
    AncRestore n 2 C (phaseOracle allOnes) := by
  obtain ⟨hWF, hnb⟩ := mczFew_logDepth_WF hC
  obtain ⟨hok, hus, -, -, -⟩ := logDepth_classical n (fun _ => false)
  exact mczFew_ancRestore_of_classical hC hWF hnb hok hus
    (fun x => ⟨(logDepth_classical n x).2.2.2.1, (logDepth_classical n x).2.2.2.2⟩) le_rfl

theorem inRange_min {n a b : ℕ} {q : Qubit} (h1 : q.inRange n a = true)
    (h2 : q.inRange n b = true) : q.inRange n (min a b) = true := by
  cases q <;> simp_all [Qubit.inRange]

theorem cnot_mem_computeGates (x y t : Qubit) (cl : Bool) :
    Gate.cnot x t ∈ computeGates (x, y, t, cl) ∧ Gate.cnot y t ∈ computeGates (x, y, t, cl) := by
  cases cl <;> simp [computeGates, TempLogicalAND, rtof]

/-- Report §8.2, §6.2.4, §9.5.2 (Stage 13a) — **`diffusionFew_logDepth_ancRestore`**: for every
`n`, the diffusion `H X · MCZ · X H` with candidate B restores its ancillae and applies
`U_s = 2|s⟩⟨s| − I` on every register `a ≥ D.nAnc` (`diffusionFew_ancRestore_of_classical` at
`a₀ = min C.nAnc 2`: the register-2 facts of `logDepth_classical`, moved down by `agree_runSteps`,
the qubits in range of `C.nAnc` by `Circuit.WF.gatesOk`). -/
theorem diffusionFew_logDepth_ancRestore {n : ℕ} {D : Circuit}
    (hD : diffusionFew n .logDepth = .ok D) : ∀ a, D.nAnc ≤ a → AncRestore n a D (diffU n) := by
  cases hC : mczFew n .logDepth with
  | error e =>
    simp [diffusionFew, hC, bind, Except.bind] at hD
  | ok C =>
    obtain ⟨hWF, hnb⟩ := mczFew_logDepth_WF hC
    obtain ⟨hok, hus, -, -, -⟩ := logDepth_classical n (fun _ => false)
    obtain ⟨hCeq, hlen⟩ := mczFew_ok hC
    have hgk := hWF.gatesOk
    have hnD : C.nData = n := by rw [hCeq]
    rw [hnD] at hgk
    have hgates : C.gates = (plan n .logDepth).1.flatMap computeGates ++ phase (plan n .logDepth).2 ++
        uncomputeAll 0 (plan n .logDepth).1.reverse := by rw [hCeq]
    have hok₀ : (plan n .logDepth).1.all (stepOk n (min C.nAnc 2)) = true := by
      rw [List.all_eq_true]
      intro st hst
      obtain ⟨x, y, t, cl⟩ := st
      have h2 := List.all_eq_true.mp hok _ hst
      obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec h2
      obtain ⟨m1, m2⟩ := cnot_mem_computeGates x y t cl
      have g1 : Gate.cnot x t ∈ C.gates := by
        rw [hgates]; simp only [List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl ⟨_, hst, m1⟩)
      have g2 : Gate.cnot y t ∈ C.gates := by
        rw [hgates]; simp only [List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inl ⟨_, hst, m2⟩)
      have rx := (hgk _ g1).1 x (by simp [Gate.qubits])
      have rt := (hgk _ g1).1 t (by simp [Gate.qubits])
      have ry := (hgk _ g2).1 y (by simp [Gate.qubits])
      simp [stepOk, inRange_min rx hx, inRange_min ry hy, inRange_min rt ht, hxy, hxt, hyt]
    have hus₀ : (plan n .logDepth).2.all (·.inRange n (min C.nAnc 2)) = true := by
      rw [List.all_eq_true]
      intro q hq
      have h2 := List.all_eq_true.mp hus q hq
      have hgq : ∃ g ∈ phase (plan n .logDepth).2, q ∈ g.qubits := by
        generalize (plan n .logDepth).2 = us at hq hlen
        rcases us with _ | ⟨p, _ | ⟨p', _ | ⟨r, l⟩⟩⟩
        · simp at hq
        · simp only [List.mem_singleton] at hq; subst hq
          exact ⟨_, List.mem_singleton_self _, by simp [Gate.qubits]⟩
        · exact ⟨_, List.mem_singleton_self _, by simpa [Gate.qubits] using hq⟩
        · simp at hlen
      obtain ⟨g, hg, hqg⟩ := hgq
      have hgC : g ∈ C.gates := by
        rw [hgates]; simp only [List.mem_append]; exact Or.inl (Or.inr hg)
      exact inRange_min ((hgk g hgC).1 q hqg) h2
    have hcl₀ : ∀ x : Reg n,
        stepsPre (plan n .logDepth).1 ((x, fun _ => false) : Reg n × Reg (min C.nAnc 2)) = true ∧
          phaseBit (min C.nAnc 2) n .logDepth x = allOnes x := by
      intro x
      obtain ⟨-, -, -, hp, hb⟩ := logDepth_classical n x
      obtain ⟨h1, h2⟩ := agree_runSteps (min_le_right C.nAnc 2) (plan n .logDepth).1 _ _ hok₀
        (agree_init x)
      refine ⟨by rw [h1]; exact hp, ?_⟩
      rw [← hb]
      simp only [phaseBit, mid]
      exact all_get_congr hus₀ h2
    exact diffusionFew_ancRestore_of_classical hC hWF hnb hok₀ hus₀ hcl₀ (min_le_left _ _) hD

/-- Report §6.1.4, §3.1.4 (Stage 13a L4) — **`mczFew_logDepth_ok`**: candidate B is synthesized for
every `n ≥ 1` (one or two qubits are left for the final phase, `plan_length`). -/
theorem mczFew_logDepth_ok {n : ℕ} (hn : n ≠ 0) : ∃ C, mczFew n .logDepth = .ok C := by
  have hlen := plan_length hn
  unfold mczFew
  rcases hp : plan n .logDepth with ⟨steps, us⟩
  rw [hp] at hlen
  have h0 : (n == 0) = false := by simpa using hn
  have h1 : (us.length == 0 || decide (us.length > 2)) = false := by
    rcases hlen with h | h <;> simp [h]
  simp [h0, h1, pure, Except.pure]

end CQRV.Grover

end
