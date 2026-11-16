module

public import CQRV.Grover.Restore
public import CQRV.Synthesis.MczFew
public import CQRV.Synthesis.MczFewK

/-!
# CQRV.Grover.MczFew

Report §6.2 (restoration is a co-equal obligation), §6.2.4 (Layers 1–3), §6.3.2, §8.2, §9.5.2 —
Stage 12c: the restoration proof of the few-ancilla MCZ of Stage 12b, candidate B
(`mczFew n .logDepth`: Khattar–Gidney 2025 §5.3 schedule, Maslov 2016 relative-phase Toffoli
pairs), **for n = 8**, and the diffusion around it (DECISIONS.md 2026-10-26, Stage 12c). The
definitions of `CQRV.Synthesis.MczFew` are not changed; `cqr certify` does not use them (12d).

Basis-vector route of Stages 6b-2 / 6b-3: every gate maps a basis vector to a phase times a basis
vector, except the MBU branches (`(√2)⁻¹` times a basis vector).

1. `rtof_basis` — `rtof a b t` maps `|s⟩` to `D(a, b, t') · |s[t ↦ t']⟩`, `t' = t ⊕ (a ∧ b)`,
   `D = diag(1, 1, 1, 1, 1, −1, −i, i)` indexed by `4a + 2b + t'` (`rtofPhase`; the order of
   `tests/diff/mcz_diff.py` (0), qubit `a` the most significant).
2. `rtofPhase_pair`, `rtof_pair_kraus` — a compute `rtof; X t` and its uncompute `X t; rtof`
   around any block that is diagonal on the intermediate basis state cancel exactly, for every
   value of the target: no "conditionally clean" hypothesis is needed.
3. `steps_kraus`, `mczFew_kraus_basis` — the inductive restoration claim: in every branch, the
   Kraus operator of `mczFew n v` maps `|x, 0…0⟩` to `(√2)⁻¹^{#AND} (−1)^{phaseBit x} |x, 0…0⟩`,
   given the per-step qubit checks and that every AND target is clean when it is computed.
4. `mczFew_logDepth_8_classical` — KG correctness for n = 8: `phaseBit x = x₀ ∧ … ∧ x₇` (and the
   clean-target precondition), by `decide +kernel` over the 256 inputs; the same for `ladder`.
5. `mczFew_ancRestore_8`, `diffusionFew_ancRestore_8` — `AncRestore` by `ancRestore_of_kraus`.
6. `mczFew8_WF`, `diffusionFew8_WF` — well-formedness by `decide +kernel`.

The kernel cannot unfold `List.mergeSort` (its body is not exposed to importing modules), which
`MczFew.substeps` uses; `substeps_eq` proves it equal to a copy with an exposed insertion sort
(`sortNat`, equal to `mergeSort` by `List.mergeSort_eq_insertionSort`), so that
`plan 8 .logDepth` can be evaluated by the kernel.
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis CQRV.Synthesis.MczFew Matrix

/-! ## A kernel-evaluable form of the schedule

Stage 30a (A1): the single definition is `CQRV.Synthesis.FewScheduleK` (Physlib-free, in `Synthesis`,
so that `Synthesis.Problem1` shares it without importing `Grover`); the Stage 12c names below are kept
as its aliases. -/

namespace FewSchedule

/-- Insert into a sorted list of naturals (exposed, kernel-evaluable): `FewScheduleK.insNat`. -/
abbrev insNat := FewScheduleK.insNat

/-- Insertion sort on naturals (exposed, kernel-evaluable): `FewScheduleK.sortNat`. -/
abbrev sortNat := FewScheduleK.sortNat

theorem insNat_eq (a : ℕ) (l : List ℕ) : insNat a l = l.orderedInsert (· ≤ ·) a :=
  FewScheduleK.insNat_eq a l

/-- `sortNat` is `List.mergeSort` on `ℕ` with `≤`. -/
theorem sortNat_eq (l : List ℕ) : l.mergeSort (fun a b => decide (a ≤ b)) = sortNat l :=
  FewScheduleK.sortNat_eq l

/-- `MczFew.substeps` with `sortNat` for `mergeSort`: `FewScheduleK.substepsK`. -/
abbrev substepsK := FewScheduleK.substepsK

theorem substeps_eq : ∀ f P Q, substeps f P Q = substepsK f P Q := FewScheduleK.substeps_eq

theorem doubling_eq (n : ℕ) : doubling n =
    ((List.range n).filter fun i => i + 2 ^ (i + 1) ≤ n).flatMap fun i =>
      substepsK i ((List.range (2 ^ i)).map (i + ·))
        ((List.range (2 ^ i + 1)).map (i + 2 ^ i + ·)) :=
  FewScheduleK.doubling_eq n

end FewSchedule

/-- Report §6.1.4 (Stage 12b) — the compute steps of `mczFew 8 .logDepth`: AND on `anc[0]`, four
relative-phase Toffolis on conditionally clean data qubits, AND on `anc[1]`. -/
def steps8 : List Step :=
  [(.data 0, .data 1, .anc 0, true), (.data 3, .data 4, .data 1, false),
   (.data 1, .data 2, .data 0, false), (.data 5, .data 6, .data 4, false),
   (.data 4, .data 7, .data 3, false), (.anc 0, .data 0, .anc 1, true)]

/-- The qubits of the final `CZ` of `mczFew 8 .logDepth`. -/
def us8 : List Qubit := [.anc 1, .data 3]

/-- Report §6.1.4 — the schedule of `mczFew 8 .logDepth`, evaluated by the kernel. -/
theorem plan_8_logDepth : plan 8 .logDepth = (steps8, us8) := by
  simp only [plan, FewSchedule.doubling_eq]
  decide +kernel

/-- Report §6.1.4 — the circuit `mczFew 8 .logDepth` (compute steps, `CZ`, uncompute steps). -/
def mczFew8 : Circuit :=
  ⟨8, steps8.flatMap computeGates ++ phase us8 ++ uncomputeAll 0 steps8.reverse⟩

theorem mczFew_8_ok : mczFew 8 .logDepth = .ok mczFew8 := by
  simp only [mczFew, plan_8_logDepth]
  rfl

/-- Report §9.1.1 (Stage 12c item 6) — `mczFew 8 .logDepth` is well formed. -/
theorem mczFew8_WF : mczFew8.WF := by decide +kernel

theorem mczFew8_nBits : mczFew8.nBits = 2 := by decide +kernel

noncomputable section

/-! ## Item 1 — the relative-phase Toffoli on basis vectors -/

/-- Report §6.1.4 (Maslov 2016 §B) — the diagonal `D = diag(1, 1, 1, 1, 1, −1, −i, i)` of
`rtof = D · Toffoli`, indexed by `(a, b, t')` = `4a + 2b + t'` with `t'` the target **after** the
Toffoli (the order of `tests/diff/mcz_diff.py` (0): qubit `a` most significant). -/
def rtofPhase : Bool → Bool → Bool → ℂ
  | true, false, true => -1
  | true, true, false => -Complex.I
  | true, true, true => Complex.I
  | _, _, _ => 1

/-- Report §6.1.4, §6.2.4 Layer 1 (Stage 12c item 1) — the unitary of `rtof a b t` on a basis
vector: `|s⟩ ↦ D(a, b, t') |s[t ↦ t']⟩`, `t' = s t ⊕ (s a ∧ s b)`. Proof: gate by gate on the
3-qubit slice of `s` (as `tempLogicalAND_correct_lift`), for the 8 values of `(a, b, t)`. -/
theorem rtof_unitary_basis {n m : ℕ} (a b t : Qubit) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ha : a.inRange n m = true) (hb : b.inRange n m = true)
    (ht : t.inRange n m = true) (s : Reg n × Reg m) :
    unitaryDenote n m (rtof a b t) *ᵥ basisVec s =
      rtofPhase (a.get s) (b.get s) (t.get s ^^ (a.get s && b.get s)) •
        basisVec (t.set (t.get s ^^ (a.get s && b.get s)) s) := by
  have hin : s = Qubit.slice a b t s (a.get s) (b.get s) (t.get s) := by
    rw [Qubit.slice, Qubit.set_get, Qubit.set_get, Qubit.set_get]
  have hout : ∀ z, t.set z s = Qubit.slice a b t s (a.get s) (b.get s) z := by
    intro z
    rw [Qubit.slice, Qubit.set_get, Qubit.set_get]
  rw [hout]
  conv_lhs => rw [hin]
  generalize a.get s = x
  generalize b.get s = y
  generalize t.get s = z
  have ne := Qubit.slice_t_ne (a := a) (b := b) ht s x y
  have ne' := ne.symm
  funext i
  by_cases h0 : i = Qubit.slice a b t s x y false <;>
    by_cases h1 : i = Qubit.slice a b t s x y true
  · exact absurd (h0.symm.trans h1) ne
  all_goals
  cases x <;> cases y <;> cases z <;>
    simp only [rtof, rtofPhase, unitaryDenote_cons_mulVec, unitaryDenote_nil, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul, h_basis n m ht, t_basis, tdg_basis,
      cnot_basis n m hat, cnot_basis n m hbt, cnotPerm,
      Qubit.get_slice_a hab hat ha, Qubit.get_slice_b hbt hb, Qubit.get_slice_t ht,
      Qubit.flip_slice_t ht,
      Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.xor_true,
      Bool.xor_false, ↓reduceIte,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec, h0, h1, ne, ne', Bool.false_eq_true,
      mul_one, mul_zero, add_zero, one_mul, star_ω, ← ω_sq] <;>
    ring_nf <;>
    simp only [invSqrtTwo_sq, ω_pow_four, ω_pow_six, ω_pow_eight] <;>
    ring_nf

/-- Report §6.1.4, §6.2.4 Layer 1 (Stage 12c item 1) — `rtof_basis`: the relative-phase Toffoli in
any branch of the Kraus semantics (it is measurement-free). -/
theorem rtof_basis {n m : ℕ} (nb : ℕ) (c : Fin nb → Bool) (a b t : Qubit) (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ha : a.inRange n m = true) (hb : b.inRange n m = true)
    (ht : t.inRange n m = true) (s : Reg n × Reg m) :
    krausOps n m nb (rtof a b t) c *ᵥ basisVec s =
      rtofPhase (a.get s) (b.get s) (t.get s ^^ (a.get s && b.get s)) •
        basisVec (t.set (t.get s ^^ (a.get s && b.get s)) s) := by
  rw [krausOps_of_unitary n m nb _ (by simp [rtof, Gate.isUnitary]) c,
    rtof_unitary_basis a b t hab hat hbt ha hb ht s]

/-! ## Steps of the schedule on basis vectors -/

/-- Report §6.1.4 (Stage 12c item 3) — the basis state after one compute step: an AND writes
`x ∧ y` on its (clean) target; `rtof; X t` writes `¬(t ⊕ x ∧ y)`. -/
def stepRun {n m : ℕ} : Step → Reg n × Reg m → Reg n × Reg m
  | (x, y, t, true), s => t.set (x.get s && y.get s) s
  | (x, y, t, false), s => t.set (!(t.get s ^^ (x.get s && y.get s))) s

/-- The qubit side conditions of one step: in the register, pairwise distinct. -/
def stepOk (n m : ℕ) : Step → Bool
  | (x, y, t, _) =>
    x.inRange n m && y.inRange n m && t.inRange n m && x != y && x != t && y != t

/-- The precondition of one compute step: an AND target is clean (`|0⟩`). -/
def stepPre {n m : ℕ} : Step → Reg n × Reg m → Bool
  | (_, _, t, true), s => !t.get s
  | (_, _, _, false), _ => true

/-- The scalar a compute/uncompute pair contributes: `(√2)⁻¹` for an AND (MBU), `1` for a
relative-phase Toffoli pair (`rtofPhase_pair`). -/
def stepScalar : Step → ℂ
  | (_, _, _, true) => ((Real.sqrt 2)⁻¹ : ℂ)
  | (_, _, _, false) => 1

/-- Report §6.1.4 — the basis state after a list of compute steps (pure bit evaluation). -/
def runSteps {n m : ℕ} : List Step → Reg n × Reg m → Reg n × Reg m
  | [], s => s
  | st :: rest, s => runSteps rest (stepRun st s)

/-- Every AND target is clean when its step is computed. -/
def stepsPre {n m : ℕ} : List Step → Reg n × Reg m → Bool
  | [], _ => true
  | st :: rest, s => stepPre st s && stepsPre rest (stepRun st s)

/-- The number of AND (MBU) steps. -/
def nAnd (steps : List Step) : ℕ := steps.countP (·.2.2.2)

theorem stepOk_spec {n m : ℕ} {x y t : Qubit} {cl : Bool} (h : stepOk n m (x, y, t, cl) = true) :
    x.inRange n m = true ∧ y.inRange n m = true ∧ t.inRange n m = true ∧ x ≠ y ∧ x ≠ t ∧
      y ≠ t := by
  simp only [stepOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hx, hy⟩, ht⟩, hxy⟩, hxt⟩, hyt⟩ := h
  exact ⟨hx, hy, ht, hxy, hxt, hyt⟩

section Pairs

variable {n m : ℕ} (nb : ℕ) (c : Fin nb → Bool)

/-- Report §6.1.4, §6.2.4 Layer 1 — the AND compute step (`alloc t` and Gidney's AND) on a basis
vector with a clean target. -/
theorem compute_and_basis (x y t : Qubit) (hok : stepOk n m (x, y, t, true) = true)
    (s : Reg n × Reg m) (hs : t.get s = false) :
    krausOps n m nb (computeGates (x, y, t, true)) c *ᵥ basisVec s =
      basisVec (stepRun (x, y, t, true) s) := by
  obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec hok
  rw [computeGates, krausOps_append_mulVec, single_kraus_one nb c _ rfl,
    tempLogicalAND_kraus_basis nb c x y t hxy hxt hyt hx hy ht s hs]
  rfl

/-- Report §6.2.2, §6.2.4 Layer 2 — the AND uncompute step (MBU and `free t`), every branch, on a
basis vector whose target holds `x ∧ y`. -/
theorem uncompute_and_basis (x y t : Qubit) (j : ℕ) (hok : stepOk n m (x, y, t, true) = true)
    (s : Reg n × Reg m) (hs : t.get s = (x.get s && y.get s)) :
    krausOps n m nb (uncomputeGates j (x, y, t, true)) c *ᵥ basisVec s =
      ((Real.sqrt 2)⁻¹ : ℂ) • basisVec (t.set false s) := by
  obtain ⟨-, -, ht, -, hxt, hyt⟩ := stepOk_spec hok
  rw [uncomputeGates, krausOps_append_mulVec, mbu_branch_basis x y t j hxt hyt ht c s hs,
    Matrix.mulVec_smul, single_kraus_one nb c _ rfl]

/-- The `X t` after (or before) a relative-phase Toffoli. -/
theorem x_single_basis (t : Qubit) (s : Reg n × Reg m) :
    krausOps n m nb [.x t] c *ᵥ basisVec s = basisVec (t.flip s) := by
  rw [krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec]
  exact x_basis n m t s

/-- Report §6.1.4 (KG Theorem 5.1 step) — the compute step `rtof; X t` on any basis vector. -/
theorem compute_rtof_basis (x y t : Qubit) (hok : stepOk n m (x, y, t, false) = true)
    (s : Reg n × Reg m) :
    krausOps n m nb (computeGates (x, y, t, false)) c *ᵥ basisVec s =
      rtofPhase (x.get s) (y.get s) (t.get s ^^ (x.get s && y.get s)) •
        basisVec (stepRun (x, y, t, false) s) := by
  obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec hok
  rw [computeGates, krausOps_append_mulVec, rtof_basis nb c x y t hxy hxt hyt hx hy ht s,
    Matrix.mulVec_smul, x_single_basis, Qubit.flip, Qubit.get_set_self t ht, Qubit.set_set]
  rfl

/-- Report §6.1.4 — the uncompute step `X t; rtof` on any basis vector. -/
theorem uncompute_rtof_basis (x y t : Qubit) (j : ℕ) (hok : stepOk n m (x, y, t, false) = true)
    (s : Reg n × Reg m) :
    krausOps n m nb (uncomputeGates j (x, y, t, false)) c *ᵥ basisVec s =
      rtofPhase (x.get s) (y.get s) (!t.get s ^^ (x.get s && y.get s)) •
        basisVec (t.set (!t.get s ^^ (x.get s && y.get s)) s) := by
  obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec hok
  rw [uncomputeGates, krausOps_append_mulVec, x_single_basis,
    rtof_basis nb c x y t hxy hxt hyt hx hy ht, Qubit.get_flip_ne hxt, Qubit.get_flip_ne hyt,
    Qubit.get_flip_self t ht, Qubit.flip, Qubit.set_set]

/-- Report §6.1.4 (Maslov 2016, Proposition 1; Stage 12c item 2) — the phases of a compute
`rtof; X t` and of its uncompute `X t; rtof` multiply to 1 for **every** value `z` of the target:
`D(x, y, z ⊕ xy) · D(x, y, z) = 1` (`D² = 1` on the real entries when `xy = 0`; `(−i)(i) = 1`
when `xy = 1`). -/
theorem rtofPhase_pair (x y z : Bool) : rtofPhase x y (z ^^ (x && y)) * rtofPhase x y z = 1 := by
  cases x <;> cases y <;> cases z <;> simp [rtofPhase]

/-- Report §6.1.4, §6.2.4 (Stage 12c item 2) — pair cancellation: a compute `rtof; X t`, a block
`M` that maps the intermediate basis vector to `μ` times itself, and the uncompute `X t; rtof`
map `|s⟩` to `μ |s⟩`, whatever `s` holds on the target (no "conditionally clean" hypothesis). -/
theorem rtof_pair_kraus (x y t : Qubit) (j : ℕ) (hok : stepOk n m (x, y, t, false) = true)
    (M : List Gate) (μ : ℂ) (s : Reg n × Reg m)
    (hM : krausOps n m nb M c *ᵥ basisVec (stepRun (x, y, t, false) s) =
      μ • basisVec (stepRun (x, y, t, false) s)) :
    krausOps n m nb (computeGates (x, y, t, false) ++ M ++ uncomputeGates j (x, y, t, false)) c
      *ᵥ basisVec s = μ • basisVec s := by
  obtain ⟨-, -, ht, -, hxt, hyt⟩ := stepOk_spec hok
  have hx : x.get (stepRun (n := n) (m := m) (x, y, t, false) s) = x.get s :=
    Qubit.get_set_ne hxt _ s
  have hy : y.get (stepRun (n := n) (m := m) (x, y, t, false) s) = y.get s :=
    Qubit.get_set_ne hyt _ s
  have htv : t.get (stepRun (n := n) (m := m) (x, y, t, false) s) =
      !(t.get s ^^ (x.get s && y.get s)) := Qubit.get_set_self t ht _ s
  have hback : t.set (!t.get (stepRun (n := n) (m := m) (x, y, t, false) s) ^^
      (x.get (stepRun (n := n) (m := m) (x, y, t, false) s) &&
        y.get (stepRun (n := n) (m := m) (x, y, t, false) s)))
      (stepRun (x, y, t, false) s) = s := by
    rw [hx, hy, htv, Bool.not_not, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, stepRun,
      Qubit.set_set, Qubit.set_get]
  rw [krausOps_append_mulVec, krausOps_append_mulVec, compute_rtof_basis nb c x y t hok,
    Matrix.mulVec_smul, hM, Matrix.mulVec_smul, Matrix.mulVec_smul,
    uncompute_rtof_basis nb c x y t j hok, hback,
    hx, hy, htv, Bool.not_not, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, smul_smul,
    smul_smul, mul_right_comm, rtofPhase_pair, one_mul]

/-- Report §6.2.2, §6.2.4 (Stage 12c item 3) — an AND pair (compute, `M`, MBU uncompute) on a
basis vector with a clean target: `(√2)⁻¹ μ`. -/
theorem and_pair_kraus (x y t : Qubit) (j : ℕ) (hok : stepOk n m (x, y, t, true) = true)
    (M : List Gate) (μ : ℂ) (s : Reg n × Reg m) (hs : t.get s = false)
    (hM : krausOps n m nb M c *ᵥ basisVec (stepRun (x, y, t, true) s) =
      μ • basisVec (stepRun (x, y, t, true) s)) :
    krausOps n m nb (computeGates (x, y, t, true) ++ M ++ uncomputeGates j (x, y, t, true)) c
      *ᵥ basisVec s = (((Real.sqrt 2)⁻¹ : ℂ) * μ) • basisVec s := by
  obtain ⟨-, -, ht, -, hxt, hyt⟩ := stepOk_spec hok
  have hval : t.get (stepRun (n := n) (m := m) (x, y, t, true) s) =
      (x.get (stepRun (n := n) (m := m) (x, y, t, true) s) &&
        y.get (stepRun (n := n) (m := m) (x, y, t, true) s)) := by
    simp only [stepRun]
    rw [Qubit.get_set_self t ht, Qubit.get_set_ne hxt, Qubit.get_set_ne hyt]
  have hback : t.set false (stepRun (n := n) (m := m) (x, y, t, true) s) = s := by
    rw [stepRun, Qubit.set_set, ← hs, Qubit.set_get]
  rw [krausOps_append_mulVec, krausOps_append_mulVec, compute_and_basis nb c x y t hok s hs, hM,
    Matrix.mulVec_smul, uncompute_and_basis nb c x y t j hok _ hval, hback, smul_smul, mul_comm]

/-- Report §6.1.4, §6.2.4 — one compute/uncompute pair of either kind. -/
theorem step_pair_kraus (st : Step) (j : ℕ) (hok : stepOk n m st = true) (M : List Gate)
    (μ : ℂ) (s : Reg n × Reg m) (hpre : stepPre st s = true)
    (hM : krausOps n m nb M c *ᵥ basisVec (stepRun st s) = μ • basisVec (stepRun st s)) :
    krausOps n m nb (computeGates st ++ M ++ uncomputeGates j st) c *ᵥ basisVec s =
      (stepScalar st * μ) • basisVec s := by
  obtain ⟨x, y, t, cl⟩ := st
  cases cl
  · rw [rtof_pair_kraus nb c x y t j hok M μ s hM, stepScalar, one_mul]
  · have hs : t.get s = false := by simpa [stepPre] using hpre
    exact and_pair_kraus nb c x y t j hok M μ s hs hM

/-- The uncompute list of `l ++ [st]` ends with the uncompute of `st` (at some bit). -/
theorem uncomputeAll_append (st : Step) :
    ∀ (l : List Step) (j : ℕ), ∃ j', uncomputeAll j (l ++ [st]) =
      uncomputeAll j l ++ uncomputeGates j' st
  | [], j => ⟨j, by simp [uncomputeAll]⟩
  | s :: l, j => by
    obtain ⟨j', hj'⟩ := uncomputeAll_append st l (if s.2.2.2 then j + 1 else j)
    exact ⟨j', by simp only [List.cons_append, uncomputeAll, hj', List.append_assoc]⟩

/-- Report §6.2.4, §6.3.2 (Stage 12c item 3) — **the inductive restoration claim**: for a middle
block `Φ` diagonal on basis vectors (`φ`), the compute steps, `Φ`, and the uncompute steps in
reverse map `|s⟩` to `(√2)⁻¹^{#AND} · φ(runSteps steps s) · |s⟩`, in every branch `c`, provided
the qubit checks hold and every AND target is clean when it is computed. Induction on the steps:
the outermost pair is `step_pair_kraus` around the inner block. -/
theorem steps_kraus (Φ : List Gate) (φ : Reg n × Reg m → ℂ)
    (hΦ : ∀ s, krausOps n m nb Φ c *ᵥ basisVec s = φ s • basisVec s) :
    ∀ (steps : List Step) (j : ℕ) (s : Reg n × Reg m), steps.all (stepOk n m) = true →
      stepsPre steps s = true →
      krausOps n m nb (steps.flatMap computeGates ++ Φ ++ uncomputeAll j steps.reverse) c
        *ᵥ basisVec s =
        (((Real.sqrt 2)⁻¹ : ℂ) ^ nAnd steps * φ (runSteps steps s)) • basisVec s
  | [], j, s, _, _ => by
    simp only [List.flatMap_nil, List.nil_append, List.reverse_nil, uncomputeAll,
      List.append_nil, hΦ, nAnd, List.countP_nil, pow_zero, one_mul, runSteps]
  | st :: rest, j, s, hok, hpre => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [stepsPre, Bool.and_eq_true] at hpre
    obtain ⟨j', hj'⟩ := uncomputeAll_append st rest.reverse j
    have hsplit : (st :: rest).flatMap computeGates ++ Φ ++ uncomputeAll j (st :: rest).reverse =
        computeGates st ++ (rest.flatMap computeGates ++ Φ ++ uncomputeAll j rest.reverse) ++
          uncomputeGates j' st := by
      simp only [List.flatMap_cons, List.reverse_cons, hj', List.append_assoc]
    rw [hsplit, step_pair_kraus nb c st j' hok.1 _ _ s hpre.1
      (steps_kraus Φ φ hΦ rest j (stepRun st s) hok.2 hpre.2)]
    congr 1
    obtain ⟨x, y, t, cl⟩ := st
    cases cl
    · simp [stepScalar, nAnd, runSteps]
    · simp only [stepScalar, nAnd, List.countP_cons, ↓reduceIte, pow_succ, runSteps]
      ring

/-- The sign of the final phase gate: `−1` iff every qubit of `us` is 1. -/
def phaseSign {n m : ℕ} (us : List Qubit) (s : Reg n × Reg m) : ℂ :=
  if us.all (·.get s) then -1 else 1

/-- Report §6.1.4 — the phase (`Z` on one qubit, `CZ` on two) on a basis vector. -/
theorem phase_kraus (us : List Qubit) (hus : us.length = 1 ∨ us.length = 2)
    (s : Reg n × Reg m) :
    krausOps n m nb (phase us) c *ᵥ basisVec s = phaseSign us s • basisVec s := by
  rcases us with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at hus
  · rw [phase, krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec]
    exact (z_basis n m p s).trans (by simp [phaseSign])
  · rw [phase, krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec]
    exact (cz_basis n m p q s).trans (by simp [phaseSign])
  · simp at hus

end Pairs

/-! ## The restoration claim for `mczFew` -/

/-- Report §6.1.4 (Stage 12c item 3) — `mczFew.mid`: the basis state reached from `|x, 0…0⟩`
after the compute steps of `plan n v` (pure bit evaluation). -/
def mid (a n : ℕ) (v : MczVariant) (x : Reg n) : Reg n × Reg a :=
  runSteps (plan n v).1 (x, fun _ => false)

/-- Report §6.1.4 (Stage 12c item 3) — the bit the final `CZ` / `Z` reads: the product of the
qubits left unmarked, at `mid`. -/
def phaseBit (a n : ℕ) (v : MczVariant) (x : Reg n) : Bool :=
  (plan n v).2.all (·.get (mid a n v x))

/-- `mczFew n v = .ok C` exposes the gate list of `C` and a phase on one or two qubits. -/
theorem mczFew_ok {n : ℕ} {v : MczVariant} {C : Circuit} (h : mczFew n v = .ok C) :
    C = ⟨n, (plan n v).1.flatMap computeGates ++ phase (plan n v).2 ++
      uncomputeAll 0 (plan n v).1.reverse⟩ ∧
      ((plan n v).2.length = 1 ∨ (plan n v).2.length = 2) := by
  unfold mczFew at h
  rcases hp : plan n v with ⟨steps, us⟩
  rw [hp] at h
  by_cases hn : n = 0
  · subst hn
    simp [Diffusion.fail, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · by_cases hu : us = [] ∨ 2 < us.length
    · simp [hn, hu, Diffusion.fail, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [hn, hu, pure, Except.pure] at h
      have h0 : us.length ≠ 0 := fun e => hu (Or.inl (List.length_eq_zero_iff.mp e))
      have h3 : ¬ 2 < us.length := fun e => hu (Or.inr e)
      refine ⟨?_, by simp only; omega⟩
      rw [← h]
      simp only [List.append_assoc]

/-- Report §6.2.4, §6.3.2 (Stage 12c item 3) — **the restoration claim** for `mczFew n v`: in
every branch `c`, the Kraus operator maps `|x, 0…0⟩` to
`(√2)⁻¹^{#AND} (−1)^{phaseBit x} |x, 0…0⟩`, given the per-step qubit checks and the clean-AND
precondition along the compute steps (both decidable; checked for n = 8 below). -/
theorem mczFew_kraus_basis {n a : ℕ} {v : MczVariant} {C : Circuit} (hC : mczFew n v = .ok C)
    (hok : (plan n v).1.all (stepOk n a) = true) (c : Fin C.nBits → Bool) (x : Reg n)
    (hpre : stepsPre (plan n v).1 ((x, fun _ => false) : Reg n × Reg a) = true) :
    krausOps n a C.nBits C.gates c *ᵥ basisVec ((x, fun _ => false) : Reg n × Reg a) =
      (((Real.sqrt 2)⁻¹ : ℂ) ^ nAnd (plan n v).1 * (if phaseBit a n v x then -1 else 1)) •
        basisVec ((x, fun _ => false) : Reg n × Reg a) := by
  obtain ⟨hCeq, hus⟩ := mczFew_ok hC
  generalize C.nBits = nb at c
  rw [hCeq]
  exact steps_kraus nb c _ (phaseSign (plan n v).2) (phase_kraus nb c _ hus) _ 0 _ hok hpre

/-! ## Item 4 — KG correctness, classical, n = 8 -/

/-- Report §6.1.4, KG Theorem 5.1 for n = 8 (Stage 12c item 4) — candidate B: from `|x, 0, 0⟩`
every AND target is clean when computed, and the qubits of the final `CZ` multiply to
`x₀ ∧ … ∧ x₇`. By `decide +kernel` over the 256 inputs. -/
theorem mczFew_logDepth_8_classical (x : Reg 8) :
    stepsPre (plan 8 .logDepth).1 ((x, fun _ => false) : Reg 8 × Reg 2) = true ∧
      phaseBit 2 8 .logDepth x = allOnes x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext k; fin_cases k <;> rfl
  have key : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool,
      (stepsPre steps8 ((![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇], fun _ => false) : Reg 8 × Reg 2) &&
        (us8.all (·.get (runSteps steps8
          ((![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇], fun _ => false) : Reg 8 × Reg 2))) ==
          allOnes ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇])) = true := by
    decide +kernel
  have h := key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← hx] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simpa only [phaseBit, mid, plan_8_logDepth] using h

/-- The compute steps of `mczFew 8 .logDepth` pass the qubit checks on `Reg 8 × Reg 2`. -/
theorem steps8_ok : (plan 8 .logDepth).1.all (stepOk 8 2) = true := by
  rw [plan_8_logDepth]
  decide +kernel

/-- KG correctness, classical, for candidate A (`ladder`, KG §5.2), n = 8, one clean ancilla (not
used further in Stage 12c). -/
theorem mczFew_ladder_8_classical (x : Reg 8) :
    stepsPre (plan 8 .ladder).1 ((x, fun _ => false) : Reg 8 × Reg 1) = true ∧
      phaseBit 1 8 .ladder x = allOnes x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext k; fin_cases k <;> rfl
  have key : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool,
      (stepsPre (plan 8 .ladder).1
          ((![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇], fun _ => false) : Reg 8 × Reg 1) &&
        (phaseBit 1 8 .ladder ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇] ==
          allOnes ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇])) = true := by
    decide +kernel
  have h := key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← hx] at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h

/-! ## Item 5 — assembly -/

open scoped Kronecker in
/-- Report §6.2.1, §6.3.2, §8.2 (Stage 12c item 5) — candidate B for n = 8 restores its two
clean ancillae and applies the phase oracle of `P_all = x₀ ∧ … ∧ x₇`, on density operators:
`ancRestore_of_kraus` with the scalar `(√2)⁻¹²` in each of the 4 branches
(`mczFew_kraus_basis`, `mczFew_logDepth_8_classical`, `kraus_mul_ancProj`). -/
theorem mczFew_ancRestore_8 {C : Circuit} (hC : mczFew 8 .logDepth = .ok C) :
    AncRestore 8 2 C (phaseOracle allOnes) := by
  have hCeq : C = mczFew8 := by
    rw [mczFew_8_ok] at hC
    exact (Except.ok.inj hC).symm
  have hnA : nAnd (plan 8 .logDepth).1 = 2 := by rw [plan_8_logDepth]; decide +kernel
  have hWF : C.WF := hCeq ▸ mczFew8_WF
  have hnb : C.nBits = 2 := hCeq ▸ mczFew8_nBits
  refine ancRestore_of_kraus hWF _ (fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ 2) ?_ fun c => ?_
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, hnb, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), nsmul_eq_mul]
    rw [← pow_mul, inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
      (by norm_num)]
    norm_num
  · apply kraus_mul_ancProj
    intro x
    obtain ⟨hpre, hbit⟩ := mczFew_logDepth_8_classical x
    rw [mczFew_kraus_basis hC steps8_ok c x hpre, hnA, hbit]

/-- Report §8.2 — the diffusion with candidate B for n = 8 is the V1 diffusion circuit around
`mczFew8`. -/
theorem diffusionFew_8_ok : diffusionFew 8 .logDepth = .ok (diffusionCircuit 8 mczFew8) := by
  simp only [diffusionFew, mczFew_8_ok]
  rfl

/-- Report §8.2, §6.2.4, §9.5.2 (Stage 12c item 5) — **`diffusionFew_ancRestore_8`**: the
diffusion `H X · MCZ · X H` with candidate B (2 clean ancillae) restores its ancillae and applies
`U_s = 2|s⟩⟨s| − I` on the 8 data qubits (`diffusion_ancRestore`, which cancels the global sign of
`−U_s`, around `mczFew_ancRestore_8`). -/
theorem diffusionFew_ancRestore_8 {D : Circuit} (hD : diffusionFew 8 .logDepth = .ok D) :
    AncRestore 8 2 D (diffU 8) := by
  rw [diffusionFew_8_ok] at hD
  rw [← Except.ok.inj hD]
  exact diffusion_ancRestore mczFew8 mczFew8_WF.bitsOk (mczFew_ancRestore_8 mczFew_8_ok)

end

/-- Report §9.1.1 (Stage 12c item 6) — the diffusion with candidate B for n = 8 is well formed. -/
theorem diffusionFew8_WF : (diffusionCircuit 8 mczFew8).WF := by decide +kernel

/-! ## Stage 12d — per-instance certification of candidate B

Report §5.1.3 (per-request work is specialization and a kernel check), §6.2, §8.2 — Stage 12d
decision 1 (DECISIONS.md 2026-10-26, Stage 12d): the restoration of `mczFew n v` for general `n`
and variant with the classical KG fact as an **explicit hypothesis**
(`mczFew_ancRestore_of_classical`); a certificate for a request with `n` data qubits proves the
hypothesis for that `n` by `decide +kernel` on `fewCheck` (`2ⁿ` inputs, `fewCheck_sound`). The
all-n theorem (KG Theorem 5.1) stays a planned SORRIES.md row. -/

namespace FewSchedule

/-- `MczFew.doubling` with `substepsK` (kernel-evaluable; equal by `doubling_eq`): `FewScheduleK.doublingK`. -/
abbrev doublingK := FewScheduleK.doublingK

/-- `MczFew.plan` with `doublingK` for `doubling`: the same schedule, evaluable by the kernel
(`plan_eq_planK`): `FewScheduleK.planK`. -/
abbrev planK := FewScheduleK.planK

theorem plan_eq_planK (n : ℕ) (v : MczVariant) : plan n v = planK n v :=
  FewScheduleK.plan_eq_planK n v

end FewSchedule

/-- `mczFew` with `FewSchedule.planK` for `plan`: the same circuit (`mczFew_eq_K`), evaluable by
the kernel. Generated certificates name the few-ancilla MCZ as `okPayload (mczFewK n .logDepth)`. -/
def mczFewK (n : ℕ) (v : MczVariant) : Except DSL.Diagnostic Circuit := do
  if n == 0 then Diffusion.fail .unsupportedNetwork "the MCZ needs at least one data qubit"
  let (steps, us) := FewSchedule.planK n v
  if us.length == 0 || us.length > 2 then
    Diffusion.fail .unsupportedNetwork
      s!"few:{v.name}: {us.length} qubits left unmarked for n = {n}"
  return ⟨n, steps.flatMap computeGates ++ phase us ++ uncomputeAll 0 steps.reverse⟩

theorem mczFew_eq_K (n : ℕ) (v : MczVariant) : mczFew n v = mczFewK n v := by
  simp only [mczFew, mczFewK, FewSchedule.plan_eq_planK]

/-- `f x` for every `x : Reg n`, by recursion on `n` (`Fin.cons`): the exhaustive check over
the `2ⁿ` inputs, evaluable by the kernel. -/
def allRegs : (n : ℕ) → (Reg n → Bool) → Bool
  | 0, f => f Fin.elim0
  | n + 1, f => allRegs n (fun x => f (Fin.cons false x)) && allRegs n (fun x => f (Fin.cons true x))

theorem allRegs_spec : ∀ (n : ℕ) (f : Reg n → Bool), allRegs n f = true → ∀ x, f x = true
  | 0, f, h, x => by
    have hx : x = Fin.elim0 := funext fun i => i.elim0
    rw [hx]
    exact h
  | n + 1, f, h, x => by
    simp only [allRegs, Bool.and_eq_true] at h
    have hct : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
    cases hx : x 0
    · rw [hx] at hct
      have h' := allRegs_spec n _ h.1 (Fin.tail x)
      rwa [hct] at h'
    · rw [hx] at hct
      have h' := allRegs_spec n _ h.2 (Fin.tail x)
      rwa [hct] at h'

/-- Report §6.1.4, KG Theorem 5.1 for one `n` (Stage 12d decision 1) — the per-instance check of
a schedule `p = (steps, us)` on `Reg n × Reg a`: every step passes the qubit checks, the qubits of
the final phase are in the register, and for each of the `2ⁿ` inputs every AND target is clean
when computed and the qubits of the final phase multiply to `x₀ ∧ … ∧ x_{n−1}`. -/
def fewCheck (n a : ℕ) (p : List Step × List Qubit) : Bool :=
  p.1.all (stepOk n a) && p.2.all (·.inRange n a) &&
    allRegs n fun x =>
      stepsPre p.1 ((x, fun _ => false) : Reg n × Reg a) &&
        (p.2.all (·.get (runSteps p.1 ((x, fun _ => false) : Reg n × Reg a))) == allOnes x)

/-- Report §6.1.4 (Stage 12d decision 1) — what `fewCheck` establishes for `plan n v`: the
hypotheses of `mczFew_ancRestore_of_classical`, the classical KG fact among them. -/
theorem fewCheck_sound {n a : ℕ} {v : MczVariant} (h : fewCheck n a (plan n v) = true) :
    (plan n v).1.all (stepOk n a) = true ∧ (plan n v).2.all (·.inRange n a) = true ∧
      ∀ x : Reg n, stepsPre (plan n v).1 ((x, fun _ => false) : Reg n × Reg a) = true ∧
        phaseBit a n v x = allOnes x := by
  simp only [fewCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun x => ?_⟩
  have hx := allRegs_spec n _ h3 x
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  exact ⟨hx.1, by simpa only [phaseBit, mid] using hx.2⟩

/-! ### Widening the ancilla register -/

section Widen

variable {n a a' : ℕ}

theorem inRange_mono (h : a ≤ a') {q : Qubit} (hq : q.inRange n a = true) :
    q.inRange n a' = true := by
  cases q <;> simp only [Qubit.inRange, decide_eq_true_eq] at hq ⊢ <;> omega

theorem stepOk_mono (h : a ≤ a') {st : Step} (hok : stepOk n a st = true) :
    stepOk n a' st = true := by
  obtain ⟨x, y, t, cl⟩ := st
  obtain ⟨hx, hy, ht, hxy, hxt, hyt⟩ := stepOk_spec hok
  simp [stepOk, inRange_mono h hx, inRange_mono h hy, inRange_mono h ht, hxy, hxt, hyt]

/-- Two basis states, of ancilla widths `a` and `a'`, that agree on the qubits of `Reg n × Reg a`. -/
def Agree (n a : ℕ) {a' : ℕ} (s : Reg n × Reg a) (s' : Reg n × Reg a') : Prop :=
  ∀ q : Qubit, q.inRange n a = true → q.get s = q.get s'

theorem agree_init (x : Reg n) :
    Agree n a ((x, fun _ => false) : Reg n × Reg a) ((x, fun _ => false) : Reg n × Reg a') := by
  intro q _
  cases q <;> simp [Qubit.get]

theorem agree_stepRun (h : a ≤ a') {st : Step} (hok : stepOk n a st = true)
    {s : Reg n × Reg a} {s' : Reg n × Reg a'} (hs : Agree n a s s') :
    Agree n a (stepRun st s) (stepRun st s') := by
  obtain ⟨x, y, t, cl⟩ := st
  obtain ⟨hx, hy, ht, -, -, -⟩ := stepOk_spec hok
  intro q hq
  by_cases hqt : q = t
  · rw [hqt]
    cases cl <;> simp only [stepRun] <;>
      rw [Qubit.get_set_self _ ht, Qubit.get_set_self _ (inRange_mono h ht)] <;>
      simp only [hs x hx, hs y hy, hs t ht]
  · cases cl <;> simp only [stepRun] <;> rw [Qubit.get_set_ne hqt, Qubit.get_set_ne hqt, hs q hq]

theorem agree_runSteps (h : a ≤ a') : ∀ (steps : List Step) (s : Reg n × Reg a)
    (s' : Reg n × Reg a'), steps.all (stepOk n a) = true → Agree n a s s' →
    stepsPre steps s = stepsPre steps s' ∧ Agree n a (runSteps steps s) (runSteps steps s')
  | [], _, _, _, hs => ⟨rfl, hs⟩
  | st :: rest, s, s', hok, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := agree_runSteps h rest _ _ hok.2 (agree_stepRun h hok.1 hs)
    refine ⟨?_, h2⟩
    simp only [stepsPre, h1]
    congr 1
    obtain ⟨x, y, t, cl⟩ := st
    obtain ⟨-, -, ht, -⟩ := stepOk_spec hok.1
    cases cl <;> simp [stepPre, hs t ht]

theorem all_get_congr {us : List Qubit} (hus : us.all (·.inRange n a) = true)
    {s : Reg n × Reg a} {s' : Reg n × Reg a'} (hs : Agree n a s s') :
    us.all (·.get s) = us.all (·.get s') := by
  induction us with
  | nil => rfl
  | cons q us ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hus
    simp only [List.all_cons]
    rw [hs q hus.1, ih hus.2]

end Widen

/-! ### The restoration of `mczFew` from the classical fact -/

/-- `∑_c ‖(√2)⁻¹^k‖² = 1` over the `2^k` branches of `k` measured bits. -/
theorem sum_branches_invSqrtTwo (nb k : ℕ) (hk : nb = k) :
    ∑ _c : Fin nb → Bool, ‖((Real.sqrt 2)⁻¹ : ℂ) ^ k‖ ^ 2 = 1 := by
  subst hk
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← pow_mul, inv_pow, pow_mul', Real.sq_sqrt (by norm_num)]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

open scoped Kronecker in
/-- Report §6.2.1, §6.3.2, §8.2 (Stage 12d decision 1) — **`mczFew_ancRestore_of_classical`**:
for every `n` and variant, if `mczFew n v` is synthesized and well formed, measures one bit per
AND, its steps pass the qubit checks on `Reg n × Reg a₀`, and the **classical KG fact** holds
on `Reg n × Reg a₀` (every AND target clean when computed; the qubits of the final phase multiply
to `x₀ ∧ … ∧ x_{n−1}`, for every input `x`), then on every register `a ≥ a₀` it restores its
ancillae and applies the phase oracle of `P_all`, on density operators. The classical fact is a
hypothesis; `fewCheck_sound` supplies it for one `n` by kernel evaluation. -/
theorem mczFew_ancRestore_of_classical {n a₀ : ℕ} {v : MczVariant} {C : Circuit}
    (hC : mczFew n v = .ok C) (hWF : C.WF) (hnb : C.nBits = nAnd (plan n v).1)
    (hok : (plan n v).1.all (stepOk n a₀) = true)
    (hus : (plan n v).2.all (·.inRange n a₀) = true)
    (hcl : ∀ x : Reg n, stepsPre (plan n v).1 ((x, fun _ => false) : Reg n × Reg a₀) = true ∧
      phaseBit a₀ n v x = allOnes x)
    {a : ℕ} (ha : a₀ ≤ a) : AncRestore n a C (phaseOracle allOnes) := by
  have hok' : (plan n v).1.all (stepOk n a) = true :=
    List.all_eq_true.mpr fun st hst => stepOk_mono ha (List.all_eq_true.mp hok st hst)
  have hcl' : ∀ x : Reg n,
      stepsPre (plan n v).1 ((x, fun _ => false) : Reg n × Reg a) = true ∧
        phaseBit a n v x = allOnes x := by
    intro x
    obtain ⟨h1, h2⟩ := agree_runSteps ha (plan n v).1 _ _ hok (agree_init x)
    obtain ⟨hp, hb⟩ := hcl x
    refine ⟨by rw [← h1]; exact hp, ?_⟩
    rw [← hb]
    simp only [phaseBit, mid]
    exact (all_get_congr hus h2).symm
  refine ancRestore_of_kraus hWF _ (fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ nAnd (plan n v).1)
    (sum_branches_invSqrtTwo _ _ hnb) fun c => ?_
  apply kraus_mul_ancProj
  intro x
  obtain ⟨hpre, hbit⟩ := hcl' x
  rw [mczFew_kraus_basis hC hok' c x hpre, hbit]

/-- `diffusionFew n v` is the V1 diffusion circuit around `mczFew n v`. -/
theorem diffusionFew_ok_of {n : ℕ} {v : MczVariant} {C : Circuit} (hC : mczFew n v = .ok C) :
    diffusionFew n v = .ok (diffusionCircuit n C) := by
  simp only [diffusionFew, hC]
  rfl

/-- Report §8.2, §6.2.4 (Stage 12d decision 1) — the few-ancilla diffusion restores its ancillae
and applies `U_s = 2|s⟩⟨s| − I` on every register `a ≥ D.nAnc`, given the hypotheses of
`mczFew_ancRestore_of_classical` at some `a₀ ≤ C.nAnc` (`diffusion_ancRestore`). -/
theorem diffusionFew_ancRestore_of_classical {n a₀ : ℕ} {v : MczVariant} {C D : Circuit}
    (hC : mczFew n v = .ok C) (hWF : C.WF) (hnb : C.nBits = nAnd (plan n v).1)
    (hok : (plan n v).1.all (stepOk n a₀) = true)
    (hus : (plan n v).2.all (·.inRange n a₀) = true)
    (hcl : ∀ x : Reg n, stepsPre (plan n v).1 ((x, fun _ => false) : Reg n × Reg a₀) = true ∧
      phaseBit a₀ n v x = allOnes x)
    (ha₀ : a₀ ≤ C.nAnc) (hD : diffusionFew n v = .ok D) :
    ∀ a, D.nAnc ≤ a → AncRestore n a D (diffU n) := by
  rw [diffusionFew_ok_of hC] at hD
  obtain rfl := (Except.ok.inj hD).symm
  intro a ha
  have hle : C.nAnc ≤ (diffusionCircuit n C).nAnc := by
    rw [diffusionCircuit, nAnc_append, nAnc_append]
    exact le_max_of_le_left (le_max_right _ _)
  exact diffusion_ancRestore C hWF.bitsOk
    (mczFew_ancRestore_of_classical hC hWF hnb hok hus hcl (ha₀.trans (hle.trans ha)))

/-- Report §3.2.4 (Stage 12d decision 3) — `groverCircuitFew` is `groverCircuitOf` the oracle and
the few-ancilla diffusion: `H^{⊗n}` then `r` copies of `oracle ; diffusionFew n v`, by the
same shifted `Circuit.append` as `groverCircuit`. -/
theorem groverCircuitFew_ok_of {P : Network} {n r : ℕ} {v : MczVariant} {oc C : Circuit}
    (hP : P.nInputs = n) (ho : synthesizeOracle P = .ok oc) (hC : mczFew n v = .ok C) :
    groverCircuitFew P n r v = .ok (groverCircuitOf oc (diffusionCircuit n C) n r) := by
  simp [groverCircuitFew, groverIterationFew, hP, ho, diffusionFew_ok_of hC, groverCircuitOf,
    bind, Except.bind, pure, Except.pure]

end CQRV.Grover

end
