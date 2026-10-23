module

public import CQRV.Circuit.Restoration

/-!
# CQRV.Circuit.OracleBlocks

Report §6.2.2, §6.2.4 (Layer 1), §6.1.4, §6.3.2 — the blocks of the synthesized oracle on
computational basis vectors, the parts of the basis-vector route to Lemma 6.3.2 (DECISIONS.md,
Stage 6b-2):

* `Circuit.WF_append` — the shifted append of two well-formed circuits on the same data register
  is well formed;
* `krausOps_append_mulVec` / `krausOps_append_shift_mulVec` — Kraus operators of a concatenation,
  applied to a vector, block after block (same branch, absolute bits; or shifted bits with the
  branch split as in `channelDenote_append`);
* `tempLogicalAND_correct_lift` — compute block: `|s⟩ ↦ |s[t ↦ s a ∧ s b]⟩` (phase 1), any
  register;
* `mbu_branch_basis` — uncompute block, every branch: if `t` holds `a ∧ b`, then
  `|s⟩ ↦ (1/√2) |s[t ↦ 0]⟩`, no sign;
* `z_basis`, `x_basis` — `Z t` is the phase `(−1)^{s t}`, `X q` (NOT polarity) flips `q`.

All statements are on basis vectors `basisVec s`; the gate-by-gate computation uses the lens
lemmas of `Qubit.get` / `Qubit.set` and never enumerates the register.
-/

@[expose] public section

namespace CQRV

open CQRV.Synthesis

/-! ## Item 0 — `Circuit.WF_append` -/

/-- Shifting classical bits does not change the qubit discipline of a gate. -/
theorem Gate.qubitsOk_shiftBits (nData k : ℕ) (g : Gate) :
    (g.shiftBits k).qubitsOk nData = g.qubitsOk nData := by
  cases g <;> rfl

/-- Report §9.1.1, §6.2.2 (Stage 6b-1 open question 2) — the shifted append of two well-formed
circuits on the same data register is well formed: qubit ranges are those of the pieces, the
classical-bit discipline is `Circuit.bitsOk_append`. -/
theorem Circuit.WF_append {C₁ C₂ : Circuit} (hn : C₁.nData = C₂.nData) (h₁ : C₁.WF)
    (h₂ : C₂.WF) : (C₁.append C₂).WF := by
  have hb := Circuit.bitsOk_append h₁.bitsOk h₂.bitsOk
  simp only [Circuit.WF, Circuit.wf, Bool.and_eq_true] at h₁ h₂ ⊢
  refine ⟨?_, hb⟩
  simp only [Circuit.append, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true,
    Function.comp_apply, Gate.qubitsOk_shiftBits] at h₁ h₂ ⊢
  exact ⟨h₁.1, hn ▸ h₂.1⟩

noncomputable section

open Matrix

/-! ## Lens lemmas: commuting `set`s, the 3-qubit slice of a basis state -/

namespace Qubit

variable {n m : ℕ}

theorem set_comm {p q : Qubit} (hpq : p ≠ q) (v w : Bool) (s : Reg n × Reg m) :
    p.set v (q.set w s) = q.set w (p.set v s) := by
  cases p <;> cases q <;> simp only [set] <;> split_ifs <;> simp_all <;>
    exact Function.update_comm (fun h => hpq (Fin.ext_iff.mp h).symm) _ _ _

/-- Report §6.2.2 — the basis state `s` with the qubits `a b t` set to `x y z` (the 3-qubit
slice through `s` on which a TempLogicalAND block acts). -/
def slice (a b t : Qubit) (s : Reg n × Reg m) (x y z : Bool) : Reg n × Reg m :=
  t.set z (b.set y (a.set x s))

section Slice

variable {a b t : Qubit} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ha : a.inRange n m = true)
  (hb : b.inRange n m = true) (ht : t.inRange n m = true) (s : Reg n × Reg m)

include hat hab ha in
theorem get_slice_a (x y z : Bool) : a.get (slice a b t s x y z) = x := by
  rw [slice, get_set_ne hat, get_set_ne hab, get_set_self a ha]

include hbt hb in
theorem get_slice_b (x y z : Bool) : b.get (slice a b t s x y z) = y := by
  rw [slice, get_set_ne hbt, get_set_self b hb]

include ht in
theorem get_slice_t (x y z : Bool) : t.get (slice a b t s x y z) = z := by
  rw [slice, get_set_self t ht]

include ht in
theorem flip_slice_t (x y z : Bool) : t.flip (slice a b t s x y z) = slice a b t s x y (!z) := by
  rw [flip, get_slice_t ht, slice, set_set]
  rfl

include hab hat ha in
theorem flip_slice_a (x y z : Bool) : a.flip (slice a b t s x y z) = slice a b t s (!x) y z := by
  rw [flip, get_slice_a hab hat ha, slice, slice, set_comm hat, set_comm hab, set_set]

include hbt hb in
theorem flip_slice_b (x y z : Bool) : b.flip (slice a b t s x y z) = slice a b t s x (!y) z := by
  rw [flip, get_slice_b hbt hb, slice, slice, set_comm hbt, set_set]

include ht in
theorem slice_t_ne (x y : Bool) : slice a b t s x y false ≠ slice a b t s x y true := by
  intro h
  have := congrArg t.get h
  rw [get_slice_t ht, get_slice_t ht] at this
  exact Bool.false_ne_true this

end Slice

end Qubit

/-! ## Gates on basis vectors -/

section Basis

variable (n m : ℕ)

/-- A monomial matrix maps `|s⟩` to `φ s · |σ s⟩`. -/
theorem monoMat_mulVec_basisVec {ι : Type} [Fintype ι] [DecidableEq ι] {σ : ι → ι}
    (hσ : Function.Involutive σ) (φ : ι → ℂ) (s : ι) :
    monoMat σ φ *ᵥ basisVec s = φ s • basisVec (σ s) := by
  funext i
  rw [monoMat_mulVec hσ]
  simp only [basisVec, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = σ s
  · subst h; simp [hσ s]
  · have h' : ¬ σ i = s := fun e => h (by rw [← e, hσ i])
    simp [h, h']

theorem phaseMat_basis (q : Qubit) (p : ℂ) (s : Reg n × Reg m) :
    phaseMat n m q p *ᵥ basisVec s = (if q.get s then p else 1) • basisVec s :=
  monoMat_mulVec_basisVec (fun _ => rfl) _ s

theorem projMat_basis (q : Qubit) (v : Bool) (s : Reg n × Reg m) :
    projMat n m q v *ᵥ basisVec s = (if q.get s = v then (1 : ℂ) else 0) • basisVec s := by
  rw [projMat]; exact monoMat_mulVec_basisVec (σ := id) (fun _ => rfl)
    (fun s => if q.get s = v then 1 else 0) s

/-- Report §6.2.2, §6.1.4 — `H q |s⟩ = (1/√2)((−1)^{s q} |s⟩ + |s[q ↦ ¬ s q]⟩)`. -/
theorem h_basis {q : Qubit} (hq : q.inRange n m = true) (s : Reg n × Reg m) :
    gateU n m (.h q) *ᵥ basisVec s = ((Real.sqrt 2)⁻¹ : ℂ) •
      ((if q.get s then -1 else 1) • basisVec s + basisVec (q.flip s)) := by
  funext i
  rw [gateU_h_mulVec n m hq]
  simp only [basisVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases h : i = s
  · subst h
    have h' : ¬ q.flip i = i := fun e => by
      have := congrArg q.get e; rw [Qubit.get_flip_self q hq] at this; cases hi : q.get i <;>
        simp_all
    have h'' : ¬ i = q.flip i := fun e => h' e.symm
    simp [h', h'']
  · have e : (q.flip i = s) ↔ (i = q.flip s) :=
      ⟨fun e => by rw [← e, Qubit.flip_involutive q i],
       fun e => by rw [e, Qubit.flip_involutive q s]⟩
    simp only [h, ↓reduceIte, mul_zero, smul_zero, zero_add, e]

theorem s_basis (q : Qubit) (s : Reg n × Reg m) :
    gateU n m (.s q) *ᵥ basisVec s = (if q.get s then Complex.I else 1) • basisVec s := by
  rw [gateU_s]; exact phaseMat_basis n m q _ s

theorem t_basis (q : Qubit) (s : Reg n × Reg m) :
    gateU n m (.t q) *ᵥ basisVec s = (if q.get s then ω else 1) • basisVec s := by
  rw [gateU_t]; exact phaseMat_basis n m q _ s

theorem tdg_basis (q : Qubit) (s : Reg n × Reg m) :
    gateU n m (.tdg q) *ᵥ basisVec s = (if q.get s then star ω else 1) • basisVec s := by
  rw [gateU_tdg]; exact phaseMat_basis n m q _ s

/-- Report §6.1.4 (item 4) — `Z t` on a basis state is the phase `(−1)^{s t}`: on the ancilla
holding `P(x)` it is the phase oracle. -/
theorem z_basis (t : Qubit) (s : Reg n × Reg m) :
    gateU n m (.z t) *ᵥ basisVec s = (if t.get s then (-1 : ℂ) else 1) • basisVec s := by
  rw [gateU_z]; exact phaseMat_basis n m t (-1) s

/-- Report §6.1.2, §6.1.4 (item 4) — `X q` (the NOT polarity of `prepare`) permutes basis
states: `|s⟩ ↦ |s[q ↦ ¬ s q]⟩`. -/
theorem x_basis (q : Qubit) (s : Reg n × Reg m) :
    gateU n m (.x q) *ᵥ basisVec s = basisVec (q.flip s) := by
  rw [gateU, monoMat_mulVec_basisVec (Qubit.flip_involutive q), one_smul]

theorem cnot_basis {c t : Qubit} (hct : c ≠ t) (s : Reg n × Reg m) :
    gateU n m (.cnot c t) *ᵥ basisVec s = basisVec (cnotPerm n m c t s) := by
  simp only [gateU, hct, ↓reduceIte]
  rw [monoMat_mulVec_basisVec (cnotPerm_involutive n m hct), one_smul]

theorem cz_basis (p q : Qubit) (s : Reg n × Reg m) :
    gateU n m (.cz p q) *ᵥ basisVec s =
      (if p.get s && q.get s then (-1 : ℂ) else 1) • basisVec s := by
  rw [gateU]; exact monoMat_mulVec_basisVec (σ := id) (fun _ => rfl)
    (fun s => if p.get s && q.get s then -1 else 1) s

end Basis

/-! ## Item 1 — Kraus operators of a concatenation, block after block -/

section Chain

variable (n m : ℕ)

/-- Report §9.1.1, §6.2.4 (item 1) — in one branch `c` with absolute classical bits (the form of
the synthesizer's flat gate list), the Kraus operator of `gs₁ ++ gs₂` applied to `v` is that of
`gs₂` applied to that of `gs₁` applied to `v`. Blocks chain with `mulVec`. -/
theorem krausOps_append_mulVec (nb : ℕ) (gs₁ gs₂ : List Gate) (c : Fin nb → Bool)
    (v : Reg n × Reg m → ℂ) :
    krausOps n m nb (gs₁ ++ gs₂) c *ᵥ v = krausOps n m nb gs₂ c *ᵥ (krausOps n m nb gs₁ c *ᵥ v) := by
  rw [krausOps_append_gates, Matrix.mulVec_mulVec]

/-- Report §9.1.1, §6.2.4 (item 1) — the same for the shifted append (`Circuit.append`): the
branch `c` of `m₁ + m₂` bits is split into its first `m₁` bits (read by the disciplined prefix)
and its last `m₂` bits (read by the shifted suffix), as in `channelDenote_append`. -/
theorem krausOps_append_shift_mulVec {m₁ m₂ : ℕ} (gs₁ gs₂ : List Gate)
    (h₁ : Circuit.bitsOkFrom m₁ [] gs₁ = true) (c : Fin (m₁ + m₂) → Bool)
    (v : Reg n × Reg m → ℂ) :
    krausOps n m (m₁ + m₂) (gs₁ ++ gs₂.map (Gate.shiftBits m₁)) c *ᵥ v =
      krausOps n m m₂ gs₂ (fun i => c (Fin.natAdd m₁ i)) *ᵥ
        (krausOps n m m₁ gs₁ (fun i => c (Fin.castAdd m₂ i)) *ᵥ v) := by
  rw [krausOps_append_mulVec, krausOps_castAdd n m [] (by simp) gs₁ h₁, krausOps_shift]

end Chain

/-! ## Item 2 — the compute block on any register -/

/-- Report §6.2.2, §6.2.4 Layer 1 — the lift of `tempLogicalAND_correct` to any register:
for distinct in-range qubits `a b t` and a basis state with `t = 0`, the compute listing sets
`t` to `a ∧ b` and changes nothing else (phase 1). Proof: generic, gate by gate on the 3-qubit
slice of `s` (`Qubit.slice`), for the 4 values of `(a, b)`; the vector is a combination of
`|slice x y 0⟩` and `|slice x y 1⟩` throughout. -/
theorem tempLogicalAND_correct_lift {n m : ℕ} (a b t : Qubit) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ha : a.inRange n m = true) (hb : b.inRange n m = true)
    (ht : t.inRange n m = true) (s : Reg n × Reg m) (hs : t.get s = false) :
    unitaryDenote n m (TempLogicalAND a b t) *ᵥ basisVec s =
      basisVec (t.set (a.get s && b.get s) s) := by
  have hin : s = Qubit.slice a b t s (a.get s) (b.get s) false := by
    rw [Qubit.slice, Qubit.set_get, Qubit.set_get, ← hs, Qubit.set_get]
  have hout : t.set (a.get s && b.get s) s =
      Qubit.slice a b t s (a.get s) (b.get s) (a.get s && b.get s) := by
    rw [Qubit.slice, Qubit.set_get, Qubit.set_get]
  rw [hout]
  conv_lhs => rw [hin]
  generalize a.get s = x
  generalize b.get s = y
  have hta : t ≠ a := Ne.symm hat
  have htb : t ≠ b := Ne.symm hbt
  have ne := Qubit.slice_t_ne (a := a) (b := b) ht s x y
  have ne' := ne.symm
  funext i
  by_cases h0 : i = Qubit.slice a b t s x y false <;>
    by_cases h1 : i = Qubit.slice a b t s x y true
  · exact absurd (h0.symm.trans h1) ne
  all_goals
  cases x <;> cases y <;>
    simp only [TempLogicalAND, unitaryDenote_cons_mulVec, unitaryDenote_nil, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul, h_basis n m ht, t_basis, tdg_basis, s_basis,
      cnot_basis n m hat, cnot_basis n m hbt, cnot_basis n m hta, cnot_basis n m htb, cnotPerm,
      Qubit.get_slice_a hab hat ha, Qubit.get_slice_b hbt hb, Qubit.get_slice_t ht,
      Qubit.flip_slice_a hab hat ha, Qubit.flip_slice_b hbt hb, Qubit.flip_slice_t ht,
      Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, ↓reduceIte,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec, h0, h1, ne, ne', Bool.false_eq_true,
      mul_one, mul_zero, add_zero, one_mul, star_ω, ← ω_sq] <;>
    ring_nf <;>
    simp only [invSqrtTwo_sq, ω_pow_four, ω_pow_six, ω_pow_eight, ω_pow_ten] <;>
    ring_nf

/-- Report §6.2.2, §6.2.4 Layer 1 — the compute block in any branch of the Kraus semantics (it
is measurement-free, so every Kraus operator is its unitary). -/
theorem tempLogicalAND_kraus_basis {n m : ℕ} (nb : ℕ) (c : Fin nb → Bool) (a b t : Qubit)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ha : a.inRange n m = true)
    (hb : b.inRange n m = true) (ht : t.inRange n m = true) (s : Reg n × Reg m)
    (hs : t.get s = false) :
    krausOps n m nb (TempLogicalAND a b t) c *ᵥ basisVec s =
      basisVec (t.set (a.get s && b.get s) s) := by
  rw [krausOps_of_unitary n m nb _ (by simp [TempLogicalAND, Gate.isUnitary]) c,
    tempLogicalAND_correct_lift a b t hab hat hbt ha hb ht s hs]

/-! ## Item 3 — the MBU block, every branch -/

/-- Report §6.2.2, §6.2.4 Layer 2 — the uncompute block (`H t; measure t → j; if j: CZ a b;
if j: X t`) on a basis state whose target holds `a ∧ b`: in **every** branch `c` (whatever bit
`j` reads), `|s⟩ ↦ (1/√2) |s[t ↦ 0]⟩`, with no sign. Branch 0 keeps the `|t = 0⟩` half of
`H t |s⟩` (amplitude `+1/√2`); branch 1 keeps the `|t = 1⟩` half (amplitude `(−1)^{s t}/√2`),
the fix-up `CZ` multiplies it by `(−1)^{s a · s b} = (−1)^{s t}`, and `X t` resets `t`. -/
theorem mbu_branch_basis {n m nb : ℕ} (a b t : Qubit) (j : ℕ) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : t.inRange n m = true) (c : Fin nb → Bool) (s : Reg n × Reg m)
    (hs : t.get s = (a.get s && b.get s)) :
    krausOps n m nb (UncomputeTempLogicalAND a b t j) c *ᵥ basisVec s =
      ((Real.sqrt 2)⁻¹ : ℂ) • basisVec (t.set false s) := by
  have hfa : a.get (t.flip s) = a.get s := Qubit.get_flip_ne hat s
  have hfb : b.get (t.flip s) = b.get s := Qubit.get_flip_ne hbt s
  have hft : t.get (t.flip s) = !t.get s := Qubit.get_flip_self t ht s
  have hff : t.flip (t.flip s) = s := Qubit.flip_involutive t s
  -- `s[t ↦ 0]` is `s` if `t = 0` and `t.flip s` if `t = 1`
  have hset : t.set false s = if t.get s then t.flip s else s := by
    cases hz : t.get s
    · conv_lhs => rw [← hz]
      exact Qubit.set_get t s
    · rw [Qubit.flip, hz]; rfl
  rw [hset]
  cases hz : t.get s <;> cases hβ : bitVal c j <;>
    simp only [UncomputeTempLogicalAND, krausOps_cons_mulVec, krausOps_nil, Matrix.one_mulVec,
      gateK, hβ, Bool.false_eq_true, ↓reduceIte, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_zero, h_basis _ _ ht, projMat_basis, cz_basis, x_basis, hz, hft, hfa, hfb,
      hff, ← hs, Bool.not_false, Bool.not_true, Bool.true_eq_false, smul_zero, zero_smul,
      one_smul, add_zero, zero_add, smul_add, neg_smul, smul_neg, neg_neg, Matrix.mulVec_neg,
      neg_zero]

end

end CQRV

end
