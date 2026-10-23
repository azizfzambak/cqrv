module

public import CQRV.Circuit.Semantics
public import CQRV.Synthesis.Oracle
public import QuantumInfo.Operators.Unitary

/-!
# CQRV.Circuit.Restoration

Report §6.2.1, §6.2.2, §6.2.4, §6.3.2 — ancilla restoration of the synthesized oracle, on
density operators, following the three layers of §6.2.4:

* Layer 1 — `tempLogicalAND_correct`: the §6.2.2 compute listing maps |a, b, 0⟩ ↦ |a, b, a∧b⟩
  exactly (phase 1), on 3 qubits. The lift to an arbitrary register and the other oracle blocks
  on basis vectors are in `CQRV.Circuit.OracleBlocks` (Stage 6b-2).
* Layer 2 — `mbu_channel_correct` (MBU is a channel-level statement, §6.2.2; proved in Stage
  6b-1). Lemma 6.3.2 (`lemma_6_3_2`: the synthesized oracle restores its ancillae and applies
  the phase oracle `(−1)^P(x)`), its traced form and the Grover instance are in
  `CQRV.Circuit.OracleCorrect` (Stage 6b-3), which imports this file.
* Layer 3 — `AncRestore` (§6.2.1: the output factorizes as |ψ_out⟩ ⊗ |0…0⟩_anc), its traced
  form (the report's statement of Lemma 6.3.2), and the restoration template
  `ancRestore_of_kraus`: if every Kraus operator acts on the |0…0⟩-ancilla subspace as a scalar
  multiple of `U ⊗ |0…0⟩⟨0…0|`, the squared scalars summing to 1, then `AncRestore`.

The statements are on density operators, not on basis states: on a basis state the phase
`(−1)^P(x)` is global and cancels (§6.2.4), so a basis-state statement would not see it.
Theorem 3.3a (measured composition) is not used inside the oracle (§6.3.2): the measurements
of the MBU are internal to the channel.
-/

@[expose] public section

namespace CQRV

open CQRV.Synthesis

/-! ## The networks of Lemma 6.3.2 and the Grover instance (computable data) -/

namespace Synthesis.Network

/-- Report §6.3.2 — the predicate `P : Reg n → Bool` of a one-output network: the first output
bit, input bit `k` being `x[k]` (`false` beyond `n`). -/
def pred (N : Network) (n : ℕ) (x : Reg n) : Bool :=
  (N.eval fun k => if h : k < n then x ⟨k, h⟩ else false).headD false

/-- Report §6.3.2 — an AND/NOT/OR network (OR is built by De Morgan from AND and NOT): no XOR
node. Lemma 6.3.2 is stated for these networks (Stage 6 task 6). -/
def xorFree (N : Network) : Bool :=
  N.nodes.toList.all fun v => match v with | .xor _ _ => false | _ => true

end Synthesis.Network

/-- Report §8, §6.1.4 — the network of `grover_pred_037` (`x0 ∧ x3 ∧ x7`): inputs `0..7`,
`AND(x0, x3)`, `AND(·, x7)`. -/
def groverNet : Network :=
  ⟨8, #[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7,
        .and 0 3, .and 8 7], [9]⟩

/-- Report §6.1.4 — the synthesized Grover oracle (the §6.1.4 listing; `tests/` checks that
`cqr synthesize examples/grover_pred_037.cqr` produces exactly this circuit). -/
def groverOracle : Circuit :=
  ⟨8, [.alloc (.anc 0)] ++ TempLogicalAND (.data 0) (.data 3) (.anc 0) ++
   [.alloc (.anc 1)] ++ TempLogicalAND (.anc 0) (.data 7) (.anc 1) ++
   [.z (.anc 1)] ++
   UncomputeTempLogicalAND (.anc 0) (.data 7) (.anc 1) 0 ++ [.free (.anc 1)] ++
   UncomputeTempLogicalAND (.data 0) (.data 3) (.anc 0) 1 ++ [.free (.anc 0)]⟩

/-- Report §8 — the Grover predicate `x0 ∧ x3 ∧ x7`. -/
def groverPred (x : Reg 8) : Bool := x 0 && x 3 && x 7

/-- Report §6.2.2 — the MBU circuit on (a, b, t) = (x[0], x[1], anc[0]): compute, `Z t`,
uncompute (with the Stage 5 reset `ifBit m (X t)`). -/
def mbuCircuit : Circuit :=
  ⟨2, TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)] ++
    UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0⟩

noncomputable section

open Matrix
open scoped MState Kronecker

/-! ## Layer 1 — TempLogicalAND on basis states -/

/-- Report §9.1.1 — the computational basis vector |s⟩ (the vector of `Ket.basis s`). -/
def basisVec {ι : Type} [DecidableEq ι] (s : ι) : ι → ℂ := fun j => if j = s then 1 else 0

/-- Report §6.2.2, §6.2.4 Layer 1 — the TempLogicalAND compute listing (13 gates, 4 T) on
(a, b, t) = (x[0], x[1], anc[0]) maps |a, b, 0⟩ to |a, b, a ∧ b⟩ exactly, with phase 1.
Proof: gate by gate on the state vector, for each of the 4 inputs and 8 output indices; the
amplitudes are polynomials in ω and 1/√2, reduced with `ω⁴ = −1`, `ω̄ = −ω³`, `i = ω²`. -/
theorem tempLogicalAND_correct (a b : Bool) :
    unitaryDenote 2 1 (TempLogicalAND (.data 0) (.data 1) (.anc 0)) *ᵥ basisVec (![a, b], ![false])
      = basisVec (![a, b], ![a && b]) := by
  funext ⟨u, w⟩
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1, u = ![b0, b1] :=
    ⟨u 0, u 1, by funext k; fin_cases k <;> rfl⟩
  obtain ⟨b2, rfl⟩ : ∃ b2, w = ![b2] := ⟨w 0, by funext k; fin_cases k; rfl⟩
  cases a <;> cases b <;> cases b0 <;> cases b1 <;> cases b2 <;>
    simp (config := { decide := true }) only [TempLogicalAND, unitaryDenote_cons_mulVec,
      unitaryDenote_nil, Matrix.one_mulVec, gateU_cnot_mulVec, gateU_h_mulVec, gateU_s,
      gateU_t, gateU_tdg, phaseMat_mulVec, basisVec] <;>
    simp only [ite_true, ite_false, one_mul, mul_one, mul_zero, add_zero, zero_add, star_ω,
      ← ω_sq] <;>
    ring_nf <;>
    simp only [invSqrtTwo_sq, ω_pow_four, ω_pow_six, ω_pow_eight, ω_pow_ten] <;>
    ring_nf

/-! ## Layer 3 — `AncRestore` and the phase oracle -/

/-- Report §6.2.1 — the all-zero ancilla state |0…0⟩⟨0…0|. -/
def ancZero (a : ℕ) : MState (Reg a) := MState.pure (Ket.basis fun _ => false)

/-- The diagonal of the phase oracle: `(−1)^P(x)`. -/
def phaseDiag {n : ℕ} (P : Reg n → Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if P x then -1 else 1

/-- Report §6.1.1 — the phase oracle is unitary. -/
theorem phaseDiag_mem_unitaryGroup {n : ℕ} (P : Reg n → Bool) :
    phaseDiag P ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', phaseDiag, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact star_sign_mul (P x)

/-- Report §6.1.1 — the phase oracle `U_P = diag((−1)^P(x))` on `Reg n`. -/
def phaseOracle {n : ℕ} (P : Reg n → Bool) : 𝐔[Reg n] :=
  ⟨phaseDiag P, phaseDiag_mem_unitaryGroup P⟩

/-- Report §6.2.2 — `CZ` on two qubits, as the phase oracle of `x0 ∧ x1`. -/
def czU : 𝐔[Reg 2] := phaseOracle fun x => x 0 && x 1

/-- Report §6.2.1, §6.2.4 Layer 3 — `AncRestore n a C U`: on every data state `ρ`, the circuit
with its ancillae prepared in |0…0⟩ outputs `(U ρ Uᴴ) ⊗ |0…0⟩⟨0…0|` — the ancillae are restored
and the data register has undergone `U`. A statement on density operators, through the Kraus
semantics `channelDenote` (all measurement branches). -/
def AncRestore (n a : ℕ) (C : Circuit) (U : 𝐔[Reg n]) : Prop :=
  ∀ ρ : MState (Reg n), channelDenote n a C (ρ ⊗ᴹ ancZero a) = (U ◃ ρ) ⊗ᴹ ancZero a

/-- Report §6.3.2 — the traced form: tracing out the restored ancillae leaves `U ρ Uᴴ`. -/
theorem AncRestore.traced {n a : ℕ} {C : Circuit} {U : 𝐔[Reg n]} (h : AncRestore n a C U)
    (ρ : MState (Reg n)) :
    (channelDenote n a C (ρ ⊗ᴹ ancZero a)).traceRight = U ◃ ρ := by
  rw [h ρ, MState.traceRight_prod_eq]

/-- Conjugating by `U₁`, then by `U₂`, is conjugating by `U₂ U₁`. -/
theorem uConj_uConj {n : ℕ} (ρ : MState (Reg n)) (U₁ U₂ : 𝐔[Reg n]) :
    U₂ ◃ (U₁ ◃ ρ) = (U₂ * U₁) ◃ ρ := by
  apply MState.ext_m
  change U₂.val * (U₁.val * ρ.m * U₁.valᴴ) * U₂.valᴴ =
    (U₂.val * U₁.val) * ρ.m * (U₂.val * U₁.val)ᴴ
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Report §6.2.4, §6.3.2 — restoration composes: if `C₁` restores its ancillae applying `U₁`
and `C₂` applying `U₂`, their shifted append (`Circuit.append`) restores them applying
`U₂ U₁`. The step of the induction over the AND list (Lemma 6.3.2). -/
theorem AncRestore.comp {n a : ℕ} {C₁ C₂ : Circuit} {U₁ U₂ : 𝐔[Reg n]}
    (h₁ : C₁.bitsOk = true) (h₂ : C₂.bitsOk = true)
    (r₁ : AncRestore n a C₁ U₁) (r₂ : AncRestore n a C₂ U₂) :
    AncRestore n a (C₁.append C₂) (U₂ * U₁) := by
  intro ρ
  rw [channelDenote_append n a h₁ h₂, CPTPMap.compose_eq, r₁ ρ, r₂, uConj_uConj]

/-! ## Layer 3 — the restoration template -/

/-- Report §6.2.1 — the matrix of |0…0⟩⟨0…0| (Physlib's `MState.pure (Ket.basis 0)` unfolds to
`vecMulVec`; this is its entrywise form). -/
theorem ancZero_m_apply (a : ℕ) (i j : Reg a) :
    (ancZero a).m i j = if i = (fun _ => false) ∧ j = (fun _ => false) then 1 else 0 := by
  simp only [MState.m, ancZero, MState.pure, Ket.basis, HermitianMat.mat_mk,
    Matrix.vecMulVec_apply, Bra.eq_conj, Ket.coe_fun_eq]
  by_cases hi : i = fun _ => false
  · subst hi
    by_cases hj : j = fun _ => false
    · subst hj; simp
    · have hj' : ¬ (fun _ : Fin a => false) = j := fun h => hj h.symm
      simp [hj, hj']
  · have hi' : ¬ (fun _ : Fin a => false) = i := fun h => hi h.symm
    simp [hi, hi']

theorem ancZero_m_conjTranspose (a : ℕ) : (ancZero a).mᴴ = (ancZero a).m :=
  (ancZero a).Hermitian

/-- |0…0⟩⟨0…0| is idempotent. -/
theorem ancZero_m_mul_self (a : ℕ) : (ancZero a).m * (ancZero a).m = (ancZero a).m := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (fun _ => false)]
  · simp only [ancZero_m_apply]; by_cases hi : i = fun _ => false <;> simp [hi]
  · intro k _ hk; simp [ancZero_m_apply, hk]
  · simp

/-- Report §6.2.4 Layer 3 — the projector `P = 1 ⊗ |0…0⟩⟨0…0|` onto the subspace of
`Reg n × Reg a` where the ancillae are |0…0⟩. -/
def ancProj (n a : ℕ) : Matrix (Reg n × Reg a) (Reg n × Reg a) ℂ :=
  (1 : Matrix (Reg n) (Reg n) ℂ) ⊗ₖ (ancZero a).m

/-- The Kronecker shape of `ρ ⊗ᴹ ancZero a`: Physlib's `MState.prod` is `HermitianMat.kronecker`,
whose matrix is `Matrix.kroneckerMap (· * ·)` of the two matrices (definitional). -/
theorem prod_ancZero_m {n a : ℕ} (ρ : MState (Reg n)) :
    (ρ ⊗ᴹ ancZero a).m = ρ.m ⊗ₖ (ancZero a).m := rfl

theorem ancProj_conjTranspose (n a : ℕ) : (ancProj n a)ᴴ = ancProj n a := by
  rw [ancProj, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ancZero_m_conjTranspose]

/-- Report §6.2.4 Layer 3 — matrix-level helper: `ρ ⊗ |0…0⟩⟨0…0| = P (ρ ⊗ |0…0⟩⟨0…0|) P`. -/
theorem prod_ancZero_m_eq {n a : ℕ} (ρ : MState (Reg n)) :
    (ρ ⊗ᴹ ancZero a).m = ancProj n a * (ρ ⊗ᴹ ancZero a).m * ancProj n a := by
  rw [prod_ancZero_m, ancProj, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, ancZero_m_mul_self, ancZero_m_mul_self]

/-- Report §9.1.1 — the matrix of `channelDenote` on a well-formed circuit: `∑_c K_c ρ K_cᴴ`. -/
theorem channelDenote_m {n a : ℕ} {C : Circuit} (h : C.WF) (ρ : MState (Reg n × Reg a)) :
    (channelDenote n a C ρ).m =
      ∑ c, krausOps n a C.nBits C.gates c * ρ.m * (krausOps n a C.nBits C.gates c)ᴴ :=
  channelDenote_m_of_bitsOk n a h.bitsOk ρ

/-- Report §6.2.4 Layer 3 template — restoration from the Kraus operators: if `C` is well formed
and every Kraus operator acts on the |0…0⟩-ancilla subspace as a scalar multiple of
`U ⊗ |0…0⟩⟨0…0|` (`K_c · P = l_c · (U ⊗ₖ |0…0⟩⟨0…0|)`), with `∑_c ‖l_c‖² = 1`, then
`AncRestore n a C U`. Proof: `ρ ⊗ |0…0⟩⟨0…0| = P (ρ ⊗ |0…0⟩⟨0…0|) P`, push `P` into each Kraus
operator, sum the `‖l_c‖²`. -/
theorem ancRestore_of_kraus {n a : ℕ} {C : Circuit} (hC : C.WF) (U : 𝐔[Reg n])
    (l : (Fin C.nBits → Bool) → ℂ) (hl : ∑ c, ‖l c‖ ^ 2 = 1)
    (hK : ∀ c, krausOps n a C.nBits C.gates c * ancProj n a = l c • (U.val ⊗ₖ (ancZero a).m)) :
    AncRestore n a C U := by
  intro ρ
  apply MState.ext_m
  rw [channelDenote_m hC, prod_ancZero_m_eq]
  have hterm : ∀ c, krausOps n a C.nBits C.gates c *
      (ancProj n a * (ρ ⊗ᴹ ancZero a).m * ancProj n a) * (krausOps n a C.nBits C.gates c)ᴴ =
      ((‖l c‖ ^ 2 : ℝ) : ℂ) • ((U ◃ ρ) ⊗ᴹ ancZero a).m := fun c => by
    have h1 : krausOps n a C.nBits C.gates c *
        (ancProj n a * (ρ ⊗ᴹ ancZero a).m * ancProj n a) * (krausOps n a C.nBits C.gates c)ᴴ =
        (krausOps n a C.nBits C.gates c * ancProj n a) * (ρ ⊗ᴹ ancZero a).m *
          (krausOps n a C.nBits C.gates c * ancProj n a)ᴴ := by
      rw [Matrix.conjTranspose_mul, ancProj_conjTranspose]; simp only [Matrix.mul_assoc]
    have hs : star (l c) * l c = ((‖l c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    rw [h1, hK, Matrix.conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hs, prod_ancZero_m, prod_ancZero_m, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ancZero_m_conjTranspose,
      ancZero_m_mul_self, ancZero_m_mul_self]
    rfl
  simp_rw [hterm]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hl, Complex.ofReal_one, one_smul]

/-! ## Layer 2 — MBU -/

/-- Column `j` of a matrix is its action on the basis vector |j⟩. -/
theorem mulVec_basisVec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    (M *ᵥ basisVec j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, basisVec]

theorem krausOps_nil (n a m : ℕ) (c : Fin m → Bool) : krausOps n a m [] c = 1 := rfl

theorem krausOps_cons_mulVec (n a m : ℕ) (g : Gate) (gs : List Gate) (c : Fin m → Bool)
    (v : Reg n × Reg a → ℂ) :
    krausOps n a m (g :: gs) c *ᵥ v = krausOps n a m gs c *ᵥ (gateK n a c g *ᵥ v) := by
  rw [krausOps, Matrix.mulVec_mulVec]

theorem projMat_mulVec (n a : ℕ) (q : Qubit) (v : Bool) (w : Reg n × Reg a → ℂ)
    (i : Reg n × Reg a) : (projMat n a q v *ᵥ w) i = (if q.get i = v then 1 else 0) * w i := by
  rw [projMat, monoMat_mulVec (fun _ => rfl)]
  rfl

/-- Report §6.2.2 — the per-branch identity of MBU on basis inputs: in branch `c` (the X-basis
outcome), the MBU circuit maps |x0, x1⟩|0⟩ to `(1/√2)(−1)^(x0 ∧ x1)` |x0, x1⟩|0⟩. Proof: the
compute block by `tempLogicalAND_correct`, then `Z t; H t; measure t; if c: CZ; if c: X t` gate
by gate, for the 4 inputs × 2 branches. -/
theorem mbu_kraus_basis (c : Fin 1 → Bool) (x0 x1 : Bool) :
    krausOps 2 1 1 mbuCircuit.gates c *ᵥ basisVec (![x0, x1], ![false]) =
      (((Real.sqrt 2)⁻¹ : ℂ) * (if x0 && x1 then -1 else 1)) •
        basisVec (![x0, x1], ![false]) := by
  have hsplit : mbuCircuit.gates = TempLogicalAND (.data 0) (.data 1) (.anc 0) ++
      (.z (.anc 0) :: UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0) := by
    simp [mbuCircuit]
  rw [hsplit, krausOps_append_gates,
    krausOps_of_unitary 2 1 1 (TempLogicalAND (.data 0) (.data 1) (.anc 0)) (by decide),
    ← Matrix.mulVec_mulVec, tempLogicalAND_correct]
  obtain ⟨b, rfl⟩ : ∃ b, c = ![b] := ⟨c 0, by funext k; fin_cases k; rfl⟩
  funext ⟨u, w⟩
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1, u = ![b0, b1] :=
    ⟨u 0, u 1, by funext k; fin_cases k <;> rfl⟩
  obtain ⟨b2, rfl⟩ : ∃ b2, w = ![b2] := ⟨w 0, by funext k; fin_cases k; rfl⟩
  cases b <;> cases x0 <;> cases x1 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    simp (config := { decide := true }) only [UncomputeTempLogicalAND, krausOps_cons_mulVec,
      krausOps_nil, Matrix.one_mulVec, gateK, bitVal, ↓reduceIte, ↓reduceDIte,
      gateU_h_mulVec, gateU_z, gateU_x_mulVec, gateU_cz_mulVec, phaseMat_mulVec, projMat_mulVec,
      basisVec, Pi.smul_apply, smul_eq_mul] <;>
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_mul, mul_neg,
      neg_neg, neg_zero]

/-- `P |s⟩ = |s⟩` if the ancillae of `s` are |0…0⟩, else `0`. -/
theorem ancProj_mulVec_basisVec (n a : ℕ) (s : Reg n × Reg a) :
    ancProj n a *ᵥ basisVec s = if s.2 = (fun _ => false) then basisVec s else 0 := by
  funext i
  rw [mulVec_basisVec, ancProj, Matrix.kroneckerMap_apply, ancZero_m_apply, Matrix.one_apply]
  by_cases hs : s.2 = fun _ => false
  · simp only [hs, and_true, ↓reduceIte, basisVec, Prod.ext_iff]
    split_ifs <;> simp_all
  · simp [hs]

/-- Report §6.2.2, §6.2.4 Layer 2 — the per-branch identity of MBU as a matrix identity: in
both branches, `K_c · P = (1/√2) · (CZ ⊗ |0⟩⟨0|)` (from `mbu_kraus_basis`, column by column). -/
theorem mbu_kraus (c : Fin 1 → Bool) :
    krausOps 2 1 1 mbuCircuit.gates c * ancProj 2 1 =
      ((Real.sqrt 2)⁻¹ : ℂ) • (czU.val ⊗ₖ (ancZero 1).m) := by
  ext i ⟨j1, j2⟩
  rw [← mulVec_basisVec (krausOps 2 1 1 mbuCircuit.gates c * ancProj 2 1),
    ← Matrix.mulVec_mulVec, ancProj_mulVec_basisVec]
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, ancZero_m_apply, czU, phaseOracle,
    phaseDiag, Matrix.diagonal_apply, smul_eq_mul]
  obtain ⟨x0, x1, rfl⟩ : ∃ x0 x1, j1 = ![x0, x1] :=
    ⟨j1 0, j1 1, by funext k; fin_cases k <;> rfl⟩
  by_cases hj : j2 = fun _ => false
  · subst hj
    simp only [↓reduceIte]
    rw [show ((fun _ => false) : Reg 1) = ![false] from by funext k; fin_cases k; rfl,
      mbu_kraus_basis]
    obtain ⟨i1, i2⟩ := i
    simp only [Pi.smul_apply, smul_eq_mul, basisVec, Prod.mk.injEq]
    by_cases h1 : i1 = ![x0, x1] <;> by_cases h2 : i2 = ![false] <;> simp [h1, h2]
  · simp [hj]

/-- Report §9.1.1 — the MBU circuit is well formed. -/
theorem mbuCircuit_WF : mbuCircuit.WF := by decide

/-- Report §6.2.2 — MBU correctness, a channel-level statement: on 3 qubits (a, b, t) =
(x[0], x[1], anc[0]), for every state `ρ` of the controls, compute; `Z t`; uncompute (MBU, with
the reset `if m: X t`) maps `ρ ⊗ |0⟩⟨0|` to `(CZ ρ CZᴴ) ⊗ |0⟩⟨0|`: `Z` on a target holding
a ∧ b is `CZ` on the controls, and the target returns to |0⟩ in both measurement branches.
Proof: `ancRestore_of_kraus` with `U = CZ`, `l_c = 1/√2` (`mbu_kraus`), and `2 · (1/√2)² = 1`. -/
theorem mbu_channel_correct (ρ : MState (Reg 2)) :
    channelDenote 2 1 mbuCircuit (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 := by
  refine ancRestore_of_kraus mbuCircuit_WF czU (fun _ => ((Real.sqrt 2)⁻¹ : ℂ)) ?_ mbu_kraus ρ
  have hn : mbuCircuit.nBits = 1 := by decide
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, hn, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

end

end CQRV

end
