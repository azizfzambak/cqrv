module

public import CQRV.Circuit.Semantics
public import CQRV.Synthesis.Oracle
public import QuantumInfo.Operators.Unitary

/-!
# CQRV.Circuit.Restoration

Report §6.2.1, §6.2.2, §6.2.4, §6.3.2 — ancilla restoration of the synthesized oracle, on
density operators, following the three layers of §6.2.4:

* Layer 1 — `tempLogicalAND_correct`: the §6.2.2 compute listing maps |a, b, 0⟩ ↦ |a, b, a∧b⟩
  exactly (phase 1). Proved on 3 qubits; the lift to an arbitrary register is stated.
* Layer 2 — `mbu_channel_correct` (MBU is a channel-level statement, §6.2.2) and
  `lemma_6_3_2` (Lemma 6.3.2): the synthesized oracle restores its ancillae and applies the
  phase oracle `(−1)^P(x)`. Statements only (Stage 6a); the proof is split for session 6b in
  docs/SORRIES.md.
* Layer 3 — `AncRestore` (§6.2.1: the output factorizes as |ψ_out⟩ ⊗ |0…0⟩_anc) and its traced
  form, the report's statement of Lemma 6.3.2, proved from `lemma_6_3_2`.

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
   UncomputeTempLogicalAND (.anc 0) (.data 7) (.anc 1) 1 ++ [.free (.anc 1)] ++
   UncomputeTempLogicalAND (.data 0) (.data 3) (.anc 0) 0 ++ [.free (.anc 0)]⟩

/-- Report §8 — the Grover predicate `x0 ∧ x3 ∧ x7`. -/
def groverPred (x : Reg 8) : Bool := x 0 && x 3 && x 7

/-- Report §6.2.2 — the MBU circuit on (a, b, t) = (x[0], x[1], anc[0]): compute, `Z t`,
uncompute (with the Stage 5 reset `ifBit m (X t)`). -/
def mbuCircuit : Circuit :=
  ⟨2, TempLogicalAND (.data 0) (.data 1) (.anc 0) ++ [.z (.anc 0)] ++
    UncomputeTempLogicalAND (.data 0) (.data 1) (.anc 0) 0⟩

noncomputable section

open Matrix
open scoped MState

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

/-- Report §6.2.2, §6.2.4 Layer 1 — the lift of `tempLogicalAND_correct` to any register:
for distinct in-range qubits `a b t` and a basis state with `t = 0`, the compute listing sets
`t` to `a ∧ b` and changes nothing else. The 3-qubit proof (finite case split) does not
transfer; tracked in docs/SORRIES.md. -/
theorem tempLogicalAND_correct_lift {n m : ℕ} (a b t : Qubit) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ha : a.inRange n m = true) (hb : b.inRange n m = true)
    (ht : t.inRange n m = true) (s : Reg n × Reg m) (hs : t.get s = false) :
    unitaryDenote n m (TempLogicalAND a b t) *ᵥ basisVec s =
      basisVec (t.set (a.get s && b.get s) s) := by
  sorry

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

/-! ## Layer 2 — MBU and Lemma 6.3.2 (statements) -/

/-- Report §6.2.2 — MBU correctness, a channel-level statement: on 3 qubits (a, b, t) =
(x[0], x[1], anc[0]), for every state `ρ` of the controls, compute; `Z t`; uncompute (MBU, with
the reset `if m: X t`) maps `ρ ⊗ |0⟩⟨0|` to `(CZ ρ CZᴴ) ⊗ |0⟩⟨0|`: `Z` on a target holding
a ∧ b is `CZ` on the controls, and the target returns to |0⟩ in both measurement branches.
Statement only (Stage 6a); tracked in docs/SORRIES.md. -/
theorem mbu_channel_correct (ρ : MState (Reg 2)) :
    channelDenote 2 1 mbuCircuit (ρ ⊗ᴹ ancZero 1) = (czU ◃ ρ) ⊗ᴹ ancZero 1 := by
  sorry

/-- Report §6.3.2, Lemma 6.3.2 — parametric over the Stage 5 synthesizer: for an AND/NOT/OR
network `N` whose oracle `C` is synthesized and well formed, `C` restores its ancillae and
applies the phase oracle of `N`'s predicate. The statement is on density operators, not on
basis states (§6.2.4: on basis states the phase cancels); Theorem 3.3a is not used inside the
oracle (§6.3.2). Statement only (Stage 6a); the 6b proof split is in docs/SORRIES.md. -/
theorem lemma_6_3_2 (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hN : N.xorFree = true) (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData)) := by
  sorry

/-- Report §6.3.2, Lemma 6.3.2 in the report's traced form:
`Tr_anc (⟦C⟧ (ρ ⊗ |0…0⟩⟨0…0|)) = U_P ρ U_Pᴴ`. Proved from `lemma_6_3_2` (so it inherits its
`sorry` until 6b). -/
theorem lemma_6_3_2_traced (N : Network) (C : Circuit) (hC : synthesizeOracle N = .ok C)
    (hN : N.xorFree = true) (hWF : C.WF) (ρ : MState (Reg C.nData)) :
    (channelDenote C.nData C.nAnc C (ρ ⊗ᴹ ancZero C.nAnc)).traceRight =
      phaseOracle (N.pred C.nData) ◃ ρ :=
  (lemma_6_3_2 N C hC hN hWF).traced ρ

/-- Report §8, §6.3.2 — the `grover_pred_037` instance of Lemma 6.3.2: the synthesized Grover
oracle on `x[0..8) × anc[0..2)` restores its ancillae and applies `(−1)^(x0 ∧ x3 ∧ x7)`.
Derived from `lemma_6_3_2`; the side conditions (`synthesizeOracle groverNet = .ok
groverOracle`, AND/NOT/OR, `WF`, the predicate) are checked by the kernel (`decide`, `rfl`). -/
theorem grover_pred_037_ancRestore : AncRestore 8 2 groverOracle (phaseOracle groverPred) := by
  have hC : synthesizeOracle groverNet = .ok groverOracle := by rfl
  have hN : groverNet.xorFree = true := by decide
  have hWF : groverOracle.WF := by decide
  have hP : groverNet.pred groverOracle.nData = groverPred := by funext x; rfl
  have h := lemma_6_3_2 groverNet groverOracle hC hN hWF
  rw [hP] at h
  exact h

end

end CQRV

end
