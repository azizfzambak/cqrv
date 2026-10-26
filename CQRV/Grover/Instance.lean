module

public import CQRV.Grover.Lemma

/-!
# CQRV.Grover.Instance

Report §8.4.1 (specializing to concrete parameters), §8.1, §8.2.3 — Stage 7a item 6: the Grover
parametric lemma at `grover_pred_037` (`groverNet`, the DSL bridge of Stage 6a; `n = 8`,
`M = 32`, `r = 2`). The solution count is a hypothesis of the statement, never decided
(§5.1.3). The grade `(15, 134, 72, 7)` (balanced-tree diffusion, Stage 12a; the chain's
`(15, 230, 72, 7)` is kept in the `_chain` statements) is the computed grade of the synthesized circuit
(`decide +kernel` on `Synthesis.grade`, Stage 7a decision 1); `δ = 7/128` exactly
(decision 3, `sin_sq_five_mul`).

Circuits that the elaborator cannot unfold (the synthesizer and scheduler are evaluated by the
kernel) are named by matching on the synthesizer's result; `decide +kernel` proves that the
result is `.ok` (kernel evaluation, no axiom beyond `propext`/`Quot.sound`).
-/

@[expose] public section

namespace CQRV.Grover

open CQRV CQRV.Synthesis

/-- An `Except` value known to be `.ok` is `.ok` of its payload. -/
theorem except_eq_ok_payload {ε α : Type} [Inhabited α] (e : Except ε α) (h : e.isOk = true) :
    e = .ok (match e with | .ok c => c | .error _ => default) := by
  cases e with
  | ok c => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

/-- Report §8, §6.1.4 — the `grover_pred_037` oracle (`groverNet`, Stage 6a) as a certified
oracle; Lemma 6.3.2 fills its restoration field. -/
def grover037Oracle : OracleCert 8 where
  N := groverNet
  C := groverOracle
  hn := rfl
  hC := by rfl
  hWF := by decide

theorem grover037Oracle_P : grover037Oracle.P = groverPred := funext fun _ => rfl

/-- Report §8.2 — the synthesized MCZ of the V1 diffusion on 8 qubits (7 ancillae). -/
def mcz8Circuit : Circuit :=
  match synthesizeOracle (allNet 8) with
  | .ok c => c
  | .error _ => default

theorem mcz8Circuit_ok : synthesizeOracle (allNet 8) = .ok mcz8Circuit :=
  except_eq_ok_payload (synthesizeOracle (allNet 8)) (by decide +kernel)

/-- Report §8.2 — the MCZ of `D₈` as a certified oracle of `P_all` (`WF` by kernel
evaluation). The chain MCZ (Stage 7a); `net` is the default `allNet 8`. -/
def mczCert8 : DiffusionCert 8 where
  mcz := { N := allNet 8, C := mcz8Circuit, hn := rfl, hC := mcz8Circuit_ok,
           hWF := by decide +kernel }
  hN := rfl

/-- Report §8.2 (Stage 12a) — the synthesized MCZ of the default (balanced-tree) diffusion on
8 qubits (7 ancillae). -/
def mcz8TreeCircuit : Circuit :=
  match synthesizeOracle (treeNet 8) with
  | .ok c => c
  | .error _ => default

theorem mcz8TreeCircuit_ok : synthesizeOracle (treeNet 8) = .ok mcz8TreeCircuit :=
  except_eq_ok_payload (synthesizeOracle (treeNet 8)) (by decide +kernel)

/-- Report §8.2 (Stage 12a decision 2) — the tree MCZ of `D₈` as a certified oracle of `P_all`
(`net := treeNet 8`; `hPred` by `treeNet_pred`, filled automatically). -/
def mczTreeCert8 : DiffusionCert 8 where
  net := treeNet 8
  mcz := { N := treeNet 8, C := mcz8TreeCircuit, hn := rfl, hC := mcz8TreeCircuit_ok,
           hWF := by decide +kernel }
  hN := rfl

/-- Report §8.2.1 — the synthesized Grover circuit of `grover_pred_037`, `r = 2`, V1 (since
Stage 12a with the balanced-tree diffusion, the default shape). -/
def grover037Circuit : Circuit :=
  match groverCircuit groverNet 8 2 with
  | .ok c => c
  | .error _ => default

theorem grover037Circuit_ok : groverCircuit groverNet 8 2 = .ok grover037Circuit :=
  except_eq_ok_payload (groverCircuit groverNet 8 2) (by decide +kernel)

/-- Report §8.2.5 (measured, decision 1; Stage 12a, tree diffusion) — the computed grade
`(w, d, t, a) = (15, 134, 72, 7)`. -/
theorem grover037_grade : Synthesis.grade grover037Circuit = ⟨15, 134, 72, 7⟩ := by
  decide +kernel

theorem grover037_nAnc : grover037Circuit.nAnc = 7 := by decide +kernel

/-- Report §8.2.1 (Stage 12a, kept) — the Grover circuit of `grover_pred_037`, `r = 2`, V1 with
the **chain** diffusion of Stage 5b (`--shape chain`). -/
def grover037Circuit_chain : Circuit :=
  match groverCircuit groverNet 8 2 none .chain with
  | .ok c => c
  | .error _ => default

theorem grover037Circuit_chain_ok :
    groverCircuit groverNet 8 2 none .chain = .ok grover037Circuit_chain :=
  except_eq_ok_payload (groverCircuit groverNet 8 2 none .chain) (by decide +kernel)

/-- Report §8.2.5, report v3 value (Stage 12a: the Stage 7a statement of `grover037_grade`, kept
for the chain construction) — the computed grade `(15, 230, 72, 7)`. -/
theorem grover037_grade_chain : Synthesis.grade grover037Circuit_chain = ⟨15, 230, 72, 7⟩ := by
  decide +kernel

theorem grover037_nAnc_chain : grover037Circuit_chain.nAnc = 7 := by decide +kernel

/-- Report §8.1 — the Grover parameters of `grover_pred_037`; the solution count `M = 32` is the
hypothesis `hM` (§5.1.3: never decided by enumeration). -/
def grover037Params (hM : (Finset.univ.filter fun x => groverPred x = true).card = 32) :
    GroverParams where
  n := 8
  M := 32
  hM_pos := by norm_num
  oracle := grover037Oracle
  hM_card := by rw [grover037Oracle_P]; exact hM

/-- Report §8.2.2 — `sin²θ = M/N = 32/256 = 1/8`. -/
theorem grover037_sin_sq (hM : (Finset.univ.filter fun x => groverPred x = true).card = 32) :
    Real.sin (grover037Params hM).θ ^ 2 = 1 / 8 := by
  have h0 : (0 : ℝ) ≤ ((32 : ℕ) : ℝ) / 2 ^ 8 := by positivity
  have h1 : ((32 : ℕ) : ℝ) / 2 ^ 8 ≤ 1 := by norm_num
  change Real.sin (Real.arcsin (Real.sqrt (((32 : ℕ) : ℝ) / 2 ^ 8))) ^ 2 = 1 / 8
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg (((32 : ℕ) : ℝ) / 2 ^ 8)])
    ((Real.sqrt_le_sqrt h1).trans_eq Real.sqrt_one), Real.sq_sqrt h0]
  norm_num

/-- Report §8.2.3, decision 3 — `sin²(5θ) = 121/128` at the instance's `θ`. -/
theorem grover037_sin_sq_five (hM : (Finset.univ.filter fun x => groverPred x = true).card = 32) :
    Real.sin ((2 * ((2 : ℕ) : ℝ) + 1) * (grover037Params hM).θ) ^ 2 = 121 / 128 := by
  rw [show (2 * ((2 : ℕ) : ℝ) + 1) = 5 by norm_num]
  exact sin_sq_five_mul (grover037_sin_sq hM)
    ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _), Real.arcsin_le_pi_div_two _⟩

/-- Report §8.4.1, §8.2.3 — **the `grover_pred_037` instance of the Grover parametric lemma**
(sorry-free since Stage 7b; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): given the
solution count `M = 32` as a hypothesis, the synthesized circuit (`r = 2`, V1; since Stage 12a
with the balanced-tree diffusion) realizes the search spec with `δ = 7/128` exactly within its
computed grade `(15, 134, 72, 7)`, and restores its 7 ancillae applying `G² H^{⊗8}`. -/
theorem grover_pred_037_certified_statement
    (hM : (Finset.univ.filter fun x => groverPred x = true).card = 32) :
    RealizesExact (SearchSpec groverPred) (basisPOVM 8) (groverChannel 8 grover037Circuit)
        (7 / 128) ⟨15, 134, 72, 7⟩ ∧
      AncRestore 8 7 grover037Circuit (groverOp groverPred ^ 2 * hadamardU 8) := by
  obtain ⟨h1, h2⟩ :=
    grover_parametric_lemma (grover037Params hM) mczTreeCert8 2 grover037Circuit_ok
  rw [grover037_sin_sq_five hM, show (1 : ℝ) - 121 / 128 = 7 / 128 by norm_num,
    grover037_grade] at h1
  rw [grover037_nAnc] at h2
  rw [← grover037Oracle_P]
  exact ⟨h1, h2⟩

/-- Report §8.4.1, §8.2.3, report v3 values (Stage 12a: the Stage 7b statement of
`grover_pred_037_certified_statement`, kept for the **chain** diffusion) — the chain circuit
realizes the search spec with `δ = 7/128` within `(15, 230, 72, 7)` and restores its 7 ancillae
applying `G² H^{⊗8}` (`grover_parametric_lemma_shape` at `.chain`). -/
theorem grover_pred_037_certified_statement_chain
    (hM : (Finset.univ.filter fun x => groverPred x = true).card = 32) :
    RealizesExact (SearchSpec groverPred) (basisPOVM 8) (groverChannel 8 grover037Circuit_chain)
        (7 / 128) ⟨15, 230, 72, 7⟩ ∧
      AncRestore 8 7 grover037Circuit_chain (groverOp groverPred ^ 2 * hadamardU 8) := by
  obtain ⟨h1, h2⟩ :=
    grover_parametric_lemma_shape (grover037Params hM) .chain 2 grover037Circuit_chain_ok
  rw [grover037_sin_sq_five hM, show (1 : ℝ) - 121 / 128 = 7 / 128 by norm_num,
    grover037_grade_chain] at h1
  rw [grover037_nAnc_chain] at h2
  rw [← grover037Oracle_P]
  exact ⟨h1, h2⟩

end CQRV.Grover

end
