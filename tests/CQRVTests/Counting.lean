module

import CQRV.Synthesis.Counting
import CQRV.Circuit.CountingCorrect
import CQRV.Circuit.GradeCompose
import CQRV.Grover.Counting
meta import CQRV.Synthesis.Counting
meta import CQRV.Circuit.CountingCorrect
meta import CQRV.Circuit.GradeCompose

/-!
# The counting circuit (Stage 19b, PHASE2_SPEC.md §A.3 as amended; docs/tasks/STAGE19_TASK.md
B1–B4)

* `Network.withControl` on the network of `x₀ ∧ x₁ ∧ x₂ ∧ x₃` (`n = 4`, `M = 1`) and on the
  Grover network of `grover_pred_037`: the two appended nodes, well-formedness, and the predicate
  as the conjunction on all 64 inputs of the 6-input network (bit `k` of `x` = input `k`).
* `Gate.shiftData` on sample gates; the inverse (A)QFT block at `n = 4`, `m = 2`.
* The builders at `n = 4`, `m = 2`: the shape of §A.3 (4) (the Hadamard layer, one copy of
  block 0, two copies of block 1, the inverse), the phase fix at the end of every block, the
  measured values (gate counts, grades, `GradeExt`, `nAnc`, `liveEnd`, `nBits`), `validate` in
  both modes, the composed bound of 19a, the diagnostics (existing codes only), and the block
  sizes of the probe instance `grover_pred_037` at `m = 4` (244 / 343 gates, below 600).
* `example` instances of the theorems of B1, B2, B4 and the axiom lines.
* Stage 19c (C1–C5): `example` instances at `n = 2`, `m = 2` (types written `Reg (2 + 2)`, the
  form of the theorems) — the entries of `liftS` / `liftP` / `ctrlU` / `ctrlPow`, the layers, the
  shift lemma on `qftGates 2`, the controlled oracle, the algebra, `cgU = ctrlU j G`, the product
  `powersU = ctrlPow G`, and `countingCircuit_ancRestore` with `U_count` for the exact and the
  approximate inverse QFT — and the axiom lines of `countingCircuit_ancRestore`, the C4 product
  lemma `powersU_val`, the shift lemma and `raw_eq_U_count`.
* Stage 20a2 (B1–B4): `example` instances at `n = 2`, `m = 2` on the Grover data of `x₀ ∧ x₁`
  (`M = 1`) and of `true` (`M = 2ⁿ = 4`, where `ψ_b = 0` and `θ = π/2`) — the amplitude of `U_count`
  on `|0…0⟩`, its two-phase form, `phaseDist_eq`, `qpe_two_phase_bound`, `qpe_success` — and the
  axiom lines of `U_count_zero_apply`, `phaseDist_eq`, `qpe_two_phase_bound`, `qpe_success`.
-/

namespace CQRV.Tests.Counting

open CQRV CQRV.Synthesis CQRV.Counting CQRV.Grover Matrix Real
open scoped Kronecker

/-- The network of `grover_pred_037` (`x0 ∧ x3 ∧ x7`), the literal of `groverNet`. -/
def groverNet037 : Network :=
  ⟨8, #[.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .input 6, .input 7,
        .and 0 3, .and 8 7], [9]⟩

/-- `x₀ ∧ x₁ ∧ x₂ ∧ x₃` on four inputs (`M = 1`). -/
def n4 : Network :=
  ⟨4, #[.input 0, .input 1, .input 2, .input 3, .and 0 1, .and 4 2, .and 5 3], [6]⟩

/-! ## B1 — `withControl` -/

#guard n4.withControl 2 0 ==
  ⟨6, #[.input 0, .input 1, .input 2, .input 3, .and 0 1, .and 4 2, .and 5 3, .input 4, .and 6 7],
    [8]⟩
#guard (groverNet037.withControl 4 1).nInputs == 12
#guard (groverNet037.withControl 4 1).outputs == [11]
#guard (groverNet037.withControl 4 1).nodes.size == 12
#guard (n4.withControl 2 0).wf && (n4.withControl 2 1).wf && (groverNet037.withControl 4 3).wf
-- the predicate is `c ∧ P`: control qubit `4` (phase qubit 0) resp. `5` (phase qubit 1)
#guard (List.range 64).all fun x =>
  (n4.withControl 2 0).pred 6 (fun i => (x >>> i.val) % 2 == 1) ==
    (((x >>> 4) % 2 == 1) && (x % 16 == 15))
#guard (List.range 64).all fun x =>
  (n4.withControl 2 1).pred 6 (fun i => (x >>> i.val) % 2 == 1) ==
    (((x >>> 5) % 2 == 1) && (x % 16 == 15))

/-! ## B2 — `shiftData` -/

#guard (Gate.cp 1 3 (.data 1) (.data 0)).shiftData 4 == .cp 1 3 (.data 5) (.data 4)
#guard (Gate.ifBit 2 (.cz (.data 0) (.anc 1))).shiftData 4 == .ifBit 2 (.cz (.data 4) (.anc 1))
#guard (Gate.measure (.anc 0) 3).shiftData 4 == .measure (.anc 0) 3
#guard (Gate.h (.data 2)).shiftData 0 == .h (.data 2)
#guard (countingInverse 4 2 none).gates ==
  [.h (.data 5), .cp (-1) 2 (.data 5) (.data 4), .h (.data 4)]
#guard (countingInverse 4 2 (some 1)).gates == [.h (.data 5), .h (.data 4)]
#guard (countingHLayer 4 2).gates == Diffusion.onAll .h 6

/-! ## B3 — the builders at `n = 4`, `m = 2` -/

def cg0 : Circuit := (controlledGrover n4 4 2 0).toOption.getD default
def cg1 : Circuit := (controlledGrover n4 4 2 1).toOption.getD default
def cd0 : Circuit := (controlledDiffusion 4 2 0).toOption.getD default
def cc : Circuit := (countingCircuit n4 4 2).toOption.getD default
def ccCoh : Circuit := (countingCircuit n4 4 2 none .tree .coherent).toOption.getD default

#guard (controlledGrover n4 4 2 0).toBool && (controlledGrover n4 4 2 1).toBool &&
  (controlledDiffusion 4 2 0).toBool && (countingCircuit n4 4 2).toBool &&
  (countingCircuit n4 4 2 none .tree .coherent).toBool
-- the shape of §A.3 (4): the Hadamard layer, `2^0` copies of block 0, `2^1` copies of block 1,
-- the inverse QFT on the phase register
#guard cc == ((List.replicate 2 cg1).foldl Circuit.append
  ((List.replicate 1 cg0).foldl Circuit.append (countingHLayer 4 2))).append
    (countingInverse 4 2 none)
-- every controlled iterate ends with the phase fix on its control (amendment (2))
#guard cg0.gates.getLast? == some (.z (.data 4))
#guard cg1.gates.getLast? == some (.z (.data 5))
-- the controlled diffusion is `H X ; MCZ ; X H` on the search register, `nData = n + m`
#guard cd0.nData == 6 && cd0.gates.take 8 == Diffusion.onAll .h 4 ++ Diffusion.onAll .x 4
#guard cd0.gates.reverse.take 8 == (Diffusion.onAll .x 4 ++ Diffusion.onAll .h 4).reverse
-- measured values
#guard cg0.gates.length == 171 && cg1.gates.length == 171
#guard cg0.grade == ⟨10, 92, 32, 4⟩ && cg1.grade == ⟨10, 92, 32, 4⟩
#guard cg0.gradeExt == ⟨56, 21, 0, 8, 16⟩
#guard (cg0.nAnc, cg0.liveEnd, cg0.nBits) == (4, 0, 8)
#guard cc.gates.length == 522
#guard cc.grade == ⟨10, 272, 96, 4⟩
#guard cc.gradeExt == ⟨169, 67, 1, 24, 48⟩
#guard (cc.nAnc, cc.liveEnd, cc.nBits) == (4, 0, 24)
#guard cc.validate.toBool && ccCoh.validate.toBool
#guard ccCoh.nBits == 0 && ccCoh.gradeExt.meas == 0 && ccCoh.gradeExt.ff == 0
-- the composed bound of 19a (`grade_foldl_append_le`, `grade_replicate_le`)
#guard cc.grade ≤ ((countingHLayer 4 2).grade + 1 • cg0.grade + 2 • cg1.grade) +
  (countingInverse 4 2 none).grade
#guard cc.gradeExt.tDepth ≤ (countingHLayer 4 2).gradeExt.tDepth + 1 * cg0.tCount +
  2 * cg1.tCount + (countingInverse 4 2 none).tCount

-- Stage 20b3 (C1): the assembled circuit from its blocks equals the built circuit
#guard assembleCounting (countingHLayer 4 2) [cg0, cg1] (countingInverse 4 2 none) == cc
#guard assembleCounting (countingHLayer 4 2) [cg0, cg1] (countingInverse 4 2 (some 1)) ==
  (countingCircuit n4 4 2 (some 1)).toOption.getD default
-- the composed bound of C1 at this instance, as the certificate closes it
#guard Synthesis.grade cc ≤ Synthesis.grade (countingHLayer 4 2) +
  (1 • Synthesis.grade cg0 + (2 • Synthesis.grade cg1 + 0)) +
    Synthesis.grade (countingInverse 4 2 none)

/-- The diagnostic code of a refused build. -/
def codeOf (r : Except DSL.Diagnostic Circuit) : String :=
  match r with
  | .error d => d.code.name
  | .ok _ => "ok"

#guard codeOf (controlledGrover n4 3 2 0) == "unsupported_network"
#guard codeOf (controlledGrover ⟨4, #[.input 0], []⟩ 4 2 0) == "unsupported_network"
#guard codeOf (controlledGrover n4 4 2 2) == "unsupported_combination"
#guard codeOf (controlledGrover ⟨0, #[.const true], [0]⟩ 0 2 0) == "unsupported_network"
#guard codeOf (countingCircuit n4 4 0) == "unsupported_network"
#guard codeOf (countingCircuit n4 4 2) == "ok"

-- the probe instance (B6): `grover_pred_037`, `m = 4`, both modes — every block below 600 gates
def cg037 (j : Nat) (mode : UncomputeMode) : Circuit :=
  (controlledGrover groverNet037 8 4 j .tree mode).toOption.getD default

#guard (cg037 0 .mbu).gates.length == 244 && (cg037 3 .mbu).gates.length == 244
#guard (cg037 0 .coherent).gates.length == 343 && (cg037 3 .coherent).gates.length == 343
#guard (cg037 0 .coherent).grade == ⟨20, 136, 88, 8⟩
#guard (countingHLayer 8 4).gates.length == 12 && (countingInverse 8 4 none).gates.length == 10

/-! ## Instances of the theorems -/

-- B1
example (x : Fin (n4.nInputs + 2) → Bool) :
    (n4.withControl 2 0).pred (n4.nInputs + 2) x =
      (x ⟨n4.nInputs + 0, by omega⟩ && n4.pred n4.nInputs (fun i => x (Fin.castAdd 2 i))) :=
  Network.withControl_pred (by decide +kernel) rfl (by decide) x
example : (n4.withControl 2 0).WF :=
  Network.withControl_WF (by decide +kernel) rfl (by decide)

-- B2
example : ((Gate.cp 1 3 (.data 1) (.data 0)).shiftData 4).qubitsOk (4 + 2) = true :=
  Gate.qubitsOk_shiftData 4 (by decide)
example : ((Gate.cp 1 3 (.data 1) (.data 0)).shiftData 4).isUnitary = true :=
  Gate.isUnitary_shiftData 4 _

-- B4
example (h : controlledDiffusion 4 2 0 = .ok cd0) :
    cd0.WF ∧ ∀ a, cd0.nAnc ≤ a → AncRestore 6 a cd0 (cdiffU 4 2 0 .tree) :=
  controlledDiffusion_ancRestore h (by decide) (by decide)
example (h : controlledGrover n4 4 2 0 = .ok cg0) :
    cg0.WF ∧ ∀ a, cg0.nAnc ≤ a → AncRestore 6 a cg0 (cgU n4 4 2 0 .tree) :=
  controlledGrover_ancRestore h (by decide +kernel)
example (h : countingCircuit n4 4 2 = .ok cc) :
    cc.WF ∧ AncRestore 6 cc.nAnc cc (qftInvU 4 2 none * powersU n4 4 2 .tree * hadamardU 6) :=
  countingCircuit_ancRestore_raw h (by decide +kernel) rfl rfl

-- Stage 20b3 (C1): the converse constructor from the blocks, and the two composed bounds
example (h0 : controlledGrover n4 4 2 0 .tree .mbu = .ok cg0)
    (h1 : controlledGrover n4 4 2 1 .tree .mbu = .ok cg1) :
    countingCircuit n4 4 2 none .tree .mbu =
      .ok (assembleCounting (countingHLayer 4 2) [cg0, cg1] (countingInverse 4 2 none)) :=
  countingCircuit_of_blocks none (by decide) rfl fun j hj =>
    match j, hj with
    | 0, _ => h0
    | 1, _ => h1
    | _ + 2, h => absurd h (by omega)
example (h0 : cg0.liveEnd = 0) (h1 : cg1.liveEnd = 0) :
    Synthesis.grade (assembleCounting (countingHLayer 4 2) [cg0, cg1] (countingInverse 4 2 none)) ≤
      Synthesis.grade (countingHLayer 4 2) +
        ([cg0, cg1].zipIdx.map fun p => 2 ^ p.2 • Synthesis.grade p.1).sum +
        Synthesis.grade (countingInverse 4 2 none) :=
  grade_assembleCounting_le (countingHLayer 4 2) [cg0, cg1] (countingInverse 4 2 none)
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> rfl)
    rfl rfl
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact h0
      · exact h1)
example : (Synthesis.gradeExt (assembleCounting (countingHLayer 4 2) [cg0, cg1]
      (countingInverse 4 2 none))).tDepth ≤
    (Synthesis.gradeExt (countingHLayer 4 2)).tDepth +
      ([cg0, cg1].zipIdx.map fun p => 2 ^ p.2 * (Synthesis.grade p.1).t).sum +
      (Synthesis.grade (countingInverse 4 2 none)).t := by
  have h := (gradeExt_assembleCounting (countingHLayer 4 2) [cg0, cg1]
    (countingInverse 4 2 none)).2.2.2.2
  omega
example (a : ℕ) : unitaryDenote 6 a [.z (.data 4)] =
    dataMat 6 [.z (.data 4)] ⊗ₖ (1 : Matrix (Reg a) (Reg a) ℂ) :=
  unitaryDenote_dataOnly _ rfl rfl

/-! ## Stage 19c — the tensor form of `U_count`, at `n = 2`, `m = 2` -/

/-- `x₀ ∧ x₁` on two inputs (`M = 1`). -/
def n2 : Network := ⟨2, #[.input 0, .input 1, .and 0 1], [2]⟩

def cc2 : Circuit := (countingCircuit n2 2 2).toOption.getD default
def cc2a : Circuit := (countingCircuit n2 2 2 (some 1)).toOption.getD default

#guard (countingCircuit n2 2 2).toBool && cc2.validate.toBool && cc2.nData == 4
#guard (countingCircuit n2 2 2 (some 1)).toBool && cc2a.validate.toBool

-- C1: the entries and unitarity
example (A : Matrix (Reg 2) (Reg 2) ℂ) (x y : Reg (2 + 2)) :
    liftS A x y = if phase x = phase y then A (search x) (search y) else 0 := liftS_apply A x y
example (B : Matrix (Reg 2) (Reg 2) ℂ) (x y : Reg (2 + 2)) :
    liftP B x y = if search x = search y then B (phase x) (phase y) else 0 := liftP_apply B x y
example (V : Matrix (Reg 2) (Reg 2) ℂ) (x y : Reg (2 + 2)) :
    ctrlU 1 V x y =
      if phase x = phase y then (if (phase x).bit 1 then V else 1) (search x) (search y) else 0 :=
  ctrlU_apply 1 V x y
example (V : Matrix (Reg 2) (Reg 2) ℂ) (x y : Reg (2 + 2)) :
    ctrlPow V x y =
      if phase x = phase y then (V ^ (phase x).toNatLE) (search x) (search y) else 0 :=
  ctrlPow_apply V x y
example (V : Matrix (Reg 2) (Reg 2) ℂ) (hV : V ∈ 𝐔[Reg 2]) :
    (ctrlPow V : Matrix (Reg (2 + 2)) (Reg (2 + 2)) ℂ) ∈ 𝐔[Reg (2 + 2)] := ctrlPow_mem hV
example (B : Matrix (Reg 2) (Reg 2) ℂ) (hB : B ∈ 𝐔[Reg 2]) :
    (liftP B : Matrix (Reg (2 + 2)) (Reg (2 + 2)) ℂ) ∈ 𝐔[Reg (2 + 2)] := liftP_mem hB

-- C2: the layers and the shift lemma
example : hUpTo (2 + 2) 2 = liftS (hadamardMat 2) := hUpTo_eq_liftS 2 2
example : flipUpToMat (2 + 2) 2 = liftS (xAllMat 2) := flipUpToMat_eq_liftS 2 2
example : (zU 2 2 1).val = ctrlU 1 (-1) := zU_val 2 2 1
example : dataMat (2 + 2) ((qftGates 2).map (Gate.shiftData 2)) = liftP (dataMat 2 (qftGates 2)) :=
  dataMat_shiftData 2 _ (List.all_eq_true.mpr (qftGates_unitary 2))
    (List.all_eq_true.mpr fun _ hg => qftGates_dataOnly hg)
example : (qftInvU 2 2 none).val = liftP (star (dataMat 2 (qftGates 2))) := qftInvU_val 2 2 none

-- C3: the controlled oracle
example : (phaseOracle ((n2.withControl 2 1).pred (2 + 2))).val =
    ctrlU 1 (phaseOracle (n2.pred 2)).val :=
  phaseOracle_withControl (by decide +kernel) rfl rfl (by decide)

-- C4: the algebra
example (A B : Matrix (Reg 2) (Reg 2) ℂ) :
    (ctrlU 0 A * ctrlU 0 B : Matrix (Reg (2 + 2)) (Reg (2 + 2)) ℂ) = ctrlU 0 (A * B) :=
  ctrlU_mul 0 A B
example (V : Matrix (Reg 2) (Reg 2) ℂ) : (zU 2 2 0).val * ctrlU 0 (-V) = ctrlU 0 V :=
  zU_mul_ctrlU_neg 2 2 0 V
example : (cdiffU 2 2 1 .tree).val = ctrlU 1 (-(diffU 2).val) :=
  cdiffU_val .tree (by decide) (by decide)
example : (cgU n2 2 2 1 .tree).val = ctrlU 1 (groverOp (n2.pred 2)).val :=
  cgU_val .tree (by decide +kernel) rfl rfl (by decide) (by decide)
example : (powersU n2 2 2 .tree).val = ctrlPow (groverOp (n2.pred 2)).val :=
  powersU_val .tree (by decide +kernel) rfl rfl (by decide)

-- C5: the theorem, exact and approximate inverse QFT
example (h : countingCircuit n2 2 2 = .ok cc2) :
    cc2.WF ∧ AncRestore (2 + 2) cc2.nAnc cc2 (U_count (n2.pred 2) 2 none) :=
  countingCircuit_ancRestore h (by decide +kernel) rfl rfl
example (h : countingCircuit n2 2 2 (some 1) = .ok cc2a) :
    cc2a.WF ∧ AncRestore (2 + 2) cc2a.nAnc cc2a (U_count (n2.pred 2) 2 (some 1)) :=
  countingCircuit_ancRestore h (by decide +kernel) rfl rfl
example : (U_count (n2.pred 2) 2 none).val =
    liftP (star (dataMat 2 (qftGates 2))) * ctrlPow (groverOp (n2.pred 2)).val *
      hadamardMat (2 + 2) := rfl

/-! ## Stage 20a2 — the distribution of the counting circuit, at `n = 2`, `m = 2` -/

/-- The Grover data of `x₀ ∧ x₁` on two qubits: `M = 1`. -/
def gp22 : GroverData := ⟨2, 1, le_rfl, fun x => x 0 && x 1, by decide⟩

/-- The Grover data of `true` on two qubits: `M = 2ⁿ = 4`, the case `ψ_b = 0`. -/
def gpAll : GroverData := ⟨2, 4, by norm_num, fun _ => true, by decide⟩

-- B1
example (x : Reg (gp22.n + 2)) :
    ((U_count gp22.P 2 none).val *ᵥ basisVec (zeroReg _)) x =
      ((2 ^ 2 : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ 2),
        Complex.exp (-(2 * π * Complex.I * (phase x).toNat * k / 2 ^ 2)) *
          ((groverOp gp22.P ^ k).val *ᵥ ketS gp22.n) (search x) :=
  U_count_zero_apply gp22 2 x

-- B2
example (x : Reg (gp22.n + 2)) :
    ((U_count gp22.P 2 none).val *ᵥ basisVec (zeroReg _)) x =
      ampA gp22 2 (phase x).toNat * gp22.psiGood (search x) +
        ampB gp22 2 (phase x).toNat * gp22.psiBad (search x) :=
  U_count_zero_apply_eq gp22 2 x
example (y : ℕ) : ‖ampA gp22 2 y‖ ^ 2 + ‖ampB gp22 2 y‖ ^ 2 =
    (‖qpeAmp 2 (gp22.θ / π - y / 2 ^ 2)‖ ^ 2 + ‖qpeAmp 2 (-gp22.θ / π - y / 2 ^ 2)‖ ^ 2) / 2 :=
  norm_sq_ampA_add_ampB gp22 2 y

-- B3, both for `M = 1` and for `M = 2ⁿ`
example (y : Reg 2) : phaseDist gp22 2 y =
    (qpeProb 2 (gp22.θ / π) y.toNat + qpeProb 2 (-gp22.θ / π) y.toNat) / 2 :=
  phaseDist_eq gp22 2 y
example (y : Reg 2) : phaseDist gpAll 2 y =
    (qpeProb 2 (gpAll.θ / π) y.toNat + qpeProb 2 (-gpAll.θ / π) y.toNat) / 2 :=
  phaseDist_eq gpAll 2 y
example : gpAll.psiBad = 0 := by
  funext x
  simp [GroverData.psiBad, gpAll]
example : gpAll.θ = π / 2 :=
  θ_eq_pi_div_two_of_psiBad gpAll (by funext x; simp [GroverData.psiBad, gpAll])

-- B4
open Classical in
example : 8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg 2 =>
    CircleNear 2 (gp22.θ / π) y.toNat ∨ CircleNear 2 (-gp22.θ / π) y.toNat), phaseDist gp22 2 y :=
  qpe_two_phase_bound gp22 (by norm_num)
open Classical in
example : 8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg 2 =>
    |Real.sin (π * y.toNat / 2 ^ 2) ^ 2 - gp22.M / 2 ^ gp22.n| ≤ ae_eps (gp22.M / 2 ^ gp22.n) 2),
      phaseDist gp22 2 y :=
  qpe_success gp22 (by norm_num)
open Classical in
example : 8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter (fun y : Reg 2 =>
    |Real.sin (π * y.toNat / 2 ^ 2) ^ 2 - gpAll.M / 2 ^ gpAll.n| ≤ ae_eps (gpAll.M / 2 ^ gpAll.n) 2),
      phaseDist gpAll 2 y :=
  qpe_success gpAll (by norm_num)

/-! ## Axioms (CLAUDE.md rule 10) -/

/-- info: 'CQRV.Synthesis.Network.withControl_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Network.withControl_pred

/-- info: 'CQRV.Synthesis.Network.withControl_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Network.withControl_WF

/-- info: 'CQRV.Gate.qubitsOk_shiftData' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gate.qubitsOk_shiftData

/-- info: 'CQRV.Counting.unitaryDenote_dataOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unitaryDenote_dataOnly

/-- info: 'CQRV.Counting.controlledDiffusion_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms controlledDiffusion_ancRestore

/-- info: 'CQRV.Counting.controlledGrover_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms controlledGrover_ancRestore

/-- info: 'CQRV.Counting.countingCircuit_ancRestore_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countingCircuit_ancRestore_raw

/-- info: 'CQRV.Counting.countingCircuit_ancRestore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countingCircuit_ancRestore

/-- info: 'CQRV.Counting.powersU_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms powersU_val

/-- info: 'CQRV.Counting.dataMat_shiftData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dataMat_shiftData

/-- info: 'CQRV.Counting.raw_eq_U_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_eq_U_count

/-- info: 'CQRV.Grover.U_count_zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms U_count_zero_apply

/-- info: 'CQRV.Grover.phaseDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phaseDist_eq

/-- info: 'CQRV.Grover.qpe_two_phase_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qpe_two_phase_bound

/-- info: 'CQRV.Grover.qpe_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qpe_success

end CQRV.Tests.Counting
