# Paper 2 — draft (reviewer's draft for milestone M4; the author owns the final text)

Working title: **Restoration under measurement: a mechanized theory of measurement-based
uncomputation and ancilla regimes**

Status: the reviewer's draft, written 2026-11-15 under the author's delegation (PHASE2_SPEC §A.9,
"21m done"). Every technical claim names its Lean theorem. Every theorem cited here is checked by
`lake build` and has the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) unless
stated otherwise. Nothing here is published; the text is revised by the author before Stage 30.

**Updated at Stage 30c (2026-11-16), for the author:**
- One open item is closed by Track C (§10).
- The mechanization note on convex combinations is corrected (§8).
- The CI count is current (26 steps).

The Track B results themselves are unchanged since M4.

## Abstract (draft)

Measurement-based uncomputation (MBU) returns an ancilla holding a Boolean function f of the data
to |0⟩. It measures the ancilla in the X basis and, on outcome 1, applies the phase oracle of f to
the data. For the temporary logical-AND the correction is a CZ and costs nothing. We give a
mechanized account, in Lean 4 on density-operator semantics, of when and why this works, and of
how restoration composes.
- **The general theorem.** MBU restores the ancilla and leaves the data unchanged for every
  phase-exact compute block. A compute phase φ is not removed: it remains on the data as diag(φ).
- **The exact boundary.** In a circuit language whose classically controlled gates are Clifford,
  MBU applies exactly to the f of degree at most 2 over GF(2). The correction is Clifford iff f
  is quadratic, and a well-formed MBU circuit forces f to be quadratic.
- **The restoration algebra.**
  - Without its correction, MBU still restores the ancilla but dephases the data in the basis of
    f.
  - Blocks certified on different ancilla registers compose.
  - The regimes clean, conditionally clean and dirty form a strict hierarchy, and a circuit that
    resets an ancilla by measurement can never be dirty restoring.
- **A cost bound.** Under the cost model of the Khattar–Gidney family, the 8n − 24 T-count of a
  two-ancilla multi-controlled Z is optimal among Problem-1 schedules.

## 1. Introduction

[To write. Points:]
- Restoration is the obligation that makes reversible-circuit verification hard. The ancillas
  must return to a state independent of the data; otherwise they stay entangled (report §6.2.1).
- MBU (Gidney 2018) halves the T-cost of AND-based oracles. Its correctness is usually argued for
  the AND gadget alone.
- Contributions, in order: the general MBU theorem (§3); the Clifford boundary (§4); the
  restoration algebra (§5); the regimes (§6); the cost bound (§7); the mechanization (§8).
- Context: this is the restoration layer of a certifying quantum compiler (CQRV, Paper 1), where
  each emitted circuit carries a kernel-checked certificate. Here we isolate the theory.

## 2. Setting

- **The circuit language.** Gates H, S, S†, T, T†, X, Z, CNOT, CZ, phase gates p(a, k) and
  cp(a, k), computational-basis measurement into a classical bit, and classically controlled
  gates `ifBit j g`.
- **Well-formedness** (`Circuit.WF`): qubits in range, and a classical-bit discipline. A
  controlled gate reads a bit already written, and `g` must be Clifford (`Gate.bitOk`).
- **Semantics.** The register is `Reg n × Reg a` (data, ancillas). A circuit denotes the Kraus
  channel ρ ↦ ∑_c K_c ρ K_cᴴ over its branches c (`channelDenote`).
- **Clean restoration.** `AncRestore n a C U`: for every data state ρ, the circuit maps
  ρ ⊗ |0…0⟩⟨0…0| to (U ρ Uᴴ) ⊗ |0…0⟩⟨0…0|.
- **The Kraus template** (`ancRestore_of_kraus'`). If every branch acts on the clean-ancilla
  subspace as a scalar times U ⊗ |0⟩⟨0|, the circuit restores. The weights summing to one follow
  from completeness (`sum_norm_sq_eq_one_of_kraus`); the original template assumed it.

## 3. The general MBU theorem

**Definitions.**
- A *compute block* for f with phase φ (`ComputesInto`) is a unitary gate list mapping
  |x, 0…0⟩ ↦ φ(x) |x, e_t(f(x))⟩.
- A *phase implementation* of f (`PhaseImpl`) is a data-only unitary list equal to
  λ · diag((−1)^f) ⊗ 1.
- The uncompute is `mbuUncompute t j O = H t; measure t → j; if j: O; if j: X t`.

**Theorem 1** (`mbu_general`, `mbu_general_phase`). For a well-formed circuit B ++ mbuUncompute
t j O, `AncRestore` holds with U = diag(φ). With Z t inserted before the uncompute, U =
diag(φ · (−1)^f). At φ = 1 the conclusions are the identity and the phase oracle of f
(`mbu_general_one`, `mbu_general_phase_one`).

*Proof idea.* In branch 0 the data is unchanged. In branch 1 the X-basis measurement leaves
(−1)^{f(x)}, which O cancels. Both branches carry weight 1/2, with the global phase λ in branch
1, and the reset returns t to |0⟩.

**Corollary** (`mbu_channel_correct_of_general`). The AND gadget (TempLogicalAND; Z; MBU with CZ)
maps ρ ⊗ |0⟩⟨0| to CZ ρ CZ ⊗ |0⟩⟨0|. This is a second proof of the Stage 6 statement.

**Remark.** MBU needs a phase-exact compute block: a compute phase is left on the data. The
coherent uncompute (B†) would remove it. That this needs a phase-exact compute block is visible
in the theorem's conclusion.

## 4. The Clifford boundary

- **Theorem 2** (`clifford_iff_quadratic`). For a sign diagonal D = diag((−1)^f), D conjugates
  every X_i to a Pauli up to phase iff f is quadratic over GF(2). The route is the derivative
  criterion `isQuadratic_iff_deriv_affine`: f is quadratic iff every derivative
  x ↦ f(x) ⊕ f(x ⊕ e_i) is affine. Then `conj_pauliX_phaseDiag` and
  `phaseDiag_eq_smul_pauliZ_iff`.
- **Theorem 3** (`phaseCircuitQuad_phaseImpl`, `mbu_quadratic`). Every quadratic f has a Clifford
  phase implementation by Z and CZ gates, hence a restoring MBU circuit.
- **Theorem 4** (`mbu_wf_forces_quadratic`, `mbu_exactly_quadratic`). In the circuit language
  above, a well-formed circuit B ++ [Z t] ++ mbuUncompute t j O with a phase implementation O of
  f exists iff f is quadratic, for any well-formed measurement-free B.
  - The proof builds a Pauli / Clifford layer on the register in the symplectic representation
    (`pauliMono`, with an exact product rule).
  - It proves every Clifford gate of the language Clifford (`gateU_isClifford`), and restricts
    from the register to the data (`isCliffordDiag_of_tensor`).
- **Reading.** For the three-input AND (CCZ) the correction is not Clifford (a test proves
  ¬ IsCliffordDiag of the CCZ diagonal). In this language it is excluded by well-formedness, not
  by cost. In a language that allowed T under classical control, MBU beyond degree 2 would be
  expressible but pay non-Clifford corrections; that is outside the mechanization.
- **Note on j.** One classical bit is written, so j = 0 is forced. The theorem states j
  existentially; a fixed-j form is false for j ≥ 1.

## 5. The restoration algebra

- **Block lists** (`ancRestore_list`). Local restoration implies global restoration for any list
  of blocks, with the product of their unitaries.
- **Theorem 5** (`ancRestoreMix_of_kraus`: restoration under measurement with a mixed data
  action). If branch c acts on the clean subspace as l_c · U_c ⊗ |0⟩⟨0|, the ancillas are
  restored and the data undergoes ρ ↦ ∑ |l_c|² U_c ρ U_cᴴ.
- **Corollary** (`mbu_uncorrected`). MBU without its correction restores the ancilla, and the data
  undergoes ½ ρ + ½ O_f ρ O_f: a dephasing in the basis of f. The correction of Theorem 1 is
  exactly what turns this mixture back into a unitary.
- **Widening** (`AncRestore.widen`, `AncRestore.comp_widen`). A block certified on a ancillas,
  touching only those, is certified on a + b ancillas. So blocks certified with different
  ancilla counts compose on the larger register (ancilla reuse).

## 6. Three regimes

Report §6.2.3, Table 4.
- **Dirty** (`AncRestoreDirty`): (U ρ Uᴴ) ⊗ σ for every ancilla state σ. A dirty block acts as
  Ad(U ⊗ 1) on every state (`AncRestoreDirty.all`; product states span, by polarization).
- **Conditionally clean** (`AncRestoreCond … cond`): Ad(U ⊗ 1) on the states supported on
  V_cond = span{|x, w⟩ : cond(x) → w = 0}.
- **Theorem 6** (the hierarchy). Dirty = Cond(false) ⇒ Cond(cond) ⇒ Cond(true) ⇒ clean
  (`AncRestoreCond.toDirty`, `ancRestoreDirty_iff_cond_false`, `AncRestoreCond.mono`,
  `AncRestoreCond.toClean`). Both inclusions are strict: CZ(x0, anc) is conditionally clean
  under x0, not dirty, and clean.
- **Theorem 7** (`reset_not_dirty`). A circuit that ends by measuring an ancilla, applying a
  data-only correction and resetting it, is not dirty restoring for any U. MBU in particular
  cannot serve dirty ancillas (`mbu_not_dirty`).
- **A dirty instance.** CNOT(x0 → d); CZ(d, x1); CNOT(x0 → d); CZ(d, x1) is dirty restoring with
  CZ: the dirty value cancels.
- **Composition** (`AncRestoreDirty.comp`, `AncRestoreCond.comp`), the latter when the first
  unitary maps V_cond into V_cond'.
- **The bridge to Khattar–Gidney** (`Grover.KG.Inv.cond_value`). In the invariant of the
  formalized KG construction, a marked target has its value fixed by the indices below it.

## 7. The cost of two clean ancillas

**The model** (`CQRV/Synthesis/Problem1.lean`). A schedule is a list of conjunctions (t; x, y) on
an index set. The target t must be available, and the controls x and y must hold live values. A
step makes t live and x, y available, so the number of live values drops by one (`live_step`).
The KG family's costs:
- 4 T for a conjunction on a fresh clean target (Gidney's AND, uncomputed by MBU);
- 8 T for every other conjunction (a relative-phase Toffoli pair, at Maslov's 4 T each, assumed).

The final phase acts on at most two live values (CZ, 0 T).

**Theorem 8** (`cost_lower_bound`, `problem1_T_lower_bound`). A valid schedule from n live values
to k costs at least 8 (n − k) − 4 min(c, n − k), where c is the number of clean ancillas. With
c = 2 and k ≤ 2 this is 8n − 24 for n ≥ 4. The number of clean ancillas is what the bound counts:
with c = 3 the model allows 8n − 28.

**Attainment.** The two-ancilla candidate of the compiler (Khattar–Gidney §5.3 doubling and §5.2
greedy) translates into the model; its emitted T-count equals the schedule's cost
(`planB_tCount`).
- For n = 6 … 12 it is 8n − 24 (`planB_cost`).
- For n = 4, 5 it is 8n − 20 (`planB_cost_small`): one ancilla is never targeted. The bound is
  still attained in the model there, by another schedule.
- These facts are proved per n by kernel evaluation, not for all n.

**Scope.** This is optimality within the stated model, not a lower bound on the T-count of every
multi-controlled-Z circuit. Maslov's 4 T per relative-phase Toffoli is an assumption of the model.

## 8. Mechanization

- Lean 4 (v4.35.0), Mathlib, Physlib (density operators, CPTP maps).
- Modules: `MBUGeneral` (468 lines), `MBUClifford` (540), `MBUBoundary` (801),
  `RestoreAlgebra` (593), `RestoreRegimes` (818), `KGRegime` (44), `Problem1` (362); about
  3 600 lines with their tests.
- No `sorry`; standard axioms. The CI had 19 steps at M4 and has 26 at M5.
- Conventions that mattered:
  - 𝔽₂ as `ZMod 2`;
  - the symplectic representation of Paulis;
  - statements on Kraus operators rather than on `MState` mixtures. *Corrected at M5:* the
    earlier note said Physlib has no convex-combination API. It has one, `CPTPMap.instMixable`,
    through Choi matrices, used in Stage 27a (`mix_eq_mix_ab`). The Kraus form was chosen before
    that, and it remains the form of the Track B statements.

## 9. Related work

[To write; verify each reference before use.]
- Gidney 2018, the temporary logical-AND and MBU (arXiv:1709.06648).
- Khattar and Gidney 2025, conditionally clean ancillae (Quantum 9, 1752).
- Maslov 2016, relative-phase Toffolis (PRA 93, 022311).
- Barenco et al. 1995 (PRA 52, 3457).
- Bennett 1989, pebbling.
- Safe uncomputation in Silq (Bichsel et al., PLDI 2020) and Unqomp (Paradis et al., PLDI
  2021).
- Verified compilation in SQIR / VOQC (Hietala et al., POPL 2021).
- Paper 1 (the certifying compiler).

## 10. Limitations and open items

- The circuit language has no classically controlled iteration and no non-Clifford gate under
  classical control. The boundary theorem is relative to that language.
- Not yet proved:
  - clean ⇒ Cond(true);
  - the dirty widening.
- **Proved since M4:** the commutation of blocks on disjoint qubits, in Track C (Stage 26b2,
  `CQRV/Hardware/Reorder.lean`):
  - `gateK_comm_of_disjoint`: gates on disjoint qubits and bits commute in every branch;
  - `krausOps_reorder`: a reordering that is topological for the dependency queues preserves the
    Kraus operators.

  Both have the standard three axioms.
- The 8n − 24 bound is relative to the stated cost model. Its attainment by the compiler's
  candidate is proved per n (6 … 12), not for all n.
- The KG construction is cleanly restoring as a whole; the conditionally clean regime enters it as
  an internal invariant, bridged by one lemma.
