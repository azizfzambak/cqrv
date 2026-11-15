# Stage 22 — The general MBU theorem (PHASE2_SPEC §B.1; Track B, Paper 2)

PHASE2_SPEC.md §B.1. Report: §6.2.1, §6.2.2, §6.2.4, §6.3.2. PHASE2_ROADMAP row 22. Written at
the 21b2 review (2026-11-15) by the reviewer, under the author's delegation.

Stage 22 has two tasks, one commit each:
- **22a**, `mbu_general`, is specified here;
- **22b**, the Clifford corollary, is outlined here and gets its detailed text at the 22a review.

Precondition: main = the 21b2 review commit. Start with `git switch -c stage-22a main`.
Untracked and not yours: `docs/paper/`, `docs/cqrv_report_revised_v4.docx`. Windows:
`LEAN_NUM_THREADS=4`.

The process is the delegated one (PHASE2_SPEC §A.9, "21m done"):
1. The reviewer session sends the prompt.
2. You implement, and say "ready for CI".
3. The reviewer audits and runs CI.
4. You commit on the reviewer's prompt.

`scripts/ci_local.sh` is the reviewer's to run.

**Invariants of Stage 22.**
- **No existing theorem statement changes.** `mbu_channel_correct` keeps its statement and its
  proof; the re-derivation is a new theorem.
- **Nothing is regenerated.** No certificate, CLI or harness change.
- **The `cqr` closure is unchanged.** The new modules are Physlib-side and imported by
  `CQRV.lean` only.
- **No new CI step.** The pass mark stays **19 PASS, 0 FAIL, 4 n/a**.
- **No `sorry`.** It is not part of the acceptance; if a lemma resists after a serious attempt,
  stop and ask.
- **False statements.** If a statement here is false, give the counterexample and the corrected
  form.
- **Lemma names.** CLAUDE.md rule 2.

---

## 22a — `mbu_general` (`CQRV/Circuit/MBUGeneral.lean`, new)

### K1. Definitions

- **`ancBasis t b : Reg a`.** The ancilla basis state with t = b and every other ancilla 0, for
  an ancilla qubit `t = .anc i` with i < a.
- **`ComputesInto n a B t f φ`.** `B.all Gate.isUnitary`, and for every x : Reg n:
  `unitaryDenote n a B *ᵥ basisVec (x, 0) = φ x • basisVec (x, ancBasis t (f x))`.
  Use the vector form of `tempLogicalAND_correct_lift`.
- **`PhaseImpl n a O f`.** `O.all Gate.isUnitary`, every qubit of O is a data qubit, and there is
  λ with ‖λ‖ = 1 and `unitaryDenote n a O = λ • (phaseDiag f ⊗ₖ 1)`. A basis-vector form is
  acceptable if it is easier to use.
- **`mbuUncompute t j O`** as in §B.1, with `uncomputeTempLogicalAND_eq : UncomputeTempLogicalAND a
  b t m = mbuUncompute t m [.cz a b] := rfl` (or by `simp`).
- **`diagU φ : 𝐔[Reg n]`** for a phase function of modulus 1. Reuse an existing construction if
  one exists (rule 2); `phaseOracle f` must be `diagU` of the sign function, or provably equal to
  it.

### K2. Theorems

- **`mbu_general`.** Hypotheses:
  - C.WF;
  - C.gates = B ++ mbuUncompute t j O;
  - C.nBits = j + 1, and B and O contain no measurement;
  - t is an in-range ancilla;
  - ComputesInto n a B t f φ;
  - PhaseImpl n a O f.

  Conclusion: `AncRestore n a C (diagU φ)`.
- **`mbu_general_phase`.** The same hypotheses, with C.gates = B ++ [.z t] ++ mbuUncompute t j O.
  Conclusion: `AncRestore n a C (diagU fun x => φ x * (if f x then -1 else 1))`.
- **The φ = 1 corollaries:** `AncRestore … 1`, and `AncRestore … (phaseOracle f)`.
- **The proof route.** `ancRestore_of_kraus` with l_c = λ_c/√2, where λ_c is 1 on branch 0 and λ
  on branch 1. K_c · P is computed column by column:
  - `krausOps_append_gates`;
  - `krausOps_of_unitary` on B;
  - `ComputesInto` on |x, 0⟩;
  - then the gates of `mbuUncompute` on |x, ancBasis t (f x)⟩.
- **`mbu_channel_correct_of_general`.** The statement of `mbu_channel_correct`, word for word,
  proved from `mbu_general_phase` with B = `TempLogicalAND (.data 0) (.data 1) (.anc 0)`,
  f = x0 ∧ x1, O = `[.cz (.data 0) (.data 1)]` and φ = 1. `ComputesInto` comes from
  `tempLogicalAND_correct_lift`; `PhaseImpl` comes from the CZ matrix (`czU` is
  `phaseOracle (x0 ∧ x1)`).

### K3. Tests (`tests/CQRVTests/MBUGeneral.lean`, new)

- `#guard_msgs` on the axioms of `mbu_general`, `mbu_general_phase` and
  `mbu_channel_correct_of_general` (the standard three or a subset).
- **A linear instance:** f = x0 ⊕ x1, B = `[.cnot x0 t, .cnot x1 t]`, O = `[.z x0, .z x1]`. Show
  its `AncRestore` conclusion from `mbu_general_phase`.
- **A degree-3 instance (optional):** f = x0 ∧ x1 ∧ x2. B is two temporary ANDs, the first one
  uncomputed coherently (its adjoint) inside B; O is a phase-exact CCZ (the standard 7-T
  network, up to a global phase).
  - If proving `ComputesInto` and `PhaseImpl` for it costs more than about 150 lines, skip it and
    say so in (e).
  - It is the example Paper 2 uses for "MBU is costly beyond degree 2".

### 22a Docs / Acceptance / Stop

Docs:
- a DECISIONS.md entry;
- `docs/PROJECT_STATUS.md`;
- README's status line.

Acceptance:
- `lake build` green and warning-free;
- CI 19 PASS, 0 FAIL, 4 n/a;
- the axioms as in K3;
- `mbu_channel_correct` unchanged.

Stop and ask in any of these cases:
- a hypothesis of `mbu_general` turns out to be insufficient, for example when B uses an ancilla
  that the circuit's `nAnc` does not cover; give the counterexample and the corrected form;
- a Lean process above 8 GB;
- a single proof above about 400 lines.

---

## 22b — The Clifford corollary (outline; detailed at the 22a review)

PHASE2_SPEC §B.1 "The Clifford corollary".
- `IsQuadratic f`: there are c, a and b with f(x) = c ⊕ ⊕ a_i x_i ⊕ ⊕_{i<j} b_ij x_i x_j.
- The constructive (⇐): `phaseCircuitQuad` of Z and CZ gates, with `PhaseImpl`.
- `IsCliffordDiag` for a diagonal unitary: every X_i is conjugated to a Pauli up to a phase.
- (⇒) through the derivatives D_i f, and the theorem `phaseImpl_clifford_iff_quadratic`.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
