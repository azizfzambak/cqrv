# Stage 29 note — why the SQIR / VOQC comparison is not run, and what the literature says (30b, 2026-11-16)

PHASE2_SPEC §A.9 (3), §D.2; PHASE2_ROADMAP row 29. Written from the repository alone. **The citation
rule**: only works whose authors, title, venue and year the author of this note is sure of are cited
as such; no figure (proof size, time, line count) is taken from any paper; anything uncertain is
marked **to be checked by the author**.

## 1. Why Stage 29 is not run

Stage 29 was to compare CQRV's certificates with a verified quantum compiler on the same instances:
proof effort, proof size, what is checked, what is trusted. It is not run, for three reasons recorded
at M3 (DECISIONS.md, 2026-11-15; PHASE2_SPEC §A.9 (3)):

1. **No Coq toolchain on the machine, and none allowed without the author.** SQIR and VOQC are Coq
   developments (with an OCaml extraction); installing Coq, opam and the SQIR sources is a download
   and an account-free but external dependency, which under the delegation rules of 2026-11-15 needs
   the author's explicit approval; it was not asked for, since the comparison is not needed by any
   claim of Paper 1 or Paper 2.
2. **The effort is a project of its own.** A fair comparison needs the same circuits in both
   systems, the same statements, and a measure of proof effort that is defined before measuring; CQRV
   certifies *realization* statements (`RealizesExact` of a specification by a channel, with a grade)
   while the verified compilers certify *semantic preservation* of a transformation — the statements
   differ in kind, so the comparison is partly conceptual (section 3), and that part needs no
   toolchain.
3. **Phase 2's budget went to Tracks B and C.** The M3 close chose the hardware chain (Stages 24–27)
   over the comparison; the frontier and the conditional certificates are the result.

What remains is this note: the conceptual comparison, from the literature only, with the citation rule
above.

## 2. Verified quantum compilation in the literature

Works the author of this note is sure of (authors, title, venue, year):

- **SQIR**: Kesha Hietala, Robert Rand, Shih-Han Hung, Liyi Li, Michael Hicks. *Proving Quantum
  Programs Correct.* ITP 2021. — A small quantum intermediate representation embedded in Coq, with a
  denotational semantics (unitary and density-matrix) and proofs of program correctness (e.g.
  Grover's and Deutsch–Jozsa are among the verified programs; which exactly: **to be checked by the
  author**).
- **VOQC**: Kesha Hietala, Robert Rand, Shih-Han Hung, Xiaodi Wu, Michael Hicks. *A Verified Optimizer
  for Quantum Circuits.* POPL 2021. — Circuit optimizations (gate cancellation, rotation merging,
  Hadamard reduction, …) over SQIR, each proved to preserve the circuit's semantics, extracted to
  OCaml and run on standard benchmark circuits.
- **QWIRE**: Jennifer Paykin, Robert Rand, Steve Zdancewic. *QWIRE: A Core Language for Quantum
  Circuits.* POPL 2017. — A circuit language with a linear type system, embedded in Coq, with a
  denotational semantics on density matrices.
- **Qbricks**: Christophe Chareton, Sébastien Bardin, François Bobot, Valentin Perrelle, Benoît
  Valiron. *An Automated Deductive Verification Framework for Circuit-building Quantum Programs.*
  ESOP 2021. — Parametric circuit-building programs verified in Why3 with a path-sum semantics; Grover
  and QPE among the case studies (**to be checked by the author**).
- **CoqQ**: Li Zhou, Gilles Barthe, Pierre-Yves Strub, Junyi Liu, Mingsheng Ying. *CoqQ: Foundational
  Verification of Quantum Programs.* Proc. ACM Program. Lang. 7 (POPL), article 29, 2023. — A Coq library for quantum programs with a
  Hilbert-space and quantum-logic foundation (MathComp-based).
- **Giallar / CertiQ** (verification of the Qiskit compiler's passes): Runzhou Tao, Yunong Shi, Jianan
  Yao, et al. *Giallar: push-button verification for the Qiskit quantum compiler.* PLDI 2022 — the full
  author list and the venue year **to be checked by the author**; CertiQ (Yunong Shi et al., 2019,
  arXiv) is its predecessor — **to be checked by the author**.
- **Unqomp**: Anouk Paradis, Benjamin Bichsel, Samuel Steffen, Martin Vechev. *Unqomp: Synthesizing
  Uncomputation in Quantum Circuits.* PLDI 2021. — Automatic uncomputation with a correctness
  argument (not machine-checked), the reference for Track B's "safety conditions" item.
- **Silq**: Benjamin Bichsel, Maximilian Baader, Timon Gehr, Martin Vechev. *Silq: A High-Level Quantum
  Language with Safe Uncomputation and Intuitive Semantics.* PLDI 2020.
- **Isabelle Marries Dirac**: Anthony Bordg, Hanna Lachnitt, Yijun He. *Certified Quantum
  Computation in Isabelle/HOL.* Journal of Automated Reasoning, 2021 — the exact title and year **to
  be checked by the author**.
- The few-ancilla MCZ constructions of Track B follow Khattar and Gidney (2025) as cited in
  `docs/DECISIONS.md` (Stage 12b); title and venue **to be checked by the author**.

No figures from these works are reported here (proof sizes, benchmark counts, speed-ups): none was
measured by this repository, and the citation rule forbids quoting them from memory.

## 3. What CQR's specialization adds, and what it does not

Where the works above verify a **transformation** (an optimizer or compiler pass preserves the
semantics of every circuit it is given) or a **program** (a fixed algorithm meets its specification),
CQRV certifies a **realization per request**:

1. **Proof-carrying patterns, specialized per instance.** The library holds a parametric lemma per
   pattern (`grover_parametric_lemma`, `ae_parametric_lemma`), and `cqr certify` emits, for a request,
   a self-contained `Cert.lean` whose theorem `cert` is the lemma instantiated at the request's
   network, with the instance facts (`emitted_ok`, `grade_eq`, `hM_count`, the front end) decided by
   the kernel. The user checks one file with `lake env lean`; no trust in the compiler's run is
   needed (M3 report §2; this is the discipline of report §9.5.1).
2. **Kernel checks of untrusted output.** The synthesizer, the matcher, the emitter and, in Track C,
   Qiskit's layout and routing are untrusted tools; what they output is re-decided by the kernel
   against a literal (`emitted_ok`, `recon` by `rfl`, `edges_ok`, `emitted_eq`). The witness, not the
   transpiler, is the object of the proof — the same stance as translation validation, applied to
   routing (`applyWitness_sound`, Stage 26b3).
3. **The noise premise as a hypothesis.** Where a verified compiler's statement ends at the ideal
   semantics, CQRV's conditional certificate states the noisy realization under four named premises
   ((P-cal), (P-stoch), (P-ro), (P-idle)) and carries the exact bound δ' as a kernel fact
   (`phys_noisy_inst`, Stage 27b2). The premises are hypotheses of a theorem, never facts about a
   device; the frontier (`docs/hw_frontier/FRONTIER.md`) says where the bound is below 1.
4. **Resource grades as part of the statement.** Every certificate carries a measured grade
   (w, d, t, a) and `grade_ext`, and selection under a budget is itself certified (`select_spec`,
   `selectPhys_spec`, `selectNoise_spec`).

What CQRV does not do, that the works above do: it verifies no general optimization pass (Track C
uses Qiskit's routing untrusted and checks its witness); its matcher's completeness is for a fragment
(Miller patterns with uniform arity); its patterns are two (Grover search and quantum counting), plus
the few-ancilla MCZ family and the hardware chain; the all-n restoration theorem of the few-ancilla
MCZ is per instance (`fewCheck_sound`); and it has no device result. A quantitative comparison (proof
effort, proof size, kernel time per instance against a SQIR proof of the same circuit) is **future
work**, conditional on the author's approval of the Coq toolchain; the measured side of such a
comparison for CQRV is already in `docs/M5_REPORT.md` §1.2 (kernel times) and §4 (module sizes).
