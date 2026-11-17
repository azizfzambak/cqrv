<div class="titleblock">
<div class="ttl">Certified Quantum Realization in Lean 4:<br>A Two-Pattern Prototype with Measurement-Based Uncomputation,<br>Validated Routing, and Conditional Noise Bounds</div>
<div class="auth">Aziz F. Zambak</div>
<div class="aff">Middle East Technical University, Ankara</div>
<div class="aff">zambak@metu.edu.tr</div>
<div class="date">November 2026</div>
</div>

<div class="abstract">

**Abstract.** *Certified quantum realization* (CQR) replaces translation-by-trusted-passes with three steps:
1. match a classical specification against a library of pre-proved, resource-graded circuit patterns;
2. instantiate the pattern;
3. emit a certificate that a proof-assistant kernel checks, or reject the request with a diagnostic and a repair hint.

We report a two-pattern prototype of CQR in Lean 4 on Mathlib and Physlib. The specifications are Boolean predicates on bit vectors written in a small functional language, and the two patterns are Grover search and quantum counting by amplitude estimation.

**What a certificate states.** Each certificate is a kernel-checked theorem with two conjuncts:
- the generated circuit (ε, δ)-realizes the specification under a decoding measurement, within a resource grade, with the decoding taken after the ancillae are traced out;
- the circuit restores every ancilla, a separate statement on density operators, so measurement-based uncomputation (MBU) lies inside the correctness notion.

For the running example, an 8-bit predicate with 32 solutions, the certificate gives δ = 7/128 at the measured grade (15, 134, 72, 7).

**Restoration.** Around these certificates we mechanize a theory of restoration under measurement:
- a general MBU theorem;
- the boundary at which an MBU correction is Clifford, which happens exactly when the uncomputed function is quadratic over 𝔽<sub>2</sub>;
- implications among the clean, conditionally clean and dirty ancilla regimes;
- a proof for every n of the Khattar–Gidney two-ancilla multi-controlled Z;
- a lower bound of 8n − 24 T gates within its schedule family.

**Routing and noise.**
- *Routed circuits.* An untrusted transpiler (Qiskit) routes a circuit on a fake IBM backend and records a witness. Lean reconstructs the physical circuit from the witness, the kernel checks the reconstruction against the transpiler's output, and a soundness theorem transfers the certified realization to the routed circuit, on an ideal device with the target's gates and connectivity.
- *Noise.* We prove a perturbation theorem whose stochastic premise is stated on the full register. Instantiated with calibration-derived numbers, it gives *conditional* certificates whose premises are named in every artifact. Within the tested Grover family, on two shipped calibration snapshots, the bound is non-vacuous only up to three data qubits, and for some of those instances it does not beat a classical baseline.

**Scope.** The development has 39 114 lines of Lean library, no `sorry`, and only the standard axioms. The evidence is kernel checking and internal consistency (Lean against an independent statevector harness). No device was run. The repository is public, with its full history, under the Apache License 2.0.

</div>

<div class="keywords">

**Keywords:** certified compilation; Lean 4; quantum circuits; uncomputation; ancilla restoration; Clifford group; Grover search; amplitude estimation; translation validation; qubit routing; diamond norm; noise bounds.

</div>


## 1 Introduction

**Translation, and why it is fragile.** A classical program describes what should be computed. A quantum circuit is a procedure that, once executed and measured, returns samples. The usual bridge is compilation by translation: rewrite the classical description pass by pass into reversible logic and gates, and accept the result because each pass is believed or tested to preserve meaning. Three facts make this fragile:
1. **Copying and discarding.** A uniform translation of classical programs into unitary circuits cannot preserve the copying and discarding of classical data, which is the categorical form of no-cloning [Abramsky 2010].
2. **Equivalence checking.** Deciding the equivalence of arbitrary circuits is QMA-hard [Janzing et al. 2005], so an unverified compiler's output cannot in general be checked after the fact.
3. **Garbage.** Reversible embeddings produce garbage qubits [Bennett 1973; Landauer 1961], which must be returned to a known state or they destroy interference.

Verified compilers prove each rewrite sound once [Amy et al. 2017; Hietala et al. 2021b; Leroy 2009]. Their correctness statements are about unitary semantics, not about the measurement-based uncomputation, terminal measurement and resource bounds that a realization of a classical specification involves.

**Certified quantum realization (CQR)** was proposed in a specification report [Zambak 2026b], distributed with the repository but not peer-reviewed, elaborating an earlier proposal [Zambak 2026a]. It replaces "compile anything" by four steps:
1. decide whether the specification matches the precondition of a pattern in a finite library, inside a decidable matching fragment;
2. instantiate the pattern's circuit family;
3. emit a certificate: a machine-checkable proof that the instance realizes the specification within stated resources and restores its ancillae;
4. or diagnose a non-match with a repair hint.

Each pattern carries a parametric theorem proved once. The per-request work is specializing it and checking the specialized proof with a kernel, in the spirit of proof-carrying code [Necula 1997].

### 1.1 Scope of this paper

This paper reports a **two-pattern prototype** of CQR in Lean 4 [de Moura and Ullrich 2021] on Mathlib [mathlib 2020] and Physlib [Physlib 2026]. The specifications it realizes are fixed Boolean predicates P : {0,1}<sup>n</sup> → {0,1}, written in a small functional language. Its two patterns are:
- **search** for an x with P(x), by Grover's algorithm;
- **counting** of the solutions of P, by amplitude estimation.

**What the prototype is not.** The framework is defined for general relational specifications, but the prototype realizes only these two problem classes. The search specification has trivial input (the predicate is built into the circuit). The prototype is not a compiler for arbitrary classical programs.

**How the work proceeded.** It treated the specification document as its specification, in Stage 0 and thirty further stages (31 in all). It recorded every disagreement and resolved it in the direction of what can be constructed and proved. Appendix C lists the specification errata, and Appendix D the development method.

### 1.2 What is certified

For P written in the input language, `cqr certify` produces a Lean file whose theorem `cert` states, for the network `net` built from P and the emitted circuit C:

<div class="eq">GroverChannel<sub>n</sub>(C) ⊨ RealizesExact(Search<sub>P</sub>, basis decoding, δ, g(C))  ∧  AncRestore(C, G<sup>r</sup>H<sup>⊗n</sup>),</div>

Here δ = 1 − sin<sup>2</sup>((2r+1)θ) is an exact rational, and g(C) is the grade the kernel measures on C. The file is checked by the kernel and its axioms are audited.

**What the certificate depends on.** The theorem has no hypothesis when n is at most a configurable limit (10 by default): the kernel decides the solution count M. Above the limit, M is a hypothesis. The step from the source text to the typed program is outside the kernel (parser, surface checker, and the printer of the typed-term literal). The step from the typed program to `net` is proved and re-checked in the file.

**Counting.** The counting certificate states (ε, δ)-realization of the counting specification with ε = 2π√(a(1−a))/2<sup>m</sup> + π<sup>2</sup>/4<sup>m</sup> at a = M/2<sup>n</sup> and δ = 1 − 8/π<sup>2</sup>. Its grade is a certified *compositional upper bound*, not a whole-circuit measurement.

**Routed circuits.** Two further certificate kinds are about routed circuits on a fake IBM backend:
- a **physical certificate**: the routed circuit realizes the specification with the same δ on an ideal device with the target's gates and connectivity, under named model premises (Section 3.6);
- a **conditional certificate**: under four further named premises about the device's noise, it realizes the specification with an exact δ′.

### 1.3 Contributions

1. **Realization and restoration, mechanized** (Section 3). Specifications are relations, (ε, δ)-realization holds of graded CPTP maps under a decoding POVM, and resource grades form a monoid with a budget order. The measured and coherent composition theorems come with the hypotheses the formalization made explicit. A diamond distance is built from Physlib's primitives. A trust-model table states what each certificate kind assumes.
2. **A certifying compiler for Boolean predicates** (Section 4):
   - a front end proved from typed term to network;
   - an extractor;
   - a Miller-pattern matcher that is sound and complete for *signature matching* on its fragment;
   - an oracle synthesizer with Gidney's temporary logical-AND and MBU, and a coherent alternative.
3. **A theory of restoration under measurement** (Section 5):
   - restoration of every synthesized oracle;
   - a general MBU theorem;
   - the Clifford/quadratic boundary of MBU corrections;
   - an algebra of restoration;
   - implications among three ancilla regimes;
   - the Khattar–Gidney two-ancilla MCZ for every n;
   - a lower bound of 8n − 24 within its schedule family.
4. **Two certified patterns and certified selection** (Section 6):
   - the Grover lemma for every iteration count;
   - the QFT, a diamond-distance bound for its approximation, and the two-eigenphase phase-estimation bound for the Grover iterate;
   - the counting lemma;
   - certified selection among candidates under a budget;
   - a *logical* measured-composition bound for counting followed by search.
5. **Translation validation of an untrusted transpiler** (Section 7):
   - a witness-based reconstruction of the physical circuit;
   - a soundness theorem transferring realization and restoration to the routed circuit, for transpiler outputs in a stated fragment;
   - a linear-design kernel check, measured at 2 541–4 170 gates;
   - a physical grade with an exact timing model.
6. **Conditional noise bounds** (Section 8):
   - a step semantics with the classical register;
   - a perturbation theorem whose stochastic premise needs no tensor stability;
   - conditional certificates with named premises;
   - a measured bound-vacuity frontier, compared with a classical baseline.

### 1.4 What is not claimed

- **No device.** No device was run, and nothing is "verified on hardware".
- **The premises.** They are hypotheses about a device, not facts proved here. The stochastic premise in particular is not implied by calibration data.
- **Non-vacuity is not usefulness.** A non-vacuous conditional bound need not beat a classical baseline (Section 8.4).
- **The emitters.** The QIR / OpenQASM emitters are translation-validated by re-parsing. For floating-point rotation angles this validates the structure and a numerical round trip, not exact equality with the IR rotation.
- **Matching.** Matcher completeness is completeness of signature matching on a fragment, not semantic completeness over programs.
- **The artifact.** The evidence is kernel checking and internal consistency, not independent reproduction (Section 11).


## 2 Background

### 2.1 States, channels, distances

**States and channels.** For a finite type X, ℋ<sub>X</sub> = ℂ<sup>X</sup> has the basis {|x⟩}, and 𝒟(ℋ<sub>X</sub>) is the set of density operators. A channel is a CPTP map with Kraus operators {K<sub>c</sub>}, Σ K<sub>c</sub><sup>†</sup>K<sub>c</sub> = I. A POVM {E<sub>y</sub>} yields the distribution y ↦ tr(E<sub>y</sub>ρ).

**Distances.**
- The trace distance T(ρ, σ) = ½‖ρ − σ‖<sub>1</sub> is contracted by channels, and bounds the change of every event probability.
- The diamond norm ‖Φ<sub>1</sub> − Φ<sub>2</sub>‖<sub>⋄</sub> is the worst-case trace-norm distance of the outputs over inputs entangled with a reference system [Kitaev 1997; Aharonov et al. 1998; Watrous 2018].

### 2.2 Grover search and amplitude estimation

**Grover search.** Let P have M ≥ 1 solutions among N = 2<sup>n</sup>, and let sin<sup>2</sup>θ = M/N. With the phase oracle O<sub>P</sub>, the diffusion U<sub>s</sub> = 2|s⟩⟨s| − I with |s⟩ = H<sup>⊗n</sup>|0⟩, and G = U<sub>s</sub>O<sub>P</sub>, the state G<sup>r</sup>H<sup>⊗n</sup>|0⟩ yields a solution with probability sin<sup>2</sup>((2r+1)θ) [Grover 1996; Boyer et al. 1998].

**The running example** is P(x) = x<sub>0</sub> ∧ x<sub>3</sub> ∧ x<sub>7</sub> on n = 8: M = 32, sin<sup>2</sup>θ = 1/8, and with r = 2 the success probability is 121/128.

**Phase and amplitude estimation.** On span{ψ<sub>g</sub>, ψ<sub>b</sub>}, G has eigenvalues e<sup>±2iθ</sup>, and |s⟩ is a superposition of the two eigenvectors. Phase estimation with m phase qubits, controlled powers of G and an inverse QFT [Kitaev 1995; Cleve et al. 1998] yields y ∈ {0, …, 2<sup>m</sup> − 1}. Amplitude estimation [Brassard et al. 2002] outputs the *real* estimate ã(y) = sin<sup>2</sup>(πy/2<sup>m</sup>), indexed by the rational grid point y/2<sup>m</sup>. It satisfies |ã − a| ≤ 2π√(a(1−a))/2<sup>m</sup> + π<sup>2</sup>/4<sup>m</sup> with probability at least 8/π<sup>2</sup>. The approximate QFT drops the rotations by angles below 2π/2<sup>kmax</sup> [Coppersmith 1994; Barenco et al. 1996].

### 2.3 Uncomputation, ancilla regimes, Cliffords

**Uncomputation.** A reversible oracle computes intermediate values into ancillae and must return each to |0⟩ independently of the data; otherwise tracing it out decoheres the data.
- *Bennett's construction* uncomputes by running the computation backwards [Bennett 1973, 1989].
- *Gidney's temporary logical-AND* computes a ∧ b into a fresh |0⟩ with four T gates. Its measurement-based uncomputation (MBU) measures the target in the X basis and, on outcome 1, corrects the phase with a CZ on the controls, at no T cost [Gidney 2018].

**Ancilla regimes.**
- *Clean* ancillae start and end in |0⟩.
- *Dirty* ones must be returned to an unknown state.
- *Conditionally clean* ones are known to be in a fixed state whenever the outcome depends on them [Khattar and Gidney 2025], which lets cheaper relative-phase Toffolis [Maslov 2016] replace Toffolis.

**Cliffords.** The Clifford group normalizes the Pauli group. A diagonal unitary diag((−1)<sup>f</sup>) is Clifford exactly when f has degree ≤ 2 over 𝔽<sub>2</sub> [Gottesman 1998; Dehaene and De Moor 2003]. Controlled phases such as controlled-S are not Clifford.

### 2.4 Physical compilation and calibration

**What a device offers.** A device offers a basis gate set (for IBM's Heron processors {rz, sx, x, cz}), a coupling map, and calibration data: error rates, readout errors, T1/T2 and durations.

**What compilation to the device does.** It translates into the basis, places logical qubits, and inserts SWAPs so that two-qubit gates lie on coupling edges, for example by SABRE [Li et al. 2019] in Qiskit [Javadi-Abhari et al. 2024]. It may also reorder commuting gates.

**Calibrated errors.** These are usually randomized-benchmarking average infidelities [Magesan et al. 2011]. For a Pauli error channel of total probability p on d = 2<sup>k</sup> dimensions, the average infidelity is dp/(d+1) [Horodecki et al. 1999; Nielsen 2002]. Calibration numbers do not determine the error channel. Coherent errors, in particular, can have a diamond distance of order √r for an infidelity r, unless the noise is twirled [Wallman and Emerson 2016].

### 2.5 Lean 4

Lean 4 has a small trusted kernel.
- **Mathlib** provides analysis and linear algebra.
- **Physlib** provides density operators (`MState`), CPTP maps, POVMs, the trace distance, partial traces, tensor products of channels, and convex combinations of channels.
- **`decide +kernel`** evaluates a decidable proposition inside the kernel. We forbid `native_decide`, which trusts compiled code and adds the axiom `Lean.ofReduceBool`.
- **`#print axioms`** lists a theorem's axioms, which makes the audit mechanical.

The toolchain is pinned: Lean v4.35.0, Mathlib v4.35.0 (commit 56a0058), Physlib 96a6bc5.


## 3 The realizability framework and the trust model

Definitions and theorems are stated as in Lean (`CQRV/Realizability`). Names in `typewriter` are Lean names.

### 3.1 Specifications and grades

<div class="thm">

**Definition 3.1 (Specification).** A specification is a relation S ⊆ X × Y.
- Its domain is dom S = {x | ∃y. S(x, y)}.
- Composition is relational.
- On a pseudo-metric space Y, the ε-relaxation is S<sup>ε</sup>(x, y) ⟺ ∃y<sub>0</sub>. S(x, y<sub>0</sub>) ∧ d(y, y<sub>0</sub>) ≤ ε.

</div>

<div class="thm">

**Definition 3.2 (Grade).** A grade g = (w, d, t, a) ∈ ℕ<sup>4</sup> records width, depth, T-count and peak ancillae. Sequential and parallel composition are g<sub>1</sub> ⊕ g<sub>2</sub> = (max w, d<sub>1</sub> + d<sub>2</sub>, t<sub>1</sub> + t<sub>2</sub>, max a) and g<sub>1</sub> ⊗ g<sub>2</sub> = (w<sub>1</sub> + w<sub>2</sub>, max d, t<sub>1</sub> + t<sub>2</sub>, a<sub>1</sub> + a<sub>2</sub>). Grades are ordered componentwise, and a budget b is fitted by g ≤ b.

</div>

**In Lean,** ⊕ is the `+` of an additive monoid instance on `Grade`, with unit `0` = (0, 0, 0, 0). Appendix A writes `+`.

**When ⊕ describes a physical pipeline.** Only when two conditions hold:
1. the stages share the data register;
2. each restores its ancillae.

For circuits, Section 6.4 proves that ⊕ *bounds* the measured grade of a concatenation (`grade_append_le`). A second record, `GradeExt`, has five components: two-qubit gates, T-depth, rotations, mid-circuit measurements and feed-forward gates. Its exact counting rules are in Section 4.5.

### 3.2 Realization

Inputs are encoded in the computational basis.

<div class="thm">

**Definition 3.3 (Realization; `Realizes`, `RealizesExact`).** A graded channel Φ = (Φ.chan, Φ.grade) (ε, δ)-*realizes* S under a decoding POVM `dec` within a budget r if

<div class="eq">Φ.grade ≤ r  and  ∀x ∈ dom S.  Pr<sub>y∼dec(Φ.chan(|x⟩⟨x|))</sub>[S<sup>ε</sup>(x, y)] ≥ 1 − δ.</div>

`RealizesExact` is the case ε = 0 with S itself; it needs no metric.

</div>

**Restoration is separate.** Realization constrains the channel after the ancillae are traced out (`GradedChannel.traceAnc`). Restoration, which says they come back clean, is the separate obligation `AncRestore` (Section 5). A circuit can have correct output statistics while its ancillae stay entangled with the data, and it is then useless inside a coherent computation.

**Pseudo-metric outputs.** Amplitude estimation's outcome space carries only a pseudo-metric (Section 6.3), so both composition theorems are also stated on `PseudoMetricSpace`, with the same proofs.

### 3.3 Composition at a measured interface

At a measured interface, the output of Φ is decoded and re-encoded before Ψ runs. In the composite `measuredComp`, the grade is Φ.grade ⊕ Ψ.grade *by definition*: measurement and re-encoding are counted at grade 0.

<div class="thm">

**Theorem 3.4 (Measured composition; report Thm. 3.3a; `measured_composition`).** Let Y, Z be pseudo-metric spaces, Φ ⊩<sup>r</sup><sub>ε<sub>f</sub>,δ<sub>f</sub></sub> S<sub>f</sub> and Ψ ⊩<sup>s</sup><sub>ε<sub>g</sub>,δ<sub>g</sub></sub> S<sub>g</sub>. Assume:
- (i) x ∈ dom S<sub>f</sub> and S<sub>f</sub><sup>ε<sub>f</sub></sup>(x, y) imply y ∈ dom S<sub>g</sub>;
- (ii) for y ∈ dom S<sub>g</sub> and S<sub>g</sub>(y′, z′) there is z with S<sub>g</sub>(y, z) and d(z, z′) ≤ d(y, y′);
- (iii) 0 ≤ δ<sub>f</sub> and 0 ≤ δ<sub>g</sub> ≤ 1.

Then the measured composite (ε<sub>f</sub> + ε<sub>g</sub>, δ<sub>f</sub> + δ<sub>g</sub>)-realizes S<sub>g</sub> ∘ S<sub>f</sub> within r ⊕ s.

</div>

<div class="proof">

*Proof idea.* Let y be an intermediate outcome with S<sub>f</sub><sup>ε<sub>f</sub></sup>(x, y). It has a witness y<sub>0</sub> with S<sub>f</sub>(x, y<sub>0</sub>) and d(y, y<sub>0</sub>) ≤ ε<sub>f</sub>; hence ε<sub>f</sub> ≥ 0, so S<sub>f</sub><sup>ε<sub>f</sub></sup>(x, y<sub>0</sub>) holds and y<sub>0</sub> ∈ dom S<sub>g</sub> by (i). Let z<sub>out</sub> be a final outcome with S<sub>g</sub><sup>ε<sub>g</sub></sup>(y, z<sub>out</sub>). It has a witness z′ with S<sub>g</sub>(y, z′) and d(z<sub>out</sub>, z′) ≤ ε<sub>g</sub>.

Apply (ii) at y<sub>0</sub> with the pair (y, z′). This gives z<sub>0</sub> with S<sub>g</sub>(y<sub>0</sub>, z<sub>0</sub>) and d(z<sub>0</sub>, z′) ≤ d(y<sub>0</sub>, y). By symmetry and the triangle inequality,

<div class="eq">d(z<sub>out</sub>, z<sub>0</sub>) ≤ d(z<sub>out</sub>, z′) + d(z′, z<sub>0</sub>) ≤ ε<sub>g</sub> + ε<sub>f</sub>,</div>

which is the event inclusion (`relax_comp`). The probability bound is a mixture argument (`mixture_union_bound`): (1 − δ<sub>f</sub>)(1 − δ<sub>g</sub>) ≥ 1 − δ<sub>f</sub> − δ<sub>g</sub>, which uses (iii).

</div>

**On the hypotheses.**
- The report states the theorem without (i)–(iii), and the formalization showed that each is needed.
- No hypothesis ε ≥ 0 is needed: a negative ε makes the relaxed event empty, which forces dom S = ∅ or δ ≥ 1.
- The exact case needs only (i) and (iii).

**A logical bound, not a physical one.** The theorem is a *logical* bound. A physical pipeline also pays for the measurement, the classical computation between the stages, the selection of the next circuit, re-preparation of the register, and latency. Achieving width max(w<sub>1</sub>, w<sub>2</sub>) with different data widths relies on re-preparing the register between runs.

### 3.4 The diamond distance and coherent composition

Physlib has no diamond norm. We define it from the tensor of a channel with the identity and the partial trace.

<div class="thm">

**Definition 3.5 (`diamondDist`).** For Λ<sub>1</sub>, Λ<sub>2</sub> : 𝒟(ℋ<sub>A</sub>) → 𝒟(ℋ<sub>B</sub>),

<div class="eq">d<sub>⋄</sub>(Λ<sub>1</sub>, Λ<sub>2</sub>) = sup<sub>ρ∈𝒟(ℋ<sub>A</sub>⊗ℋ<sub>A</sub>)</sub> 2 T((Λ<sub>1</sub> ⊗ id<sub>A</sub>)ρ, (Λ<sub>2</sub> ⊗ id<sub>A</sub>)ρ).</div>

</div>

**The reference system.** It has the input's dimension. That this equals ‖Λ<sub>1</sub> − Λ<sub>2</sub>‖<sub>⋄</sub> is cited [Watrous 2018, §3.3], not proved, and no theorem below depends on it.

<div class="thm">

**Lemma 3.6.** d<sub>⋄</sub> is a bounded pseudo-metric on channels with values in [0, 2]. Composition does not increase it, in two forms:
- *post-composition* (`diamondDist_compose_le`): d<sub>⋄</sub>(Ψ ∘ Φ<sub>1</sub>, Ψ ∘ Φ<sub>2</sub>) ≤ d<sub>⋄</sub>(Φ<sub>1</sub>, Φ<sub>2</sub>);
- *pre-composition by an endomorphism Λ of the input space* (`diamondDist_precompose_le`): d<sub>⋄</sub>(Φ<sub>1</sub> ∘ Λ, Φ<sub>2</sub> ∘ Λ) ≤ d<sub>⋄</sub>(Φ<sub>1</sub>, Φ<sub>2</sub>).

Pre-composition needs an endomorphism because (Λ ⊗ id)ρ must again be a state on A × A.

</div>

<div class="thm">

**Lemma 3.7 (Domination; `diamond_dominates`).** For every ρ, 2 T(Λ<sub>1</sub>ρ, Λ<sub>2</sub>ρ) ≤ d<sub>⋄</sub>(Λ<sub>1</sub>, Λ<sub>2</sub>).

</div>

<div class="proof">

*Proof.* Use the input ρ ⊗ ρ. The partial trace over the reference recovers Λ<sub>i</sub>ρ, and it is a channel. Data processing therefore bounds 2 T(Λ<sub>1</sub>ρ, Λ<sub>2</sub>ρ) by twice the trace distance of the stabilized outputs, which is at most the supremum.

</div>

<div class="thm">

**Theorem 3.8 (Coherent composition; report Thm. 3.3b; `coherent_composition_diamond`).** Let Φ<sub>1</sub>, Φ<sub>2</sub> : 𝒟(ℋ<sub>X</sub>) → 𝒟(ℋ<sub>D</sub>) and Ψ<sub>1</sub>, Ψ<sub>2</sub> : 𝒟(ℋ<sub>D</sub>) → 𝒟(ℋ<sub>E</sub>). Assume:
- Ψ<sub>1</sub> ∘ Φ<sub>1</sub> (ε<sub>0</sub>, δ<sub>0</sub>)-realizes S under a POVM on ℋ<sub>E</sub>;
- d<sub>⋄</sub>(Φ<sub>2</sub>, Φ<sub>1</sub>) ≤ η<sub>f</sub> and d<sub>⋄</sub>(Ψ<sub>2</sub>, Ψ<sub>1</sub>) ≤ η<sub>g</sub>.

Then Ψ<sub>2</sub> ∘ Φ<sub>2</sub> (ε<sub>0</sub>, δ<sub>0</sub> + ½(η<sub>f</sub> + η<sub>g</sub>))-realizes S within the sum of the grades.

</div>

**The proof** uses only the triangle inequality, data processing for Ψ<sub>2</sub>, and domination on the basis input. It does not use pre-composition, which is why Φ<sub>1</sub> need not be an endomorphism. The n-step noise theorem of Section 8 does need pre-composition, and therefore works on one space.

### 3.5 The obstruction theorem

The report's Theorem 3.1 is a categorical no-cloning statement [Abramsky 2010]. We mechanize a linear-algebra core.

<div class="thm">

**Theorem 3.9 (No-cloning).** Let X be a finite type.
1. If X is non-empty, there is no ℂ-linear C : ℂ<sup>X</sup> → ℂ<sup>X×X</sup> with Cψ = ψ ⊗ ψ for all ψ (`no_cloning_linear`); for |X| ≥ 2 this also follows by superposition (`no_cloning_obstruction`).
2. If |X| ≥ 2, there is no ℂ-linear Φ : M<sub>X</sub>(ℂ) → M<sub>X×X</sub>(ℂ) with Φ(|ψ⟩⟨ψ|) = |ψ⟩⟨ψ| ⊗ |ψ⟩⟨ψ| for every unit vector ψ (`no_cloning_pure`).
3. If |X| = 1, such a Φ exists: Φ(M) = M ⊗ I (`pure_cloning_of_card_one`).

</div>

**Which statement is about states.** Part 1 needs only scaling: C(2e<sub>i</sub>) has the entry 4 at (i, i), while 2Ce<sub>i</sub> has 2. Scaling is not available on unit vectors, so part 1 says nothing about states. Part 2 is the statement about pure states. With ψ<sub>±</sub> = (e<sub>i</sub> ± e<sub>j</sub>)/√2 one has |ψ<sub>+</sub>⟩⟨ψ<sub>+</sub>| + |ψ<sub>−</sub>⟩⟨ψ<sub>−</sub>| = E<sub>ii</sub> + E<sub>jj</sub>, and linearity forces the entry ((i, i), (j, j)) of the two sides to agree: it is 1/2 on one side and 0 on the other. Part 3 shows that |X| ≥ 2 is exactly the right hypothesis: a single unit ray can be cloned. The categorical (functorial) statement itself is not mechanized.

### 3.6 The trust model

Every certificate kind rests on a stated set of components outside the kernel and of model premises. Table 1 lists them. The rest of the paper refers to this table instead of repeating its caveats.

<p class="caption"><b>Table 1.</b> What each certificate kind assumes. "Kernel" means checked by the Lean kernel with the axioms exactly <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>.</p>

| Certificate kind | Kernel-checked | Outside the kernel (declared) | Model premises |
|---|---|---|---|
| Logical (search) | the theorem `cert`: realization ∧ restoration of the circuit literal; `emitted_ok` (synthesis re-run); grades; the count M (n ≤ limit); `front_end` (typed term ↔ network) | parser, surface checker (incl. call inlining), the printer of the typed-term literal; extraction and the matcher's run (the theorem restates the instance); the emitters (QIR / QASM validated by re-parse); the toolchain | ideal gates; exact initial \|0⟩; M is a hypothesis above the count limit |
| Logical (counting) | as above, with the grade a certified compositional *upper bound* from per-block kernel-measured grades | as above | as above; M ≥ 1 |
| Physical | the logical theorem; `emitted_eq`; the reconstruction of the routed circuit from the witness and its equality with the transpiler's output; coupling edges; the channel transfer; `PhysGrade` | Qiskit (transpiler and fake backends); the target file's content (bound by hash); the printer of `physical.qasm` | an ideal device with the target's gates and connectivity; (P-prep) exact all-\|0⟩ preparation; (P-ctrl) exact classical control and bookkeeping; the feed-forward latency L, used for timing only |
| Conditional (noise) | the above, plus the noise theorem at the instance and the exact bound δ′ | as above; the calibration snapshot (bound by hash) | (P-cal), (P-stoch), (P-ro), (P-idle) of Section 8.3, in addition to (P-prep) and (P-ctrl) |
| Selection | admissibility and minimality of the choice among candidates whose grades the kernel computed | the candidates' artifacts, each linked by hash to its own check file | as for the candidates |


## 4 The certifying compiler

**The command-line tool.** `cqr` exposes the stages `check`, `extract`, `match`, `synthesize`, `certify` and `emit`, and the hardware subcommands of Section 7. Every stage is a total Lean function returning a result or a machine-readable diagnostic. The executable's import closure is 62 modules over `Lean` and `Mathlib` only. The semantics and the theorems are on the Physlib side.

<figure>
<svg viewBox="0 0 760 175" width="100%" xmlns="http://www.w3.org/2000/svg" font-family="Cambria, serif" font-size="12">
<defs><marker id="ar" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0,0 L8,4 L0,8 z" fill="#333"/></marker></defs>
<rect x="10" y="20" width="110" height="46" rx="6" fill="#eeeeee" stroke="#666"/><text x="65" y="40" text-anchor="middle">source text</text><text x="65" y="56" text-anchor="middle" font-size="10">parse, check, inline</text>
<rect x="150" y="20" width="120" height="46" rx="6" fill="#dbe8f6" stroke="#36c"/><text x="210" y="40" text-anchor="middle">typed term → network</text><text x="210" y="56" text-anchor="middle" font-size="10">toNetwork (proved)</text>
<rect x="300" y="20" width="120" height="46" rx="6" fill="#eeeeee" stroke="#666"/><text x="360" y="40" text-anchor="middle">extractor ℰ</text><text x="360" y="56" text-anchor="middle" font-size="10">ground signature</text>
<rect x="450" y="20" width="130" height="46" rx="6" fill="#dbe8f6" stroke="#36c"/><text x="515" y="40" text-anchor="middle">signature matcher</text><text x="515" y="56" text-anchor="middle" font-size="10">sound; complete on fragment</text>
<rect x="610" y="20" width="140" height="46" rx="6" fill="#dbe8f6" stroke="#36c"/><text x="680" y="40" text-anchor="middle">synthesis, instance</text><text x="680" y="56" text-anchor="middle" font-size="10">re-run by the kernel</text>
<rect x="450" y="105" width="130" height="46" rx="6" fill="#dbe8f6" stroke="#36c"/><text x="515" y="125" text-anchor="middle">Cert.lean</text><text x="515" y="141" text-anchor="middle" font-size="10">kernel check, axiom audit</text>
<rect x="300" y="105" width="120" height="46" rx="6" fill="#eeeeee" stroke="#666"/><text x="360" y="125" text-anchor="middle">QIR / OpenQASM 3</text><text x="360" y="141" text-anchor="middle" font-size="10">re-parse (structure)</text>
<rect x="150" y="105" width="120" height="46" rx="6" fill="#f6e7d5" stroke="#c63"/><text x="210" y="125" text-anchor="middle">Qiskit routing</text><text x="210" y="141" text-anchor="middle" font-size="10">untrusted; witness</text>
<rect x="10" y="105" width="110" height="46" rx="6" fill="#dbe8f6" stroke="#36c"/><text x="65" y="125" text-anchor="middle">PhysCert.lean</text><text x="65" y="141" text-anchor="middle" font-size="10">reconstruction, noise</text>
<line x1="120" y1="43" x2="148" y2="43" stroke="#333" marker-end="url(#ar)"/><line x1="270" y1="43" x2="298" y2="43" stroke="#333" marker-end="url(#ar)"/><line x1="420" y1="43" x2="448" y2="43" stroke="#333" marker-end="url(#ar)"/><line x1="580" y1="43" x2="608" y2="43" stroke="#333" marker-end="url(#ar)"/>
<line x1="680" y1="66" x2="582" y2="120" stroke="#333" marker-end="url(#ar)"/><line x1="450" y1="128" x2="422" y2="128" stroke="#333" marker-end="url(#ar)"/><line x1="300" y1="128" x2="272" y2="128" stroke="#333" marker-end="url(#ar)"/><line x1="150" y1="128" x2="122" y2="128" stroke="#333" marker-end="url(#ar)"/>
</svg>
<figcaption><b>Figure 1.</b> The pipeline. Grey: outside the kernel, validated or declared. Blue: proved, or re-checked by the kernel inside a certificate. Orange: the untrusted transpiler, whose output is reconstructed and checked.</figcaption>
</figure>

### 4.1 The input language: surface and core

**The language.** It is a side-effect-free functional language over `Bool`, `Vec Bool n` and bounded naturals `Nat n`. It has `let`, `if`, the Boolean connectives, indexing, bounded folds `for i in [0 ..< n] with acc = e do e'`, and non-recursive calls. The *surface checker* inlines every call before producing a typed term, and it rejects any cycle in the call graph (`non_structural_recursion`). Inlining is therefore part of the unverified front of the pipeline.

**The `loop` construct.** The surface language also has a functional `loop … while c do …` with no static bound. It exists so that such programs reach the matcher and receive a repair hint rather than a syntax error. In the typed term:
- the reference evaluator `evalProgram` is total and structural: on a `loop` it returns the loop's initial value, a totality device with no intended semantics;
- the network builder rejects `loop` with `unbounded_loop`.

**The core language.** The proved statements are therefore about the *loop-free core*. Theorem 4.1's premise `toNetwork prog = .ok net` already implies that `prog` contains no `loop`. Separating the surface and core languages in the definitions themselves is planned (`docs/REVIEW_RESPONSE_1.md`, R9).

<div class="thm">

**Theorem 4.1 (Front end; `toNetwork_pred`, `toNetwork_WF`, `toNetwork_succeeds`).** For a *scoped* typed program `prog` (a decidable predicate: every variable refers to a binding in scope), if `toNetwork prog = .ok net`, then:
- `net` is well formed;
- `evalProgram prog x = Network.pred net n x` for every x.

`toNetwork` succeeds on every scoped program without `loop`.

</div>

**In the certificate.** Every certificate contains the typed-term literal `prog` with the kernel-checked facts `prog_scoped`, `net_ok : toNetwork prog = .ok net` and `front_end`. The source text is bound by `predicate_hash`.

**Why the parser is not run in the kernel.** It is a total, fuel-bounded Lean function, so in principle it could run in the kernel on a string literal. Kernel evaluation of string processing is slow, and we have not attempted it.

### 4.2 Extraction and the solution count

**The signature.** The extractor ℰ computes a ground signature with these fields:
- the problem class;
- the arity n;
- the solution count M, when it is symbolic: a conjunction of k literals on distinct bits gives M = 2<sup>n−k</sup>;
- the static iteration bound of the source's loops (`iter`; for the running example 1, not the Grover repetition count r = 2);
- the oracle structure;
- an upper bound ĉ<sub>∧</sub> on the multiplicative complexity;
- the AND-depth.

**When M is not symbolic.** It must be supplied (`--solutions M`); otherwise matching fails with a gap at M (Section 4.3). For n at most the count limit (10 by default), the CLI evaluates the count and the certificate re-decides it in the kernel (`hM_count`). A supplied M that differs from it is the diagnostic `solution_count_mismatch`. Computing the true multiplicative complexity is NP-hard [Boyar et al. 2000], so ĉ<sub>∧</sub> is only a bound, and certified grades are always measured on the synthesized circuit.

### 4.3 Signature matching and repair hints

**Patterns.** A library entry carries a precondition pattern over first-order terms with AC sets. In φ<sub>Grover</sub> = ⟨Search, n:F<sub>1</sub>, M:F<sub>2</sub>, P:Bool<sup>F<sub>1</sub></sup>→Bool, iter:bounded(F<sub>3</sub>), oracle:PhaseKickback(Multiplicative, F<sub>4</sub>)⟩ with F<sub>2</sub> ≥ 1, Bool<sup>F<sub>1</sub></sup>→Bool is the term encoding of the type `Vec Bool n -> Bool`. Patterns lie in Miller's fragment [Miller 1991].

<div class="thm">

**Theorem 4.2 (`millerMatch_sound`).** If the matcher returns σ on φ and t, then φσ = t.

</div>

**Completeness.** The matcher is also complete on Miller patterns of uniform arity (Theorem 6.11). This is completeness of *signature matching*: a rejection is proved relative to the extracted signature and the library. It is not a proof that no circuit in the synthesis library could realize the original program. The extractor is not proved, and its symbolic count covers only special cases.

**Repair hints.** On failure, the least general generalization [Plotkin 1970; Reynolds 1970] of the signature and the partially instantiated pattern marks the gaps. Near misses are ranked by the number of gaps (`dist`) and the size of what they replace, among entries with the term's root shape. Hints are heuristic. For example, `examples/search_while.cqr` without `--solutions` yields `dist` 2, with gaps at M and at `iter`, and the suggestion to bound the loop.

### 4.4 Oracle synthesis

**Networks and affine forms.** Synthesis starts from a Boolean network of input, constant, NOT, AND and XOR nodes. Each value is an affine form over 𝔽<sub>2</sub>: a sorted list of atoms (inputs and AND results) and a constant. NOT and XOR cost nothing at the node.

**An AND of operands u, v:**
- *exact identities* (1 ∧ v, 0 ∧ v, u ∧ u, u ∧ ¬u) emit nothing;
- *otherwise `prepare`* gathers u onto its smallest atom p<sub>u</sub> by CNOTs. If p<sub>u</sub> occurs in v, with linear parts {p<sub>u</sub>} ∪ R<sub>u</sub> and {p<sub>u</sub>} ∪ R<sub>v</sub>, then after the gather v's linear part in the new qubit contents is {p<sub>u</sub>} ∪ (R<sub>u</sub> △ R<sub>v</sub>). Its pivot is taken from R<sub>u</sub> △ R<sub>v</sub>, and p<sub>u</sub> remains among the atoms gathered onto it;
- a fresh ancilla receives u ∧ v by the temporary logical-AND, and the uncompute block replays the preparation around the MBU.

**The oracle** is compute blocks, a phase flip (a Z on the gathered output), and uncompute blocks in reverse order. Its width is n + #AND, and t = 4·#AND.

**Bennett pebbling** [Bennett 1989; Meuli et al. 2019]. For AND chains it is available under an ancilla budget, by a 0–1 breadth-first search where placing a pebble (an AND, 4 T) costs 1 and removing one (an MBU) costs 0. Pebbled oracles are tested, not certified.

### 4.5 The circuit IR, its semantics, and resource accounting

**Gates.** H, X, Z, S, S<sup>†</sup>, T, T<sup>†</sup>, CNOT and CZ; the exact phase gates `p a k` = diag(1, e<sup>2πi a/2<sup>k</sup></sup>) and `cp a k` (a ∈ ℤ, k ∈ ℕ); `measure q -> j`; `ifBit j g` (g Clifford); and `alloc` / `free`.

**Kraus-branch semantics.** Each assignment c of the classical bits gives a Kraus operator K<sub>c</sub>:
- `measure` is the projector onto q = c<sub>j</sub>;
- `ifBit j g` is g if c<sub>j</sub>, and I otherwise;
- `alloc` and `free` denote I: restoration is proved, not assumed.

The channel is Σ<sub>c</sub> K<sub>c</sub>ρK<sub>c</sub><sup>†</sup> (`channelDenote`). Completeness needs the bit discipline (each bit written once before it is read), which is part of `Circuit.WF`.

**Resource accounting.** These are the exact rules of `CQRV/Circuit/IR.lean`:
- **T-count.** `t` and `tdg` count 1. `p a k` counts 1 iff its angle is an odd multiple of π/4, that is 2<sup>k</sup> ∣ 8a and 2<sup>k</sup> ∤ 4a. `cp` counts 0. `ifBit` counts its gate.
- **Clifford.** `p a k` is Clifford iff 2<sup>k</sup> ∣ 4a. `cp a k` is Clifford iff 2<sup>k</sup> ∣ 2a, which makes it CZ or the identity.
- **`rot`.** It counts the `p` and `cp` gates that are neither Clifford nor T-powers. This includes every controlled phase other than CZ, controlled-S among them, since CS is not Clifford.

The grade's t is therefore a *native-gate* T-count. Arbitrary-angle `p` and `cp` are treated as native rotations, and their Clifford+T synthesis cost at a chosen precision is **not** included. It is reported only through `rot`.

**Depth.** An as-soon-as-possible scheduler computes depth, T-depth and the peak of live ancillae. It was fixed before any number was compared with the specification.

### 4.6 Certificates, emission, and their limits

**Certificate forms.**
- A *flat* certificate states `emitted_ok`, `grade_eq` and `gradeExt_eq` by kernel evaluation on the whole circuit literal. Its grade is *measured*.
- Above a measured ceiling (Section 6.4), a *compositional* certificate measures each named block and bounds the whole by ⊕. Its grade is an *upper bound*.

**Hashes.** SHA3-256 [NIST 2015] is implemented in Lean. `predicate_hash`, `circuit_hash` and `proof_hash` bind the source, the circuit and the Lean file with the pinned toolchain. `hashes.library` binds the certificate to the library it was checked against: a hash over every Lean file of the library and the CLI, with the build files. Re-certification in CI compares certificates modulo this field, and a release check requires every recorded library hash to be current. Hardware files cite a logical certificate by its hash modulo the library field, so a library change does not ripple into them.

**Emission.** QIR (Adaptive Profile) and OpenQASM 3 [QIR Alliance 2024; Cross et al. 2022] are emitted from the circuit literal and re-parsed. For QIR, `p a k` is printed as `rz` with a binary floating-point angle, which generally differs from 2πa/2<sup>k</sup>. The re-parse therefore validates the gate structure and the numerical round trip of the printed number. It does not establish exact equality between the emitted floating-point circuit and the exact IR rotation. A proved bound on the resulting channel error, through the operator-norm argument of Lemma 6.4, is a planned addition (R6).


## 5 Restoration under measurement

This section collects everything the development proves about returning ancillae to their initial state:
- the restoration predicate and its proof template;
- measurement-based uncomputation, from the AND gadget to a general theorem and its Clifford boundary;
- restoration of every synthesized oracle;
- an algebra of restoration and three ancilla regimes;
- the two-ancilla diffusion and its T-count bound.

### 5.1 The predicate and a proof template

<div class="thm">

**Definition 5.1 (`AncRestore`).** A circuit C on Reg<sub>n</sub> × Reg<sub>a</sub> restores its ancillae and applies a unitary U if, for every ρ ∈ 𝒟(ℋ<sub>Reg<sub>n</sub></sub>),

<div class="eq">⟦C⟧(ρ ⊗ |0<sup>a</sup>⟩⟨0<sup>a</sup>|) = UρU<sup>†</sup> ⊗ |0<sup>a</sup>⟩⟨0<sup>a</sup>|.</div>

</div>

**Why this form.** The predicate quantifies over all data density operators. Its left-hand side is the full Kraus channel, measurement branches included, so it covers MBU, whose individual branches are not unitary on the joint register. Tracing out the ancillae gives UρU<sup>†</sup>, and restoration statements compose under concatenation.

<div class="thm">

**Lemma 5.2 (`ancRestore_of_kraus`).** Let C be well formed with m classical bits, let U be unitary, and let λ : {0,1}<sup>m</sup> → ℂ. Suppose that in every branch c, K<sub>c</sub>(|ψ⟩ ⊗ |0<sup>a</sup>⟩) = λ<sub>c</sub>(U|ψ⟩) ⊗ |0<sup>a</sup>⟩. Then `AncRestore`(C, U).

</div>

**The branch scalars.** Σ<sub>c</sub>|λ<sub>c</sub>|<sup>2</sup> = 1 follows from Kraus completeness (`sum_norm_sq_eq_one_of_kraus`); an earlier version assumed it. The scalars absorb every phase that is invisible on density operators: a measurement branch's 1/√2, a correction's unit factor λ, and a global sign.

### 5.2 Measurement-based uncomputation

<div class="thm">

**Theorem 5.3 (MBU correctness; `mbu_channel_correct`).** On three qubits (a, b, t), consider the circuit that:
1. computes a ∧ b into t by the temporary logical-AND;
2. applies Z to t;
3. uncomputes by MBU: H t, measure t, and on outcome 1 a CZ on a, b and an X on t.

It maps ρ ⊗ |0⟩⟨0| to CZ ρ CZ<sup>†</sup> ⊗ |0⟩⟨0| for every two-qubit ρ.

</div>

**A missing gate.** The published listing reproduced by the specification omits the X on t, so on outcome 1 it leaves t in |1⟩. The statevector harness found the failing branch, and the theorem is about the corrected listing. The general form of the theorem separates what is being uncomputed from how.

<div class="thm">

**Definition 5.4 (`ComputesInto`, `PhaseImpl`, `mbuUncompute`).**
- A measurement-free list B *computes f into the ancilla t with phase φ* if |φ(x)| = 1 and B(|x⟩ ⊗ |0<sup>a</sup>⟩) = φ(x)|x⟩ ⊗ |e<sub>t</sub>(f(x))⟩ for every basis input x. Here e<sub>t</sub>(b) is the ancilla basis state with qubit t set to b and every other ancilla 0.
- A measurement-free list O on the data is a *phase implementation* of f if its unitary is λ·diag((−1)<sup>f(x)</sup>) ⊗ I with |λ| = 1.
- The MBU uncompute is `mbuUncompute t j O` = [H t, measure t → j] ++ (O under `ifBit j`) ++ [`ifBit j` (X t)].

</div>

<div class="thm">

**Theorem 5.5 (General MBU; `mbu_general`).** Let C be well formed with gates B ++ `mbuUncompute t j O`, where t = `anc i` with i < a, B computes f into t with phase φ, and O is a phase implementation of f. Then `AncRestore`(C, diag φ).

</div>

<div class="proof">

*Proof idea.* It suffices to compute each branch on a basis input. B gives φ(x)|x⟩|e<sub>t</sub>(f(x))⟩. H on t and the projection onto outcome b give (1/√2)(−1)<sup>b·f(x)</sup>φ(x)|x⟩|e<sub>t</sub>(b)⟩.
- *Outcome 0:* nothing more acts, and the branch is (1/√2)φ(x)|x⟩|0<sup>a</sup>⟩.
- *Outcome 1:* O multiplies by λ(−1)<sup>f(x)</sup>, which cancels the sign, and X resets t. The branch is (λ/√2)φ(x)|x⟩|0<sup>a</sup>⟩.

Lemma 5.2 applies with the branch scalars 1/√2 and λ/√2.

</div>

**Recovering Theorem 5.3.** The AND/MBU pair is the instance in which the compute block includes the phase kick: B′ = (temporary logical-AND) ++ [Z t], which computes a ∧ b into t with φ(a, b) = (−1)<sup>a∧b</sup>, and O = [CZ a b]. Theorem 5.5 then gives `AncRestore`(C, CZ); this re-derivation is `mbu_channel_correct_of_general`. With B the AND alone, φ ≡ 1 and the data unitary is the identity, as it should be.

**Several ancillae.** Theorem 5.5 is about one ancilla. Oracles with several ANDs pair their MBU blocks from the inside out. Section 5.3 does this for synthesized oracles, and Section 5.5 gives the composition laws.

### 5.3 Restoration of every synthesized oracle

<div class="thm">

**Theorem 5.6 (Report Lemma 6.3.2; `lemma_6_3_2_xor`).** If `synthesizeOracle N = ok C` and C is well formed, then `AncRestore`(C, O<sub>P<sub>N</sub></sub>), with P<sub>N</sub> the network's predicate. The same holds on every larger ancilla register.

</div>

<div class="proof">

*Proof idea.* The synthesizer is a fold over the nodes. Its invariant records, for each processed AND, the operands' affine forms, the preparation, the target ancilla and its value. Under this invariant:
- the compute blocks map |x⟩|0⟩ to |x⟩|v(x)⟩;
- the phase flip contributes (−1)<sup>P<sub>N</sub>(x)</sup>;
- each uncompute block, in reverse order, meets the hypothesis of the MBU gadget, because everything after it is already undone.

Lemma 5.2 concludes.

</div>

<div class="thm">

**Theorem 5.7 (`synthesizeOracle_WF`, `synthesizeOracle_succeeds`).** For a well-formed network N (inputs in range, operands below their node, outputs are nodes):
- `synthesizeOracle N = ok C` implies C is well formed;
- if N has one output, synthesis succeeds.

</div>

**The hypotheses are necessary.** A network whose only node reads input 5 of an empty input set synthesizes a gate outside the register. A network with no output is rejected.

<div class="thm">

**Theorem 5.8 (Coherent mode; `lemma_6_3_2_coherent`).** Theorems 5.6 and 5.7 hold when every AND is uncomputed by the adjoint of its compute block. This mode uses no measurement and no feed-forward, at 8 T per AND, and `Circuit.adjoint` is proved to denote the adjoint channel.

</div>

### 5.4 The Clifford boundary of MBU corrections

<div class="thm">

**Definition 5.9.**
- f is *quadratic* if f(x) = c + Σ a<sub>i</sub>x<sub>i</sub> + Σ b<sub>ij</sub>x<sub>i</sub>x<sub>j</sub> over 𝔽<sub>2</sub>.
- A diagonal D is *Clifford-diagonal* if D X<sub>i</sub> D<sup>†</sup> = λ·X<sub>i</sub>Z<sup>b</sup> for every qubit i, for some unit λ and some b.

</div>

<div class="thm">

**Theorem 5.10 (`clifford_iff_quadratic`).** diag((−1)<sup>f</sup>) is Clifford-diagonal iff f is quadratic.

</div>

**Proof idea.** Conjugating X<sub>i</sub> gives X<sub>i</sub>·diag((−1)<sup>∂<sub>i</sub>f</sup>), where ∂<sub>i</sub>f(x) = f(x) + f(x ⊕ e<sub>i</sub>). This is a Pauli iff every derivative is affine, iff f is quadratic (`isQuadratic_iff_deriv_affine`).

**What is new.** The characterization is classical [Dehaene and De Moor 2003]. What is new is its use in the restoration semantics and the boundary theorem below. A quadratic f has a correction made of Z and CZ gates (`phaseCircuitQuad`), and a constant term of f is a global sign absorbed into λ.

<div class="thm">

**Theorem 5.11 (The IR boundary; `mbu_exactly_quadratic`).** Let B be unitary on in-range qubits, and let t = `anc i` with i < a (so a ≥ 1). There exist a bit j, a correction O and a well-formed C with C.nData = n and gates B ++ [Z t] ++ `mbuUncompute t j O`, with O a phase implementation of f, **iff** f is quadratic.

</div>

**The argument.** `IsClifford` means that conjugation maps every Pauli monomial to a Pauli monomial. The direction from well-formedness uses three facts:
- every IR Clifford gate is Clifford on the whole register (`gateU_isClifford`);
- products of Cliffords are Clifford;
- a Clifford diagonal of the form D ⊗ I has a Clifford-diagonal D (`isCliffordDiag_of_tensor`), which uses a ≥ 1.

**Consequence.** A degree-3 function cannot be uncomputed by MBU in this IR, because its correction would be a non-Clifford gate under classical control.

**Note.** f is a free parameter here: the theorem characterizes the corrections that are admissible, not which f a given B computes. The bit j must be existential. With a fixed j ≥ 1 the statement is false, because the bit discipline requires every bit below the bit count to be written.

### 5.5 An algebra of restoration

<div class="thm">

**Theorem 5.12 (Stage 23a).**
1. Block lists restore with the product of their unitaries (`ancRestore_list`).
2. If the branches satisfy K<sub>c</sub>(· ⊗ |0⟩) = λ<sub>c</sub>(U<sub>c</sub> ·) ⊗ |0⟩ with branch-dependent unitaries, then the ancilla is restored and the data undergoes the mixed-unitary channel Σ<sub>c</sub>|λ<sub>c</sub>|<sup>2</sup> U<sub>c</sub>ρU<sub>c</sub><sup>†</sup> (`ancRestoreMix_of_kraus`).
3. Without its correction, MBU still restores the ancilla, but dephases the data: ρ ↦ ½D<sub>0</sub>ρD<sub>0</sub><sup>†</sup> + ½D<sub>1</sub>ρD<sub>1</sub><sup>†</sup>, with D<sub>0</sub> = diag φ and D<sub>1</sub> = diag(φ·(−1)<sup>f</sup>) (`mbu_uncorrected`).
4. Restoration holds on any larger ancilla register, so blocks with different ancilla counts compose (`AncRestore.widen`, `comp_widen`).

</div>

**What item 3 says.** It is the precise sense in which the correction is necessary: without it, the data loses coherence across the split by the value of f.

### 5.6 Three ancilla regimes

<div class="thm">

**Definition 5.13 (Regimes).**
- *Clean* is `AncRestore`.
- *Dirty* (`AncRestoreDirty`): ⟦C⟧(ρ ⊗ σ) = UρU<sup>†</sup> ⊗ σ for every data state ρ and every ancilla state σ.
- *Conditionally clean* under a predicate cond on the data (`AncRestoreCond cond`): ⟦C⟧(ω) = (U ⊗ I)ω(U ⊗ I)<sup>†</sup> for every joint state ω supported on V<sub>cond</sub> = span{|x, w⟩ : cond(x) → w = 0}.

</div>

**Extreme cases.** V<sub>false</sub> is the whole space, and V<sub>true</sub> = ℋ<sub>D</sub> ⊗ |0<sup>a</sup>⟩.

<div class="thm">

**Theorem 5.14 (Implications and separations; Stage 23b).**
1. Dirty = Cond(false) ⇒ Cond(cond) ⇒ Cond(true) ⇔ Clean (`ancRestoreCond_true_iff`), and Cond(c<sub>1</sub>) ⇒ Cond(c<sub>2</sub>) when c<sub>1</sub> implies c<sub>2</sub> pointwise (then V<sub>c<sub>2</sub></sub> ⊆ V<sub>c<sub>1</sub></sub>).
2. Each regime is closed under sequential composition.
3. *Dirty is strictly stronger than clean:* no MBU circuit with its reset is dirty-restoring, since a dirty ancilla in |1⟩ is reset to |0⟩ (`reset_not_dirty`).
4. A concrete CZ-based circuit is conditionally clean under x<sub>0</sub> and clean, but not dirty; the pure state |1⟩⟨1| ⊗ |+⟩⟨+| separates it.

</div>

**Cond(true) and Clean.** They are equivalent, and the equivalence is proved. The direction Clean ⇒ Cond(true) rests on a support-factorization lemma (`supportFactor`): a state ω supported on V<sub>true</sub> equals tr<sub>anc</sub>(ω) ⊗ |0⟩⟨0|, because every entry with a non-zero ancilla index vanishes. The clean statement applied to tr<sub>anc</sub>(ω) then gives the conditional equation. We therefore claim the implications, the equivalence at cond ≡ true, and the two separations above, not a strict hierarchy.

**The Khattar–Gidney construction** is clean as a whole. Conditional cleanliness enters it only as an internal invariant (clause (b) of Theorem 5.17), tied to the regime by one bridge lemma (`Inv.cond_value`).

### 5.7 The diffusion and a two-ancilla multi-controlled Z for every n

**The diffusion.** It is D<sub>n</sub> = H<sup>⊗n</sup>X<sup>⊗n</sup>·O<sub>P<sub>all</sub></sub>·X<sup>⊗n</sup>H<sup>⊗n</sup> with P<sub>all</sub> = y<sub>0</sub> ∧ ⋯ ∧ y<sub>n−1</sub>, which equals I − 2|s⟩⟨s| = −(2|s⟩⟨s| − I). In Lean, `diffU` is 2|s⟩⟨s| − I. The circuit's global sign −1 is a branch scalar in Lemma 5.2 and is invisible to `AncRestore`, so `AncRestore`(D, `diffU`) holds. The sign matters only when the diffusion is *controlled*, and the counting circuit corrects it by a Z on the control (Section 6.3).

**Ancilla counts.** With a balanced tree of ANDs for P<sub>all</sub>, D<sub>8</sub> has grade (15, 41, 28, 7), using seven ancillae. The specification claims (10, 16, 28, 2) without a source. We surveyed the constructions (Table 2), implemented two from Khattar and Gidney's conditionally clean ancillae with Maslov's relative-phase Toffolis (RTOF), and proved one correct for every n.

<p class="caption"><b>Table 2.</b> Constructions surveyed for an n-qubit MCZ with few ancillae (T-counts for n = 8; k = n − 1 controls in Khattar and Gidney's convention).</p>

| Construction | Ancillae | T-count; remarks |
|---|---|---|
| temporary-AND tree [Gidney 2018] | n − 1 clean | 4(n − 1) = 28 |
| Barenco et al. Lemma 7.2 [1995] | dirty | O(n) Toffolis; ≈ 140 T with RTOFs |
| Maslov Props. 4–5 [2016] | ⌈(n − 3)/2⌉ | 8n − 17 = 47 |
| Khattar–Gidney §5.2 (candidate A) | 1 clean | 8k − 12 = 8n − 20 = 44 |
| Khattar–Gidney §5.3 (candidate B) | 2 clean | 8n − 24 = 40 in our instantiation |
| Nie et al. [2024] | 1 | O(log n) depth; not implemented |

**Problem 1.** Both schedules solve Khattar and Gidney's Problem 1 on an array A[0..n]. Index 0 is the clean ancilla and index i is data qubit x<sub>i−1</sub>.
- **Marks.** A *marked* index (A[i] = 1) is available as a target. An *unmarked* index (A[i] = 0) holds a live value in the running product. Initially only index 0 is marked.
- **Operations.** An operation (t, x, y) with t < x < y, t marked and x, y unmarked computes x ∧ y into t, unmarks t and marks x, y:
  - on t = 0, by a temporary-AND, later uncomputed by MBU;
  - on a data qubit, by RTOF(x, y; t) followed by X<sub>t</sub>, which writes ¬(v<sub>t</sub> ⊕ v<sub>x</sub>v<sub>y</sub>).
- **The end.** After the compute phase, the product of the unmarked qubits is x<sub>0</sub> ∧ ⋯ ∧ x<sub>n−1</sub>. A final CZ (or Z) acts on them, and the operations are undone in reverse order.

**Schedule B** has three phases:
1. Khattar and Gidney's doubling timesteps; timestep i applies 2<sup>i</sup> operations of the form (c − 1 − k, c + 2k + 1, c + 2k + 2);
2. their greedy rule;
3. the greedy rule over a second clean ancilla on the qubits left unmarked, a fresh array whose index 0 is the second ancilla.

After k doubling timesteps the marks are exactly [k, k + 2<sup>k</sup>), a closed form proved in Lean. For n = 8:
- the first timestep (0, 1, 2) marks {1, 2};
- the second, (2, 4, 5) then (1, 2, 3), marks {2, 3, 4, 5} = [2, 6);
- two greedy steps follow, then one temporary-AND onto the second ancilla.

That is two ANDs and four RTOF pairs: 2·4 + 4·8 = 40 T. For n ≤ 2 the construction uses no ancilla (a Z or a CZ), and the second phase is skipped when at most two unmarked qubits remain.

<div class="thm">

**Lemma 5.15 (Pair cancellation; `rtofPhase_pair`).** RTOF = D·Toffoli with D = diag(1, 1, 1, 1, 1, −1, −i, i). For the diagonal entries ϕ of D and all bits x, y, z: ϕ(x, y, z ⊕ xy)·ϕ(x, y, z) = 1.

</div>

**Why the phases cancel.** Between a compute RTOF and its uncompute, every gate in a branch acts on basis states as a permutation with a phase. The two RTOFs therefore see the same three bit values, and their phases cancel whatever the target held. Cleanliness is needed only for the classical value of the product.

<div class="thm">

**Lemma 5.16 (`mczFew_kraus_basis`).** Assume every step passes the qubit checks and every AND target is clean when computed. Then every branch maps |x, 0⟩ to (1/√2)<sup>#AND</sup>(−1)<sup>phaseBit(x)</sup>|x, 0⟩, where phaseBit(x) is the product of the unmarked qubits after the compute phase.

</div>

<div class="thm">

**Theorem 5.17 (KG invariant; `KG.inv_step`).** Let F be the product of the initial unmarked values, and Clear(M, v, s) mean that every index below s is marked or holds 1. Every valid operation on an array of length L preserves:
- (a) Clear(M, v, L) ⟺ F;
- (b) every marked t > 0 with v<sub>t</sub> = 0 has an unmarked 0 to its left (it is conditionally clean);
- (c) if index 0 is marked, v<sub>0</sub> = 0.

</div>

<div class="proof">

*Proof idea.*
- **For (a).** If t = 0, or v<sub>t</sub> = 1, the new value of t is v<sub>x</sub>v<sub>y</sub> and the product is unchanged. If t > 0 and v<sub>t</sub> = 0, (b) gives an unmarked i < t < x < y holding 0, untouched by the step, so both sides are 0.
- **For (b) at the new marks x, y.** Only the case v<sub>x</sub>v<sub>y</sub> = 0 matters, in three subcases:
  - t = 0: by (c) and the AND, t now holds 0;
  - t > 0 and v<sub>t</sub> = 1: t now holds ¬(1 ⊕ 0) = 0;
  - t > 0 and v<sub>t</sub> = 0: t now holds 1, and (b) at t before the step gives an untouched unmarked 0 below t.
- **For older marks**, the witness survives or is replaced by t.
- **For (c)**, index 0 is never re-marked.

A simulation lemma (`KG.sim`) transports the index model to qubits.

</div>

<div class="thm">

**Theorem 5.18 (KG Theorem 5.1, every n; `mczFew_logDepth_ok`, `mczFew_logDepth_ancRestore`, `diffusionFew_logDepth_ancRestore`).**
- For every n ≥ 1, `mczFew n .logDepth` succeeds.
- Whenever it returns C, `AncRestore`(C, O<sub>P<sub>all</sub></sub>) holds on two ancillae.
- The corresponding diffusion restores with `diffU` on every larger register.

No well-formedness, bit-count or classical hypothesis remains.

</div>

**Size.** The proof is 1 462 lines, instantiated in tests at n = 12, 64 and 1 000. With `--shape few:log`, `cqr certify` cites it: `grover_certificate_few_all`. Before this theorem, the classical step was checked per instance by evaluating all 2<sup>n</sup> inputs in the kernel. Table 3 compares the two.

<p class="caption"><b>Table 3.</b> Kernel time of a few:log certificate for x<sub>0</sub> ∧ x<sub>3</sub> ∧ x<sub>7</sub> on n inputs, with the per-instance 2<sup>n</sup> check (old) and with Theorem 5.18 (new). <i>Provenance:</i> measured at Stage 13a′, before the front-end block (Stage 16) and the kernel-decided count (Stage 14a) were added. The certificates then carried M as a hypothesis, so these are not final end-to-end times. Six interleaved runs, first excluded. The machine has performance and efficiency cores, hence the min/median spread.</p>

| n | old (min) | new (min) | old (median) | new (median) |
|---|---|---|---|---|
| 8 | 7.19 s | 5.93 s | 21.4 s | 18.5 s |
| 10 | 12.7 s | 9.93 s | 39.4 s | 30.5 s |
| 12 | 50.5 s | 13.4 s | 83.1 s | 43.9 s |

**Against the specification's claim.** Candidate B attains w = 10 and a = 2, with D<sub>8</sub> at (10, 60, 40, 2) and the Grover slice at (10, 172, 96, 2). The claimed 28 T and 16 layers are not reached. The depth claim conflicts with the 11 layers of one temporary-AND compute phase. Candidate A is tested, not certified.

### 5.8 A lower bound within the schedule family

<div class="thm">

**Definition 5.19 (The Problem 1 cost model; `CQRV/Synthesis/Problem1.lean`).**
- **State.** A state records, per index, whether it is available or live, and whether it is fresh (a clean index not yet targeted).
- **Validity.** An operation (t, x, y) is valid if t is available, x and y are live, and the three are distinct. It makes t live, x and y available, and t no longer fresh.
- **Cost.** 4 if the target is fresh (an AND uncomputed by MBU), and 8 otherwise (a pair of RTOFs at 4 T each). The cost model is the assumption of the family, not a bound on all circuits.

</div>

<div class="thm">

**Theorem 5.20 (`problem1_T_lower_bound`).** Every valid schedule from n ≥ 4 live values and two fresh indices down to at most two live values costs at least 8n − 24.

</div>

<div class="proof">

*Proof.* Each step lowers the number of live values by one, so there are at least n − 2 steps. At most two of them target a fresh index. Since cost + 4·#fresh = 8·#steps, the cost is at least 8(n − 2) − 8.

</div>

<div class="thm">

**Theorem 5.21 (`planB_valid`, `planB_cost`, `planB_cost_small`, `planB_tCount`).** Schedule B, translated into the model, is valid for n = 4, …, 12. It costs 8n − 24 for n = 6, …, 12, and 8n − 20 at n = 4, 5, where the second ancilla is unused. The emitted circuit's T-count equals the cost. All of this is decided by the kernel.

</div>

**Scope.** Within this family and cost model, 40 T at n = 8 is optimal, and B attains it. The all-n form of the attainment is open. Candidate A's 8k − 12 = 8n − 20 is the one-ancilla value of the same counting.


## 6 Certified patterns: Grover search and quantum counting

### 6.1 The Grover parametric lemma and the generated certificate

**The search specification** is Search<sub>P</sub> ⊆ Unit × Reg<sub>n</sub>, the set of pairs ((), x) with P(x). The decoding is the basis POVM on the data. GroverChannel<sub>n</sub>(C) prepares |0<sup>n</sup>⟩|0<sup>a</sup>⟩, runs ⟦C⟧ and traces out the ancillae; in Lean it is `groverChannel n C`. `GroverParams` packages n, 1 ≤ M ≤ 2<sup>n</sup> (M is the cardinality of a subset of Reg<sub>n</sub>), an oracle certificate, and θ with sin<sup>2</sup>θ = M/2<sup>n</sup>.

<div class="thm">

**Theorem 6.1 (`grover_parametric_lemma_diff`, `_gen`).** Let:
- the oracle be certified in either uncomputation mode;
- D be a diffusion that respects the bit discipline and satisfies `AncRestore`(D, `diffU`) on every register at least as large as its own;
- C = H<sup>⊗n</sup>·(oracle; D)<sup>r</sup>.

Then for every r:
- GroverChannel<sub>n</sub>(C) satisfies `RealizesExact`(Search<sub>P</sub>, basis, 1 − sin<sup>2</sup>((2r+1)θ), g(C));
- `AncRestore`(C, G<sup>r</sup>H<sup>⊗n</sup>) holds.

</div>

**The proof.** Restoration composes over the concatenation. Realization follows from it by the rotation argument in span{ψ<sub>g</sub>, ψ<sub>b</sub>}. The terminal measurement is the decoding POVM itself, so no composition step is needed.

**What is a parameter.** The budget is the *measured* grade g(C). The iteration count r is a parameter: the tool's floating-point choice of r lies outside the proof.

<div class="thm">

**Theorem 6.2 (`sin_sq_odd_mul`).** For rational s = sin<sup>2</sup>θ, sin<sup>2</sup>((2r+1)θ) is a kernel-evaluable rational function of s and r, computed by the Chebyshev recurrence. For the running example it gives 121/128.

</div>

**The certificate.** `cqr certify` writes `Cert.lean` (Listing 1). The kernel re-runs synthesis on the network literal (`emitted_ok`), computes the grade and `GradeExt`, evaluates δ, counts the solutions, and checks the front end. `cert` is a one-line application of Theorem 6.1. The tool prints *certified* only if the kernel check passes and `#print axioms` lists exactly the three standard axioms.

<div class="listing">

**Listing 1.** A generated certificate (abridged).

<div class="code">def net : Network := ⟨8, #[.input 0, ..., .input 7, .and 0 3, .and 8 7], [9]⟩
def prog : DSL.TypedProgram := ...                         -- the typed term (printed, outside the kernel)
theorem net_ok : toNetwork prog = .ok net := ...           -- the kernel runs the proved front end
theorem front_end : ∀ x, DSL.evalProgram prog x = Network.pred net 8 x := ...
def emitted : Circuit := ⟨8, [...]⟩                         -- 418 IR instructions
theorem emitted_ok : groverCircuit net 8 2 = .ok emitted := ...    -- the kernel re-runs synthesis
theorem grade_eq : Synthesis.grade emitted = ⟨15, 134, 72, 7⟩ := by decide +kernel
theorem hM_count : (Finset.univ.filter fun x => Network.pred net 8 x = true).card = 32 := ...
theorem cert : RealizesExact (SearchSpec (Network.pred net 8)) (basisPOVM 8)
                 (groverChannel 8 emitted) (7 / 128 : ℝ) ⟨15, 134, 72, 7⟩ ∧
               AncRestore 8 7 emitted (groverOp (Network.pred net 8) ^ 2 * hadamardU 8) := ...</div>

</div>

### 6.2 The QFT and its approximation

The IR's exact phase gates express the QFT: H on each qubit, followed by `cp` rotations of decreasing angle. The approximate QFT keeps the rotations with k ≤ kmax.

<div class="thm">

**Theorem 6.3 (`qft_basis`).** The unitary of `qftGates m` maps |x⟩ to the state with amplitude (1/√2)<sup>m</sup>·exp(2πi·x·rev(s)/2<sup>m</sup>) at |s⟩. Here x and s are read with qubit 0 as the most significant bit, and rev is bit reversal.

</div>

<div class="thm">

**Lemma 6.4.**
- ‖U<sub>qft</sub> − U<sub>aqft</sub>‖ ≤ 2πm/2<sup>kmax</sup> (`aqft_opNorm_le`).
- d<sub>⋄</sub>(Ad U, Ad V) ≤ 2‖U − V‖ (`diamondDist_ofUnitary_le`).
- The channel of a measurement-free circuit is the unitary channel of its matrix (`channelDenote_of_unitary`).

</div>

<div class="thm">

**Theorem 6.5 (`aqft_diamond_le`).** d<sub>⋄</sub>(⟦qft<sub>m</sub>⟧, ⟦aqft<sub>m,kmax</sub>⟧) ≤ 4πm/2<sup>kmax</sup>, and likewise for the inverses.

</div>

### 6.3 Quantum counting

**The register layout.** The counting circuit has n search qubits, followed by m phase qubits, then ancillae. Its unitary is stated on the factor order *phase ⊗ search*, through explicit embeddings (`liftS`, `liftP`). Phase qubit k controls G<sup>2<sup>k</sup></sup>, so the inverse QFT undoes the bit reversal of Theorem 6.3, and the phase outcome y is read most significant bit first with no `bitRev` in the decoding.

**The controlled iterate.** The controlled oracle is the phase oracle of `withControl N c`, the network whose output is (input c) ∧ (out N), so Theorem 5.6 applies unchanged. The controlled diffusion conjugates a controlled MCZ by uncontrolled data layers. A Z on the control corrects the diffusion's global sign, which matters only under control.

**The circuit.** `countingCircuit` is three parts: H on all n + m qubits; 2<sup>k</sup> controlled iterates on each control k; the inverse (approximate) QFT.

<div class="thm">

**Theorem 6.6 (`countingCircuit_ancRestore`).** For a well-formed one-output N, the counting circuit is well formed and restores its ancillae, applying

<div class="eq">U<sub>count</sub> = (QFT<sub>m</sub><sup>†</sup> ⊗ I)·(Σ<sub>k=0</sub><sup>2<sup>m</sup>−1</sup> |k⟩⟨k| ⊗ G<sup>k</sup>)·H<sup>⊗(n+m)</sup>.</div>

</div>

<div class="thm">

**Theorem 6.7 (QPE for the Grover iterate; `phaseDist_eq`, `qpe_success`).** For Grover data (1 ≤ M ≤ 2<sup>n</sup>, a = M/2<sup>n</sup>) and m ≥ 1, the phase distribution phaseDist of U<sub>count</sub>|0⟩ satisfies

<div class="eq">Σ<sub>y : |sin<sup>2</sup>(πy/2<sup>m</sup>) − a| ≤ ε(a,m)</sub> phaseDist(y) ≥ 8/π<sup>2</sup>,  ε(a, m) = 2π√(a(1−a))/2<sup>m</sup> + π<sup>2</sup>/4<sup>m</sup>.</div>

</div>

**Proof idea.** The distribution is the equal mixture of the two single-phase distributions at ±θ/π. This is shown with exponentials, not eigenvectors, so the case M = 2<sup>n</sup> needs no separate treatment. Each single-phase distribution puts mass at least 8/π<sup>2</sup> on the two nearest grid points (`two_point_bound`). A grid point within 2<sup>−m</sup> decodes within ε (`sin_sq_sub_le`). Both phases decode to the same estimate.

**The output type.** A POVM needs a finite outcome type, while a is not in general an outcome. We use CountOut<sub>m</sub> = Reg<sub>m</sub> ⊕ Unit:
- an outcome inl y has the estimate ã(y) = sin<sup>2</sup>(πy/2<sup>m</sup>), a real number;
- the outcome inr () has the estimate a;
- the type carries the pseudo-metric induced by ã.

**The specification.** CountSpec<sub>m,a</sub> accepts only inr (), and its ε-relaxation is {y : |ã(y) − a| ≤ ε}. The decoding `countPOVM n m` is a POVM on the whole (n + m)-qubit data space: the basis measurement of the phase qubits tensored with the identity on the search qubits, with the zero operator on inr ().

<div class="thm">

**Theorem 6.8 (Amplitude-estimation lemma; `ae_parametric_lemma`).** Assume:
- gp is Grover data with 1 ≤ M, and m ≥ 1;
- N is a well-formed one-output network computing gp's predicate on n inputs;
- `countingCircuit N n m none shape mode = .ok C` (either shape, either mode);
- g(C) ≤ g.

Then GroverChannel<sub>n+m</sub>(C) satisfies `Realizes`(CountSpec<sub>m,a</sub>, `countPOVM`, ε(a, m), 1 − 8/π<sup>2</sup>, g), and `AncRestore`(C, U<sub>count</sub>). The AQFT form adds η<sub>aqft</sub>/2 to δ by Theorem 3.8 and Theorem 6.5.

</div>

**Parametric theorem and generated certificate.** Theorem 6.8 is the *parametric* result, uniform over networks and their counts. The generated certificate `grover_pred_037_count` (n = 8, m = 4, exact inverse QFT, MBU) concerns *one* network. Its statement "for every M equal to the network's count" is a formulation device, equivalent to its instance at M = 32 (`cert_count`: ε ≈ 0.168426, δ ≈ 0.189431). It adds no coverage. The case M = 0 is excluded (planned: R8). With no solution, G fixes |s⟩, the phase outcome is 0, and the estimate a = 0 is exact.

**The specification departure.** The specification asked for amplitude *amplification* as its second pattern. We implemented estimation instead, because it exercises the coherent composition theorem with a real η, needs ε > 0 and δ > 0, and produces the count that search assumes. Estimation does not discharge the amplification pattern, which remains unimplemented.

### 6.4 Grade composition and the compositional certificate

The counting circuit of the running example has 3 682 gates (MBU), above the flat form's ceiling.

**The ceiling.** The ceiling was measured at Stages 14b and 18a. The flat form is memory-bound at about 750 instructions on 16 GB: 6.9 GB at 706 instructions, above 8 GB at 838. An earlier failure was traced to `grade_eq`, whose scheduler state was built by `Array.push`; a cons-list state removed it with every value unchanged.

<div class="thm">

**Theorem 6.9 (`grade_append_le`, list and n-fold forms).** If C<sub>1</sub> and C<sub>2</sub> share the data register and C<sub>1</sub> frees every ancilla it allocates (`liveEnd C₁ = 0`), then g(C<sub>1</sub> ++ C<sub>2</sub>) ≤ g(C<sub>1</sub>) ⊕ g(C<sub>2</sub>). Width, T-count and peak ancillae hold with equality, and depth is a bound because the scheduler overlaps the boundary. The analogue holds for `GradeExt`.

</div>

**The block form.** The certificate measures each named block in the kernel and links the whole circuit to the blocks (`countingCircuit_of_blocks`). It bounds the grade by Theorem 6.9. A block boundary requires `liveEnd = 0`, so this form cannot cut inside a single oracle cone whose ancillae stay live, which is a limitation for very large single oracles.

**Per-block accounting.** Table 4 resolves the T and rotation accounting.

<p class="caption"><b>Table 4.</b> Per-block accounting of the counting certificate (n = 8, m = 4, MBU). Grades are those the kernel measured per block (<code>*_grade_eq</code>, <code>*_gradeExt_eq</code>). Totals are composed by Theorem 6.9: width and ancillae by max, the rest by sums (depth 1 + 15·92 + 7 = 1 388).</p>

| Block | Gates | Copies | Grade (w, d, t, a) | GradeExt (2Q, T-depth, rot, meas, ff) |
|---|---|---|---|---|
| H layer | 12 | 1 | (12, 1, 0, 0) | (0, 0, 0, 0, 0) |
| controlled iterate cg<sub>k</sub>, k = 0…3 | 244 | 1, 2, 4, 8 (15 in all) | (20, 92, 44, 8) each | (77, 24, 0, 11, 22) each |
| inverse QFT<sub>4</sub> | 10 | 1 | (12, 7, 0, 0) | (6, 0, 6, 0, 0) |
| **composed** | **3 682** | | **(20, 1388, 660, 8)** | **(1161, ≤ 660, 6, 165, 330)** |

**Reading the table.** The T-count 660 = 15 × 44 comes from the controlled iterates. The inverse QFT contributes no T and six *rotations*: its six controlled phases (angles π/2, π/4, π/8) are neither Clifford nor T-powers under the rules of Section 4.5. Their Clifford+T cost is not in t. The T-depth is stated only as a bound.

### 6.5 The library: uniform soundness, signature-match completeness, selection

**The library.** The pattern definition of the specification (a QPLP) is a Lean record: a precondition, a parameter type, a builder, a specification and decoding, and a soundness proof. The two entries `groverSem` and `countSem` instantiate it.

<div class="thm">

**Theorem 6.10 (`QPLP.Sem.realizes_of_le`).** For every entry e, every parameter p satisfying e's precondition, and every circuit C with `e.builder p = .ok C`: C realizes `e.spec p` within every budget g ≥ g(C), and restores its ancillae.

</div>

<div class="thm">

**Theorem 6.11 (Signature-match completeness; `millerMatch_complete`, `matchers_agree`, `matchLibrary_spec`).** Let φ be a Miller pattern of uniform arity, t a ground signature term, and σ a well-formed substitution with φσ = t. Then:
- `millerMatch φ t` succeeds, with a result extending σ;
- any two well-formed matchers agree on φ's metavariables;
- `matchLibrary` returns `matched e σ` exactly when t matches entry e, and otherwise no entry matches.

</div>

**Scope.**
- *Uniform arity is necessary.* There is a counterexample with one metavariable used at two arities, kept as a test.
- *The cost bound* of the specification's Proposition 5.1 is not formalized.
- *Completeness is about signatures*, not about programs (Section 4.3).

**Certified selection.** Selection chooses among the three search candidates at the request's r: tree/MBU, tree/coherent and few:log/MBU.

<div class="thm">

**Theorem 6.12 (`select_spec`).** The selected candidate fits the budget and has no admissible competitor with a lexicographically smaller key, where the key puts the preferred component first. `none` holds iff nothing fits.

</div>

**The selection certificate.** It states its claim about the *builders' outputs*. In it, the kernel computes each candidate's grade. With `--budget 12,200,100,8 --prefer depth` it selects few:log/MBU at (10, 172, 96, 2). On (w, d, t, a) the coherent candidate is dominated, so its advantage (no measurement and no feed-forward) appears only in `GradeExt`, and becomes decisive on hardware without feed-forward (Section 7.8).

### 6.6 A logical measured-composition bound: counting, then search

**The pipeline.** Counting estimates M. A measure-and-prepare channel, built from its Choi matrix because Physlib has none, maps the outcome y to the Grover circuit C(y) for the iteration count r(y) computed from ã(y). The pipeline assumes M ≥ 1.

<div class="thm">

**Theorem 6.13 (`search_unknown_M`, `search_unknown_M_8_32_5`).** Assume:
- C(y) = C<sub>0</sub> for every outcome whose estimate is within the counting ε;
- g<sub>2</sub> bounds the grade of every C(y).

Then the measured composite realizes "search after count" with ε = ε<sub>count</sub> and δ = δ<sub>count</sub> + δ<sub>search</sub>, within g(C<sub>1</sub>) ⊕ g<sub>2</sub>.

</div>

**Why m = 5.** The hypothesis C(y) = C<sub>0</sub> requires every outcome in the counting ε-ball to choose the same iteration count. For (n, M) = (8, 32) at m = 4, ε(1/8, 4) ≈ 0.168 exceeds a. The ball then contains y = 0 and y = 1 with r = 12 and r = 3, so the composite δ ≈ 1.04 is vacuous. At m = 5, ε ≈ 0.0746, the ball is y ∈ {3, 4, 28, 29}, all with r = 2. This is the decided lemma `domain_8_32_5`, which gives δ = (1 − 8/π<sup>2</sup>) + 7/128 ≈ 0.244.

**The grades.**
- **First stage.** g<sub>1</sub> = (21, 2862, 1364, 8), a composed bound.
- **Second stage.** g<sub>2</sub> must bound *every* branch: the largest r = 12 at y = 0 gives (15, 794, 432, 7).
- **The composite.** g<sub>1</sub> ⊕ g<sub>2</sub> = (21, 3656, 1796, 8).

**A logical bound.** The result does not count the measurement, the classical computation of r(y), the selection, the re-preparation or the latency (Section 3.3). No composite certificate is generated.


## 7 Validating routed circuits

A device offers a basis gate set, a sparse coupling map and calibration data. This section carries the logical certificate to a routed circuit without trusting the transpiler. Untrusted tools do the work and record a witness, and Lean checks the witness. The tools are Qiskit 2.6.2, Qiskit Aer 0.18.2 and the fake backends of qiskit-ibm-runtime 0.52.1, in a separate pinned environment. Everything not checked is a named premise (Table 1).

### 7.1 Targets

**The target file.** A target is exported once from a fake backend to a JSON file that Lean reads (`HardwareTarget`). It records the basis, the directed coupling map, three capability flags (mid-circuit measurement, feed-forward, reset), a calibration snapshot and durations. The snapshot is bound by a SHA3-256 hash over a canonical JSON form that Lean and Python reproduce byte for byte. To make that possible, every calibration number is stored as a decimal string.

**The two targets.**
- **FakeTorino:** 133 qubits, basis {cz, rz, sx, x}, feed-forward available.
- **FakeWashington:** 127 qubits, basis {cx, rz, sx, x}, no feed-forward.

Their snapshots are those shipped with the fake backends, recorded from real devices on past dates.

### 7.2 Translation is sound

**The embedding.** The basis gates are IR gates up to a global phase:
- sx = H S H exactly;
- rz(θ) = e<sup>−iθ/2</sup>p(θ);
- x, cz and cx = CNOT are IR gates.

A global phase multiplies each branch's Kraus operator by a unit scalar (inside a conditioned gate, only on the branches where the bit is 1) and leaves the channel unchanged.

<div class="thm">

**Theorem 7.1 (`decomp_sound`).** For every table entry g, the *IR expansion* of its basis sequence (with rz read as p) has unitary e<sup>2πi·irPhase(g)</sup>·gateU(g). Here irPhase(g) is the table's phase plus a/2<sup>k+1</sup> for each rz(2πa/2<sup>k</sup>) in the sequence.

</div>

**An example.** H's table entry is rz(π/2) sx rz(π/2), whose physical matrix product is e<sup>−iπ/4</sup>H: a table phase of −1/8 of a turn. The IR expansion is S(HSH)S = e<sup>iπ/4</sup>H, and irPhase(H) = −1/8 + 2·1/8 = +1/8. The task text had stated the theorem with the table phase, which is false for H. The proof found the corrected form.

<div class="thm">

**Theorem 7.2 (`translate_sound`, `translate_wf`).** The table translation of a well-formed circuit is well formed and has the same channel. Realization and restoration transfer to it.

</div>

**The ancilla count.** "Translation preserves the ancilla count" is false in general: ⟨1, [alloc (anc 3)]⟩ loses its only ancilla. The proved form assumes `ancCovered`, a decidable property that holds for every synthesized circuit.

### 7.3 Relabeling, SWAPs, embedding, reordering

<div class="thm">

**Theorem 7.3 (`channelDenote_relabel`, `ud_swapEntry`, `channelDenote_embed`).**
- Relabeling the data qubits by a permutation σ conjugates the channel by the permutation matrix P<sub>σ</sub>.
- The table's SWAP, three CNOTs, is a unit scalar times P<sub>(p q)</sub>.
- Placing a circuit on n + a + b physical qubits with layout σ, with the idle qubits in |0⟩, maps the embedded input to the embedded output: ⟦physOf<sub>b,σ</sub>(C)⟧(embed<sub>b,σ</sub>ρ) = embed<sub>b,σ</sub>(⟦C⟧ρ).

</div>

<div class="thm">

**Theorem 7.4 (`gateK_comm_of_disjoint`, `krausOps_reorder`).**
- In every branch, gates on disjoint qubits and disjoint classical bits commute.
- A permutation of the gate list that keeps the relative order of the gates on every qubit and every bit (the dependency-queue condition `validReorder`) preserves the Kraus operator of every branch.

Two reads of one bit are treated as dependent, which is stricter than needed.

</div>

### 7.4 The witness and its soundness

**What the witness records.** Qiskit's SabreLayout is the only routing pass. A recording pass writes a witness containing:
- the initial layout;
- the order in which the dependency-queue matcher consumed the logical elements (gates, or blocks under one condition);
- the SWAPs;
- the final layout;
- a classical-bit map.

The circuit is compacted to its used qubits.

**The reconstruction.** `applyWitness b C w N` (Physlib-free) rebuilds the physical gate list from the logical circuit and the witness. It checks that:
- the layouts are in range and injective;
- each consumed element heads its dependency queues;
- the final layout matches;
- a block's SWAPs compose to the identity on the whole register.

**The classical-bit map.** The reconstruction keeps the logical bit numbering. `applyWitness` and `applyWitnessQ` therefore check explicitly that the witness's bit map is the identity [0, …, k − 1] and covers every bit of the circuit, and refuse any other map with a named error. The soundness theorems are unchanged. All fifteen committed witnesses pass the check.

<div class="thm">

**Theorem 7.5 (`applyWitness_sound`).** Assume:
- C is well formed;
- `applyWitness b C w N = .ok G` with N = n + (a + b), where b is the number of idle physical qubits (`bb` in Lean);
- the physical circuit of G is well formed with C's bit count;
- σ<sub>0</sub> realizes the initial layout.

Then the final layout is realized by σ<sub>f</sub> = irPerm(steps)·σ<sub>0</sub>, and for every ρ,

<div class="eq">⟦physCircuit<sub>N</sub>(G)⟧(embed<sub>b,σ<sub>0</sub></sub>ρ) = embed<sub>b,σ<sub>f</sub></sub>(⟦C⟧ρ).</div>

</div>

**The proof** (97 lines; the file is 1 266 lines) has four steps:
1. migrate every SWAP to the end, at top level and inside blocks; inside a block the condition bit is handled once;
2. undo the reordering by Theorem 7.4, the independence being preserved by injectivity;
3. identify the placement (Theorem 7.3) and the translation (Theorem 7.2);
4. cancel the unit scalars.

**Two checks found by the proof.** The proof required two checks that the task specification lacked:
- an *injective* initial layout: with [0, 0], two logical qubits would share a physical qubit;
- SWAPs that compose to the identity on the *whole* register: (0 1)(1 2)(2 0) restores a one-qubit layout yet exchanges two idle qubits.

<div class="thm">

**Corollary 7.6 (`AncRestore.phys`, `realizes_phys`, `realizesExact_phys`).** Restoration and realization transfer to the physical channel, which prepares the embedded |0⟩, runs the physical circuit, and un-embeds. The physical channel has the same ε and δ, at the physical circuit's own grade.

</div>

### 7.5 A linear-design kernel check

**The problem.** As written, `applyWitness` is quadratic for the kernel. On the routed running example (1 253 entries, 2 541 gates) it had not finished after 15 minutes and 8 GB.

**The linear form.** `applyWitnessQ` keeps one dependency queue per wire and takes an element when it heads all its queues. It never indexes a list by element position, a *design* that is linear in the number of elements. Its running time is measured, not proved. A first version indexed the translated gate list per element, and the kernel's cache made it quadratic in memory (8.9 GB). A lockstep pass over elements and gates brought it to 4.1 GB.

<div class="thm">

**Theorem 7.7 (`applyWitnessQ_ok`, `applyWitnessQ_sound`).** For a well-formed C, `applyWitnessQ` = `.ok G` implies `applyWitness` = `.ok G`. `applyWitnessQ_sound` restates Theorem 7.5 with σ<sub>f</sub> a closed term the kernel evaluates.

</div>

**Check files.** For each committed artifact, `cqr hw check` re-checks three hashes (the logical circuit's, against both the manifest and the literal's own hash; the witness's; the target snapshot's). It writes a check file containing:
- `recon` (by `rfl`);
- `edges_ok`: every two-qubit gate lies on a coupling edge;
- the channel transfer `phys_channel`;
- `phys_zero`: from the all-|0⟩ physical state;
- two tampering tests.

The literal-hash check caught a generator bug that dropped the conditions of conditioned gates. Fifteen check files run in CI (Table 5).

<p class="caption"><b>Table 5.</b> Check files: wall time of <code>lean</code>, run directly with the <code>LEAN_PATH</code> of <code>lake env</code> (about 9 s of it is loading), and peak memory; median of 3 runs at commit <code>2025ed2</code> (R11). Standard axioms only.</p>

| Artifact | Target | Physical gates | Time | Peak |
|---|---|---|---|---|
| MBU gadget / wrapped gadget | FakeTorino | 102 / 142 | 9.5 / 9.8 s | 1.8 / 1.9 GB |
| hw_n2 / hw_n3 (tree, MBU) | FakeTorino | 226 / 848 | 10 / 14 s | 1.9 / 2.3 GB |
| grover_pred_037, tree, MBU (the physical certificate's instance) | FakeTorino | 2 541 | 29 s | 4.0 GB |
| grover_pred_037, tree, coherent | FakeTorino / FakeWashington | 3 177 / 879 | 30 / 18 s | 4.1 / 2.7 GB |
| grover_pred_037, few:log, MBU | FakeTorino | 2 232 | 21 s | 3.1 GB |
| simple_alu_x0_1, tree, MBU | FakeTorino | 3 528 | 30 s | 4.0 GB |
| simple_alu_x0_1, tree, coherent (the largest check) | FakeTorino / FakeWashington | 4 170 / 933 | 29 / 17 s | 3.9 / 2.6 GB |
| simple_alu_x0_1, few:log, MBU | FakeTorino | 3 290 | 27 s | 3.7 GB |
| three bound-vacuity-frontier instances (Section 8.5) | both | 92–909 | 9.5–14 s | 1.9–2.4 GB |

**Scope of the checker.** It is independent of the routing *heuristics*, such as SABRE's choices and seeds. It is not independent of the *kind* of transformation. It supports fixed table translation, dependency-respecting reordering, layouts, SWAP insertion and conditioned blocks. A pass that cancels or rewrites gates, inserts resets, or uses non-SWAP permutations would need a richer witness and new soundness proofs.

### 7.6 The physical certificate

`cqr hw certify` writes a self-contained physical certificate. It holds:
- the logical certificate's declarations;
- the artifact's check body;
- `emitted_eq : emitted = C`, decided by the kernel with no axioms;
- `phys_realizes`.

<div class="thm">

**Theorem 7.8 (`phys_realizes`, at the instance).** There is σ<sub>f</sub> such that the physical Grover channel of the routed 2 541-gate circuit on FakeTorino satisfies `RealizesExact` for the search specification of x<sub>0</sub> ∧ x<sub>3</sub> ∧ x<sub>7</sub> with δ = 7/128, at the physical circuit's grade. The channel prepares all-|0⟩ on the used qubits, runs the circuit, and un-embeds.

</div>

**Status and cost.** The certificate checks in 53 s at 4.1 GB (median of 3, commit `2025ed2`). Its status words are `logical_certified`, `hardware_compatible` and `physical_translation_validated`. The printed `physical.qasm` is produced by an unverified printer from the validated gate list and re-parsed against the artifact.

### 7.7 The physical grade

<div class="thm">

**Definition 7.9 (`PhysGrade`).** From the gate list, the target and a feed-forward latency L, the physical grade records:
- the used qubits;
- the two-qubit gates;
- the mid-circuit measurements;
- the feed-forward gates;
- the wall-clock depth of an as-soon-as-possible schedule in which a conditioned gate also waits for its measurement's end plus L;
- the physical bound of Section 8.4.

</div>

**Durations.** They are the exact rationals of the decimals in the target file. A rule "convert to an integer unit or stop" would have stopped on both targets: FakeWashington uses dt = 2/9 ns, and FakeTorino lists 119.99999999999999 ns. L is a stated assumption, since the fakes give none. Lean and a Python mirror agree exactly on all artifacts.

**The running example on FakeTorino:** 16 qubits, 315 two-qubit gates, 18 measurements, 624 conditioned basis gates, and a depth of about 33.7 µs at L = 0 and 43.7 µs at L = 1 µs.

### 7.8 Selection by a physical component

**The selector.** `selectKey` chooses among a request's artifacts on a target:
- *admissibility:* an MBU candidate needs feed-forward, and an optional budget on the key must hold;
- *the key:* two-qubit count, depth, physical bound, or noise bound.

`selectKey_spec` proves the choice admissible and minimal.

**The four committed selection files.**
- **FakeWashington.** Only the coherent mode is admissible.
- **FakeTorino.** The physical bound and the two-qubit count select few:log/MBU (262 two-qubit gates against 315 and 375). The depth selects tree/coherent (20.1 µs against 33.7 µs). With the budget "bound < 1", nothing is admissible.

**A difference, reported.** The committed physical certificate is of the tree/MBU artifact, generated with an explicit mode.


## 8 Conditional noise bounds

**The approach.** A device does not run the ideal channel. We do not claim that a device behaves as its calibration says. We prove a perturbation theorem, state the bridge from calibration numbers to channels as named premises, and evaluate the resulting bound exactly. The result is a **conditional perturbation theorem parameterized by calibration-derived numbers**, not a calibrated guarantee about a device.

### 8.1 A step semantics with the classical register

`channelDenote` sums over branches of classical bits, so a circuit's channel is not a composition of per-gate channels on the quantum register: a measurement and the gates that read its bit are linked through the bits. We extend the register to X<sup>+</sup> = (Reg<sub>n</sub> × Reg<sub>a</sub>) × Reg<sub>m</sub>, with the bits as dephased qubits, and give each gate a channel:
- unitary gates act as gateU(g) ⊗ I;
- `measure q -> j` has the Kraus operators P<sub>q=v</sub> ⊗ X<sub>j</sub><sup>v</sup> (v ∈ {0, 1});
- `ifBit j g` is gateU(g) ⊗ |1⟩⟨1|<sub>j</sub> + I ⊗ |0⟩⟨0|<sub>j</sub>, in the factor order of X<sup>+</sup>.

<div class="thm">

**Theorem 8.1 (`channelDenote_eq_steps`).** For a well-formed C, ⟦C⟧(ρ) = tr<sub>bits</sub>((stepChan g<sub>k</sub> ∘ ⋯ ∘ stepChan g<sub>1</sub>)(ρ ⊗ |0⋯0⟩⟨0⋯0|)).

</div>

**Proof idea.** The invariant is Σ<sub>d : supp d ⊆ W</sub> K<sub>d</sub>ρK<sub>d</sub><sup>†</sup> ⊗ |d⟩⟨d|, where W is the set of bits written so far. The final trace needs that every bit is written under the bit discipline.

**Where measurements sit.** The *mid-circuit* measurements are steps of this list. The *terminal* readout of the data qubits is not: it is the decoding POVM, applied after un-embedding.

### 8.2 Perturbation and the stochastic premise

<div class="thm">

**Theorem 8.2 (`diamondDist_steps_le`).** For lists of channels on one space with d<sub>⋄</sub>(Ψ<sub>i</sub>, Φ<sub>i</sub>) ≤ η<sub>i</sub>, the composites are within Σ η<sub>i</sub>. The proof uses Lemma 3.6, both directions.

</div>

<div class="thm">

**Lemma 8.3 (`diamondDist_mix_le`).** For p ∈ [0, 1] and any channel Φ′ on the same spaces, d<sub>⋄</sub>((1 − p)Φ + pΦ′, Φ) ≤ 2p. The mixture is Physlib's convex combination of channels.

</div>

**What the premise avoids.** Φ′ is arbitrary *on the whole register*, crosstalk and correlated errors included, so no stability of the diamond norm under tensoring is needed. Locality is replaced by a stronger premise, not proved.

<div class="thm">

**Theorem 8.4 (`noisy_realization`).** If the ideal composite Γ ∘ tr<sub>bits</sub> ∘ (Φ<sub>k</sub> ∘ ⋯ ∘ Φ<sub>1</sub>) ∘ prep realizes S with (ε, δ), and each noisy step satisfies d<sub>⋄</sub>(Ψ<sub>i</sub>, Φ<sub>i</sub>) ≤ η<sub>i</sub>, then the noisy composite realizes S with (ε, δ + ½Σ η<sub>i</sub>).

</div>

<div class="thm">

**Theorem 8.5 (`phys_noisy_stochastic`).** Assume:
- each *basis operation* g of the routed circuit, including each mid-circuit measurement, is (1 − p<sub>g</sub>) times its ideal channel plus p<sub>g</sub> times an arbitrary channel;
- each terminal data readout is modelled by an identity step with error r<sub>j</sub> appended before the decoding.

Then for *every* choice of the arbitrary channels, the noisy physical channel satisfies `RealizesExact` with δ′ = δ + Σ<sub>g</sub> p<sub>g</sub> + Σ<sub>j</sub> r<sub>j</sub>.

</div>

**Basis operations, not IR gates.** The premise attaches to a basis operation's composite, not to each IR gate, because sx expands to three IR steps (`steps_flatMap`, `stepsOf_physCircuit`).

### 8.3 The premises

A conditional certificate rests on the model premises of Table 1, (P-prep) and (P-ctrl), and on four noise premises. Every manifest names all six, each with its sentence:
- **(P-cal)** The calibration snapshot of the target file, by hash. It is shipped with qiskit-ibm-runtime and recorded from a real device on a past date. It is not a live calibration.
- **(P-stoch)** Each basis operation on k qubits is stochastic with p = min(1, (d+1)/d·r), d = 2<sup>k</sup>, where r is its calibrated error. This is the *Pauli reading* of a randomized-benchmarking infidelity: factor 3/2 for one qubit, 5/4 for two, and 0 for virtual rz.
- **(P-ro)** Each readout, mid-circuit or terminal, is ideal with probability at least 1 − r<sub>j</sub>, with r<sub>j</sub> the calibrated readout error of its qubit.
- **(P-idle)** Idle qubits do not err.

**How strong (P-stoch) is.** Calibration numbers do not imply it:
- *Coherent errors.* For a coherent error of infidelity r, the diamond distance can be of order √r rather than r.
- *Amplitude damping* is not a mixture with the identity.
- *(P-idle)* ignores decoherence during the long measurements and feed-forward waits (Section 8.5).

The bound is therefore **optimistic** for untwirled hardware. Randomized compiling [Wallman and Emerson 2016] is the known way to bring real noise closer to the stochastic form, and it is not in the certified path.

### 8.4 The bound and the conditional certificates

**The bound.** `noiseBound` = δ + Σ<sub>g</sub> p<sub>g</sub> + Σ<sub>j</sub> r<sub>j</sub>, computed exactly in ℚ and equal to a Python mirror on all artifacts. It is decided by the kernel in each certificate (`phys_noisy_inst`). The earlier figure δ + Σ r is the reading p = r, which is 17–25 % lower.

<p class="caption"><b>Table 6.</b> Conditional certificates. The classical baseline is the success probability (q + 1)/N of the best q-query classical search for M = 1, with q = r oracle queries. Status words: L logical_certified, H hardware_compatible, P physical_translation_validated, N noise_conditional, S emulator_sanity_checked.</p>

| Certificate | Instance (target) | Ideal success | Certified 1 − δ′ | Classical (q+1)/N | Beats baseline? | Status |
|---|---|---|---|---|---|---|
| hw_n2_torino | n = 2, r = 1, tree/MBU (FakeTorino) | 1 | 0.821 | 0.500 | yes | L H P N S |
| fr_n2_tree_coherent_rb_washington | n = 2, r = 1, tree/coherent, pruned (FakeWashington) | 1 | 0.789 | 0.500 | yes | L H P N |
| fr_n3_tree_coherent_rb_torino | n = 3, r = 2, tree/coherent, pruned (FakeTorino) | 121/128 | 0.404 | 0.375 | barely | L H P N |
| hw_n3_torino | n = 3, r = 2, tree/MBU (FakeTorino) | 121/128 | 0.248 | 0.375 | **no** | L H P N S |
| fr_n3_fewlog_mbu_torino | n = 3, r = 2, few:log/MBU (FakeTorino) | 121/128 | 0.222 | 0.375 | **no** | L H P N |
| mbu_gadget_torino | the MBU gadget, channel form: trace distance ≤ 0.0995 | — | — | — | — | H P N |

**The emulator protocol.** Runs on Aer with the fake's own noise model used 4 000 shots and seed 25. Each was compared with the one-sided Hoeffding criterion p̂ ≥ 1 − δ′ − √(ln(1/α)/(2·shots)), with α = 0.05 (margin ≈ 0.0194):

| Run | p̂ | Threshold |
|---|---|---|
| hw_n2 | 3527/4000 = 0.882 | 0.801 |
| hw_n3 | 2361/4000 = 0.590 | 0.229 |
| wrapped MBU gadget | 0.900 | 0.857 |

The emulator's noise model is not of the (P-stoch) form, so these are *sanity checks* of the pipeline, not evidence for the premise, and the status word says so. Each manifest records the protocol: α, shots, seed, the success count, the margin formula and its value.

### 8.5 The bound-vacuity frontier

**The family.** Grover on x<sub>0</sub> ∧ ⋯ ∧ x<sub>n−1</sub> with M = 1, for n = 2…7, at the tool's iteration counts (r = 1, 2, 3, 4, 6, 8), in the three modes on FakeTorino and the coherent mode on FakeWashington. Two routings were used:
- (a) the full coupling map;
- (b) the coupling map without edges of calibrated error ≥ 1/2. Its edges are edges of the target, so `edges_ok` is unchanged.

<p class="caption"><b>Table 7.</b> The bound-vacuity frontier: within the tested family and routings, on the two shipped snapshots, the largest n with δ′ &lt; 1 (<code>docs/hw_frontier/FRONTIER.md</code>; 30 rows, Stage 27c).</p>

| Target | Mode | (a) full map | (b) pruned map |
|---|---|---|---|
| FakeTorino | tree / MBU | n = 3, δ′ = 0.7521 | n = 3, 0.9590 |
| FakeTorino | tree / coherent | n = 3, 0.7415 | n = 3, 0.5962 |
| FakeTorino | few:log / MBU | n = 3, 0.7776 | n = 3, 0.8345 |
| FakeWashington | tree / coherent | n = 2, 0.2278 | n = 2, 0.2110 |

**Scope of the frontier.** It is not a frontier of device feasibility. Shallower circuits, other predicates, fewer iterations or better calibrations could differ. Every tested FakeTorino series is vacuous from n = 4, and FakeWashington from n = 3. The running example's conditional bound is 2.90.

**The idle diagnostic.** For each used qubit it computes idle time over T2 on the ASAP schedule. It is 0.05–0.38 at the frontier and above 1 at n = 5: there, a qubit idles longer than a coherence time while (P-idle) assumes it keeps its state.

**The honest reading.** On these snapshots the conditional guarantee is meaningful only for two- and three-qubit instances. Even there it beats a classical baseline only in three of five cases (Table 6).


## 9 Evaluation

**Provenance.** All numbers are produced by the repository's tools on one workstation: Intel Core i9-13900H (20 logical CPUs, performance and efficiency cores), 16 GB RAM, Windows 11, `LEAN_NUM_THREADS=4`, Lean 4.35.0 with the pinned Mathlib and Physlib. Every kernel time, wall time and peak memory in Tables 5 and 8 and in Section 9.2 comes from **one run at one commit**, `2025ed2` (revision R11; `docs/BENCHMARKS.md`). The run covered all 40 committed Lean check files, one Lean process at a time. Before each file it recorded the free memory and a load sample: the CPU was at most 7.4 % busy and no other Lean process ran. Logical certificates are the median of 5 runs after one warm-up; the other files the median of 3. The runs of each file agree within 9 % (within 6 % for every file above 1 s). Earlier stages had seen kernel times vary by up to a factor of three on a loaded machine. Table 3, the flat-form ceiling (Section 6.3) and the CI durations are separate experiments and name their stage.

### 9.1 Logical certificates

<p class="caption"><b>Table 8.</b> Committed logical certificates. All are certified with the standard axioms; the count is kernel-decided (n ≤ 10). <i>Kernel</i> is the <code>kernel_check</code> field of each <code>certificate.json</code>: the profiler's type-checking time, median of 5 runs after one warm-up, with the front-end block, <code>GradeExt</code> and the count check enabled. <i>Peak</i> is the Lean process's peak working set. All measured at commit <code>2025ed2</code> (R11).</p>

| Certificate | Instance | Grade (w, d, t, a) | GradeExt (2Q, T-depth, rot, meas, ff) | ε; δ | Kernel; peak |
|---|---|---|---|---|---|
| grover_pred_037 | Grover, n = 8, M = 32, r = 2; tree, MBU | (15, 134, 72, 7) measured | (126, 39, 0, 18, 36) | 0; 7/128 | 12.0 s; 3.7 GB |
| grover_pred_037_coh | tree, coherent | (15, 200, 144, 7) measured | (216, 74, 0, 0, 0) | 0; 7/128 | 21.0 s; 5.4 GB |
| grover_pred_037_few | few:log, MBU | (10, 172, 96, 2) measured | (106, 77, 0, 8, 16) | 0; 7/128 | 10.3 s; 3.5 GB |
| grover_pred_037_sel | selection → few:log | (10, 172, 96, 2) measured | as above | 0; 7/128 | 23.2 s; 4.8 GB |
| grover_pred_037_count | Count, n = 8, m = 4 | (20, 1388, 660, 8) **bound** | (1161, ≤ 660, 6, 165, 330) | 0.168426; 0.189431 | 16.9 s; 2.6 GB |
| simple_alu_x0_1 | RevLib ALU bit, n = 6, M = 30, r = 1 | (16, 121, 60, 10) measured | (137, 28, 0, 15, 30) | 0; 833/2048 | 12.1 s; 3.4 GB |
| addchk3 | x + y ≡ z (mod 8), 3-bit; n = 9, M = 64, r = 2 | (17, 226, 104, 8) measured | (262, 55, 0, 26, 52) | 0; 7/128 | 44.8 s; 6.8 GB |
| wt8_3 | exactly three of eight bits; n = 8, M = 56, r = 1 | (20, 159, 76, 12) measured | (281, 27, 0, 19, 38) | 0; 25/2048 | 38.6 s; 6.9 GB |
| wt8_3_count | Count, n = 8, m = 4 | (25, 2738, 1260, 13) **bound** | (4431, ≤ 1260, 6, 315, 630) | 0.200894; 0.189431 | 106.0 s; 7.0 GB |
| hw_n2, hw_n3 | n = 2, 3; M = 1 | (3, 32, 8, 1), (5, 110, 32, 2) | — | 0; 0 and 7/128 | 0.27 s, 2.3 s; 1.9, 2.3 GB |
| three frontier certificates | n = 2, 3 | (3, 46, 16, 1) to (5, 164, 64, 2) | — | — | 0.40–4.3 s; 1.9–2.7 GB |

**The arithmetic benchmarks.** `addchk3` and `wt8_3` were added after the reviews (revision R12), written from their definitions; `wt8_3` has the shape of the RevLib weight functions (rd53, rd73, rd84). A third, the 4-bit comparator x − y ≥ 5 (n = 8, M = 66), passes the harness, but its kernel check peaks at 8.6–8.8 GB (60.5 s; single runs, R12), above the 8 GB budget we keep for continuous integration on a 16 GB machine; it is therefore not committed as a certificate. Peak memory does not follow circuit size: `wt8_3` has more gates than the comparator and needs 1.7–1.9 GB less (Table 8).

**Where the kernel time goes.** It is mostly the kernel's evaluation of the synthesizer and scheduler on the literals; the parametric lemma is applied in constant time. Wall time adds 9–10 s, mostly loading the imported modules. The specification estimated 0.3 s for a certificate check.

**The diffusion variants.** For n = 8, r = 2:

| Diffusion | D<sub>8</sub> | Grover slice | Status |
|---|---|---|---|
| chain | (15, 89, 28, 7) | (15, 230, 72, 7) | proved |
| tree | (15, 41, 28, 7) | (15, 134, 72, 7) | default, certified |
| candidate A | (9, 93, 44, 1) | (10, 238, 104, 2) | tested only |
| candidate B | (10, 60, 40, 2) | (10, 172, 96, 2) | certified for every n |

In every row the Grover depth is 2(27 + d<sub>D</sub>) − 2, because consecutive blocks overlap by three layers. This is why the specification's formula r<sup>⋆</sup>(d<sub>O</sub> + d<sub>D</sub>) overestimates.

### 9.2 Physical and conditional certificates

See Tables 5–7.
- The fifteen check files take 9.5–30 s each and at most 4.1 GB.
- The physical certificate takes 53 s at 4.1 GB.
- The six conditional certificates take 10–22 s each and at most 2.7 GB.
- The four selection files take 7.5–31 s each and at most 3.3 GB.

The *featured* physical certificate is of a 2 541-gate circuit; the *largest* reconstruction checked in CI has 4 170 gates.

### 9.3 Differential testing

**The harness.** An independent Python statevector harness enumerates every measurement branch of each synthesized circuit with at most 12 data qubits (20 simulated qubits). For the R12 benchmarks, whose checks have 2<sup>5</sup> to 2<sup>26</sup> branches, it enumerates every branch up to 2<sup>13</sup> and 32 distinct sampled branches beyond (4 in CI). From random superpositions, it checks two things:
- each branch's output against U|ψ⟩ ⊗ |0⟩, to 10<sup>−9</sup>;
- the |0⟩ state of every freed qubit.

**Coverage.**
- 30 random predicates with XOR and `if`, all chain and tree diffusions for n ≤ 10, and both few-ancilla candidates (with negative controls).
- The counting circuits (phase statistics against the closed form to 2·10<sup>−14</sup>, for n ≤ 6 and m ≤ 4), and the QFT and AQFT for m ≤ 6.
- The ALU predicate: 32 768 branches.
- The R12 benchmarks: each program against its arithmetic definition on all 2<sup>n</sup> inputs, then the oracle, one iteration and the full circuit in both shapes.
- The hardware lowering on 18 instances, and the ideal equivalence of every routed circuit.

**Findings.** The harness found the missing MBU reset before the proof was attempted. No grade is claimed for a circuit that has not passed it.

### 9.4 Size and continuous integration

| Component | Size |
|---|---|
| Lean library (`CQRV/`, 111 modules) | 39 114 lines, about 2 000 theorem and lemma declarations |
| CLI (`Apps/cqr`) | 1 716 lines |
| Lean tests | 6 062 lines |
| Python and shell (harness, hardware tools, checks) | 13 236 lines |
| `sorry` | 0 |
| Development | 171 commits over 27 days |

Sizes are at the Stage 30 commit `a2e1b6e`. The first revision task after the reviews (R1, R2, R15) added 241 net lines to the library.

**The local CI** has 26 steps (4 not applicable locally) and runs in about 35 minutes. It includes:
- a warning-free build and a blocking axiom audit;
- a full re-certification of every example, byte for byte;
- the harness;
- the hardware target, lowering, transpile (reproducing every artifact from its seed), emulator, check-file, physical-certificate and noise steps.

The largest step takes 675–1 040 s depending on machine load. The CI has not run on a hosted runner.

### 9.5 What the evaluation does and does not show

**What it shows.** The repository's Lean and Python paths agree, every claimed certificate checks in the kernel, and the per-instance checks scale to a few thousand gates on this machine.

**What it does not show.**
- **Breadth.** Few predicates are certified: a 3-literal conjunction, one RevLib function [Wille et al. 2008], two small arithmetic predicates (a 3-bit adder check and a weight function), and the small frontier family. Kernel memory, not time, limited the third arithmetic predicate.
- **Scaling.** There is no scaling study beyond the reported sizes, and no formal complexity proof of the checker.
- **Independent reproduction.** None so far; the repository is public.
- **A comparison with other verified toolchains.** None on the same circuits (Section 10).


## 10 Related work

<p class="caption"><b>Table 9.</b> Feature comparison, as we read the cited papers. "Restoration" means a machine-checked ancilla-restoration statement; "MBU" means measurement-based uncomputation inside the verified semantics.</p>

| System | Proof assistant / method | Verifies | Non-unitary MBU | Restoration | Terminal measurement in the spec | Resource grade | Routing validation | Noise |
|---|---|---|---|---|---|---|---|---|
| ReVerC [Amy et al. 2017] | F⋆ | compiler (Boolean → reversible) | no | clean, yes | no | no | no | no |
| VQO [Li et al. 2022] | Coq | oracle compiler, all sizes | no | yes | no | no | no | no |
| SQIR / VOQC [Hietala et al. 2021a, b] | Coq | programs; optimizer passes; mapping | no | — | programs, yes | no | mapping for unitary circuits | no |
| QWIRE / ReQWIRE [Paykin et al. 2017; Rand et al. 2019] | Coq | circuits; ancilla correctness | no | yes | — | no | no | no |
| Qbricks [Chareton et al. 2021] | Why3 | parametric programs (Grover, QPE) | no | — | yes | some | no | no |
| CoqQ [Zhou et al. 2023] | Coq | programs (quantum logic) | — | — | yes | no | no | no |
| CertiQ / Giallar [Shi et al. 2019; Tao et al. 2022] | SMT, push-button | Qiskit passes, once | no | — | — | no | passes verified | no |
| QCEC [Burgholzer and Wille 2021; Burgholzer et al. 2020] | decision diagrams, ZX (unverified tool) | equivalence of compiled circuits | dynamic circuits | — | — | no | post hoc, unitary | no |
| Ancilla safety [Li et al. 2026] | algorithmic verification and repair | clean/dirty ancilla safety | — | yes (checked, not mechanized) | — | no | no | no |
| **This work** | Lean 4 kernel | per-request certificates; two patterns | **yes** | **yes**, on density operators | **yes** (decoding POVM) | **yes** (measured, or bound) | **witness check, kernel** | **conditional, named premises** |

**Verified compilation and programs.** Quantum Hoare logic has been mechanized in Isabelle/HOL [Liu et al. 2019], and the systems of Table 9 verify programs or compilers in Coq, F⋆ and Why3. VQO is the closest system for oracles. It proves an oracle compiler correct from source to circuit for every input size. Its semantics is unitary, so MBU lies outside it, and it has no resource grade or matching layer. Our front end is proved from typed term to network, with the parser a declared boundary.

**Phase estimation.** QPE has been mechanized for abstract unitaries: in Qbricks, and in SQIR as the core of order finding [Chareton et al. 2021; Hietala et al. 2021a]. Our Theorem 6.7 is the two-eigenphase bound for the *synthesized* Grover iterate. It decodes sin<sup>2</sup>(πy/2<sup>m</sup>) under a pseudo-metric realization, inside a circuit that restores its ancillae under MBU, and composes with the AQFT bound.

**Uncomputation.** Silq and Unqomp [Bichsel et al. 2020; Paradis et al. 2021] make uncomputation safe or automatic at the language level. Li et al. [2026] verify and repair clean- and dirty-ancilla safety algorithmically at scale. Our Section 5 is a mechanized semantic account specific to MBU: the general theorem, its Clifford boundary in a circuit language, the regimes as predicates on joint states, and a proof of the Khattar–Gidney construction for every n.

**Validating Qiskit's output.**
- *Once-and-for-all verification.* CertiQ and Giallar verify passes of the Qiskit compiler once.
- *Post-hoc equivalence checking.* Burgholzer et al. [2020] and QCEC [Burgholzer and Wille 2021] check the equivalence of compiled circuits with fast, unverified decision-diagram and ZX methods.
- *Mapping in VOQC.* VOQC includes verified circuit mapping for unitary circuits.

Our Track C is a translation validator in the sense of Pnueli et al. [1998], whose checker runs in a proof-assistant kernel. It covers dynamic circuits with mid-circuit measurement and conditioned blocks, the basis translation, and coupling edges. It also transfers the realization and restoration statements, not only equivalence, to the routed circuit. Its scope is the transformation fragment of Section 7.5.

**Noise.** Diamond-norm perturbation bounds are standard [Aharonov et al. 1998; Watrous 2018]. What is specific here is that the bound is a kernel-checked theorem about a certified physical circuit, with its premises as hypotheses. Their weakness relative to real noise is discussed in Section 8.3.

**Stage 29.** A quantitative comparison with SQIR / VOQC on the same circuits (proof size, effort, checking time) was planned and not carried out: it needs the Coq toolchain, which was not installed without the author's approval. No figure from those systems is used here.


## 11 Limitations and threats to validity

**What is outside the kernel** (Table 1):
- the parser, the surface checker with its call inlining, and the printer of the typed-term literal;
- extraction and the matcher's run;
- the emitters, including QIR's floating-point angles;
- Qiskit, the target files and the calibration snapshots, each bound by hash;
- the Lean toolchain.

**Model premises.** The physical statement assumes an ideal device with the target's gates and connectivity, exact preparation (P-prep) and exact classical control (P-ctrl). The conditional statement adds (P-cal), (P-stoch), (P-ro) and (P-idle). (P-stoch) is not derivable from calibration numbers and is optimistic for coherent errors, and (P-idle) is contradicted by the idle diagnostic at moderate sizes.

**Scope.**
- Two patterns.
- Specifications are Boolean predicates; search has trivial input.
- Counting excludes M = 0, so search after count assumes a satisfiable predicate.
- Amplitude amplification is not implemented.
- The few-ancilla `ladder` variant is not certified.
- Signature-match completeness is not semantic completeness.
- The cost bound of matching is not formalized.
- Kernel memory bounds the size of a flat certificate on the development machine: a 4-bit comparator needs 8.6–8.8 GB.

**Resources.**
- The T-count is native-gate: arbitrary-angle rotations are counted separately, without synthesis cost.
- The counting grade is a composed bound.
- Measured composition charges nothing for measurement, selection, re-preparation or latency.
- Wall-clock depth depends on an assumed feed-forward latency.

**Open proofs.**
- The widening of the dirty regime.
- The all-n attainment of 8n − 24.
- The categorical form of the no-cloning theorem.

**Threats to validity of the evidence.**
- **Internal consistency.** The evidence is kernel checking and agreement between the Lean and Python paths, not independent reproduction.
- **Measurements.** The times and memory come from one run at one commit, on one machine with heterogeneous cores; no second machine has repeated them.
- **The development process.** A second session of the same AI assistant reviewed the implementing session. That review is procedural and not an independent scientific audit; the kernel cannot tell whether a definition captures the intended physical concept. A human expert audit of `Realizes`, `AncRestore`, `channelDenote` and the premises is recommended before the claims are relied on (R14).
- **Sources not peer-reviewed.** The specification report the project implements [Zambak 2026b] has not been peer-reviewed; its revisions v2 and v3 are in the repository. The earlier proposal [Zambak 2026a] is unpublished.
- **The artifact.** The repository is public with its full history ([GITHUB-URL], tag `v1.0.0`), so every commit cited in this paper can be inspected. No container image is provided; reproduction relies on the pinned toolchain and the steps in `docs/RELEASE.md`.

## 12 Conclusion

**The prototype.** We built a two-pattern prototype of certified quantum realization in Lean 4. For Boolean predicates, its logical certificates state realization (with exact δ for search and an (ε, δ) estimate for counting) together with ancilla restoration on density operators, so measurement-based uncomputation is inside the correctness statement. Each certificate's assumptions are enumerated (Table 1): the parser, surface checker, typed-term printer and emitters as declared boundaries, the solution count as a hypothesis above a limit, and a measured grade for flat certificates or a certified compositional bound for counting.

**The theory around it.**
- a general MBU theorem, and the Clifford/quadratic boundary of its corrections in the circuit language;
- implications among the ancilla regimes;
- the Khattar–Gidney two-ancilla MCZ for every n;
- the 8n − 24 lower bound within its family;
- the QFT and AQFT bounds and the phase-estimation bound for the Grover iterate.

**Routed circuits.** The certificate can follow a circuit through an untrusted transpiler. A witness-based reconstruction, checked by the kernel for circuits of up to 4 170 gates, transfers the realization to the routed circuit on an ideal device with the target's gates and connectivity, for transpiler outputs in a stated fragment.

**Noise.** Noise enters as named premises of a proved perturbation theorem. On two shipped calibration snapshots, within the tested family, the resulting bound is non-vacuous only up to three data qubits, and beats a classical baseline in three of five such instances. We report this as the current reach of guarantees of this kind, not as a property of the method's soundness.

**What the process showed.** The implementation recorded sixteen discrepancies with its guiding specification, nine of them substantive, and corrected its own task texts eight times, each by a measurement or a counterexample (Appendix C). The lesson we draw is the one the reviews of this paper reinforced: the difficulty is less in proving theorems about circuits than in making every claim say exactly what the theorem says.

## Acknowledgements and disclosure of AI assistance

**AI assistance.** The software was implemented by an AI coding assistant (Claude Code, Anthropic), task by task, under written project rules (Appendix D). The task specifications and the reviews of each task were drafted by a second session of the assistant; through Stage 21 the author approved or amended them.

**This article.** It was drafted with AI assistance and revised after two external reviews, and it is the author's responsibility.

**What does not depend on the assistants.** Every theorem reported as proved is checked by the Lean kernel and audited for axioms.

## Data and code availability

**The repository** contains the Lean sources, the generators, the Python harness and hardware tools, all committed certificates, check files, selection files and artifacts with their run reports, the decision log, the obligation ledger, and CI logs. It is public at [GITHUB-URL] under the Apache License 2.0, with its full development history. This paper describes the code at commit `2f8200b`; the tag `v1.0.0` adds only documentation (the license, the citation file, the release notes and this paper). `docs/RELEASE.md` gives the reproduction steps: the pins, the two Python environments and every CI step with its command. No container image is provided.

**The pinned toolchain:**
- Lean v4.35.0, Mathlib `56a0058`, Physlib `96a6bc5`;
- for the hardware layer, qiskit 2.6.2, qiskit-aer 0.18.2 and qiskit-ibm-runtime 0.52.1, whose fake backends' calibration snapshots are the ones used.


## References

<div class="refs">

[Zambak 2026a] is an unpublished report, available from the author; revisions v2 and v3 of [Zambak 2026b] are in the repository.

- [Abramsky 2010] Samson Abramsky. No-cloning in categorical quantum mechanics. In S. Gay and I. Mackie, eds., *Semantic Techniques in Quantum Computation*, pp. 1–28. Cambridge University Press, 2010.
- [Aharonov et al. 1998] Dorit Aharonov, Alexei Kitaev, Noam Nisan. Quantum circuits with mixed states. In *Proc. 30th ACM STOC*, pp. 20–30, 1998.
- [Amy et al. 2017] Matthew Amy, Martin Roetteler, Krysta M. Svore. Verified compilation of space-efficient reversible circuits. In *CAV 2017*, LNCS 10427, pp. 3–21. Springer, 2017.
- [Barenco et al. 1995] Adriano Barenco, Charles H. Bennett, Richard Cleve, David P. DiVincenzo, Norman Margolus, Peter Shor, Tycho Sleator, John A. Smolin, Harald Weinfurter. Elementary gates for quantum computation. *Physical Review A* 52(5):3457–3467, 1995.
- [Barenco et al. 1996] Adriano Barenco, Artur Ekert, Kalle-Antti Suominen, Päivi Törmä. Approximate quantum Fourier transform and decoherence. *Physical Review A* 54:139–146, 1996.
- [Bennett 1973] Charles H. Bennett. Logical reversibility of computation. *IBM J. Res. Dev.* 17(6):525–532, 1973.
- [Bennett 1989] Charles H. Bennett. Time/space trade-offs for reversible computation. *SIAM J. Comput.* 18(4):766–776, 1989.
- [Bichsel et al. 2020] Benjamin Bichsel, Maximilian Baader, Timon Gehr, Martin Vechev. Silq: A high-level quantum language with safe uncomputation and intuitive semantics. In *PLDI 2020*, pp. 286–300.
- [Boyar et al. 2000] Joan Boyar, René Peralta, Denis Pochuev. On the multiplicative complexity of Boolean functions over the basis (∧, ⊕, 1). *Theoretical Computer Science* 235(1):43–57, 2000.
- [Boyer et al. 1998] Michel Boyer, Gilles Brassard, Peter Høyer, Alain Tapp. Tight bounds on quantum searching. *Fortschritte der Physik* 46(4–5):493–505, 1998.
- [Brassard et al. 2002] Gilles Brassard, Peter Høyer, Michele Mosca, Alain Tapp. Quantum amplitude amplification and estimation. In *Quantum Computation and Information*, Contemporary Mathematics 305, pp. 53–74. AMS, 2002.
- [Burgholzer and Wille 2021] Lukas Burgholzer, Robert Wille. Advanced equivalence checking for quantum circuits. *IEEE Trans. Comput.-Aided Des. Integr. Circuits Syst.* 40(9):1810–1824, 2021.
- [Burgholzer et al. 2020] Lukas Burgholzer, Rudy Raymond, Robert Wille. Verifying results of the IBM Qiskit quantum circuit compilation flow. In *IEEE Int. Conf. on Quantum Computing and Engineering (QCE)*, 2020. arXiv:2009.02376.
- [Chareton et al. 2021] Christophe Chareton, Sébastien Bardin, François Bobot, Valentin Perrelle, Benoît Valiron. An automated deductive verification framework for circuit-building quantum programs. In *ESOP 2021*, LNCS 12648, pp. 148–177. Springer, 2021.
- [Cleve et al. 1998] Richard Cleve, Artur Ekert, Chiara Macchiavello, Michele Mosca. Quantum algorithms revisited. *Proc. R. Soc. Lond. A* 454:339–354, 1998.
- [Coppersmith 1994] Don Coppersmith. An approximate Fourier transform useful in quantum factoring. IBM Research Report RC 19642, 1994; arXiv:quant-ph/0201067.
- [Cross et al. 2022] Andrew Cross, Ali Javadi-Abhari, Thomas Alexander, Niel de Beaudrap, Lev S. Bishop, Steven Heidel, Colm A. Ryan, Prashant Sivarajah, John Smolin, Jay M. Gambetta, Blake R. Johnson. OpenQASM 3: A broader and deeper quantum assembly language. *ACM Trans. Quantum Comput.* 3(3):12:1–12:50, 2022.
- [de Moura and Ullrich 2021] Leonardo de Moura, Sebastian Ullrich. The Lean 4 theorem prover and programming language. In *CADE 28*, LNCS 12699, pp. 625–635. Springer, 2021.
- [Dehaene and De Moor 2003] Jeroen Dehaene, Bart De Moor. Clifford group, stabilizer states, and linear and quadratic operations over GF(2). *Physical Review A* 68:042318, 2003.
- [Gidney 2018] Craig Gidney. Halving the cost of quantum addition. *Quantum* 2:74, 2018.
- [Gottesman 1998] Daniel Gottesman. The Heisenberg representation of quantum computers. arXiv:quant-ph/9807006, 1998.
- [Grover 1996] Lov K. Grover. A fast quantum mechanical algorithm for database search. In *Proc. 28th ACM STOC*, pp. 212–219, 1996.
- [Hietala et al. 2021a] Kesha Hietala, Robert Rand, Shih-Han Hung, Liyi Li, Michael Hicks. Proving quantum programs correct. In *ITP 2021*, LIPIcs 193, pp. 21:1–21:19.
- [Hietala et al. 2021b] Kesha Hietala, Robert Rand, Shih-Han Hung, Xiaodi Wu, Michael Hicks. A verified optimizer for quantum circuits. *Proc. ACM Program. Lang.* 5(POPL):37:1–37:29, 2021.
- [Horodecki et al. 1999] Michał Horodecki, Paweł Horodecki, Ryszard Horodecki. General teleportation channel, singlet fraction, and quasidistillation. *Physical Review A* 60:1888–1898, 1999.
- [Janzing et al. 2005] Dominik Janzing, Pawel Wocjan, Thomas Beth. "Non-identity check" is QMA-complete. *Int. J. Quantum Inf.* 3(3):463–473, 2005.
- [Javadi-Abhari et al. 2024] Ali Javadi-Abhari et al. Quantum computing with Qiskit. arXiv:2405.08810, 2024.
- [Khattar and Gidney 2025] Tanuj Khattar, Craig Gidney. Rise of conditionally clean ancillae for efficient quantum circuit constructions. *Quantum* 9:1752, 2025. arXiv:2407.17966.
- [Kitaev 1995] A. Yu. Kitaev. Quantum measurements and the Abelian stabilizer problem. arXiv:quant-ph/9511026, 1995.
- [Kitaev 1997] A. Yu. Kitaev. Quantum computations: algorithms and error correction. *Russian Math. Surveys* 52(6):1191–1249, 1997.
- [Landauer 1961] Rolf Landauer. Irreversibility and heat generation in the computing process. *IBM J. Res. Dev.* 5(3):183–191, 1961.
- [Leroy 2009] Xavier Leroy. Formal verification of a realistic compiler. *Commun. ACM* 52(7):107–115, 2009.
- [Li et al. 2019] Gushu Li, Yufei Ding, Yuan Xie. Tackling the qubit mapping problem for NISQ-era quantum devices. In *ASPLOS 2019*, pp. 1001–1014.
- [Li et al. 2022] Liyi Li, Finn Voichick, Kesha Hietala, Yuxiang Peng, Xiaodi Wu, Michael Hicks. Verified compilation of quantum oracles. *Proc. ACM Program. Lang.* 6(OOPSLA2):146:1–146:27, 2022. arXiv:2112.06700.
- [Li et al. 2026] Jiqi Li, Jingyi Mei, Wang Fang, Ji Guan. Formal verification of quantum ancilla safety. arXiv:2608.13099, 2026.
- [Liu et al. 2019] Junyi Liu, Bohua Zhan, Shuling Wang, Shenggang Ying, Tao Liu, Yangjia Li, Mingsheng Ying, Naijun Zhan. Formal verification of quantum algorithms using quantum Hoare logic. In *CAV 2019*, LNCS 11562, pp. 187–207.
- [Magesan et al. 2011] Easwar Magesan, Jay M. Gambetta, Joseph Emerson. Scalable and robust randomized benchmarking of quantum processes. *Physical Review Letters* 106:180504, 2011.
- [Maslov 2016] Dmitri Maslov. Advantages of using relative-phase Toffoli gates with an application to multiple control Toffoli optimization. *Physical Review A* 93:022311, 2016.
- [mathlib 2020] The mathlib Community. The Lean mathematical library. In *CPP 2020*, pp. 367–381.
- [Meuli et al. 2019] Giulia Meuli, Mathias Soeken, Martin Roetteler, Nikolaj Bjørner, Giovanni De Micheli. Reversible pebbling game for quantum memory management. In *DATE 2019*, pp. 288–291.
- [Miller 1991] Dale Miller. A logic programming language with lambda-abstraction, function variables, and simple unification. *J. Logic Comput.* 1(4):497–536, 1991.
- [Necula 1997] George C. Necula. Proof-carrying code. In *POPL 1997*, pp. 106–119.
- [Nie et al. 2024] Junhong Nie, Wei Zi, Xiaoming Sun. Quantum circuit for multi-qubit Toffoli gate with optimal resource. arXiv:2402.05053, 2024.
- [Nielsen 2002] Michael A. Nielsen. A simple formula for the average gate fidelity of a quantum dynamical operation. *Physics Letters A* 303:249–252, 2002.
- [NIST 2015] National Institute of Standards and Technology. SHA-3 standard: Permutation-based hash and extendable-output functions. FIPS 202, 2015.
- [Paradis et al. 2021] Anouk Paradis, Benjamin Bichsel, Samuel Steffen, Martin Vechev. Unqomp: Synthesizing uncomputation in quantum circuits. In *PLDI 2021*, pp. 222–236.
- [Paykin et al. 2017] Jennifer Paykin, Robert Rand, Steve Zdancewic. QWIRE: A core language for quantum circuits. In *POPL 2017*, pp. 846–858.
- [Physlib 2026] Physlib contributors. Physlib: physics and quantum information in Lean 4. https://github.com/leanprover-community/physlib, 2026. Commit 96a6bc5.
- [Plotkin 1970] Gordon D. Plotkin. A note on inductive generalization. In *Machine Intelligence 5*, pp. 153–163. Edinburgh University Press, 1970.
- [Pnueli et al. 1998] Amir Pnueli, Michael Siegel, Eli Singerman. Translation validation. In *TACAS 1998*, LNCS 1384, pp. 151–166.
- [QIR Alliance 2024] QIR Alliance. QIR specification. https://github.com/qir-alliance/qir-spec, 2024. Base and Adaptive Profiles.
- [Rand et al. 2019] Robert Rand, Jennifer Paykin, Dong-Ho Lee, Steve Zdancewic. ReQWIRE: Reasoning about reversible quantum circuits. In *QPL 2018*, EPTCS 287, pp. 299–312, 2019.
- [Reynolds 1970] John C. Reynolds. Transformational systems and the algebraic structure of atomic formulas. In *Machine Intelligence 5*, pp. 135–151. Edinburgh University Press, 1970.
- [Shi et al. 2019] Yunong Shi, Xupeng Li, Runzhou Tao, Ali Javadi-Abhari, Andrew W. Cross, Frederic T. Chong, Ronghui Gu. CertiQ: A mostly-automated verification of a realistic quantum compiler. arXiv:1908.08963, 2019.
- [Tao et al. 2022] Runzhou Tao, Yunong Shi, Jianan Yao, Xupeng Li, Ali Javadi-Abhari, Andrew W. Cross, Frederic T. Chong, Ronghui Gu. Giallar: Push-button verification for the Qiskit quantum compiler. In *PLDI 2022*, pp. 641–656.
- [Wallman and Emerson 2016] Joel J. Wallman, Joseph Emerson. Noise tailoring for scalable quantum computation via randomized compiling. *Physical Review A* 94:052325, 2016.
- [Watrous 2018] John Watrous. *The Theory of Quantum Information*. Cambridge University Press, 2018.
- [Wille et al. 2008] Robert Wille, Daniel Große, Lisa Teuber, Gerhard W. Dueck, Rolf Drechsler. RevLib: An online resource for reversible functions and reversible circuits. In *ISMVL 2008*, pp. 220–225.
- [Zambak 2026a] Aziz F. Zambak. Certified quantum realization of classical specifications (Revision 3). Research proposal, unpublished technical report, 2026. Available from the author.
- [Zambak 2026b] Aziz F. Zambak. Applying certified quantum realization: A practical implementation guide. Technical report, June 2026. Revision v2 (June 27, 2026); revision v3 with errata appendix, October 2026. Both revisions are in the CQRV repository (`docs/cqrv_report_revised_v2.docx`, `docs/cqrv_report_revised_v3.docx`).
- [Zhou et al. 2023] Li Zhou, Gilles Barthe, Pierre-Yves Strub, Junyi Liu, Mingsheng Ying. CoqQ: Foundational verification of quantum programs. *Proc. ACM Program. Lang.* 7(POPL):833–865, 2023.

</div>


<div class="appendix">

## Appendix A — Main Lean statements

The statements below are transliterated from the Lean sources, with implicit arguments and type-class assumptions abbreviated. `⊗ᴹ` is Physlib's product of states, `◃` the action ρ ↦ UρU<sup>†</sup>, and `∘ₘ` composition of channels. `+` on `Grade` is the sequential sum ⊕ of Section 3.1. In the hardware statements `b` is the target's basis and `bb` the number of spare physical qubits, so the device register has N = n + (a + bb) qubits. Each statement is restated in full in `tests/CQRVTests/PaperStatements.lean` and proved there by the library name, so the kernel confirms that the form below is the library's up to these abbreviations; `docs/PAPER_STATEMENTS.md` gives each declaration's file and line. Three further differences are notational: `grover_parametric_lemma_diff` takes C implicitly, `mbu_exactly_quadratic` states its gate conditions as Boolean equalities, and `diamondDist_mix_le` has the cast 2 · (p : ℝ).

**Realization and restoration** (`CQRV/Realizability/Realizes.lean`, `CQRV/Circuit/Restoration.lean`).

<div class="code">def Realizes (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (ε δ : ℝ) (r : Grade) : Prop :=
  Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S.relax ε x)
def RealizesExact (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (δ : ℝ) (r : Grade) : Prop :=
  Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S x)
def AncRestore (n a : ℕ) (C : Circuit) (U : 𝐔[Reg n]) : Prop :=
  ∀ ρ : MState (Reg n), channelDenote n a C (ρ ⊗ᴹ ancZero a) = (U ◃ ρ) ⊗ᴹ ancZero a</div>

**No-cloning** (`CQRV/Realizability/Obstruction.lean`).

<div class="code">theorem no_cloning_linear [Nonempty d] :
    ¬ ∃ C : (d → ℂ) →ₗ[ℂ] (d × d → ℂ), ∀ ψ : d → ℂ, C ψ = fun ij => ψ ij.1 * ψ ij.2
theorem no_cloning_pure (hd : 2 ≤ Fintype.card d) :
    ¬ ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ, ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ)
theorem pure_cloning_of_card_one (hd : Fintype.card d = 1) :
    ∃ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix (d × d) (d × d) ℂ, ∀ ψ : d → ℂ, ∑ k, Complex.normSq (ψ k) = 1 →
        Φ (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) ⊗ₖ vecMulVec ψ (star ψ)</div>

**Composition and the diamond distance** (`CQRV/Realizability/`).

<div class="code">theorem measured_composition_pseudo (hf : Realizes S_f dec_f Φ ε_f δ_f r) (hg : Realizes S_g dec_g Ψ ε_g δ_g s)
    (hdom : ∀ x ∈ S_f.dom, ∀ y, S_f.relax ε_f x y → y ∈ S_g.dom)
    (hnonexp : ∀ y ∈ S_g.dom, ∀ y' z', S_g y' z' → ∃ z, S_g y z ∧ dist z z' ≤ dist y y')
    (hdf : 0 ≤ δ_f) (hdg : 0 ≤ δ_g) (hdg1 : δ_g ≤ 1) :
    Realizes (S_g.comp S_f) dec_g (measuredComp Φ dec_f Ψ) (ε_f + ε_g) (δ_f + δ_g) (r + s)
def diamondDist (Λ₁ Λ₂ : CPTPMap A B) : ℝ :=
  ⨆ ρ : MState (A × A), 2 * TrDistance ((Λ₁ ⊗ᶜᵖ CPTPMap.id) ρ) ((Λ₂ ⊗ᶜᵖ CPTPMap.id) ρ)
theorem coherent_composition_diamond (hideal : Realizes (S_g.comp S_f) dec ⟨Ψ₁ ∘ₘ Φ₁, 0⟩ ε₀ δ₀ 0)
    (hΦ : diamondDist Φ₂.chan Φ₁ ≤ η_f) (hΨ : diamondDist Ψ₂.chan Ψ₁ ≤ η_g)
    (hr : Φ₂.grade ≤ r) (hs : Ψ₂.grade ≤ s) :
    Realizes (S_g.comp S_f) dec ⟨Ψ₂.chan ∘ₘ Φ₂.chan, Φ₂.grade + Ψ₂.grade⟩ ε₀ (δ₀ + (η_f + η_g) / 2) (r + s)</div>

**Synthesis, Grover, the two-ancilla diffusion.**

<div class="code">theorem lemma_6_3_2_xor (hC : synthesizeOracle N = .ok C) (hWF : C.WF) :
    AncRestore C.nData C.nAnc C (phaseOracle (N.pred C.nData))
theorem synthesizeOracle_WF (hN : N.WF) (hC : synthesizeOracle N = .ok C) : C.WF
theorem synthesizeOracle_succeeds (hN : N.WF) (h1 : N.outputs.length = 1) : ∃ C, synthesizeOracle N = .ok C
theorem grover_parametric_lemma_diff (gp : GroverParams) (Dc : Circuit) (hDb : Dc.bitsOk = true)
    (hDr : ∀ a, Dc.nAnc ≤ a → AncRestore gp.n a Dc (diffU gp.n)) (r : ℕ) (C : Circuit)
    (hC : C = groverCircuitOf gp.oracle.C Dc gp.n r) :
    RealizesExact (SearchSpec gp.oracle.P) (basisPOVM gp.n) (groverChannel gp.n C)
      (1 - Real.sin ((2 * r + 1) * gp.θ) ^ 2) (Synthesis.grade C) ∧
    AncRestore gp.n C.nAnc C (groverOp gp.oracle.P ^ r * hadamardU gp.n)
theorem mczFew_logDepth_ok (hn : n ≠ 0) : ∃ C, mczFew n .logDepth = .ok C
theorem mczFew_logDepth_ancRestore (hC : mczFew n .logDepth = .ok C) : AncRestore n 2 C (phaseOracle allOnes)
theorem diffusionFew_logDepth_ancRestore (hD : diffusionFew n .logDepth = .ok D) :
    ∀ a, D.nAnc ≤ a → AncRestore n a D (diffU n)</div>

**Counting.**

<div class="code">theorem qpe_success (gp : GroverData) (hm : 1 ≤ m) :
    8 / π ^ 2 ≤ ∑ y ∈ univ.filter (fun y : Reg m => |sin (π * y.toNat / 2 ^ m) ^ 2 - gp.M / 2 ^ gp.n|
                                      ≤ ae_eps (gp.M / 2 ^ gp.n) m), phaseDist gp m y
theorem ae_parametric_lemma (gp : GroverData) (hm : 1 ≤ m) (hN : N.WF) (hn : N.nInputs = gp.n)
    (h1 : N.outputs.length = 1) (hP : N.pred gp.n = gp.P)
    (hC : countingCircuit N gp.n m none shape mode = .ok C) (g : Grade) (hg : Synthesis.grade C ≤ g) :
    Realizes (CountSpec m (gp.M / 2 ^ gp.n)) (countPOVM gp.n m (gp.M / 2 ^ gp.n))
        (groverChannel (gp.n + m) C) (ae_eps (gp.M / 2 ^ gp.n) m) ae_delta g ∧
      AncRestore (gp.n + m) C.nAnc C (U_count gp.P m none)
theorem aqft_diamond_le (m kmax : ℕ) :
    diamondDist (channelDenote m 0 (qftCircuit m)) (channelDenote m 0 (aqftCircuit m kmax)) ≤ eta_aqft m kmax</div>

**Restoration under measurement.**

<div class="code">theorem mbu_general (hWF : C.WF) (hgates : C.gates = B ++ mbuUncompute t j O) (hanc : ∃ i, i < a ∧ t = .anc i)
    (hB : ComputesInto n a B t f φ) (hO : PhaseImpl n a O f) : AncRestore n a C (diagU φ hB.norm)
theorem clifford_iff_quadratic (f : Reg n → Bool) : IsCliffordDiag (phaseDiag f) ↔ IsQuadratic f
theorem mbu_exactly_quadratic (hB : ∀ g ∈ B, g.qubitsOk n ∧ g.isUnitary) (hanc : ∃ i, i < a ∧ t = .anc i) (f) :
    (∃ j O C, C.nData = n ∧ C.WF ∧ C.gates = B ++ [.z t] ++ mbuUncompute t j O ∧ PhaseImpl n a O f) ↔ IsQuadratic f
theorem supportFactor (hω : ancProj n a * ω.m * ancProj n a = ω.m) : ω = ω.traceRight ⊗ᴹ ancZero a
theorem ancRestoreCond_true_iff : AncRestoreCond n a C U (fun _ => true) ↔ AncRestore n a C U
theorem problem1_T_lower_bound (h : valid s os = true) (hn : s.live = n) (hf : s.freshCard = 2)
    (hk : (run s os).live ≤ 2) (h4 : 4 ≤ n) : 8 * n - 24 ≤ cost s os</div>

**The backend and noise.**

<div class="code">theorem applyWitness_sound (hC : C.WF) (hG : applyWitness b C w N = .ok G)
    (hWF : (physCircuit N G).WF) (hM : (physCircuit N G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin N)) (h₀ : w.initial = layOf N (n + a) σ₀) :          -- N = n + (a + bb)
    ∃ σf, w.final = layOf N (n + a) σf ∧
      ∀ ρ, channelDenote N 0 (physCircuit N G) (embed bb σ₀ ρ) = embed bb σf (channelDenote n a C ρ)
theorem applyWitnessQ_ok (hC : C.WF) (h : applyWitnessQ b C w N = .ok G) : applyWitness b C w N = .ok G
theorem applyWitnessQ_sound (hC : C.WF) (hG : applyWitnessQ b C w N = .ok G) (hWF : (physCircuit N G).WF)
    (hM : (physCircuit N G).nBits = C.nBits) (σ₀ : Equiv.Perm (Fin N)) (h₀ : w.initial = layOf N (n + a) σ₀) :
    w.final = layOf N (n + a) (finalPerm b C w N σ₀) ∧
      ∀ ρ, channelDenote N 0 (physCircuit N G) (embed bb σ₀ ρ) = embed bb (finalPerm b C w N σ₀) (channelDenote n a C ρ)
theorem channelDenote_eq_steps (hC : C.WF) (ρ) :
    channelDenote n a C ρ = traceRight (stepsOf n a C.nBits C.gates (ρ ⊗ᴹ ancZero C.nBits))
theorem diamondDist_mix_le (p : Prob) (Φ Φ' : CPTPMap A B) : diamondDist (mix p Φ Φ') Φ ≤ 2 * p
theorem noisy_realization (hideal : RealizesExact S dec ⟨Γ ∘ₘ traceRight ∘ₘ steps (L.map (·.1)) ∘ₘ prep, g⟩ δ r)
    (hL : ∀ t ∈ L, diamondDist t.2.1 t.1 ≤ t.2.2) :
    RealizesExact S dec ⟨Γ ∘ₘ traceRight ∘ₘ steps (L.map (·.2.1)) ∘ₘ prep, g⟩ (δ + (L.map (·.2.2)).sum / 2) r
theorem phys_noisy_stochastic (hC : C.WF) (hG : applyWitness b C w N = .ok G) (hWF : (physCircuit N G).WF)
    (hM : (physCircuit N G).nBits = C.nBits) (σ₀ : Equiv.Perm (Fin N)) (h₀ : w.initial = layOf N (n + a) σ₀)
    (h : RealizesExact S dec (groverChannel n C) δ r)
    (T : List (BasisGate × Prob × CPTPMap X⁺ X⁺)) (hT : T.map (·.1) = G) (R : List (Prob × CPTPMap X⁺ X⁺)) :
    ∃ σf, w.final = layOf N (n + a) σf ∧
      RealizesExact S dec ⟨unembed bb σf ∘ₘ traceRight ∘ₘ steps (stochasticSteps N m T R) ∘ₘ physPrep N m (embed bb σ₀ ρ₀), g_phys⟩
        (δ + Σ_{t ∈ T} p_t + Σ_{r ∈ R} r) g_phys          -- X⁺ = XReg N 0 m, m = (physCircuit N G).nBits,
                                    -- ρ₀ = ancZero n ⊗ᴹ ancZero a, g_phys = grade (physCircuit N G)</div>

## Appendix B — Reproduction and provenance

**Environment.** Reproduction needs:
- the pinned toolchain, with the Mathlib cache fetched (`lake exe cache get`);
- the harness environment `.venv` with its locked requirements;
- for the hardware layer, the environment `.venv-hw` with its lock.

The commands below rebuild the library, run the local CI and regenerate representative files. The generated files must be byte-identical to the committed ones.

<div class="code">lake build
LEAN_NUM_THREADS=4 scripts/ci_local.sh                     # 26 steps; about 35 minutes
lake exe cqr certify examples/grover_pred_037.cqr --report
lake exe cqr certify examples/grover_pred_037.cqr --shape few:log
lake exe cqr certify examples/grover_pred_037.cqr --problem count --precision 4
lake exe cqr hw check --artifact hw/artifacts/grover_pred_037_tree_mbu__fake_torino --target hw/targets/fake_torino.json
lake exe cqr hw certify --cert examples/certs/grover_pred_037 --artifact hw/artifacts/grover_pred_037_tree_mbu__fake_torino --target hw/targets/fake_torino.json --ff-latency 1000
lake exe cqr hw noisecert --cert examples/certs/hw_n2 --artifact hw/artifacts/hw_n2_tree_mbu__fake_torino --target hw/targets/fake_torino.json --ff-latency 1000
lake env lean examples/certs/grover_pred_037_torino/PhysCert.lean</div>

**What reproduces byte for byte.** Every committed artifact, from its recorded seed with the pinned Qiskit versions, and every certificate directory, by regeneration.

**What does not.** Kernel times and memory, which depend on the machine and its load.

**Where each number comes from.**

| Number | Source | Measured at |
|---|---|---|
| grades, `GradeExt`, ε, δ | `certificate.json` of each certificate (regenerated in CI) | generation stage; re-checked byte for byte in every CI run |
| kernel times, wall times and peak memory of every Lean check file (Tables 5, 8; Section 9.2) | `kernel_check` field of each `certificate.json`; `docs/BENCHMARKS.md`; the state files of `scripts/bench_all.py` | one run at commit `2025ed2` (R11) |
| noise bounds δ′, emulator counts | `manifest.json`, `docs/hw_runs/*.json` | Stages 25b, 27b, 27c |
| frontier | `docs/hw_frontier/frontier.json` | Stage 27c |
| code size, commits | `wc`, `git log` at main `a2e1b6e` | Stage 30 |
| R1, R2, R15 theorems and the `clbitMap` check | commits `6c66a87`, `040e967`, `8dfced6` | revision task A, CI 26 PASS |
| the paper's statements checked; `hashes.library`; manifests with the run protocol and all premises | commits `f648115`, `d51a975`, `ba15d9c` | revision task B, CI 26 PASS |
| `addchk3`, `wt8_3`, `wt8_3_count`; the comparator's memory | commit `ec06b84`; `docs/DECISIONS.md` (R12) | revision task C, single runs |
| one measurement of all 40 Lean check files; `kernel_check` records its commit | commits `e509fef`, `2025ed2` (driver, measured), `b27dd45` (recorded) | revision task D, CI 26 PASS |

**At one commit (R11).** Every Lean check file was measured in one run at commit `2025ed2` (`scripts/bench_all.py`, resumable, one Lean process at a time, with memory and time guards), with the machine, the toolchain, the free memory and a load sample recorded per file; `docs/BENCHMARKS.md` lists the results. Each logical certificate's `kernel_check` names that commit. Each certificate records the library hash it was checked against (`hashes.library`).

## Appendix C — Specification errata

**The two rules.** The specification document [Zambak 2026b] was written before any of its numbers were measured or its lemmas mechanized. Two rules held from the first stage:
1. **The report is the source of truth.** A disagreement between code and report is reported, not silently resolved.
2. **A certified grade is the measured grade** of a synthesized circuit, never a number copied from the report.

### C.1 Phase 1: sixteen recorded discrepancies

Sixteen discrepancies were found in Stages 0–13, each with a dated entry in the decision log. Report v3 carries them as tracked changes and an errata appendix. Table 10 paraphrases the claims; the report's revisions v2 and v3 are in the repository. Nine items, in seven groups (1, 2, 3–4, 5, 8–9, 12, 16), are substantive (∗).

<p class="caption"><b>Table 10.</b> Specification claims corrected or qualified by the implementation.</p>

| # | Report claim | Measured or proved |
|---|---|---|
| 1∗ | Grover oracle depth 21 | 27: 11 of the 13 compute gates of a temporary AND act on its target, so one compute phase needs 11 layers |
| 2∗ | the MBU listing restores the target by a "reset" | the listing has no reset; a classically controlled X is added (Clifford, 0 T) |
| 3∗ | Bennett table: an a<sub>max</sub> = 2 row for an 8-AND chain | infeasible: with p pebbles the farthest reachable node is 2<sup>p</sup> − 1 |
| 4∗ | Bennett table: an a<sub>max</sub> = 1 row for the same chain | infeasible, for the same reason |
| 5∗ | a<sub>max</sub> = 4: depth ×2 | ×1.45 (144 vs. 99 layers), T = 48 |
| 6 | complexity tuple (8, 2, 3) | (8, 2, 2): the AND-depth is 2 |
| 7 | one metavariable F<sub>1</sub> for arity and iteration bound | distinct F<sub>1</sub>, F<sub>3</sub>; a separate namespace for lgg variables |
| 8∗ | diffusion D<sub>8</sub> = (10, 16, 28, 2) | (15, 89, 28, 7) chain; (15, 41, 28, 7) tree |
| 9∗ | Grover slice (10, 74, 72, 2) | (15, 230, 72, 7) chain, (15, 134, 72, 7) tree; t agrees |
| 10 | kernel check ≈ 0.3 s | 7.2 s at Stage 9; 12.0 s (median of 5, commit `2025ed2`), with the front end, `GradeExt` and the count check |
| 11 | Theorem 3.3a "applies at the terminal measurement" | the terminal measurement is the decoding POVM of realization; no composition step |
| 12∗ | well-formedness of synthesized circuits without hypothesis | false for ill-formed networks; requires `Network.WF` |
| 13 | signature `delta_bound = 1/8` | M/N = sin<sup>2</sup>θ = 1/8; the certified δ is 7/128 |
| 14 | "the verified emitter" | unverified, a declared trust boundary, translation-validated |
| 15 | kernel check ≈ 0.3 s for the second predicate | 6.4 s at Stage 9; 12.1 s (median of 5, commit `2025ed2`) |
| 16∗ | two-ancilla diffusion at 28 T, 16 layers | partially confirmed: w = 10, a = 2 certified for every n; t = 40, d = 60; 40 T optimal within the family (Theorem 5.20) |

**Categories.**
- **Arithmetic carried forward from an unmeasured base** (1, 8, 9).
- **Constructions stated without being built** (2–5, 16).
- **Hypotheses left implicit** (12, and the hypotheses of Theorem 3.3a, made explicit in Theorem 3.4).
- **Wording that overstated assurance** (10, 11, 14, 15).

### C.2 Phase 2: departures and task-text corrections

**Deliberate departures**, each recorded with its reason:
1. Amplitude estimation instead of amplification as the second pattern (Section 6.3).
2. The kernel ceiling attributed to `grade_eq` rather than `emitted_ok`; certificates beyond it use the compositional form.
3. The hardware bound δ<sub>hw</sub> ≤ δ + G·p̄ replaced by a theorem with named premises (Section 8).

**False statements in the task texts.** The task texts of Phase 2 were written by the reviewer session from the specification. The implementer refuted eight statements in them, almost always with a counterexample, and the corrected forms were proved:

| Stage | False statement in the task text | Correction |
|---|---|---|
| 21a1 | a search request's nearest miss is Grover | nearest among entries of the same root shape |
| 22c | the MBU boundary with a fixed classical bit | the bit is existential (Theorem 5.11) |
| 23c | candidate B attains 8n − 24 for n = 4, …, 12 | 8n − 20 at n = 4, 5 (Theorem 5.21) |
| 26a | `decomp_sound` with the table's phase | false for H; `irPhase` (Theorem 7.1) |
| 26b1 | translation preserves the ancilla count | counterexample ⟨1, [alloc (anc 3)]⟩; needs `ancCovered` |
| 26b3 | the layout check implies that block SWAPs collapse | (0 1)(1 2)(2 0); two checks added (Section 7.4) |
| 26c2 | durations convert exactly to an integer unit | dt = 2/9 ns, 119.999…99 ns; exact rationals |
| 27b | the noise premise per IR gate | sx is three IR steps; per basis operation |

**What survived.** The framework's central claims:
- realization and restoration can be stated on CPTP maps and proved for a non-trivial synthesizer with non-unitary uncomputation;
- per-request certification reduces to specialization and a kernel check;
- matching is decidable, and complete on its fragment for signature match;
- the Grover slice has the exact success probability 121/128 and the T-count 72 the report predicts.

**What changed.** The grade is worse in depth and width than claimed. The two-ancilla variant rests on firmer ground than the report gave it. The hardware story is both stronger (a proved transfer to the routed circuit) and more sober (bounds non-vacuous only up to three data qubits on the shipped snapshots).

## Appendix D — Development methodology

**The process.** The system was built in Stage 0 and thirty further stages, subdivided into tasks, over 27 calendar days and 171 commits. An AI coding assistant (Claude Code) implemented each task in a terminal session on the repository, from a written task specification. A second session of the same assistant acted as reviewer. For each task it:
- drafted the task specification;
- audited the result and ran the local continuous integration;
- recorded its decisions.

**What this is not.** It is not a controlled experiment and not evidence about productivity. The reviewer session is not independent of the implementer (Section 11).

### D.1 Rules

The rules read at the start of every implementation session:
1. Every change builds, and the build log tail is part of the report.
2. No library lemma name is used before it is confirmed to exist (`#check`, `exact?`); a missing lemma is reported as an obligation, not guessed.
3. `sorry` is allowed only as a tracked obligation, each with a ledger entry (file and line, statement, report section, dependencies, size). The build must be warning-free except for listed sorries.
4. No toolchain or dependency bump without explicit instruction.
5. Report section names and identifiers are kept, and cited in doc comments and commit messages.
6. Every design decision gets a dated entry in a decision log: what, why, and which alternative was rejected.
7. One task is one buildable commit; the next task is never started on the assistant's own initiative.
8. Theorems are stated as in the report first, with any hypotheses the formalization needs made explicit.
9. Every synthesized circuit passes the independent statevector harness before any grade is claimed.
10. Nothing is called "verified" unless the proof term is sorry-free and axiom-audited.

**Task specifications.** Each named the report sections and the starting commit, the reviewer's decisions, a proof plan marked "verify every step, do not trust it", acceptance criteria, and *guards*. A guard is a condition under which the implementer must stop and report rather than improvise. In Phase 2 the guards were:
- a task above about 1 200 lines, or a single proof above about 500 lines;
- a missing hypothesis;
- an exceeded kernel budget;
- an existing statement that would have to change.

Every task ended with a fixed-format report of at most 40 lines.

### D.2 What the discipline caught

**Guards were triggered, and were useful.** Several tasks stopped at their guard and were split (26b into three parts, 26c1, 26c2 and 27b into two each). Each split ended with a committed, accepted part and a re-specified remainder, never with a half-finished proof. In Phase 1, Stage 12a stopped because making the tree diffusion the default would have changed existing theorem statements; the old statements were kept under a `_chain` suffix.

**Errors were caught in both directions.**
- *The implementer caught the reviewer's errors*, each time by trying to state or prove the theorem: the eight task-text corrections of Appendix C.2, and in Phase 1 a library name absent at the pinned version, a non-expansiveness hypothesis quantified over all points instead of the domain, and a well-formedness theorem without its hypothesis.
- *The reviewer caught the implementer's errors*: stray scratch files, stale status texts, a flaky comparison of machine-dependent fields, and a schema that rejected a field a task had added. The last was found by running the whole CI step, not only the tool.
- *The final review* caught a misreported proof status in the release report (KG Theorem 5.1 described as per-instance although Stage 13a proved it for every n) and a citation whose author list had been written from memory.

**Estimates were optimistic.** Proof-size estimates were consistently low: 150 lines estimated against 394 for synthesis success; 600 against 1 462 for the every-n two-ancilla diffusion. Every stage had a fallback that would have narrowed the obligation instead of leaving a `sorry`; none had to be used, and the obligation ledger closed every entry it ever held.

**The kernel became the measure of cost.** In Phase 2 the recurring cost was kernel evaluation, not proof search: an `Array.push` chain, the quadratic witness check, a per-element list index, and `List.mergeSort`, which the kernel does not evaluate. Each was found by measuring the kernel, and each fix was a proved equivalence, never a weaker check.

### D.3 What the discipline does not cover

The kernel check and the axiom audit make the theorems independent of the assistants' account of them. Nothing makes the *definitions*, the interpretation of the numbers, the positioning against related work or the prose independent of them. This is why a human audit is recommended (R14). Continuous integration was kept local by the author's decision; a workflow kept in sync with the local script is in the repository but has not run on a hosted runner.

## Appendix E — The stages

Stage 0 and thirty further stages (31 in all). Stage 28 was not run by the author's decision; Stage 29 was replaced by a literature note.

| Stage | Content |
|---|---|
| 0 | repository, pinned toolchain, Physlib, CI design |
| 1–2 | grades and budgets; specifications, realization, statements of Theorems 3.1, 3.3a/b |
| 3–4 | DSL, parser, surface checker, extractor; Miller matcher, lgg repair hints |
| 5, 5b | networks, oracle synthesis, Bennett pebbling, scheduler; diffusion and Grover circuits |
| 6, 6b-1..3 | IR semantics, MBU on density operators, restoration template, Lemma 6.3.2 |
| 7a–7b | Grover parametric lemma, exact δ, the instance |
| 8a–8b | SHA3 in Lean, certificate schema, QIR / OpenQASM emitters, `cqr certify` |
| 9a–9b | Lemma 6.3.2 with XOR; front-end validation; second predicate (RevLib ALU); milestone M2 |
| 10a–10b | Theorem 3.3a (general ε), Theorem 3.3b (abstract distance) |
| 11a–11b | well-formedness of synthesized circuits; hardware profiles |
| 12a–12d | balanced-tree diffusion; few-ancilla survey; candidate B; certificates |
| 13a–13c | KG Theorem 5.1 for every n; diamond distance and Theorem 3.3b; synthesis succeeds |
| 14a–14c | solution count decided by the kernel; kernel-time scaling; count limit |
| 15a–15b | coherent uncomputation mode; the abstract-oracle Grover lemma; coherent certificates |
| 16a–16b | the front end proved; `front_end` in every certificate |
| 17a–17b | exact phase gates p, cp; `GradeExt`; emitters |
| 18a–18c | the kernel's ceiling re-attributed; QFT on basis states; AQFT in the diamond distance |
| 19a–19c | grade composition; the counting circuit and its restoration; the tensor form |
| 20a–20b | the QPE bound; the amplitude-estimation lemma; the counting certificate |
| 21a1–21b2 | Count entry; matcher completeness; QPLP record; certified selection; M3; measured composition exercised |
| 22a–22c | the general MBU theorem; Clifford ⇔ quadratic; the IR boundary |
| 23a–23c | restoration algebra; three regimes; the 8n − 24 lower bound; M4 |
| 24a–24c | target model; lowering against the harness; table bounds |
| 25a–25b | transpiling with a witness; emulator runs |
| 26a–26c2b | translation soundness; relabeling, SWAPs, reordering; `applyWitness_sound`; linear check; check files; physical certificate; `PhysGrade`; selection |
| 27a–27c | step semantics; `noisy_realization`; conditional certificates; the bound-vacuity frontier |
| 28 | device runs: not run (the author's decision, 2026-11-16) |
| 29 | SQIR / VOQC comparison: not run; a literature note |
| 30a–30b | housekeeping (one schedule, layering check); M5 report, release documentation |

</div>
