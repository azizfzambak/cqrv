module

public import CQRV.Grades.Order
public import CQRV.Realizability.Spec
public import QuantumInfo.Measurements.POVM

/-!
# CQRV.Realizability.Realizes

Report §2.1.2 (Definition 2.2) and §2.3.1 (Definition 3.2) — (ε,δ)-realization of a classical
specification by a graded quantum channel, read through a decoding POVM.

Channels are Physlib `CPTPMap`s, states `MState`s, decodings `POVM`s (docs/DECISIONS.md,
2026-10-21: Physlib builds, so no channel type of our own).
-/

@[expose] public section

noncomputable section

namespace CQRV

/-- Report §2.1.2 — the probability `Pr_{y ∼ p}[E y]` of an event under a finite distribution.
Physlib's `ProbDistribution` has no event probability, so it is defined here as
`∑ y, [E y] · p y`; decidability of the event is classical. -/
def prob {Y : Type} [Fintype Y] (p : ProbDistribution Y) (E : Y → Prop) : ℝ :=
  open Classical in ∑ y, if E y then (p y : ℝ) else 0

/-- Report §2.1.2 — classical inputs are encoded in the computational basis of the Hilbert
space indexed by the input type itself: `x ↦ |x⟩⟨x|`. The encoding is fixed, not a parameter;
this is what makes the measured interface of Theorem 3.3a exactly `POVM.measureDiscard`
(docs/DECISIONS.md, 2026-10-23). -/
def encode {X : Type} [Fintype X] [DecidableEq X] (x : X) : MState X :=
  MState.ofClassical (ProbDistribution.constant x)

/-- Report §2.3.1, Definition 3.2 — a graded channel: a CPTP map from the encoded input space
`X` to the output space `dY`, together with its resource grade.

Trust gap: in Stage 2 the grade is *declared data*, not computed. It is derived from a
circuit (and checked against the channel) only from Stage 5/6 on. -/
structure GradedChannel (X dY : Type) [Fintype X] [DecidableEq X] [Fintype dY] where
  /-- The channel `Φ : 𝓓(ℋ_X) → 𝓓(ℋ_dY)` (§2.1.2). -/
  chan : CPTPMap X dY
  /-- The declared resource grade (§2.3.1, §3.1.1). -/
  grade : Grade

/-- Report §2.1.2, Definition 2.2 — the channel after the ancilla register `A` is traced out.
Definition 2.2 constrains this reduced channel; that the ancillae come back clean is the
separate obligation `AncRestore` (Stage 6, §6.2). The grade is unchanged. -/
def GradedChannel.traceAnc {X dY A : Type} [Fintype X] [DecidableEq X] [Fintype dY]
    [DecidableEq dY] [Fintype A] [DecidableEq A] (Φ : GradedChannel X (dY × A)) :
    GradedChannel X dY :=
  ⟨CPTPMap.traceRight ∘ₘ Φ.chan, Φ.grade⟩

/-- Report §2.1.2 (Definition 2.2) and §2.3.1 (Definition 3.2) — `Φ` (ε,δ)-realizes `S`
within grade `r` under the decoding `dec`: the grade lies in the fibre over `r`
(`Φ.grade ≤ r`, §3.1.2), and on every input in the domain, decoding the output yields an
ε-acceptable answer with probability at least `1 − δ`. -/
def Realizes {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype dY] [DecidableEq dY] [PseudoMetricSpace Y]
    (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (ε δ : ℝ) (r : Grade) : Prop :=
  Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S.relax ε x)

/-- Report §2.1.2 (Definition 2.2, discrete case ε = 0) and §2.3.1 — `Φ` (0,δ)-realizes `S`
within grade `r`: decoding yields an `S`-acceptable answer (no relaxation) with probability at
least `1 − δ`. Needs no metric on `Y`, so it applies to outputs such as `Fin (2^n)` that have
no `MetricSpace` instance (docs/DECISIONS.md, 2026-10-23). -/
def RealizesExact {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype dY] [DecidableEq dY]
    (S : Spec X Y) (dec : POVM Y dY) (Φ : GradedChannel X dY) (δ : ℝ) (r : Grade) : Prop :=
  Φ.grade ≤ r ∧ ∀ x ∈ S.dom, 1 - δ ≤ prob (dec.measure (Φ.chan (encode x))) (S x)

/-- Report §2.1.2 — on a metric output space, (0,δ)-realization is `RealizesExact`
(`S^0 = S`, `Spec.relax_zero`). -/
theorem realizes_zero_iff {X Y dY : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype dY] [DecidableEq dY] [MetricSpace Y]
    {S : Spec X Y} {dec : POVM Y dY} {Φ : GradedChannel X dY} {δ : ℝ} {r : Grade} :
    Realizes S dec Φ 0 δ r ↔ RealizesExact S dec Φ δ r := by
  rw [Realizes, RealizesExact, Spec.relax_zero]

end CQRV

end

end
