# Few-ancilla multi-controlled Z — literature and measurements (Stage 12b)

Question (report v2 §3.1.4 / Table 3.3, §6.1.4; v3 erratum 8): can D₈ = H X · MCZ₈ · X H be built
with **2 clean ancillae** at **28 T, 16 layers**, as v2 claimed ("relative-phase multi-controlled-Z
decomposition", no source)? MCZ₈ = H-conjugated 7-controlled X. Sources read from this machine
(arXiv full texts, 2026-10-26). T counts for n = 8 data qubits; "pairs cancel" = whether the
relative phases of the construction cancel in a compute–uncompute pair.

| Construction | Ancillae | T-count (general → n = 8) | Depth | Pairs cancel |
|---|---|---|---|---|
| Gidney 2018 TempLogicalAND tree (arXiv:1709.06648; 12a default) | n − 1 clean | 4(n − 1) → **28** | 5 + 12⌈log₂n⌉ → 41 | AND exact; MBU uncompute, 0 T |
| Barenco et al. 1995 (PRA 52, 3457) Lemma 7.2 | m − 2 dirty for ∧ₘ(X) | 4(m − 2) Toffolis | O(n) | yes: "modulo phase shifts" except 4 Toffolis (Cor. 7.4) |
| Barenco et al. 1995 Cor. 7.4 (Lemma 7.2 + 7.3) | 1 dirty | 8(n′ − 5) Toffolis, n′ = n + 1 → 32 Toffolis, ≈ 140 T with Maslov RTOF | O(n) | yes, except 4 exact Toffolis |
| Maslov 2016 (PRA 93, 022311) Prop. 4 | ⌈(N − 3)/2⌉ clean, N = n qubits of TOF_N | 8N − 17 → 47 | O(n) | yes (Props. 1–2) |
| Maslov 2016 Prop. 5 | ⌈(N − 3)/2⌉ dirty | 8N − 16 → 48 | O(n) | yes |
| Gidney 2015 blog, as tabulated in KG Table 1 | 1 clean / 1 dirty | 24n / 32n | O(n) | — |
| **Khattar–Gidney 2025** (Quantum 9, 1752) §5.2 | 1 clean | 8k − 12, k = n − 1 controls → **44** | O(n) | AND by MBU; Toffolis in pairs |
| **Khattar–Gidney 2025** §5.3 | 2 clean | 8k − 12 (→ 40 here, see below) | O(log n) | as §5.2 |

Implemented (decision 2): KG Problem 1 schedules, each Toffoli on a conditionally clean target as
a relative-phase Toffoli with Maslov's Fig. 3 counts (Margolus-form list: 4 T, self-inverse, = D·Toffoli with
D = diag(1,1,1,1,1,−1,−i,i)), the first operation as Gidney's AND on `anc[0]`. **A = `few:ladder`**
(KG §5.2 greedy): 1 AND + (n − 3) RTOF pairs, T = 8n − 20. **B = `few:log`** (KG §5.3 doubling,
then the §5.2 greedy on the rest, then §5.2 over `anc[1]`): 2 ANDs + (n − 4) pairs, T = 8n − 24.

## Measured (decision-4 scheduler; harness: every branch, n = 1..10, negative controls rejected)

| Diffusion | w | d | t | a | Grover r⋆ = 2 (w, d, t, a) | Kyiv depth (≤ 200) |
|---|---|---|---|---|---|---|
| V1 chain | 15 | 89 | 28 | 7 | (15, 230, 72, 7) | exceeds |
| V1 tree (12a) | 15 | 41 | 28 | 7 | (15, 134, 72, 7) | fits |
| A: KG §5.2 + RTOF, 1 clean | 9 | 93 | 44 | 1 | (10, 238, 104, 2) | exceeds |
| B: KG §5.3 + RTOF, 2 clean | 10 | 60 | 40 | 2 | (10, 172, 96, 2) | fits |

The Grover a = 2 comes from the oracle of grover_pred_037, (10, 27, 8, 2).

## The v2 claim (10, 16, 28, 2) is not reached by any surveyed construction

* An MCZₙ needs n − 2 conjunctions before the final CZ. One on a **clean** target costs 4 T
  (AND; MBU uncompute, 0 T); with 2 clean ancillae at most 2 operations target clean qubits in KG
  Problem 1 (and a pebbled AND chain reaches only 3 nodes, Stage 5b). Every other conjunction
  targets a conditionally clean or dirty qubit and must be uncomputed coherently: 2 × 4 T at best
  (Maslov's 4-T lower bound per relative-phase Toffoli, which he states conditionally). So this
  family needs at least 4·2 + 8(n − 4) = 8n − 24 = **40** T for n = 8 (> 28); B attains it.
* d = 16: one AND compute phase alone takes 11 layers on its target (Stage 5 erratum); B measures
  58 for the bare MCZ₈, A 91.
* w = 10, a = 2: reached by B (and w = 9, a = 1 by A); only the t and d components of the v2
  claim are unreachable with these constructions. This is a statement about the surveyed
  constructions, not a lower-bound theorem.
* Stage 23c: the counting is now a theorem under the stated cost model — `problem1_T_lower_bound`
  (`CQRV/Synthesis/Problem1.lean`: 4 T per conjunction on a fresh clean target, 8 T per other
  conjunction, at most two live values at the end) gives 8n − 24 for every valid Problem 1 schedule
  with two clean indices, and candidate B attains it for n = 6 … 12 (`planB_cost`, `planB_tCount`;
  at n = 4, 5 it costs 8n − 20). It is still not a lower bound on the T-count of all circuits.

## Stage 12c — candidate B proved for n = 8

`CQRV/Grover/MczFew.lean`: `mczFew_ancRestore_8` (`mczFew 8 .logDepth` restores `anc[0]`, `anc[1]`
and applies the phase oracle of x₀ ∧ … ∧ x₇, on density operators) and `diffusionFew_ancRestore_8`
(the `few:log` diffusion applies 2|s⟩⟨s| − I). The relative phases cancel pair by pair for every
target value: D(x, y, z ⊕ xy) · D(x, y, z) = 1 (`rtofPhase_pair`), so the cancellation needs no
"conditionally clean" hypothesis. KG correctness is proved for n = 8 by `decide +kernel` (both
variants); all n is a planned SORRIES.md row. `cqr certify` still uses the tree (Stage 12d).

## Stage 12d — candidate B certified per instance

`cqr certify <file> --shape few:log` certifies the Grover circuit with the B diffusion
(`groverCircuitFew … .logDepth`) through `grover_parametric_lemma_diff`; the restoration of
`mczFew n .logDepth` is `mczFew_ancRestore_of_classical` (general n) with the classical KG fact
as a hypothesis, which each certificate proves for its own n by `decide +kernel` on `fewCheck`
(2ⁿ inputs). Kernel time of that step: n = 8: 1.53 s, n = 10: 8.13 s, n = 12: 40.9 s.
grover_pred_037 (`examples/certs/grover_pred_037_few/`): `certified (conditional on:
solution_count = 32)`, grade (10, 172, 96, 2), Kyiv fits all budgets (d = 172 ≤ 200), δ_hw =
2467/640 (vacuous); kernel check 6.76 s kernel / 16.37 s wall (median of 5). The tree stays the
default of `cqr certify` / `cqr emit`. Status labels: `few:log` "restoration proved (Stage 12c);
certified per instance via `cqr certify --shape few:log` (Stage 12d)"; `few:ladder` "classical
step checked at n = 8, restoration not certified".
