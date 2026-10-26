# Stage 12b (improvement 3, part 2) — 2-ancilla multi-controlled Z: construction and measurement

Report sections: §3.1.4 / Table 3.3 and §6.1.4 (v2 claim: D₈ with "a multi-controlled Z gate
decomposed with 2 clean ancilla … 28 T-gates, 16 layers", via "the relative-phase multi-controlled-Z
decomposition"; v3 erratum 8: not reproduced), §6.2 (restoration is a co-equal obligation),
§9.5.2 (loose-but-proved: an unproved construction is never certified).
Precondition: Stage 12a accepted. `git switch -c stage-12b main`; one commit; include this file.
Windows: `LEAN_NUM_THREADS=4`; Python `.venv`. **Engineering + literature stage, no proofs**;
the certificate path is **not** changed in this stage (an unproved circuit is never certified).

## Goal

Decide, with measurements, whether an 8-qubit MCZ (the core of D₈) can be built with **2 clean
ancillae** (w = 10 for the Grover slice), at what T-count and depth, and whether it beats the
12a tree on the Kyiv profile. This is the construction the v2 report asserted without a source.

## Reviewer decisions (record in DECISIONS.md)

1. **Literature first, no invention.** Identify published constructions for an n-controlled Z /
   Toffoli with few clean (or dirty) ancillae and T-count linear in n — e.g. relative-phase Toffoli
   ladders (Maslov 2016, "Advantages of using relative-phase Toffoli gates…"), Barenco et al. 1995
   (Lemma 7.2, dirty ancillae), Gidney's constructions for large controlled NOTs, Khattar–Gidney
   conditionally clean ancillae (the report's ref. 18). For each candidate record: citation,
   ancilla count (clean/dirty), T-count, Clifford depth formula, and whether the relative phases
   cancel in a compute–uncompute pair. If no source can be accessed from this machine, stop.
2. **Implement at most two candidates** as gate lists in the existing IR (only gates the IR has;
   no rotations other than T/S), as `mczFew (n) (variant)` in `CQRV/Synthesis/`, building D₈ =
   `H X · MCZ · X H` around them.
3. **The harness decides correctness**: every measurement branch, random complex superpositions,
   exact `(2|s⟩⟨s| − I)` up to global phase, ancillae back to |0⟩ (as in Stage 5b); n = 3..10.
   A relative-phase gadget that is only correct up to a phase on the *ancilla* subspace must still
   leave the data register exact — check it.
4. **No certificate change**: `cqr certify` keeps the 12a tree. The new MCZ is available only via
   `cqr synthesize --diffusion n --shape few:<variant>` and is labelled "unproved" in all output.

## Tasks

1. Literature table (decision 1) in DECISIONS.md and `docs/MCZ_NOTES.md` (≤ 1 page).
2. Implementation (decision 2) and harness (decision 3).
3. Measured comparison for n = 8, and the Grover slice with each MCZ, against Kyiv:

| Diffusion | w | d | t | a | Grover r⋆ = 2 (w, d, t, a) | Kyiv depth |
|---|---|---|---|---|---|---|
| V1 chain | 15 | 89 | 28 | 7 | (15, 230, 72, 7) | exceeds |
| V1 tree (12a) | | | | | | |
| 2-ancilla candidate A | | | | | | |
| 2-ancilla candidate B | | | | | | |

4. A recommendation: is a 2-ancilla MCZ worth a restoration proof (stage 12c)? Which one, and what
   proof shape would it need (MBU does not apply directly to a relative-phase gadget — say what does)?

## Acceptance

- `lake build` green, sorry-free, harness passes for the implemented candidates (or the failing
  branch is reported and the candidate dropped), `scripts/ci_local.sh` all PASS.
- The table filled with measured values and citations; the v2 claim "(10, 16, 28, 2)" either
  reproduced or shown unreachable by the surveyed constructions — reported as such.

## Stop conditions

- No accessible literature source → stop and report.
- A candidate needs gates the IR lacks (e.g. arbitrary rotations) → note it, do not extend the IR
  in this stage.
- Do not touch the certificate generator or any proof file.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the table, the citations, and the recommendation for 12c.
