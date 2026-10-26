# Stage 12d — Certify Grover with the 2-ancilla diffusion (`cqr certify --shape few:log`)

Report sections: §8.2 (diffusion), §8.2.4 (realization ∧ restoration), §5.1.3 (per-request work
is specialization + kernel check), §8.4 (certificate), §3.1.4 / Table 3.3 (v2's w = 10, a = 2),
§9.5.1 (certified only if sorry-free and axiom-audited).
Precondition: Stage 12c accepted (main = 26e7ca7). `git switch -c stage-12d main`; one
commit; include this file (untracked). Windows: `LEAN_NUM_THREADS=4`; Python `.venv`.
The repository stays sorry-free; **no existing statement changes**; the tree stays the default
everywhere (CLI, generator, committed certificates byte-identical).

## What exists (12c) and what is missing

12c proved the restoration of `mczFew` for general n, variant and ancilla count, **given** the
classical fact "the product of the unmarked qubits after the compute steps equals x₀ ∧ … ∧ xₙ₋₁";
that fact is proved by `decide +kernel` only at n = 8 (`mczFew_logDepth_8_classical`), and
`diffusionFew_ancRestore_8 : AncRestore 8 2 D (diffU 8)`. The Grover lemmas take the diffusion
from the synthesizer (`DiffusionShape` chain | tree, `DiffusionCert`), so B is not yet usable there.

## Reviewer decisions (record in DECISIONS.md)

1. **Classical step per instance.** State `mczFew_ancRestore_of_classical` for general n and variant
   with the classical fact as an explicit hypothesis (if 12c's general claim is not already in this
   shape, add the corollary — do not change 12c statements). The certificate for a request with n
   data qubits proves that hypothesis **for that n** by `decide +kernel` (2ⁿ cases; n ≤ 12 by the
   front-end limit — measure the kernel time at n = 8, 10, 12 and report it). The all-n theorem
   (KG Theorem 5.1) stays a planned row.
2. **Generic Grover lemma over any certified diffusion.** Add (new names only)
   `grover_parametric_lemma_diff`: for an oracle certificate, any diffusion circuit `Dc` with
   `Dc.bitsOk` and `AncRestore n a Dc (diffU n)`, and the Grover circuit built from them, the same
   conclusion as `grover_parametric_lemma` (realization with `δ = 1 − sin²((2r+1)θ)` and the measured
   grade; restoration with `groverOp^r · H^{⊗n}`). Prove it by refactoring the 7a/12a proofs into a
   lemma parameterized by the diffusion's restoration fact; the existing theorems become corollaries
   with unchanged statements.
3. **Circuit construction.** Add a `DiffusionShape.fewLog` (or an equivalent explicit path) so that
   `groverCircuit … .fewLog` builds `oracle ++ diffusionFew n .logDepth` per iteration through the
   same shifted `Circuit.append`; `--shape few:log` in `cqr certify` uses it. Check that the
   harness (`diff_grover`) passes for the B Grover circuit of grover_pred_037 (sampled branches,
   exact success probability 121/128) before claiming a grade.
4. **Generator.** For `--shape few:log` the generated `Cert.lean` contains the `decide +kernel`
   classical step for its n, `diffusionFew n .logDepth = .ok Dc` and `Dc.WF` by `decide +kernel`,
   and applies `grover_parametric_lemma_diff`. Never `native_decide`.
5. **Labels and schema.** `MczVariant.status` and the MczFew docstrings: "restoration proved
   (Stage 12c); certified per instance via `cqr certify --shape few:log` (Stage 12d)" for
   `logDepth`; `ladder` stays "classical step checked at n = 8, restoration not certified".
   Certificate schema minor bump: optional field `diffusion_shape` ("tree" default, omitted ⇒ tree,
   so the committed tree certificates stay byte-identical).

## Tasks

1. Items 1–2 in Lean (`CQRV/Grover/`), guarded `#print axioms`.
2. Items 3–5 (Synthesis, CLI, generator, schema, labels).
3. Commit a third example: `examples/certs/grover_pred_037_few/` from
   `cqr certify examples/grover_pred_037.cqr --shape few:log --profile ibm_kyiv`.
4. `check_certify.sh`: the B certificate is `certified (conditional on: solution_count = 32)`, grade
   (10, 172, 96, 2) (or the measured value — report any difference), Kyiv fits; negative test: a
   `Cert.lean` whose classical step is replaced by a wrong n fails the kernel check.

## Acceptance

- `lake build` green, sorry-free, guarded axioms standard three; `scripts/ci_local.sh` all PASS
  (or `check_certify.sh` alone if step 19 runs out of memory).
- Tree certificates byte-identical; the new B certificate certified with the honest status line.
- Kernel-check times for the B certificate and for the classical step at n = 8, 10, 12 reported.

## Stop conditions

- Any existing theorem statement would have to change → stop and propose.
- The classical step at some n ≤ 12 is false (KG schedule fails) or too slow for the kernel → stop
  and report that n; do not certify it.
- The B Grover circuit fails the harness → stop.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the B status line and Kyiv line, measured grade, kernel
times, and the new theorem names.
