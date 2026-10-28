# Stage 13a′ — `cqr certify --shape few:log` without the 2ⁿ classical check

Report sections: §5.1.3 (per-request work is specialization + kernel check), §8.4 (certificate),
§8.2, §6.2, §9.5.1 (certified only if sorry-free and axiom-audited).
Precondition: main = 238cf09 (Stage 13a). `git switch -c stage-13a2 main`; one commit; include
this file (untracked). Windows: `LEAN_NUM_THREADS=4`; Python `.venv`. Repository stays sorry-free.

## Why

Stage 12d certificates prove the KG classical step for their own `n` by `decide +kernel` over
`2ⁿ` inputs (`fewCheck`; kernel 1.53 s / 8.13 s / 40.9 s at n = 8 / 10 / 12). Stage 13a proved it
for every `n` (`mczFew_logDepth_ancRestore`, `diffusionFew_logDepth_ancRestore`,
`mczFew_logDepth_WF`, `CQRV/Grover/MczFewAll.lean`). A few:log certificate should now cite the
general theorem and check only what is specific to the request.

## Reviewer decisions (record in DECISIONS.md)

1. **New specialization theorem, old one kept.** Add `grover_certificate_few_all`
   (`CQRV/Certify/Specialize.lean`, new name) with the conclusion of `grover_certificate_few` and
   only the request-specific hypotheses: `O`, `hM_pos`, `hD : diffusionFew n .logDepth = .ok Dc`,
   `hC`, `hδ`, `hg`, `ha`, `hM_card`. No `hWF`, `hnb`, `hchk`, `ha₀`; derive `Dc.WF` (or its
   `bitsOk`) for every `n` from 13a (`mczFew_logDepth_WF` and the diffusion wrapper) — if that
   needs a small new lemma, add it; if it cannot be closed, keep `hDWF` as a hypothesis checked by
   `decide +kernel` and say so. `grover_certificate_few` and every existing statement stay unchanged.
2. **Generator.** For `--shape few:log`, `renderCertFew` emits a `Cert.lean` without
   `classical_step`, `mcz_WF`, `mcz_nBits`, `mcz_nAnc` (whatever 1 makes unnecessary) and applies
   `grover_certificate_few_all`. The doc comment says: "KG Theorem 5.1 for every n
   (`mczFew_logDepth_ancRestore`, Stage 13a); no per-instance classical check". Never `native_decide`.
3. **Labels.** `MczVariant.status` for `logDepth`: "restoration proved for every n (Stage 13a);
   certified via `cqr certify --shape few:log`". `ladder` unchanged. Update the docstrings in
   `CQRV/Synthesis/MczFew.lean` that mention the per-instance check. If the label appears in a
   golden file, regenerate it and list the file.
4. **Schema.** If a `certificate.json` / `run_report` field describes the classical step, change it
   with a minor schema bump; otherwise no bump. Tree certificates stay byte-identical.
5. **Regenerate deliberately** `examples/certs/grover_pred_037_few/` (`cqr certify
   examples/grover_pred_037.cqr --shape few:log --profile ibm_kyiv`); record old → new Cert.lean
   hash and kernel time in DECISIONS.md. Grade (10, 172, 96, 2), δ, circuit hash, QIR, QASM must
   be unchanged — only the proof text and timing move.

## Tasks

1. Decisions 1–5.
2. `check_certify.sh` / `tests/diff/certify_check.py`: the few:log checks follow the new Cert.lean
   (no `fewCheck`, applies `grover_certificate_few_all`). The negative test "classical step for
   n = 7" no longer applies: replace it by "the committed few Cert.lean with `mcz_ok` (or `diff_ok`)
   stated for n = 7 → kernel check fails".
3. Measure the kernel time of a few:log certificate at n = 8, 10, 12 (old vs new table).

## Acceptance

- `lake build` green, sorry-free; guarded `#print axioms` for `grover_certificate_few_all` and the
  regenerated certificate: standard three.
- `scripts/ci_local.sh` all PASS (or `check_certify.sh` alone if step 19 runs out of memory).
- Tree certificates byte-identical; the few certificate `certified (conditional on:
  solution_count = 32)`, same grade and hashes of the emitted artifacts, Kyiv fits.

## Stop conditions

- Grade, circuit hash, QIR or QASM of the few certificate would change → stop.
- Any existing statement would have to change → stop and propose.

## Closing reply

CLAUDE.md format, under 40 lines; in (e): the kernel-time table (old / new, n = 8, 10, 12), the
Cert.lean old → new hash, whether `hDWF` stayed a hypothesis, and any schema bump.
