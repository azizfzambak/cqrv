# Kernel times of the committed certificates (Stage 14b)

Report §9.5.1; the `scripts/bench_kernel.sh` protocol applied by `scripts/bench_scaling.py committed`: 6 interleaved runs of `lean -Dprofiler=true Cert.lean` per certificate (round-major order), the first run excluded; kernel time = the profiler's `type checking`. Generated from `bench/scaling/out/state.json`; no hand-edited number.

Machine: 13th Gen Intel(R) Core(TM) i9-13900H; 20 logical CPUs; 2600 MHz; RAM 16108 MB; Microsoft Windows 11 Home Single Language 10.0.26200; `LEAN_NUM_THREADS=4` (recorded by the certify phase); toolchain leanprover/lean4:v4.35.0, Mathlib 56a005855ea1, Physlib 96a6bc5e3c50.

| certificate | runs (all samples, s; first excluded) | min | median | wall median | peak MB | outcome | 14a median (certificate.json) |
|---|---|---|---|---|---|---|---|
| examples/certs/grover_pred_037 | 7.94 8.04 7.98 8.02 7.98 8.03 | 7.98 s | 8.02 s | 16.86 s | 4023 | certified | 12.30 s |
| examples/certs/simple_alu_x0_1 | 8.83 8.89 8.88 8.90 8.96 8.89 | 8.88 s | 8.89 s | 17.78 s | 3559 | certified | 11.10 s |
| examples/certs/grover_pred_037_few | 6.75 6.80 6.79 6.77 6.81 6.80 | 6.77 s | 6.80 s | 15.59 s | 3706 | certified | 6.72 s |

The `reference_configuration.kernel_check` recorded inside each certificate.json is the median of 5 of its own `cqr certify --bench 5` run (Stage 14a regeneration); the table above is an independent measurement with the same protocol. This run's samples are unimodal (every spread max/min below 1.3; SCALING.md, *Modality of the samples*); the 14a samples were bimodal (DECISIONS.md 2026-10-29). grover_pred_037: 14a median / this median = 1.53 (the 14a median came from the mixed regime); simple_alu_x0_1: 14a median / this median = 1.25 (the 14a median came from the mixed regime); grover_pred_037_few: 14a median / this median = 0.99 (both in the fast regime).
