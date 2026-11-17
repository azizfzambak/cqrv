# Benchmarks — every measurement at one commit (revision R11)

REVIEW_RESPONSE_1 §4 R11; docs/tasks/REVD_TASK.md; report §9.5.1, §9.5.3. Both reviews asked for one measurement of everything at one commit, with the machine, the enabled checks and the load recorded, in place of the timing tables mixed from Stages 21a3, 21a4, 21m, 26c1b, 27b and 27c. Written by `scripts/bench_all.py --report` from its state files (`.lake/bench/`, not committed); no hand-edited number.

**Commit** `2025ed24a20247c9a005e697b178188f835f3def`. **Machine** 13th Gen Intel(R) Core(TM) i9-13900H; 20 logical CPUs; 2600 MHz; RAM 16108 MB; Microsoft Windows 11 Home Single Language 10.0.26200; Windows-10-10.0.26200-SP0; `LEAN_NUM_THREADS=4`. **Toolchain** leanprover/lean4:v4.35.0, Mathlib 56a005855ea1, Physlib 96a6bc5e3c50 (`Lean (version 4.35.0, x86_64-w64-windows-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`). **Run** started 2026-11-17 03:04:51, in a terminal outside the agent harness; tracked files modified at the run: none; guards 900 s and 8192 MB per run, none hit.

**Method.** lean -Dprofiler=true <file> as the direct child (LEAN_PATH of `lake env`); kernel time = the profiler's `type checking`; wall = the lean process; peak = PeakWorkingSetSize; logical certificates 1 warm-up + 5 runs (median of 5), hardware files 3 runs (median of 3). The wall is that of `lean` itself, run directly — the earlier figures of `reference_configuration.kernel_check` and of the 2026-11-16 table in `examples/hw_checks/README.md` were walls of `lake env lean`, 1–2 s more (the lake start); the kernel time is the same quantity in both. Peak = the peak working set of the Lean process (the maximum over the runs of an item).

**Load.** 40 of 40 items done; CPU busy at the start of an item 0.8–7.4 %; free physical memory 7232–7746 MB; other lean / lake processes running: 0; flags: none (no run over the guards; no median off its earlier figure by more than a factor of 3).

The logical certificates carry these figures in `reference_configuration.kernel_check` (`cqr certify --kernel-check-from`, with `commit`); the hardware files cite a certificate modulo `hashes.library` and `reference_configuration`, so the measurement moved none of them (DECISIONS.md 2026-11-17, R11 D1.5 and D2).

## Logical certificates (`examples/certs/*/Cert.lean`; 1 warm-up + 5 runs, the median of 5)

| certificate | instance | kernel s | the 5 kernel samples (s) | wall s | peak MB | before: kernel s (`--bench`, `lake env lean`) | ratio |
|---|---|---|---|---|---|---|---|
| `addchk3` | n = 9, M = 64, r = 2 | 44.8 | 46.0 44.8 44.4 44.9 44.4 | 54.4 | 6814 | 45.4 | 1.01 |
| `fr_n2_tree_coherent_rb` | n = 2, M = 1, r = 1 | 0.399 | 0.399 0.39 0.392 0.415 0.403 | 9.54 | 1897 | 0.398 | 1.0 |
| `fr_n3_fewlog_mbu` | n = 3, M = 1, r = 2 | 1.48 | 1.48 1.47 1.5 1.49 1.47 | 10.8 | 2119 | 1.48 | 1.0 |
| `fr_n3_tree_coherent_rb` | n = 3, M = 1, r = 2 | 4.29 | 4.24 4.35 4.29 4.34 4.29 | 13.5 | 2675 | 4.3 | 1.0 |
| `grover_pred_037` | n = 8, M = 32, r = 2 | 12.0 | 11.9 12.2 12.0 12.0 11.7 | 21.3 | 3729 | 12.1 | 1.01 |
| `grover_pred_037_coh` | n = 8, M = 32, r = 2 | 21.0 | 21.0 21.2 21.0 21.0 21.1 | 30.3 | 5419 | 21.3 | 1.01 |
| `grover_pred_037_count` | n = 8, m = 4, M = 32 | 16.9 | 16.7 17.1 16.9 17.1 16.9 | 26.1 | 2592 | 16.9 | 1.0 |
| `grover_pred_037_few` | n = 8, M = 32, r = 2 | 10.3 | 10.3 10.3 10.2 10.2 10.3 | 19.5 | 3543 | 10.3 | 1.0 |
| `grover_pred_037_sel` | n = 8, M = 32, r = 2 | 23.2 | 23.5 23.2 23.4 22.9 22.9 | 32.8 | 4751 | 23.5 | 1.01 |
| `hw_n2` | n = 2, M = 1, r = 1 | 0.274 | 0.275 0.274 0.29 0.268 0.273 | 9.53 | 1867 | 0.277 | 1.01 |
| `hw_n3` | n = 3, M = 1, r = 2 | 2.26 | 2.29 2.3 2.22 2.23 2.26 | 11.5 | 2275 | 2.32 | 1.03 |
| `simple_alu_x0_1` | n = 6, M = 30, r = 1 | 12.1 | 12.1 12.1 12.1 12.3 12.4 | 21.6 | 3353 | 12.1 | 1.0 |
| `wt8_3` | n = 8, M = 56, r = 1 | 38.6 | 38.6 39.8 38.9 37.9 38.2 | 48.4 | 6924 | 39.8 | 1.03 |
| `wt8_3_count` | n = 8, m = 4, M = 56 | 106.0 | 106.0 106.0 107.0 107.0 105.0 | 116.0 | 7011 | 106.0 | 1.0 |

## Hardware check files (`examples/hw_checks/*/Check.lean`; 3 runs, the median of 3)

| file | wall s | peak MB | kernel s | 2026-11-16 table: wall s (`lake env lean`) / peak MB | ratio (wall) |
|---|---|---|---|---|---|
| `fr_n2_tree_coherent_rb__fake_washington` | 9.53 | 1865 | 0.306 | 11.0 / 1946 | 1.15 |
| `fr_n3_fewlog_mbu__fake_torino` | 12.5 | 2193 | 1.9 | 14.0 / 2253 | 1.12 |
| `fr_n3_tree_coherent_rb__fake_torino` | 14.3 | 2380 | 2.61 | 15.0 / 2458 | 1.05 |
| `grover_pred_037_fewlog_mbu__fake_torino` | 21.1 | 3110 | 6.81 | 22.0 / 3174 | 1.05 |
| `grover_pred_037_tree_coherent__fake_torino` | 29.6 | 4073 | 11.7 | 31.0 / 4198 | 1.05 |
| `grover_pred_037_tree_coherent__fake_washington` | 17.6 | 2746 | 5.09 | 19.0 / 2765 | 1.08 |
| `grover_pred_037_tree_mbu__fake_torino` | 29.3 | 4049 | 12.1 | 31.0 / 4096 | 1.06 |
| `hw_n2_tree_mbu__fake_torino` | 10.3 | 1926 | 0.539 | 12.0 / 1946 | 1.17 |
| `hw_n3_tree_mbu__fake_torino` | 13.8 | 2324 | 2.55 | 15.0 / 2355 | 1.09 |
| `mbu_gadget__fake_torino` | 9.53 | 1849 | 0.24 | 11.0 / 1843 | 1.15 |
| `mbu_gadget_wrapped__fake_torino` | 9.78 | 1865 | 0.316 | 11.0 / 1946 | 1.12 |
| `simple_alu_x0_1_fewlog_mbu__fake_torino` | 26.8 | 3658 | 10.3 | 28.0 / 3789 | 1.04 |
| `simple_alu_x0_1_tree_coherent__fake_torino` | 29.1 | 3941 | 11.5 | 31.0 / 3994 | 1.07 |
| `simple_alu_x0_1_tree_coherent__fake_washington` | 17.0 | 2617 | 4.77 | 18.0 / 2662 | 1.06 |
| `simple_alu_x0_1_tree_mbu__fake_torino` | 29.8 | 3959 | 12.4 | 31.0 / 4096 | 1.04 |

## Physical certificates (`examples/certs/*/PhysCert.lean`; 3 runs, the median of 3)

| file | wall s | peak MB | kernel s |
|---|---|---|---|
| `examples/certs/fr_n2_tree_coherent_rb_washington/PhysCert.lean` | 10.8 | 1921 | 1.09 |
| `examples/certs/fr_n3_fewlog_mbu_torino/PhysCert.lean` | 17.3 | 2244 | 6.26 |
| `examples/certs/fr_n3_tree_coherent_rb_torino/PhysCert.lean` | 21.6 | 2679 | 9.78 |
| `examples/certs/grover_pred_037_torino/PhysCert.lean` | 52.9 | 4094 | 35.1 |
| `examples/certs/hw_n2_torino/PhysCert.lean` | 11.5 | 1970 | 1.65 |
| `examples/certs/hw_n3_torino/PhysCert.lean` | 19.6 | 2379 | 8 |

## Conditional (noise) certificate (`NoiseCert.lean`; 3 runs, the median of 3)

| file | wall s | peak MB | kernel s |
|---|---|---|---|
| `examples/certs/mbu_gadget_torino/NoiseCert.lean` | 10.0 | 1877 | 0.391 |

## Selection files (`examples/hw_select/*/Select.lean`; 3 runs, the median of 3)

| file | wall s | peak MB | kernel s |
|---|---|---|---|
| `examples/hw_select/grover_pred_037__fake_torino/Select.lean` | 21.8 | 2664 | 15.4 |
| `examples/hw_select/grover_pred_037__fake_washington/Select.lean` | 7.53 | 1447 | 1.96 |
| `examples/hw_select/simple_alu_x0_1__fake_torino/Select.lean` | 30.8 | 3256 | 24.0 |
| `examples/hw_select/simple_alu_x0_1__fake_washington/Select.lean` | 8.78 | 1590 | 2.49 |

The comparator `cmp4` (REVC_TASK, R12) is not an item: no certificate, its kernel peak is above 8 GB (docs/M5_REPORT.md §1.2, DECISIONS.md 2026-11-17).
