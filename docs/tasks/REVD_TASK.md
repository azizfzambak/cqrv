# Revision task D — R11: every measurement at one commit

Written 2026-11-16 by the reviewer session (author's decision of 2026-11-16; `docs/REVIEW_RESPONSE_1.md`
§4, R11). Runs **last**, after tasks B and C are accepted, on branch `rev-d` from `main` at
`5095f3a` (the rev-c review commit). This file goes into the first commit. The items include the
R12 certificates (`addchk3`, `wt8_3`, `wt8_3_count`); the comparator `cmp4` is **not** an item
(its kernel peak is above 8 GB).

**Why.** The paper's timing tables mix measurements from Stages 21a3, 21a4, 21m, 26c1b, 27b and 27c,
each labelled, on one machine whose load varied. The reviewers asked for one measurement of
everything at one commit, with the enabled checks and the machine recorded.

## D1 — the driver (you)

`scripts/bench_all.py`, resumable (one state file per item under `.lake/bench/`, skip what is done),
one Lean process at a time, with a per-process memory kill at about 8 GB and a timeout of 900 s per
run. Items:
- every logical certificate (`examples/certs/*/Cert.lean`): kernel time, median of 5 after one
  warm-up run, as the existing `reference_configuration.kernel_check` records it;
- every hardware check file (`examples/hw_checks/*/Check.lean`), the physical certificate
  (`PhysCert.lean`), the conditional certificates and the selection files: wall time and peak
  memory, median of 3;
- the commit, the CPU, `LEAN_NUM_THREADS`, the toolchain and dependency revisions, the free memory
  at the start of each item, and whether another heavy process was running (a load sample).

Do **not** run the whole driver yourself: the reviewer runs it in a terminal outside the harness
(the reaper kills long background Lean jobs). Run it on two items to show it works.

## D2 — recording (you, after the reviewer's run)

1. The results go into `docs/BENCHMARKS.md` (one table per kind, the commit and the machine at the
   top) and into the `reference_configuration` of each `certificate.json` through the generator,
   not by hand. If the timing fields make re-certification differ byte for byte, they are already
   excluded from the comparison (check); otherwise stop and report.
2. The README tables that quote times (`examples/hw_checks/README.md`, `examples/hw_select/README.md`,
   `hw/README.md`) take the new numbers, with the commit named.

## Guards

Any item over 900 s or 8 GB; any result that differs from the earlier measurement by more than a
factor of three (report it; it may be load); about 400 hand-written lines.

## Acceptance

`lake build` green; the regenerated files differ only in timing fields; the usual report.
