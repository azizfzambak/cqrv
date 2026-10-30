# Stage 14 — solution counts decided by the kernel, an illustrative profile name, kernel-time scaling

Report sections: §5.1.3, §8.2 (M as a parameter of the search problem), §8.4.1, §8.4.4
(certificate, status words, kernel check), §9.5.1 (master discipline). Three tasks, **three
commits**: do **14a**, reply, and stop. Start **14b** only after the reviewer has accepted 14a.
**14c** (added 2026-10-30 after the 14b review) starts only after the 14b review commit.

Precondition: main = `beee551` (Stage 13c review). Windows: `LEAN_NUM_THREADS=4`.
`docs/paper/`, `docs/cqrv_report_revised_v4.docx`, `docs/PHASE2_ROADMAP.md`, `docs/PHASE2_SPEC.md`
and `docs/tasks/STAGE15_TASK.md` are untracked and belong to the reviewer (the last three are
committed with Stage 15a): do not add, modify or commit them.

---

## 14a — `hM_card` decided by the kernel for small n; the profile renamed

`git switch -c stage-14a main`; one commit; include this file (untracked).
**Proof stage** for A1 (3 build–fix rounds); repository stays sorry-free and warning-free.
**No change** to `grover_certificate`, `grover_parametric_lemma_diff`, the synthesizer, the
scheduler, emitted circuits, or any existing theorem statement. New names only.

### A1. Counting by evaluation, proved equal to the Finset count

New file `CQRV/Certify/Count.lean` (or next to `Network.pred`; say where):
- `Network.countSat (N : Network) (n : Nat) : Nat` — counts the inputs `k < 2^n` whose bit vector
  (bit `i` of `k` at index `i`) satisfies `Network.pred N n`. Kernel-friendly: `List.range` /
  `Nat.rec` folds, no `Finset`, no `native_decide`.
- `theorem countSat_eq_card (N : Network) (n : Nat) :
     N.countSat n = (Finset.univ.filter fun x => Network.pred N n x = true).card`
  Route: a bijection between `Fin (2^n)` and `Fin n → Bool`. Look for an existing Mathlib
  equivalence first (`#check`, `exact?`, `apply?` — rule 2; do not guess names); if there is
  none, prove the bit-vector bijection directly and say so.
- `#guard`s: `countSat` of the `grover_pred_037` network at n = 8 is 32; of `simple_alu_x0_1` at
  n = 6 is 30.

### A2. The generator

- New flag `--count-limit k` for `cqr certify` (default **12**; `0` disables). If `n ≤ k`, the
  tool first evaluates `countSat` itself; if it differs from the supplied or extracted `M`, it
  reports the diagnostic `solution_count_mismatch` (supplied M, computed count) and writes **no**
  certificate. Otherwise `Cert.lean` contains
  `theorem hM_count : (Finset.univ.filter fun x => Network.pred net n x = true).card = M`
  (by `countSat_eq_card` and `decide +kernel`), and `theorem cert` takes **no hypothesis**: it is
  `grover_certificate … hM_count`.
- If `n > k`: the current conditional form, unchanged.
- Status word: `certified` when `hM_count` is present; `certified (conditional on:
  solution_count = M)` otherwise. Certificate JSON: record how M was obtained, e.g.
  `"solution_count": {"value": 32, "status": "kernel_decided" | "hypothesis"}`; update
  `docs/certificate.schema.json` and `tests/diff/cert_schema.py`. The run report's trust-boundary
  line for the solution count follows the same two cases.
- The axiom audit is unchanged: exactly `propext`, `Classical.choice`, `Quot.sound`.

### A3. Rename the profile `ibm_kyiv` → `illustrative_sc`

The bundled profile carries the specification's illustrative figures, not calibration data of a
device; its name should not suggest otherwise. Rename the file and its `name` field, and update
every **current** reference: `CQRV/Grades/Profile.lean`, tests (`tests/CQRVTests/*.lean`,
`tests/diff/*.py`), `scripts/*.sh`, `README.md`, `docs/PROJECT_STATUS.md`, `docs/M2_REPORT.md`.
Add to the profile a `note`: "illustrative figures from the specification's example; not
calibration data of any device". **No alias**: `--profile ibm_kyiv` must fail with the existing
unknown-profile diagnostic, which lists the available profiles. Historical records (old entries in
`docs/DECISIONS.md`, old task files) are **not** edited.

### A4. Regenerate the committed certificates

Re-certify the three examples (`grover_pred_037`, `grover_pred_037_few`, `simple_alu_x0_1`) with
the new generator and profile. Expected diffs: `cert` without hypothesis, `hM_count`, status word,
profile name, hashes, machine fields. Golden files of the synthesizer and emitters stay
byte-identical. Measure the kernel-time change caused by `hM_count` on all three
(`scripts/bench_kernel.sh` protocol) and report it in (e).

### Acceptance (14a)

- `lake build` green, sorry-free, warning-free; guarded `#print axioms` for `countSat_eq_card` and
  the three `cert` theorems: the standard three.
- Negative tests (in `scripts/cli_smoke.sh` or `check_certify.sh`; mind the CRLF memory note):
  `grover_pred_037` with `--solutions 31` → `solution_count_mismatch`, no file written;
  `grover_pred_037` with `--count-limit 4` → the conditional form and status;
  `--profile ibm_kyiv` → unknown profile.
- `scripts/ci_local.sh` all PASS, with re-certification byte-identical to the **new** committed
  files.
- `docs/DECISIONS.md`: dated entries for the count route, the default limit 12 and why, the
  rename and the no-alias decision. `docs/PROJECT_STATUS.md` updated (status words, profile name).
  SORRIES.md: no new rows.

### Stop conditions (14a)

- `countSat_eq_card` does not close after 3 build–fix rounds, or needs more than about 250 lines →
  stop, report the remaining goal; do not ship the generator change without the theorem.
- A certificate's median kernel time rises by more than 10 s → stop and report the numbers before
  committing.
- Any existing theorem statement would have to change → stop and propose.

---

## 14b — kernel-time and grade scaling (measurement only)

Start only after 14a is accepted. `git switch -c stage-14b stage-14a`; one commit.
**No change to the Lean library.** Allowed: new scripts, generated DSL sources, docs. The iteration
count is fixed with the existing `cqr certify --iterations r` (the parametric lemma holds for
every r).

### B1. Families

Generator `scripts/gen_scaling.py`, fixed seeds, sources committed under `bench/scaling/`:
- **carry_k**: carry-out of a k-bit ripple-carry adder, n = 2k, k = 1, 2, …, 8 (n ≤ 16).
- **rand_a**: random one-output predicates with AND, XOR, NOT and `if`, n ≤ 12, targeting
  a = 4, 8, 16, 32, 64 AND nodes after synthesis (reuse the generator of the harness's random
  predicates if it fits; say which).
- **alu_bits**: the other output bits of RevLib "Simple ALU" that are expressible in the DSL, if
  the transcription of `simple_alu_x0_1` extends without new constructs; otherwise skip and say so.

For each instance certify with **r = 1** (isolates oracle size) and, where r* ≤ 4, also with r*.
Instances with n ≤ 12 must pass the statevector harness (oracle at least) before their grade is
reported (rule 9). M comes from 14a's count (n ≤ 12) or from harness enumeration (n ≤ 16).

### B2. Measurements

Per instance and r: n, AND / XOR node counts, oracle grade, full grade, emitted instruction count,
G, kernel time **min and median** over 6 interleaved runs with the first excluded (the
`bench_kernel.sh` protocol), wall time, peak memory if it can be measured without new
dependencies, and outcome (`certified`, `timeout` at 900 s, `oom`, `error`). Apply the same
protocol to the three committed certificates and report all samples, min and median.

Outputs: `docs/benchmarks/SCALING.md` (method: machine, OS, `LEAN_NUM_THREADS`, protocol; tables;
the smallest instance per family whose kernel check exceeds 300 s or fails),
`docs/benchmarks/scaling.csv`, and `docs/benchmarks/KERNEL_TIMES.md` for the committed
certificates. Benchmark outputs (certificates, logs) go to a gitignored directory, not committed.

### Acceptance (14b)

- Build unchanged and green; `scripts/ci_local.sh` all PASS.
- The tables are generated by the script from raw results (no hand-edited numbers); the raw CSV
  is committed.
- DECISIONS.md entry: families, sizes, timeouts, and anything skipped.

### Stop conditions (14b)

- An instance fails for a reason other than time or memory (synthesis error, kernel-check failure,
  harness mismatch, count mismatch) → stop and report it as a bug with the instance; do not fix it
  in this stage.
- The projected total benchmark time exceeds 6 h → stop after the first two sizes per family and
  report the projection.

---

## 14c — the count-limit default and the stack experiment (small; one commit)

Start only after 14b is accepted and main is fast-forwarded to the 14b review commit.
`git switch -c stage-14c main`; one commit; include this file. C1 is a small code change, C2 is
measurement only. Long Lean runs (the C2 phase, `ci_local.sh`) are run by the user in a separate
terminal, one Lean process at a time: you prepare the exact command lines and stop.

### C1. Default `--count-limit` 12 → 10

14b measured: every n = 12 kernel-decided certificate timed out at 900 s; the largest that
finished is carry_5 (n = 10, 103 s median, 11 371 MB peak on a 16 108 MB machine). Set
`defaultCountLimit` in `Apps/cqr/Main.lean` to **10**; `--count-limit k` keeps its meaning (`0`
disables). Update every **current** mention of the default: the doc-comments and usage text of
`Main.lean`, `README.md` ("n ≤ 12"), `docs/PROJECT_STATUS.md` (status words, trust-boundary
line, and the §4 open-item row, which this closes), the comments of `tests/diff/certify_check.py`
and `scripts/check_certify.sh`. Historical records (DECISIONS.md entries, the 14a/14b text above,
SCALING.md) are **not** edited. The committed certificates (n = 8, 8, 6) are unchanged:
`check_certify.sh` must still find them byte-identical outside the machine fields. New test in
`certify_check.py`, item (f′): a tiny n = 11 predicate written by the test to a temporary file
(e.g. `x0 ∧ x10`), certified **without** the flag → `certified (conditional on: solution_count =
M)`, `Cert.lean` with `hM_card`, `solution_count.status = hypothesis`. The kernel-decided form at
n = 11 is **not** run (that cost is what 14b measured). Budget for the new test: under 60 s.

### C2. Stack experiment on the deep-recursion ceiling (measurement only)

14b: `rand_a64_r1_h` (1953 emitted instructions) fails in the kernel with `deep recursion
detected` inside `emitted_ok` after 29.6 s of type checking. This toolchain's `lean` has
`-s, --tstack=num` (thread stack size in KB; see `lake env lean --help`). Question: is the ceiling
the thread stack or structural? Add a phase `stack <key> --tstack N` to `scripts/bench_scaling.py`:
`lake env lean --tstack=N -Dprofiler=true <Cert.lean>` with the same 900 s timeout, the same
peak-memory measurement, the full output saved next to the Cert.lean, the outcome classified as in
`classify`, recorded in `state.json` under `stack` (key, N, outcome, kernel s, wall s, peak MB,
message), and a generated paragraph "Stack experiment" in SCALING.md (report phase; no hand-edited
number; `scaling.csv` unchanged, the experiment is not a scaling row). Runs: N = 65536 (64 MB)
and, only if that run still hits the guard, N = 524288 (512 MB); at most two runs; a timeout or
`oom` ends the experiment. Whatever the result, record it: **no library or generator change** in
this stage, whatever the result suggests (a recommendation in DECISIONS.md is enough).

### Docs (14c)

`docs/DECISIONS.md`: one dated entry: the default 10 and why (the 14b figures); the alternatives
rejected (a default tied to the network size: needs a cost model, none measured yet; keeping 12
with a warning: the user would wait 15 minutes to learn what the warning says); the stack
experiment's result and what it says about the ceiling. `docs/PROJECT_STATUS.md`: the new default
in the status words; §4 rows updated (count-limit row closed; the rand_a64 row carries the
experiment's result). SORRIES.md: no new rows.

### Acceptance (14c)

- `lake build` green, warning-free; `scripts/ci_local.sh` all PASS (user's terminal); the
  committed certificates byte-identical outside the machine fields; test (f′) passes.
- The stack experiment recorded in `state.json`; SCALING.md regenerated, `git diff` showing the
  new paragraph only.

### Stop conditions (14c)

- A committed certificate would change → stop and report (it must not).
- Test (f′) exceeds 60 s → shrink the predicate; if that does not help, report.
- The second stack run also fails → record and stop; no third run, no `maxRecDepth`, no code change.

---

## Closing reply (each task)

CLAUDE.md format, under 40 lines. In (e) for 14a: the count route and its line count, the
kernel-time change per certificate. For 14b: the threshold per family and the growth trend of
kernel time against instruction count. For 14c: the new default and the (f′) result; the stack
experiment (N, outcome, kernel time, peak) and, in one sentence, whether the ~2000-instruction
ceiling is a stack-size artifact.
