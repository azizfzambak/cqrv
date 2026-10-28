# Setting up CQRV on a new workstation (Windows)

Reference machine: Dell Precision 7920 Tower, 2 × Xeon Silver 4116 (2 × 12 cores / 48 threads,
2.1 GHz, turbo 3.0 GHz), 128 GB DDR4, system disk C: = 2 TB SATA HDD, external Samsung T9 2 TB
SSD. Development so far: laptop with an i9-13900H, 4 Lean threads (low memory). CI stays local
(`scripts/ci_local.sh`; DECISIONS.md 2026-10-28).

## 1. Put everything on the SSD, not on C:

C: is a mechanical disk (≈ 136 MB/s, ≈ 140 random-read IOPS); Lean reads thousands of small
Mathlib `.olean` files. Keep the repository **and** the toolchain on the T9 (below `E:` stands
for the T9's drive letter).

- Repository: on the laptop, with the T9 plugged in: `git clone C:/Users/azizz/cqrv E:/cqrv`
  (a clone carries the full history; `.lake/` and `.venv/` are not copied and are rebuilt below).
  Plug the T9 into a USB 3.x port of the workstation (rear ports; a 10 or 20 Gbit/s port if
  available).
- Toolchain: set the user environment variable `ELAN_HOME=E:\elan` **before** installing elan.

## 2. Install the tools

1. Git for Windows (provides Git Bash, which `scripts/*.sh` need).
2. elan (Lean toolchain manager): https://github.com/leanprover/elan — accept the defaults; the
   repository's `lean-toolchain` (`leanprover/lean4:v4.35.0`) is downloaded on first use. Never
   change `lean-toolchain` or `lake-manifest.json` (pinned, CLAUDE.md rule 4).
3. Python 3.11 (the harness was run with 3.11.9).
4. Optional: LLVM (`llvm-as` on `PATH`) for the QIR step; without it the step uses llvmlite only.

## 3. Build (Git Bash, in `E:/cqrv`)

```
python -m venv .venv
.venv/Scripts/python.exe -m pip install --no-deps -r tests/diff/requirements.lock
lake exe cache get        # downloads the Mathlib build cache; skipping it means hours of compiling
lake build
LEAN_NUM_THREADS=16 scripts/ci_local.sh
```

All steps must print PASS (the n/a lines are steps without a local counterpart). Step 20
(`scripts/check_certify.sh`) certifies the examples into a temporary directory and checks that
their `Cert.lean`, `.qir` and `.qasm` are byte-identical to the committed `examples/certs/*`
(`certificate.json` modulo machine fields) — this is the check that the new machine reproduces
the certificates.

## 4. Settings to choose yourself (system / security settings)

- **Microsoft Defender exclusions** for `E:\cqrv` and `E:\elan`: real-time scanning of every
  `.olean` read slows the build markedly. Only exclude these two folders.
- **Power plan**: High performance (or Ultimate performance).
- `LEAN_NUM_THREADS`: 4 was a low-memory setting. With 128 GB, 16–24 is safe; `ci_local.sh`
  reads it from the environment.

## 5. What to expect

- `lake build` and `ci_local.sh` parallelize across files: faster than on the laptop.
- A single certificate's kernel check is single-threaded; the Xeon's single-core speed is lower
  than the laptop's P-cores, so per-certificate kernel times (`kernel_check` in
  `certificate.json`) may be **longer** than the committed ones. That is a machine field, not a
  failure (the run-vs-run comparisons ignore machine fields since the Stage 13a′ review). Measure once and
  record the figures in DECISIONS.md if they are to be quoted.
- The step-20 low-memory failures seen on the laptop should not occur.
