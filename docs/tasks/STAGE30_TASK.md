# Stage 30 — The release (PHASE2_SPEC §D.3; Milestone M5)

PHASE2_SPEC.md §D. PHASE2_ROADMAP row 30. Written at the 27c review (2026-11-16) by the reviewer,
under the author's delegation.

Stage 30 has four tasks:
- **30a**, housekeeping (implementer, one commit), is specified here;
- **30b**, the reports (implementer, one commit), is specified here;
- **30c**, the drafts, is the reviewer's; its files are committed in the 30b review commit;
- **30d**, the release, is the author's, step by step.

**Invariants of Stage 30:**
- No theorem statement and no declaration name changes. A moved file keeps its declarations and
  namespaces.
- Every certificate, check file, selection file and artifact stays byte-identical, except the
  manifests that 30a A3 names.
- Every existing `cqr` output stays byte-identical, except where 30a names a change.
- No `sorry`, no `native_decide`, no new download.
- `docs/paper/` and `docs/cqrv_report_revised_v4.docx` are neither read nor edited nor staged.
- Nothing is published or pushed.
- The CI pass mark (26 PASS) is kept, or raised by a new step.

---

## 30a — Housekeeping

Precondition: main = the 27c review commit; start with `git switch -c stage-30a main`.

**A1. The duplicated schedule** (§B.3 (2)). `Grover.FewSchedule`'s kernel-evaluable plan and
Problem1's copy of it (`planK`, `plan_eq`) become one definition.
- Put it in a module that both may import without breaking the layering (Circuit and Synthesis
  never import Grover), or prove the copy equal to the original and drop the copy's own proofs.
- `problem1_T_lower_bound` and the `planB_*` theorems keep their statements.

**A2. The layering exception** (§B.3 (2)). `CQRV/Circuit/CountingCorrect.lean` imports
`CQRV/Grover/Restore.lean`. Remove the edge: either move the lemmas it needs down into
`CQRV/Circuit/`, or move the file up into `CQRV/Grover/`, with its declarations' names unchanged.
Say which.

**A3. The manifest relabel** (27b2 review).
- In the physical-certificate manifests, the top-level `meaning` ("… not a statement about noise
  …") becomes `meaning_physical_translation`.
- The physical-certificate manifest schema gets a minor version bump.
- The seven physical / noise certificate manifests are regenerated: grover_pred_037_torino,
  hw_n2_torino, hw_n3_torino, mbu_gadget_torino and the three fr_* ones. Their `.lean` files and
  `physical.qasm` stay byte-identical.
- The Python checks follow the new key.

**A4. The READMEs.**
- `hw/README.md`: restructured from one section per stage to (target, lowering, transpile with
  witness, runs, checks, certificates, noise, frontier).
- `examples/hw_checks/README.md`: one table of all fifteen check files.

**A5. A layering check in CI.** A short script, run in an existing step, fails if any
`CQRV/Circuit/*` or `CQRV/Synthesis/*` module imports a `CQRV/Grover/*` module. Also list any
other upward import it finds; report it, do not fix it.

**30a Acceptance / Stop**
- **Acceptance:**
  - `lake build` green and warning-free;
  - CI 26 PASS;
  - the axiom audit unchanged;
  - `git diff --stat` shows no certificate change outside A3's manifests.
- **Guards.** Stop and report if:
  - A1 or A2 would change a statement;
  - the task goes above about 800 lines.

## 30b — The reports

Precondition: main = the 30a review commit. Written from the repository alone; `docs/paper/` is
not read.

**R1. `docs/M5_REPORT.md`.** In the form of `docs/M3_REPORT.md`, every number from a committed
file or a CI log:
1. **What is certified.** Track A (counting, selection, measured composition), Track B
   (restoration under measurement, Clifford ⇔ quadratic, the regimes, the 8n − 24 bound), Track C
   (the chain from logical to physical, and the conditional noise theorem), each with its axiom
   lines.
2. **The committed certificates**, logical, physical and conditional: grades, `PhysGrade`, δ / δ',
   and kernel times.
3. **The CI** with its 26 steps and their times.
4. **The open items.** Clean ⇒ Cond(true), the dirty widening, and the all-n forms of 23c are
   open. The block commutation is closed in 26b2. Stage 28 follows the author's decision (§D.1).
5. **The claims** Paper 1 and Paper 2 may make, each with its evidence and exact scope, and the
   claims they must not make: "verified on hardware", useful problem sizes on these calibrations,
   (P-stoch) as a fact.

**R2. `docs/STAGE29_NOTE.md`.**
- **Why Stage 29 is not run:** no Coq / SQIR toolchain, and the download and effort it needs.
- **The comparison with verified quantum compilation in the literature:** SQIR / VOQC, and others
  you can name with authors, venue and year.
- **What CQR's specialization adds:** proof-carrying patterns specialized per instance, kernel
  checks of untrusted output, the noise premise as a hypothesis.
- **The citation rule.** No figures from papers you cannot point to. Anything uncertain is marked
  "to be checked by the author".

**R3. `docs/RELEASE.md`.**
- **Reproduction:**
  - the toolchain and the dependency pins;
  - the two virtual environments and their locks (qiskit 2.6.2, qiskit-aer 0.18.2,
    qiskit-ibm-runtime 0.52.1, whose fake backends' snapshots are the shipped ones);
  - the commands for each CI step and its expected time;
  - which artifacts reproduce byte for byte from their seeds.
- **The trust boundary:**
  - what the kernel checks;
  - what is untrusted (Qiskit, Aer, the printers, the parsers);
  - what is a premise ((P-cal), (P-stoch), (P-ro), (P-idle), the feed-forward latency).

**R4. The README.** The top-level README becomes a release README:
- what the project is;
- the three tracks in a paragraph each;
- how to build and check;
- pointers to `docs/RELEASE.md`, `docs/M5_REPORT.md` and the examples.

**30b Acceptance / Stop**
- **Acceptance:**
  - `lake build` green;
  - CI 26 PASS;
  - every number in R1 traceable to a file;
  - nothing in R1–R4 says "verified on hardware".
- **Guard.** Stop and report if R1 would need a number that no committed file or CI log gives.

## 30c — The drafts (reviewer)

Committed in the 30b review commit, for the author's approval:
- `docs/notes/REPORT_V5_DRAFT.md`;
- `docs/notes/PAPER1_REVISION_DRAFT.md`;
- `docs/notes/PAPER2_DRAFT.md` updated.

## 30d — The release (author)

Each step needs the author's explicit approval, asked one at a time:
- the public repository and its licence;
- the CI run off this machine;
- the archive with a DOI;
- the preprint of Paper 1;
- the submission of Paper 2.

The author's `docs/paper/ARXIV_CHECKLIST.md` is the checklist for that day.

## Closing reply (each task)

Per CLAUDE.md: (a) files, (b) build tail, (c) tests, (d) SORRIES.md, (e) open questions. Send it
to the reviewer session (QUANTUM CODING) with SendMessage, and print it.
