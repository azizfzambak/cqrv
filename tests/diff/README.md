# Differential test harness (Python)

Statevector simulator used to check synthesized circuits for n ≤ 12 before any grade is
claimed (CLAUDE.md rule 9; report §9.5.1). This is the only Python in the repository and it
is test-only: nothing here is part of the trusted pipeline.

- Stage 0: `statevector.py` is a placeholder simulator (H, X, CNOT) with a self-test.
- Stage 5: the executor for the CQRV gate-level IR (mid-circuit measurement, TempLogicalAND,
  MBU) and the randomized oracle tests are added here.

Run from the repository root:

```bash
pip install -r tests/diff/requirements.txt
python -I tests/diff/statevector.py --selftest
```
