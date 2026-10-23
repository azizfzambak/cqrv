# Differential test harness (Python)

Statevector simulator used to check synthesized circuits for n ≤ 12 before any grade is
claimed (CLAUDE.md rule 9; report §9.5.1). This is the only Python in the repository and it
is test-only: nothing here is part of the trusted pipeline.

- Stage 0: `statevector.py` is a placeholder simulator (H, X, CNOT) with a self-test.
- Stage 5: `statevector.py` executes the IR exported by `cqr synthesize --json` (H, S, S†, T,
  T†, X, Z, CNOT, CZ, mid-circuit measurement with **both outcomes enumerated**, classically
  controlled gates, `alloc`/`free` asserting |0⟩). `oracle_diff.py` checks the synthesized
  phase oracles in every measurement branch on random complex superpositions (report §6.2.4):
  100 random AND/NOT/OR predicates (fixed seed, n ≤ 12) + `grover_pred_037`, 30 xor/`if`
  predicates, and Bennett-pebbled AND chains. Driver: `scripts/diff_oracles.sh` (CI).
- Stage 6b-3: `oracle_json.py` checks that `cqr synthesize --json` on the corpus files
  (grover_pred_037, search_or, and_chain_8) and 20 random predicates (fixed seed) is
  byte-identical to `oracle_json_golden.txt` (proof-only synthesizer changes must not change
  the circuit). Driver: `scripts/check_oracle_json.sh` (CI); `--write` regenerates the golden
  file.

Run from the repository root:

```bash
pip install -r tests/diff/requirements.txt
python -I tests/diff/statevector.py --selftest
lake build && scripts/diff_oracles.sh      # PYTHON=.venv/Scripts/python.exe on Windows
```
