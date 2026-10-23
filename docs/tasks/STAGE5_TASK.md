# Stage 5 — Circuit IR and oracle synthesizer (engineering; no proofs)

Report sections: §6.1.1 (no phase qubit: Z on the last AND ancilla), §6.1.2 (Eq. 2: T ≤ 4ĉ∧,
a = ĉ∧), §6.1.3 (Bennett tradeoff, Table 2), §6.1.4 (the oracle listing, Table 3: grade
(10, 21, 8, 2)), §6.2.2 (Gidney TempLogicalAND / MBU listing), §6.3.1 (Eq. 5: oracle grade).
Precondition: Stage 4 accepted (main = stage-4 = b648c03). `git switch -c stage-5 main`; one
commit; include this file (untracked) in it. Windows: `LEAN_NUM_THREADS=4`; Python:
`.venv/Scripts/python.exe -I`. Module system. No Physlib in `CQRV/Circuit` or `CQRV/Synthesis`
in this stage (the semantics into Physlib channels is Stage 6).

**The point of this stage:** the Python statevector harness must catch synthesizer errors —
and errors in the report's own listings — before anyone tries to prove anything (CLAUDE.md
rule 9). Every number the report gives is a *claim to be measured*, not a target to hit.

## Reviewer decisions (record each in DECISIONS.md, dated, with "Rejected:")

1. **Synthesis input is a Boolean network, not `SigmaIn`.** `SigmaIn` carries counts only.
   Add `toNetwork : TypedProgram → Network` (AND / NOT / XOR nodes over input bits; `or` via De
   Morgan, never DNF; `if` via the Stage 3 mux rule) and a test that its AND count equals ĉ∧
   from ℰ on the corpus. Rejected: re-parsing the source in the synthesizer.
2. **Scope of the synthesizer.** Mandatory: networks of AND/NOT/OR over input literals (chains
   and trees), one ancilla per AND, `Z` on the ancilla holding P(x) (or on the data qubit when
   ĉ∧ = 0), MBU uncompute in reverse order. XOR and `if` nodes: implement only if in-place XOR
   (CNOT onto an operand, undone afterwards) keeps width = n + ĉ∧; otherwise reject them with a
   diagnostic and leave them for Stage 9. Rejected: an extra qubit per XOR (changes Eq. 5).
3. **Bennett scheduler only for AND chains** (Table 2 is about a chain). General networks use
   the straight-line full-ancilla schedule. A valid pebble move: place node i only if its
   predecessor is pebbled; remove node i (MBU) only if its predecessor is pebbled (the CZ
   fix-up needs both controls). For an infeasible budget return an error, never a circuit.
4. **Depth is measured by one fixed scheduler:** ASAP layering, a gate occupies every qubit it
   touches, a classically controlled gate depends on its measurement, `allocate` is free.
   Rejected: tuning the scheduler to reproduce a number from the report.

## Tasks

1. **`CQRV/Circuit/IR.lean`** — gates `H, S, S†, T, T†, X, Z, CNOT, CZ`, `measure q → c`
   (computational basis), `ifBit c g` (classically controlled Clifford), `alloc q`, `free q`;
   `Circuit := List Gate` over named data/ancilla qubits. `Schedule.lean`: the decision-4
   scheduler; `depth`, `tCount` (T and T†, executed), `width`, `peakAncilla`; a layer dump for
   debugging (`cqr synthesize --layers`).
2. **`CQRV/Synthesis/TempAnd.lean`** — `TempLogicalAND a b t` gate-for-gate as the §6.2.2
   listing (4 T) and `UncomputeTempLogicalAND a b t` = `H t; measure t → m; ifBit m (CZ a b)`.
   The listing says the target is "restored to |0⟩ (reset)" but contains no reset: after an
   X-basis measurement the target is |m⟩. Add `ifBit m (X t)` and record it as a report erratum
   (it is Clifford, 0 T, and can share the CZ's layer).
3. **`CQRV/Synthesis/Oracle.lean`** — `synthesizeOracle : Network → Circuit` (decision 2),
   `grade : Circuit → Grade` = (width, depth, tCount, peakAncilla) from the scheduler;
   `CQRV/Synthesis/Bennett.lean` — `pebbleChain (L aMax : Nat) : Except String (List Move)`
   plus the executed T-count (4 × forward placements) and depth for a chain oracle.
4. **JSON export** of a circuit (`cqr synthesize <file> [--amax k] [--json] [--layers]`; prints
   the grade, and with `--json` the IR in a flat format the harness reads).
5. **`tests/diff/`** — extend the simulator to execute the IR JSON, including mid-circuit
   measurement: **enumerate both outcomes of every measurement** (branch tree), and in every
   branch of non-zero probability check, for a **random complex superposition** on the data
   register (basis inputs are not enough — §6.2.4: on basis states the phase cancels), that the
   post-state equals `U_P^ideal |ψ⟩ ⊗ |0…0⟩_anc` up to a global phase per branch (factorization
   + correct phase). Random predicates: AND/NOT/OR trees over random literals, n ≤ 12;
   **100 predicates** with a fixed seed, plus `grover_pred_037`. Driver script in `scripts/`,
   run by CI.

## Tests

- Lean (`tests/CQRVTests/Synthesis.lean`): TempLogicalAND has 4 T; uncompute 0 T; network AND
  count = ĉ∧ on the corpus; `pebbleChain 8 8` gives 1 round and T = 32.
- **Grover oracle grade:** the report claims (10, 21, 8, 2). Expect w = 10, t = 8, a = 2 to hold.
  For d, compute it with the decision-4 scheduler and **report the layer dump**. If d ≠ 21, do
  **not** change the scheduler or the circuit to reach 21: record the measured d, the layer dump
  and the reason in DECISIONS.md and in the closing reply (the report's Table 3 counts 7 layers
  per compute phase; check whether its listing can be scheduled in 7). The test then asserts
  the measured value.
- **Table 2 (c∧ = 8 chain):** for a_max ∈ {8, 4, 2, 1} report feasibility, rounds, depth
  multiplier and executed T; assert T ≤ 32 × multiplier for feasible rows. If a row of
  Table 2 is infeasible under decision 3 (e.g. a_max = 1), record it as a report erratum —
  do not invent a schedule.
- Python: 100 random predicates + grover_pred_037 pass in every measurement branch.

## Acceptance

- `lake build` green, no new `sorry`, check scripts pass; differential test green on 101
  predicates (paste the summary line).
- Grade of the Grover oracle measured and printed by `cqr synthesize examples/grover_pred_037.cqr`;
  every deviation from Table 3 / Table 2 documented, none hidden.
- DECISIONS.md: decisions 1–4, the reset erratum, and the measured depth.

## Stop conditions

- The §6.2.2 TempLogicalAND listing, implemented gate for gate, fails the harness (wrong AND
  value or ancilla not restored) → **stop** and report the failing branch; do not repair the
  listing on your own (the reviewer will compare it with Gidney's Fig. 3).
- The Z-then-MBU construction of §6.1.4 does not give `(−1)^P(x)` on superpositions → stop.
- Do not write the diffusion operator (separate task) and do not start Stage 6 (semantics).

## Closing reply

CLAUDE.md format, under 40 lines; in (e) at least: measured oracle depth vs 21, the Table 2
rows, whether XOR/`if` were implemented, and any listing that needed a fix.
