# Verification record — `icho_2026_t1_a4`

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t1_a4/campaign/workspace`
with Lean toolchain `leanprover/lean4:v4.31.0` and Mathlib `v4.31.0`
(see `lean-toolchain`, `lake-manifest.json`).

## 1. Direct elaboration of the solution file

```
lake env lean IChO2026Problems/problem_icho_2026_t1_a4.lean
```

Result: **exit code 0, no errors** (full log `/tmp/leantest/full10.log`, ends `EXIT:0`;
wall time ≈ 4.8 min; the bulk of the time is the per-case interval sweeps in the
envelope chunks, run at `maxHeartbeats 2500000`).
The only diagnostics are style/deprecation **warnings** (unused-tactic branches in
`first | … | …` disjunctions and the `push_neg` deprecation notice), which do not
affect soundness.

## 2. Full project build (lib target `IChO2026Problems`, incl. `All.lean`)

```
lake build
```

Result: **"Build completed successfully (8581 jobs)"**, exit code 0.
One pre-existing style warning in the protected umbrella `IChO2026Problems.lean:4`
(line longer than 100 chars) — present in the provided template, untouched.

## 3. Axiom audit of the final theorems

Probe file (namespace opened, `#print axioms` on every key theorem):

```
import IChO2026Problems.problem_icho_2026_t1_a4
open IChO2026Problems.T1A4
#print axioms main_answer
#print axioms answer_aluminium
#print axioms theAnswer_correct
#print axioms stoichiometry_at_aluminium
#print axioms x_bound
#print axioms n_bound
#print axioms envelope_v2
#print axioms envelope_v3
#print axioms table_no_match_v2
#print axioms table_match_v3
```

run as

```
lake env lean /tmp/leantest/axioms.lean
```

Result: **every theorem depends only on `[propext, Classical.choice, Quot.sound]`** —
the three standard Lean logical axioms. No custom or unchecked axioms, no `sorryAx`.

## 4. No proof shortcuts in the source

```
grep -n "sorry\|admit\|axiom\|native_decide\|unsafe" IChO2026Problems/problem_icho_2026_t1_a4.lean
```

Result: the only match is the header doc-comment line
"No `sorry`/`admit`, no custom axioms." — the file contains **no** sorry, admit,
custom axiom declarations, `native_decide`, or `unsafe` code.

## 5. Statement-faithfulness check (independent reading)

The requested outputs are classification/formula answers (Q, C·xH₂O, D). The formal
development establishes:

* `answer_aluminium` / `theAnswer_correct`: the submitted identification
  (Al, AlF₃·3H₂O, Na₃AlF₆) reproduces all three printed percentages strictly inside
  their displayed half-quantum windows — existence/correctness of the answer.
* `main_answer`: **uniqueness** — any `(v, x, n)` with v ∈ {2,3}, 1 ≤ x, 1 ≤ n,
  `0 < ArQ ≤ 294`, satisfying the three measured data, whose true mass matches a printed
  periodic-table value within half a quantum, must be `(3,3,3)` with the matched table
  entry z = 12 (atomic number 13, aluminium, printed mass 26.98).
* Supporting: `x_bound` (x ≤ 37), `n_bound` (n ≤ 13) — search bounds *derived* from the
  data, not asserted; `envelope_v2`/`table_no_match_v2` rule out v = 2 against the table
  printed in the same paper; `envelope_v3`/`table_match_v3` single out aluminium;
  `stoichiometry_at_aluminium` re-derives x = 3 and n = 3 at the tightened aluminium mass.

The three chemical modelling inputs that cannot be derived from the problem text
(valence family v ∈ {2,3}; the NaF-adduct structure NaₙQF_{v+n} of D; 0 < Ar ≤ 294;
half-quantum matching to the printed table) are declared as assumptions M-A4-1..4 in the
file header and recorded in `result.json` (`assumptions` / `source_gaps`).

## 6. Numeric cross-check of the answer (independent of Lean)

```
54.048/138.028 = 0.391577…   (hydration, window 0.39155–0.39165)  ✓
68.97/209.94   = 0.328524…   (sodium,    window 0.32845–0.32855)  ✓
26.98/209.94   = 0.128513…   (metal,     window 0.12845–0.12855)  ✓
```

Feasibility scan (exact rational arithmetic) over v ∈ {2,3}, 1 ≤ x ≤ 37, 1 ≤ n ≤ 13
against all three windows leaves exactly two families: (2,2,2) with
Ar ∈ (17.9776, 17.9920) — no such printed element (O = 16.00, F = 19.00) — and
(3,3,3) with Ar ∈ (26.9663, 26.9880) — uniquely matching aluminium 26.98.
