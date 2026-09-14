# Verification for `icho_2026_t2_a2`

Verification was performed from the workspace root. The final verification
commands and their results are recorded below.

## Source integrity

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T2_page-1.png icho_2026_source/image/T2_page-2.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
0b9e4e1edf255a14c8def4465de188b6cbd72b9df782a7d7efa32528b15c5ff2  icho_2026_source/image/T2_page-1.png
77bd97168be820a9643a8acac845ca1ef8c4c1a4a99f678c78227e6e5e48ef8b  icho_2026_source/image/T2_page-2.png
```

These hashes agree with `TASK.json` and `isolation_manifest.json`.

The original PDF was inspected directly. It contains 93 pages. PDF page 16 is
the question page; blank answer-sheet pages 19 and 20 contain the two answer
fields for `[HBrO2]_A` and `[HBrO2]_B`, respectively.

## Shared-library build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
Build completed successfully (8561 jobs).
```

The build also emitted only the pre-existing style-header warnings in
`IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean`.

## Target proof and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t2_a2.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T2A2.processA_rate_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A2.hbro2_process_a_stationary' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A2.hbro2_process_b_stationary' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A2.hbro2_process_a_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A2.hbro2_process_b_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A2.icho_2026_t2_a2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms. No custom unchecked axiom appears.

## Semantic-fidelity audit

- `ProcessASteadyState` uses the printed stoichiometry to encode
  `2 r1 - r2 = 0` for `BrO2` radical and
  `-r1 + r2 - 2 r3 = 0` for `HBrO2`. The proved elimination is
  `r1 = 2 r3`, not an assumed final formula.
- `ProcessBSteadyState` encodes `-r4 + r5 = 0` for `HBrO2`. Its proof cancels
  bromide only under the explicit active-phase hypothesis `0 < bromide`.
- Substitution of the exact printed data yields the exact Lean reals
  `6/1000000` and `504/10000000000000`. The reporting theorems separately
  prove validity at quanta `10^-8` M and `10^-13` M.
- The Process-A positivity hypothesis and Process-B bromide-positivity
  hypothesis exclude only inactive zero-factor degeneracies. They are stated
  in the final theorem rather than hidden in algebraic cancellation.
- Step (6), `k6`, malonic acid, and cerium initial concentration do not affect
  these two `HBrO2` balances. No printed fallback concentration was used.

## Shortcut scan

Command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t2_a2.lean; then exit 1; else echo 'No sorry/admit/unsafe/custom axiom declarations found.'; fi
```

Result (exit code 0):

```text
No sorry/admit/unsafe/custom axiom declarations found.
```

## Artifact checks

Commands and results:

```text
if grep -nE '[[:blank:]]+$|^(<<<<<<<|=======|>>>>>>>)' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t2_a2.lean; then exit 1; else echo 'No trailing whitespace or conflict markers found.'; fi
# No trailing whitespace or conflict markers found.

python3 -m json.tool result.json >/dev/null
# exit code 0; no output
```
