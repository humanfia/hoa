# Verification record

All commands below were run from the workspace root:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t3_a2/campaign/workspace`

## Source integrity

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T3_page-1.png icho_2026_source/image/T3_page-2.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
b45e76d54ec6b862b5c07437ef7ff3274f18695cacf71e924a900209318a7cb8  icho_2026_source/image/T3_page-1.png
a5ccbc95f044ecac46d1e2f836e9fe0b9fec633a181b8986f6b2360e7b303b40  icho_2026_source/image/T3_page-2.png
```

These values match `TASK.json`. The original PDF was independently opened and
inspected at pages 25 (molecular drawing), 26 (T3-A2 statement), and 32 (blank
A3-1 student answer sheet containing the 3.2 work box and `d = ___ Å`).

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
Build completed successfully (8561 jobs).
```

The build emitted only pre-existing short-copyright-header linter warnings for
`IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean`.

## Target compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t3_a2.lean
```

Result (exit code 0):

```text
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_side_bond_counts' does not depend on any axioms
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_side_length_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_internal_diameter_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.problem_icho_2026_t3_a2.sqrt_three_reporting_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_internal_diameter_rounding_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_internal_diameter_submission_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.problem_icho_2026_t3_a2.cof2_internal_diameter_reported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The final theorems therefore use only standard Lean logical axioms. In
particular, `sorryAx` is absent and no custom axiom is declared.

## Forbidden-shortcut scan

Command:

```text
if grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t3_a2.lean; then exit 1; else printf 'No forbidden proof shortcuts found.\n'; fi
```

Result (exit code 0):

```text
No forbidden proof shortcuts found.
```

## Result manifest syntax

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0 with no output.
