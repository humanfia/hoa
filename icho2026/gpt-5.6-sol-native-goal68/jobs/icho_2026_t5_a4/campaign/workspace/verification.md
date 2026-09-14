# Verification record for `icho_2026_t5_a4`

This file records final-state checks. All commands were run from the workspace
root.

## Lean verification

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t5_a4.lean
```

Observed result: exit code 0. The file itself runs `#print axioms` for the
dependency, measurement, uniqueness, and requested-output theorems. Lean
reported:

```text
'IChO2026Problems.ProblemIChO2026T5A4.fattyAcid_formula_from_source' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.ProblemIChO2026T5A4.fattyAcid_formula_from_all_source_constraints' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.ProblemIChO2026T5A4.iodineUptake_matches_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T5A4.iodineBromide_matches_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T5A4.iodineReagent_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T5A4.compound_x_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are only permitted Lean/Mathlib logical foundations; there is no
`sorryAx` and no custom unchecked axiom.

## Shortcut scan

Command:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t5_a4.lean; then exit 1; else echo 'No forbidden proof shortcuts found.'; fi
```

Observed result: exit code 0 and:

```text
No forbidden proof shortcuts found.
```

## Source-integrity check

Command:

```text
sha256sum icho_2026_source/image/T5_page-1.png icho_2026_source/image/T5_page-2.png icho_2026_source/image/T5_page-3.png icho_2026_source/raw/theory_problem.pdf
```

Observed result: exit code 0 and:

```text
4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347  icho_2026_source/image/T5_page-1.png
7f0f35d726d79f8d1ff9b15ee00574efeb89d8b179ab05469b5c297cb147bb96  icho_2026_source/image/T5_page-2.png
9824f187e7baa6e5929ec0c7cda6c740aee46a1404afdcad974c734b083b86b7  icho_2026_source/image/T5_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

All four match `TASK.json`, confirming that the source inputs remain
unchanged.
