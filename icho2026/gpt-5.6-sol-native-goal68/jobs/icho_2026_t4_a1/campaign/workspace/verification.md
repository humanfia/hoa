# Verification

## Source checks

Command:

```text
sha256sum icho_2026_source/image/T4_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  icho_2026_source/image/T4_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match `TASK.json` and `isolation_manifest.json`. Visual
inspection covered the supplied `T4_page-1.png`, PDF page 5 (`G1-5`, periodic
table), PDF page 37 (`Q4-1`), and all four T4 blank student answer sheets on PDF
pages 40--43 (`A4-1`--`A4-4`).

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
⚠ [8558/8561] Replayed IChO2026Chem.Core
warning: IChO2026Chem/Core.lean:1:1: * '-/':
Copyright too short!

Note: This linter can be disabled with `set_option linter.style.header false`
⚠ [8559/8561] Replayed IChO2026Chem.Reporting
warning: IChO2026Chem/Reporting.lean:1:1: * '-/':
Copyright too short!

Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (8561 jobs).
```

This compiles the fixed shared reporting definitions used by the target. The
two style warnings concern pre-existing copyright headers and do not affect
verification. No source file was changed by this command.

## Final Lean check and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a1.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T4A1.uranium235_atomic_fraction_characterization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T4A1.uranium235_abundance_percent_characterization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T4A1.uranium235_raw_percent_satisfies_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T4A1.uranium235_atomic_fraction_is_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T4A1.uranium235_reported_percent_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A1.uranium235_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A1.uranium235_abundance_output' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The output comes from the explicit `#print axioms` commands at the end of the
target file. It contains only standard Lean logical axioms allowed by the goal;
there are no custom unchecked axioms.

## Forbidden-placeholder scan

Command:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t4_a1.lean
```

Result: exit code 1 with no output, meaning no forbidden proof placeholder,
unsafe declaration, or custom axiom occurs in the target file.
