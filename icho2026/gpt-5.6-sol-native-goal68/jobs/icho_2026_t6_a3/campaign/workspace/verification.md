# Verification record

All commands were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t6_a3/campaign/workspace`

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T6_page-1.png icho_2026_source/image/T6_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba  icho_2026_source/image/T6_page-1.png
d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362  icho_2026_source/image/T6_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes match `TASK.json` and `isolation_manifest.json`.

## Lean compilation and axiom inspection

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t6_a3.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T6A3.availableEnergy_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.fluorine_not_accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.chlorine_not_accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.bromine_not_accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.iodine_accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.energeticallyAccessible_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A3.possibleHalogens_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The displayed dependencies are standard Lean logical axioms. In particular,
there is no `sorryAx` and no custom unchecked axiom.

## Shortcut scan

Command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe)([[:space:]]|$)|^[[:space:]]*(axiom|constant)[[:space:]]' IChO2026Problems/problem_icho_2026_t6_a3.lean; then exit 1; else echo 'PASS: no sorry/admit/unsafe or custom axiom/constant declaration'; fi
```

Result (exit code 0):

```text
PASS: no sorry/admit/unsafe or custom axiom/constant declaration
```
