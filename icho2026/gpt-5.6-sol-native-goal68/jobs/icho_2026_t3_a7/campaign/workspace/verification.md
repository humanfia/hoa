# Verification

All commands were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t3_a7/campaign/workspace`

## Source identity

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-6.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-7.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
59aaf302f84f2f5ef23177b8de3fa18d670cbda2cda8404c9cef07a6c49b2bb6  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-6.png
285c433a7a9b27363f60e9e15f733e8b834a79faf46ad8a0ef743d453d91562e  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T3_page-7.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

These are exactly the hashes recorded in `TASK.json` and
`isolation_manifest.json`.

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result: exit code 0; `Build completed successfully (8561 jobs).` The only
messages were pre-existing short-copyright-header style warnings in the shared
infrastructure.

## Final target check and axiom inspection

The target file contains explicit `#print axioms` commands for its structural,
raw-numerical, reporting, and collected final theorems.

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t3_a7.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T3A7.pore_stoichiometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A7.cof9_formula_per_pore' does not depend on any axioms
'IChO2026Problems.T3A7.equilibrium_capacity_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A7.uranyl_ions_per_pore_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A7.equilibrium_capacity_three_significant_figures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T3A7.uranyl_ions_per_pore_three_significant_figures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T3A7.t3_a7_requested_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` and no custom unchecked axiom; the listed axioms are
standard Lean logical axioms allowed by the goal.

## Shortcut scan

Command:

```text
! grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t3_a7.lean
```

Expected/result: exit code 0 with no output, confirming that none of the
forbidden proof shortcuts occurs in the target.

## Result manifest validation

Command:

```text
python3 -m json.tool result.json
```

Result: exit code 0; the command printed the parsed JSON document without an
error.
