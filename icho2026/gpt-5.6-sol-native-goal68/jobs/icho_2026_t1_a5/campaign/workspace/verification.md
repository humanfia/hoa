# Verification — `icho_2026_t1_a5`

## Source inspection

- Read `GOAL.txt` and `TASK.json` first.
- Visually inspected `icho_2026_source/image/T1_page-3.png` and `T1_page-2.png` at original resolution.
- Inspected the original 93-page `icho_2026_source/raw/theory_problem.pdf`. PDF page 8 is Q1-3 and contains T1.5; PDF page 13 is the blank student answer sheet A1-4 and contains three untemplated boxes labelled E, F, and G.
- Verified the three task-listed SHA-256 values with:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T1_page-2.png icho_2026_source/image/T1_page-3.png
```

Result:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb  icho_2026_source/image/T1_page-2.png
fbdc901fd87b13a184497f3cb922f1cceb63ec8d01f0ff7fc6985d4131e70a17  icho_2026_source/image/T1_page-3.png
```

## Lean verification

Exact command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t1_a5.lean
```

Result: exit code 0. All theorem declarations compiled. The embedded `#print axioms` audit reported:

```text
hydrogen_percentage_selects_methyl: [propext, Quot.sound]
oxygen_percentage_selects_three_waters: [propext, Quot.sound]
structure_e_from_problem: [propext, Quot.sound]
structure_f_from_problem: [propext, Quot.sound]
structure_g_from_problem: [propext, Quot.sound]
structure_e_connectivity: no axioms
structure_f_connectivity: no axioms
structure_g_connectivity: [propext]
structure_e_has_sixfold_axis: [propext]
structure_f_has_sixfold_axis: [propext]
structure_g_has_threefold_axis: [propext]
structure_g_matches_49_98_percent_oxygen: [propext, Classical.choice, Quot.sound]
triple_dehydration_formula_balance: [propext]
identified_structures: [propext, Quot.sound]
```

These are standard Lean logical axioms only. The file contains no `sorry`, `admit`, `unsafe`, custom `axiom`, or `native_decide` proof.

The formal checks cover:

- explicit atoms, hydrogens, bonds, bond orders, charges, radicals, and stereochemical fields;
- formulas `C12H18`, `C12H6O12`, and `C12O9`;
- ordinary neutral closed-shell valences;
- the full graph edits for sixfold benzylic oxidation and three adjacent dehydrations;
- exact half-last-place interval arithmetic for 11.18% H and 49.98% O;
- graph automorphisms of exact order 6 for E and F and exact order 3 for G;
- formula balance `F = G + 3 H2O`.

## Shortcut scan

Exact command:

```text
grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom|native_decide)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t1_a5.lean
```

Expected and observed result: no matches (exit code 1 from `grep`, meaning none of the forbidden tokens occurs).

