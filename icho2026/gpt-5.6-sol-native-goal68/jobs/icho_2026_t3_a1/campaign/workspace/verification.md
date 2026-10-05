# Verification: IChO 2026 T3-A1

## Source integrity and inspection

The question image, original PDF question page, periodic-table page, and blank
student answer sheet were inspected. In the 93-page PDF these are pages 25
(`Q3-1`), 5 (`G1-5`), and 32 (`A3-1`), respectively. The blank sheet contains
only `COF-1: ______` and `C: ______ %` for part 3.1.

Command:

```text
sha256sum icho_2026_source/image/T3_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
b45e76d54ec6b862b5c07437ef7ff3274f18695cacf71e924a900209318a7cb8  icho_2026_source/image/T3_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

Both hashes exactly match `TASK.json`.

## Lean dependency build

The shared reporting module had no pre-existing local build artifact, so it
was built before invoking Lean directly on the target.

Command:

```text
lake build IChO2026Chem.Reporting
```

Result (exit code 0): `Build completed successfully (8558 jobs).` The command
also emitted the pre-existing style warning `Copyright too short!` for
`IChO2026Chem/Reporting.lean`; it is unrelated to this target.

## Target compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t3_a1.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T3A1.cof1_empirical_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A1.cof1_carbon_mass_percent_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A1.cof1_carbon_mass_percent_two_decimal_places' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T3A1.icho_2026_t3_a1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the task. In particular,
`sorryAx` is absent and no custom axiom is used.

Proof-shortcut scan command:

```text
grep -nE '(^|[[:space:]])(sorry|admit|axiom|unsafe)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t3_a1.lean
```

Result (exit code 1): no matches, as intended.

## Semantic audit

- The source-data namespace contains only diagram readings (`C6H4` phenylene,
  `B3O3` boroxine) and the four printed atomic weights.
- `balanced_cell_multiplicities` proves from `2L = 3R` that every periodic
  cell has `L = 3k` and `R = 2k`; `balanced_cell_formula` then proves its atom
  inventory is a multiple of `C3H2BO`.
- `cof1_empirical_formula_is_primitive` proves the subscript gcd is 1, and
  `cof1_empirical_formula` proves normalization of the counted cell.
- `cof1_carbon_mass_percent_exact` proves the unrounded value is exactly
  `450375 / 8107 = 55.553842358...` percent.
- `cof1_carbon_mass_percent_two_decimal_places` proves the raw value belongs
  to the `55.55` rounding interval at quantum `0.01` under the shared
  half-away-from-zero reporting relation.
- The final theorem `icho_2026_t3_a1` states the literal atom-count result,
  exact raw percentage, and explicit reported percentage together.

No source gaps or unproved chemistry dependencies remain for this subquestion.
