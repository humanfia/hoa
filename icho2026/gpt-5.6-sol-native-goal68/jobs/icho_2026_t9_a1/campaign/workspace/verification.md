# Verification for `icho_2026_t9_a1`

## Source checks

Command:

```text
sha256sum icho_2026_source/image/T9_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
c7f5114e9bb5d3e821a3df76d40c4ab86006fdb550992aa8013bc50b68a90608  icho_2026_source/image/T9_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match `TASK.json`. Visual inspection covered the supplied
question image, original PDF page 84 (Q9-1), the periodic table on original PDF
page 5, and the blank answer sheet on original PDF page 89 (A9-1).

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0): the build completed successfully (`8561 jobs`). The only
messages were pre-existing style warnings that the copyright headers in
`IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean` are too short.

## Final Lean verification

Command, run from the workspace root:

```text
lake env lean IChO2026Problems/problem_icho_2026_t9_a1.lean
```

Result: exit code 0. The `#print axioms` commands in the checked file printed:

```text
'IChO2026Problems.ProblemIcho2026T9A1.beta_cd_has_seven_glycosidic_bonds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A1.water_molar_mass_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A1.beta_cd_raw_molar_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A1.beta_cd_three_significant_figures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A1.beta_cd_molar_mass_answer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean logical axioms allowed by the task. There is no
`sorryAx`, custom axiom, `sorry`, `admit`, or `unsafe` declaration.

Forbidden-declaration scan command:

```text
! grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t9_a1.lean
```

Result: exit code 0 and no output (no forbidden declaration matched).

## Semantic coverage

The formalization separates source data from derived results:

1. It records the seven-unit beta-CD input and exact printed masses.
2. It models the cyclic links as pairs from every unit to its successor and
   proves that this finite set has cardinality seven.
3. It applies the glycosidic-condensation mass balance without intermediate
   rounding and proves the exact raw result `141876 / 125 = 1135.008`.
4. It proves that reporting `1140` with quantum `10` satisfies the project's
   nearest-value, half-away-from-zero relation, i.e. the requested
   `1.14 * 10^3 g mol^-1` at three significant figures.
