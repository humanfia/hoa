# Verification for `icho_2026_t1_a6`

## Source integrity and inspection

Command:

```text
sha256sum icho_2026_source/image/T1_page-3.png icho_2026_source/image/T1_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
fbdc901fd87b13a184497f3cb922f1cceb63ec8d01f0ff7fc6985d4131e70a17  icho_2026_source/image/T1_page-3.png
a430d0875b35b8bc21e571c8e2fcd931f3db8288fc5cddcb8f62594f241aac46  icho_2026_source/image/T1_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes equal the values in `TASK.json` and `isolation_manifest.json`.
The 93-page PDF was inspected directly. Relevant pages were G1-5 (periodic
table), Q1-3/Q1-4 (statement), and blank student sheets A1-3/A1-4/A1-5. The
provided T1 page images were also inspected at original resolution.

## Lean verification

The shared local module was first built with:

```text
lake build IChO2026Chem
```

Result: exit code 0. The only messages were pre-existing style warnings in
`IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean` about short copyright
headers.

Final required compile command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t1_a6.lean
```

Result: exit code 0. The `#print axioms` commands in the source printed:

```text
'IChO2026Problems.T1A6.icho_2026_t1_a6_formulae' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A6.hydration_number_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A6.combustion_product_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A6.aluminaFraction_in_measurement_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical/quotient axioms. There are no custom unchecked
axioms.

Shortcut scan command:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t1_a6.lean; then exit 1; else echo 'no forbidden proof shortcuts'; fi
```

Result: exit code 0 and `no forbidden proof shortcuts`.

## Semantic coverage

The formalization proves:

- the A4 percentage checks for `AlF3.3H2O` and `Na3AlF6`;
- the A5 percentage checks and balanced formula transformations for
  hexamethylbenzene, mellitic acid, and `C12O9`;
- propagation of all displayed mass half-widths to exact ratio intervals;
- uniqueness of `x = 16` over every natural-number hydration count, without a
  search bound;
- uniqueness of the unknown nonvolatile combustion product as `Al2O3` from
  atom conservation; and
- agreement of both proposed TGA plateaux with the measurement intervals.
