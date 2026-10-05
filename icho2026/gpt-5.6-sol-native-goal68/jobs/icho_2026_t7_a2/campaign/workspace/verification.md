# Verification record: `icho_2026_t7_a2`

## Source checks

The following problem-only inputs were inspected:

- `GOAL.txt` and `TASK.json`;
- `icho_2026_source/image/T7_page-1.png`;
- `icho_2026_source/raw/theory_problem.pdf`, especially PDF page 5
  (periodic table), page 63 (printed Q7-1), page 67 (blank A7-1), and page 68
  (blank A7-2).

Input-integrity command:

```text
sha256sum icho_2026_source/image/T7_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
ee7fe1adff7ac3aae8701bf684981bd2b1e21b28f1c9e4b21dd9c38c3bdb79ad  icho_2026_source/image/T7_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These are exactly the hashes recorded in `TASK.json`.

## Lean verification

The shared local library first had to be compiled because the fresh workspace
contained source files but no local `IChO2026Chem` object file:

```text
lake build IChO2026Chem
```

Result: exit code 0, ending with:

```text
Build completed successfully (8561 jobs).
```

Required final-file verification command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a2.lean
```

Result: exit code 0. The file's `#print axioms` commands produced:

```text
'IChO2026Problems.T7A2.fig1_methane_ammonia_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A2.annual_methane_mass_required' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal. There are no
custom axioms.

Proof-shortcut audit command:

```text
grep -nE '\b(sorry|admit)\b|unsafe' IChO2026Problems/problem_icho_2026_t7_a2.lean
```

Expected and obtained result: exit code 1 with no output, meaning none of the
forbidden proof shortcuts occurs in the final Lean file.

## Semantic coverage

`fig1_labeled_air_unique` proves that the diagram's one-O2 basis uniquely
forces `x = 7/2` and `y = 3/2`; `fig1_labeled_air_basis` then checks every
relevant process stage on that basis. `fig1_feed_relation`,
`fig1_methane_ammonia_relation`, and
`fig1_methane_per_theoretical_ammonia` derive the 7:16
methane/theoretical-ammonia mole relation. The raw-mass definition depends on
that derived basis ratio. `annual_methane_mass_exact` proves the unrounded
tonnage from the source atomic masses and yield.
`annual_methane_submission_valid` proves that 280,000 is the correct nearest
1000-ton report, and the final theorem `annual_methane_mass_required`
combines the chemical basis, derived ratio, raw value, final value, and
reporting contract.
