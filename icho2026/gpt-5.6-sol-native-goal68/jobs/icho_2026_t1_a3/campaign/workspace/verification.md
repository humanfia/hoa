# Verification record

Verified in
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t1_a3/campaign/workspace`
on 2026-09-13 (UTC).

## Source integrity and inspection

Command:

```text
sha256sum TASK.json icho_2026_source/image/T1_page-2.png icho_2026_source/image/T1_page-3.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
d92efaaa0a88e1d088f58d5b7daf7fa19a96080867ef358a9626d4c3c5b54f80  TASK.json
06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb  icho_2026_source/image/T1_page-2.png
fbdc901fd87b13a184497f3cb922f1cceb63ec8d01f0ff7fc6985d4131e70a17  icho_2026_source/image/T1_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The PNGs were inspected at original resolution. The original PDF was opened
locally and found to have 93 pages. In addition to PDF pages 7 and 8 (Q1-2 and
Q1-3), PDF page 11 (blank sheet A1-2) was rendered and inspected. Its T1-A3
area contains `n = ______` and checkboxes for `W` numbered 1 through 10. The
PDF and PNG hashes agree with the protected task manifest.

## Lean dependency build

The shared local import was built once before direct verification of the target
file:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
Built IChO2026Chem.Core
Built IChO2026Chem.Reporting
Built IChO2026Chem
Build completed successfully (8561 jobs).
```

There were only style-linter warnings about the short copyright header in the
pre-existing shared `Core.lean` and `Reporting.lean` files.

## Final Lean verification and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t1_a3.lean
```

Result (exit code 0):

```text
'IChO2026T1A3.carbon_atom_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A3.compound_identity' depends on axioms: [propext]
'IChO2026T1A3.solve_t1_a3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal. No custom
unchecked axiom occurs.

Command:

```text
if grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t1_a3.lean; then exit 1; else echo 'No forbidden proof shortcuts or custom axiom declarations found.'; fi
```

Result (exit code 0):

```text
No forbidden proof shortcuts or custom axiom declarations found.
```

## Semantic audit

- `molecularIonWeight` and `plusOneIonWeight` encode the all-carbon-12 and
  exactly-one-carbon-13 binomial weights.
- `theoreticalPeakRatio_cross_mul` proves cancellation to
  `ratio * (11*n) = 989`; it is not postulated.
- `carbon_atom_count` derives both strict integral bounds `9 < n` and `n < 11`
  from the source measurement interval, without a search bound.
- `ten_carbons_matches_displayed_ratio` proves that the answer exists and
  predicts a ratio that displays as 9:1.
- `candidateCarbonCount` records all ten printed formula carbon counts;
  `phenolic_candidates_are_one_or_five` exhaustively checks the ten candidate
  constructors; `compound_identity` eliminates compound 1 using `n = 10`.
- `solve_t1_a3` combines the independent carbon-count and compound-identity
  proofs and returns exactly the two outputs requested on blank sheet A1-2.

