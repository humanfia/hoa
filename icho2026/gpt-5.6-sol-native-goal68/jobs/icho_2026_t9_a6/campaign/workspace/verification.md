# Verification record for `icho_2026_t9_a6`

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t9_a6/campaign/workspace`.

## Source identity

Command:

```text
sha256sum icho_2026_source/image/T9_page-3.png icho_2026_source/image/T9_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
a63869290bd2dcbc80632be3cbf121fab1ffa361f725255f17c191d16df7da4f  icho_2026_source/image/T9_page-3.png
a65b4bf067ff9b1aa03ad40758319abec68f959fce4bf64380bd0e8227bee48f  icho_2026_source/image/T9_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match `TASK.json`.  The relevant PDF pages were also
inspected directly: page 86 is `Q9-3`, and page 91 is the blank `A9-3`
student response sheet containing sections 9.5–9.7.

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result: exit code 0, ending with:

```text
Build completed successfully (8561 jobs).
```

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t9_a6.lean
```

Result: exit code 0.  The final `#print axioms` commands reported:

```text
'IChO2026Problems.ProblemIcho2026T9A6.lFreePrimarySites_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A6.monomer_regioisomer_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A6.exchanging_dimer_ends_does_not_create_an_isomer' depends on axioms: [propext,
 Quot.sound]
'IChO2026Problems.ProblemIcho2026T9A6.dimer_isomer_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice`, and `Quot.sound` are standard Lean logical
axioms.  There are no custom unchecked axioms.

## Shortcut scan

Command:

```text
grep -nE '^[[:space:]]*(axiom|unsafe)([[:space:]]|$)|\b(sorry|admit)\b' IChO2026Problems/problem_icho_2026_t9_a6.lean
```

Expected and obtained result: exit code 1 with no output, meaning no custom
`axiom`, `unsafe`, `sorry`, or `admit` declaration/use was found.

## Semantic coverage

The final theorem does not assert `3` as a premise.  It defines the two
source-selected primary sites as a finite subtype, proves that subtype has
cardinality two, represents exchange of the two identical dimer ends by
Mathlib's unordered-pair type `Sym2`, proves the end-swap equality, and derives
the final cardinality using `Sym2.card`.

