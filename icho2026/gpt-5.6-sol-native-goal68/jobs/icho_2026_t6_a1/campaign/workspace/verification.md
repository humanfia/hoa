# Verification record for `icho_2026_t6_a1`

All commands were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t6_a1/campaign/workspace`

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T6_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0.

```text
29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba  icho_2026_source/image/T6_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These match `TASK.json`. The problem page (PDF page 52) and blank student
answer sheet A6-1 (PDF page 57) were also visually inspected.

## Lean kernel check and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t6_a1.lean
```

Final result: exit code 0.

The file itself executes `#print axioms` on all eight output theorems and the
combined table theorem. Exact output:

```text
'IChO2026Problems.IChO2026T6A1.c18_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.c18_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.c16_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.c16_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.triplet_c13_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.triplet_c13_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.singlet_c13_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.singlet_c13_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.IChO2026T6A1.completed_table' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only standard Lean logical axioms appear. In particular, there is no
`sorryAx`, no `native_decide` implementation axiom, and no custom axiom.

## Shortcut and manifest checks

Commands:

```text
grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t6_a1.lean
python3 -m json.tool result.json > /dev/null
```

Final results: the grep command exited 1 with no matches (successfully showing
that none of the forbidden proof shortcuts occurs), and the JSON validation
command exited 0.

## Semantic audit

- Every requested output has a separate theorem.
- `completed_table` packages the values in the `TASK.json`/A6-1 order.
- The two systems are represented by an exhaustive two-constructor type, so
  the counts are genuinely cardinalities of classified π manifolds.
- `huckelAromatic_iff_four_k_plus_two` and
  `huckelAntiaromatic_iff_four_k` prove that the executable remainder tests are
  equivalent to the stated Hückel forms; the latter excludes the unphysical
  zero-electron anti-aromatic case.
- The chemistry inputs are isolated in `piElectronCount`; all table values are
  derived by proof rather than stated as unchecked axioms.
- The singlet-C₁₃ modeling boundary is disclosed in `answer.md`, the Lean file,
  and `result.json`.
