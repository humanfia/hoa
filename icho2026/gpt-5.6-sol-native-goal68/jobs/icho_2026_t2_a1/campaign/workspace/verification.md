# Verification: IChO 2026 T2-A1

All commands were run from the workspace root:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t2_a1/campaign/workspace`

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t2_a1.lean
```

Result: exit code 0. Output:

```text
'IChO2026Problems.icho_2026_t2_a1.balanced_bz_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.icho_2026_t2_a1.balanced_overall_shape_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.icho_2026_t2_a1.bz_coefficients_are_the_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are standard Lean logical axioms. In particular, `sorryAx` and any
custom chemistry axiom are absent.

## Proof-shortcut scan

Command:

```text
/usr/bin/grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t2_a1.lean
```

Expected and obtained result: exit code 1 with no output (no matches).

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T2_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0. The obtained hashes exactly match `TASK.json`:

```text
0b9e4e1edf255a14c8def4465de188b6cbd72b9df782a7d7efa32528b15c5ff2  icho_2026_source/image/T2_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

## Result-record validation

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0 with no output; `result.json` is valid JSON.

## Semantic audit

The formal candidate has coefficients `(3,4,9,4,6)` for malonic acid,
bromate, carbon dioxide, bromide, and water. Expanding
`CH2(COOH)2 = C3H4O4` gives reactant/product totals C 9/9, H 12/12,
O 24/24, Br 4/4, and charge -4/-4. The classification theorem derives all
balanced coefficient vectors as whole-number multiples of this vector, and
the minimum theorem proves this is the least positive one. Ce(IV) is stored
in the catalyst set and has coefficient zero on both sides.
