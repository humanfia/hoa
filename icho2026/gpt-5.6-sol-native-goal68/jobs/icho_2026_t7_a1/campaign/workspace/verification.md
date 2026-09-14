# Verification record for `icho_2026_t7_a1`

The Lean source contains `#print axioms` commands for all three final theorems, so the compiler run below checks the proofs and prints their complete axiom dependencies in one pass.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a1.lean
```

Result: exit code `0`.

```text
'IChO2026Problems.Icho2026T7A1.gases_m1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T7A1.gases_m2' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T7A1.xy_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical/quotient axioms; there are no custom unchecked axioms.

## Forbidden-shortcut scan

Command:

```text
if grep -nE '\b(sorry|admit|axiom|unsafe)\b' IChO2026Problems/problem_icho_2026_t7_a1.lean; then
  echo 'Forbidden proof shortcut token found'
  exit 1
else
  echo 'No sorry/admit/axiom/unsafe tokens found.'
fi
```

Result: exit code `0`.

```text
No sorry/admit/axiom/unsafe tokens found.
```

## Result manifest validation

Command:

```text
python -m json.tool result.json >/dev/null && echo 'result.json: valid JSON'
```

Result: exit code `0`.

```text
result.json: valid JSON
```

## Source identity

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T7_page-1.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result: exit code `0`.

```text
ee7fe1adff7ac3aae8701bf684981bd2b1e21b28f1c9e4b21dd9c38c3bdb79ad  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T7_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

## Semantic audit

- `gases_m1` computes the oxidation-stage outlet from the two source-labeled feeds and the printed quantitative oxidation reaction; it proves exactly `{CO, H2, N2}`.
- `gases_after_shift` independently reproduces the next stream label `{N2, CO2, H2}`, checking the M1 computation against another part of Fig. 1.
- `gases_m2` first proves that scrubbing leaves `{N2, H2}`, then uses the stated non-quantitative ammonia stage and explicit recycle/output labels to prove exactly `{N2, H2, NH3}`.
- `xy_relation` does not assume `x > y`. It derives it from quantitative 1:1 reaction extent `min(x,y)` and the diagram's exact reformer-outlet support. `reformer_source_consistent` supplies a concrete witness, showing the premise is not vacuous.
- The theorem conclusions match all three requested outputs without numerical tolerances, weakened containments, or extra gas species.
