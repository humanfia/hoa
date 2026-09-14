# Verification for `icho_2026_t8_a10`

The commands below were run from:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t8_a10/campaign/workspace`

## Source integrity

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-4.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-5.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
55fc19db05fe771eb0403d5fcf611d83ff5a22882b1221129ef689bd8704285a  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-4.png
2e6c474d4a7e74a268c029c53b69c64eb30e63f58696855bec0e204c0614dad4  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T8_page-5.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

These are exactly the hashes recorded in `TASK.json` and
`isolation_manifest.json`.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a10.lean
```

Result (exit code 0):

```text
'IChO2026Problems.ProblemIChO2026T8A10.quenchedLifetime_strictAntiOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIChO2026T8A10.lifetime_s1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T8A10.lifetime_t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T8A10.icho_2026_t8_a10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The output comes from the four `#print axioms` commands in the target file.
Only standard logical axioms are present; in particular, `sorryAx` and custom
unchecked axioms are absent.

## Forbidden-proof-shortcut scan

Command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe|axiom)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t8_a10.lean; then exit 1; else echo 'PASS: no sorry/admit/unsafe/custom-axiom declarations'; fi
```

Result (exit code 0):

```text
PASS: no sorry/admit/unsafe/custom-axiom declarations
```

## Result manifest syntax

Command:

```text
python3 -m json.tool result.json >/dev/null && echo 'PASS: result.json is valid JSON'
```

Result (exit code 0):

```text
PASS: result.json is valid JSON
```

## Semantic coverage

- `DescribesTrend .decreases` is defined as strict antitonicity over all
  nonnegative reductant concentrations, so it is stronger than a comparison at
  just two selected concentrations.
- `quenchedLifetime_strictAntiOn` proves that property algebraically from the
  dynamic-quenching law and positivity of `tau0` and `kq`.
- `lifetime_s1` and `lifetime_t1` instantiate the exact source values in SI
  units and prove the two requested outputs.
- `icho_2026_t8_a10` combines them, matching the single option-(b) checkbox on
  the blank answer sheet.
