# Verification for `icho_2026_t8_a9`

This file records the final reproducible checks. The Lean source itself ends
with `#print axioms` commands for the general kinetic identity and the combined
final-output theorem.

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T8_page-5.png icho_2026_source/image/T8_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
2e6c474d4a7e74a268c029c53b69c64eb30e63f58696855bec0e204c0614dad4  icho_2026_source/image/T8_page-5.png
55fc19db05fe771eb0403d5fcf611d83ff5a22882b1221129ef689bd8704285a  icho_2026_source/image/T8_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

## Lean compilation and axiom inspection

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a9.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T8A9.quenchingFraction_eq_dimensionless' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A9.final_quenching_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms; no custom unchecked axiom is present.

## Forbidden-proof-shortcut scan

Command:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|axiom|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t8_a9.lean; then echo 'Forbidden proof shortcut found.'; exit 1; else echo 'No forbidden proof shortcuts found.'; fi
```

Result (exit code 0):

```text
No forbidden proof shortcuts found.
```

## Metadata syntax

Command:

```text
python -m json.tool result.json >/dev/null && echo 'result.json is valid JSON.'
```

Result (exit code 0):

```text
result.json is valid JSON.
```
