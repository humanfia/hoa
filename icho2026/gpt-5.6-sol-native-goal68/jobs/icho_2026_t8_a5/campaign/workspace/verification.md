# Verification: IChO 2026 T8-A5

All commands below were run from the workspace root:

`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t8_a5/campaign/workspace`

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T8_page-2.png icho_2026_source/image/T8_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
cfd3c6fa64d0126843e3cf65a1235337fa3f869db285f36fbb0a18dddebfacee  icho_2026_source/image/T8_page-2.png
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes match `TASK.json`.

The original PDF was inspected directly. PDF page 73 contains T8-A5, PDF
page 3 contains the physical constants and nanometre conversion, and PDF page
81 is the blank A8-5 student answer sheet.

## Lean build and proof check

The local shared library was first built so its import was available:

```text
lake build IChO2026Chem
```

Result: exit code 0, `Build completed successfully (8561 jobs).` The build
also emitted pre-existing style-linter warnings about short copyright headers
in the shared infrastructure; these do not concern the target proof.

Required final-file command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a5.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T8A5.surfaceDensity_independent_of_sample_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T8A5.catalyst_surface_density_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T8A5.catalyst_surface_density_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the task. In particular,
the audit contains no `sorryAx` and no custom unchecked axiom.

Shortcut scan:

```text
grep -nE '^[[:space:]]*(axiom|unsafe)[[:space:]]|\bsorry\b|\badmit\b' IChO2026Problems/problem_icho_2026_t8_a5.lean
```

Result: no matches. The surrounding audit command converted that expected
`grep` no-match status into overall exit code 0.

## What the proofs establish

- `squareNanometre_conversion` proves the squared unit conversion.
- `oneGram_support_mass` proves the support mass balance implied by the
  printed mass fraction.
- `surfaceDensity_independent_of_sample_mass` proves that the arbitrary sample
  basis cancels for every positive total mass.
- `catalyst_surface_density_exact` proves the unrounded exact value
  $5720900000/2385360289$.
- `catalyst_surface_density_rounding_bounds` proves that this exact value is
  in the half-open 0.01-wide rounding bin centered on 2.40.
- `catalyst_surface_density_reported` packages those facts as a valid numeric
  submission with raw and reported values kept separate.
