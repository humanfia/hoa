# Verification record for `icho_2026_t4_a8`

Verification was performed in the workspace root on 2026-09-13 (UTC).

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T4_page-2.png icho_2026_source/image/T4_page-3.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc  icho_2026_source/image/T4_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These match `TASK.json` and `isolation_manifest.json`.

The original 93-page PDF was inspected directly.  Relevant locations are PDF
page 3 (gas constant), page 4 (ideal-gas and enthalpy equations), pages 38–39
(T4 inputs and T4-A8), and page 42 (blank A4-3 student answer sheet).

## Lean checks

Command:

```text
lake build IChO2026Chem
```

Result: exit code 0, `Build completed successfully (8561 jobs).`  Only
pre-existing short-copyright-header linter warnings were emitted.

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a8.lean
```

Result: exit code 0.  The embedded `#print axioms` commands reported:

```text
'IChO2026Problems.T4A8.reactionEnthalpy2000_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A8.methaneMolesForPrintedVolume_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A8.intendedDailyEnergyRaw_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A8.dailyEnergySubmission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A8.missing_time_basis_changes_daily_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms; there are no custom unchecked axioms.

Command:

```text
lake build IChO2026Problems
```

Result: exit code 0, `Build completed successfully (8564 jobs).`  The target,
the authorized `All.lean` umbrella, and the `IChO2026Problems` library all
built.  The only warnings concerned pre-existing/general header or line-length
lint.

Command:

```text
lake build IChO2026Run
```

Result: exit code 0, `Build completed successfully (8581 jobs).`  The complete
isolated run library built successfully.

Command (final-file rerun after generation of all deliverables):

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a8.lean
```

Result: exit code 0.  It reproduced exactly the five standard-axiom reports
shown above and emitted no errors or warnings.

Command:

```text
lake env lean IChO2026Run.lean
```

Result: exit code 0 with no output.

Command:

```text
! grep -R -n -E '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t4_a8.lean
```

Result: exit code 0 with no output, proving that the target contains none of
the forbidden proof shortcuts or custom `axiom` declarations.

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0 with no output; `result.json` is valid JSON.
