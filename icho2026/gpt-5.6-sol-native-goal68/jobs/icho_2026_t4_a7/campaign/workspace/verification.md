# Verification for `icho_2026_t4_a7`

Verification is performed from the workspace root.

## Source identity and inspection

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf \
  icho_2026_source/image/T4_page-2.png \
  icho_2026_source/image/T4_page-3.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc  icho_2026_source/image/T4_page-3.png
```

These are the hashes recorded in `TASK.json`.  The two supplied question PNGs
were inspected visually.  The original 93-page PDF was independently opened
and rendered using a temporary PyMuPDF installation.  PDF page 39 is `Q4-3`
and contains T4-A7; page 41 is blank answer sheet `A4-2` with the T4-A6 line;
page 42 is blank answer sheet `A4-3` with the T4-A7 answer line and unit.

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
Build completed successfully (8561 jobs).
```

The build emitted only the pre-existing short-copyright-header lint warnings
for `IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean`.

## Target proof check and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a7.lean
```

Result (exit code 0):

```text
'IChO2026Problems.Icho2026T4A7.methane_combustion_enthalpy_2000_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.Icho2026T4A7.methane_combustion_enthalpy_2000_of_constantCp_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.Icho2026T4A7.methane_combustion_enthalpy_2000_reports_three_sig_figures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.Icho2026T4A7.methane_combustion_enthalpy_2000_submission_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The output comes from the four `#print axioms` commands at the end of the
target file.  Every listed axiom is a standard Lean logical axiom permitted by
the goal; there are no target-defined unchecked axioms.

## Forbidden-proof-token scan

Command:

```text
grep -RInE 'sorry|admit|unsafe|^\s*axiom\b' \
  IChO2026Problems/problem_icho_2026_t4_a7.lean
```

Expected and obtained result: exit code 1 with no output, meaning no match.

## Result metadata validation

Command:

```text
python3 -m json.tool result.json
```

Expected and obtained result: exit code 0; the file parses as JSON.
