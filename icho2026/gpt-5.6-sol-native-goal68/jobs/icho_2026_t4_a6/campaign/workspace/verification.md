# Verification for `icho_2026_t4_a6`

Verification date: 2026-09-13 (UTC).

## Source verification

Command:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T4_page-1.png icho_2026_source/image/T4_page-2.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  icho_2026_source/image/T4_page-1.png
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
```

These hashes match `TASK.json`. Both listed question images were inspected.
The original 93-page PDF was independently opened and inspected: one-based
page 38 contains Q4-2 and the thermodynamic table for 4.6; one-based page 41
is the blank A4-2 student answer sheet and contains the sole 4.6 field
`Delta_r H_298 = ____ kJ mol^-1`. The neighboring T4 pages were also checked
for context. The red `-750 kJ mol^-1` on Q4-2 is expressly a fallback for
later parts, not the answer to 4.6.

## Lean dependency build

Command:

```text
lake build IChO2026Chem
```

Result (exit code 0):

```text
⚠ [8558/8561] Replayed IChO2026Chem.Core
warning: IChO2026Chem/Core.lean:1:1: * '-/':
Copyright too short!
⚠ [8559/8561] Replayed IChO2026Chem.Reporting
warning: IChO2026Chem/Reporting.lean:1:1: * '-/':
Copyright too short!
Build completed successfully (8561 jobs).
```

The warnings belong to unchanged shared infrastructure and do not affect the
target proof.

## Required direct Lean check and axiom audit

The final target file contains `#print axioms` commands for every theorem.

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a6.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T4A6.methane_combustion_is_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A6.methane_combustion_hess_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A6.combustion_enthalpy_298_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A6.combustion_enthalpy_298_reporting_scale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T4A6.combustion_enthalpy_298_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T4A6.combustion_enthalpy_298_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All dependencies shown are standard Lean logical axioms. There are no custom
unchecked axioms.

## Prohibited-shortcut scan

Command:

```text
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe|axiom)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t4_a6.lean; then exit 1; else echo 'No forbidden proof shortcuts found.'; fi
```

Result (exit code 0):

```text
No forbidden proof shortcuts found.
```

## Metadata validation

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0; `result.json` is valid JSON.

## Semantic completion audit

- The formal species and coefficients encode exactly
  `CH4(g) + 2 O2(g) -> CO2(g) + 2 H2O(g)`, and
  `methane_combustion_is_balanced` proves atom conservation for C, H, and O.
- `problemThermodynamicData` transcribes every entry of the printed 4.6 table.
  The three relevant formation enthalpies are not inferred or fitted.
- `oxygenStandardFormationEnthalpy` separately records the standard
  reference-state convention `Delta_f H degrees(O2(g)) = 0`; it is not
  presented as a printed input.
- `methane_combustion_hess_expansion` proves that the formal Hess sum has the
  correct product-minus-reactant stoichiometry.
- `combustion_enthalpy_298_raw` proves the exact raw value `-8023/10`, i.e.
  `-802.3 kJ mol^-1`, without intermediate rounding.
- `combustion_enthalpy_298_reporting_scale` proves that the raw magnitude lies
  between 100 and 1000 and that the selected three-significant-figure quantum
  is 1 kJ mol^-1.
- `combustion_enthalpy_298_reported` proves that `-802 kJ mol^-1` satisfies the
  shared nearest-quantum, ties-away-from-zero reporting relation.
- `combustion_enthalpy_298_answer` packages the exact raw result, displayed
  result, and validity proof as the complete requested numerical output.

No requested output is missing, and no source gap remains.
