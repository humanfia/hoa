# Verification record

Target: `icho_2026_t4_a5`

## Source audit

The SHA-256 checks made against the immutable source assets matched the values
in `TASK.json`:

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  icho_2026_source/image/T4_page-1.png
60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94  icho_2026_source/image/T4_page-2.png
```

Both PNGs were visually inspected at original resolution. The 93-page original
PDF was inspected independently: PDF page 38 contains Q4-2/T4-A5, PDF page 40
contains blank answer sheet A4-1, and PDF page 41 contains blank answer sheet
A4-2 with the `n_c` field. These agree with `TASK.json`; the sheets add no
unstated condition or datum.

## Lean verification

All commands were run from the workspace root.

```text
$ lake build IChO2026Chem.Reporting
⚠ [8558/8558] Built IChO2026Chem.Reporting (11s)
warning: IChO2026Chem/Reporting.lean:1:1: * '-/':
Copyright too short!
Build completed successfully (8558 jobs).
```

The warning is a pre-existing style linter warning in shared infrastructure and
does not concern the target proof.

The target file ends with
`#print axioms IChO2026Problems.T4A5.icho_2026_t4_a5_answer`, so the direct
compilation command also performs the required axiom inspection:

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t4_a5.lean
'IChO2026Problems.T4A5.icho_2026_t4_a5_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit status: `0`. These are standard Lean logical axioms permitted by the goal.
There is no `sorryAx`, no custom axiom, and no `sorry`, `admit`, or `unsafe`
shortcut in the target file.

The declared target module also built successfully:

```text
$ lake build IChO2026Problems.problem_icho_2026_t4_a5
⚠ [8558/8559] Replayed IChO2026Chem.Reporting
warning: IChO2026Chem/Reporting.lean:1:1: * '-/':
Copyright too short!
ℹ [8559/8559] Built IChO2026Problems.problem_icho_2026_t4_a5 (22s)
info: IChO2026Problems/problem_icho_2026_t4_a5.lean:167:0: 'IChO2026Problems.T4A5.icho_2026_t4_a5_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8559 jobs).
```

Exit status: `0`.

## Semantic coverage audit

- Printed values are exact definitions: 2 MeV, 0.012 eV, and 0.948.
- The MeV-to-eV conversion is explicit and proved to produce 2,000,000 eV.
- `averageCollisionCount_satisfies` proves that the raw expression solves the
  constant-decrement equation; `averageCollisionCount_unique` proves no other
  real average count solves it.
- `totalLogDecrement_bounds` uses mathlib's proved bounds for `log 2`, `log 3`,
  and `log 5`, after an exact factorization of the energy ratio. It does not
  postulate a decimal approximation.
- `averageCollisionCount_rounding_interval` proves the raw result lies in
  `(19.95, 20.05)`, and `answerSubmission_valid` proves that reported `20.0`
  with quantum 0.1 meets the shared reporting definition.
- `icho_2026_t4_a5_answer` combines equation satisfaction, uniqueness, and
  reporting validity, covering the one numeric output requested by `TASK.json`.

No source gap was found.
