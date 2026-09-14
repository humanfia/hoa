# Verification: IChO 2026 T8-A1

Verification was performed in the workspace root on 2026-09-13 (UTC).

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T8_page-1.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

Both hashes equal the values recorded in `TASK.json`. Direct visual inspection
confirmed Q8-1 on PDF page 72 and the empty 8.1 response box on answer sheet
A8-1, PDF page 77.

## Lean verification

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t8_a1.lean
```

Result: exit code 0, with the following output produced by the file's
`#print axioms` commands:

```text
'IChO2026Problems.ProblemIChO2026T8A1.submittedHalfEquation_balanced' does not depend on any axioms
'IChO2026Problems.ProblemIChO2026T8A1.submittedHalfEquation_isReduction' does not depend on any axioms
'IChO2026Problems.ProblemIChO2026T8A1.balanced_normalized_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.ProblemIChO2026T8A1.icho_2026_t8_a1' does not depend on any axioms
```

`propext`, `Classical.choice`, and `Quot.sound` are standard Lean logical
axioms used by Mathlib automation. There are no custom unchecked axioms.

Shortcut scan command:

```text
grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t8_a1.lean
```

Result: no output and exit code 1, confirming that no forbidden proof
shortcuts or custom axiom declarations were found.

Manifest validation command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: no output and exit code 0.

## Semantic audit

The formal species table assigns CO2 the atom vector `(C,H,O) = (1,0,2)`, CO
the vector `(1,0,1)`, H2O `(0,2,1)`, H+ `(0,1,0)` with charge `+1`, and e-
`(0,0,0)` with charge `-1`. For submitted coefficients `(1,2,2,1,1)`, the Lean
theorems prove equality of all three atom totals and equality of total charge.
The positive coefficient 2 for reactant electrons establishes the requested
reduction direction. The uniqueness theorem independently derives all five
coefficients from those conservation equations and the conventional
normalization `CO2 = 1`; it does not assume the target tuple as a premise.
