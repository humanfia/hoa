# Verification for `icho_2026_t4_a4`

## Source integrity

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

These exactly match `TASK.json`.

## Lean prerequisite build

Command:

```text
lake build IChO2026Chem
```

Result: exit code 0; `Build completed successfully (8561 jobs).` The only messages were pre-existing short-copyright-header lint warnings in `IChO2026Chem/Core.lean` and `IChO2026Chem/Reporting.lean`.

## Final target verification and axiom inspection

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a4.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T4A4.DerivedChannel.commonFission_massNumberBalanced' depends on axioms: [propext]
'IChO2026Problems.T4A4.DerivedChannel.commonFission_atomicNumberBalanced' depends on axioms: [propext]
'IChO2026Problems.T4A4.answer_fission_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` commands are part of the final Lean file. The output contains only standard Lean logical axioms allowed by the goal; there is no `sorryAx` and no custom unchecked axiom.

## Proof-safety scan

Command:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t4_a4.lean
```

Result: exit code 1 with no output, as expected for an empty match set. None of the forbidden proof shortcuts occurs in the formalization.

## Semantic coverage

The checked theorem chain proves:

1. the derived (^{235}\mathrm U+n\to{}^{93}\mathrm{Rb}+{}^{140}\mathrm{Cs}+3n) channel conserves mass number and atomic number;
2. the two bound fragments contain 233 nucleons;
3. initial and final binding energies are exactly 1783.65 and 1968.85 MeV;
4. their exact difference is 185.20 MeV (equivalently (926/5\) MeV); and
5. 185 MeV is a valid one-MeV-quantum report, i.e. the target's three-significant-figure output.
