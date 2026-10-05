# Verification record — `icho_2026_t7_a7`

## Source inspection

The following problem-only inputs were inspected:

- `GOAL.txt` and `TASK.json`;
- `icho_2026_source/image/T7_page-2.png`;
- `icho_2026_source/image/T7_page-3.png`;
- `icho_2026_source/image/T7_page-4.png`;
- original `icho_2026_source/raw/theory_problem.pdf`, especially PDF page 5
  (G1-5 periodic table), PDF page 66 (Q7-4), and PDF page 71 (A7-5 blank
  answer sheet).

The answer sheet was blank and contained only the four requested slots for
7, 8, 9, and 10. No solution-bearing source was used.

## Lean verification

Dependency build command:

```text
lake build IChO2026Chem
```

Result: exit code 0. It built `IChO2026Chem.Reporting` and
`IChO2026Chem.Core`; only pre-existing style-header warnings were emitted.

Final target command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a7.lean
```

Result: exit code 0. The in-file `#print axioms` checks reported:

```text
'IChO2026Problems.T7A7.nitride_percentages_match_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A7.stoichiometric_mass_ratios_match_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A7.synthesis_atom_balance' does not depend on any axioms
'IChO2026Problems.T7A7.formula10_is_primitive' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T7A7.nitride_charge_neutrality' depends on axioms: [propext]
'IChO2026Problems.T7A7.anion_compositions_forced' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T7A7.icho_2026_t7_a7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib logical axioms. There are no custom axioms.

Shortcut scan command:

```text
grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t7_a7.lean
```

Expected and observed result: exit code 1 with no output, meaning no matching
proof shortcut occurs in the target source.

JSON validation command:

```text
python3 -m json.tool result.json
```

Expected and observed result: exit code 0.

## Semantic verification

- The three exact raw nitrogen percentages lie in the source half-quantum
  intervals for 9.16%, 18.90%, and 39.94%.
- The batch `10 LaN + 6 Ca3N2 + 7 Si3N4 + 5 SiO2` gives raw normalized mass
  ratios 5.089365951…, 2.960758862…, 3.268996505…, and 1, each inside the
  respective printed interval.
- Lean proves componentwise atom conservation to twice
  La5Ca9Si13N25O5, as well as primitiveness of the reduced formula.
- Lean proves the bracket decomposition, neutral formal-charge sum, and the
  uniqueness of `S = O` and `T = SiO3N` under the stated compositional
  monoatomic/tetrahedral constraints.
