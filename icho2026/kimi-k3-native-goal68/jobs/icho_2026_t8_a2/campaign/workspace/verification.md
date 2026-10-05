# Verification record for icho_2026_t8_a2 (IChO 2026, T8, subquestion 8.2)

All commands were run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a2/campaign/workspace`.

## Problem inputs read

- `TASK.json` (target metadata, requested outputs structure_3 ... structure_7).
- `icho_2026_source/image/T8_page-1.png` (problem page Q8-1, source page 72):
  the TEOA structure of reductant 2, the mechanism scheme
  `2 --(-1e-)--> [3] --(-H+)--> [4] --(-1e-)--> [5] --(+H2O, -H+)--> 6 + 7`,
  the sentence "Species 3, 4, and 5 are short-lived ionic and radical
  intermediates", and "7 yields a silver mirror with the [Ag(NH3)2]OH test".
- `icho_2026_source/image/T8_page-2.png` ... `T8_page-5.png` (Q8-2 ... Q8-5):
  confirm that no other part of T8 constrains species 3-7.
- `icho_2026_source/raw/theory_problem.pdf` (93 pages), read via PyMuPDF:
  pages 72-76 = Q8-1...Q8-5 (problem), pages 77-83 = A8-1...A8-7 (blank
  student answer sheets).  The answer sheet for 8.2 (A8-1, PDF page 77)
  contains five empty boxes labeled 3, 4, 5, 6, 7 and no other fields; no
  stereochemistry or auxiliary data are requested.  Rendered copy checked at
  150 dpi.

## Build commands and results

1. Direct compilation of the final deliverable:

       lake env lean IChO2026Problems/problem_icho_2026_t8_a2.lean

   Result: exit code 0, no errors, no warnings (no `sorry`).

2. Full project build (includes `IChO2026Problems/All.lean`, which imports the
   deliverable):

       lake build

   Result: "Build completed successfully (8581 jobs)."  The only warning is a
   pre-existing style line-length linter in the fixed umbrella file
   `IChO2026Problems.lean` (not part of this target).

3. Axiom audit.  A temporary file `axcheck.lean` with
   `import IChO2026Problems.problem_icho_2026_t8_a2` and `#print axioms` for
   every final theorem was compiled with

       lake env lean axcheck.lean

   Result (then the temporary file was removed):

   - `teoa_atoms`, `species3_atoms`, `species4_atoms`, `species5_atoms`,
     `species6_atoms`, `species7_atoms`, `step1_atoms_balanced`,
     `step2_atoms_balanced`, `step3_atoms_balanced`, `step4_atoms_balanced`:
     depend on **no axioms at all** (pure computational `rfl` proofs).
   - `species2_closed`, `species3_charge_radical`, `species4_charge_radical`,
     `species5_charge_radical`, `species6_species7_closed`,
     `tollens_implies_aldehyde`, `step1_charge_balanced`,
     `step2_charge_balanced`, `step3_charge_balanced`, `step4_charge_balanced`,
     `radical_fate_through_scheme`, `overall_two_electron_donation`:
     depend on `[propext]` only (introduced by the `≠`/`decide` step inside
     `tollens_implies_aldehyde`; propext is a standard Lean logical axiom).
   - No `sorryAx`, no custom or unchecked axioms anywhere.

## Sanity checks behind the structure data

Every atom inventory used in the formalization was independently checked with
`rfl`-evaluated count theorems for all four elements (C, H, N, O) per species:

- 2 = C6H15NO3 (25 explicit atoms),  3 = C6H15NO3 with N(+1, one radical),
- 4 = C6H14NO3 with alpha-C(radical), 5 = C6H14NO3 with N(+1, N=C double bond),
- 6 = C4H11NO2 (diethanolamine),     7 = C2H4O2 (glycolaldehyde, -CHO
  verified from the explicit bond list).

Step balances proved computationally:

- 2 -> 3 (-1e-): atoms unchanged, charge 0 = (+1) + (-1).
- 3 -> 4 (-H+): atoms 3 = 4 + H+, charge +1 = 0 + (+1).
- 4 -> 5 (-1e-): atoms unchanged, charge 0 = (+1) + (-1).
- 5 + H2O -> 6 + 7 + H+: atoms balance per element, charge +1 + 0 = 0 + 0 + 1.
- Net: 2 + H2O -> 6 + 7 + 2H+ + 2e- (atoms and charge), i.e. the sacrificial
  reductant donates exactly two electrons, matching the 8.1 conjugate
  half-reaction CO2 + 2H+ + 2e- -> CO + H2O.

## Semantic faithfulness check

- Species 3 = radical cation (charge +1 and one unpaired electron on N):
  matches "ionic and radical intermediates" and the first -1e- arrow.
- Species 4 = neutral alpha-amino radical (charge 0, radical on the
  alpha-carbon): matches -H+ from 3 and the radical part of the problem text.
- Species 5 = iminium cation (charge +1, closed shell, N=C double bond):
  matches the second -1e- arrow and the ionic part of the problem text.
- Species 6 = diethanolamine, species 7 = glycolaldehyde: match the
  +H2O/-H+ hydrolysis and, for 7, the stated positive [Ag(NH3)2]OH silver
  mirror test (Tollens: aldehyde); `tollens_implies_aldehyde` proves the
  -CHO fragment from the explicit bond list rather than assuming it.
