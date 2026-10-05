# IChO 2026, Problem T8 (Recycling of Carbon Dioxide), Subquestion 8.2 (part_id T8-A2)

## Question (problem page Q8-1 / source page 72 / `T8_page-1.png`)

The conjugate oxidation reaction occurs with sacrificial reductant **2** in
aqueous solution with the following mechanism:

    2  --(-1e-)-->  [3]  --(-H+)-->  [4]  --(-1e-)-->  [5]
       --(+H2O, -H+, equilibrium)-->  6 + 7

Species **3**, **4**, and **5** are short-lived ionic and radical
intermediates. **7** yields a silver mirror with the [Ag(NH3)2]OH test.
Compound **2** is drawn on the same figure as the tertiary amine with three
2-hydroxyethyl arms, N(CH2CH2OH)3 (triethanolamine, TEOA), C6H15NO3.

Command: **Draw** the structures of **3-7**. (16.0 pt)

## Answer

| Species | Structure (condensed) | Formula | Charge | Radical? | Identity |
|---------|-----------------------|---------|--------|----------|----------|
| **3** | [N(CH2CH2OH)3]+ radical | C6H15NO3 | +1 | yes (radical cation) | TEOA radical cation |
| **4** | (HOCH2CH2)2N-CH(*)-CH2OH | C6H14NO3 | 0 | yes (alpha-amino radical) | TEOA minus one alpha H+ |
| **5** | [(HOCH2CH2)2N=CH-CH2OH]+ | C6H14NO3 | +1 | no | iminium ion |
| **6** | HN(CH2CH2OH)2 | C4H11NO2 | 0 | no | diethanolamine (DEOA) |
| **7** | HO-CH2-CHO | C2H4O2 | 0 | no | glycolaldehyde |

Structure drawings (line descriptions):

- **3**: N(CH2CH2OH)3 with a (+) on N and one radical dot: the one-electron
  oxidation product of **2**.  Skeletal formula unchanged relative to **2**;
  N bears the positive charge and the unpaired electron.
- **4**: (HOCH2CH2)2N-CH(*)-CH2OH : H+ (the alpha-C-H proton) removed from
  one arm of **3**; the unpaired electron sits on the alpha-carbon, N is now
  neutral and three-coordinate.
- **5**: [(HOCH2CH2)2N=CH-CH2OH]+ : a second one-electron oxidation converts
  the alpha-amino radical **4** into an iminium, an N=CH double bond between
  the former radical carbon and nitrogen.  All six carbons are still present.
- **7**: HOCH2-CHO (O=CH-CH2OH), the aldehyde.  It gives the Tollens
  silver-mirror test stated in the problem ([Ag(NH3)2]OH oxidises aldehydes
  to carboxylates while depositing metallic Ag).
- **6**: HN(CH2CH2OH)2, the secondary amine diethanolamine left over after
  the iminium arm is hydrolysed off.

## Derivation from the problem constraints (no external answer source used)

Every step uses only the problem figure/text and standard general chemistry
(mass/charge conservation, reductive quenching by tertiary amines, iminium
hydrolysis, Tollens' test).

1. **2 -> 3 (loss of 1e-)**: species **3** is stated to be a short-lived
   ionic *and* radical intermediate formed by loss of one electron from the
   tertiary amine **2**.  One-electron oxidation of an amine removes an
   electron from the nitrogen lone pair, giving the amine radical cation
   [N(CH2CH2OH)3]+ (charge +1, one unpaired electron, formula C6H15NO3).

2. **3 -> 4 (loss of H+)**: an amine radical cation is a strong alpha-C-H
   acid; deprotonation alpha to nitrogen gives a neutral alpha-amino
   radical.  Formula C6H14NO3, charge +1 - 1 = 0, still one unpaired
   electron: (HOCH2CH2)2N-CH(*)-CH2OH.  Deprotonation at O-H instead would
   leave no route to a second oxidation that keeps six carbons and ends in a
   secondary amine plus a Tollens-positive two-carbon fragment.

3. **4 -> 5 (loss of 1e-)**: a second one-electron oxidation of the
   alpha-amino radical gives the closed-shell iminium cation; the C(alpha)-N
   bond order rises from 1 to 2, N becomes four-coordinate with formal
   charge +1: [(HOCH2CH2)2N=CH-CH2OH]+, formula C6H14NO3, charge +1, no
   radical.  Together the three intermediates are exactly "ionic and radical
   intermediates": 3 = ionic radical, 4 = neutral radical, 5 = ionic.

4. **5 + H2O -> 6 + 7 (loss of H+)**: water adds to the iminium carbon, a
   proton is lost, and the C-N bond cleaves (standard iminium hydrolysis):
   [(R2N=CH-CH2OH)]+ + H2O -> R2NH + HOCH2-CHO + H+ with R = CH2CH2OH.
   Hence **6** = HN(CH2CH2OH)2 (C4H11NO2) and **7** = HOCH2-CHO (C2H4O2).
   Atom and charge check: C4H11NO2 + C2H4O2 + H+ = C6H16NO5+ =
   C6H14NO3 + H2O, and 0 + 0 + (+1) = +1.

5. **7 gives a silver mirror with [Ag(NH3)2]OH (Tollens' test)**: the
   classical selective test for aldehydes.  HOCH2-CHO is an aldehyde; the
   carbonyl carbon of **7** carries a C-H bond (-CHO), i.e. the iminium
   carbon of **5** becomes the aldehyde carbon of **7**.  This constraint is
   what fixes **7** as glycolaldehyde rather than any other C2H4O2 isomer.

## Overall bookkeeping

- Species charges: 2 = 0, 3 = +1, 4 = 0, 5 = +1, 6 = 0, 7 = 0.
- Step balances (electron counted as one H atom, the standard
  electron-balance convention since the H atom = proton + electron):
  2 = 3 + e-; 3 = 4 + H+; 4 = 5 + e-; 5 + H2O = 6 + 7 + H+.
- Net: 2 + H2O -> 6 + 7 + 2 H+ + 2 e-: the sacrificial reductant is
  oxidised by two electrons to diethanolamine + glycolaldehyde, exactly the
  two electrons demanded by the 8.1 half-reaction,
  CO2 + 2 H+ + 2 e- -> CO + H2O.  This is what "the conjugate oxidation
  reaction" requires stoichiometrically.

## Source grounding

- Single problem page asset: `icho_2026_source/image/T8_page-1.png`
  (sha256 3490231d..., source page 72 of `theory_problem.pdf`).  The
  structure of **2**, the four arrows with their reagent labels
  (-1e-, -H+, -1e-, +H2O/-H+), the sentence "Species 3, 4, and 5 are
  short-lived ionic and radical intermediates", and the Tollens statement
  about **7** all come from this one page; nothing else in the T8 pages
  constrains species 3-7.  The student answer area for 8.2 requests drawn
  structures and asks for no stereochemistry (no stereocentres exist in
  these small acyclic species).
- General chemistry laws used (allowed as trusted general law): amine
  one-electron oxidation -> radical cation; alpha-deprotonation of amine
  radical cations -> alpha-amino radicals; second oxidation -> iminium
  ions; iminium hydrolysis -> secondary amine + aldehyde; Tollens reagent
  as an aldehyde test.
- Forced representation choice: the deprotonation site of **4** (alpha-C-H)
  is forced by steps 3-5: only the alpha-deprotonated radical can be
  oxidised to a species that hydrolyses to a secondary amine plus a
  Tollens-positive two-carbon aldehyde while keeping six carbons in **5**.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t8_a2.lean` represents every atom,
bond (with order), charge and radical count explicitly using an inductive
`Element`, an `Atom` record (element + formal charge + radical count) and
a `Bond` triple (two atom indices + order), and proves:

- `species3_atoms` ... `species7_atoms`: each structure proposal binds the
  exact element multisets C6H15NO3, C6H14NO3, C6H14NO3, C4H11NO2, C2H4O2,
  with per-atom charge/radical records on every explicit atom.
- `step1_atoms_balanced` ... `step4_charge_balanced`: all four elementary
  steps of the scheme conserve C, H, N, O and total charge (each -1e- arrow
  implemented as m1 = m2 + 1: one electron leaves the molecular system).
- `overall_two_electron_donation`: the net reaction
  2 + H2O -> 6 + 7 + 2H+ + 2e-, matching the 8.1 two-electron reduction.
- `tollens_implies_aldehyde`: species 7 contains a carbon bearing both a
  double bond to O and a single bond to H (the -CHO group detected by
  [Ag(NH3)2]OH), read off the recorded explicit bonds rather than assumed.
- `species*_charge` / `step1_radical_preserved` ... : the ionic/radical
  classification stated in the problem is verified against the structures:
  3 ionic + radical, 4 neutral radical, 5 ionic closed-shell, 6 and 7
  neutral closed-shell.

See `verification.md` for the exact build commands and axiom audits.
