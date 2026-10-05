# IChO 2026 T8.2 — structures 3–7

The structures are:

```text
3   [(HOCH₂CH₂)₃N]•⁺
                  ↑ the unpaired electron and + charge are on N

4   (HOCH₂CH₂)₂N–ĊH–CH₂OH
                       ↑ radical on the carbon α to N

5   [(HOCH₂CH₂)₂N⁺=CH–CH₂OH]
                    N=C iminium ion

6   HN(CH₂CH₂OH)₂                 diethanolamine

7   HOCH₂–C(=O)H                  glycolaldehyde
```

Any of the three identical hydroxyethyl arms of 2 may be drawn as the arm that
reacts in 4 and 5; these drawings represent the same structure because the
three arms of triethanolamine are symmetry-equivalent. There are no
stereocentres to specify: the radical centre in 4 and the iminium carbon in 5
are not tetrahedral stereocentres, and the remaining carbons are CH₂ or CHO.

## Derivation

Species 2 in the figure is triethanolamine, `N(CH₂CH₂OH)₃`.

1. Removing one electron from the nitrogen lone pair gives the tertiary-amine
   radical cation 3. Its formula remains C₆H₁₅NO₃, its net charge is +1, and it
   has one unpaired electron on N.
2. Loss of H⁺ from a carbon α to N transfers the radical character to that
   carbon and neutralizes the charge, giving 4,
   `(HOCH₂CH₂)₂N–ĊH–CH₂OH` (C₆H₁₄NO₃).
3. Removing the second electron from the α-amino radical gives the iminium
   Lewis structure 5, `[(HOCH₂CH₂)₂N⁺=CH–CH₂OH]` (C₆H₁₄NO₃⁺).
4. Water hydrolyses the iminium C=N bond. The nitrogen fragment becomes
   diethanolamine 6, while the cleaved carbon fragment becomes glycolaldehyde
   7. Across the two neutral products the net printed operation `+H₂O, −H⁺`
   adds one O and one H relative to 5.

The assignment of the product labels is fixed by the last clue: 7 must be the
aldehyde `HOCH₂–C(=O)H`, because its `–CHO` group gives the silver-mirror test;
diethanolamine 6 has no aldehyde carbon.

## Source grounding

- `TASK.json` identifies the requested output as the structures of 3–7 and
  points to printed source page 72.
- `icho_2026_source/image/T8_page-1.png` and PDF page 72 (`Q8-1`) show species 2
  as triethanolamine and print the sequence `−1e⁻`, `−H⁺`, `−1e⁻`, then
  `+H₂O/−H⁺`; they also state that 7 gives a silver mirror.
- The original PDF's student sheet, PDF page 77 (`A8-1`), was inspected. Its
  8.2 area contains five empty boxes labelled 3–7 and supplies no additional
  structural template or stereochemical constraint.
- The mechanistic steps used above are standard general chemistry rules for
  one-electron oxidation of tertiary amines, α-deprotonation of aminium radical
  cations, oxidation to iminium ions, iminium hydrolysis, and the aldehyde
  response in Tollens' test. No answer key, marking scheme, or prior solution
  was used.

The Lean formalization represents every heavy atom as a graph vertex and every
attached hydrogen by an exact count on that vertex. Bond order, formal charge,
unpaired-electron count, and stereochemical annotation are separate data. It
then executes graph rewrites corresponding to the four printed arrows and
proves that their results equal independently written graphs for 3–7. It also
checks local valence, formula, charge, radical count, and the aldehyde subgraph
that distinguishes 7 from 6.
