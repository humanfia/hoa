# IChO 2026 T8-A4

Let **L** denote neutral tetradentate ligand **8**, drawn with the problem's N4
cartoon.  Thus every formula below contains four L-N→Fe bonds.  The two
remaining octahedral sites are cis; in a five-coordinate species one of those
sites is vacant.  No atom stereocentre or absolute stereochemical descriptor
is specified in the source figure.

## Structures and requested values

| species | structure using the ligand-8 cartoon | OS(Fe) | CN(Fe) | VE(Fe) | Z |
|---:|---|---:|---:|---:|---:|
| **9** | cis-[Fe(L)(OH2)2]^2+ | +2 | 6 | 18 | +2 |
| **10** | [Fe(L)(OH2)]^+ | +1 | 5 | 17 | +1 |
| **11** | [Fe(L)(κ^2-C,O-CO2)]^+, with the chelating CO2 fragment formally CO2^2- | +3 | 6 | 17 | +1 |
| **12** | [Fe(L)-C(=O)-OH]^+ (C-bound hydroxycarbonyl, COOH^-) | +2 | 5 | 16 | +1 |
| **13** | cis-[Fe(L)(OH2)-C(=O)-OH]^+ | +2 | 6 | 18 | +1 |
| **14** | cis-[Fe(L)(OH2)(CO)]^2+, with C-bound CO | +2 | 6 | 18 | +2 |
| **15** | [Fe(L)(OH2)]^2+ | +2 | 5 | 16 | +2 |

The nontrivial connectivities are:

```text
11 (the two displayed Fe bonds occupy the cis labile sites):

          O
          ║
    L4N—Fe—C⁻
          \ /
           O⁻

12: L4N—Fe—C(=O)—OH
13: L4N—Fe(OH2)—C(=O)—OH
14: L4N—Fe(OH2)—C≡O
15: L4N—Fe—OH2
```

Here `L4N—Fe` is only shorthand for all four N→Fe bonds in the mandated
cartoon, not a single bond.  In **11**, Fe is bonded to the carbon and to the
singly bonded oxygen, so the CO2-derived ligand occupies two coordination
sites.  In **12** and **13**, the Fe-C bond is retained but the Fe-O bond is
not.  In **14**, the aqua ligand introduced in 12→13 remains bound while the
COOH group is protonated and loses water to become C-bound CO.

## Derivation

The precursor drawn on Q8-1 is neutral [Fe^II(L)Cl2]: L is a neutral N4 donor
and each chloride is -1.  The first arrow exchanges two Cl^- ligands for two
neutral waters.  Because the two chlorides leave as anions, **9** has charge
+2.  The 9→10 arrow adds one electron and removes neutral water, giving
charge +1 and Fe(I).

The 10→11 arrow removes the other water and adds CO2.  The blank answer sheet
supplies OS(11) = +3 and CN(11) = 6.  Since L already supplies four donors,
CO2 must occupy both remaining sites.  Charge conservation keeps Z = +1, so
the bound CO2 fragment must have ionic charge -2: this is the
κ^2-C,O-CO2^2- structure shown above.  It oxidizes the formal Fe assignment
from +1 to +3 without changing the complex's total charge.

The 11→12 arrow supplies e^- and H^+.  Their charges cancel, so Z remains +1.
Protonation converts the dianionic C,O-bound CO2 fragment into a monoanionic,
C-bound COOH fragment; the supplied CN(12) = 5 confirms loss of the Fe-O
contact.  Consequently Fe is +2.  Water binding gives six-coordinate **13**,
in agreement with the supplied OS(13) = +2.

For 13→14, adding H^+ raises the complex charge from +1 to +2 while neutral
H2O leaves from the COOH group.  The separately coordinated aqua ligand is
retained, giving [Fe(L)(OH2)(CO)]^2+.  CO loss then gives **15** with one aqua
ligand still bound.  This is independently forced by the supplied VE(15) =
16: bare [Fe^II(L)]^2+ would be four-coordinate and only 14-electron, whereas
[Fe^II(L)(OH2)]^2+ is five-coordinate and 16-electron.  Adding water to 15
therefore regenerates 9 exactly.

For every row, the ionic count used is

```text
OS = Z - (sum of ligand ionic charges)
CN = number of Fe-bound donor atoms
VE = (8 - OS) + 2(CN)
```

because Fe is a group-8 metal and all displayed donor atoms contribute a
two-electron pair in ionic counting.  Thus **10** and **11** are the two odd
17-electron species; no ligand-centred radical is introduced.

Summing the arrows from 9 back to 9 also checks the reconstruction: all
spectator waters cancel except one product water, giving

```text
CO2 + 2 H+ + 2 e- → CO + H2O.
```

## Source grounding

- `TASK.json` identifies T8-A4 and requires structures 9-15 plus OS, CN, VE,
  and Z for each.
- `icho_2026_source/raw/theory_problem.pdf`, SHA-256
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`,
  was inspected directly.  Physical page 72 (Q8-1) contains ligand 8, its N4
  cartoon, and the FeCl2 precursor reaction; physical page 73 (Q8-2) contains
  the full 1→9→…→15→9 mechanism and all arrow labels.
- The blank student sheets on physical pages 79-80 (A8-3/A8-4) supply exactly
  OS(11) = +3, CN(11) = 6, CN(12) = 5, OS(13) = +2, and VE(15) = 16.  Those
  fields were used as constraints, not as a solution source.
- The task PNGs were checked against their recorded hashes:
  `T8_page-1.png` is
  `3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843`
  and `T8_page-2.png` is
  `cfd3c6fa64d0126843e3cf65a1235337fa3f869db285f36fbb0a18dddebfacee`.

The only general chemistry conventions used beyond the printed inputs are
charge conservation, the ionic definition of oxidation state, coordination
number as donor-atom count, and standard ionic valence-electron counting.
No official solution, marking scheme, answer repository, or historical answer
was consulted.  There is no source gap needed to determine the requested
outputs.
