# IChO 2026 — Problem T3, subquestion 3.5 (target `icho_2026_t3_a5`)

**Question (source: `theory_problem.pdf`, printed page Q3-5 = PDF page 29 = image
`T3_page-5.png`, with the monomer library on page Q3-3 = `T3_page-3.png`):**

> Macrocycle **X** was synthesised by post-synthetic modification of **COF-7 (C2 + D4)** followed by degradation.
> **3.5 Draw** the smallest repeat unit of macrocycle **X**. (6.0 pt)

The bundle is problem-only (93 PDF pages, all "Q…" problem pages; no answer key or
worked solutions, consistent with the answer-blind protocol in `TASK.json`), so the
structure below is derived entirely from the printed structures and reaction scheme,
using standard condensation/oxidation chemistry (trusted general laws).

---

## 1. What the scheme shows (source grounding)

### Monomer C2 — the black building block

Reading the high-resolution structure on page 29: two identical
**1,3-bis(4-aminophenyl)benzene** halves joined **by a central C=C double bond
between the two remaining (5- and 5′-) positions** — i.e. a stilbene:
**(E/Z)-1,2-bis[3,5-bis(4-aminophenyl)phenyl]ethene**, formula C₃₈H₃₂N₄ (DBE check:
(2·38+2+4−32)/2 = 25 = 6 benzene rings × 4 + 1 C=C ✓). C2 is a **4-connector**:
each central phenylene carries two aniline arms, and the two arms of one half leave
their ring at the 3- and 5-positions (≈120° apart); the two halves are held together
solely by the stilbene C=C bond.

### Monomer D4 — the red building block

**2,3,5,6-tetrafluoroterephthalaldehyde**: a benzene ring bearing CHO at positions
1 and 4 and F at 2, 3, 5 and 6; formula C₈H₂F₄O₂ — a **linear 2-connector** with
**no aryl H**.

### COF-7 (arrow labelled AcOH)

Acid-catalysed imine condensation: each aldehyde of D4 condenses with one aniline
NH₂ of C2, giving an **aldimine –CH=N–** (C on the D4 side, N–aryl on the C2 side)
plus H₂O. The tetratopic C2 nodes (degree 4) linked by linear D4 edges give the
**Kagome** lattice — exactly the combination pre-printed in the topology table on
page Q3-4 ("Kagome: **C2 + D4**") and drawn as the COF-7 scheme (black X-nodes =
C2, red edges = D4). Ratio 1 C2 : 2 D4; each formula cell
C2 + 2·D4 − 4·H₂O = **C₅₄H₂₈F₈N₄**, with four imine –CH=N– linkages per cell.

### Sequence overview

```
C2 (ArCH=CHAr core, 4 x NH2 arms)  +  D4 (2,3,5,6-F4-C6(CHO)2)
      |  AcOH, imine condensation, -4 H2O per cell
      v
COF-7 : Kagome lattice,   ...N=CH-C6F4-CH=N...   (imine edges)
      |  NaClO2 / NaH2PO4   (Pinnick: aldimine -> amide)
      v
amide-linked COF,         ...NH-C(=O)-C6F4-C(=O)-NH...   (C=C still intact)
      |  1) O3  2) Me2S     (ozonolysis, reductive work-up)
      v
X : macrocycle - the stilbene C=C of every C2 node cleaved to 2 x CHO
```

---

## 2. The two post-synthetic steps (trusted general chemistry)

1. **NaClO2 / NaH2PO4 (Pinnick-type oxidation).** Chlorite under buffered acidic
   conditions oxidises aldehydes **and aldehyde-derived aldimines**
   (Ar–CH=N–Ar′ → Ar–C(=O)–NH–Ar′); aryl C–F bonds, aromatic rings and the
   stilbene C=C of the node survive. COF-7 is thereby converted **in place** into
   an **amide-linked** framework: every edge is then
   Ar(C2)–NH–C(=O)–C₆F₄–C(=O)–NH–Ar(C2), and node integrity still relies on the
   stilbene double bond.

2. **O3, then Me2S (ozonolysis with reductive work-up — the "degradation").**
   Alkene ozonolysis followed by dimethyl sulfide converts Ar–CH=CH–Ar into
   **two aldehydes, Ar–CHO** (standard rule; Me2S is a reductive work-up, so the
   products are aldehydes, not acids or alcohols). The only non-aromatic C=C
   bonds in the framework are the stilbene bonds of the C2 nodes, so ozonolysis
   **cuts every C2 node into two identical halves**, each half being a
   5-formyl-1,3-phenylene carrying two 4-(amide-linked)aniline arms,
   C₁₉H₁₄N₂O.

**What survives the cut.** In the Kagome net each degree-4 vertex uses two pairs
of adjacent edges: the pair of edges bound by a 120° vertex wedge belongs to a
hexagonal pore, while the two 60° wedges belong to triangles. After ozonolysis
the two arms that remain covalently connected at a former node are exactly the
pair carried by **one benzene half of C2** — a ≈120°-spread pair — so the closed
covalent loops that survive are the **hexagonal-pore perimeters** of the Kagome
net: COF-7 disintegrates into discrete rings made of **6 C2-halves alternating
with 6 D4 linkers**. That cyclic oligomer is macrocycle **X**, formula
(C₂₇H₁₄F₄N₂O₃)₆ = **C₁₆₂H₈₄F₂₄N₁₂O₁₈**.

*(The smallest repeat unit asked for in 3.5 is one single C2-half + D4 motif; it
is the same object whatever the ring size.)*

---

## 3. Answer: smallest repeat unit of macrocycle X

**One C2-half plus one D4 linker**, joined by the two amide bonds created by the
Pinnick step and bearing the aldehyde created by ozonolysis. Along the ring (one
period, amide N → next amide N):

```
                      CHO                         <- formed by ozonolysis of C=C
                       |
   -NH-C(=O)-C6F4-C(=O)-NH-(1,4-C6H4)-[1,3,5-C6H3(CHO)]-(1,4-C6H4)-
   |_______________________ one period _______________________|
```

As a structural sketch of the period (dashed bonds = continuation around the
macrocycle, in the same convention as the COF-1 dashed-line example printed in
part 3.4):

```
                                O
                                ||
                                C-H            aldehyde on the central ring
                                |
        .............  (1,3,5-C6H3) .............
       /                                             \
  (1,4-C6H4)                                    (1,4-C6H4)
       |                                             |
      NH                                            NH      former imine N atoms
       |                                             |
     C(=O)- - - - (2,3,5,6-F4-C6) - - - - C(=O)     D4 ring, F at 2,3,5,6
       |________________ dashed edges continue around X ________________|
```

* the **central 1,3,5-trisubstituted benzene** (from one half of C2) carries the
  **CHO group at position 1** and the two arm phenylenes at positions 3 and 5;
* each **arm is a 1,4-phenylene** terminated by an **amide N–H** (the former
  aniline/imine nitrogen);
* the **D4 residue is 2,3,5,6-tetrafluorobenzene-1,4-diyl-bis(carbonyl)**, both
  carbonyls produced by the Pinnick step, all four F atoms retained;
* the period closes onto the next C2-half through the shared amide nitrogen: the
  blocks strictly alternate C2-half / D4 around the ring.

**Repeat-unit formula (verified in Lean): C₂₇H₁₄F₄N₂O₃.**

**Minimality.** Around the macrocycle the building blocks strictly alternate
half(C2), D4, half(C2), D4, …: two C2-halves are never adjacent (every aniline
N of a C2-half is bonded to a D4 carbonyl carbon) and two D4 rings are never
adjacent (every carbonyl carbon of a D4 is bonded to a C2 aniline nitrogen). Any
contiguous period of the ring therefore contains at least one C2-half and one D4
unit; the motif above realises exactly that bound, and any smaller fragment would
have to sever a covalent amide bond, so it is the **smallest** repeat unit. X is
then the cyclo-oligomer (C₂₇H₁₄F₄N₂O₃)ₙ with n = 6 repeats for the Kagome
hexagonal-pore ring.

---

## 4. Independent stoichiometric cross-check (proved in the Lean file)

Material balance per pair of repeat units, from the printed monomers:

```
C2 (C38H32N4)  +  2 D4 (C8H2F4O2)  +  6 [O]
      =  2 x repeat-unit (C27H14F4N2O3)  +  4 H2O
```

C: 38+16 = 54 = 2×27 ✓ · H: 32+4 = 36 = 28+8 ✓ · N: 4 = 2×2 ✓ · F: 8 = 2×4 ✓
O: 4+6 = 10 = 2×3+4 ✓ — the four H₂O of imine condensation, the four oxygen
atoms of the Pinnick imine→amide oxidation and the two oxygen atoms of
ozonolysis are all accounted for. The Lean file verifies this balance and every
fragment composition by explicit atom-level enumeration of the printed
structures, and encodes the alternating-block structure and its minimality as a
proved circular-word argument.

## Assumptions and source gaps

* Trusted general laws used: aldimine condensation
  (–CHO + H₂N– → –CH=N– + H₂O); Pinnick oxidation of aldimines to amides;
  ozonolysis/Me₂S of a stilbene C=C giving two aldehydes; inertness of aryl C–F
  bonds and aromatic rings to all three steps. These are standard organic
  chemistry rules, not competition answers.
* Figure-derived inputs: constitutions of C2 and D4 (read directly from the
  printed structures on Q3-5), the Kagome topology of COF-7 (printed scheme plus
  the pre-printed "C2 + D4 → Kagome" table entry on Q3-4), and the reagent
  sequence (printed arrows).
* The bundle contains no answer sheet or worked solution for 3.5; nothing beyond
  the printed problem material was consulted.
