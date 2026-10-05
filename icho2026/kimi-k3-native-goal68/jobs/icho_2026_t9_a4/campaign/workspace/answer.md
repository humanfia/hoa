# IChO 2026 — Problem T9, subquestion 9.4 (target `icho_2026_t9_a4`)

## What the problem asks

> **9.4 Draw the structure of Y with stereochemistry by completing the CD template.** (3.0 pt)

Source: `theory_problem.pdf`, printed page 2 (question page Q9-2 / PDF page 85), scheme
"alpha-Cycloaltrin, a synthetic analogue of alpha-CD, was synthesised as follows",
together with the blank answer sheet A9-2, which shows the CD-template chair to be
completed and the label **Y - C72H132O24Si6** (page images T9_page-1.png, T9_page-2.png;
PDF pages 85 and 90).

## English rendering of the scheme (grounded in the figures)

```
        alpha-CD  --1) TBSCl (6 equiv.), Py-->  Y  --1) t-Bu4NF----->  alpha-cycloaltrin
                    2) NaH (12 equiv.)  (C72H132O24Si6)   2) H2O, 100 C
                    3) TsCl (6 equiv.)
```

The starting drawn material is alpha-CD (bracket subscript 6, all-glucose units: OH at C2
and C3 shown below the ring in the standard alpha-D-gluco chair, CH2OH at C6 drawn up).
The legend defines TBSCl = Cl-Si(CH3)2-C(CH3)3; the TBS group is Si(CH3)2(C(CH3)3) and
t-Bu = C(CH3)3. The product of the second arrow, alpha-cycloaltrin, is drawn as the same
six-unit macrocycle whose chair shows the 2-OH **axial (down)**, the 3-OH **up**
(hydrogen bond drawn to the ring oxygen O5), and CH2OH up: the alpha-D-altropyranoside
pattern - the C2 stereocentre of each glucose unit has been inverted, everything else
unchanged.

## Reasoning (answer-blind derivation)

Per alpha-D-glucopyranoside unit of alpha-CD the free OH groups are the primary C6-OH and
the secondary O2-H and O3-H.

1. **TBSCl (6 equiv.), Py.** Exactly one TBSCl per unit. The problem statement itself
   says "Primary and secondary hydroxy groups show different reactivity due to being a
   part of CDs"; with the bulky silyl chloride the primary C6-OH reacts first (standard
   selectivity of TBSCl/Py: primary before secondary). So the six C6-OH groups are
   silylated: C6 -> CH2-O-TBS. The secondary 2-OH and 3-OH stay free for step 2.

2. **NaH (12 equiv.), then TsCl (6 equiv.).** NaH (2 per unit) deprotonates both
   secondary hydroxy groups (2-O- and 3-O- alkoxides). TsCl (1 per unit) tosylates only
   **O3**: the neighbouring alkoxide directs mono-tosylation, and the printed product
   discloses the outcome - the C2 centre is inverted in alpha-cycloaltrin. The only
   course consistent with the 12/6 equivalences and that inversion is the Sinay-type
   intramolecular epoxidation: the 2-alkoxide displaces the 3-OTs intramolecularly
   (trans-diaxial SN2), closing a **2,3-anhydro (allopyranoside) ring** across O3-C2-C3
   with inversion at both epoxide carbons relative to glucose; C6 stays CH2OTBS. No free
   OH remains in Y.

   Formula audit against the printed Y = C72H132O24Si6. alpha-CD is C36H60O30
   (6 x C6H12O6 minus 6 H2O for the six 1,4-glycosidic links). Per unit, epoxide Y is
   counted term by term (done formally in Lean): ring carbons O5-C1..C5-C6 with the
   epoxide oxygen and the CH2OTBS arm give the clean per-unit count **C12H22O4Si**; six
   units give exactly **C72H132O24Si6**, the formula printed under Y on both Q9-2 and
   answer sheet A9-2. This atom-by-atom identity is a checkable fingerprint of the
   hexa-TBS 2,3-anhydro structure.

3. **Y -> alpha-cycloaltrin (printed sequel, used only as a consistency test).** t-Bu4NF
   removes the six TBS groups; H2O at 100 C opens each 2,3-anhydro ring by backside
   attack of water at C2 (trans-diaxial Fuerst-Plattner opening), installing the new OH
   at C2 axial (down) and restoring OH at C3 up - net double inversion at C2: a glucose
   to **altrose** configurational change at every unit. The drawn alpha-cycloaltrin
   (2-OH axial down, 3-OH up, CH2OH up) matches exactly, confirming the epoxide
   assignment.

## The structure of Y (answer)

**Y = hexakis(6-O-tert-butyldimethylsilyl)-2,3-anhydro-alpha-cyclodextrin**: the
alpha-CD macrocycle of six sugar units, in which **for every unit**

* C6 carries **CH2-O-Si(CH3)2C(CH3)3** (C6-O-TBS), the C5/C6 geometry as in the starting
  glucose (CH2OR arm up);
* the 2-OH and 3-OH have been replaced by a **2,3-epoxide** (oxirane fused across the
  C2-C3 bond, O3 as the bridge oxygen): a three-membered C2-O-C3 ring;
* configuration at **C2 and C3 is inverted** relative to alpha-CD (both new C-O bonds
  lie on the upper face of the ring; on the printed template the epoxide O and the two
  C-O bonds are drawn bold/wedged toward the viewer, while C2-H and C3-H point down) -
  the **allo** pattern that becomes altrose after the printed hydrolytic opening;
* C1 (alpha-glycosidic bond to the next unit), C4 (glycosidic O linkage) and C5 (ring
  oxygen, CH2OTBS arm) are **unchanged** from alpha-CD;
* no free OH group remains; each of the six silicons carries two methyls and one
  tert-butyl (TBS = SiMe2-t-Bu).

On the A9-2 CD template this is drawn by writing the C6 arm as -CH2-O-TBS (up) and the
bold three-membered O-bridge between C2 and C3, six times around the macrocycle
(subscript 6 retained). The per-unit composition C12H22O4Si reproduces the printed
formula C72H132O24Si6 exactly.

## Grounding notes

* Starting-material identity (all-glucose alpha-CD, six units) and the legends TBSCl and
  t-Bu are read directly from the scheme and its legend boxes (page Q9-2).
* The silylation regioselectivity uses the problem's own sentence "Primary and secondary
  hydroxy groups show different reactivity due to being a part of CDs" together with the
  count "TBSCl (6 equiv.)".
* The 2,3-anhydro intermediate, the inversion at C2/C3, and the glucose-to-altrose
  change are forced jointly by (i) the equivalence counts 6/12/6, (ii) the printed
  formula C72H132O24Si6 (proved atom-by-atom in Lean), and (iii) the printed
  alpha-cycloaltrin structure whose 2-OH is axial down. No answer key, marking scheme,
  or external competition solution was used.
* The mechanistic vocabulary (Sinay-type 2,3-anhydrose; Fuerst-Plattner diaxial opening)
  is textbook carbohydrate chemistry, used only to *justify* the assignment, not to
  supply the answer.
