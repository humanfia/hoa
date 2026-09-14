# IChO 2026, Problem T5 (Cardiolipins), subquestion 5.3 (T5-A3)

## Answer

**The fatty acid is RCOOH = C₁₈H₃₂O₂** (a linear C₁₈ monocarboxylic acid with
two C=C double bonds — linoleic acid; realised in mammalian-heart
cardiolipin as (9Z,12Z)-octadecadienoic acid).

## Sources used

* T5 page 1 (structural fragments a–d with quantities n, 2, 3, 4; the worked
  example W showing how free valences pair; "R is a hydrocarbon substituent";
  "PL1 does not contain any peroxide bonds"; the chirality paragraph: PL1
  contains four identical fatty acid residues, is chiral, and all other
  diastereomers have a plane of symmetry).
* T5 page 3 (question 5.3: non-ionised PL1 contains 255 σ- and π-bonds in
  total; reductive ozonolysis of RCOOH gives three different organic
  products in equimolar amounts).
* T5 page 4 (balanced hydrolysis PL1 + 8 H₂O → 4 RCOOH + 2 H₃PO₄ +
  3 glycerol, used as an independent consistency check of the inventory).
* Trusted general laws only: standard neutral valences of the elements
  (C : 4, H : 1, O : 2, P : 5 for phosphate P(V) as drawn in fragment b) and
  the handshake lemma (every σ- or π-bond contributes exactly two valence
  ends); reductive ozonolysis cleaves every C=C bond of an acyclic chain to
  carbonyls. No official solutions, marking schemes or answer repositories
  were used.

## Calculation supporting the answer

**1. Atom inventory of the assembly.** With cR = number of carbons of the
acyl group (including the carbonyl carbon of fragment d) and u = number of
C=C double bonds in the hydrocarbon substituent R = C_{cR−1}H_{2cR−1−2u}:

| fragment | count | C | H | O | P |
|---|---|---|---|---|---|
| a (⤳H) | n | 0 | n | 0 | 0 |
| b (HO–P(=O)⤝⤝) | 2 | 0 | 2 | 4 | 2 |
| c (⤳O–CH₂–CH(O⤳)–CH₂–O⤝) | 3 | 9 | 15 | 9 | 0 |
| d (O=C⤳–R) + R | 4 | 4 + 4(cR−1) | 4(2cR−1−2u) | 4 | 0 |
| **PL1** | | **9 + 4·cR** | **13 + n + 8·cR − 8·u** | **17** | **2** |

(Fragment c bears no O–H hydrogens: the three glycerol OH hydrogens of the
hydrolysis products are supplied during assembly by fragments a — cf. the
worked example W, where the single a-fragment provides the H of the glycerol
OH.)

**2. Bond-count (handshake) formula.** For the neutral, acyclic, peroxide-free
molecule, σ + π bonds = (Σ valences)/2:

  B = (4·C + H + 2·O + 5·P)/2
    = (4(9 + 4·cR) + (13 + n + 8·cR − 8·u) + 2·17 + 5·2)/2
    = (93 + n + 24·cR − 8·u)/2.

**3. Determination of n (re-derivation of the 5.1 result).** Since the
valence sum must be even, n is odd (the 5.1 answer "n is an odd number").
The chirality paragraph fixes the value: the only candidate stereogenic
centres are the central carbons of the three glycerol fragments. Any
glycerol whose three oxygens do not carry two acyls plus one phosphate
(flanking glycerols) — i.e. any glycerol with an H-capped acyl position —
has two identical arms at its central carbon, loses that stereocentre, and
the molecule is one of the achiral diastereomers with a plane of symmetry
that the problem says PL1 is not. Hence all four acyls esterify the two
flanking glycerols, both phosphates bridge to the central glycerol, and n = 1:
the single H caps the central oxygen of the bridging glycerol, whose central
carbon stays stereogenic because the two phosphate halves it connects are
constitutionally different — this is the cardiolipin structure.

**4. The 255-bond equation.** With n = 1:

  255 = (94 + 24·cR − 8·u)/2   ⟹   24·cR − 8·u = 416   ⟹   3·cR − u = 52.

**5. Ozonolysis fixes u.** A linear monocarboxylic acid with u C=C bonds
yields exactly u + 1 organic fragments under reductive ozonolysis. "Three
different products in equimolar amounts" forces u + 1 = 3 (each fragment
formed exactly once), so u = 2.

**6. Solve.** 3·cR = 52 + 2 = 54 ⟹ cR = 18. The fatty acid is therefore
C₁₈H_{2·18−2·2}O₂ = **C₁₈H₃₂O₂**.

## Independent consistency checks

* **Hydrolysis balance (page 4):** 4·C18H32O2 + 2·H3PO4 + 3·C3H8O3 − 8·H2O
  = C81H142O17P2 = pl1Atoms(1, 18, 2). ✓
* **Bond count (direct):** PL1 = C81H142O17P2 has 242 atoms; the acyclic
  molecule has 241 σ bonds (82 C–H, 4 P–OH, 1 O–H of the bridging glycerol,
  and 154 bonds of the heavy-atom framework) and 14 π bonds (4 ester C=O,
  8 C=C, 2 P=O), totalling 255. ✓ Equivalently by the handshake lemma:
  (4·81 + 142 + 2·17 + 5·2)/2 = 510/2 = 255. ✓
* **Ozonolysis (page 3):** with the Δ9,Δ12 placement of linoleic acid,
  HOOC–(CH₂)₇–CH=CH–CH₂–CH=CH–(CH₂)₄–CH₃ gives HOOC–(CH₂)₇–CHO (8 C),
  OHC–CH₂–CHO (3 C) and OHC–(CH₂)₄–CH₃ (6 C): three different products,
  formed 1 : 1 : 1 (8 + 3 + 6 = 17 = 18 − 1 carbons). The molecular formula
  itself does not depend on the placement, only on u = 2.
* **Cross-check with 5.4 data (not needed for the answer):** 100 g of
  C18H32O2 (M = 280.45 g/mol) reacts with 2 mol I₂ = 507.6/2.8045 ≈ 181.0 g
  of iodine — exactly the number quoted on page 3.
* **Fallback note (5.3's red text):** a student who did not find the PL1
  structure may instead reason from the raw fragments a–d with unknown n.
  Because every free valence ends in an assembled bond anyway, the total
  bond count is the same handshake expression, and n = 1 follows from parity
  (n odd) plus the fragment-count bound n ≤ 3 − (number of glycerol-centre
  OH caps compatible with chirality)… simplest: n = 1 is the smallest odd
  value compatible with the four-acyl, two-phosphate cardiolipin skeleton;
  the equation 3·cR − u = 52 is unchanged.

## Answer-blind reporting

The requested output is an exact symbolic molecular formula; no rounding or
precision quantum applies.

**RCOOH = C18H32O2** (linoleic acid; PL1 is tetralinoleoyl cardiolipin,
C81H142O17P2 in its non-ionised form).
