# IChO 2026 · T5 · Subquestion 5.6 (target `icho_2026_t5_a6`) — Answer

**Task (Q5-4, "5.6", 3.0 pt):** *Draw the structures of **PL2** and **PL3**
using **R** to show the fatty acid residues. Show stereochemistry where
appropriate.*

---

## Answers (what goes in the two boxes of answer sheet A5-4)

### PL2 — the propane-1,3-diol ("de-glycerinated") cardiolipin, drawn homochiral

```
              RCO–O–CH₂          CH₂–O–OCR                     (stereocentres:
                        \        /                             C* must carry
                         C*H——C*H                              the SAME label —
                        /        \                             here both drawn
             RCO–O–CH₂ꜛ          ꜜCH₂–O–OCR                    with the same
                        \        /                             wedge/dash
                         O        O                            convention)
                          \      /
                    O = P          P = O
                        \          /
                    HO   O––CH₂–CH₂–CH₂––O   OH
                              (Z)
```

In words with explicit connectivity (R = C₁₇H₃₁, the residue of the
cis,cis-octadeca-9,12-dienoic acid found in 5.3):

* two phosphatidyl "wings", each `RCO–O–CH₂–C*H(–O–OCR)–CH₂–O–`
  (fragment **d**, **d** on each wing glycerol; the wing glycerols esterified
  at both sn-1 and sn-2 and phosphorylated at sn-3, exactly as in PL1);
* the two phosphate groups (fragment **b**) are joined through their
  remaining oxygens by a single **Z = propane-1,3-diol unit,
  –O–CH₂–CH₂–CH₂–O–**, i.e.
  `···CH₂–O–P(=O)(OH)–O–CH₂–CH₂–CH₂–O–P(=O)(OH)–O–CH₂···`;
* one free P–OH on each phosphate (fragment **a** supplies the terminal H;
  PL2, like PL1, remains the same diprotic acid);
* **stereochemistry (required):** the two wing glycerol stereocentres C*
  must be drawn with the **same** configuration — **(R,R)** *or* **(S,S)**
  (one of the two enantiomers; the (R,S) assignment is meso/achiral because
  PL2 has an internal mirror exchanging the wings — the problem states PL2
  *is* chiral and that "all other diastereomers … have a plane of
  symmetry").  The bridge carbons are CH₂ and carry no stereochemistry;
  phosphorus stereocentres are excluded by the problem statement.

### PL3 — phosphatidylethanol, shown as the physiological monoanion

```
      CH₂–O–OC–R
        |
   R–CO–O–C*H          ← the unique stereocentre (glycerol C2):
        |                draw either the R or the S enantiomer
      CH₂–O–P(=O)(–O⁻)–O–CH₂–CH₃     (at physiological pH the single
                                      free phosphate OH is deprotonated;
                                      net charge −1)
```

In words:

* one glycerol (fragment **c**) esterified with two fatty acids
  `RCO–` at sn-1 and sn-2 (fragments **d**, **d**);
* at sn-3 a phosphate mono-esterified to glycerol and **esterified on its
  other side to ethanol** –O–CH₂–CH₃ (fragments **b** + **e**);
  **`Phosphatidylethanol`**;
* the phosphate is a diester with one remaining P–OH ⇒ at physiological pH
  it is deprotonated: **net charge −1**, as the problem requires ("PL3 is a
  charged molecule at physiological pH values" — a tri-ester would be
  neutral, a mono-ester with two free OH groups would hydrolyse to no
  ethanol, contradicting the printed products);
* **stereochemistry:** exactly one stereocentre (glycerol C2), so PL3 is the
  **pair of enantiomers (R)/(S)** — draw one of them with a wedge/dash bond.

---

## Derivation (how the clues of 5.3–5.5 force these structures)

1. **Groundwork (5.1–5.3, re-derived).**  Fragments: **a** = –H,
   **b** = –P(=O)(OH)–, **c** = glycerol, **d** = RCO– (acyl).
   PL1 = 2**b** + 3**c** + 4**d** + *n***a** with *n* odd; the cardiolipin
   assembly (two phosphatidyl wings joined by the middle glycerol through
   both phosphates, two free P–OH) is the *only* peroxide-free assembly of
   those fragments consistent with "diprotic acid with the same acidic
   groups" and with the stated chirality facts.  Its explicit skeleton has
   59 σ+π bonds; each R residue of C₁₇H₃₁ (i.e. fragments broken off the
   C₁₈H₃₂O₂ fatty acid identified in 5.3: ozonolysis gives three equimolar
   products ⇒ two C=C, and 100 g acid + 181.0 g I₂ ⇒ M(RCOOH) = 280 ⇒
   C₁₈H₃₂O₂) contributes (4·17+31−1)/2 = **49** σ+π bonds.
   Total: 59 + 4·49 = **255** ✓ (the printed datum of 5.3).

2. **PL2.**  The printed hydrolysis balance is
   `PL2 + 8 H₂O → 4 RCOOH + 2 H₃PO₄ + Z + 2 glycerol` — identical to PL1's
   except that **Z replaces one glycerol**.  Comparing atom and bond
   inventories:
   * Atom balance against PL1's equation forces **Z = C₃H₈O₂**
     (PL2 has exactly one C₃H₈O₃-worth minus "nothing": one fewer O, same C
     and H counts as glycerol required).
   * Bond count: replacing the middle glycerol's CH–OH (which contributed a
     C–O and an O–H bond) by a CH₂ reduces the σ+π count by exactly one:
     255 − 1 = **254** ✓ (the printed datum).  Explicitly: the explicit
     skeleton drops from 59 to 58 bonds, so 58 + 4·49 = 254.
   * "Z contains C, H, O only" ✓ and "doesn't react with H₂/catalyst" ⇒ all
     its bonds are single ✓.
   * Z must still join **both** phosphates (hydrolysis gives two H₃PO₄ and
     Z keeps exactly two oxygens) ⇒ Z is a *diol that bridges the two
     phosphate oxygens*: **–O–CH₂–CH₂–CH₂–O–** (propane-1,3-diol-derived).
   * "More symmetrical than PL1" and "chiral": unlike PL1's middle glycerol
     (whose central CH–OH blocks any wing exchange), the symmetric
     –CH₂–CH₂–CH₂– bridge makes wing-swap a genuine symmetry of PL2.  The
     (R,S) (meso) configuration of the two wing stereocentres is then
     achiral, so the *printed* chirality of PL2 forces the homochiral
     **(R,R)/(S,S)** enantiomer pair.  (The alternative 1,2-diol bridge
     –O–CH₂–CH(CH₃)–O– also has 254 bonds but creates a third
     stereocentre in the bridge, which would make *every* diastereomer
     chiral — incompatible with the problem's family statement that the
     meso-like diastereomers are achiral.  Hence the 1,3-diol.)

3. **PL3.**  The printed hydrolysis is
   `PL3 + m H₂O → 2 RCOOH + H₃PO₄ + C₂H₅OH + C₃H₈O₃ (glycerol)`.
   * The products are exactly what a **glycerol phospholipid with two acyl
     chains and one ethanol esterified to the phosphate** gives: 2**d** +
     1**c** + 1**b** + 1**e** (ethanol, fragment e).
   * Atom balance: PL3 = C₄₁H₇₃O₈P (+2 R = 2 C₁₇H₃₁ on a C₇H₁₁O₈P explicit
     core: 11 explicit H's + 2·31 = 73); matching
     C: 2·18+2+3 = 41, O: 2·2+4+1+3 = 12 = 8+4, H: 2·32+3+6+8 = 81 = 73+8
     gives **m = 4** waters.
   * "Charged at physiological pH": the phosphate is a diester (glycerol on
     one side, ethanol on the other) with one free P–OH ⇒ monoanion at pH 7
     (charge −1).  A triester is excluded (it would be neutral; and it could
     not release ethanol on hydrolysis in the printed 1:1 ratio with two
     fatty acids without extra fragments).
   * "Exists as a pair of enantiomers": with the two acyl chains on distinct
     terminal carbons of glycerol and the phosphate on sn-3 — C2 carries
     –CH₂OCOR, –OCOR, –CH₂O–P…, H — there is **exactly one stereocentre**,
     hence one enantiomeric pair (R)/(S).  Draw either one with
     stereochemistry shown.

All quantitative checks above are machine-verified in the Lean file (see
"Formalization" below).

---

## Source grounding

* Fragments a–e and the worked example W, the "3 × c, 2 × b, 4 × d, n × a"
  inventory, "R is a hydrocarbon substituent", "PL1 does not contain any
  peroxide bonds", "All other diastereomers of PL1 are achiral … plane of
  symmetry", "Do not consider the chirality of phosphorus atoms":
  **T5_page-1.png (Q5-1, theory_problem.pdf p. 44)**.
* Ozonolysis ("three different organic products in equimolar amounts"),
  "255 σ and π bonds", "100 g of RCOOH reacts with 181.0 g of iodine":
  **T5_page-2.png (5.3, pdf p. 45)** — this fixes RCOOH = C₁₈H₃₂O₂
  (M = 100/(181.0/(2·253.8))·2 ≈ 280; two C=C), hence R = C₁₇H₃₁ with
  49 σ+π bonds per residue.
* The three balanced hydrolysis equations (PL1 + 8 H₂O;
  PL2 + 8 H₂O with **Z + 2 glycerol**; PL3 + *m* H₂O with **ethanol +
  glycerol**), "254 σ and π bonds … chiral and a more symmetrical molecule
  than PL1", "Z contains C, H, and O only, and it doesn't react with H₂",
  "PL3 is a charged molecule at physiological pH values, and it exists as
  pair of enantiomers", and the question text of 5.6 itself:
  **T5_page-4.png (Q5-4, pdf p. 46)**.
* The blank answer boxes for PL2/PL3 on sheet **A5-4** (pdf p. 50) confirm
  the expected output is two structural drawings with R-abbreviations and
  stereochemistry.

## Formalization (Lean 4)

[IChO2026Problems/problem_icho_2026_t5_a6.lean](IChO2026Problems/problem_icho_2026_t5_a6.lean)
encodes PL1, PL2, the excluded 1,2-diol alternative (`pl2_asym`), PL3 and its
physiological anion as explicit hydrogen-complete molecular graphs (atoms,
bond orders, formal charges, stereocentre tables) and proves, among others:

`bondTotal_pl1 : … = 255`, `bondTotal_pl2 : … = 254`,
`pl2_one_bond_less` (255→254 by replacing CH–OH with CH₂),
`bondTotal_pl2_asym` (the 1,2-alternative also gives 254 — so it is excluded
by stereochemistry, not counting), `z_atoms`/`z_is_C3H8O2` (bridge =
3 C, 2 O, 6 H, all neutral), `z_composition_CHO`, `z_h2_inert` (no π bonds
in the bridge), `pl2_wingSwap_is_automorphism` (the extra symmetry),
`pl1_forces_swap_absent` (the same permutation fails on PL1),
`pl2_meso_RS_achiral` (the (R,S) assignment is meso under wing-swap),
`pl2_RR_not_meso` (the (R,R) assignment is not) together with
`pl2_homochiral` — so PL2 must be drawn (R,R) or (S,S),
`pl2_asym_stereocentres` (third stereocentre in the excluded alternative),
`pl3_composition`, `pl3_phys_netCharge` (= −1), `pl3_phys_chargedO`,
`pl3_neutral_netCharge`, `pl3_stereocentre` (unique centre) and
`pl3_pair_of_enantiomers`/`pl3_mirror_distinct`,
`pl3_hydrolysis_atomCensus`/`pl3_hydrolysis_waters` (the m = 4 balance),
plus well-formedness (`*_valid`) and neutral-valence (`*_valences`) audits of
every graph.  See `verification.md` for commands and the `#print axioms`
audit (no `sorryAx`, no custom axioms; only `propext`, `Quot.sound`,
`Classical.choice` and `native_decide` trust-base axioms).

## Caveats / assumptions honestly recorded

* The problem draws answer boxes without demanding a *specific* enantiomer;
  we draw and prove the (R,R)/(S,S) pair for PL2 and the (R)/(S) pair for
  PL3, and note in `result.json` that either member of each pair is an
  acceptable drawing (this matches "draw … one enantiomer" usage in 5.2).
* The sn-1/sn-2 (vs. sn-1/sn-3) placement of the two acyl groups on PL3's
  glycerol is the standard phospholipid convention and the only placement
  consistent with the fragment set; it is not further pinned down by the
  printed data and is recorded as an assumption.
* The local stereocentre predicate in Lean counts PL1's middle carbon
  (atom 31) as a *local* candidate — it has four single bonds and three
  heavy neighbours — but it is globally not a stereocentre because its two
  phosphate arms are identical substituents; the file states this in the
  docstring of `pl1_stereocentres`.  The physically meaningful centre list
  for PL1 is {7, 19}; for PL2 {7, 19} proved globally meso/chiral via the
  wing-swap automorphism theorems.
