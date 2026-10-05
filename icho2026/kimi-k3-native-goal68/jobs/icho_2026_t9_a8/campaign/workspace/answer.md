# IChO 2026, T9, Question 9.8 (icho_2026_t9_a8)

**Task (T9_page-4.png; blank answer templates A9-4/A9-5 in theory_problem.pdf):** draw the structures of **O, P, Q, R, S** on the six-box alpha-CD templates (units 1-6 as numbered on the sheet; the (OBn)12 secondary rim is preprinted on every template and stays benzyl-protected throughout). The problem instructs: *1,2-unit modification happens clockwise, 1,3-unit modification happens counterclockwise; protic groups have stronger directing effects than alkenes.* Shared context (9.5 preface, page Q9-3): a single protic group (NH or OH) directs the next reductive debenzylation of a primary OH to the 1,4-unit, **or to the 1,3-unit if the 1,4 position is not available**; Sollogoub et al. use alkenes to direct debenzylation to the **ortho** (1,2) glucopyranose unit.

## Starting material N (given in the problem figure)

Primary face: unit 1 = CH2OH; units 2-6 = CH2OBn (mirrored text "BnOH2C" in boxes 2 and 3). Secondary rim: (OBn)12.

## Step-by-step structures (figure-grounded)

### N to O : 1) (COCl)2, DMSO  2) (C6H5)3P=CH2
Swern oxidation turns the only free primary alcohol into the aldehyde, and Wittig methylenation gives the terminal alkene (a vinyl group). This installs the alkene directing group of the Sollogoub method.

- **O:** unit 1 = **-CH=CH2**; units 2-6 = -CH2OBn.

### O to P : 1) DIBAL-H (1 equiv.)  2) MsCl  3) NaN3
DIBAL-H reductively debenzylates one primary benzyl ether. The only directing group present is the vinyl at unit 1 (an *alkene*), which directs to an **ortho** unit; the 9.8 convention places a 1,2-modification **clockwise**, i.e. at **unit 2**. Mesylation and SN2 with azide then convert the freed CH2OH into CH2N3.

- **P:** unit 1 = -CH=CH2; unit 2 = **-CH2N3**; units 3-6 = -CH2OBn.

### P to Q : 1) DIBAL-H (2 equiv.)  2) NaH, ClCH2C(=CH2)CH2Cl
Two equivalents of DIBAL-H do two jobs (standard DIBAL-H chemoselectivity): (i) reduction of the unit-2 azide to a **primary amine** -CH2NH2, which is a **protic** directing group; (ii) a directed debenzylation. Protic beats alkene, so NH2@2 directs to its **1,4-unit = unit 5** (available; no fallback needed). NaH then deprotonates the new OH(5) and NH2(2), and the 2-methylallyl bridging reagent ClCH2-C(=CH2)-CH2Cl doubly alkylates them, giving the N,O **methylenebis bridge** between units 2 and 5, still bearing its central =CH2 alkene.

- **Q:** unit 1 = -CH=CH2; unit 2 = **-CH2-NH-CH2-C(=CH2)-CH2-O-** (to 5); units 3, 4, 6 = -CH2OBn; unit 5 = **-CH2-O-CH2-C(=CH2)-CH2-NH-** (to 2).

### Q to R : 1) DIBAL-H (1 equiv.)  2) Boc2O (1 equiv.)  3) MsCl  4) NaN3
The bridge NH at unit 2 is the protic director. Its 1,4-unit (unit 5) is **not available** (occupied by the bridge ether oxygen), so the stated fallback applies: the 1,3-unit **counterclockwise** from 2 = **unit 6**, whose CH2OH is freed. Boc2O protects the bridge nitrogen (this step only makes sense because an N-H exists in Q - internal evidence for the azide-to-amine reading of the previous step); mesylation/azide substitution installs the second azide at unit 6.

- **R:** unit 1 = -CH=CH2; unit 2 = -CH2-**N(Boc)**-CH2-C(=CH2)-CH2-O-; unit 5 = bridge-O arm; unit 6 = **-CH2N3**; units 3, 4 = -CH2OBn.

### R to S : 1) CF3COOH  2) NaH, BnI  3) DIBAL-H (2 equiv.)
TFA removes the Boc group, restoring the bridge N-H at unit 2, which is then benzylated (NaH, BnI; the only protic site in R) to give **NHBn** at unit 2. The final 2 equivalents of DIBAL-H again do two jobs: reduce the unit-6 azide to **-CH2NH2**, and debenzylate once more. Of the two protic amines now present, NHBn@2 has both directional targets blocked (1,4 goes to unit 5, the bridge; 1,3-ccw goes to unit 6), while the new NH2@6 has a clean **1,4-unit = unit 3**, which is freed to CH2OH. Unit 4 therefore keeps its benzyl ether.

- **S:** unit 1 = -CH=CH2; unit 2 = -CH2-**N(Bn)**-CH2-C(=CH2)-CH2-O-; unit 3 = **-CH2OH**; unit 4 = -CH2OBn; unit 5 = -CH2-O-CH2-C(=CH2)-CH2-N(Bn)-; unit 6 = **-CH2NH2**. Secondary rim: (OBn)12.

## Template answer summary (box contents per template; (OBn)12 outside)

| Unit | O | P | Q | R | S |
|---|---|---|---|---|---|
| 1 | CH=CH2 | CH=CH2 | CH=CH2 | CH=CH2 | CH=CH2 |
| 2 | CH2OBn | CH2N3 | CH2-NH-(bridge) | CH2-NBoc-(bridge) | CH2-NBn-(bridge) |
| 3 | CH2OBn | CH2OBn | CH2OBn | CH2OBn | **CH2OH** |
| 4 | CH2OBn | CH2OBn | CH2OBn | CH2OBn | CH2OBn |
| 5 | CH2OBn | CH2OBn | CH2-O-(bridge) | CH2-O-(bridge) | CH2-O-(bridge) |
| 6 | CH2OBn | CH2OBn | CH2OBn | **CH2N3** | **CH2NH2** |

Bridge (Q, R, S): -CH2-NR-CH2-C(=CH2)-CH2-O- linking units 2 and 5, with R = H (Q), Boc (R), Bn (S); its central alkene is intact throughout (a structural white box on the answer sheet may be used to show it).

**Consistency check:** the six units of S are pairwise different (vinyl / N(Bn)-bridge arm / CH2OH / CH2OBn / O-bridge arm / CH2NH2) - exactly the "hexadifferentiated alpha-CD S" of the problem preamble.

## Source grounding and assumptions

- Problem-grounded inputs: the template of N (figure, T9_page-4), the reaction arrows and reagents of each step (same figure), the Sinay protic 1,4 -> (1,3-if-blocked) rule and the Sollogoub alkene -> ortho rule (problem text, pages Q9-3/Q9-4), and the 9.8 instruction fixing 1,2 = clockwise, 1,3 = counterclockwise and protic stronger than alkene. All five structures use only these.
- Trusted general chemistry (ordinary scientific knowledge, not competition answers): Swern oxidation gives the aldehyde; Wittig methylenation gives the terminal alkene; MsCl/NaN3 performs OH -> OMs -> N3 by SN2; Boc2O protects a secondary amine and TFA removes it; NaH deprotonates OH/NH2 and a dichloride doubly alkylates the pair; **DIBAL-H also reduces alkyl azides to primary amines** (the standard explanation of the "2 equiv." in the P-to-Q and R-to-S steps, and the only reading consistent with the downstream Boc2O step and the problem's own "protic NH" directing language); isolated vinyl and bridge C=C groups are untouched by DIBAL-H.
- The regiochemistry of every directed debenzylation is a direct hit or a single stated fallback under the printed convention: P (alkene@1, 1,2-cw -> 2), Q (amine@2, 1,4 -> 5), R (amine@2, 1,4 occupied -> 1,3-ccw -> 6), S (amine@6, 1,4 -> 3; the rival director NHBn@2 has both targets occupied). No unprinted hopping rules are invoked.
