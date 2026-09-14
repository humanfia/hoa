# IChO 2026 T1-A4

## Answer

- **Q = Al** (aluminium)
- **C·xH₂O = AlF₃·3H₂O** (aluminium fluoride trihydrate), so **C = AlF₃** and **x = 3**
- **D = Na₃AlF₆** (cryolite, trisodium hexafluoroaluminate)

## Derivation

The industrial-use clue points to cryolite, Na₃AlF₆, the molten fluoride used in the Hall–Héroult production of aluminium.  Thus the metal in D is Al.  Using the atomic masses printed in the problem's periodic table,

\[
M(\mathrm{Na_3AlF_6})
=3(22.99)+26.98+6(19.00)
=209.95\ \mathrm{g\ mol^{-1}}.
\]

The two calculated mass percentages are

\[
w(\mathrm{Na})=100\frac{3(22.99)}{209.95}
=32.8506787\%\longrightarrow 32.85\%,
\]

\[
w(\mathrm{Al})=100\frac{26.98}{209.95}
=12.8506787\%\longrightarrow 12.85\%.
\]

Both reproduce the two values in the question.  The anhydrous precursor is aluminium fluoride, and its conversion with excess sodium fluoride is atom-balanced as

\[
\mathrm{AlF_3+3NaF\longrightarrow Na_3AlF_6}.
\]

Therefore C is AlF₃.  From the supplied atomic masses,

\[
M(\mathrm{AlF_3})=26.98+3(19.00)=83.98,
\qquad
M(\mathrm{H_2O})=2(1.008)+16.00=18.016.
\]

Consequently,

\[
100\frac{18.016x}{83.98+18.016x}=39.16.
\]

Solving with the central displayed value gives $x=3.000343\ldots$, hence the integral hydration number is 3.  More rigorously, treating the printed 39.16% as the interval 39.155–39.165% gives

\[
2.9997138\ldots\le x\le 3.0009732\ldots,
\]

whose only natural-number value is $x=3$.  The direct check is

\[
100\frac{3(18.016)}{83.98+3(18.016)}
=39.1572724\%\longrightarrow 39.16\%.
\]

## Source grounding and assumptions

The problem-only evidence was read from `TASK.json`, the checksum-matching `T1_page-2.png` and `T1_page-3.png`, and the original 93-page `theory_problem.pdf`.  In the PDF, source page 8 (`Q1-3`) contains the full T1-A4 statement, source page 5 (`G1-5`) supplies H = 1.008, O = 16.00, F = 19.00, Na = 22.99, and Al = 26.98, and the blank student answer sheet on source page 12 (`A1-3`) requests exactly the three entries “Q”, “C·xH₂O”, and “D”.  The two image and PDF checksums match those recorded in `TASK.json`/`isolation_manifest.json`.

One necessary interpretation is not defined inside the competition text itself: the text expects the solver to know the industrial aluminium/cryolite connection and to interpret precipitated C as the sodium-free metal fluoride precursor.  This is treated as ordinary chemistry rather than as an unstated numerical premise.  The USGS states that aluminium is produced by electrolytic reduction of alumina in molten natural or synthetic cryolite, explicitly giving cryolite as Na₃AlF₆: [USGS, Bauxite and Alumina Statistics and Information](https://www.usgs.gov/centers/national-minerals-information-center/bauxite-and-alumina-statistics-and-information).  PubChem independently lists cryolite as trisodium hexafluoroaluminate, Na₃AlF₆, and as an electrolyte in aluminium production: [PubChem, Cryolite](https://pubchem.ncbi.nlm.nih.gov/compound/Sodium-hexafluoroaluminate).  PubChem also records aluminium fluoride trihydrate as AlF₃·3H₂O: [PubChem, Aluminium fluoride trihydrate](https://pubchem.ncbi.nlm.nih.gov/compound/Aluminium-fluoride-trihydrate).

That phase-identity assumption is genuinely necessary.  At the level of formula arithmetic alone, the distinct formal composition Na₂AlF₅·6H₂O also has 39.1572724% water with the paper's atomic masses and satisfies Na₂AlF₅ + NaF → Na₃AlF₆.  The problem text does not explicitly rule this algebraic countermodel out; it is excluded by identifying the actual pH-controlled precipitate as aluminium fluoride trihydrate, not merely by the percentage.  Accordingly, the answer above is the standard chemical identification, while the formal proof does not overclaim that the displayed numbers alone make C unique.

The Lean development does not hide that general-chemistry input.  `IndustrialFluoridePair` explicitly represents the Hall–Héroult classification, while the final identification theorem takes the sodium-free nature of C and the stated NaF conversion as hypotheses.  It then derives C by atom balance and derives $x=3$ for every natural $x$ satisfying the printed water-percentage interval; no finite search bound is assumed.  The theorem `bare_arithmetic_does_not_identify_C` formalizes the countermodel above.

## Formal results

The main theorem is `IChO2026Problems.T1A4.identify_metal_C_and_D`.  Dedicated output theorems are `metal_q_identity`, `hydrated_c_formula`, and `compound_d_formula`.  The theorem `identified_answer_satisfies_problem_data` proves together the water percentage, both elemental percentages, and the NaF reaction balance.
