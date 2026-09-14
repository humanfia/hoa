# IChO 2026 T5-A3

The fatty acid has molecular formula

\[
\boxed{\mathrm{C_{18}H_{32}O_2}}.
\]

## Calculation

Write the acid formula as \(\mathrm{C_cH_hO_2}\). Let \(d\) be the number
of C=C bonds and, to avoid silently excluding another possible hydrocarbon
multiple bond, let \(t\) be the number of C≡C bonds.

Complete ozonolytic cleavage of an acyclic carbon skeleton at \(d+t\)
multiple-bond positions gives \(d+t+1\) chain fragments. The problem reports
three *different* products in equimolar amounts. The fragment retaining the
single original COOH group occurs exactly once per acid molecule; equimolarity
therefore makes the other two product multiplicities one as well. Thus no
product fragment is repeated and

\[
d+t+1=3, \qquad d+t=2. \tag{1}
\]

For an acyclic monocarboxylic acid, the saturated formula is
\(\mathrm{C_cH_{2c}O_2}\). A C=C bond removes two H atoms and a C≡C bond
removes four, hence

\[
h=2c-2d-4t. \tag{2}
\]

The fragment composition of neutral PL1 is equivalent to combining four
fatty acids, three glycerol molecules, and two phosphoric acid molecules while
losing eight water molecules. Thus

\[
\begin{aligned}
4\,\mathrm{C_cH_hO_2}
+3\,\mathrm{C_3H_8O_3}
+2\,\mathrm{H_3PO_4}
-8\,\mathrm{H_2O}
=\mathrm{C_{4c+9}H_{4h+14}O_{17}P_2}.
\end{aligned}
\]

Neutral PL1 is connected and acyclic. It contains

\[
(4c+9)+(4h+14)+17+2=4c+4h+42
\]

atoms, so it has \(4c+4h+41\) sigma bonds. Its pi bonds comprise four
copies of every chain multiple bond, four C=O bonds, and two P=O bonds:

\[
N_\pi=4d+8t+4+2=4d+8t+6.
\]

Using the stated total of 255 sigma and pi bonds gives

\[
4c+4h+4d+8t+47=255. \tag{3}
\]

Substituting (2) into (3) and dividing by 4 gives

\[
3c-d-2t=52. \tag{4}
\]

From (1), \(t=2-d\), so (4) becomes

\[
3c+d=56.
\]

Because \(d,t\ge 0\) and \(d+t=2\), \(d\in\{0,1,2\}\). Reduction modulo
3 gives \(d\equiv 56\equiv2\pmod 3\), hence \(d=2\), \(t=0\), and
\(c=18\). Equation (2) then gives

\[
h=2(18)-2(2)=32.
\]

As a direct check, the resulting neutral PL1 formula is
\(\mathrm{C_{81}H_{142}O_{17}P_2}\). It has 242 atoms and therefore 241
sigma bonds; its eight C=C, four C=O, and two P=O bonds contribute 14 pi
bonds. The total is \(241+14=255\), exactly as stated.

## Source grounding

- `TASK.json` supplies the current question and identifies the problem-only
  assets. `T5_page-3.png` states both observations used above: three different
  equimolar reductive-ozonolysis products and 255 total sigma and pi bonds.
- `T5_page-1.png` shows that PL1 is an acyclic phospholipid assembled from
  four fatty-acyl fragments, three glycerol fragments, and two phosphate
  fragments; it also shows the C=O and P=O bonds counted above.
- `T5_page-2.png` is the blank student answer sheet for Q5.2. It contains no
  additional chemical premise or filled-in structure.
- The original `theory_problem.pdf` has SHA-256
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`,
  matching the hash recorded in `TASK.json`. Its following T5 page prints the
  balanced hydrolysis equation
  \(\mathrm{PL1+8H_2O\to4RCOOH+2H_3PO_4+3\,glycerol}\), independently
  confirming the fragment atom balance used here.

The only non-numerical inputs beyond the printed structure are standard
chemical bookkeeping laws: cleavage of an acyclic skeleton at each
carbon-carbon multiple bond, the hydrogen-deficiency formula, and the graph
identity that a connected acyclic molecule with \(N\) atoms has \(N-1\)
sigma bonds. No official solution, marking scheme, or historical answer was
used, and there is no source gap affecting the requested molecular formula.
