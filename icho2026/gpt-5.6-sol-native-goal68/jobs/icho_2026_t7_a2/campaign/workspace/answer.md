# IChO 2026 T7-A2

The annual methane requirement is

\[
\boxed{m(\mathrm{CH_4})=2.80\times 10^5\ \text{tons per year}}.
\]

The exact raw value used before final reporting is

\[
m(\mathrm{CH_4})
=\frac{77\,202\,125\,000}{275\,383}\ \text{tons}
=280\,344.556490\ldots\ \text{tons}.
\]

## Derivation

Use the `4 N2 + 1 O2` air portion printed above the partial-oxidation
reactor in Fig. 1 as a basis. Quantitative partial oxidation,

\[
2\mathrm{CH_4}+\mathrm{O_2}\longrightarrow
2\mathrm{CO}+4\mathrm{H_2},
\]

therefore consumes 2 mol CH4 and supplies 4 mol H2. Let `y` mol CH4 be
consumed in the preceding steam-reforming reactor. Since that reactor is
quantitative and its outgoing stream contains CH4 but no H2O, the same `y`
mol is the amount of steam consumed:

\[
\mathrm{CH_4}+\mathrm{H_2O}\longrightarrow
\mathrm{CO}+3\mathrm{H_2}.
\]

The reformer contributes `y` mol CO and `3y` mol H2. Partial oxidation adds
2 mol CO and 4 mol H2. Quantitative water-gas shift converts all `y+2` mol CO
and produces another `y+2` mol H2:

\[
\mathrm{CO}+\mathrm{H_2O}\longrightarrow
\mathrm{CO_2}+\mathrm{H_2}.
\]

After CO2 scrubbing, the total hydrogen amount is consequently

\[
3y+4+(y+2)=4y+6.
\]

The 4 mol N2 brought by the air portion requires 12 mol H2 according to the
displayed Haber–Bosch equation
`N2 + 3 H2 ⇌ 2 NH3`. Hence `4y+6=12`, so `y=3/2`. The total methane feed on
this basis is

\[
x=y+2=\frac72\ \text{mol},
\]

while 4 mol N2 corresponds to 8 mol theoretical NH3. Thus Fig. 1 gives the
derived mole ratio

\[
\frac{n(\mathrm{CH_4})}{n(\mathrm{NH_3,theoretical})}
=\frac{7/2}{8}=\frac7{16}.
\]

The periodic table supplied on PDF page 5 gives

\[
M(\mathrm{CH_4})=12.01+4(1.008)=16.042\ \mathrm{g\,mol^{-1}},
\]

\[
M(\mathrm{NH_3})=14.01+3(1.008)=17.034\ \mathrm{g\,mol^{-1}}.
\]

Interpreting the stated overall yield in the standard way,
`actual output = 0.970 × theoretical output`, gives

\[
\begin{aligned}
m(\mathrm{CH_4})
&=\frac{660\,000}{0.970}
  \left(\frac7{16}\right)
  \left(\frac{16.042}{17.034}\right)\\
&=280\,344.556490\ldots\ \text{tons}.
\end{aligned}
\]

Applying the task's three-significant-figure reporting policy only at the
end yields `2.80 × 10^5 tons`.

## Source grounding

- `TASK.json` identifies subquestion T7-A2, the requested 660,000-ton annual
  NH3 output, the 97.0% overall yield, and the three-significant-figure final
  reporting policy.
- `icho_2026_source/image/T7_page-1.png` and the identical problem page in
  `icho_2026_source/raw/theory_problem.pdf` (PDF page 63, printed Q7-1) supply
  every reaction and stream ratio used above. Their SHA-256 values agree with
  those recorded in `TASK.json`.
- The original PDF's page 5 supplies the printed atomic masses H = 1.008,
  C = 12.01, and N = 14.01.
- The original blank answer sheets were inspected at PDF pages 67–68
  (printed A7-1 and A7-2). A7-2 provides working space and only the final
  blank `m(CH4) = ______`; it adds no scientific premise or hidden numerical
  datum.
- The 7:16 mole ratio and the raw tonnage are derived here rather than taken
  from a previous-part answer or any answer source. No source gap is needed
  to obtain the requested output from the simplified process as drawn.

