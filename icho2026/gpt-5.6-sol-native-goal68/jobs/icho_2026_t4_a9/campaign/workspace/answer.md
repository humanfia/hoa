# IChO 2026 T4.9

## Answer

\[
\boxed{TN=4.23\times 10^{24}\ \text{fissions}},\qquad
\boxed{m=5.56\ \text{kg of enriched uranium}}.
\]

The unrounded values are

\[
TN=4.230206366232801957\times 10^{24},\qquad
m=5.558991132160095\ \text{kg}.
\]

## Derivation

Part 4.9 says to use the result of part 4.4, so that result must first be
derived from the problem rather than replaced by the 200 MeV fallback.  The
two maxima of the supplied fission-yield graph are read at mass numbers 93 and
140.  The same-periodic-group condition in part 4.3, together with charge
conservation, selects rubidium and caesium (both group 1):

\[
{}^{235}_{92}\mathrm U+{}^1_0\mathrm n
\longrightarrow
{}^{93}_{37}\mathrm{Rb}+{}^{140}_{55}\mathrm{Cs}
+3\,{}^1_0\mathrm n .
\]

This conserves both nucleon number, \(235+1=93+140+3\), and atomic number,
\(92=37+55\).  Since the emitted neutrons are free, the two bound products
contain \(93+140=233\) nucleons.  Consequently the part 4.4 energy release is

\[
\begin{aligned}
\Delta E
 &=233(8.45)-235(7.59)\\
 &=1968.85-1783.65\\
 &=185.20\ \mathrm{MeV\,fission^{-1}}.
\end{aligned}
\]

Using \(1\ \mathrm{MeV}=1.602176634\times10^{-13}\ \mathrm J\), the energy
per fission is

\[
E_{\mathrm{fis}}
=185.20(1.602176634\times10^{-13})
=2.967231126168\times10^{-11}\ \mathrm J.
\]

The stated explosive energy is

\[
E_{\mathrm{expl}}
=30\ \mathrm{kiloton}\,
  1000\frac{\mathrm{ton}}{\mathrm{kiloton}}\,
  4.184\times10^9\frac{\mathrm J}{\mathrm{ton}}
=1.25520\times10^{14}\ \mathrm J.
\]

Therefore

\[
TN=\frac{E_{\mathrm{expl}}}{E_{\mathrm{fis}}}
=4.230206366232801957\times10^{24}.
\]

Every fission consumes one uranium-235 nucleus.  If only 33% of the original
uranium-235 nuclei fissioned, the original uranium-235 amount was

\[
n(^{235}\mathrm U)=\frac{TN}{0.33N_{\mathrm A}},
\quad N_{\mathrm A}=6.02214076\times10^{23}\ \mathrm{mol^{-1}}.
\]

Using the \(235.04\) atomic-mass value printed in part 4.1 as the numerical
molar mass in \(\mathrm{g\,mol^{-1}}\), and then dividing by the 0.90 mass
fraction of uranium-235, gives

\[
\begin{aligned}
m
&=\frac{TN}{0.33N_{\mathrm A}}
  \frac{235.04\ \mathrm g}{\mathrm{mol}}
  \frac{1\ \mathrm{kg}}{1000\ \mathrm g}
  \frac1{0.90}\\
&=5.558991132160095\ \mathrm{kg}.
\end{aligned}
\]

The final values are rounded only here, to the requested default of three
significant figures.  In particular, the respective last-place quanta are
\(10^{22}\) fissions and \(0.01\ \mathrm{kg}\).

## Source grounding and assumptions

- [`T4_page-1.png`](icho_2026_source/image/T4_page-1.png) supplies the fission
  reaction context and the graph maxima used for parts 4.3--4.4.
- [`T4_page-2.png`](icho_2026_source/image/T4_page-2.png) supplies the 7.59 and
  8.45 MeV/nucleon binding energies and says to neglect the binding energy of
  free neutrons.
- [`T4_page-3.png`](icho_2026_source/image/T4_page-3.png) supplies the
  30-kiloton yield, \(4.184\ \mathrm{GJ/ton}\), 90% enrichment, 33% fissioned
  fraction, and the 200 MeV fallback.  The fallback is not used because part
  4.4 was derived.
- The original [`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf)
  was checked at PDF pages 37--39 for T4 and at pages 40--43 for the blank
  student answer sheets.  Page 43 (A4-4) requests exactly \(TN\) and \(m\) in
  kg and supplies no additional condition.
- The elementary charge \(e=1.602176634\times10^{-19}\ \mathrm C\) and the
  Avogadro constant \(N_{\mathrm A}=6.02214076\times10^{23}\ \mathrm{mol^{-1}}\)
  are exact SI defining constants; these values are documented by the
  [BIPM SI Brochure](https://www.bipm.org/documents/20126/41483022/SI-Brochure-9.pdf).
  The electronvolt definition then gives the MeV-to-joule conversion above.
- The atomic numbers and common group of Rb and Cs are standard periodic-table
  data, cross-checked against the
  [IUPAC Periodic Table](https://iupac.org/wp-content/uploads/2015/07/IUPAC_Periodic_Table_A3-28Nov16.pdf).

The calculation uses the energy-balance interpretation requested by the
question: the TNT-equivalent explosion energy is divided by the energy per
fission.  It also uses the standard chemistry convention that the isotope's
atomic mass has the same numerical molar-mass value in g/mol.  All printed
problem values are retained exactly through the raw calculation, as required
by `TASK.json`; there is no unresolved source gap.

## Formalization

[`IChO2026Problems/problem_icho_2026_t4_a9.lean`](IChO2026Problems/problem_icho_2026_t4_a9.lean)
proves the reaction balances, the 185.20 MeV dependency, the explosion and
per-fission energy conversions, both physical balance equations and their
uniqueness, the exact raw results, and the final reporting intervals.  The two
requested-output theorems are `total_fissions_output` and
`enriched_uranium_mass_output`; `requested_outputs` combines them.
