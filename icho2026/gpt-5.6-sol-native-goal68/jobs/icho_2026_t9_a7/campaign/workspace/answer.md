# IChO 2026 T9-A7

The two sodium-adduct peaks are

\[
\boxed{[M_1+\mathrm{Na}]^+:\ m/z=1299}
\qquad\text{and}\qquad
\boxed{[M_2+\mathrm{Na}]^+:\ m/z=1731}.
\]

Here (M_1) denotes the smaller degradation fragment.

## Derivation

The problem states that β-CD contains seven glucopyranoside units. On Q9-3,
the first free primary OH is numbered as unit 1 and directs the second
debenzylation to unit 4 (unit 4 is available here). Thus L is cut at units 1
and 4 by the degradation sequence. The two paths between those units contain
respectively

- units 2 and 3: two intact residues;
- units 5, 6, and 7: three intact residues.

The Q9-4 product scheme supplies the following component accounting:

- each intact bracketed residue contributes
  \(R=\mathrm{C}_{27}\mathrm{H}_{28}\mathrm{O}_{5}\);
- the bracketed enose end contributes
  \(E=\mathrm{C}_{22}\mathrm{H}_{25}\mathrm{O}_{4}\);
- the other cut end bears the additional acetoxy group shown as AcO, whose
  attached-group formula is \(A=\mathrm{C}_{2}\mathrm{H}_{3}\mathrm{O}_{2}\).

Consequently, each fragment has formula (E+A+nR), where (n) is the number
of intact residues on its path.

For the smaller fragment, (n=2):

\[
\begin{aligned}
E+A+2R
 &= \mathrm{C}_{22}\mathrm{H}_{25}\mathrm{O}_{4}
  + \mathrm{C}_{2}\mathrm{H}_{3}\mathrm{O}_{2}
  +2(\mathrm{C}_{27}\mathrm{H}_{28}\mathrm{O}_{5})\\
 &= \mathrm{C}_{78}\mathrm{H}_{84}\mathrm{O}_{16}.
\end{aligned}
\]

Using integer atomic masses C = 12, H = 1, O = 16, and Na = 23, and noting
that the ion has charge magnitude one,

\[
m/z=78(12)+84(1)+16(16)+23=1299.
\]

For the larger fragment, (n=3):

\[
\begin{aligned}
E+A+3R
 &= \mathrm{C}_{22}\mathrm{H}_{25}\mathrm{O}_{4}
  + \mathrm{C}_{2}\mathrm{H}_{3}\mathrm{O}_{2}
  +3(\mathrm{C}_{27}\mathrm{H}_{28}\mathrm{O}_{5})\\
 &= \mathrm{C}_{105}\mathrm{H}_{112}\mathrm{O}_{21},\\[2mm]
m/z &=105(12)+112(1)+21(16)+23=1731.
\end{aligned}
\]

## Source grounding

- `TASK.json` requests exactly two integer `m/z` outputs and identifies
  `T9_page-3.png`, `T9_page-4.png`, and the original `theory_problem.pdf` as
  the problem-only sources.
- `T9_page-3.png` / PDF page 86 (Q9-3) gives the numbered seven-unit β-CD
  template and the unit-1-to-unit-4 directing rule used to identify L.
- `T9_page-4.png` / PDF page 87 (Q9-4) gives the degradation drawing, the
  formulas \(\mathrm{C}_{27}\mathrm{H}_{28}\mathrm{O}_{5}\) and
  \(\mathrm{C}_{22}\mathrm{H}_{25}\mathrm{O}_{4}\), the AcO end group, and
  asks for `[M+Na]⁺` using integer atomic masses.
- The blank student answer sheet on PDF page 91 (A9-3) contains precisely two
  fields, `[M₁+Na]⁺` and `[M₂+Na]⁺`; it provides no answer values.
- The source hashes match `TASK.json` / `isolation_manifest.json`: Q9-3
  `a63869290bd2dcbc80632be3cbf121fab1ffa361f725255f17c191d16df7da4f`,
  Q9-4 `a387cc56150da4c1070f2eb0b61e1e7c130429b1ec58594613fdfdb816476a1d`,
  and the PDF
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`.

No previous-part answer, official solution, marking scheme, or answer
repository is used. The only conventional chemistry expansion needed beyond
the printed formulas is `AcO = CH₃COO`.
