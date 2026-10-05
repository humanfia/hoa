# IChO 2026 T3-A2

## Answer

Trace one side of the idealized COF-2 honeycomb from the centre of one B3
junction to the centre of the neighbouring B3 junction in the molecular
drawing. With the width of the linkers neglected, this path contains:

- three arene C–C increments in each B3 half-junction, hence six in total;
- two further arene C–C increments across the para-phenylene A2 linker;
- one C–B and one B–O increment at each end of A2.

Thus one hexagon side has eight arene C–C increments, two C–B increments,
and two B–O increments:

\[
\begin{aligned}
a
  &=8(1.39)+2(1.56)+2(1.38)\ \text{Å}\\
  &=11.12+3.12+2.76\ \text{Å}\\
  &=17.00\ \text{Å}.
\end{aligned}
\]

Using the relation supplied in the question,

\[
d=\sqrt3\,a=17\sqrt3\ \text{Å}
  \approx 29.4448637\ \text{Å}.
\]

The requested three-significant-figure result is therefore

\[
\boxed{d=29.4\ \text{Å}}.
\]

No intermediate value was rounded.

## Source grounding

- `icho_2026_source/image/T3_page-1.png` (also original PDF page 25, Q3-1)
  supplies the COF-2 molecular drawing. It shows the B3 three-connected
  junctions linked by para-disubstituted A2 units; tracing one idealized edge
  gives the `3 C–C, B–O, C–B, 2 C–C, C–B, B–O, 3 C–C` walk used above. The
  coefficients 8, 2, and 2 are derived from this drawing, not added numerical
  premises.
- `icho_2026_source/image/T3_page-2.png` and original PDF page 26 (Q3-2)
  stipulate C–C/C=C = 1.39 Å, C–B = 1.56 Å, B–O = 1.38 Å, the relation
  `d = √3 a`, and the instruction to neglect linker width.
- The original blank student answer sheet is PDF page 32 (A3-1). Its 3.2 box
  ends with `d = ___ Å` and contains no additional datum or precision rule.
- `TASK.json` supplies the answer-blind default of three significant figures
  because the printed subquestion gives no explicit precision. For a positive
  number near 29 Å, this is nearest 0.1 Å. The formal proof establishes
  `29.35 ≤ 17√3 < 29.45`, so the reported value is rigorously 29.4 Å.

The stipulated decimal bond lengths are treated as exact, as required by the
task's measurement policy. There is no source gap needed to obtain the answer.

## Formalization summary

`IChO2026Problems/problem_icho_2026_t3_a2.lean` represents the image-derived
edge as a typed bond walk. It proves the 8/2/2 bond counts, its exact 17 Å
length, the exact diameter `17 * Real.sqrt 3`, rational bounds sufficient for
rounding, and a valid `NumericSubmission` with reported value `147/5 = 29.4`
and reporting quantum `1/10` Å.
