# IChO 2026 T2-A3

For the two competing elementary steps, the mass-action rates are

\[
v_1=k_1[\mathrm{HBrO_2}][\mathrm{BrO_3^-}][\mathrm{H^+}]
\]

and

\[
v_4=k_4[\mathrm{HBrO_2}][\mathrm{Br^-}][\mathrm{H^+}].
\]

The critical bromide concentration is the boundary between the two strict
rate orderings, so at that concentration \(v_1=v_4\).  Both common
concentration factors are positive and cancel:

\[
k_1[\mathrm{BrO_3^-}]
  =k_4[\mathrm{Br^-}]_{\mathrm{critical}},
\qquad
[\mathrm{Br^-}]_{\mathrm{critical}}
  =\frac{k_1}{k_4}[\mathrm{BrO_3^-}].
\]

Using the printed values \(k_1=1.0\times10^4\),
\(k_4=2.0\times10^9\), and the maintained
\([\mathrm{BrO_3^-}]=0.06\ \mathrm{M}\), without intermediate rounding,

\[
[\mathrm{Br^-}]_{\mathrm{critical}}
=\frac{1.0\times10^4}{2.0\times10^9}(0.06)
=3\times10^{-7}\ \mathrm{M}.
\]

Thus, to the required three significant figures,

\[
\boxed{[\mathrm{Br^-}]_{\mathrm{critical}}
  =3.00\times10^{-7}\ \mathrm{mol\,dm^{-3}}}.
\]

As a direction check, bromide concentrations above this value give
\(v_4>v_1\), which is the stated condition for switching from Process A to
Process B.  Below it, \(v_1>v_4\), corresponding to the reverse preference.

## Source grounding

- `TASK.json` identifies T2-A3 and supplies the shared official problem text,
  the answer-blind three-significant-figure reporting rule, and the requested
  unit `mol dm^-3`.
- `T2_page-2.png` (official question page Q2-2) prints elementary steps (1)
  and (4), \(k_1=1.0\times10^4\ \mathrm{M^{-2}s^{-1}}\),
  \(k_4=2.0\times10^9\ \mathrm{M^{-2}s^{-1}}\), the maintained bromate
  concentration \(0.06\ \mathrm M\), and \([\mathrm H^+]=0.8\ \mathrm M\).
- `T2_page-3.png` (official question page Q2-3) defines the critical bromide
  concentration and states the switch criterion by comparison of the rates of
  steps (4) and (1).
- The original `theory_problem.pdf` was checked at PDF page 17 for Q2-3 and at
  PDF page 21 for the blank student answer sheet A2-3.  The latter contains the
  blank field `2.3 (4.0 pt) [Br−]critical = ___ M`, confirming that the output
  is one molar concentration and supplying no answer value.
- The only general scientific law used beyond the printed data is the standard
  mass-action rate law for an elementary reaction.  The cancellation requires
  positive \([\mathrm{HBrO_2}]\) and \([\mathrm H^+]\).  The problem prints
  \([\mathrm H^+]=0.8\ \mathrm M\) and positive fallback values for both
  stationary \([\mathrm{HBrO_2}]\) levels.  Consequently, T2-A2's numerical
  result is not needed: either positive level cancels from the calculation.

No official solution, marking scheme, answer repository, or historical answer
was used, and there is no source gap affecting this result.
