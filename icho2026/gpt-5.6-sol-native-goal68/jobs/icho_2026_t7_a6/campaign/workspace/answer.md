# IChO 2026 T7.6

## Answer

The Red/Ad combinations in decreasing predicted ammonia yield are

\[
\boxed{\mathrm{B>C>D>A}}.
\]

## Reasoning from the problem data

All four candidates A--D use the triflate counterion, so the strong
chloride/triflate effect seen by comparing calibration rows 2 and 4 is held
constant in the requested ranking.

The printed calibration table provides two useful controlled comparisons:

1. Rows 1 and 4 use the same 2,6-lutidinium triflate additive
   (\(pK_a=14.4\)).  Changing the reductant potential from \(-0.88\) V to
   \(-1.15\) V changes the ammonia amount from 0 to 11.8 mol.  Thus the
   sufficiently more negative, stronger reductant belongs to the productive
   regime of this catalytic system.
2. Rows 3 and 4 use the same reductant (\(E^\circ=-1.15\) V) and a triflate
   additive.  The row with \(pK_a=14.4\) gives 11.8 mol, whereas the row with
   \(pK_a=13.9\) gives 9.1 mol.  For the comparison requested here, this is the
   problem's empirical direction: within the productive reductant regime,
   larger additive \(pK_a\) ranks higher.

Candidates B, C, and D all use vanadocene with \(E^\circ=-1.10\) V.  Their
additive values therefore give

\[
15.0\;(\mathrm B)>13.7\;(\mathrm C)>10.6\;(\mathrm D),
\]

so \(\mathrm B>C>D\).  A and C have the same 1,10-phenanthrolinium
triflate additive (\(pK_a=13.7\)), but A uses nickelocene at only
\(-0.09\) V while C uses vanadocene at \(-1.10\) V.  Nickelocene is even
less reducing than the \(-0.88\) V zero-yield calibration, placing A last;
the vanadocene candidates are close to the productive \(-1.15\) V
calibration.  Hence the full sequence is \(\mathrm{B>C>D>A}\).

## Source grounding and scope

- `TASK.json` identifies Q7-3 (PDF page 65) as the source page and requests one
  exact symbolic classification.
- `icho_2026_source/image/T7_page-3.png` and page 65 of
  `icho_2026_source/raw/theory_problem.pdf` contain the calibration and
  candidate tables transcribed above.
- The original PDF's blank answer sheet is page 70 (A7-4).  Its 7.6 area is a
  free-response box and imposes no additional notation or rounding rule.

The candidate yields themselves are not printed measurements.  Consequently,
the answer is the qualitative extrapolation the question asks the student to
make from its calibration table, not a claim that ammonia yield is universally
monotone in only \(E^\circ\) and \(pK_a\) for arbitrary catalysts.  The Lean
file makes this boundary explicit: it proves the computed classification under
the named problem-trend rule and states the corresponding theorem for numerical
yields with trend compatibility as a visible hypothesis.
