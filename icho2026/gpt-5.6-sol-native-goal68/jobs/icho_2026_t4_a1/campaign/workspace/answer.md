# IChO 2026 T4-A1

Let $x$ be the atomic fraction of \(^{235}\mathrm U\). Under the question's
two-isotope assumption, the atomic fraction of \(^{238}\mathrm U\) is $1-x$.
The isotope-weighted average atomic mass is therefore

\[
238.03 = 235.04x + 238.05(1-x).
\]

Solving without intermediate rounding,

\[
x=\frac{238.05-238.03}{238.05-235.04}
  =\frac{0.02}{3.01}
  =\frac{2}{301}.
\]

Thus the exact raw percentage is

\[
100x=\frac{200}{301}\%=0.664451827\ldots\%.
\]

Using the `TASK.json` reporting rule of three significant figures, the requested
answer is

\[
\boxed{\text{atomic abundance of }{}^{235}\mathrm U=0.664\%}.
\]

## Source grounding

- `TASK.json` and `T4_page-1.png` identify T4-A1 and print the isotope masses
  235.04 a.u. and 238.05 a.u., together with the assumption that natural uranium
  is treated as containing only these two isotopes.
- The original `theory_problem.pdf`, page 37 (`Q4-1`), gives the same question.
- The supplied general periodic table in the same PDF, page 5 (`G1-5`), prints
  uranium's natural atomic mass as 238.03. This is the otherwise implicit datum
  required by the requested calculation.
- The four blank T4 student answer sheets are PDF pages 40--43 (`A4-1` through
  `A4-4`). Page 40 supplies only a blank `235U: ___ %` field; none adds a
  numerical premise or reveals an answer for T4-A1.
- The only scientific law used is the standard definition of an element's
  average atomic mass as the atomic-fraction-weighted mean of its isotope
  masses. Following `TASK.json`, printed constants are used exactly as printed,
  and no intermediate rounding is performed.

The Lean formalization separates the three printed masses in the
`ProblemInputs` namespace from the derived balance, proves that $2/301$ is the
unique atomic fraction satisfying that balance, converts it exactly to
$200/301\%$, and proves that $0.664\%$ is the correct nearest-thousandth
report.
