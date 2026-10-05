# IChO 2026 T2-A2

## Answer

The stationary concentrations are

\[
\boxed{[\mathrm{HBrO_2}]_{\mathrm A}=6.00\times10^{-6}\ \mathrm{mol\,dm^{-3}}}
\]

and

\[
\boxed{[\mathrm{HBrO_2}]_{\mathrm B}=5.04\times10^{-11}\ \mathrm{mol\,dm^{-3}}}.
\]

Because \(1\ \mathrm M=1\ \mathrm{mol\,dm^{-3}}\), these are also
\(6.00\times10^{-6}\ \mathrm M\) and
\(5.04\times10^{-11}\ \mathrm M\), respectively.

## Derivation

Use mass-action rates for the elementary steps printed in the problem. Write
\(x=[\mathrm{HBrO_2}]\), and denote the rates of steps (1)--(5) by
\(r_1,\ldots,r_5\).

### Process A

The relevant mass-action rates are

\[
r_1=k_1x[\mathrm{BrO_3^-}][\mathrm{H^+}],\qquad
r_2=k_2[\mathrm{BrO_2^\bullet}][\mathrm{Ce^{3+}}][\mathrm{H^+}],
\qquad r_3=k_3x^2.
\]

Step (1) produces two \(\mathrm{BrO_2^\bullet}\) radicals and step (2)
consumes one, so the radical steady-state equation is

\[
0=\frac{d[\mathrm{BrO_2^\bullet}]}{dt}=2r_1-r_2,
\quad\text{hence}\quad r_2=2r_1.
\]

The stoichiometric coefficients of \(\mathrm{HBrO_2}\) in steps (1), (2),
and (3) are \(-1,+1,-2\), respectively. Its steady-state equation is therefore

\[
0=\frac{dx}{dt}=-r_1+r_2-2r_3.
\]

Substitution of \(r_2=2r_1\) gives \(r_1=2r_3\). On the active, nonzero
Process-A branch, canceling \(x\) gives

\[
x=\frac{k_1[\mathrm{BrO_3^-}][\mathrm{H^+}]}{2k_3}
=\frac{(1.0\times10^4)(0.06)(0.8)}{2(4.0\times10^7)}
=6.00\times10^{-6}\ \mathrm M.
\]

The uncancelled algebraic equations also have the inactive solution \(x=0\),
for which every Process-A rate in this balance vanishes. The requested
stationary concentration *while Process A occurs* selects the positive branch.
The Lean theorem exposes this branch condition explicitly.

### Process B

Only steps (4) and (5) consume or produce \(\mathrm{HBrO_2}\):

\[
r_4=k_4x[\mathrm{Br^-}][\mathrm{H^+}],\qquad
r_5=k_5[\mathrm{BrO_3^-}][\mathrm{Br^-}][\mathrm{H^+}]^2.
\]

Thus

\[
0=\frac{dx}{dt}=-r_4+r_5.
\]

During active Process B, \([\mathrm{Br^-}]>0\); the printed proton
concentration is also positive. Canceling the common
\([\mathrm{Br^-}][\mathrm{H^+}]\) factor gives

\[
x=\frac{k_5[\mathrm{BrO_3^-}][\mathrm{H^+}]}{k_4}
=\frac{(2.1)(0.06)(0.8)}{2.0\times10^9}
=5.04\times10^{-11}\ \mathrm M.
\]

Step (6) does not enter this balance because it changes \(\mathrm{HBrO}\), not
\(\mathrm{HBrO_2}\). If \([\mathrm{Br^-}]=0\), both \(r_4\) and \(r_5\)
would vanish and this equation would not determine \(x\); that is the inactive
zero-bromide degeneracy, not the stated occurring Process B.

## Numerical reporting

No intermediate result was rounded. The exact raw values formalized in Lean
are

\[
\frac{6}{1{,}000{,}000}\ \mathrm M
\quad\text{and}\quad
\frac{504}{10{,}000{,}000{,}000{,}000}\ \mathrm M.
\]

For the required three-significant-figure displays, their final-place quanta
are \(10^{-8}\ \mathrm M\) and \(10^{-13}\ \mathrm M\), respectively. Both raw
values already lie exactly on the corresponding reporting grid, producing
`6.00 × 10⁻⁶` and `5.04 × 10⁻¹¹`.

## Source grounding

- `TASK.json` identifies T2-A2, the two requested numerical outputs, their
  units, and the three-significant-figure reporting rule.
- `icho_2026_source/image/T2_page-2.png` and page 16 of
  `icho_2026_source/raw/theory_problem.pdf` give elementary steps (1)--(7), all
  rate constants, the maintained values
  \([\mathrm{BrO_3^-}]=0.06\ \mathrm M\) and
  \([\mathrm{H^+}]=0.8\ \mathrm M\), the alternating active-process context,
  and the exact wording of question 2.2. `T2_page-1.png` supplies the preceding
  BZ-reaction context.
- Blank student answer-sheet pages 19 and 20 of the original PDF contain the
  separate fields \([\mathrm{HBrO_2}]_\mathrm A=\_\ \mathrm M\) and
  \([\mathrm{HBrO_2}]_\mathrm B=\_\ \mathrm M\). They add no numerical data or
  special precision instruction.
- The only general scientific rule added to those inputs is the standard
  mass-action rate law for an elementary reaction. The steady-state
  approximation is applied by setting the relevant species derivatives to
  zero. No fallback value printed for later subquestions is used.

There is no numerical source gap. The positivity conditions needed for valid
cancellation are the explicit mathematical form of selecting an occurring,
chemically active Process A or B; the formalization does not silently assume
them.
