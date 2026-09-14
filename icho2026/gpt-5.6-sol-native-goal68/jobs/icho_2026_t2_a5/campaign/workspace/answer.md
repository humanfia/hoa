# IChO 2026 T2-A5

The oscillation period is

\[
\boxed{\tau = 48.1\ \mathrm{s}}
\]

to three significant figures. The unrounded value is
\(48.0844068661\ldots\ \mathrm{s}\).

## Derivation

Write \(v_i\) for the mass-action rate of elementary step \(i\).
The prerequisite steady-state concentrations are derived directly from the
printed mechanism, rather than from the fallback values.

For Process A, steady state of \(\mathrm{BrO_2^{\bullet}}\) gives

\[
2v_1-v_2=0,
\]

and steady state of \(\mathrm{HBrO_2}\) gives

\[
-v_1+v_2-2v_3=0.
\]

Eliminating \(v_2\) yields \(v_1=2v_3\), so the positive stationary
concentration is

\[
[\mathrm{HBrO_2}]_A
=\frac{k_1[\mathrm{BrO_3^-}][\mathrm{H^+}]}{2k_3}
=\frac{(1.0\times10^4)(0.06)(0.8)}{2(4.0\times10^7)}
=6.00\times10^{-6}\ \mathrm{M}.
\]

For Process B, the \(\mathrm{HBrO_2}\) steady-state equation is
\(v_5-v_4=0\). Cancelling the positive concentrations of bromide and
hydrogen ions gives

\[
[\mathrm{HBrO_2}]_B
=\frac{k_5[\mathrm{BrO_3^-}][\mathrm{H^+}]}{k_4}
=\frac{(2.1)(0.06)(0.8)}{2.0\times10^9}
=5.04\times10^{-11}\ \mathrm{M}.
\]

At the switch, the problem says that the rates of steps (4) and (1) are
equal. Hence

\[
k_4[\mathrm{HBrO_2}][\mathrm{Br^-}][\mathrm{H^+}]
=k_1[\mathrm{HBrO_2}][\mathrm{BrO_3^-}][\mathrm{H^+}],
\]

and therefore

\[
[\mathrm{Br^-}]_{\mathrm{critical}}
=\frac{k_1[\mathrm{BrO_3^-}]}{k_4}
=\frac{(1.0\times10^4)(0.06)}{2.0\times10^9}
=3.00\times10^{-7}\ \mathrm{M}.
\]

The long part of a cycle is the colourless Process B branch, where the
bromide concentration falls from \(7.0\times10^{-4}\ \mathrm{M}\) to the
critical value. In this branch steps (4) and (5) each consume one bromide ion.
Since \(v_4=v_5\), their combined bromide-consumption rate is

\[
-\frac{d[\mathrm{Br^-}]}{dt}
=v_4+v_5
=2k_4[\mathrm{HBrO_2}]_B[\mathrm{H^+}][\mathrm{Br^-}]
=\kappa[\mathrm{Br^-}],
\]

with

\[
\kappa
=2(2.0\times10^9)(5.04\times10^{-11})(0.8)
=0.16128\ \mathrm{s^{-1}}.
\]

Integration of this first-order decay gives

\[
\tau
=\frac{1}{\kappa}
  \ln\!\left(
    \frac{[\mathrm{Br^-}]_{\max}}
         {[\mathrm{Br^-}]_{\mathrm{critical}}}
  \right)
=\frac{1}{0.16128}
  \ln\!\left(\frac{7.0\times10^{-4}}{3.00\times10^{-7}}\right)
=48.0844068661\ldots\ \mathrm{s}.
\]

The source states that, after reaching the critical concentration, bromide
returns to its maximum almost immediately. Thus that reset time is neglected
relative to the slow Process B duration. This is also consistent with the
colourless branch being attributed to \(\mathrm{Ce^{3+}}\): the
\(\mathrm{Ce^{4+}}\)-dependent bromide-producing step (7) is negligible over
the modeled slow decay and belongs to the rapid regeneration part of the
cycle.

## Source grounding and formalization

- `TASK.json` identifies the only requested output as the period \(\tau\) in
  seconds and fixes three-significant-figure reporting.
- `T2_page-2.png` supplies steps (1)--(7), their rate constants, the fixed
  concentrations, and the steady-state instruction for Processes A and B.
- `T2_page-3.png` supplies the switching criterion, the maximum bromide
  concentration, the slow decrease to the critical concentration, the
  near-instantaneous reset, and subquestion 2.5.
- The original `theory_problem.pdf` was checked at PDF page 17 for the question
  and at its blank student answer-sheet page 22. The answer sheet contains the
  field \(\tau=\underline{\hspace{2cm}}\ \mathrm{s}\), confirming that no
  additional unit or precision condition is present there.
- The Lean file separates the printed constants from the derived rate
  balances. It proves both prerequisite stationary concentrations, the
  critical concentration, the slow-phase rate law and endpoint, the exact raw
  expression
  \[
  \tau=\frac{3125}{504}\ln\!\left(\frac{7000}{3}\right),
  \]
  and the certified reporting interval \(48.05\le\tau<48.15\), which justifies
  the displayed value \(48.1\ \mathrm{s}\).

No official solution, marking scheme, grading report, historical answer, or
answer repository was used.
