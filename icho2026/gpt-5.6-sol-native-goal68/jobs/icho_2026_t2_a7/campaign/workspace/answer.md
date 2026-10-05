# IChO 2026 T2-A7

## Answer

Tick the **bottom-right box** (third row, right column): the curve in which
\(dG/dt\) oscillates entirely on the negative side of zero, with a decaying
amplitude, and approaches zero from below.

## Reasoning

For the standard use of Gibbs energy—spontaneous evolution of a closed system
at constant temperature and pressure, with no non-expansion work—the entropy
production inequality gives

\[
\frac{dG}{dt}=-T\frac{d_iS}{dt}\le 0.
\]

Thus an oscillatory reaction may make the *magnitude* of the Gibbs-energy loss
oscillate, but it may not make \(dG/dt\) cross above zero. Because the system is
closed, it is not continuously replenished. Its chemical driving force is
eventually exhausted and it relaxes toward equilibrium, where
\(dG/dt\to 0\). The transient oscillations must therefore die away.

This eliminates the other five drawings:

- the top-left and middle-left curves are not oscillatory;
- the top-right and bottom-left curves repeatedly have \(dG/dt>0\);
- the middle-right curve oscillates below zero but trends farther from zero;
- only the bottom-right curve oscillates without becoming positive and damps
  toward zero.

## Source grounding and scope

- `TASK.json` identifies the requested output as the qualitative
  `gibbs_rate_graph` classification and reproduces the statement that the
  system is closed and the reaction oscillatory.
- `icho_2026_source/image/T2_page-4.png` and PDF page 18 (one-indexed) contain
  question 2.7. `T2_page-3.png` contains the preceding BZ oscillation context.
- The six selectable curves are not printed on Q2-4 itself. They occur on the
  blank student answer sheet A2-6, PDF page 24 (one-indexed). Reading its 3-by-2
  grid row by row, the required damped, nonpositive curve is the sixth,
  bottom-right choice.
- The checked SHA-256 values match the hashes in `TASK.json`:
  `b5e103f6fca031d7080e03073c4dad882142bd4e53cc0690f4140eaa4f6dea47`
  for `T2_page-4.png`,
  `c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260`
  for `T2_page-3.png`, and
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`
  for `theory_problem.pdf`.

There is one genuine qualification in the problem-only source: it says
“closed” but does not explicitly say constant temperature and pressure or
exclude non-expansion work. Closedness by itself does not make Gibbs energy
monotone under arbitrary thermal/mechanical forcing. The selected graph is
therefore the answer under the standard, evidently intended isothermal and
isobaric spontaneous-reaction interpretation. The formalization keeps this
condition explicit rather than claiming it for every possible closed system.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t2_a7.lean` separates the model premises
from their consequences:

1. `ContinuousFixedTPClosedOscillatoryEvolution` models the literal printed
   derivative with `HasDerivAt`. Its antitonicity, oscillation, and equilibrium
   limit fields are explicit premises, not custom axioms.
2. `gibbsDerivative_nonpositive` proves that the literal derivative is at most
   zero at every time, and `continuous_gibbs_rate_constraints` collects the
   three physical graph constraints.
3. A separate discrete model proves rather than assumes the limiting result:
   `gibbs_tends_to_infimum` applies monotone convergence to a lower-bounded,
   nonincreasing Gibbs sequence, and `stepGibbsRate_tends_to_zero` proves its
   forward changes tend to zero.
4. `graphFeatures` transcribes the visible properties of all six answer-sheet
   curves. `satisfies_constraints_iff_bottomRight` exhausts all constructors
   and proves that the three required properties hold exactly for the
   bottom-right graph.
5. `continuous_system_selects_bottomRight` combines the literal-derivative
   constraints with that exhaustive classification and proves uniqueness.

The source supplies no explicit kinetic function from which a concrete
derivative curve could be constructed. Accordingly, the continuous theorem is
conditional on a differentiable Gibbs trajectory with the stated physical
properties; the discrete theorem independently verifies that the analogous
relaxation follows from monotonicity and a lower bound.
