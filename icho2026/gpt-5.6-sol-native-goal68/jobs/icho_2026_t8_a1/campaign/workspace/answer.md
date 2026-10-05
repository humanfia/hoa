# IChO 2026 T8-A1

## Answer

\[
\boxed{\mathrm{CO_2 + 2\,H^+ + 2\,e^- \longrightarrow CO + H_2O}}
\]

The equation is written in the reduction direction: the electrons are on the
reactant side.

## Derivation and checks

Start with the conversion specified by the question, `CO2 → CO`.

1. Carbon is already balanced with coefficient 1 on both sides.
2. The reactant has two O atoms, while CO has one. Add one `H2O` to the product
   side to balance oxygen.
3. That water contributes two H atoms. Because the medium is acidic, add two
   `H+` to the reactant side.
4. The reactant side now has charge `+2`. Add two electrons to that side, making
   its net charge zero, equal to the neutral product side.

The final atom totals are `C: 1 = 1`, `O: 2 = 1 + 1`, and `H: 2 = 2`.  The
charge totals are `2(+1) + 2(-1) = 0` on the left and `0` on the right.  Thus
both atoms and charge are conserved, and exactly two electrons are consumed.
No physical-state labels are added because the prompt does not request or
fully stipulate them.

## Source grounding

- `TASK.json` identifies the sole requested output as the balanced acidic
  CO2-to-CO reduction half-equation, including the electron count.
- `icho_2026_source/image/T8_page-1.png` visibly contains question 8.1 with the
  same wording. Its SHA-256 hash is
  `3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843`,
  matching `TASK.json`.
- The original `icho_2026_source/raw/theory_problem.pdf` was inspected directly.
  PDF page 72 contains Q8-1 and the prompt; PDF page 77 is the corresponding
  blank student answer sheet A8-1. The 8.1 box on that sheet is empty, so it
  supplies no answer. The PDF hash is
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`,
  also matching `TASK.json`.

The problem supplies the transformation and acidic medium. The only general
chemistry rules used in the derivation are formula interpretation and
conservation of atoms and electric charge; `H2O`, `H+`, and `e-` are the
standard balancing species for an acidic reduction half-equation. No previous
part result or external answer is used, and there is no source gap affecting
this result.

## Formalization correspondence

`IChO2026Problems/problem_icho_2026_t8_a1.lean` represents the equation as the
coefficient tuple `(CO2, H+, e-, CO, H2O) = (1, 2, 2, 1, 1)`. It proves carbon,
hydrogen, oxygen, and charge balance from explicit atom-count and charge
definitions. It also proves that any balanced equation in this acidic
half-equation template with the CO2 coefficient normalized to one has exactly
these five coefficients.
