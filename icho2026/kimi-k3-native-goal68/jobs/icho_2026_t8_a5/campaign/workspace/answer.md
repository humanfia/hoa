# IChO 2026, Theory Problem 8.5 (target `icho_2026_t8_a5`)

## Question (as printed on Q8-2)

"Calculate the number of catalytic molecules per nm², $N_{cat}$, of C₃N₄
loaded with **1**, when the mass fraction of catalyst, $\omega_{cat}$ = 3.8 %,
if the specific surface area of C₃N₄ is 17.8 m² g⁻¹. $M_{cat}$ =
557.21 g mol⁻¹."  (5.0 pt)

The blank answer sheet (PDF page A8-5) asks only for $N_{cat} = \_\_\_\_$.

The answer sheet supplies no extra precondition on the definition or units of
$N_{cat}$ ; hence the question is answered directly from the mass fraction,
molar mass, specific surface area and the Avogadro constant printed in the
problem booklet.

## Solution

Take a basis of **1 g of C₃N₄ support** ("per gram of C₃N₄ loaded with **1**",
as 8.7 puts it). At a mass fraction of catalyst $\omega_{cat}=3.8\,\%$:

1. Mass of catalyst per g of support:

   $$m_{cat} = \omega_{cat} \times 1\ \text{g} = 0.038\ \text{g}.$$

2. Number of catalyst molecules:

   $$N = \frac{m_{cat}}{M_{cat}}\,N_A
       = \frac{0.038\ \text{g}}{557.21\ \text{g mol}^{-1}}
         \times 6.022\times 10^{23}\ \text{mol}^{-1}
       = 4.107\times 10^{19}\ \text{molecules}.$$

3. Surface area available per g of support:

   $$A = 17.8\ \text{m}^2 = 17.8\times 10^{18}\ \text{nm}^2
       \qquad (1\ \text{nm}^2 = 10^{-18}\ \text{m}^2).$$

4. Surface density:

   $$N_{cat} = \frac{\omega_{cat}\,N_A}{M_{cat}\,SSA}\times 10^{-18}
   = \frac{0.038 \times 6.022\times 10^{23}}
           {557.21\ \text{g mol}^{-1} \times 17.8\ \text{m}^2\ \text{g}^{-1}}
     \times \frac{1}{10^{18}\ \text{nm}^2\ \text{m}^{-2}}$$

   $$N_{cat} = 2.307\ldots \ \textbf{molecules nm}^{-2}
   \;\bigl(\equiv 2.31\times 10^{18}\ \text{molecules m}^{-2}\bigr).$$

**Answer: $N_{cat} \approx 2.31$ molecules nm⁻²** (3 significant figures,
per the project reporting default).

### Measurement-interval check

Treating each printed quantity as a measurement with half-width of one half of
its last displayed quantum (ω = 3.8 % ± 0.05 %; M = 557.21 ± 0.005;
SSA = 17.8 ± 0.05; N_A = 6.022×10²³ ± 0.0005×10²³), the density ranges over
the corners

* lower corner (ω = 3.7995 %, M = 557.215, SSA = 17.85, N_A = 6.0215×10²³):
  N_cat = 2.30022… nm⁻²
* upper corner (ω = 3.8005 %, M = 557.205, SSA = 17.75, N_A = 6.0225×10²³):
  N_cat = 2.31421… nm⁻²

Both corners, like the central value, round to **2.3 nm⁻²**, and the 3 s.f.
value 2.31 lies strictly inside the envelope [2.3002, 2.3143].  The reported
answer is therefore stable against the half-quantum reading errors of the
printed measurands.  (All bounds proved exactly in the Lean file; no
intermediate rounding is used anywhere.)

## Source grounding

- ω_cat = 3.8 %, SSA = 17.8 m² g⁻¹, M_cat = 557.21 g mol⁻¹ — printed in
  question 8.5 (Q8-2 page; confirmed in the embedded text of
  `theory_problem.pdf`, page Q8-2).
- N_A = 6.022×10²³ mol⁻¹ — "Physical Constants and Equations" page G1-3 of the
  same official problem PDF (page 3 of 93): "Avogadro constant
  N_A = 6.022 × 10²³ mol–1".
- Answer-sheet A8-5 shows only "$N_{cat}$ = ____", so no extra data are hidden
  on the answer sheet.
- The "gram" in the SSA unit and the mass-fraction basis are understood the
  same way as in question 8.7 ("per gram of C₃N₄ loaded with **1**"); the
  density is intensive, so the 1 g basis cancels in the ratio.
- No results from other subquestions are needed (8.5 is a standalone
  mass-balance/geometry calculation).

No external competition solutions were consulted; the derivation uses only the
printed inputs and the definitions of mass fraction, molar mass, the Avogadro
constant, and 1 nm² = 10⁻¹⁸ m².
