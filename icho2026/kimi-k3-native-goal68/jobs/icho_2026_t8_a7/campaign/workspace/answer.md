# IChO 2026, Theory 8.7 (T8-A7) — Answer

**Answer: box (a) — the overall rate of CO formation per gram of C₃N₄ loaded with 1 *increases* with increasing ω_cat.**

## Problem statement (as printed)

Page Q8-3 of `theory_problem.pdf` (= `source_page` 74), immediately above question
8.7, shows a diagram of "the change in the TOF of CO as ω_cat is varied".  Its red
data points are labelled:

| ω_cat (%) | 0.1 | 0.3 | 0.6 | 1.0 | 2.0 | 2.9 | 3.8 |
|-----------|-----|-----|-----|-----|-----|-----|-----|
| TOF (h⁻¹) | 62  | 56  | 37  | 29  | 15  | 11  | 8   |

Question 8.7 (2.0 pt): "How does the overall rate of CO formation per gram of
C₃N₄ loaded with 1 change with increasing ω_cat? Tick the correct box.
a) increases  b) decreases  c) doesn't change."
The blank student answer sheet A8-6 gives three empty boxes a/b/c — no hint is
included.

## Reasoning

The trap in this question is that the *diagram itself slopes down*: the turnover
frequency per catalyst molecule falls as loading rises.  But the question asks for
the rate **per gram of loaded material**, so we must multiply TOF by the number of
catalyst molecules present in one gram.

From the problem-stated TOF definition (page Q8-2: "TOF is the number of product
molecules formed per active catalyst molecule per hour"):

    rate per gram  =  TOF x (catalyst molecules per gram)
                   =  TOF(omega) x (omega/100) x N_A / M_cat

with N_A = 6.022e23 mol^-1 (official constants page G1-3) and M_cat = 557.21
g mol^-1 (given in 8.5).  So the per-gram rate is proportional to the product
omega x TOF(omega).  Evaluating this product at every printed point:

| omega_cat (%)        | 0.1 | 0.3  | 0.6  | 1.0 | 2.0 | 2.9  | 3.8  |
|----------------------|-----|------|------|-----|-----|------|------|
| omega x TOF (%.h^-1) | 6.2 | 16.8 | 22.2 | 29  | 30  | 31.9 | 30.4 |

Reading across the measured range, the product climbs from 6.2 to about 31,
roughly five-fold, before dipping slightly at the very last point
(31.9 -> 30.4, ~5 %).  The overall rate per gram therefore **increases** with
omega_cat — precisely the reverse of the TOF trend, because the number of
catalyst molecules per gram grows linearly with the loading while TOF drops
more slowly than 1/omega over the stated range.

A robustness check under the project measurement convention (an integer display
is consistent with plus-or-minus half of the last displayed quantum) shows:

* The end-to-end conclusion is rock solid: even at the worst tolerance corners,
  rate(3.8 %) >= 3.8 x 7.5 = 28.5 versus rate(0.1 %) <= 0.1 x 62.5 = 6.25
  (in units of %.h^-1), a stricter-than-4.5-fold increase (and ~4.9-fold at the
  displayed values).
* Every interior step rises strictly already at the displayed values
  (6.2 -> 16.8 -> 22.2 -> 29 -> 30 -> 31.9).
* The small final step (2.9 % -> 3.8 %) is *not* sign-determined by the
  diagram: displays 11 -> 8 are compatible with true values 10.5 -> 8.5
  (increasing to 32.3) as well as 11.5 -> 7.5 (decreasing to 28.125).  The
  classification question asks for the overall behaviour, which is
  unambiguously an increase; this residual one-step ambiguity is honestly
  discharged in the Lean file as `last_step_direction_not_determined`.

Independent cross-check of the axis reading: the text on Q8-2 states a TOF of
8 h^-1 for 10 mg of C₃N₄ loaded with omega_cat = 3.8 %, matching the last data
point of the diagram exactly.

## Source grounding

* Diagram with the seven labelled points `(omega_cat %, TOF h^-1)`:
  `icho_2026_source/image/T8_page-3.png` (page Q8-3 of `theory_problem.pdf`,
  verified at 6x zoom directly from the PDF page).
* Question text 8.7 and the blank answer boxes: page Q8-3 and answer sheet
  A8-6 (blank — verified directly from the PDF).
* TOF definition, M_cat = 557.21 g mol^-1, reference point TOF = 8 h^-1 at
  omega_cat = 3.8 %: page Q8-2 (`T8_page-2.png`).
* N_A = 6.022e23 mol^-1: official constants page G1-3 of `theory_problem.pdf`.

No official solutions, marking schemes, external solver agents, or answer
repositories were used.

## Formalization

`IChO2026Problems/problem_icho_2026_t8_a7.lean` defines
`coRatePerGram omega tof = tof x (omega/100) x N_A / M_cat` from the
problem-stated TOF definition and proves:

* `co_rate_trend` — the requested classification:
  `tickedBox = RateTrend.increases`, together with the strict end-to-end
  inequality `rate(0.1 %, 62) < rate(3.8 %, 8)`.
* `measured_rates_increase_interior` — strict increase along every consecutive
  pair of measured interior points (0.1 % ... 2.9 %).
* `endpoint_rate_increases_robust` — the end-to-end increase persists for *any*
  true TOF values consistent with the half-quantum tolerance of the integer
  displays.
* `last_step_direction_not_determined` — the final small step is compatible
  with both directions within tolerance; reported honestly rather than
  over-claimed.
* Structural facts: `catMoleculesPerGram_strictMonoOn` (more loading gives
  strictly more catalyst molecules per gram) and `coRatePerGram_strictMono_tof`
  (rate strictly increases in TOF at fixed loading).

Compilation: `lake env lean IChO2026Problems/problem_icho_2026_t8_a7.lean`
exits 0; `#print axioms` reports only `propext, Classical.choice, Quot.sound`
(standard Lean logical axioms; no `sorryAx`, no custom axioms).  Full details
in `verification.md`.
