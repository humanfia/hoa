# IChO 2026 - Problem T2, subquestion 2.7 (target `icho_2026_t2_a7`)

**Question (official English, problem page Q2-4 of `theory_problem.pdf`,
printed page 4):**

> Which graph qualitatively illustrates the rate of change of Gibbs energy
> (dG/dt) of a **closed** system in which an oscillatory reaction occurs?
> Tick the correct box.

The six candidate graphs appear only on the blank student answer sheet
(A2-6, PDF page 24 = index 23), arranged in a 3 x 2 grid.

## Answer

**Tick the bottom-right box (row 3, column 2 of the grid on answer sheet
A2-6)** - the graph in which dG/dt

* starts far below zero (large negative value at t = 0),
* stays strictly negative for all t > 0,
* oscillates while it rises, with the oscillation amplitude decaying, and
* tends to 0 from below as t grows.

## Source-grounding of the candidate set

Rendered at 200 dpi from `icho_2026_source/raw/theory_problem.pdf`
(sha256 af51373f..., page index 23, sheet code "A2-6"), the six options are,
in reading order:

| position | sketch of dG/dt vs t |
|---|---|
| 1. top-left | starts at 0 and decreases along a straight line (constant negative rate, never approaching 0) |
| 2. top-right | steady oscillation **about the time axis** (takes positive values) |
| 3. middle-left | starts very negative and rises **monotonically** toward 0 (no oscillation) |
| 4. middle-right | starts at 0, descends with small ripple along a fixed downward slope (never approaches 0) |
| 5. bottom-left | oscillation **about the axis** whose amplitude **grows** with time (takes positive values) |
| 6. bottom-right | starts very negative, rises toward 0 with **decaying** oscillation, always below the axis |

## Reasoning (answer-blind, from the problem text and general laws only)

1. **Sign - the second law of thermodynamics**
   (allowed source: `trusted_general_law`).  In a *closed* system at constant
   temperature and pressure, a spontaneous overall process decreases the
   Gibbs energy: dG/dt <= 0, with equality only at equilibrium.  Therefore
   the correct graph can **never** take positive values.  This immediately
   eliminates options 2 and 5, which oscillate about the axis and are
   positive for half of every period.

2. **Closed system implies the oscillation is transient, so dG/dt -> 0-.**
   The problem statement (part 2.1) states that in the BZ reaction malonic
   acid is oxidised to CO2 and BrO3- is reduced to Br-, with Ce(IV) as
   **catalyst**: the oscillation concerns only the *intermediates*
   (Ce4+/Ce3+, Br-, HBrO2), while the bulk reactants are steadily consumed.
   In a closed vessel no fresh reactant enters, so the overall reaction must
   wind down toward equilibrium, and dG/dt tends to 0 from below.
   This eliminates option 1 (constant negative rate forever) and option 4
   (fixed downward trend forever) - a forever-negative, non-vanishing dG/dt
   would mean the closed system never equilibrates, contradicting the second
   law for finite initial reactant amounts.

3. **The oscillation must be visible but decaying.**
   Because the reaction *is* oscillatory (that is the premise), dG/dt must
   oscillate too: the intermediates' concentrations oscillate, modulating the
   instantaneous overall rate of Gibbs-energy decrease.  Option 3 shows a
   perfectly monotone relaxation with no ripple, so it misses the oscillatory
   modulation.  The amplitude must *decay* - not grow - because the approach
   to equilibrium shrinks the thermodynamic driving force and hence the rate
   modulation: option 5 (growing amplitude) is doubly impossible, both for
   its positive excursions and its growth.

4. **Initial behaviour.**  At t = 0 the freshly mixed reactants
   ([BrO3-]0 = 0.06 M, [MA]0 = 0.1 M, ..., from the shared context) are far
   from equilibrium, so G decreases fastest at the start: dG/dt begins at a
   large negative value, not at 0.  This matches the bottom-right sketch,
   whose curve begins well below the axis, and not options 2 or 5 (start at
   the axis) or 1 and 4 (start at the axis and stay on a fixed slope).

Only the **bottom-right** graph satisfies all four constraints: strictly
negative for all t > 0, large magnitude at t = 0, genuine oscillation with
decaying amplitude, and limit 0 from below as t grows.

## Formalization

`IChO2026Problems/problem_icho_2026_t2_a7.lean` formalizes the qualitative
shape of each candidate as predicates on curves `f : R -> R`:

* `P1 f` - strictly negative for all t > 0 (second-law screen);
* `P2 f` - starts at magnitude >= 1 below the axis at t = 0 (far from
  equilibrium);
* `P3 f` - `Tendsto f atTop (nhds 0)` (closed system equilibrates);
* `P4 f` - a decaying envelope bounds |f| on the physical half-line;
* `P5 f` - arbitrary-late strict local maxima (genuine, non-monotone
  oscillation);
* `P6 f` - the oscillation dies out (uniform tube property);

and defines `OptionSixShape f := P1 f /\ P2 f /\ P3 f /\ P4 f /\ P5 f /\ P6 f`,
the shape of the bottom-right sketch.  The file exhibits the concrete
representative

```
fRepr t = -(2 + cos (8t)) / (2*(t + 1))
```

(always negative on t >= 0, `fRepr 0 = -3/2`, tends to 0, perpetual ripple of
amplitude about `1/(2(t+1))`) and proves `OptionSixShape fRepr`
(`theorem optionSixShape_fRepr`).  It then proves the exclusion screens:

* `positive_violates_P1` + `sine_fails_P1` + `growing_sine_fails_P1`:
  options 2 and 5 (about-axis oscillations) fail P1;
* `constant_rate_fails_P3` + `negative_slope_fails_P3`: options 1 and 4
  (non-decaying negative rate) fail P3;
* `monotone_fails_P5` + `optionThree_shape_fails_P5`: option 3
  (monotone relaxation) fails P5.

The final theorem `answer_is_bottom_right : OptionSixShape fRepr` records the
selected option.  All proofs are complete from Mathlib; `#print axioms`
reports only `propext, Classical.choice, Quot.sound` (see
`verification.md`).

## Assumptions and source gaps

* The six candidates are line drawings without a printed legend; the
  formalization uses the qualitative predicates described above.  No
  numerical data beyond the shared context is needed.
* The only external scientific input is the second law of thermodynamics for
  closed systems at constant T and p (dG/dt <= 0 for the spontaneous overall
  direction, equality at equilibrium), an allowed `trusted_general_law`.
* No source gap affects the answer: the problem statement supplies the
  "closed system" and "oscillatory reaction" premises and the BZ
  overall-reaction information used in step 2.
