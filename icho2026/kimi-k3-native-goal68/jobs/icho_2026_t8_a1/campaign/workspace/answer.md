# IChO 2026, Theory Problem T8, Subquestion 8.1 (target `icho_2026_t8_a1`, 2.0 pt)

## Requested output

**Write** the half equation for the reduction of CO2 to CO in an acidic medium.

## Answer

$$\mathrm{CO_2 + 2\,H^+ + 2\,e^- \;\longrightarrow\; CO + H_2O}$$

## Why this is the answer (independent derivation)

The derivation uses only the printed reaction `CO2 --1--> CO` on the
problem page and the standard half-equation balancing conventions
(trusted general chemistry law for acidic aqueous medium: balance O with
H2O, balance H with H+, then balance charge with e-).

1. **Substrates (carbon).** The problem prints the net conversion
   `CO2 --1--> CO` above catalyst **1**, so one CO2 is consumed per one
   CO formed; carbon is already balanced 1 : 1.
2. **Oxygen.** CO2 has two O atoms, CO has one. One oxygen is left over
   on the left, so one H2O is added to the right: `CO2 -> CO + H2O`.
3. **Hydrogen.** With one H2O on the right, two H+ are needed on the
   left in acidic medium: `CO2 + 2 H+ -> CO + H2O`.
4. **Charge / electrons.** Left charge before electrons: 0 + 2 = +2;
   right charge: 0. Adding two electrons to the left equalizes charge:
   left 2 - 2 = 0 = right. Electrons on the reactant side make this a
   **reduction** half equation.
5. **Consistency check (electron count).** Carbon is +IV in CO2 and +II
   in CO, a gain of two electrons per carbon, matching the 2 e- found by
   charge balancing. This confirms the equation is internally consistent;
   it was not used to *assume* the electron count.

Uniqueness: given one CO2 in, one CO out, two electrons consumed on the
left, and only H+/H2O allowed as the acidic-medium reagents (H+ left,
H2O right), oxygen balance forces exactly 1 H2O (2*1 = 1 + n(H2O)) and
hydrogen balance then forces exactly 2 H+ (n(H+) = 2*1). No other
coefficients are possible for this skeleton.

## Source grounding

- `TASK.json` (`question`, `requested_outputs[0]`): "balanced acidic
  CO2-to-CO reduction half equation including electron count",
  exact symbolic reporting, no units.
- `theory_problem.pdf` source page 72 / image `T8_page-1.png` (both
  checked directly): subquestion **8.1** reads "*Write* the half equation
  for the reduction of CO2 to CO in an acidic medium. 2.0 pt", under the
  heading "T8. Recycling of Carbon Dioxide ... photocatalytic reduction
  of CO2 to CO using molecular catalyst **1**", with the printed scheme
  `CO2 --1--> CO`. The full page including the neighboring subquestions
  (8.2, 8.3) and the student answer-sheet area was read; none of it
  contains data needed for 8.1.
- No official solutions, marking schemes, grading reports, or answer
  repositories were used; the equation was derived from the balancing
  conventions above.

## Source gaps

None for this subquestion. Every input used (the CO2 -> CO conversion,
the acidic medium, the half-equation format) is printed in the problem
material or is a trusted general balancing law. No numerical data or
prior-part results were required.

## Formalization (Lean 4)

`IChO2026Problems/problem_icho_2026_t8_a1.lean` models each species by
its (C, O, H, charge) inventory, defines balance as equality of
coefficient-weighted totals on both sides, and proves:

- `IChO2026.Problems.T8.A1.half_equation_balanced` - the equation
  CO2 + 2 H+ + 2 e- -> CO + H2O conserves C, O, H and net charge.
- `IChO2026.Problems.T8.A1.is_reduction` - electrons are reactants
  (reduction half equation).
- `IChO2026.Problems.T8.A1.substrates_as_printed` - exactly one CO2
  consumed per one CO formed, as printed on the problem page.
- `IChO2026.Problems.T8.A1.two_electron_reduction` - 2 e- per CO2
  (carbon goes from +IV to +II).
- `IChO2026.Problems.T8.A1.coefficients_forced` - the acidic-medium
  coefficients (2 H+, 1 H2O) are uniquely forced by atom balance.

Build: `lake env lean IChO2026Problems/problem_icho_2026_t8_a1.lean`
succeeds; `#print axioms` reports only standard logical axioms
(`propext`, `Quot.sound`). See `verification.md`.
