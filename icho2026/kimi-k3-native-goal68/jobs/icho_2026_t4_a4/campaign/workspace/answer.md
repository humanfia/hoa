# IChO 2026 — Theory Problem T4, Subquestion A4 (question 4.4)

## Question (verbatim, official English paper, page Q4-2)

> **4.4** **Calculate** the energy released in this reaction (ΔE, MeV), if the binding energy
> BE(²³⁵U) = 7.59 MeV/nucleon and average binding energy for fission products
> BE(fis.) = 8.45 MeV/nucleon. *Neglect* the binding energy of free neutrons.

## Answer

**ΔE = 185.2 MeV, reported as 185 MeV (three significant figures).**

The blank student answer sheet (page A4-2) requests exactly one numeric entry:
"ΔE : ___ MeV", so 185 MeV (raw 185.2 MeV) is the submitted answer.

## Source grounding

All inputs come from the printed problem materials only:

1. **The reaction ("this reaction")** is the fission equation of subquestion 4.3,
   derived from problem-only information:
   - The shared context prints ²³⁵U + ¹n → … + 3 ¹n: **three** neutrons are emitted.
   - The yield curve P(A) printed on page Q4-1 has its two maxima at
     **A ≈ 93** and **A ≈ 140–141**.
   - The two product elements must lie in the **same group** of the Periodic Table,
     and mass/charge conservation require A₁ + A₂ = 236 − 3 = 233 and
     Z₁ + Z₂ = 92.
   - The unique pair satisfying all of these is rubidium (Z = 37, group 1) and
     caesium (Z = 55, group 1): 37 + 55 = 92 and 93 + 140 = 233, matching the
     graph peaks. Hence

         ²³⁵U + ¹n → ⁹³Rb + ¹⁴⁰Cs + 3 ¹n

2. **Numerical data printed in 4.4:** BE(²³⁵U) = 7.59 MeV/nucleon,
   BE(fis.) = 8.45 MeV/nucleon, free-neutron binding to be neglected.

3. **Consistency check from the paper itself:** question 4.9 offers the
   fallback "If you did not get an answer for 4.4, use ΔE = 200 MeV", which is
   a rough substitute consistent in magnitude with the exact result 185.2 MeV.

## Physical reasoning

Binding energy is the energy needed to split a nucleus into free nucleons.
Energy is **released** whenever the total binding energy of the final state
exceeds that of the initial state. With free neutrons carrying no binding
energy (as instructed), and the absorbed neutron being free as well:

- Nucleons bound initially: 235 (the ²³⁵U nucleus).
  Total initial binding energy: 235 × 7.59 = 1783.65 MeV.
- Nucleons bound in the fragments: 236 − 3 = 233 (= 93 + 140 in Rb and Cs).
  Total final binding energy: 233 × 8.45 = 1968.85 MeV.

Therefore

    ΔE = 1968.85 − 1783.65 = 185.20 MeV ≈ 185 MeV (3 s.f.).

The sign is positive: the fission products are more tightly bound in total
than ²³⁵U, so the reaction releases energy — as it must, since energy release
is stated in the shared context.

No intermediate rounding is performed; the value 185.2 MeV is exact under the
printed binding energies, and only the final display is rounded to the
three-significant-figure reporting default (quantum 1 MeV).

## Formalization

`IChO2026Problems/problem_icho_2026_t4_a4.lean` proves:

- `mass_balance : 93 + 140 + freeNeutrons = nucleonsInitial` — the 4.3
  equation conserves nucleon number (236 = 236).
- `charge_balance : 37 + 55 = 92` — the equation conserves charge.
- `nucleons_fission_products_value : nucleonsFissionProducts = 233`.
- `fissionEnergy_eq : fissionEnergy = 233 * 8.45 - 235 * 7.59` — the
  energy-balance law with the stoichiometry inserted.
- `fissionEnergy_value : fissionEnergy = 185.2` — the exact raw answer.
- `products_binding_energy : (233:ℝ) * 8.45 = 1968.85` and
  `uranium_binding_energy : (235:ℝ) * 7.59 = 1783.65` — the two intermediate
  totals.
- `fission_releases_energy : 0 < fissionEnergy` — energy is indeed released.
- `submission_valid : ValidNumericSubmission fissionEnergy submission` —
  the display 185 MeV at quantum 1 MeV obeys the answer-blind
  `ReportsAtQuantum` contract for the raw value 185.2.
- `t4_a4_answer` — the main result bundling all of the above.

Axiom audit (`#print axioms IChO2026.T4.A4.t4_a4_answer`):
`[propext, Classical.choice, Quot.sound]` — standard Lean logical axioms only;
no `sorryAx` and no custom axioms.

## Assumptions and source gaps

- The phrase "this reaction" is interpreted as the 4.3 equation
  ²³⁵U + n → ⁹³Rb + ¹⁴⁰Cs + 3n, derived inline from problem text, the printed
  yield curve, and periodic-table structure (general scientific knowledge).
  The numeric result does not depend on which same-group fragment pair is
  chosen, only on the conserved nucleon counts (235 bound initially, 233 bound
  finally), which the shared context fixes independently of 4.3's answer.
- "Neglect the binding energy of free neutrons" is applied to all four
  neutrons appearing in the equation (the absorbed one and the three emitted
  ones) — none contributes binding energy in the balance.
- No measured-value tolerances enter: the printed binding energies are used
  as exact stipulated inputs, per the measurement policy for stipulated
  constants.
