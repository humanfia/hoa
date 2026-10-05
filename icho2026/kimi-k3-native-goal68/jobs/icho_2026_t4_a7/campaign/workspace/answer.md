# IChO 2026 — Theory Problem 4, Part 4.7 (icho_2026_t4_a7)

**Question.** Calculate ΔrH₂₀₀₀ (kJ mol⁻¹) per mole of methane combustion
reaction at 2000 K. Assume all species are gaseous.

## Answer

**ΔrH₂₀₀₀ = −782 kJ mol⁻¹** (raw, unrounded value −781.876 kJ mol⁻¹; reported
to three significant figures per the answer-blind reporting default).

## Working (from problem-supplied data only)

Combustion reaction (from the shared Problem 4 statement, all species gaseous):

    CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)

Data stipulated in Part 4.6 (page Q4-2 of the problem):

| quantity                    | value            |
|-----------------------------|------------------|
| ΔfH°₂₉₈(CH₄)                | −74.8 kJ mol⁻¹   |
| ΔfH°₂₉₈(H₂O, gas)           | −241.8 kJ mol⁻¹  |
| ΔfH°₂₉₈(CO₂)                | −393.5 kJ mol⁻¹  |
| Cₚ(CH₄)                     | 35 J mol⁻¹ K⁻¹   |
| Cₚ(H₂O, gas)                | 34 J mol⁻¹ K⁻¹   |
| Cₚ(O₂)                      | 29 J mol⁻¹ K⁻¹   |
| Cₚ(CO₂)                     | 37 J mol⁻¹ K⁻¹   |

**Step 1 — Part 4.6 prerequisite (derived inline, Hess's law).** O₂(g) is an
element in its standard state, so ΔfH°₂₉₈(O₂) = 0.

    ΔrH°₂₉₈ = [ΔfH°₂₉₈(CO₂) + 2·ΔfH°₂₉₈(H₂O,g)] − [ΔfH°₂₉₈(CH₄) + 2·0]
            = (−393.5) + 2·(−241.8) − (−74.8)
            = −802.3 kJ mol⁻¹

(The problem's printed fallback "use ΔH₂₉₈ = −750 kJ mol⁻¹" applies only when
4.6 was not answered; here it is, so the fallback is not used.)

**Step 2 — Kirchhoff's law with the problem's constant heat capacities.** The
table gives single, temperature-independent Cₚ values; no temperature
dependence is supplied anywhere in the problem, so Cₚ is taken constant:

    ΔCₚ = Cₚ(CO₂) + 2·Cₚ(H₂O,g) − Cₚ(CH₄) − 2·Cₚ(O₂)
        = 37 + 2·34 − 35 − 2·29
        = +12 J mol⁻¹ K⁻¹ = 0.012 kJ mol⁻¹ K⁻¹

    ΔrH(T) = ΔrH°₂₉₈ + ΔCₚ·(T − 298)

**Step 3 — Evaluate at T = 2000 K:**

    ΔrH₂₀₀₀ = −802.3 + 0.012·(2000 − 298)
            = −802.3 + 0.012·1702
            = −802.3 + 20.424
            = −781.876 kJ mol⁻¹

Reported to three significant figures: **−782 kJ mol⁻¹**.

The red fallback printed under 4.7 ("use ΔH₂₀₀₀ = −700 kJ mol⁻¹") is explicitly
conditional on not obtaining an answer for 4.7; the problem data fully
determine the value, so the fallback is not used.

## Source grounding

- Question text: TASK.json `question`/`current_question` fields and the problem
  pages `T4_page-3.png` (Part 4.7 box) and `T4_page-2.png` (Part 4.6 data
  table), printed pages 2–3 of Problem 4 (source page 39 of
  `theory_problem.pdf`).
- All numerical inputs (formation enthalpies, heat capacities, 2000 K target
  temperature, "all species gaseous") are stipulated on the problem pages.
- The only externally sourced physics is standard trusted-general-law
  thermochemistry: Hess's law, ΔfH° of an element in its standard state = 0,
  and Kirchhoff's law dH/dT = ΔCₚ, applied with the problem's constant Cₚ
  values. No official solution, marking scheme, or external answer was
  consulted.

## Lean formalization

See `IChO2026Problems/problem_icho_2026_t4_a7.lean`:

- `CombustionStoichiometry.unique` — atom balances plus "one mole of methane
  consumed" force ν = (−1, −2, +1, +2) for (CH₄, O₂, CO₂, H₂O).
- `reaction_enthalpy_298` — Hess's-law value ΔrH°₂₉₈ = −802.3 kJ mol⁻¹
  (the Part 4.6 prerequisite, proved from the problem data).
- `reaction_heat_capacity` — ΔCₚ = 12 J mol⁻¹ K⁻¹ from the problem data.
- `reaction_enthalpy_2000_exact` — Kirchhoff's-law value
  ΔrH₂₀₀₀ = −781.876 kJ mol⁻¹, exactly.
- `reported_at_2000`, `final_submission_valid` — certificates that −782
  kJ mol⁻¹ is the nearest 3-significant-figure (quantum 1 kJ mol⁻¹) display of
  the raw value under the workspace's answer-blind reporting contract.
