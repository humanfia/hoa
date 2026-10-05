# IChO 2026 — T4-A6: Enthalpy of methane combustion at 298 K

## Reaction

CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)

## Result

**Δ_rH°₂₉₈ = −802.3 kJ mol⁻¹**

(All species gaseous; computed directly from the tabulated standard enthalpies of formation at 298 K.)

## Derivation

Hess's law for the standard reaction enthalpy:

Δ_rH°₂₉₈ = Σ Δ_fH°₂₉₈(products) − Σ Δ_fH°₂₉₈(reactants)

Using the thermodynamic data provided in the problem (page Q4-2):

| Species | Δ_fH°₂₉₈ (kJ mol⁻¹) |
|---------|---------------------|
| CH₄(g) | −74.8 |
| H₂O(g) | −241.8 |
| CO₂(g) | −393.5 |

Since Δ_fH°(O₂, g) = 0 (element in its standard state):

Δ_rH°₂₉₈ = [Δ_fH°(CO₂) + 2 Δ_fH°(H₂O)] − [Δ_fH°(CH₄) + 2 Δ_fH°(O₂)]
        = [(−393.5) + 2(−241.8)] − [(−74.8) + 2(0)]
        = −877.1 − (−74.8)
        = −802.3 kJ mol⁻¹

## Source grounding

- The problem explicitly asks for Δ_rH°₂₉₈ in kJ mol⁻¹ for one mole of methane combustion at 298 K with all species gaseous.
- The three enthalpies of formation required (CH₄, H₂O gas, CO₂) are all given in the table on page Q4-2.
- The heat-capacity values (C_P) provided in the same table are not needed for this subquestion; they would only enter for temperature corrections away from 298 K.
- The fallback value ΔH₂₉₈ = −750 kJ mol⁻¹ printed in red is only for students who fail to derive the answer; our derived value (−802.3) is the intended result.
