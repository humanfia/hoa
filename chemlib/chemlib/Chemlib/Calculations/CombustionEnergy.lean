import Chemlib.Thermochemistry.TemperatureCorrection

/-!
# Ideal-gas combustion-energy throughput

An ideal-gas pressure-volume throughput at its measured gas-state temperature
determines an amount throughput.  The released energy is the amount multiplied
by the negated molar reaction enthalpy, with the enthalpy independently
corrected from its reference temperature to the target reaction temperature.

Source:

* `icho_2026_t4_a8:T4-A8`, IChO 2026 Theory Task 4.8, p. 39:
  <https://scheikundeolympiade.science.ru.nl/internationaal/2026/IChO2026%20Theory%20task%20final%20English.pdf>
-/

namespace Chemlib.Thermochemistry

/-- Amount throughput inferred from an ideal-gas pressure-volume state. -/
noncomputable def idealGasAmount : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun pressure volume gasConstant gasTemperature ↦
    pressure * volume / (gasConstant * gasTemperature)

/-- Positive released energy associated with an exothermic molar reaction
enthalpy. -/
def releasedEnergy : ℝ → ℝ → ℝ :=
  fun amount molarReactionEnthalpy ↦ amount * (-molarReactionEnthalpy)

/-- Released energy from ideal-gas amount throughput and a reaction enthalpy
corrected between independent thermochemical temperatures. -/
noncomputable def idealGasReleasedEnergyAt : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun pressure volume gasConstant gasTemperature referenceEnthalpy deltaCp
      referenceTemperature targetTemperature ↦
    releasedEnergy (idealGasAmount pressure volume gasConstant gasTemperature)
      (reactionEnthalpyAt referenceEnthalpy deltaCp referenceTemperature targetTemperature)

/-- The composed combustion-energy calculation is amount times the corrected
molar reaction enthalpy. -/
theorem idealGasReleasedEnergyAt_eq :
    {pressure volume gasConstant gasTemperature referenceEnthalpy deltaCp
      referenceTemperature targetTemperature : ℝ} →
    idealGasReleasedEnergyAt pressure volume gasConstant gasTemperature
        referenceEnthalpy deltaCp referenceTemperature targetTemperature =
      releasedEnergy (idealGasAmount pressure volume gasConstant gasTemperature)
        (reactionEnthalpyAt referenceEnthalpy deltaCp referenceTemperature
          targetTemperature) := by
  intro pressure volume gasConstant gasTemperature referenceEnthalpy deltaCp
    referenceTemperature targetTemperature
  rfl

/-- Released energy is nonnegative for a nonnegative amount and a nonpositive
molar reaction enthalpy. -/
theorem releasedEnergy_nonneg :
    {amount molarReactionEnthalpy : ℝ} →
    0 ≤ amount →
    molarReactionEnthalpy ≤ 0 →
    0 ≤ releasedEnergy amount molarReactionEnthalpy := by
  intro amount molarReactionEnthalpy hAmount hEnthalpy
  exact mul_nonneg hAmount (neg_nonneg.mpr hEnthalpy)

/-- The ideal-gas amount and released-energy functions expose their defining
formulas. -/
theorem idealGasEnergyFormulas :
    (pressure volume gasConstant gasTemperature amount molarReactionEnthalpy : ℝ) →
    idealGasAmount pressure volume gasConstant gasTemperature =
        pressure * volume / (gasConstant * gasTemperature) ∧
      releasedEnergy amount molarReactionEnthalpy =
        amount * (-molarReactionEnthalpy) := by
  intro pressure volume gasConstant gasTemperature amount molarReactionEnthalpy
  constructor <;> rfl

/-- On the physical sign domain, both ideal-gas amount throughput and composed
released energy are nonnegative. -/
theorem idealGasCombustion_physicalDomain_nonneg :
    {pressure volume gasConstant gasTemperature referenceEnthalpy deltaCp
      referenceTemperature targetTemperature : ℝ} →
    0 ≤ pressure →
    0 ≤ volume →
    0 < gasConstant →
    0 < gasTemperature →
    reactionEnthalpyAt referenceEnthalpy deltaCp referenceTemperature
        targetTemperature ≤ 0 →
    0 ≤ idealGasAmount pressure volume gasConstant gasTemperature ∧
      0 ≤ idealGasReleasedEnergyAt pressure volume gasConstant gasTemperature
        referenceEnthalpy deltaCp referenceTemperature targetTemperature := by
  intro pressure volume gasConstant gasTemperature referenceEnthalpy deltaCp
    referenceTemperature targetTemperature hPressure hVolume hGasConstant
    hGasTemperature hEnthalpy
  have hAmount : 0 ≤ idealGasAmount pressure volume gasConstant gasTemperature := by
    exact div_nonneg (mul_nonneg hPressure hVolume)
      (mul_nonneg (le_of_lt hGasConstant) (le_of_lt hGasTemperature))
  constructor
  · exact hAmount
  · exact releasedEnergy_nonneg hAmount hEnthalpy

end Chemlib.Thermochemistry
