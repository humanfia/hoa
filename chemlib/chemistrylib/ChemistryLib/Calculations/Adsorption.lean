import Mathlib.Data.Real.Basic

/-!
# Adsorption calculations

Real-valued mass-balance formulas for equilibrium adsorption capacity and the
corresponding adsorbate-to-pore number ratio. All empirical quantities and the
mass-unit conversion scale remain explicit parameters.

Source: sanitized corpus entry `icho_2026_t3_a7:T3-A7`, IChO 2026 Theory Task 3,
part A7, “Into Reticular Chemistry”
(<https://scheikundeolympiade.science.ru.nl/internationaal/2026/IChO2026%20Theory%20task%20final%20English.pdf>).
-/

namespace ChemistryLib.Adsorption

noncomputable section

/-- The adsorbate-to-pore number ratio obtained from an adsorption capacity. -/
def adsorbateToPoreRatio : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun capacity massScale frameworkMassPerMoleOfPores adsorbateMolarMass =>
    capacity * massScale * frameworkMassPerMoleOfPores / adsorbateMolarMass

theorem adsorbateToPoreRatio_eq
    {capacity massScale frameworkMassPerMoleOfPores adsorbateMolarMass : ℝ} :
    adsorbateToPoreRatio capacity massScale frameworkMassPerMoleOfPores adsorbateMolarMass =
      capacity * massScale * frameworkMassPerMoleOfPores / adsorbateMolarMass := by
  rfl

/-- Equilibrium adsorption capacity from the solution mass balance. -/
def equilibriumCapacity : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun initialConcentration equilibriumConcentration volume adsorbentMass =>
    (initialConcentration - equilibriumConcentration) * volume / adsorbentMass

theorem equilibriumCapacity_eq
    {initialConcentration equilibriumConcentration volume adsorbentMass : ℝ} :
    equilibriumCapacity initialConcentration equilibriumConcentration volume adsorbentMass =
      (initialConcentration - equilibriumConcentration) * volume / adsorbentMass := by
  rfl

theorem physicalDomain_nonneg
    {initialConcentration equilibriumConcentration volume adsorbentMass massScale
      frameworkMassPerMoleOfPores adsorbateMolarMass : ℝ}
    (_hEquilibriumConcentrationNonneg : 0 ≤ equilibriumConcentration)
    (hEquilibriumLeInitial : equilibriumConcentration ≤ initialConcentration)
    (hVolumeNonneg : 0 ≤ volume)
    (hAdsorbentMassPos : 0 < adsorbentMass)
    (hMassScaleNonneg : 0 ≤ massScale)
    (hFrameworkMassPerMoleOfPoresNonneg : 0 ≤ frameworkMassPerMoleOfPores)
    (hAdsorbateMolarMassPos : 0 < adsorbateMolarMass) :
    0 ≤ equilibriumCapacity initialConcentration equilibriumConcentration volume adsorbentMass ∧
      0 ≤ adsorbateToPoreRatio
        (equilibriumCapacity initialConcentration equilibriumConcentration volume adsorbentMass)
        massScale frameworkMassPerMoleOfPores adsorbateMolarMass := by
  have hCapacityNonneg :
      0 ≤ (initialConcentration - equilibriumConcentration) * volume / adsorbentMass :=
    div_nonneg
      (mul_nonneg (sub_nonneg.mpr hEquilibriumLeInitial) hVolumeNonneg)
      (le_of_lt hAdsorbentMassPos)
  constructor
  · exact hCapacityNonneg
  · exact
      div_nonneg
        (mul_nonneg (mul_nonneg hCapacityNonneg hMassScaleNonneg)
          hFrameworkMassPerMoleOfPoresNonneg)
        (le_of_lt hAdsorbateMolarMassPos)

end

end ChemistryLib.Adsorption
