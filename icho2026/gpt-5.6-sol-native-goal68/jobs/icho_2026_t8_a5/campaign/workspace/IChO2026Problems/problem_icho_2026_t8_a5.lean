import IChO2026Chem.Reporting

/-!
# IChO 2026 T8-A5: surface density of the molecular catalyst

This file keeps the numerical data printed in the problem separate from the
calculation.  All quantities are expressed by their numerical values in the
units printed in the booklet.  Consequently, the final quotient has unit
`molecules nm⁻²`.

The phrase "mass fraction of catalyst" is used in its defining sense

`catalyst mass / total mass of the loaded sample`.

Thus a loaded sample of mass `m` contains catalyst mass `ω * m` and support
mass `(1 - ω) * m`.  This distinction is needed because the supplied specific
surface area is per gram of C₃N₄ support, not per gram of loaded composite.
-/

namespace IChO2026Problems.T8A5

open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem inputs -/

/-- Printed catalyst mass fraction, `ω_cat = 3.8 %`. -/
def catalystMassFraction : ℝ := 38 / 1000

/-- Printed specific surface area of C₃N₄, in `m² g⁻¹`. -/
def specificSurfaceArea : ℝ := 178 / 10

/-- Printed molar mass of catalyst 1, in `g mol⁻¹`. -/
def catalystMolarMass : ℝ := 55721 / 100

/-- Avogadro constant printed in the general-information sheet, in `mol⁻¹`. -/
def avogadroConstant : ℝ := 6022 * 10 ^ 20

/-- Number of square nanometres in one square metre.

The general-information sheet gives `1 nm = 10⁻⁹ m`; squaring the reciprocal
gives `1 m² = 10¹⁸ nm²`.
-/
def squareNanometresPerSquareMetre : ℝ := 10 ^ 18

theorem squareNanometre_conversion : ((10 : ℝ) ^ 9) ^ 2 =
    squareNanometresPerSquareMetre := by
  norm_num [squareNanometresPerSquareMetre]

/-! ## Derived calculation -/

/-- Number of catalyst molecules in a loaded sample whose total mass is `m` g. -/
def catalystMolecules (m : ℝ) : ℝ :=
  (catalystMassFraction * m / catalystMolarMass) * avogadroConstant

/-- C₃N₄ surface area of a loaded sample of total mass `m` g, in `nm²`. -/
def supportAreaNm2 (m : ℝ) : ℝ :=
  ((1 - catalystMassFraction) * m) * specificSurfaceArea *
    squareNanometresPerSquareMetre

/-- Requested number of catalytic molecules per `nm²`, evaluated directly
from the printed data. -/
def catalystSurfaceDensity : ℝ :=
  catalystMassFraction * avogadroConstant /
    (catalystMolarMass * (1 - catalystMassFraction) * specificSurfaceArea *
      squareNanometresPerSquareMetre)

/-- On a one-gram loaded-sample basis, 3.8% catalyst leaves 0.962 g of support. -/
theorem oneGram_support_mass :
    (1 - catalystMassFraction) * (1 : ℝ) = 962 / 1000 := by
  norm_num [catalystMassFraction]

/-- The arbitrary sample mass cancels from the molecules-per-area quotient. -/
theorem surfaceDensity_independent_of_sample_mass (m : ℝ) (hm : 0 < m) :
    catalystMolecules m / supportAreaNm2 m = catalystSurfaceDensity := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  norm_num [catalystMolecules, supportAreaNm2, catalystSurfaceDensity,
    catalystMassFraction, catalystMolarMass, specificSurfaceArea,
    avogadroConstant, squareNanometresPerSquareMetre] at hm0 ⊢
  field_simp
  ring

/-- Exact raw result before decimal reporting. -/
theorem catalyst_surface_density_exact :
    catalystSurfaceDensity = 5720900000 / 2385360289 := by
  norm_num [catalystSurfaceDensity, catalystMassFraction, catalystMolarMass,
    specificSurfaceArea, avogadroConstant,
    squareNanometresPerSquareMetre]

/-- The raw value lies in the rounding bin for `2.40` at quantum `0.01`. -/
theorem catalyst_surface_density_rounding_bounds :
    (240 : ℝ) / 100 - (1 / 100) / 2 ≤ catalystSurfaceDensity ∧
      catalystSurfaceDensity < (240 : ℝ) / 100 + (1 / 100) / 2 := by
  rw [catalyst_surface_density_exact]
  norm_num

/-- Submission retaining both the exact raw calculation and its requested
three-significant-figure display. -/
def catalystSurfaceDensitySubmission : NumericSubmission where
  rawValue := catalystSurfaceDensity
  reportedValue := 240 / 100
  reportingQuantum := 1 / 100

/-- Final requested output: the exact raw surface density reports as
`2.40 molecules nm⁻²` to three significant figures. -/
theorem catalyst_surface_density_reported :
    ValidNumericSubmission catalystSurfaceDensity
      catalystSurfaceDensitySubmission := by
  constructor
  · rfl
  · change ReportsAtQuantum catalystSurfaceDensity (240 / 100) (1 / 100)
    refine ⟨by norm_num, ?_, ?_⟩
    · exact ⟨240, by norm_num [catalystSurfaceDensitySubmission]⟩
    · rw [if_pos]
      · exact catalyst_surface_density_rounding_bounds
      · rw [catalyst_surface_density_exact]
        norm_num

#print axioms surfaceDensity_independent_of_sample_mass
#print axioms catalyst_surface_density_exact
#print axioms catalyst_surface_density_reported

end

end IChO2026Problems.T8A5
