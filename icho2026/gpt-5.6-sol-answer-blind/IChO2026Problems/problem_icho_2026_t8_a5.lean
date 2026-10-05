import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T8, part A5

The numerical quantities below are represented by real numbers in the printed
units.  The mass fraction is catalyst mass divided by the total mass of the
loaded composite.  Hence a reference sample of total mass `m` contains
`ω * m` grams of catalyst and `(1 - ω) * m` grams of C₃N₄ support.
-/

namespace IChO2026T8A5

noncomputable section

/-- Printed catalyst mass fraction, `3.8 %` of the total loaded composite. -/
def catalystMassFraction : ℝ := (38 : ℝ) / 1000

/-- Printed specific surface area of C₃N₄, in `m² g⁻¹` of support. -/
def specificSupportArea_m2_per_g : ℝ := (178 : ℝ) / 10

/-- Printed molar mass of catalyst 1, in `g mol⁻¹`. -/
def catalystMolarMass_g_per_mol : ℝ := (55721 : ℝ) / 100

/-- The exact SI Avogadro constant, in molecules per mole. -/
def avogadroConstant_per_mol : ℝ := 602214076000000000000000

/-- Unit conversion from one square metre to square nanometres. -/
def squareNanometresPerSquareMetre : ℝ := (10 : ℝ) ^ (18 : ℕ)

/-- Catalyst mass in a loaded-composite sample of total mass `totalMass_g`. -/
def catalystMassFor (totalMass_g : ℝ) : ℝ :=
  catalystMassFraction * totalMass_g

/-- C₃N₄ support mass in a loaded-composite sample of total mass `totalMass_g`. -/
def supportMassFor (totalMass_g : ℝ) : ℝ :=
  (1 - catalystMassFraction) * totalMass_g

/-- The total-mixture mass-fraction convention and its solved catalyst/support
mass ratio.  This prevents treating `3.8 %` as catalyst mass per gram of support. -/
theorem total_mixture_mass_fraction_basis (totalMass_g : ℝ)
    (h_totalMass : 0 < totalMass_g) :
    catalystMassFor totalMass_g + supportMassFor totalMass_g = totalMass_g ∧
      catalystMassFor totalMass_g / totalMass_g = catalystMassFraction ∧
      catalystMassFor totalMass_g / supportMassFor totalMass_g =
        catalystMassFraction / (1 - catalystMassFraction) := by
  have h_totalMass_ne : totalMass_g ≠ 0 := ne_of_gt h_totalMass
  constructor
  · unfold catalystMassFor supportMassFor
    ring
  constructor
  · unfold catalystMassFor
    field_simp
  · unfold catalystMassFor supportMassFor
    field_simp [catalystMassFraction, h_totalMass_ne]

/-- Amount of catalyst 1, in moles, for a reference loaded-composite mass. -/
def catalystAmountMolFor (totalMass_g : ℝ) : ℝ :=
  catalystMassFor totalMass_g / catalystMolarMass_g_per_mol

/-- Number of catalyst molecules for a reference loaded-composite mass. -/
def catalystMoleculeCountFor (totalMass_g : ℝ) : ℝ :=
  catalystAmountMolFor totalMass_g * avogadroConstant_per_mol

/-- C₃N₄ surface area, in `nm²`, for a reference loaded-composite mass. -/
def supportSurfaceAreaNm2For (totalMass_g : ℝ) : ℝ :=
  supportMassFor totalMass_g * specificSupportArea_m2_per_g *
    squareNanometresPerSquareMetre

/-- Catalyst molecules per square nanometre for a reference total mass. -/
def catalystSurfaceDensityFor (totalMass_g : ℝ) : ℝ :=
  catalystMoleculeCountFor totalMass_g / supportSurfaceAreaNm2For totalMass_g

/-- The requested exact raw quantity, evaluated on a one-gram reference sample.
The following theorem records that the choice of positive reference mass cancels. -/
def rawCatalystSurfaceDensity : ℝ := catalystSurfaceDensityFor 1

/-- Positivity and fraction-domain side conditions supplied by the printed data. -/
def SourceInputConditions : Prop :=
  0 < catalystMassFraction ∧ catalystMassFraction < 1 ∧
    0 < specificSupportArea_m2_per_g ∧
    0 < catalystMolarMass_g_per_mol ∧
    0 < avogadroConstant_per_mol ∧
    0 < squareNanometresPerSquareMetre

/-- The computed density is independent of the arbitrary positive total mass
chosen for the loaded-composite reference sample. -/
theorem surface_density_independent_of_positive_reference_mass
    (totalMass_g : ℝ) (h_totalMass : 0 < totalMass_g) :
    catalystSurfaceDensityFor totalMass_g = rawCatalystSurfaceDensity := by
  have h_totalMass_ne : totalMass_g ≠ 0 := ne_of_gt h_totalMass
  unfold rawCatalystSurfaceDensity catalystSurfaceDensityFor
    catalystMoleculeCountFor catalystAmountMolFor catalystMassFor
    supportSurfaceAreaNm2For supportMassFor catalystMassFraction
    catalystMolarMass_g_per_mol avogadroConstant_per_mol
    specificSupportArea_m2_per_g squareNanometresPerSquareMetre
  field_simp

/-- Source-to-result specification: solve the total-mass balance first, convert
catalyst mass to molecules, and divide by the support area in square nanometres.
The final equality is an exact reduced rational evaluation, not a rounded input. -/
def CatalystSurfaceDensityRawSpec : Prop :=
  SourceInputConditions ∧
    catalystMassFor 1 = (38 : ℝ) / 1000 ∧
    supportMassFor 1 = (962 : ℝ) / 1000 ∧
    catalystMassFor 1 + supportMassFor 1 = 1 ∧
    rawCatalystSurfaceDensity =
      (((catalystMassFraction / (1 - catalystMassFraction)) /
          catalystMolarMass_g_per_mol) * avogadroConstant_per_mol) /
        (specificSupportArea_m2_per_g * squareNanometresPerSquareMetre) ∧
    rawCatalystSurfaceDensity = (5721033722 : ℝ) / 2385360289

/-- Exact raw derivation together with a non-degenerate certified decimal
enclosure: `2.39839 ≤ Ncat ≤ 2.39840` molecules per square nanometre. -/
theorem catalyst_surface_density_raw :
    CatalystSurfaceDensityRawSpec ∧
      (239839 : ℝ) / 100000 ≤ rawCatalystSurfaceDensity ∧
      rawCatalystSurfaceDensity ≤ (1499 : ℝ) / 625 := by
  norm_num [CatalystSurfaceDensityRawSpec, SourceInputConditions,
    rawCatalystSurfaceDensity, catalystSurfaceDensityFor,
    catalystMoleculeCountFor, catalystAmountMolFor, catalystMassFor,
    supportSurfaceAreaNm2For, supportMassFor, catalystMassFraction,
    catalystMolarMass_g_per_mol, avogadroConstant_per_mol,
    specificSupportArea_m2_per_g, squareNanometresPerSquareMetre]

/-- Candidate-payload spelling of the three-significant-figure result. -/
theorem catalyst_surface_density_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      rawCatalystSurfaceDensity ((240 : ℝ) / 100) ((1 : ℝ) / 100) := by
  have hraw :
      rawCatalystSurfaceDensity = (5721033722 : ℝ) / 2385360289 :=
    catalyst_surface_density_raw.1.2.2.2.2.2
  refine ⟨by norm_num, ⟨240, by norm_num⟩, ?_⟩
  rw [if_pos]
  · rw [hraw]
    norm_num
  · rw [hraw]
    norm_num

/-- Reduced-fraction spelling used by the deterministic numeric-reporting
guard.  This is the same `2.40` result as the payload spelling above. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"catalyst_surface_density","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"2.40","reporting_quantum":"0.01","raw_declaration":"IChO2026T8A5.rawCatalystSurfaceDensity","reporting_declaration":"IChO2026T8A5.catalyst_surface_density_reporting_certificate"}
theorem catalyst_surface_density_reporting_certificate :
    IChO2026Chem.Reporting.ReportsAtQuantum
      rawCatalystSurfaceDensity ((12 : ℝ) / 5) ((1 : ℝ) / 100) := by
  simpa only [show ((240 : ℝ) / 100) = (12 : ℝ) / 5 by norm_num] using
    catalyst_surface_density_reported

end
end IChO2026T8A5
