import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A7: methane combustion enthalpy at 2000 K

The chemical equation is

`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`.

All printed decimal data are represented by exact rationals.  Heat capacities
are kept in J mol⁻¹ K⁻¹, so the constant-`Cₚ` Kirchhoff correction is divided by
1000 when it is added to an enthalpy in kJ mol⁻¹.  The standard formation
enthalpy of elemental O₂(g) is zero by the standard-state convention; this is
kept separate from the values printed in the problem.
-/

namespace IChO2026Problems.Icho2026T4A7

open IChO2026Chem.Reporting

noncomputable section

/-- A four-species table in the order used by the methane combustion reaction. -/
structure CombustionSpeciesData where
  ch4 : ℝ
  o2 : ℝ
  co2 : ℝ
  h2o : ℝ

/-- Products minus reactants for
`CH₄ + 2 O₂ → CO₂ + 2 H₂O`. -/
def methaneCombustionChange (d : CombustionSpeciesData) : ℝ :=
  d.co2 + 2 * d.h2o - (d.ch4 + 2 * d.o2)

namespace ProblemInput

/-- Standard formation enthalpies printed in T4-A6, in kJ mol⁻¹.
The oxygen field is supplied separately by the standard-state convention. -/
def formationEnthalpies298 : CombustionSpeciesData where
  ch4 := -74.8
  o2 := 0
  co2 := -393.5
  h2o := -241.8

/-- Constant-pressure molar heat capacities printed in T4-A6,
in J mol⁻¹ K⁻¹. -/
def heatCapacities : CombustionSpeciesData where
  ch4 := 35
  o2 := 29
  co2 := 37
  h2o := 34

def referenceTemperatureK : ℝ := 298
def targetTemperatureK : ℝ := 2000

end ProblemInput

/-- Kirchhoff's law evaluated with a constant reaction heat capacity.
`hRef` is in kJ mol⁻¹, `deltaCpJ` is in J mol⁻¹ K⁻¹, and temperatures are in K. -/
def kirchhoffConstantCp
    (hRef deltaCpJ referenceTemperature targetTemperature : ℝ) : ℝ :=
  hRef + deltaCpJ * (targetTemperature - referenceTemperature) / 1000

/-- The reaction enthalpy at 298 K obtained from the formation enthalpies. -/
def reactionEnthalpy298 : ℝ :=
  methaneCombustionChange ProblemInput.formationEnthalpies298

/-- The reaction heat-capacity change for the balanced combustion reaction. -/
def reactionHeatCapacity : ℝ :=
  methaneCombustionChange ProblemInput.heatCapacities

/-- The requested raw methane combustion enthalpy at 2000 K, in kJ mol⁻¹. -/
def reactionEnthalpy2000 : ℝ :=
  kirchhoffConstantCp
    reactionEnthalpy298
    reactionHeatCapacity
    ProblemInput.referenceTemperatureK
    ProblemInput.targetTemperatureK

/-- Explicit scientific model boundary.  An enthalpy function satisfies the
model when it has the formation-enthalpy value at 298 K and follows Kirchhoff's
law with the tabulated reaction heat capacity treated as constant. -/
def SatisfiesTabulatedConstantCpModel (enthalpy : ℝ → ℝ) : Prop :=
  enthalpy ProblemInput.referenceTemperatureK = reactionEnthalpy298 ∧
  ∀ temperature,
    enthalpy temperature =
      enthalpy ProblemInput.referenceTemperatureK +
        reactionHeatCapacity *
          (temperature - ProblemInput.referenceTemperatureK) / 1000

theorem reactionEnthalpy298_value :
    reactionEnthalpy298 = (-8023 : ℝ) / 10 := by
  norm_num [reactionEnthalpy298, methaneCombustionChange,
    ProblemInput.formationEnthalpies298]

theorem reactionHeatCapacity_value :
    reactionHeatCapacity = (12 : ℝ) := by
  norm_num [reactionHeatCapacity, methaneCombustionChange,
    ProblemInput.heatCapacities]

theorem temperatureRise_value :
    ProblemInput.targetTemperatureK - ProblemInput.referenceTemperatureK =
      (1702 : ℝ) := by
  norm_num [ProblemInput.targetTemperatureK, ProblemInput.referenceTemperatureK]

theorem kirchhoffCorrection_value :
    reactionHeatCapacity *
        (ProblemInput.targetTemperatureK - ProblemInput.referenceTemperatureK) /
        1000 =
      (20424 : ℝ) / 1000 := by
  rw [reactionHeatCapacity_value, temperatureRise_value]
  norm_num

/-- Exact unrounded answer: `-781.876 kJ mol⁻¹`. -/
theorem methane_combustion_enthalpy_2000_raw :
    reactionEnthalpy2000 = (-781876 : ℝ) / 1000 := by
  rw [show reactionEnthalpy2000 =
      reactionEnthalpy298 +
        reactionHeatCapacity *
          (ProblemInput.targetTemperatureK - ProblemInput.referenceTemperatureK) /
          1000 by
        rfl]
  rw [reactionEnthalpy298_value, kirchhoffCorrection_value]
  norm_num

/-- Any physical enthalpy function obeying the explicitly delimited model has
the requested value at 2000 K. -/
theorem methane_combustion_enthalpy_2000_of_constantCp_model
    (enthalpy : ℝ → ℝ)
    (hModel : SatisfiesTabulatedConstantCpModel enthalpy) :
    enthalpy ProblemInput.targetTemperatureK = (-781876 : ℝ) / 1000 := by
  rw [hModel.2 ProblemInput.targetTemperatureK, hModel.1,
    reactionEnthalpy298_value, reactionHeatCapacity_value,
    temperatureRise_value]
  norm_num

/-- The raw answer lies in the one-unit reporting interval centered at `-782`.
At this magnitude, a quantum of 1 kJ mol⁻¹ is three significant figures. -/
theorem methane_combustion_enthalpy_2000_reports_three_sig_figures :
    ReportsAtQuantum ((-781876 : ℝ) / 1000) (-782 : ℝ) 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨(-782 : ℤ), by norm_num⟩
  · norm_num

/-- Solver-owned submission, retaining the exact raw value separately from the
requested three-significant-figure display. -/
def methaneCombustionEnthalpy2000Submission : NumericSubmission where
  rawValue := reactionEnthalpy2000
  reportedValue := -782
  reportingQuantum := 1

/-- Final formalized output for T4-A7. -/
theorem methane_combustion_enthalpy_2000_submission_valid :
    ValidNumericSubmission
      reactionEnthalpy2000
      methaneCombustionEnthalpy2000Submission := by
  constructor
  · rfl
  · change ReportsAtQuantum reactionEnthalpy2000 (-782 : ℝ) 1
    rw [methane_combustion_enthalpy_2000_raw]
    exact methane_combustion_enthalpy_2000_reports_three_sig_figures

#print axioms methane_combustion_enthalpy_2000_raw
#print axioms methane_combustion_enthalpy_2000_of_constantCp_model
#print axioms methane_combustion_enthalpy_2000_reports_three_sig_figures
#print axioms methane_combustion_enthalpy_2000_submission_valid

end

end IChO2026Problems.Icho2026T4A7
