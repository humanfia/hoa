import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A6: gaseous methane combustion at 298 K

The numerical entries in `problemThermodynamicData` are the data printed in
question 4.6.  They are kept separate from the derived reaction enthalpy.
The only additional chemistry convention is
`oxygenStandardFormationEnthalpy`: the standard enthalpy of formation of
O₂(g), an element in its reference state at 298 K, is zero by definition.

The reaction formalized below is

`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`.
-/

namespace IChO2026Problems.T4A6

open IChO2026Chem.Reporting

noncomputable section

/-- Elements needed to check the atom balance of methane combustion. -/
inductive Element where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq

/-- The four gaseous species in the stated combustion reaction. -/
inductive Species where
  | methane
  | oxygen
  | carbonDioxide
  | waterVapor
  deriving DecidableEq, Fintype

/-- Number of atoms of an element in one molecule of a species. -/
def atomCount : Element → Species → ℕ
  | .carbon, .methane => 1
  | .carbon, .oxygen => 0
  | .carbon, .carbonDioxide => 1
  | .carbon, .waterVapor => 0
  | .hydrogen, .methane => 4
  | .hydrogen, .oxygen => 0
  | .hydrogen, .carbonDioxide => 0
  | .hydrogen, .waterVapor => 2
  | .oxygen, .methane => 0
  | .oxygen, .oxygen => 2
  | .oxygen, .carbonDioxide => 2
  | .oxygen, .waterVapor => 1

/-- Stoichiometric coefficients on the reactant side, per mole of CH₄. -/
def reactantCoefficient : Species → ℕ
  | .methane => 1
  | .oxygen => 2
  | .carbonDioxide => 0
  | .waterVapor => 0

/-- Stoichiometric coefficients on the product side, per mole of CH₄. -/
def productCoefficient : Species → ℕ
  | .methane => 0
  | .oxygen => 0
  | .carbonDioxide => 1
  | .waterVapor => 2

/-- Total atoms of `e` on one side specified by its coefficient function. -/
def sideAtomCount (coefficients : Species → ℕ) (e : Element) : ℕ :=
  ∑ s : Species, coefficients s * atomCount e s

/-- The combustion equation used for Hess's-law calculation conserves C, H,
and O atoms. -/
theorem methane_combustion_is_balanced (e : Element) :
    sideAtomCount reactantCoefficient e =
      sideAtomCount productCoefficient e := by
  cases e <;> decide

/-- The complete thermodynamic table printed under question 4.6.  Formation
enthalpies are in kJ mol⁻¹ and heat capacities in J mol⁻¹ K⁻¹.
The displayed decimals are exact inputs under the task's stipulated-constant
policy. -/
structure ThermodynamicData where
  methaneFormation : ℝ
  waterVaporFormation : ℝ
  carbonDioxideFormation : ℝ
  methaneHeatCapacity : ℝ
  waterVaporHeatCapacity : ℝ
  oxygenHeatCapacity : ℝ
  carbonDioxideHeatCapacity : ℝ

/-- Problem-only numerical inputs transcribed from Q4-2. -/
def problemThermodynamicData : ThermodynamicData where
  methaneFormation := -(748 : ℝ) / 10
  waterVaporFormation := -(2418 : ℝ) / 10
  carbonDioxideFormation := -(3935 : ℝ) / 10
  methaneHeatCapacity := 35
  waterVaporHeatCapacity := 34
  oxygenHeatCapacity := 29
  carbonDioxideHeatCapacity := 37

/-- Trusted general thermochemical convention: O₂(g) is oxygen's reference
state at 298 K, so its standard enthalpy of formation is zero. -/
def oxygenStandardFormationEnthalpy : ℝ := 0

/-- Formation enthalpy at 298 K for each species relevant to this reaction. -/
def formationEnthalpy298 (data : ThermodynamicData) : Species → ℝ
  | .methane => data.methaneFormation
  | .oxygen => oxygenStandardFormationEnthalpy
  | .carbonDioxide => data.carbonDioxideFormation
  | .waterVapor => data.waterVaporFormation

/-- Stoichiometry-weighted formation-enthalpy sum over all four species. -/
def weightedFormationEnthalpy
    (coefficients : Species → ℕ) (formationEnthalpy : Species → ℝ) : ℝ :=
  (coefficients .methane : ℝ) * formationEnthalpy .methane +
  (coefficients .oxygen : ℝ) * formationEnthalpy .oxygen +
  (coefficients .carbonDioxide : ℝ) * formationEnthalpy .carbonDioxide +
  (coefficients .waterVapor : ℝ) * formationEnthalpy .waterVapor

/-- Hess's law: the product formation-enthalpy sum minus the reactant sum. -/
def hessReactionEnthalpy
    (products reactants : Species → ℕ) (formationEnthalpy : Species → ℝ) : ℝ :=
  weightedFormationEnthalpy products formationEnthalpy -
    weightedFormationEnthalpy reactants formationEnthalpy

/-- Raw standard reaction enthalpy in kJ mol⁻¹ for one mole of methane. -/
def methaneCombustionEnthalpy298 : ℝ :=
  hessReactionEnthalpy productCoefficient reactantCoefficient
    (formationEnthalpy298 problemThermodynamicData)

/-- The generic Hess sum reduces to the familiar product-minus-reactant
expression for the balanced methane combustion equation. -/
theorem methane_combustion_hess_expansion :
    methaneCombustionEnthalpy298 =
      (problemThermodynamicData.carbonDioxideFormation +
        2 * problemThermodynamicData.waterVaporFormation) -
      (problemThermodynamicData.methaneFormation +
        2 * oxygenStandardFormationEnthalpy) := by
  norm_num [methaneCombustionEnthalpy298, hessReactionEnthalpy,
    weightedFormationEnthalpy,
    productCoefficient, reactantCoefficient, formationEnthalpy298,
    problemThermodynamicData, oxygenStandardFormationEnthalpy]

/-- Exact raw result before final-answer rounding: −802.3 kJ mol⁻¹. -/
theorem combustion_enthalpy_298_raw :
    methaneCombustionEnthalpy298 = -(8023 : ℝ) / 10 := by
  rw [methane_combustion_hess_expansion]
  norm_num [problemThermodynamicData, oxygenStandardFormationEnthalpy]

/-- The answer-blind submission keeps the exact raw value and reports it to a
unit quantum, appropriate to three significant figures at magnitude 10². -/
def combustionEnthalpy298Submission : NumericSubmission where
  rawValue := -(8023 : ℝ) / 10
  reportedValue := -802
  reportingQuantum := 1

/-- The raw value has hundreds magnitude, so a unit quantum is the
three-significant-figure place. -/
theorem combustion_enthalpy_298_reporting_scale :
    (100 : ℝ) ≤ |methaneCombustionEnthalpy298| ∧
      |methaneCombustionEnthalpy298| < 1000 ∧
      combustionEnthalpy298Submission.reportingQuantum = 1 := by
  rw [combustion_enthalpy_298_raw]
  norm_num [combustionEnthalpy298Submission, abs_of_nonpos]

/-- Requested output: the raw Hess-law result is validly rounded to
−802 kJ mol⁻¹ at a 1 kJ mol⁻¹ quantum (three significant figures). -/
theorem combustion_enthalpy_298_reported :
    ValidNumericSubmission methaneCombustionEnthalpy298
      combustionEnthalpy298Submission := by
  constructor
  · simpa [combustionEnthalpy298Submission] using
      combustion_enthalpy_298_raw.symm
  · change ReportsAtQuantum (-(8023 : ℝ) / 10) (-802) 1
    refine ⟨by norm_num, ⟨(-802 : ℤ), by norm_num⟩, ?_⟩
    norm_num

/-- Complete formal answer to T4-A6, exhibiting the exact raw calculation,
the displayed numerical answer, and a proof that the display is the specified
rounding of the raw value. -/
theorem combustion_enthalpy_298_answer :
    methaneCombustionEnthalpy298 = -(8023 : ℝ) / 10 ∧
      combustionEnthalpy298Submission.reportedValue = -802 ∧
      ValidNumericSubmission methaneCombustionEnthalpy298
        combustionEnthalpy298Submission := by
  exact ⟨combustion_enthalpy_298_raw, by
    norm_num [combustionEnthalpy298Submission],
    combustion_enthalpy_298_reported⟩

end

end IChO2026Problems.T4A6

#print axioms IChO2026Problems.T4A6.methane_combustion_is_balanced
#print axioms IChO2026Problems.T4A6.methane_combustion_hess_expansion
#print axioms IChO2026Problems.T4A6.combustion_enthalpy_298_raw
#print axioms IChO2026Problems.T4A6.combustion_enthalpy_298_reporting_scale
#print axioms IChO2026Problems.T4A6.combustion_enthalpy_298_reported
#print axioms IChO2026Problems.T4A6.combustion_enthalpy_298_answer
