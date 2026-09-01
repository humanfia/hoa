import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T4-A8

This file formalizes the source-side calculation of the energy released per
day by complete gaseous methane combustion at 2000 K.  Every numerical datum
below is either printed in T4-A6--A8, supplied by the controller-curated flow
unit correction, or is the printed ideal-gas constant.  The previous-part
enthalpy is derived inline; the printed `-700 kJ mol⁻¹` fallback is not used.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T4A8

noncomputable section

/-! ## Chemical identities, phases, and the complete-combustion reaction -/

/-- Elements whose atom ledgers are outcome-relevant for methane combustion. -/
inductive Element where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- The four gaseous species in the source-stipulated complete reaction. -/
inductive GasSpecies where
  | methane
  | oxygen
  | carbonDioxide
  | waterVapor
  deriving DecidableEq, Fintype, Repr

/-- The phase relevant to T4-A7/A8; the source says every species is gaseous. -/
inductive Phase where
  | gas
  deriving DecidableEq, Repr

/-- Molecular-formula atom counts for CH₄, O₂, CO₂, and H₂O(g). -/
def atomCount : GasSpecies → Element → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .methane, .oxygen => 0
  | .oxygen, .carbon => 0
  | .oxygen, .hydrogen => 0
  | .oxygen, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .hydrogen => 0
  | .carbonDioxide, .oxygen => 2
  | .waterVapor, .carbon => 0
  | .waterVapor, .hydrogen => 2
  | .waterVapor, .oxygen => 1

/-- Phase assignment implementing the problem's “all species are gaseous”. -/
def speciesPhase (_ : GasSpecies) : Phase := .gas

/-- Reactant coefficients in `CH₄(g) + 2 O₂(g)`. -/
def methaneCombustionReactants : GasSpecies → ℕ
  | .methane => 1
  | .oxygen => 2
  | .carbonDioxide => 0
  | .waterVapor => 0

/-- Product coefficients in `CO₂(g) + 2 H₂O(g)`. -/
def methaneCombustionProducts : GasSpecies → ℕ
  | .methane => 0
  | .oxygen => 0
  | .carbonDioxide => 1
  | .waterVapor => 2

/-- Explicit atom-conservation predicate for a reaction over the local species. -/
def IsAtomBalanced
    (reactants products : GasSpecies → ℕ) : Prop :=
  ∀ element : Element,
    (∑ species : GasSpecies,
        reactants species * atomCount species element) =
      ∑ species : GasSpecies,
        products species * atomCount species element

/-- Named balance carrier for complete methane combustion. -/
def MethaneCombustionAtomBalance : Prop :=
  IsAtomBalanced methaneCombustionReactants methaneCombustionProducts

/-- Named phase carrier for the four reaction species. -/
def MethaneCombustionAllGaseous : Prop :=
  ∀ species : GasSpecies, speciesPhase species = .gas

theorem methaneCombustion_atom_balanced :
    MethaneCombustionAtomBalance := by
  classical
  unfold MethaneCombustionAtomBalance IsAtomBalanced
  intro element
  rw [show (Finset.univ : Finset GasSpecies) =
      {.methane, .oxygen, .carbonDioxide, .waterVapor} by
    ext species
    fin_cases species <;> simp]
  fin_cases element <;> decide

theorem methaneCombustion_all_gaseous :
    MethaneCombustionAllGaseous := by
  intro species
  rfl

/-- Expand a sum over the four source species into its four contributions. -/
private theorem sum_gasSpecies {M : Type*} [AddCommMonoid M]
    (f : GasSpecies → M) :
    (∑ species : GasSpecies, f species) =
      f .methane + (f .oxygen + (f .carbonDioxide + f .waterVapor)) := by
  classical
  rw [show (Finset.univ : Finset GasSpecies) =
      {.methane, .oxygen, .carbonDioxide, .waterVapor} by
    ext species
    fin_cases species <;> simp]
  simp

/-! ## Printed thermodynamic data and the inline T4-A7 derivation -/

/-- Standard formation enthalpies at 298 K, in kJ mol⁻¹.

The methane, water-vapor, and carbon-dioxide values are printed in T4-A6.
The oxygen value is zero by the standard-state formation-enthalpy convention.
-/
def formationEnthalpy298KJPerMol : GasSpecies → ℝ
  | .methane => -74.8
  | .oxygen => 0
  | .carbonDioxide => -393.5
  | .waterVapor => -241.8

/-- Constant-pressure heat capacities printed in T4-A6, in J mol⁻¹ K⁻¹. -/
def heatCapacityJPerMolK : GasSpecies → ℝ
  | .methane => 35
  | .oxygen => 29
  | .carbonDioxide => 37
  | .waterVapor => 34

/-- Products-minus-reactants reaction sum for a molar scalar property. -/
def reactionPropertyChange (property : GasSpecies → ℝ) : ℝ :=
  (∑ species : GasSpecies,
      (methaneCombustionProducts species : ℝ) * property species) -
    ∑ species : GasSpecies,
      (methaneCombustionReactants species : ℝ) * property species

/-- Methane-combustion enthalpy at 298 K, in kJ mol⁻¹, by Hess's law. -/
def methaneCombustionEnthalpy298KJPerMol : ℝ :=
  reactionPropertyChange formationEnthalpy298KJPerMol

/-- Reaction heat-capacity change, in J mol⁻¹ K⁻¹. -/
def methaneCombustionDeltaCpJPerMolK : ℝ :=
  reactionPropertyChange heatCapacityJPerMolK

/-- Source temperatures, in K. -/
def referenceTemperatureK : ℝ := 298

def combustionTemperatureK : ℝ := 2000

/-- Kirchhoff constant-`Cₚ` relation, including the J-to-kJ conversion. -/
def KirchhoffConstantCpSpec : Prop :=
  methaneCombustionEnthalpy298KJPerMol =
      reactionPropertyChange formationEnthalpy298KJPerMol ∧
    methaneCombustionDeltaCpJPerMolK =
      reactionPropertyChange heatCapacityJPerMolK

/-- Inline T4-A7 carrier: reaction enthalpy at 2000 K, in kJ mol⁻¹. -/
def methaneCombustionEnthalpy2000KJPerMol : ℝ :=
  methaneCombustionEnthalpy298KJPerMol +
    methaneCombustionDeltaCpJPerMolK *
      (combustionTemperatureK - referenceTemperatureK) / 1000

/-- The source-side Kirchhoff equation determining the T4-A7 value. -/
def MethaneCombustionEnthalpy2000Spec : Prop :=
  methaneCombustionEnthalpy2000KJPerMol =
    methaneCombustionEnthalpy298KJPerMol +
      methaneCombustionDeltaCpJPerMolK *
        (combustionTemperatureK - referenceTemperatureK) / 1000

theorem methaneCombustionEnthalpy298_exact :
    methaneCombustionEnthalpy298KJPerMol = -(8023 : ℝ) / 10 := by
  unfold methaneCombustionEnthalpy298KJPerMol reactionPropertyChange
  simp only [sum_gasSpecies]
  norm_num [formationEnthalpy298KJPerMol,
    methaneCombustionProducts, methaneCombustionReactants]

theorem methaneCombustionDeltaCp_exact :
    methaneCombustionDeltaCpJPerMolK = 12 := by
  unfold methaneCombustionDeltaCpJPerMolK reactionPropertyChange
  simp only [sum_gasSpecies]
  norm_num [heatCapacityJPerMolK, methaneCombustionProducts,
    methaneCombustionReactants]

theorem methaneCombustionEnthalpy2000_exact :
    methaneCombustionEnthalpy2000KJPerMol = -(195469 : ℝ) / 250 := by
  unfold methaneCombustionEnthalpy2000KJPerMol
  rw [methaneCombustionEnthalpy298_exact,
    methaneCombustionDeltaCp_exact]
  norm_num [combustionTemperatureK, referenceTemperatureK]

/-! ## Corrected daily flow, ideal gas conversion, and energy release -/

/-- Well pressure converted from the printed `101.325 kPa` to Pa. -/
def wellPressurePa : ℝ := 101.325 * 1000

/-- Controller-curated corrected flow, in m³ day⁻¹. -/
def methaneVolumeFlowM3PerDay : ℝ := 2.2 * 10 ^ 5

/-- Temperature of the methane before ignition, in K. -/
def methaneFlowTemperatureK : ℝ := 298

/-- Printed molar gas constant, in J K⁻¹ mol⁻¹. -/
def molarGasConstantJPerMolK : ℝ := 8.314

/-- Daily methane amount from the printed ideal-gas law, in mol day⁻¹. -/
def methaneAmountFlowMolPerDay : ℝ :=
  wellPressurePa * methaneVolumeFlowM3PerDay /
    (molarGasConstantJPerMolK * methaneFlowTemperatureK)

/-- Nondegenerate ideal-gas flow relation with its required positivity domain. -/
def IdealGasMethaneFlowSpec : Prop :=
  0 < wellPressurePa ∧
    0 < methaneVolumeFlowM3PerDay ∧
    0 < methaneFlowTemperatureK ∧
    0 < molarGasConstantJPerMolK ∧
    0 < methaneAmountFlowMolPerDay ∧
    wellPressurePa * methaneVolumeFlowM3PerDay =
      methaneAmountFlowMolPerDay * molarGasConstantJPerMolK *
        methaneFlowTemperatureK

/-- Exact conversion factor from kJ to J. -/
def joulesPerKilojoule : ℝ := 1000

/-- Unrounded requested output, in J day⁻¹.

The leading minus sign converts the negative exothermic reaction enthalpy into
the positive magnitude described by “energy released”.
-/
def dailyEnergyRaw : ℝ :=
  methaneAmountFlowMolPerDay *
    (-methaneCombustionEnthalpy2000KJPerMol) * joulesPerKilojoule

/-- Full source-to-output derivation contract for complete isothermic burning. -/
def DailyEnergyDerivationSpec : Prop :=
  MethaneCombustionAtomBalance ∧
    MethaneCombustionAllGaseous ∧
    KirchhoffConstantCpSpec ∧
    MethaneCombustionEnthalpy2000Spec ∧
    combustionTemperatureK = 2000 ∧
    methaneCombustionEnthalpy2000KJPerMol < 0 ∧
    IdealGasMethaneFlowSpec ∧
    dailyEnergyRaw =
      methaneAmountFlowMolPerDay *
        (-methaneCombustionEnthalpy2000KJPerMol) * joulesPerKilojoule

theorem methaneAmountFlow_exact :
    methaneAmountFlowMolPerDay = (5572875000000 : ℝ) / 619393 := by
  norm_num [methaneAmountFlowMolPerDay, wellPressurePa,
    methaneVolumeFlowM3PerDay, molarGasConstantJPerMolK,
    methaneFlowTemperatureK]

theorem dailyEnergy_exact :
    dailyEnergyRaw = (4357297213500000000 : ℝ) / 619393 := by
  unfold dailyEnergyRaw
  rw [methaneAmountFlow_exact, methaneCombustionEnthalpy2000_exact]
  norm_num [joulesPerKilojoule]

/-- Raw answer-blind result contract: derivation plus a one-joule exact enclosure. -/
theorem dailyEnergy_raw_result :
    DailyEnergyDerivationSpec ∧
      ((7034786013887 : ℝ) ≤ dailyEnergyRaw ∧
        dailyEnergyRaw ≤ (7034786013888 : ℝ)) := by
  constructor
  · unfold DailyEnergyDerivationSpec
    refine ⟨methaneCombustion_atom_balanced,
      methaneCombustion_all_gaseous, ?_, ?_, rfl, ?_, ?_, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rfl
    · rw [methaneCombustionEnthalpy2000_exact]
      norm_num
    · norm_num [IdealGasMethaneFlowSpec, wellPressurePa,
        methaneVolumeFlowM3PerDay, methaneFlowTemperatureK,
        molarGasConstantJPerMolK, methaneAmountFlowMolPerDay]
  · rw [dailyEnergy_exact]
    constructor <;> norm_num

/-- The problem-specific final reporting proposition. -/
def DailyEnergyReportedSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
    dailyEnergyRaw (7030000000000 : ℝ) (10000000000 : ℝ)

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"daily_energy","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"7030000000000","reporting_quantum":"10000000000","raw_declaration":"IChO2026Problems.ProblemIcho2026T4A8.dailyEnergyRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T4A8.dailyEnergy_reported_result"}
theorem dailyEnergy_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      dailyEnergyRaw (7030000000000 : ℝ) (10000000000 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(703 : ℤ), by norm_num⟩, ?_⟩
  rw [if_pos]
  · rw [dailyEnergy_exact]
    constructor <;> norm_num
  · rw [dailyEnergy_exact]
    norm_num

end
end ProblemIcho2026T4A8
end IChO2026Problems
