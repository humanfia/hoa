import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 4, part 7

This file formalizes the constant-heat-capacity temperature correction for one
mole of the gaseous methane-combustion reaction

`CH₄(g) + 2 O₂(g) ⟶ CO₂(g) + 2 H₂O(g)`.

The part-4.6 value at 298 K is rederived below from the thermodynamic table in
the problem.  In particular, no result from another generated problem file and
neither of the printed fallback values is used.

All enthalpy values are in `kJ mol⁻¹` per mole of reaction, all heat capacities
are in `J mol⁻¹ K⁻¹`, and temperatures are in kelvin.
-/

namespace IChO2026Problems
namespace Icho2026T4A7

noncomputable section

/-- The phases relevant to the statement. -/
inductive Phase where
  | gas
deriving DecidableEq, Repr

/-- The finite species domain of complete methane combustion, read from the
reaction named in the problem and its thermodynamic table. -/
inductive Species where
  | methane
  | oxygen
  | carbonDioxide
  | water
deriving DecidableEq, Fintype, Repr

/-- Every species is gaseous, as explicitly stipulated in parts 4.6 and 4.7. -/
def speciesPhase (_ : Species) : Phase := .gas

theorem speciesPhase_eq_gas (s : Species) : speciesPhase s = .gas := by
  rfl

/-- Elements needed for the atom ledger of the combustion reaction. -/
inductive Element where
  | carbon
  | hydrogen
  | oxygen
deriving DecidableEq, Fintype, Repr

/-- Number of atoms of an element in one molecule of a species. -/
def atomCount : Species → Element → ℕ
  | .methane, .carbon => 1
  | .methane, .hydrogen => 4
  | .methane, .oxygen => 0
  | .oxygen, .carbon => 0
  | .oxygen, .hydrogen => 0
  | .oxygen, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .hydrogen => 0
  | .carbonDioxide, .oxygen => 2
  | .water, .carbon => 0
  | .water, .hydrogen => 2
  | .water, .oxygen => 1

/-- Signed stoichiometric coefficients: negative for reactants and positive
for products. -/
def methaneCombustionCoefficient : Species → ℤ
  | .methane => -1
  | .oxygen => -2
  | .carbonDioxide => 1
  | .water => 2

/-- Outcome-decisive atom ledger for the quantitative combustion stage. -/
def combustionAtomLedger (e : Element) : ℤ :=
  ∑ s : Species, methaneCombustionCoefficient s * (atomCount s e : ℤ)

theorem methaneCombustion_atom_balanced (e : Element) :
    combustionAtomLedger e = 0 := by
  cases e <;>
    native_decide

/-- All four molecular species are neutral. -/
def formalCharge (_ : Species) : ℤ := 0

/-- Charge ledger for the combustion reaction. -/
def combustionChargeLedger : ℤ :=
  ∑ s : Species, methaneCombustionCoefficient s * formalCharge s

theorem methaneCombustion_charge_balanced : combustionChargeLedger = 0 := by
  native_decide

/-- Explicit source-level specification of the normalized, all-gaseous,
balanced reaction basis used for the thermochemical sums. -/
def MethaneCombustionSourceSpecification : Prop :=
  methaneCombustionCoefficient .methane = -1 ∧
  methaneCombustionCoefficient .oxygen = -2 ∧
  methaneCombustionCoefficient .carbonDioxide = 1 ∧
  methaneCombustionCoefficient .water = 2 ∧
  (∀ s : Species, speciesPhase s = .gas) ∧
  (∀ e : Element, combustionAtomLedger e = 0) ∧
  combustionChargeLedger = 0

/-- A pair of source quantities for a gaseous species. -/
structure GasThermochemicalDatum where
  formationEnthalpy298_kJPerMol : ℝ
  constantPressureHeatCapacity_JPerMolK : ℝ

/-- The standard enthalpy of formation of elemental `O₂(g)` is zero by the
standard-state convention. -/
def oxygenFormationEnthalpy298_kJPerMol : ℝ := 0

/-- Thermodynamic data printed in part 4.6, together with the standard-state
zero for `O₂(g)`.  The printed decimals are represented as exact rationals. -/
def gasThermochemicalDatum : Species → GasThermochemicalDatum
  | .methane => ⟨(-748 : ℝ) / 10, 35⟩
  | .oxygen => ⟨oxygenFormationEnthalpy298_kJPerMol, 29⟩
  | .carbonDioxide => ⟨(-3935 : ℝ) / 10, 37⟩
  | .water => ⟨(-2418 : ℝ) / 10, 34⟩

/-- Stoichiometric sum of a molar property over the methane-combustion
reaction. -/
def reactionPropertyChange (property : Species → ℝ) : ℝ :=
  ∑ s : Species, (methaneCombustionCoefficient s : ℝ) * property s

/-- Part 4.6 rederived from formation enthalpies rather than imported as a
previous-part answer. -/
def combustionEnthalpy298_kJPerMol : ℝ :=
  reactionPropertyChange fun s =>
    (gasThermochemicalDatum s).formationEnthalpy298_kJPerMol

/-- Constant-pressure heat-capacity change of one mole of reaction. -/
def combustionConstantPressureHeatCapacityChange_JPerMolK : ℝ :=
  reactionPropertyChange fun s =>
    (gasThermochemicalDatum s).constantPressureHeatCapacity_JPerMolK

def referenceTemperature_K : ℝ := 298

def targetTemperature_K : ℝ := 2000

def joulesPerKilojoule : ℝ := 1000

/-- Physical side conditions for the two temperatures and the J/kJ scale. -/
def ThermodynamicScaleSpecification : Prop :=
  0 < referenceTemperature_K ∧
    referenceTemperature_K < targetTemperature_K ∧
    0 < joulesPerKilojoule

/-- Positivity and ordering side conditions for the thermodynamic scale and
the unit conversion used below. -/
theorem thermodynamicScale_conditions :
    ThermodynamicScaleSpecification := by
  norm_num [ThermodynamicScaleSpecification, referenceTemperature_K,
    targetTemperature_K, joulesPerKilojoule]

/-- Kirchhoff constant-heat-capacity correction from 298 K to 2000 K. -/
def combustionTemperatureCorrection_kJPerMol : ℝ :=
  combustionConstantPressureHeatCapacityChange_JPerMolK *
    (targetTemperature_K - referenceTemperature_K) / joulesPerKilojoule

/-- Exact, unrounded output carrier for part 4.7. -/
def combustionEnthalpy2000_kJPerMol : ℝ :=
  combustionEnthalpy298_kJPerMol + combustionTemperatureCorrection_kJPerMol

/-- Source-to-Lean derivation specification.  It binds the reaction and scale
specifications before recording the inline part-4.6 Hess-law calculation, the
reaction heat-capacity change, the Kirchhoff correction, and the resulting
exact raw value. -/
def CombustionEnthalpy2000Derivation : Prop :=
  MethaneCombustionSourceSpecification ∧
  ThermodynamicScaleSpecification ∧
  combustionEnthalpy298_kJPerMol = (-8023 : ℝ) / 10 ∧
  combustionConstantPressureHeatCapacityChange_JPerMolK = 12 ∧
  combustionTemperatureCorrection_kJPerMol = (2553 : ℝ) / 125 ∧
  combustionEnthalpy2000_kJPerMol = (-195469 : ℝ) / 250

/-- Raw-result contract, including a nondegenerate interval strictly inside
the one-unit reporting cell around `-782`. -/
theorem combustionEnthalpy2000_raw :
    CombustionEnthalpy2000Derivation ∧
      (-1565 : ℝ) / 2 < combustionEnthalpy2000_kJPerMol ∧
      combustionEnthalpy2000_kJPerMol < (-1563 : ℝ) / 2 := by
  have hSpeciesUniv :
      (Finset.univ : Finset Species) =
        {.methane, .oxygen, .carbonDioxide, .water} := by
    native_decide
  have hSource : MethaneCombustionSourceSpecification := by
    exact ⟨rfl, rfl, rfl, rfl, speciesPhase_eq_gas,
      methaneCombustion_atom_balanced, methaneCombustion_charge_balanced⟩
  have hEnthalpy298 :
      combustionEnthalpy298_kJPerMol = (-8023 : ℝ) / 10 := by
    rw [combustionEnthalpy298_kJPerMol, reactionPropertyChange,
      hSpeciesUniv]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_singleton]
    norm_num [gasThermochemicalDatum, methaneCombustionCoefficient,
      oxygenFormationEnthalpy298_kJPerMol]
  have hHeatCapacityChange :
      combustionConstantPressureHeatCapacityChange_JPerMolK = 12 := by
    rw [combustionConstantPressureHeatCapacityChange_JPerMolK,
      reactionPropertyChange, hSpeciesUniv]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_insert (by native_decide)]
    rw [Finset.sum_singleton]
    norm_num [gasThermochemicalDatum, methaneCombustionCoefficient]
  have hCorrection :
      combustionTemperatureCorrection_kJPerMol = (2553 : ℝ) / 125 := by
    rw [combustionTemperatureCorrection_kJPerMol, hHeatCapacityChange]
    norm_num [targetTemperature_K, referenceTemperature_K,
      joulesPerKilojoule]
  have hEnthalpy2000 :
      combustionEnthalpy2000_kJPerMol = (-195469 : ℝ) / 250 := by
    rw [combustionEnthalpy2000_kJPerMol, hEnthalpy298, hCorrection]
    norm_num
  refine ⟨⟨hSource, thermodynamicScale_conditions, hEnthalpy298,
    hHeatCapacityChange, hCorrection, hEnthalpy2000⟩, ?_, ?_⟩
  · rw [hEnthalpy2000]
    norm_num
  · rw [hEnthalpy2000]
    norm_num

/-- Three significant figures at this magnitude prescribe a
`1 kJ mol⁻¹` reporting quantum. -/
def combustionEnthalpy2000ReportingQuantum_kJPerMol : ℝ := 1

/-- The mechanically reported three-significant-figure value. -/
def reportedCombustionEnthalpy2000_kJPerMol : ℝ := -782

/-- Final numerical-reporting contract: nearest multiple of the fixed quantum,
with exact ties rounded away from zero. -/
theorem combustionEnthalpy2000_reportsAtThreeSignificantFigures :
    IChO2026Chem.Reporting.ReportsAtQuantum
      combustionEnthalpy2000_kJPerMol (-782 : ℝ) 1 := by
  have hraw : combustionEnthalpy2000_kJPerMol = (-195469 : ℝ) / 250 :=
    combustionEnthalpy2000_raw.1.2.2.2.2.2
  rw [hraw]
  refine ⟨by norm_num, ⟨-782, by norm_num⟩, ?_⟩
  norm_num [IChO2026Chem.Reporting.ReportsAtQuantum]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"combustion_enthalpy_2000","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-782","reporting_quantum":"1","raw_declaration":"IChO2026Problems.Icho2026T4A7.combustionEnthalpy2000_kJPerMol","reporting_declaration":"IChO2026Problems.Icho2026T4A7.combustionEnthalpy2000_reportsAtThreeSignificantFigures"}

end
end Icho2026T4A7
end IChO2026Problems
