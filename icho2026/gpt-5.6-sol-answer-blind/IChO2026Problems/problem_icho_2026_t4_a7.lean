import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 4.7

This file formalizes the constant-heat-capacity Kirchhoff correction for one
mole of gas-phase methane combustion,

`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`.

All source decimals are represented exactly.  Enthalpies are in `kJ mol⁻¹`,
heat capacities are in `J mol⁻¹ K⁻¹`, and temperatures are in kelvin.
-/

open scoped BigOperators

namespace IChO2026Problems.T4A7

noncomputable section

/-! ## Chemical entities and the balanced combustion reaction -/

/-- The complete species domain used in the methane-combustion calculation. -/
inductive CombustionSpecies
  | methane
  | oxygen
  | carbonDioxide
  | waterVapor
  deriving DecidableEq, Fintype

/-- A finite sum over the source-derived species domain is the four-term
stoichiometric ledger used below. -/
private theorem sum_combustionSpecies
    {M : Type*} [AddCommMonoid M] (f : CombustionSpecies → M) :
    ∑ s, f s =
      f .methane + f .oxygen + f .carbonDioxide + f .waterVapor := by
  have hSpecies : (Finset.univ : Finset CombustionSpecies) =
      {.methane, .oxygen, .carbonDioxide, .waterVapor} := by
    decide
  rw [hSpecies]
  rw [Finset.sum_insert (by decide :
        CombustionSpecies.methane ∉
          ({.oxygen, .carbonDioxide, .waterVapor} : Finset CombustionSpecies))]
  rw [Finset.sum_insert (by decide :
        CombustionSpecies.oxygen ∉
          ({.carbonDioxide, .waterVapor} : Finset CombustionSpecies))]
  rw [Finset.sum_insert (by decide :
        CombustionSpecies.carbonDioxide ∉
          ({.waterVapor} : Finset CombustionSpecies))]
  rw [Finset.sum_singleton]
  simp only [add_assoc]

/-- The phase information needed by this subquestion. -/
inductive Phase
  | gas
  deriving DecidableEq

/-- Every species in the stipulated reaction is gaseous. -/
def speciesPhase (_ : CombustionSpecies) : Phase := .gas

/-- Source reaction: `CH₄ + 2 O₂ → CO₂ + 2 H₂O(g)`. -/
def methaneCombustion : CRNT.Reaction CombustionSpecies where
  source := fun
    | .methane => 1
    | .oxygen => 2
    | .carbonDioxide => 0
    | .waterVapor => 0
  target := fun
    | .methane => 0
    | .oxygen => 0
    | .carbonDioxide => 1
    | .waterVapor => 2

/-- Elements whose conservation is outcome-decisive for the reaction ledger. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

/-- Number of atoms of an element in one molecule of a combustion species. -/
def atomCount : Element → CombustionSpecies → ℕ
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

/-- Atom count of an element in a stoichiometric complex. -/
def complexAtomCount (e : Element) (c : CRNT.Complex CombustionSpecies) : ℕ :=
  ∑ s, c s * atomCount e s

/-- A reaction is atom-balanced on the source-derived element domain. -/
def AtomBalanced (r : CRNT.Reaction CombustionSpecies) : Prop :=
  ∀ e, complexAtomCount e r.source = complexAtomCount e r.target

theorem methaneCombustion_coefficients :
    methaneCombustion.source .methane = 1 ∧
    methaneCombustion.source .oxygen = 2 ∧
    methaneCombustion.target .carbonDioxide = 1 ∧
    methaneCombustion.target .waterVapor = 2 := by
  norm_num [methaneCombustion]

theorem methaneCombustion_atomBalanced : AtomBalanced methaneCombustion := by
  intro e
  cases e <;>
    norm_num [complexAtomCount, sum_combustionSpecies, methaneCombustion,
      atomCount]

theorem allSpeciesGaseous : ∀ s, speciesPhase s = .gas := by
  intro s
  rfl

/-! ## Problem-supplied thermochemical data -/

/-- Formation enthalpy and constant molar heat capacity tables from part 4.6.
The oxygen formation enthalpy is zero by the standard-state convention. -/
structure ThermochemicalData where
  formationEnthalpy298 : CombustionSpecies → ℝ
  molarHeatCapacity : CombustionSpecies → ℝ

/-- Exact source data.  The two fields have units `kJ mol⁻¹` and
`J mol⁻¹ K⁻¹`, respectively. -/
def sourceData : ThermochemicalData where
  formationEnthalpy298 := fun
    | .methane => -(748 : ℝ) / 10
    | .oxygen => 0
    | .carbonDioxide => -(3935 : ℝ) / 10
    | .waterVapor => -(2418 : ℝ) / 10
  molarHeatCapacity := fun
    | .methane => 35
    | .oxygen => 29
    | .carbonDioxide => 37
    | .waterVapor => 34

/-- Product-minus-reactant change of an additive molar property. -/
def reactionPropertyChange
    (r : CRNT.Reaction CombustionSpecies)
    (property : CombustionSpecies → ℝ) : ℝ :=
  ∑ s, r.vector s * property s

/-- Blind inline derivation of part 4.6, in `kJ mol⁻¹`. -/
def reactionEnthalpy298 : ℝ :=
  reactionPropertyChange methaneCombustion sourceData.formationEnthalpy298

/-- Heat-capacity change of the reaction, in `J mol⁻¹ K⁻¹`. -/
def reactionHeatCapacityChange : ℝ :=
  reactionPropertyChange methaneCombustion sourceData.molarHeatCapacity

/-- The source temperatures, in kelvin. -/
def initialTemperature : ℝ := 298

def finalTemperature : ℝ := 2000

/-- Constant-`C_P` Kirchhoff correction, converting joules to kilojoules. -/
def kirchhoffConstantCp
    (enthalpyAtInitial deltaCp initial final : ℝ) : ℝ :=
  enthalpyAtInitial + deltaCp / 1000 * (final - initial)

/-- Exact, unrounded requested output in `kJ mol⁻¹`. -/
def combustionEnthalpy2000Raw : ℝ :=
  kirchhoffConstantCp reactionEnthalpy298 reactionHeatCapacityChange
    initialTemperature finalTemperature

/-! ## Assumption/target split and answer-blind result contracts

The assumptions are exactly the reaction, gas phases, tabulated formation
enthalpies and heat capacities, the standard-state zero for oxygen, and the
constant-heat-capacity Kirchhoff relation above.  The target is the resulting
unrounded enthalpy and its independently fixed three-significant-figure report.
-/

/-- Problem-specific derivation specification.  All numerical equalities here
are conclusions obtained from the source tables and stoichiometric ledger. -/
def CombustionEnthalpy2000DerivationSpec : Prop :=
  AtomBalanced methaneCombustion ∧
  (∀ s, speciesPhase s = .gas) ∧
  reactionEnthalpy298 = -(8023 : ℝ) / 10 ∧
  reactionHeatCapacityChange = 12 ∧
  combustionEnthalpy2000Raw =
    reactionEnthalpy298 + reactionHeatCapacityChange / 1000 *
      (finalTemperature - initialTemperature) ∧
  combustionEnthalpy2000Raw = -(195469 : ℝ) / 250

/-- Raw result contract, including a nondegenerate closed rational interval
around the exact value `-781.876 kJ mol⁻¹`. -/
theorem combustionEnthalpy2000_raw :
    (CombustionEnthalpy2000DerivationSpec) ∧
    (((-781877 : ℝ) / 1000) ≤ (combustionEnthalpy2000Raw) ∧
    (combustionEnthalpy2000Raw) ≤ ((-6255 : ℝ) / 8)) := by
  have h298 : reactionEnthalpy298 = -(8023 : ℝ) / 10 := by
    norm_num [reactionEnthalpy298, reactionPropertyChange,
      sum_combustionSpecies,
      methaneCombustion, sourceData]
  have hCp : reactionHeatCapacityChange = 12 := by
    norm_num [reactionHeatCapacityChange, reactionPropertyChange,
      sum_combustionSpecies,
      methaneCombustion, sourceData]
  have hKirchhoff :
      combustionEnthalpy2000Raw =
        reactionEnthalpy298 + reactionHeatCapacityChange / 1000 *
          (finalTemperature - initialTemperature) := by
    rfl
  have hRaw : combustionEnthalpy2000Raw = -(195469 : ℝ) / 250 := by
    rw [hKirchhoff, h298, hCp]
    norm_num [initialTemperature, finalTemperature]
  refine ⟨?_, ?_⟩
  · exact ⟨methaneCombustion_atomBalanced, allSpeciesGaseous, h298, hCp,
      hKirchhoff, hRaw⟩
  · rw [hRaw]
    norm_num

/-- The raw magnitude is in the hundreds cell, so three significant figures
correspond to a reporting quantum of `1 kJ mol⁻¹`. -/
theorem combustionEnthalpy2000_magnitudeCell :
    100 ≤ |combustionEnthalpy2000Raw| ∧
    |combustionEnthalpy2000Raw| < 1000 := by
  have hSpec := combustionEnthalpy2000_raw.1
  change
    AtomBalanced methaneCombustion ∧
      (∀ s, speciesPhase s = .gas) ∧
      reactionEnthalpy298 = -(8023 : ℝ) / 10 ∧
      reactionHeatCapacityChange = 12 ∧
      combustionEnthalpy2000Raw =
        reactionEnthalpy298 + reactionHeatCapacityChange / 1000 *
          (finalTemperature - initialTemperature) ∧
      combustionEnthalpy2000Raw = -(195469 : ℝ) / 250 at hSpec
  rcases hSpec with ⟨_, _, _, _, _, hRaw⟩
  rw [hRaw]
  norm_num [abs_of_nonpos]

set_option linter.style.longLine false in
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"combustion_enthalpy_2000","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-782","reporting_quantum":"1","raw_declaration":"IChO2026Problems.T4A7.combustionEnthalpy2000Raw","reporting_declaration":"IChO2026Problems.T4A7.combustionEnthalpy2000_reported"}
theorem combustionEnthalpy2000_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      combustionEnthalpy2000Raw (-782) 1 := by
  have hSpec := combustionEnthalpy2000_raw.1
  change
    AtomBalanced methaneCombustion ∧
      (∀ s, speciesPhase s = .gas) ∧
      reactionEnthalpy298 = -(8023 : ℝ) / 10 ∧
      reactionHeatCapacityChange = 12 ∧
      combustionEnthalpy2000Raw =
        reactionEnthalpy298 + reactionHeatCapacityChange / 1000 *
          (finalTemperature - initialTemperature) ∧
      combustionEnthalpy2000Raw = -(195469 : ℝ) / 250 at hSpec
  rcases hSpec with ⟨_, _, _, _, _, hRaw⟩
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  rw [hRaw]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨(-782 : ℤ), by norm_num⟩
  · norm_num

end

end IChO2026Problems.T4A7
