import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A6: gaseous methane combustion at 298 K

The problem asks for one numerical molar reaction enthalpy.  The exact raw
carrier below is a products-minus-reactants formation-enthalpy calculation;
rounding occurs only in the final `ReportsAtQuantum` theorem.
-/

open scoped BigOperators

namespace IChO2026Problems.T4A6

noncomputable section

/-- Elements needed to audit the methane-combustion atom balance. -/
inductive Atom where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

/-- The four chemical species in the gas-phase combustion equation and in the
thermodynamic table on the problem page. -/
inductive Species where
  | methane
  | oxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Fintype

/-- The phase stipulated for every species in this subquestion. -/
inductive Phase where
  | gas
  | liquid
  | solid
  | aqueous
  deriving DecidableEq

/-- All four named species are gaseous in the source's 298 K model. -/
def speciesPhase (_ : Species) : Phase := .gas

/-- Molecular formula data for `CH₄`, `O₂`, `CO₂`, and `H₂O`. -/
def molecularAtomCount : Species → Atom → ℕ
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

/-- Atom-balance equations for a combustion equation whose methane coefficient
is one.  The variables are respectively the coefficients of `O₂`, `CO₂`, and
`H₂O`. -/
def IsBalancedOneMoleMethaneCombustion
    (oxygenCoeff carbonDioxideCoeff waterCoeff : ℕ) : Prop :=
  carbonDioxideCoeff = 1 ∧
  2 * waterCoeff = 4 ∧
  2 * oxygenCoeff = 2 * carbonDioxideCoeff + waterCoeff

/-- The integer stoichiometric coefficients are fixed by the three element
balances once the methane coefficient is one. -/
theorem balancedOneMoleMethaneCombustion_unique
    {oxygenCoeff carbonDioxideCoeff waterCoeff : ℕ}
    (h : IsBalancedOneMoleMethaneCombustion
      oxygenCoeff carbonDioxideCoeff waterCoeff) :
    oxygenCoeff = 2 ∧ carbonDioxideCoeff = 1 ∧ waterCoeff = 2 := by
  unfold IsBalancedOneMoleMethaneCombustion at h
  omega

/-- The source-bounded complete gas-phase combustion reaction
`CH₄ + 2 O₂ ⟶ CO₂ + 2 H₂O`. -/
def methaneCombustionReaction : CRNT.Reaction Species where
  source := fun
    | .methane => 1
    | .oxygen => 2
    | .carbonDioxide => 0
    | .water => 0
  target := fun
    | .methane => 0
    | .oxygen => 0
    | .carbonDioxide => 1
    | .water => 2

/-- An explicit coefficient-level carrier for the combustion reaction. -/
def MethaneCombustionStoichiometry : Prop :=
  methaneCombustionReaction.source .methane = 1 ∧
  methaneCombustionReaction.source .oxygen = 2 ∧
  methaneCombustionReaction.source .carbonDioxide = 0 ∧
  methaneCombustionReaction.source .water = 0 ∧
  methaneCombustionReaction.target .methane = 0 ∧
  methaneCombustionReaction.target .oxygen = 0 ∧
  methaneCombustionReaction.target .carbonDioxide = 1 ∧
  methaneCombustionReaction.target .water = 2

theorem methaneCombustion_stoichiometry :
    MethaneCombustionStoichiometry := by
  norm_num [MethaneCombustionStoichiometry, methaneCombustionReaction]

/-- Count an element in a CRNT complex, with stoichiometric multiplicity. -/
def atomInventory (complex : CRNT.Complex Species) (atom : Atom) : ℕ :=
  ∑ species, complex species * molecularAtomCount species atom

/-- Nontrivial atom-conservation carrier for the chosen combustion equation. -/
theorem methaneCombustion_atomBalanced (atom : Atom) :
    atomInventory methaneCombustionReaction.source atom =
      atomInventory methaneCombustionReaction.target atom := by
  cases atom <;> decide

/-- The requested thermodynamic reference temperature, in kelvin. -/
def referenceTemperatureKelvin : ℝ := 298

/-- Formation-enthalpy entries printed in the problem, in `kJ mol⁻¹`.
`O₂(g)` is absent from that part of the printed table. -/
def printedFormationEnthalpy298 : Species → Option ℝ
  | .methane => some ((-748 : ℝ) / 10)
  | .oxygen => none
  | .carbonDioxide => some ((-3935 : ℝ) / 10)
  | .water => some ((-2418 : ℝ) / 10)

/-- Standard formation enthalpy at 298 K, in `kJ mol⁻¹`.  The oxygen value is
zero by the standard-state reference convention; the other three values are
the exact decimals printed in the source table. -/
def standardFormationEnthalpy298 : Species → ℝ
  | .methane => (-748 : ℝ) / 10
  | .oxygen => 0
  | .carbonDioxide => (-3935 : ℝ) / 10
  | .water => (-2418 : ℝ) / 10

/-- Constant-pressure molar heat capacities printed in the same table, in
`J mol⁻¹ K⁻¹`.  They are retained as supplied data, although no temperature
correction is needed because this part asks directly for the 298 K value. -/
def printedMolarHeatCapacity : Species → ℝ
  | .methane => 35
  | .oxygen => 29
  | .carbonDioxide => 37
  | .water => 34

/-- Exact carrier for every thermodynamic-table row printed for T4-A6.  The
`none` entry records that the page does not print a formation enthalpy for
`O₂(g)`; its standard-state value is kept as a separate convention below. -/
def PrintedThermodynamicTable298 : Prop :=
  printedFormationEnthalpy298 .methane = some ((-748 : ℝ) / 10) ∧
  printedFormationEnthalpy298 .oxygen = none ∧
  printedFormationEnthalpy298 .carbonDioxide = some ((-3935 : ℝ) / 10) ∧
  printedFormationEnthalpy298 .water = some ((-2418 : ℝ) / 10) ∧
  printedMolarHeatCapacity .methane = 35 ∧
  printedMolarHeatCapacity .oxygen = 29 ∧
  printedMolarHeatCapacity .carbonDioxide = 37 ∧
  printedMolarHeatCapacity .water = 34

theorem printedThermodynamicTable298_fromSource :
    PrintedThermodynamicTable298 := by
  norm_num [PrintedThermodynamicTable298, printedFormationEnthalpy298,
    printedMolarHeatCapacity]

/-- Every formation enthalpy actually printed on the page is the corresponding
entry used in the Hess-law calculation. -/
def FormationEnthalpyDataCoherent : Prop :=
  ∀ species value, printedFormationEnthalpy298 species = some value →
    standardFormationEnthalpy298 species = value

theorem formationEnthalpyData_coherent : FormationEnthalpyDataCoherent := by
  intro species value h
  cases species <;>
    simp_all [printedFormationEnthalpy298, standardFormationEnthalpy298]

/-- The only unprinted formation datum used by the calculation is the ordinary
standard-state reference value for elemental `O₂(g)`. -/
def OxygenStandardStateReferenceConvention : Prop :=
  standardFormationEnthalpy298 .oxygen = 0

theorem oxygenStandardState_reference :
    OxygenStandardStateReferenceConvention := by
  rfl

/-- Sum of standard formation enthalpies for a stoichiometric complex, in
`kJ mol⁻¹` per firing of the reaction. -/
def formationEnthalpyOfComplex298 (complex : CRNT.Complex Species) : ℝ :=
  ∑ species, (complex species : ℝ) * standardFormationEnthalpy298 species

/-- Hess formation-enthalpy difference: products minus reactants. -/
def reactionEnthalpyFromFormation298 (reaction : CRNT.Reaction Species) : ℝ :=
  formationEnthalpyOfComplex298 reaction.target -
    formationEnthalpyOfComplex298 reaction.source

/-- Exact, unrounded source-derived reaction enthalpy for one mole of gaseous
methane combustion at 298 K, in `kJ mol⁻¹`. -/
def combustionEnthalpy298Raw : ℝ :=
  reactionEnthalpyFromFormation298 methaneCombustionReaction

/-- Expansion of the finite Hess sum using the independently balanced
coefficients.  This is the governing products-minus-reactants equation, before
any numerical evaluation or reporting. -/
theorem combustionEnthalpy298_hessExpansion :
    combustionEnthalpy298Raw =
      (standardFormationEnthalpy298 .carbonDioxide +
          2 * standardFormationEnthalpy298 .water) -
        (standardFormationEnthalpy298 .methane +
          2 * standardFormationEnthalpy298 .oxygen) := by
  have species_univ : (Finset.univ : Finset Species) =
      {.methane, .oxygen, .carbonDioxide, .water} := by
    decide
  unfold combustionEnthalpy298Raw reactionEnthalpyFromFormation298
    formationEnthalpyOfComplex298
  rw [species_univ]
  simp [Finset.sum_insert, methaneCombustionReaction]

/-- Problem-specific derivation specification.  It exposes the temperature,
phase condition, reaction coefficients, atom balance, all formation-enthalpy
inputs (including the standard-state oxygen zero), and Hess's products-minus-
reactants relation without inserting the final numerical result as a premise. -/
def combustionEnthalpy298DerivationSpec : Prop :=
  referenceTemperatureKelvin = 298 ∧
  (∀ species, speciesPhase species = .gas) ∧
  MethaneCombustionStoichiometry ∧
  (∀ atom,
    atomInventory methaneCombustionReaction.source atom =
      atomInventory methaneCombustionReaction.target atom) ∧
  PrintedThermodynamicTable298 ∧
  FormationEnthalpyDataCoherent ∧
  OxygenStandardStateReferenceConvention ∧
  standardFormationEnthalpy298 .methane = (-748 : ℝ) / 10 ∧
  standardFormationEnthalpy298 .oxygen = 0 ∧
  standardFormationEnthalpy298 .carbonDioxide = (-3935 : ℝ) / 10 ∧
  standardFormationEnthalpy298 .water = (-2418 : ℝ) / 10 ∧
  combustionEnthalpy298Raw =
    (standardFormationEnthalpy298 .carbonDioxide +
        2 * standardFormationEnthalpy298 .water) -
      (standardFormationEnthalpy298 .methane +
        2 * standardFormationEnthalpy298 .oxygen)

/-- Exact arithmetic consequence of the unrounded Hess-law expression. -/
theorem combustionEnthalpy298_exact :
    combustionEnthalpy298Raw = (-8023 : ℝ) / 10 := by
  rw [combustionEnthalpy298_hessExpansion]
  norm_num [standardFormationEnthalpy298]

/-- Raw answer-blind result contract, including a nondegenerate certified
interval around the exact rational raw value. -/
theorem combustionEnthalpy298_raw_result :
    combustionEnthalpy298DerivationSpec ∧
      ((-80231 : ℝ) / 100 ≤ combustionEnthalpy298Raw ∧
        combustionEnthalpy298Raw ≤ (-80229 : ℝ) / 100) := by
  constructor
  · refine ⟨rfl, ?_, methaneCombustion_stoichiometry,
      methaneCombustion_atomBalanced,
      printedThermodynamicTable298_fromSource,
      formationEnthalpyData_coherent,
      oxygenStandardState_reference,
      rfl, rfl, rfl, rfl, combustionEnthalpy298_hessExpansion⟩
    · intro species
      rfl
  · rw [combustionEnthalpy298_exact]
    norm_num

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"combustion_enthalpy_298","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-802","reporting_quantum":"1","raw_declaration":"IChO2026Problems.T4A6.combustionEnthalpy298Raw","reporting_declaration":"IChO2026Problems.T4A6.combustionEnthalpy298_reported_result"}

/-- Final reporting contract: three significant figures at this magnitude
means a `1 kJ mol⁻¹` reporting quantum, with ties away from zero as fixed by the
source report. -/
theorem combustionEnthalpy298_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      combustionEnthalpy298Raw (-802 : ℝ) (1 : ℝ) := by
  rw [combustionEnthalpy298_exact]
  refine ⟨by norm_num, ⟨(-802 : ℤ), by norm_num⟩, ?_⟩
  norm_num

end

end IChO2026Problems.T4A6
