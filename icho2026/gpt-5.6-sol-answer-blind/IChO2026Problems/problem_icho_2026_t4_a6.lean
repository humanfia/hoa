import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T4.6

This file formalizes the standard enthalpy of combustion at 298 K for one mole
of methane when every species is gaseous.  Numerical enthalpies are represented
by their values in `kJ mol⁻¹`; heat capacities are represented by their values
in `J mol⁻¹ K⁻¹`.
-/

namespace IChO2026Problems.ProblemIcho2026T4A6

noncomputable section

/-- The chemical species occurring in the methane-combustion calculation. -/
inductive ChemicalSpecies where
  | methane
  | dioxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Repr

/-- The source explicitly stipulates that every reaction species is gaseous. -/
inductive Phase where
  | gas
  deriving DecidableEq, Repr

/-- The elements whose conservation decides the combustion stoichiometry. -/
structure MolecularComposition where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace MolecularComposition

def zero : MolecularComposition :=
  ⟨0, 0, 0⟩

def add (a b : MolecularComposition) : MolecularComposition :=
  ⟨a.carbon + b.carbon, a.hydrogen + b.hydrogen, a.oxygen + b.oxygen⟩

def scale (n : ℕ) (a : MolecularComposition) : MolecularComposition :=
  ⟨n * a.carbon, n * a.hydrogen, n * a.oxygen⟩

end MolecularComposition

/-- Molecular formula data for the four source-bounded species. -/
def molecularComposition : ChemicalSpecies → MolecularComposition
  | .methane => ⟨1, 4, 0⟩
  | .dioxygen => ⟨0, 0, 2⟩
  | .carbonDioxide => ⟨1, 0, 2⟩
  | .water => ⟨0, 2, 1⟩

/-- A species together with its whole-number stoichiometric coefficient and phase. -/
structure StoichiometricTerm where
  species : ChemicalSpecies
  coefficient : ℕ
  phase : Phase
  deriving DecidableEq, Repr

/-- A directed chemical reaction, retaining both species identities and phases. -/
structure ChemicalReaction where
  reactants : List StoichiometricTerm
  products : List StoichiometricTerm
  deriving DecidableEq, Repr

/-- `CH₄(g) + 2 O₂(g) ⟶ CO₂(g) + 2 H₂O(g)`, on a one-mole methane basis. -/
def methaneCombustionReaction : ChemicalReaction :=
  { reactants :=
      [ { species := .methane, coefficient := 1, phase := .gas },
        { species := .dioxygen, coefficient := 2, phase := .gas } ]
    products :=
      [ { species := .carbonDioxide, coefficient := 1, phase := .gas },
        { species := .water, coefficient := 2, phase := .gas } ] }

/-- Total C/H/O composition of one stoichiometric side. -/
def sideComposition (side : List StoichiometricTerm) : MolecularComposition :=
  side.foldl
    (fun total term =>
      total.add (MolecularComposition.scale term.coefficient
        (molecularComposition term.species)))
    MolecularComposition.zero

/-- Named atom-conservation carrier for the source-bounded combustion equation. -/
def methaneCombustionAtomBalance : Prop :=
  sideComposition methaneCombustionReaction.reactants =
    sideComposition methaneCombustionReaction.products

/-- Named carrier for the source stipulation that every species is gaseous. -/
def methaneCombustionAllGaseous : Prop :=
  ∀ term ∈
      methaneCombustionReaction.reactants ++ methaneCombustionReaction.products,
    term.phase = .gas

/-- The temperature specified by the question, in kelvin. -/
def standardTemperatureKelvin : ℝ := 298

/-- Units used by the printed thermodynamic table. -/
inductive ThermodynamicUnit where
  | kilojoulePerMole
  | joulePerMoleKelvin
  deriving DecidableEq, Repr

/-- A scalar thermodynamic datum together with its unit. -/
structure ThermodynamicDatum where
  value : ℝ
  unit : ThermodynamicUnit

/-- Every numerical datum printed under T4.6.

The three formation enthalpies have unit `kJ mol⁻¹`; the four constant-pressure
molar heat capacities have unit `J mol⁻¹ K⁻¹`.
-/
structure PrintedThermodynamicTable where
  methaneFormationEnthalpy298 : ThermodynamicDatum
  waterGasFormationEnthalpy298 : ThermodynamicDatum
  carbonDioxideFormationEnthalpy298 : ThermodynamicDatum
  methaneHeatCapacity : ThermodynamicDatum
  waterGasHeatCapacity : ThermodynamicDatum
  dioxygenHeatCapacity : ThermodynamicDatum
  carbonDioxideHeatCapacity : ThermodynamicDatum

/-- The source table, represented exactly as printed. -/
def printedThermodynamicTable : PrintedThermodynamicTable :=
  { methaneFormationEnthalpy298 := ⟨-(748 / 10 : ℝ), .kilojoulePerMole⟩
    waterGasFormationEnthalpy298 := ⟨-(2418 / 10 : ℝ), .kilojoulePerMole⟩
    carbonDioxideFormationEnthalpy298 := ⟨-(3935 / 10 : ℝ), .kilojoulePerMole⟩
    methaneHeatCapacity := ⟨35, .joulePerMoleKelvin⟩
    waterGasHeatCapacity := ⟨34, .joulePerMoleKelvin⟩
    dioxygenHeatCapacity := ⟨29, .joulePerMoleKelvin⟩
    carbonDioxideHeatCapacity := ⟨37, .joulePerMoleKelvin⟩ }

/-- Standard formation enthalpies at 298 K, in `kJ mol⁻¹`.

The dioxygen value is zero because gaseous O₂ is oxygen's standard elemental
state.  The other three values are taken from the printed table.
-/
def standardFormationEnthalpy298 : ChemicalSpecies → ℝ
  | .methane => printedThermodynamicTable.methaneFormationEnthalpy298.value
  | .dioxygen => 0
  | .carbonDioxide =>
      printedThermodynamicTable.carbonDioxideFormationEnthalpy298.value
  | .water => printedThermodynamicTable.waterGasFormationEnthalpy298.value

/-- Sum of coefficient-weighted standard formation enthalpies on one side. -/
def sideFormationEnthalpy
    (formationEnthalpy : ChemicalSpecies → ℝ)
    (side : List StoichiometricTerm) : ℝ :=
  (side.map fun term =>
    (term.coefficient : ℝ) * formationEnthalpy term.species).sum

/-- Hess's-law products-minus-reactants construction for a reaction. -/
def reactionEnthalpyFromFormationData
    (formationEnthalpy : ChemicalSpecies → ℝ)
    (reaction : ChemicalReaction) : ℝ :=
  sideFormationEnthalpy formationEnthalpy reaction.products -
    sideFormationEnthalpy formationEnthalpy reaction.reactants

/-- Exact, unrounded source-derived reaction enthalpy in `kJ mol⁻¹`. -/
def combustionEnthalpy298Raw : ℝ :=
  reactionEnthalpyFromFormationData
    standardFormationEnthalpy298 methaneCombustionReaction

/-- The complete problem-specific derivation specification.

It retains the 298 K condition, gaseous phases, atom balance, one-mole methane
stoichiometry, and the coefficient-weighted Hess-law expression.  Heat
capacities are not used because both the tabulated formation enthalpies and the
requested reaction enthalpy are at 298 K.
-/
def combustionEnthalpy298DerivationSpec : Prop :=
  standardTemperatureKelvin = 298 ∧
  methaneCombustionAllGaseous ∧
  methaneCombustionAtomBalance ∧
  methaneCombustionReaction.reactants =
      [ { species := .methane, coefficient := 1, phase := .gas },
        { species := .dioxygen, coefficient := 2, phase := .gas } ] ∧
  methaneCombustionReaction.products =
      [ { species := .carbonDioxide, coefficient := 1, phase := .gas },
        { species := .water, coefficient := 2, phase := .gas } ] ∧
  combustionEnthalpy298Raw =
    (printedThermodynamicTable.carbonDioxideFormationEnthalpy298.value +
      2 * printedThermodynamicTable.waterGasFormationEnthalpy298.value) -
    (printedThermodynamicTable.methaneFormationEnthalpy298.value + 2 * 0)

/-- Raw result contract: the exact derivation and its fixed reporting-cell enclosure. -/
theorem combustionEnthalpy298_raw :
    combustionEnthalpy298DerivationSpec ∧
      ((-1605 : ℝ) / 2 ≤ combustionEnthalpy298Raw ∧
        combustionEnthalpy298Raw ≤ (-1603 : ℝ) / 2) := by
  norm_num [combustionEnthalpy298DerivationSpec,
    standardTemperatureKelvin, methaneCombustionAllGaseous,
    methaneCombustionAtomBalance, sideComposition, methaneCombustionReaction,
    MolecularComposition.add, MolecularComposition.scale,
    MolecularComposition.zero, molecularComposition,
    combustionEnthalpy298Raw, reactionEnthalpyFromFormationData,
    sideFormationEnthalpy, standardFormationEnthalpy298,
    printedThermodynamicTable]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"combustion_enthalpy_298","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-802","reporting_quantum":"1","raw_declaration":"IChO2026Problems.ProblemIcho2026T4A6.combustionEnthalpy298Raw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T4A6.combustionEnthalpy298_reported"}
theorem combustionEnthalpy298_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      combustionEnthalpy298Raw (-802 : ℝ) (1 : ℝ) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  norm_num [combustionEnthalpy298Raw, reactionEnthalpyFromFormationData,
    sideFormationEnthalpy, standardFormationEnthalpy298,
    methaneCombustionReaction, printedThermodynamicTable]
  exact ⟨-802, by norm_num⟩

end

end IChO2026Problems.ProblemIcho2026T4A6
