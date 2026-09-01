import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T3-A1: composition of COF-1

This file formalizes the source-image recount before recording the requested
formula and carbon mass percentage.  The quantitative condensation stage has
the closed species domain `B3`, `A2`, assembled COF-1, and water; no anonymous
material stream is used.
-/

namespace IChO2026Problems.IChO2026T3A1

open IChO2026Chem.Reporting

noncomputable section

/-- Counts of the four elements visible in the COF-1 assembly. -/
structure CHBOFormula where
  carbon : ℕ
  hydrogen : ℕ
  boron : ℕ
  oxygen : ℕ
deriving DecidableEq, Repr

/-- Componentwise sum of molecular formulae. -/
def addFormula (x y : CHBOFormula) : CHBOFormula where
  carbon := x.carbon + y.carbon
  hydrogen := x.hydrogen + y.hydrogen
  boron := x.boron + y.boron
  oxygen := x.oxygen + y.oxygen

/-- Componentwise natural-number scaling of a molecular formula. -/
def scaleFormula (n : ℕ) (x : CHBOFormula) : CHBOFormula where
  carbon := n * x.carbon
  hydrogen := n * x.hydrogen
  boron := n * x.boron
  oxygen := n * x.oxygen

/-- The finite species domain used in the outcome-decisive condensation ledger. -/
inductive COF1StageSpecies
  | b3Node
  | a2Linker
  | assembledCOF1
  | water
deriving DecidableEq, Fintype, Repr

/-- This depicted transformation is used quantitatively, because its water loss
determines the atom counts of the requested empirical formula. -/
inductive TransformationUse
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

def cof1TransformationUse : TransformationUse :=
  .quantitativeMaterialStage

/-- Source-image topology recount for one smallest 2:3 incidence assembly.
The tritopic and ditopic incidences both count the same six connections. -/
structure TopologyRecount where
  b3Nodes : ℕ
  a2Linkers : ℕ
  b3Degree : ℕ
  a2Degree : ℕ
  connections : ℕ
  watersPerConnection : ℕ
deriving DecidableEq, Repr

def cof1Topology : TopologyRecount where
  b3Nodes := 2
  a2Linkers := 3
  b3Degree := 3
  a2Degree := 2
  connections := 6
  watersPerConnection := 2

/-- Non-opaque carrier for the node/linker and cross-boundary bond recount in
`icho_2026_source/image/T3_page-1.png`. -/
def COF1TopologySpec : Prop :=
  cof1Topology.b3Nodes = 2 ∧
  cof1Topology.a2Linkers = 3 ∧
  cof1Topology.b3Degree = 3 ∧
  cof1Topology.a2Degree = 2 ∧
  cof1Topology.connections = 6 ∧
  cof1Topology.watersPerConnection = 2 ∧
  cof1Topology.b3Nodes * cof1Topology.b3Degree = cof1Topology.connections ∧
  cof1Topology.a2Linkers * cof1Topology.a2Degree = cof1Topology.connections

/-- The tritopic B3 building block read from the COF-1 panel. -/
def b3NodeFormula : CHBOFormula where
  carbon := 18
  hydrogen := 12
  boron := 0
  oxygen := 6

/-- The ditopic A2 diboronic-acid linker read from the source figure. -/
def a2LinkerFormula : CHBOFormula where
  carbon := 6
  hydrogen := 8
  boron := 2
  oxygen := 4

def waterFormula : CHBOFormula where
  carbon := 0
  hydrogen := 2
  boron := 0
  oxygen := 1

/-- Full input assembly `2 B3 + 3 A2`, before condensation. -/
def cof1AssemblyInput : CHBOFormula :=
  addFormula (scaleFormula cof1Topology.b3Nodes b3NodeFormula)
    (scaleFormula cof1Topology.a2Linkers a2LinkerFormula)

/-- The twelve waters lost at the six cyclic boronate connections. -/
def cof1CondensationLoss : CHBOFormula :=
  scaleFormula (cof1Topology.connections * cof1Topology.watersPerConnection)
    waterFormula

/-- Recombined atom count of the periodic assembly after condensation. -/
def cof1AssemblyProduct : CHBOFormula where
  carbon := 54
  hydrogen := 24
  boron := 6
  oxygen := 12

/-- Carbon conservation for the quantitative material stage. -/
def COF1CarbonLedger : Prop :=
  cof1AssemblyInput.carbon =
    cof1AssemblyProduct.carbon + cof1CondensationLoss.carbon

/-- Hydrogen conservation for the quantitative material stage. -/
def COF1HydrogenLedger : Prop :=
  cof1AssemblyInput.hydrogen =
    cof1AssemblyProduct.hydrogen + cof1CondensationLoss.hydrogen

/-- Boron conservation for the quantitative material stage. -/
def COF1BoronLedger : Prop :=
  cof1AssemblyInput.boron =
    cof1AssemblyProduct.boron + cof1CondensationLoss.boron

/-- Oxygen conservation for the quantitative material stage. -/
def COF1OxygenLedger : Prop :=
  cof1AssemblyInput.oxygen =
    cof1AssemblyProduct.oxygen + cof1CondensationLoss.oxygen

/-- Complete source-bounded atom ledger, with the named water stream as the
only output other than the assembled framework. -/
def COF1CondensationSpec : Prop :=
  cof1TransformationUse = .quantitativeMaterialStage ∧
  cof1Topology.connections * cof1Topology.watersPerConnection = 12 ∧
  addFormula cof1AssemblyProduct cof1CondensationLoss = cof1AssemblyInput ∧
  COF1CarbonLedger ∧ COF1HydrogenLedger ∧ COF1BoronLedger ∧ COF1OxygenLedger

/-- A formula is primitive when its four displayed subscripts have gcd one. -/
def IsPrimitive (f : CHBOFormula) : Prop :=
  Nat.gcd f.carbon (Nat.gcd f.hydrogen (Nat.gcd f.boron f.oxygen)) = 1

/-- A primitive formula whose positive integral multiple is the assembled
periodic composition is an empirical formula of that assembly. -/
def IsEmpiricalFormulaOf (assembly candidate : CHBOFormula) : Prop :=
  IsPrimitive candidate ∧
  ∃ n : ℕ, 0 < n ∧ scaleFormula n candidate = assembly

/-- Candidate obtained by gcd reduction of `C54H24B6O12`. -/
def cof1EmpiricalFormula : CHBOFormula where
  carbon := 9
  hydrogen := 4
  boron := 1
  oxygen := 2

def COF1EmpiricalFormulaSpec : Prop :=
  scaleFormula 6 cof1EmpiricalFormula = cof1AssemblyProduct ∧
  IsEmpiricalFormulaOf cof1AssemblyProduct cof1EmpiricalFormula

/-- One version-pinned atomic-weight record used by the mass calculation. -/
structure AtomicWeightDatum where
  element : String
  value : ℚ
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String
  sourceUrl : String
deriving DecidableEq, Repr

def atomicWeightDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def atomicWeightDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def carbonAtomicWeightDatum : AtomicWeightDatum where
  element := "C"
  value := 12011 / 1000
  datasetVersion := atomicWeightDatasetVersion
  datasetSha256 := atomicWeightDatasetSha256
  recordSha256 := "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a"
  sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm"

def hydrogenAtomicWeightDatum : AtomicWeightDatum where
  element := "H"
  value := 126 / 125
  datasetVersion := atomicWeightDatasetVersion
  datasetSha256 := atomicWeightDatasetSha256
  recordSha256 := "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"
  sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm"

def boronAtomicWeightDatum : AtomicWeightDatum where
  element := "B"
  value := 1081 / 100
  datasetVersion := atomicWeightDatasetVersion
  datasetSha256 := atomicWeightDatasetSha256
  recordSha256 := "1c5d40bfe965195b46bab8df18add6fbf178bdf4720dcba73b24c61c62038173"
  sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm"

def oxygenAtomicWeightDatum : AtomicWeightDatum where
  element := "O"
  value := 15999 / 1000
  datasetVersion := atomicWeightDatasetVersion
  datasetSha256 := atomicWeightDatasetSha256
  recordSha256 := "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"
  sourceUrl := "https://ciaaw.org/abridged-atomic-weights.htm"

def carbonAtomicWeight : ℝ := carbonAtomicWeightDatum.value
def hydrogenAtomicWeight : ℝ := hydrogenAtomicWeightDatum.value
def boronAtomicWeight : ℝ := boronAtomicWeightDatum.value
def oxygenAtomicWeight : ℝ := oxygenAtomicWeightDatum.value

/-- Numerator of the carbon mass fraction: mass of the nine carbon atoms in
one empirical-formula unit. -/
def cof1CarbonMassContribution : ℝ :=
  cof1EmpiricalFormula.carbon * carbonAtomicWeight

/-- Denominator of the carbon mass fraction: total mass of the entire
`C9H4BO2` empirical-formula unit, not a carbon-free base mass. -/
def cof1FormulaMolarMass : ℝ :=
  cof1EmpiricalFormula.carbon * carbonAtomicWeight +
  cof1EmpiricalFormula.hydrogen * hydrogenAtomicWeight +
  cof1EmpiricalFormula.boron * boronAtomicWeight +
  cof1EmpiricalFormula.oxygen * oxygenAtomicWeight

/-- Exact, unrounded carbon mass percentage. -/
def rawCarbonMassPercent : ℝ :=
  100 * cof1CarbonMassContribution / cof1FormulaMolarMass

/-- End-to-end arithmetic specification for the exact carbon percentage. -/
def CarbonMassPercentDerivationSpec : Prop :=
  cof1CarbonMassContribution = (108099 : ℝ) / 1000 ∧
  cof1FormulaMolarMass = (154939 : ℝ) / 1000 ∧
  0 < cof1FormulaMolarMass ∧
  rawCarbonMassPercent =
    100 * cof1CarbonMassContribution / cof1FormulaMolarMass ∧
  rawCarbonMassPercent = (10809900 : ℝ) / 154939 ∧
  (13953 : ℝ) / 200 ≤ rawCarbonMassPercent ∧
  rawCarbonMassPercent < (2791 : ℝ) / 40

/-- Mixed raw-result proposition covering both requested outputs. -/
def RawResultSpec : Prop :=
  COF1TopologySpec ∧
  COF1CondensationSpec ∧
  COF1EmpiricalFormulaSpec ∧
  CarbonMassPercentDerivationSpec

/-- Mixed displayed-result proposition: the formula stays exact while only the
mass percentage crosses the source-requested two-decimal reporting boundary. -/
def ReportedResultSpec : Prop :=
  COF1EmpiricalFormulaSpec ∧
  ReportsAtQuantum rawCarbonMassPercent ((6977 : ℝ) / 100) ((1 : ℝ) / 100)

theorem cof1Topology_from_source_image : COF1TopologySpec := by
  unfold COF1TopologySpec
  decide

theorem cof1Condensation_atom_ledger : COF1CondensationSpec := by
  unfold COF1CondensationSpec COF1CarbonLedger COF1HydrogenLedger
    COF1BoronLedger COF1OxygenLedger
  decide

theorem cof1EmpiricalFormula_raw : COF1EmpiricalFormulaSpec := by
  unfold COF1EmpiricalFormulaSpec IsEmpiricalFormulaOf
  refine ⟨rfl, ?_, ⟨6, by norm_num, rfl⟩⟩
  norm_num [IsPrimitive, cof1EmpiricalFormula]

theorem cof1CarbonMassPercent_raw : CarbonMassPercentDerivationSpec := by
  norm_num [CarbonMassPercentDerivationSpec, cof1CarbonMassContribution,
    cof1FormulaMolarMass, rawCarbonMassPercent, cof1EmpiricalFormula,
    carbonAtomicWeight, hydrogenAtomicWeight, boronAtomicWeight,
    oxygenAtomicWeight, carbonAtomicWeightDatum, hydrogenAtomicWeightDatum,
    boronAtomicWeightDatum, oxygenAtomicWeightDatum]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"cof1_carbon_mass_percent","reporting_policy_kind":"decimal_places","reporting_policy_digits":2,"reported_value":"69.77","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.IChO2026T3A1.rawCarbonMassPercent","reporting_declaration":"IChO2026Problems.IChO2026T3A1.cof1CarbonMassPercent_reported"}
theorem cof1CarbonMassPercent_reported :
    ReportsAtQuantum rawCarbonMassPercent ((6977 : ℝ) / 100) ((1 : ℝ) / 100) := by
  rcases cof1CarbonMassPercent_raw with
    ⟨_, _, _, _, _, hLower, hUpper⟩
  unfold ReportsAtQuantum
  refine ⟨by norm_num, ⟨(6977 : ℤ), by norm_num⟩, ?_⟩
  have hRawNonnegative : 0 ≤ rawCarbonMassPercent := by
    exact le_trans (by norm_num) hLower
  rw [if_pos hRawNonnegative]
  constructor
  · norm_num at hLower ⊢
    exact hLower
  · norm_num at hUpper ⊢
    exact hUpper

theorem rawResultSpec_valid : RawResultSpec := by
  exact ⟨cof1Topology_from_source_image, cof1Condensation_atom_ledger,
    cof1EmpiricalFormula_raw, cof1CarbonMassPercent_raw⟩

theorem reportedResultSpec_valid : ReportedResultSpec := by
  exact ⟨cof1EmpiricalFormula_raw, cof1CarbonMassPercent_reported⟩

/-- Payload-bound raw mixed-result contract for the answer-blind verifier. -/
theorem rawResultContract :
    ("db16f7a8d4f438e3502cb5e1b30feb6549923e196fbc8d00de193aa73275ebbb" : String) =
      "db16f7a8d4f438e3502cb5e1b30feb6549923e196fbc8d00de193aa73275ebbb" ∧
    RawResultSpec := by
  exact ⟨rfl, rawResultSpec_valid⟩

/-- Payload-bound displayed mixed-result contract for the answer-blind verifier. -/
theorem reportedResultContract :
    ("bf450ef6bebbc4ef9d11cc134e4c26da43634cb04b5d502bc87b33e88aac2514" : String) =
      "bf450ef6bebbc4ef9d11cc134e4c26da43634cb04b5d502bc87b33e88aac2514" ∧
    ReportedResultSpec := by
  exact ⟨rfl, reportedResultSpec_valid⟩

end

end IChO2026Problems.IChO2026T3A1
