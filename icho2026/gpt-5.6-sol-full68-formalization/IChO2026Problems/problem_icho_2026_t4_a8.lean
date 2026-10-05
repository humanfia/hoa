import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T4-A8

This is the assumption-augmented version authorized for this target only.
The original page prints `Q = 2.2 * 10^5 m^3` without a time denominator.
Supplement `t4_a8_flow_per_day_user_approved` supplies the missing
interpretation `Q = 2.2 * 10^5 m^3 day^-1`; it is not printed source data and
is not an official correction.

The file derives the T4-A7 combustion enthalpy from the bound table, applies
the ideal-gas amount equation to the supplemented daily methane flow, audits
the complete gaseous combustion ledger, and rounds only the final energy.
-/

namespace IChO2026Problems.ProblemIcho2026T4A8

noncomputable section

/-! ## Evidence and assumption provenance -/

inductive EvidenceOrigin
  | problemImage
  | explicitUserSupplement
  | publicLiterature
  | configuredLibrary
  deriving DecidableEq

structure SourceLocator where
  path : String
  sha256 : String
  region : String
  deriving DecidableEq

structure EvidenceCitation where
  origin : EvidenceOrigin
  title : String
  stableURL : String
  locator : String
  exactScopedClaim : String
  applicabilityConditions : List String
  exclusions : List String
  contentSha256 : String
  deriving DecidableEq

structure SupplementalAssumption where
  assumptionId : String
  recordPath : String
  recordSha256 : String
  sourceBundleSha256 : String
  sourceRecordSha256 : String
  evaluationBasis : String
  originalProblemUnchanged : Bool
  printedUnit : String
  assumedUnit : String
  sourceLocator : String
  deriving DecidableEq

def page2ThermochemicalLocator : SourceLocator where
  path := "icho_2026_source/image/T4_page-2.png"
  sha256 :=
    "60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94"
  region := "T4-A6 gaseous-species condition and seven-row thermochemical table"

def page3FlowLocator : SourceLocator where
  path := "icho_2026_source/image/T4_page-3.png"
  sha256 :=
    "c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc"
  region := "methane inlet sentence immediately above T4-A8"

def page3QuestionLocator : SourceLocator where
  path := "icho_2026_source/image/T4_page-3.png"
  sha256 :=
    "c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc"
  region := "T4-A8 requested total energy per day in J day^-1"

def flowPerDaySupplement : SupplementalAssumption where
  assumptionId := "t4_a8_flow_per_day_user_approved"
  recordPath := ".archon/user_input_assumptions/icho_2026_t4_a8.json"
  recordSha256 :=
    "b00c46ed4f03b1478b16f32382766d4ffef427001440d998d01c96ff3577a252"
  sourceBundleSha256 :=
    "865b4417565ec94097e4287aa7746ee08fb527c80f72b7c15378fa0db9fd8ddc"
  sourceRecordSha256 :=
    "2d0e4b9c891b7752aa1dc83b95ba09a2784e5117cafe1c8d7f9b9b6fa131c38b"
  evaluationBasis := "user_assumption_augmented"
  originalProblemUnchanged := true
  printedUnit := "m^3"
  assumedUnit := "m^3 day^-1"
  sourceLocator := "theory_problem.pdf page 39 / Q4-3, flow datum before 4.8"

def printedPressure_kPa : ℝ := (101325 : ℝ) / 1000
def pascalsPerKilopascal : ℝ := 1000
def printedPressure_Pa : ℝ := printedPressure_kPa * pascalsPerKilopascal
def printedInletTemperature_K : ℝ := 298
def printedCombustionTemperature_K : ℝ := 2000
def printedFlowMagnitude_m3 : ℝ := (22 : ℝ) / 10 * 10 ^ 5
def printedFlowRoleText : String := "volumetric flow"
def printedFlowUnitTokens : List String := ["m^3"]
/-- The original image has no time-denominator token attached to the flow. -/
def printedFlowTimeDenominatorTokens : List String := []
def requestedOutputUnitText : String := "J day^-1"
def requestedTimeHorizonText : String := "per day"

/-- The original-paper facts, deliberately kept separate from the supplement. -/
def OriginalPrintedFlowAndQuestionFacts : Prop :=
  page3FlowLocator.path = "icho_2026_source/image/T4_page-3.png" ∧
  page3FlowLocator.sha256 =
    "c9d3ffc7f4dcd8176195f846733981e77fe9ac3cf21e5b6a1be89f140eecdbdc" ∧
  printedPressure_kPa = (101325 : ℝ) / 1000 ∧
  printedPressure_Pa = 101325 ∧
  printedInletTemperature_K = 298 ∧
  printedFlowMagnitude_m3 = 220000 ∧
  printedFlowRoleText = "volumetric flow" ∧
  printedFlowUnitTokens = ["m^3"] ∧
  printedFlowTimeDenominatorTokens = [] ∧
  requestedTimeHorizonText = "per day" ∧
  requestedOutputUnitText = "J day^-1" ∧
  printedCombustionTemperature_K = 2000

theorem originalPrintedFlowAndQuestionFacts :
    OriginalPrintedFlowAndQuestionFacts := by
  norm_num [OriginalPrintedFlowAndQuestionFacts, page3FlowLocator,
    printedPressure_kPa, printedPressure_Pa, pascalsPerKilopascal,
    printedInletTemperature_K, printedCombustionTemperature_K,
    printedFlowMagnitude_m3, printedFlowRoleText, printedFlowUnitTokens,
    printedFlowTimeDenominatorTokens, requestedTimeHorizonText,
    requestedOutputUnitText]

/-- The sole added experimental input: the printed magnitude is per day. -/
def supplementedMethaneFlow_m3PerDay : ℝ := printedFlowMagnitude_m3

def UserApprovedFlowSupplementFacts : Prop :=
  flowPerDaySupplement.assumptionId =
    "t4_a8_flow_per_day_user_approved" ∧
  flowPerDaySupplement.recordSha256 =
    "b00c46ed4f03b1478b16f32382766d4ffef427001440d998d01c96ff3577a252" ∧
  flowPerDaySupplement.evaluationBasis = "user_assumption_augmented" ∧
  flowPerDaySupplement.originalProblemUnchanged = true ∧
  flowPerDaySupplement.printedUnit = "m^3" ∧
  flowPerDaySupplement.assumedUnit = "m^3 day^-1" ∧
  printedFlowTimeDenominatorTokens = [] ∧
  supplementedMethaneFlow_m3PerDay = 220000

theorem userApprovedFlowSupplementFacts :
    UserApprovedFlowSupplementFacts := by
  norm_num [UserApprovedFlowSupplementFacts, flowPerDaySupplement,
    supplementedMethaneFlow_m3PerDay, printedFlowMagnitude_m3,
    printedFlowTimeDenominatorTokens]

/-! ## Exact SI molar gas constant and the ideal-gas bridge -/

def gasConstantCitation : EvidenceCitation where
  origin := .publicLiterature
  title := "NIST CODATA complete listing of the 2022 constants"
  stableURL := "https://physics.nist.gov/cuu/Constants/Table/allascii.txt"
  locator := "molar gas constant, Avogadro constant, and Boltzmann constant rows"
  exactScopedClaim :=
    "N_A = 6.02214076e23 mol^-1 and k = 1.380649e-23 J K^-1 are exact; R = N_A*k = 8.31446261815324 J mol^-1 K^-1."
  applicabilityConditions := ["ideal-gas amount calculation in SI units"]
  exclusions := ["no empirical claim about methane combustion products"]
  contentSha256 :=
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"

def idealGasLawLibraryCitation : EvidenceCitation where
  origin := .configuredLibrary
  title := "Physlib ideal gas as a microcanonical ensemble"
  stableURL := ""
  locator :=
    "Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas.lean, IdealGas.ideal_gas_law"
  exactScopedClaim := "For positive volume and temperature, the model proves P*V = n*R*T."
  applicabilityConditions := ["ideal-gas model", "positive volume", "positive temperature"]
  exclusions := ["the library theorem uses normalized dimensionless R = 1"]
  contentSha256 :=
    "0e04f27a5a11406d39f7bcd69c6f852c447724c41d922ee629b7f7fc5c16d3fc"

def avogadroConstant_perMol : ℝ := 602214076000000000000000
def boltzmannConstant_JPerKelvin : ℝ :=
  1380649 / 100000000000000000000000000000
def molarGasConstant_JPerMolKelvin : ℝ :=
  avogadroConstant_perMol * boltzmannConstant_JPerKelvin

def GasConstantReferenceAudit : Prop :=
  gasConstantCitation.origin = .publicLiterature ∧
  gasConstantCitation.stableURL =
    "https://physics.nist.gov/cuu/Constants/Table/allascii.txt" ∧
  gasConstantCitation.contentSha256 =
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67" ∧
  idealGasLawLibraryCitation.origin = .configuredLibrary ∧
  molarGasConstant_JPerMolKelvin =
    avogadroConstant_perMol * boltzmannConstant_JPerKelvin ∧
  molarGasConstant_JPerMolKelvin =
    (207861565453831 : ℝ) / 25000000000000 ∧
  0 < molarGasConstant_JPerMolKelvin

theorem gasConstantReferenceAudit : GasConstantReferenceAudit := by
  norm_num [GasConstantReferenceAudit, gasConstantCitation,
    idealGasLawLibraryCitation, molarGasConstant_JPerMolKelvin,
    avogadroConstant_perMol, boltzmannConstant_JPerKelvin]

/-! ## Complete gaseous methane combustion -/

inductive CombustionSpecies
  | methane
  | oxygen
  | carbonDioxide
  | water
  deriving DecidableEq, Fintype

inductive CombustionElement
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

inductive Phase
  | gas
  deriving DecidableEq

def speciesPhase (_ : CombustionSpecies) : Phase := .gas

/-- `CH4(g) + 2 O2(g) -> CO2(g) + 2 H2O(g)`. -/
def methaneCombustion : CRNT.Reaction CombustionSpecies where
  source
    | .methane => 1
    | .oxygen => 2
    | .carbonDioxide => 0
    | .water => 0
  target
    | .methane => 0
    | .oxygen => 0
    | .carbonDioxide => 1
    | .water => 2

def atomCount : CombustionSpecies → CombustionElement → ℕ
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

def complexAtomCount
    (complex : CombustionSpecies → ℕ) (element : CombustionElement) : ℕ :=
  Finset.univ.sum fun species : CombustionSpecies =>
    complex species * atomCount species element

def formalCharge (_ : CombustionSpecies) : ℤ := 0

def complexFormalCharge (complex : CombustionSpecies → ℕ) : ℤ :=
  Finset.univ.sum fun species : CombustionSpecies =>
    (complex species : ℤ) * formalCharge species

def CompleteGaseousCombustionContract : Prop :=
  methaneCombustion.source .methane = 1 ∧
  methaneCombustion.source .oxygen = 2 ∧
  methaneCombustion.target .carbonDioxide = 1 ∧
  methaneCombustion.target .water = 2 ∧
  (∀ element : CombustionElement,
    complexAtomCount methaneCombustion.source element =
      complexAtomCount methaneCombustion.target element) ∧
  complexFormalCharge methaneCombustion.source =
    complexFormalCharge methaneCombustion.target ∧
  (∀ species : CombustionSpecies, speciesPhase species = .gas)

theorem completeGaseousCombustionContract :
    CompleteGaseousCombustionContract := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro element
    cases element <;> decide
  · simp [complexFormalCharge, formalCharge]
  · intro species
    rfl

/-- The inductive carrier is exactly the four named species; it has no
anonymous `other` or residual stream. -/
theorem combustionSpeciesDomain_exhaustive (species : CombustionSpecies) :
    species = .methane ∨ species = .oxygen ∨
      species = .carbonDioxide ∨ species = .water := by
  cases species <;> simp

/-! ## Rootless inline derivation of prerequisite T4-A7 -/

/-- Printed standard formation enthalpies at 298 K, in kJ mol^-1. `O2(g)` is
zero by the standard-state definition of formation enthalpy. -/
def formationEnthalpy298_kJPerMol : CombustionSpecies → ℝ
  | .methane => -(748 : ℝ) / 10
  | .oxygen => 0
  | .carbonDioxide => -(3935 : ℝ) / 10
  | .water => -(2418 : ℝ) / 10

/-- Printed constant-pressure heat capacities, in J mol^-1 K^-1. -/
def heatCapacity_JPerMolKelvin : CombustionSpecies → ℝ
  | .methane => 35
  | .oxygen => 29
  | .carbonDioxide => 37
  | .water => 34

def reactionPropertyChange (property : CombustionSpecies → ℝ) : ℝ :=
  Finset.univ.sum fun species : CombustionSpecies =>
    methaneCombustion.vector species * property species

def deltaH298_kJPerMol : ℝ :=
  reactionPropertyChange formationEnthalpy298_kJPerMol

def deltaCp_JPerMolKelvin : ℝ :=
  reactionPropertyChange heatCapacity_JPerMolKelvin

/-- Kirchhoff correction with constant printed heat capacities. -/
def deltaH2000_kJPerMol : ℝ :=
  deltaH298_kJPerMol +
    deltaCp_JPerMolKelvin *
      (printedCombustionTemperature_K - printedInletTemperature_K) / 1000

def PrintedThermochemicalFacts : Prop :=
  page2ThermochemicalLocator.path =
    "icho_2026_source/image/T4_page-2.png" ∧
  page2ThermochemicalLocator.sha256 =
    "60fade5df8174639d11a19bc537d53719ebd964c90940d40844f99c42f932c94" ∧
  formationEnthalpy298_kJPerMol .methane = -(748 : ℝ) / 10 ∧
  formationEnthalpy298_kJPerMol .oxygen = 0 ∧
  formationEnthalpy298_kJPerMol .carbonDioxide = -(3935 : ℝ) / 10 ∧
  formationEnthalpy298_kJPerMol .water = -(2418 : ℝ) / 10 ∧
  heatCapacity_JPerMolKelvin .methane = 35 ∧
  heatCapacity_JPerMolKelvin .oxygen = 29 ∧
  heatCapacity_JPerMolKelvin .carbonDioxide = 37 ∧
  heatCapacity_JPerMolKelvin .water = 34

theorem printedThermochemicalFacts : PrintedThermochemicalFacts := by
  norm_num [PrintedThermochemicalFacts, page2ThermochemicalLocator,
    formationEnthalpy298_kJPerMol, heatCapacity_JPerMolKelvin]

theorem deltaH298_exact :
    deltaH298_kJPerMol = -(8023 : ℝ) / 10 := by
  have hspecies :
      (Finset.univ : Finset CombustionSpecies) =
        {.methane, .oxygen, .carbonDioxide, .water} := by
    decide
  rw [deltaH298_kJPerMol, reactionPropertyChange, hspecies]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [methaneCombustion, CRNT.Reaction.vector,
    formationEnthalpy298_kJPerMol]

theorem deltaCp_exact : deltaCp_JPerMolKelvin = 12 := by
  have hspecies :
      (Finset.univ : Finset CombustionSpecies) =
        {.methane, .oxygen, .carbonDioxide, .water} := by
    decide
  rw [deltaCp_JPerMolKelvin, reactionPropertyChange, hspecies]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [methaneCombustion, CRNT.Reaction.vector,
    heatCapacity_JPerMolKelvin]

/-- T4-A7 is derived; neither printed fallback is used. -/
theorem deltaH2000_exact :
    deltaH2000_kJPerMol = -(195469 : ℝ) / 250 := by
  rw [deltaH2000_kJPerMol, deltaH298_exact, deltaCp_exact]
  norm_num [printedCombustionTemperature_K, printedInletTemperature_K]

theorem heatReleasedPerMole2000_pos : 0 < -deltaH2000_kJPerMol := by
  rw [deltaH2000_exact]
  norm_num

/-! ## Daily ideal-gas amount and quantitative combustion ledger -/

def methaneAmountPerDay_molPerDay : ℝ :=
  printedPressure_Pa * supplementedMethaneFlow_m3PerDay /
    (molarGasConstant_JPerMolKelvin * printedInletTemperature_K)

def IdealGasAmountEquation (amount_molPerDay : ℝ) : Prop :=
  printedPressure_Pa * supplementedMethaneFlow_m3PerDay =
    amount_molPerDay * molarGasConstant_JPerMolKelvin *
      printedInletTemperature_K

theorem methaneAmountPerDay_satisfiesIdealGasLaw :
    IdealGasAmountEquation methaneAmountPerDay_molPerDay := by
  norm_num [IdealGasAmountEquation, methaneAmountPerDay_molPerDay,
    printedPressure_Pa, printedPressure_kPa, pascalsPerKilopascal,
    supplementedMethaneFlow_m3PerDay, printedFlowMagnitude_m3,
    molarGasConstant_JPerMolKelvin, avogadroConstant_perMol,
    boltzmannConstant_JPerKelvin, printedInletTemperature_K]

def combustionInputPerDay_molPerDay (species : CombustionSpecies) : ℝ :=
  (methaneCombustion.source species : ℝ) * methaneAmountPerDay_molPerDay

def combustionOutputPerDay_molPerDay (species : CombustionSpecies) : ℝ :=
  (methaneCombustion.target species : ℝ) * methaneAmountPerDay_molPerDay

def atomAmountPerDay_molAtomsPerDay
    (flow : CombustionSpecies → ℝ) (element : CombustionElement) : ℝ :=
  Finset.univ.sum fun species : CombustionSpecies =>
    flow species * atomCount species element

def chargeAmountPerDay_molChargePerDay
    (flow : CombustionSpecies → ℝ) : ℝ :=
  Finset.univ.sum fun species : CombustionSpecies =>
    flow species * formalCharge species

inductive StagedTransformationClassification
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq

def combustionStageClassification : StagedTransformationClassification :=
  .quantitativeMaterialStage

/-- Complete-combustion ledger. The finite carrier contains only the four
named species, and the reaction has no anonymous stream, residue, or recycle. -/
def CompleteDailyCombustionLedger : Prop :=
  combustionStageClassification = .quantitativeMaterialStage ∧
  IdealGasAmountEquation methaneAmountPerDay_molPerDay ∧
  0 < methaneAmountPerDay_molPerDay ∧
  (∀ species : CombustionSpecies,
    0 ≤ combustionInputPerDay_molPerDay species ∧
    0 ≤ combustionOutputPerDay_molPerDay species) ∧
  (∀ element : CombustionElement,
    atomAmountPerDay_molAtomsPerDay combustionInputPerDay_molPerDay element =
      atomAmountPerDay_molAtomsPerDay
        combustionOutputPerDay_molPerDay element) ∧
  chargeAmountPerDay_molChargePerDay combustionInputPerDay_molPerDay =
    chargeAmountPerDay_molChargePerDay combustionOutputPerDay_molPerDay ∧
  (∀ species : CombustionSpecies, speciesPhase species = .gas)

theorem completeDailyCombustionLedger : CompleteDailyCombustionLedger := by
  have hamount : 0 < methaneAmountPerDay_molPerDay := by
    norm_num [methaneAmountPerDay_molPerDay, printedPressure_Pa,
      printedPressure_kPa, pascalsPerKilopascal,
      supplementedMethaneFlow_m3PerDay, printedFlowMagnitude_m3,
      molarGasConstant_JPerMolKelvin, avogadroConstant_perMol,
      boltzmannConstant_JPerKelvin, printedInletTemperature_K]
  refine ⟨rfl, methaneAmountPerDay_satisfiesIdealGasLaw, hamount, ?_, ?_, ?_, ?_⟩
  · intro species
    constructor <;> exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hamount)
  · intro element
    have hspecies :
        (Finset.univ : Finset CombustionSpecies) =
          {.methane, .oxygen, .carbonDioxide, .water} := by
      decide
    cases element <;>
      rw [atomAmountPerDay_molAtomsPerDay,
        atomAmountPerDay_molAtomsPerDay, hspecies,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton] <;>
      norm_num [combustionInputPerDay_molPerDay,
        combustionOutputPerDay_molPerDay, methaneCombustion, atomCount] <;>
      ring
  · simp [chargeAmountPerDay_molChargePerDay, formalCharge]
  · intro species
    rfl

/-! ## Dimensional audit -/

/-- Exponents of length, time, mass, temperature, and amount of substance. -/
structure ChemicalUnitDimension where
  length : ℚ
  time : ℚ
  mass : ℚ
  temperature : ℚ
  amount : ℚ
  deriving DecidableEq

def ChemicalUnitDimension.mul
    (a b : ChemicalUnitDimension) : ChemicalUnitDimension :=
  ⟨a.length + b.length, a.time + b.time, a.mass + b.mass,
    a.temperature + b.temperature, a.amount + b.amount⟩

def ChemicalUnitDimension.inv
    (a : ChemicalUnitDimension) : ChemicalUnitDimension :=
  ⟨-a.length, -a.time, -a.mass, -a.temperature, -a.amount⟩

def ChemicalUnitDimension.div
    (a b : ChemicalUnitDimension) : ChemicalUnitDimension :=
  a.mul b.inv

def volumeDimension : ChemicalUnitDimension := ⟨3, 0, 0, 0, 0⟩
def timeDimension : ChemicalUnitDimension := ⟨0, 1, 0, 0, 0⟩
def pressureDimension : ChemicalUnitDimension := ⟨-1, -2, 1, 0, 0⟩
def temperatureDimension : ChemicalUnitDimension := ⟨0, 0, 0, 1, 0⟩
def amountDimension : ChemicalUnitDimension := ⟨0, 0, 0, 0, 1⟩
def energyDimension : ChemicalUnitDimension := ⟨2, -2, 1, 0, 0⟩
def supplementedFlowDimension : ChemicalUnitDimension :=
  volumeDimension.div timeDimension
def gasConstantDimension : ChemicalUnitDimension :=
  energyDimension.div (amountDimension.mul temperatureDimension)
def molarEnthalpyDimension : ChemicalUnitDimension :=
  energyDimension.div amountDimension

def DailyEnergyDimensionAudit : Prop :=
  supplementedFlowDimension = volumeDimension.div timeDimension ∧
  (pressureDimension.mul supplementedFlowDimension).div
      (gasConstantDimension.mul temperatureDimension) =
    amountDimension.div timeDimension ∧
  (amountDimension.div timeDimension).mul molarEnthalpyDimension =
    energyDimension.div timeDimension

theorem dailyEnergyDimensionAudit : DailyEnergyDimensionAudit := by
  norm_num [DailyEnergyDimensionAudit, supplementedFlowDimension,
    gasConstantDimension, molarEnthalpyDimension, volumeDimension,
    timeDimension, pressureDimension, temperatureDimension, amountDimension,
    energyDimension, ChemicalUnitDimension.mul, ChemicalUnitDimension.inv,
    ChemicalUnitDimension.div]

/-! ## Raw requested output and reporting -/

def joulesPerKilojoule : ℝ := 1000

/-- Unrounded end-to-end requested output in J day^-1. -/
def dailyEnergyRaw_JPerDay : ℝ :=
  methaneAmountPerDay_molPerDay * (-deltaH2000_kJPerMol) *
    joulesPerKilojoule

def DailyEnergyEquation (energy_JPerDay : ℝ) : Prop :=
  energy_JPerDay =
    printedPressure_Pa * supplementedMethaneFlow_m3PerDay /
      (molarGasConstant_JPerMolKelvin * printedInletTemperature_K) *
      (-deltaH2000_kJPerMol) * joulesPerKilojoule

theorem dailyEnergyRaw_satisfiesEquation :
    DailyEnergyEquation dailyEnergyRaw_JPerDay := by
  rfl

theorem dailyEnergyRaw_positive : 0 < dailyEnergyRaw_JPerDay := by
  unfold dailyEnergyRaw_JPerDay
  exact mul_pos
    (mul_pos
      (by
        norm_num [methaneAmountPerDay_molPerDay, printedPressure_Pa,
          printedPressure_kPa, pascalsPerKilopascal,
          supplementedMethaneFlow_m3PerDay, printedFlowMagnitude_m3,
          molarGasConstant_JPerMolKelvin, avogadroConstant_perMol,
          boltzmannConstant_JPerKelvin, printedInletTemperature_K])
      heatReleasedPerMole2000_pos)
    (by norm_num [joulesPerKilojoule])

/-- Exact simplification of the end-to-end formula. -/
theorem dailyEnergyRaw_exact :
    dailyEnergyRaw_JPerDay =
      (217864860675000000000000000000 : ℝ) / 30971373252620819 := by
  rw [dailyEnergyRaw_JPerDay, methaneAmountPerDay_molPerDay,
    deltaH2000_exact]
  norm_num [printedPressure_Pa, printedPressure_kPa,
    pascalsPerKilopascal, supplementedMethaneFlow_m3PerDay,
    printedFlowMagnitude_m3, molarGasConstant_JPerMolKelvin,
    avogadroConstant_perMol, boltzmannConstant_JPerKelvin,
    printedInletTemperature_K, joulesPerKilojoule]

def exactInputPolicyText : String :=
  "Printed contest constants are exact central inputs; N_A, k, and R are exact SI constants; the output enclosure is not a measurement tolerance."

def ExactInputAndSignAudit : Prop :=
  exactInputPolicyText =
    "Printed contest constants are exact central inputs; N_A, k, and R are exact SI constants; the output enclosure is not a measurement tolerance." ∧
  deltaH2000_kJPerMol < 0 ∧
  0 < -deltaH2000_kJPerMol ∧
  0 < dailyEnergyRaw_JPerDay

theorem exactInputAndSignAudit : ExactInputAndSignAudit := by
  refine ⟨rfl, ?_, heatReleasedPerMole2000_pos, dailyEnergyRaw_positive⟩
  rw [deltaH2000_exact]
  norm_num

/-- Full assumption/target split for the raw answer. -/
def DailyEnergyRawDerivationSpec : Prop :=
  OriginalPrintedFlowAndQuestionFacts ∧
  UserApprovedFlowSupplementFacts ∧
  PrintedThermochemicalFacts ∧
  GasConstantReferenceAudit ∧
  CompleteGaseousCombustionContract ∧
  deltaH298_kJPerMol = -(8023 : ℝ) / 10 ∧
  deltaCp_JPerMolKelvin = 12 ∧
  deltaH2000_kJPerMol = -(195469 : ℝ) / 250 ∧
  IdealGasAmountEquation methaneAmountPerDay_molPerDay ∧
  CompleteDailyCombustionLedger ∧
  DailyEnergyDimensionAudit ∧
  ExactInputAndSignAudit ∧
  DailyEnergyEquation dailyEnergyRaw_JPerDay

theorem dailyEnergyRawDerivationSpec : DailyEnergyRawDerivationSpec := by
  exact ⟨originalPrintedFlowAndQuestionFacts,
    userApprovedFlowSupplementFacts, printedThermochemicalFacts,
    gasConstantReferenceAudit, completeGaseousCombustionContract,
    deltaH298_exact, deltaCp_exact, deltaH2000_exact,
    methaneAmountPerDay_satisfiesIdealGasLaw, completeDailyCombustionLedger,
    dailyEnergyDimensionAudit, exactInputAndSignAudit,
    dailyEnergyRaw_satisfiesEquation⟩

/-- Raw machine contract: the non-degenerate interval is an independently
proved rational enclosure, not an input uncertainty. -/
theorem dailyEnergy_raw_result :
    DailyEnergyRawDerivationSpec ∧
      (7034394597164 : ℝ) ≤ dailyEnergyRaw_JPerDay ∧
      dailyEnergyRaw_JPerDay ≤ (7034394597165 : ℝ) := by
  refine ⟨dailyEnergyRawDerivationSpec, ?_, ?_⟩
  · rw [dailyEnergyRaw_exact]
    norm_num
  · rw [dailyEnergyRaw_exact]
    norm_num

/-- Three significant figures at magnitude `10^12` have quantum `10^10`.
The raw value is positive, so the relation uses the positive half-open
rounding cell and the configured half-away-from-zero tie rule. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"daily_energy","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"7.03e12","reporting_quantum":"10000000000","raw_declaration":"IChO2026Problems.ProblemIcho2026T4A8.dailyEnergyRaw_JPerDay","reporting_declaration":"IChO2026Problems.ProblemIcho2026T4A8.dailyEnergy_reported_result"}
theorem dailyEnergy_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      dailyEnergyRaw_JPerDay (7030000000000 : ℝ) (10000000000 : ℝ) := by
  rw [IChO2026Chem.Reporting.ReportsAtQuantum, dailyEnergyRaw_exact]
  refine ⟨by norm_num, ⟨(703 : ℤ), by norm_num⟩, ?_⟩
  norm_num

end

end IChO2026Problems.ProblemIcho2026T4A8
