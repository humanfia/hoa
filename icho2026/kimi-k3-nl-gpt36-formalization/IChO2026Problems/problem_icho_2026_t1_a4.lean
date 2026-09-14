import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T1-A4

This file formalizes the identification requested in subquestion 1.4.  The
candidate is checked against the three printed mass percentages, the depicted
`C + NaF -> D` direction, a primitive atom ledger, and the printed industrial-
use clue.  No claim about reaction yield, completion, omitted products, or the
amount of unused excess NaF is made.
-/

open scoped BigOperators

namespace IChO2026Problems.ProblemIChO2026T1A4

noncomputable section

/-! ## Source-bounded chemical vocabulary -/

/-- Element roles that occur in the candidate composition audit.  `metalQ` is
a role, not a preselected element or a finite metal-candidate domain. -/
inductive ElementRole where
  | hydrogen
  | oxygen
  | fluorine
  | sodium
  | metalQ
  deriving DecidableEq, Fintype, Repr

/-- A complete atom-count ledger over the five roles used by this target. -/
abbrev ElementLedger := ElementRole → ℕ

namespace ElementLedger

/-- Pointwise addition of formula ledgers. -/
def add (a b : ElementLedger) : ElementLedger := fun e => a e + b e

/-- `n` copies of a formula ledger. -/
def scale (n : ℕ) (a : ElementLedger) : ElementLedger := fun e => n * a e

end ElementLedger

/-- The formula of water in the target's element-role ledger. -/
def waterFormula : ElementLedger
  | .hydrogen => 2
  | .oxygen => 1
  | .fluorine | .sodium | .metalQ => 0

/-- The formula of sodium fluoride. -/
def sodiumFluorideFormula : ElementLedger
  | .sodium | .fluorine => 1
  | .hydrogen | .oxygen | .metalQ => 0

/-- Candidate anhydrous `C`, written with the still-generic role `Q`: `QF3`. -/
def qFluorideThreeFormula : ElementLedger
  | .metalQ => 1
  | .fluorine => 3
  | .hydrogen | .oxygen | .sodium => 0

/-- Candidate `D`, written with the still-generic role `Q`: `Na3QF6`. -/
def sodiumThreeQFluorideSixFormula : ElementLedger
  | .sodium => 3
  | .metalQ => 1
  | .fluorine => 6
  | .hydrogen | .oxygen => 0

/-- A hydrate keeps the anhydrous core and the number of whole water adducts
separate, matching the notation `C * xH2O` in the question. -/
structure HydratedFormula where
  core : ElementLedger
  waterUnits : ℕ

/-- Full element ledger of a hydrate, including every water adduct. -/
def HydratedFormula.totalLedger (h : HydratedFormula) : ElementLedger :=
  ElementLedger.add h.core (ElementLedger.scale h.waterUnits waterFormula)

/-- The expanded candidate ledger `Q1 F3 H6 O3`. -/
def expandedQFluorideThreeTrihydrateFormula : ElementLedger
  | .metalQ => 1
  | .fluorine => 3
  | .hydrogen => 6
  | .oxygen => 3
  | .sodium => 0

/-- Phases that are stated in the source.  `unspecified` deliberately retains
the omitted phase of the second reaction arrow. -/
inductive Phase where
  | aqueous
  | precipitateSolid
  | unspecified
  deriving DecidableEq, Repr

/-- Named material roles appearing in the source text and scheme. -/
inductive SourceMaterial where
  | stone
  | diluteNitricAcid
  | sodiumFluoride
  | hydratedC
  | anhydrousC
  | compoundD
  deriving DecidableEq, Repr

/-- The source states the pH only qualitatively as approximately four. -/
inductive PHCondition where
  | approximatelyFour
  deriving DecidableEq, Repr

/-- Source record for the precipitation portion of the depicted scheme. -/
structure PrecipitationStage where
  startingSample : SourceMaterial
  acid : SourceMaterial
  pHCondition : PHCondition
  addedReagent : SourceMaterial
  product : SourceMaterial
  productPhase : Phase

/-- Direct transcription of the page-3 precipitation roles and direction. -/
def printedPrecipitationStage : PrecipitationStage where
  startingSample := .stone
  acid := .diluteNitricAcid
  pHCondition := .approximatelyFour
  addedReagent := .sodiumFluoride
  product := .hydratedC
  productPhase := .precipitateSolid

/-- Source record for the named transformation used only as a non-exclusive
compatibility constraint. -/
inductive ReagentAmountCondition where
  | excess
  deriving DecidableEq, Repr

structure ConversionArrow where
  reactant : SourceMaterial
  reagent : SourceMaterial
  reagentAmount : ReagentAmountCondition
  namedProduct : SourceMaterial

/-- Direct transcription of `anhydrous C --excess NaF--> D`. -/
def printedConversionArrow : ConversionArrow where
  reactant := .anhydrousC
  reagent := .sodiumFluoride
  reagentAmount := .excess
  namedProduct := .compoundD

/-! ## Pinned atomic-weight data -/

/-- One version-pinned offline atomic-weight record.  The uncertainty metadata
is retained but is not treated as a source measurement interval. -/
structure AtomicWeightRecord where
  element : String
  atomicNumber : ℕ
  value : ℝ
  uncertainty : ℝ
  unit : String
  datasetVersion : String
  datasetSHA256 : String
  recordSHA256 : String

def chemistryDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def chemistryDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def hydrogenAtomicWeight : AtomicWeightRecord where
  element := "H"
  atomicNumber := 1
  value := (10080 : ℝ) / 10000
  uncertainty := (2 : ℝ) / 10000
  unit := "1"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"

def oxygenAtomicWeight : AtomicWeightRecord where
  element := "O"
  atomicNumber := 8
  value := (15999 : ℝ) / 1000
  uncertainty := (1 : ℝ) / 1000
  unit := "1"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"

def fluorineAtomicWeight : AtomicWeightRecord where
  element := "F"
  atomicNumber := 9
  value := (18998 : ℝ) / 1000
  uncertainty := (1 : ℝ) / 1000
  unit := "1"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb"

def sodiumAtomicWeight : AtomicWeightRecord where
  element := "Na"
  atomicNumber := 11
  value := (22990 : ℝ) / 1000
  uncertainty := (1 : ℝ) / 1000
  unit := "1"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := "14234e37d6ac93ded8d1d6f1883bd01f1855b92c90a61fb1370b0bb83f736417"

def aluminiumAtomicWeight : AtomicWeightRecord where
  element := "Al"
  atomicNumber := 13
  value := (26982 : ℝ) / 1000
  uncertainty := (1 : ℝ) / 1000
  unit := "1"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := "bdb840d02b2eb42be07e27b58fc76501786c75d0a321d38f76dae129c84f5e7f"

/-- Identity data carried by the proposed metal output. -/
structure MetalIdentity where
  name : String
  atomicWeight : AtomicWeightRecord

/-- Candidate metal identity supported by the atomic-weight and industrial-use
audits below. -/
def aluminiumIdentity : MetalIdentity where
  name := "aluminium"
  atomicWeight := aluminiumAtomicWeight

/-- Atomic weight assigned to each role when auditing a proposed metal. -/
def roleAtomicWeight (q : MetalIdentity) : ElementRole → ℝ
  | .hydrogen => hydrogenAtomicWeight.value
  | .oxygen => oxygenAtomicWeight.value
  | .fluorine => fluorineAtomicWeight.value
  | .sodium => sodiumAtomicWeight.value
  | .metalQ => q.atomicWeight.value

/-- Molar mass obtained from the full element ledger. -/
def molarMass (q : MetalIdentity) (f : ElementLedger) : ℝ :=
  ∑ e : ElementRole, (f e : ℝ) * roleAtomicWeight q e

/-! ## Printed quantitative observations -/

/-- Printed mass fractions.  A displayed `0.01%` last place corresponds to a
fraction quantum of `0.0001`; the shared measurement predicate supplies the
closed half-quantum interval. -/
structure PrintedCompositionData where
  hydrateWaterFractionShown : ℝ
  hydrateWaterFractionQuantum : ℝ
  dSodiumFractionShown : ℝ
  dSodiumFractionQuantum : ℝ
  dMetalFractionShown : ℝ
  dMetalFractionQuantum : ℝ

def printedCompositionData : PrintedCompositionData where
  hydrateWaterFractionShown := (3916 : ℝ) / 10000
  hydrateWaterFractionQuantum := (1 : ℝ) / 10000
  dSodiumFractionShown := (3285 : ℝ) / 10000
  dSodiumFractionQuantum := (1 : ℝ) / 10000
  dMetalFractionShown := (1285 : ℝ) / 10000
  dMetalFractionQuantum := (1 : ℝ) / 10000

/-- Sodium numerator mass in one formula amount of `D`. -/
def sodiumComponentMass (d : ElementLedger) : ℝ :=
  (d .sodium : ℝ) * sodiumAtomicWeight.value

/-- Metal-Q numerator mass in one formula amount of `D`. -/
def metalQComponentMass (q : MetalIdentity) (d : ElementLedger) : ℝ :=
  (d .metalQ : ℝ) * q.atomicWeight.value

/-- Sodium mass divided by the total mass of the complete `D` formula. -/
def sodiumMassFraction (q : MetalIdentity) (d : ElementLedger) : ℝ :=
  sodiumComponentMass d / molarMass q d

/-- Metal-Q mass divided by the total mass of the complete `D` formula. -/
def metalQMassFraction (q : MetalIdentity) (d : ElementLedger) : ℝ :=
  metalQComponentMass q d / molarMass q d

/-- Water-adduct numerator mass in the complete hydrate. -/
def hydrateWaterComponentMass (q : MetalIdentity) (h : HydratedFormula) : ℝ :=
  molarMass q (ElementLedger.scale h.waterUnits waterFormula)

/-- Water-adduct mass divided by total hydrate mass (core plus all waters). -/
def hydrateWaterMassFraction (q : MetalIdentity) (h : HydratedFormula) : ℝ :=
  hydrateWaterComponentMass q h / molarMass q h.totalLedger

/-! ## Source-scoped industrial-use bridge -/

/-- Metadata and the exact bounded claim checked for the industrial-use clue.
This is candidate compatibility evidence, not an inverse classification rule. -/
structure IndustrialUseCitation where
  title : String
  url : String
  locator : String
  exactClaim : String
  applicabilityConditions : String
  electrolyteFormula : ElementLedger
  producedMetalName : String
  producedMetalSymbol : String

/-- Royal Society of Chemistry, *Aluminium*, “Natural abundance” and
“Chemistry in its element: aluminium” transcript.  The page states both that
aluminium oxide is dissolved in molten cryolite in commercial production and
that cryolite is sodium hexafluoroaluminate. -/
def rscCryoliteAluminiumCitation : IndustrialUseCitation where
  title := "Royal Society of Chemistry Periodic Table: Aluminium"
  url := "https://www.rsc.org/periodic-table/element/13/aluminium"
  locator := "Natural abundance; Chemistry in its element: aluminium transcript"
  exactClaim :=
    "Most commercially produced aluminium is extracted by the Hall-Heroult process. In this process aluminium oxide is dissolved in molten cryolite and then electrolytically reduced to pure aluminium. The transcript says: he dissolved aluminium oxide in a bath of molten sodium hexafluoroaluminate (more commonly known as 'cryolite')."
  applicabilityConditions :=
    "Compatibility only for sodium hexafluoroaluminate used in the Hall-Heroult production of aluminium."
  electrolyteFormula := sodiumThreeQFluorideSixFormula
  producedMetalName := "aluminium"
  producedMetalSymbol := "Al"

/-! ## Candidate and specification -/

/-- A proposed simultaneous identification of all three requested outputs. -/
structure Identification where
  metalQ : MetalIdentity
  cAnhydrous : ElementLedger
  cHydrate : HydratedFormula
  dFormula : ElementLedger
  naFConsumedCoefficient : ℕ

/-- The Kimi draft's proposed identification, exposed as a candidate and not
as a premise of the source specification. -/
def proposedIdentification : Identification where
  metalQ := aluminiumIdentity
  cAnhydrous := qFluorideThreeFormula
  cHydrate := ⟨qFluorideThreeFormula, 3⟩
  dFormula := sodiumThreeQFluorideSixFormula
  naFConsumedCoefficient := 3

/-- Primitive, non-exclusive compatibility check for the printed `C -> D`
arrow.  It balances only the candidate's consumed portion of NaF and does not
constrain unused excess reagent, yield, phases, or omitted products. -/
def ConversionCompatible (a : Identification) : Prop :=
  0 < a.naFConsumedCoefficient ∧
  ∀ e : ElementRole,
    ElementLedger.add a.cAnhydrous
        (ElementLedger.scale a.naFConsumedCoefficient sodiumFluorideFormula) e =
      a.dFormula e

/-- The candidate agrees with the independently scoped RSC industrial-use
claim. -/
def IndustrialUseCompatible (a : Identification) : Prop :=
  a.metalQ.name = rscCryoliteAluminiumCitation.producedMetalName ∧
    a.metalQ.atomicWeight.element =
      rscCryoliteAluminiumCitation.producedMetalSymbol ∧
    a.dFormula = rscCryoliteAluminiumCitation.electrolyteFormula

/-- Every decisive printed constraint used for this concrete identification.
The percentages are component mass divided by complete formula mass. -/
def CandidateSatisfiesSource (a : Identification) : Prop :=
  a.cHydrate.core = a.cAnhydrous ∧
  0 < a.cHydrate.waterUnits ∧
  ConversionCompatible a ∧
  0 < molarMass a.metalQ a.dFormula ∧
  0 < molarMass a.metalQ a.cHydrate.totalLedger ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (sodiumMassFraction a.metalQ a.dFormula)
      printedCompositionData.dSodiumFractionShown
      printedCompositionData.dSodiumFractionQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (metalQMassFraction a.metalQ a.dFormula)
      printedCompositionData.dMetalFractionShown
      printedCompositionData.dMetalFractionQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      (hydrateWaterMassFraction a.metalQ a.cHydrate)
      printedCompositionData.hydrateWaterFractionShown
      printedCompositionData.hydrateWaterFractionQuantum ∧
  IndustrialUseCompatible a

/-! ## Requested-output carriers -/

/-- Requested output 1: identity of metal `Q`. -/
def metalQIdentity : MetalIdentity := proposedIdentification.metalQ

/-- Requested output 2: formula of `C * xH2O`. -/
def hydratedCFormula : HydratedFormula := proposedIdentification.cHydrate

/-- Requested output 3: formula of compound `D`. -/
def compoundDFormula : ElementLedger := proposedIdentification.dFormula

/-- Exact symbolic carrier for the metal output. -/
def MetalQOutput : Prop :=
  metalQIdentity.name = "aluminium" ∧
  metalQIdentity.atomicWeight.element = "Al" ∧
  metalQIdentity.atomicWeight.atomicNumber = 13

/-- Exact symbolic carrier for the hydrate output `AlF3 * 3H2O`. -/
def HydratedCOutput : Prop :=
  hydratedCFormula.core = qFluorideThreeFormula ∧
  hydratedCFormula.waterUnits = 3 ∧
  hydratedCFormula.totalLedger = expandedQFluorideThreeTrihydrateFormula

/-- Exact symbolic carrier for the compound-D output `Na3AlF6`. -/
def CompoundDOutput : Prop :=
  compoundDFormula .sodium = 3 ∧
  compoundDFormula .metalQ = 1 ∧
  compoundDFormula .fluorine = 6 ∧
  compoundDFormula .hydrogen = 0 ∧
  compoundDFormula .oxygen = 0

/-- Raw result contract: the proposed simultaneous identification satisfies
all source-derived numerical and qualitative compatibility checks. -/
def RawResult : Prop := CandidateSatisfiesSource proposedIdentification

/-- Reported exact-symbolic result contract, covering the three requested
outputs in source order. -/
def ReportedResult : Prop :=
  RawResult ∧ MetalQOutput ∧ HydratedCOutput ∧ CompoundDOutput

/-- Expand a sum over the five source-bounded element roles.  This local
bridge makes the subsequent exact molar-mass calculations independent of the
implementation details of the derived `Fintype ElementRole` instance. -/
private theorem sum_elementRole (f : ElementRole → ℝ) :
    (∑ e : ElementRole, f e) =
      f .hydrogen + (f .oxygen + (f .fluorine + (f .sodium + f .metalQ))) := by
  have huniv : (Finset.univ : Finset ElementRole) =
      {.hydrogen, .oxygen, .fluorine, .sodium, .metalQ} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp

/-- Once the candidate anhydrous core is fixed, the printed water cell selects
three whole water units rather than inserting `3` as a hypothesis. -/
theorem hydrate_water_units_unique
    {x : ℕ} (hx : 0 < x)
    (hwater :
      IChO2026Chem.Reporting.ConsistentMeasurement
        (hydrateWaterMassFraction aluminiumIdentity
          ⟨qFluorideThreeFormula, x⟩)
        printedCompositionData.hydrateWaterFractionShown
        printedCompositionData.hydrateWaterFractionQuantum) :
    x = 3 := by
  norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
    hydrateWaterMassFraction, hydrateWaterComponentMass,
    HydratedFormula.totalLedger, ElementLedger.add, ElementLedger.scale,
    molarMass, sum_elementRole, roleAtomicWeight, aluminiumIdentity,
    aluminiumAtomicWeight, qFluorideThreeFormula, waterFormula,
    hydrogenAtomicWeight, oxygenAtomicWeight, fluorineAtomicWeight,
    sodiumAtomicWeight, printedCompositionData] at hwater
  have hden :
      0 < (x : ℝ) * 2 * (126 / 125) +
        ((x : ℝ) * (15999 / 1000) + 10497 / 125) := by
    positivity
  rcases abs_le.mp hwater with ⟨hlowerCell, hupperCell⟩
  have hlower :
      (979 / 2500 : ℝ) - 1 / 20000 ≤
        ((x : ℝ) * 2 * (126 / 125) + (x : ℝ) * (15999 / 1000)) /
          ((x : ℝ) * 2 * (126 / 125) +
            ((x : ℝ) * (15999 / 1000) + 10497 / 125)) := by
    linarith
  have hupper :
      ((x : ℝ) * 2 * (126 / 125) + (x : ℝ) * (15999 / 1000)) /
          ((x : ℝ) * 2 * (126 / 125) +
            ((x : ℝ) * (15999 / 1000) + 10497 / 125)) ≤
        (979 / 2500 : ℝ) + 1 / 20000 := by
    linarith
  have hlowerCross := (le_div_iff₀ hden).mp hlower
  have hupperCross := (div_le_iff₀ hden).mp hupper
  have hx_gt_two_real : (2 : ℝ) < x := by
    nlinarith
  have hx_lt_four_real : (x : ℝ) < 4 := by
    nlinarith
  have hx_gt_two : 2 < x := by
    exact_mod_cast hx_gt_two_real
  have hx_lt_four : x < 4 := by
    exact_mod_cast hx_lt_four_real
  omega

/-- The sodium atom ledger selects coefficient three for the candidate
`QF3 + n NaF -> Na3QF6` primitive compatibility equation. -/
theorem sodium_fluoride_coefficient_unique
    {n : ℕ}
    (hledger : ∀ e : ElementRole,
      ElementLedger.add qFluorideThreeFormula
          (ElementLedger.scale n sodiumFluorideFormula) e =
        sodiumThreeQFluorideSixFormula e) :
    n = 3 := by
  have hsodium := hledger ElementRole.sodium
  simpa [ElementLedger.add, ElementLedger.scale, qFluorideThreeFormula,
    sodiumFluorideFormula, sodiumThreeQFluorideSixFormula] using hsodium

/-- Component-accounting carrier for the full hydrate assembly. -/
theorem hydratedC_component_ledger :
    hydratedCFormula.totalLedger = expandedQFluorideThreeTrihydrateFormula := by
  funext e
  cases e <;> rfl

/-- Atom-ledger carrier for the candidate's primitive named transformation. -/
theorem conversion_arrow_atom_ledger : ConversionCompatible proposedIdentification := by
  refine ⟨?_, ?_⟩
  · change 0 < (3 : ℕ)
    norm_num
  intro e
  cases e <;> rfl

/-- The candidate sodium numerator over complete `D` mass lies in the printed
32.85% measurement cell. -/
theorem compoundD_sodium_fraction_check :
    IChO2026Chem.Reporting.ConsistentMeasurement
      (sodiumMassFraction metalQIdentity compoundDFormula)
      printedCompositionData.dSodiumFractionShown
      printedCompositionData.dSodiumFractionQuantum := by
  norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
    sodiumMassFraction, sodiumComponentMass, molarMass, sum_elementRole,
    roleAtomicWeight,
    metalQIdentity, compoundDFormula, proposedIdentification,
    sodiumThreeQFluorideSixFormula, sodiumAtomicWeight, aluminiumIdentity,
    aluminiumAtomicWeight, hydrogenAtomicWeight, oxygenAtomicWeight,
    fluorineAtomicWeight, printedCompositionData]

/-- The candidate metal numerator over complete `D` mass lies in the printed
12.85% measurement cell. -/
theorem compoundD_metal_fraction_check :
    IChO2026Chem.Reporting.ConsistentMeasurement
      (metalQMassFraction metalQIdentity compoundDFormula)
      printedCompositionData.dMetalFractionShown
      printedCompositionData.dMetalFractionQuantum := by
  norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
    metalQMassFraction, metalQComponentMass, molarMass, sum_elementRole,
    roleAtomicWeight,
    metalQIdentity, compoundDFormula, proposedIdentification,
    sodiumThreeQFluorideSixFormula, sodiumAtomicWeight, aluminiumIdentity,
    aluminiumAtomicWeight, hydrogenAtomicWeight, oxygenAtomicWeight,
    fluorineAtomicWeight, printedCompositionData]

/-- The three-water numerator over complete hydrate mass lies in the printed
39.16% measurement cell. -/
theorem hydratedC_water_fraction_check :
    IChO2026Chem.Reporting.ConsistentMeasurement
      (hydrateWaterMassFraction metalQIdentity hydratedCFormula)
      printedCompositionData.hydrateWaterFractionShown
      printedCompositionData.hydrateWaterFractionQuantum := by
  norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
    hydrateWaterMassFraction, hydrateWaterComponentMass,
    HydratedFormula.totalLedger, ElementLedger.add, ElementLedger.scale,
    molarMass, sum_elementRole, roleAtomicWeight, metalQIdentity, hydratedCFormula,
    proposedIdentification, qFluorideThreeFormula, waterFormula,
    sodiumAtomicWeight, aluminiumIdentity, aluminiumAtomicWeight,
    hydrogenAtomicWeight, oxygenAtomicWeight, fluorineAtomicWeight,
    printedCompositionData]

/-- The candidate matches the source-scoped industrial-production clue. -/
theorem industrial_use_compatibility : IndustrialUseCompatible proposedIdentification := by
  exact ⟨rfl, rfl, rfl⟩

/-- Machine-facing raw exact-symbolic result theorem. -/
theorem raw_result : RawResult := by
  refine ⟨rfl, ?_, conversion_arrow_atom_ledger, ?_, ?_,
    compoundD_sodium_fraction_check, compoundD_metal_fraction_check,
    hydratedC_water_fraction_check, industrial_use_compatibility⟩
  · change 0 < (3 : ℕ)
    norm_num
  · simp only [molarMass, sum_elementRole]
    norm_num [roleAtomicWeight, proposedIdentification,
      sodiumThreeQFluorideSixFormula, sodiumAtomicWeight, aluminiumIdentity,
      aluminiumAtomicWeight, hydrogenAtomicWeight, oxygenAtomicWeight,
      fluorineAtomicWeight]
  · simp only [molarMass, sum_elementRole]
    norm_num [roleAtomicWeight, HydratedFormula.totalLedger,
      ElementLedger.add, ElementLedger.scale, proposedIdentification,
      qFluorideThreeFormula, waterFormula, sodiumAtomicWeight,
      aluminiumIdentity, aluminiumAtomicWeight, hydrogenAtomicWeight,
      oxygenAtomicWeight, fluorineAtomicWeight]

/-- Machine-facing reported exact-symbolic result theorem. -/
theorem reported_result : ReportedResult := by
  refine ⟨raw_result, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hydratedC_component_ledger⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end IChO2026Problems.ProblemIChO2026T1A4
