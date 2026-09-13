import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5-A4: molecular formula of `X`

This file derives the T5-A3 fatty-acid prerequisite from the three bound
problem pages and then formalizes both quantitative addition experiments.
The unknown is filtered uniformly from the finite halogen/interhalogen domain
authorized by the pinned `analogous_halogen_addition` contest interpretation.
No premise contains the formula selected by the calculation.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T5A4

noncomputable section

/-! ## Pinned offline-reference provenance -/

def chemistryDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"

def chemistryDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def atomicWeightCRecordSHA256 : String :=
  "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a"
def atomicWeightHRecordSHA256 : String :=
  "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5"
def atomicWeightORecordSHA256 : String :=
  "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588"
def atomicWeightFRecordSHA256 : String :=
  "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb"
def atomicWeightClRecordSHA256 : String :=
  "8f8a36c33295a00c3869eb35edc210319378ef30e7224aa9aea7368d73d287c8"
def atomicWeightBrRecordSHA256 : String :=
  "dbf8e7117c46a2f42658cb13979799052784f339befe8d9e6e45a8b1da93c568"
def atomicWeightIRecordSHA256 : String :=
  "8938a0102ab270e66ebacf9c20e8315c50df879a2baffbcc7c8646b6035b025b"

def analogousHalogenPolicyRecordSHA256 : String :=
  "15887cce8fd742825ce406fccd5cc7a2daeb54d417361a7d7a7423a4313458c5"

/-! ## Formula carriers -/

/-- Atom counts for every element occurring in the two addition stages. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  fluorine : ℕ
  chlorine : ℕ
  bromine : ℕ
  iodine : ℕ
deriving DecidableEq, Repr

namespace MolecularFormula

def add (a b : MolecularFormula) : MolecularFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  oxygen := a.oxygen + b.oxygen
  fluorine := a.fluorine + b.fluorine
  chlorine := a.chlorine + b.chlorine
  bromine := a.bromine + b.bromine
  iodine := a.iodine + b.iodine

def scale (n : ℕ) (a : MolecularFormula) : MolecularFormula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  oxygen := n * a.oxygen
  fluorine := n * a.fluorine
  chlorine := n * a.chlorine
  bromine := n * a.bromine
  iodine := n * a.iodine

end MolecularFormula

/-- An acyclic monocarboxylic fatty acid `C_c H_h O₂` with `u` carbon-carbon
double bonds.  The valence equation is `h + 2u = 2c`. -/
structure FattyAcidModel where
  carbonAtoms : ℕ
  hydrogenAtoms : ℕ
  carbonCarbonDoubleBonds : ℕ
  carbonAtoms_pos : 0 < carbonAtoms
  hydrogenAtoms_pos : 0 < hydrogenAtoms
  acyclicMonocarboxylicValence :
    hydrogenAtoms + 2 * carbonCarbonDoubleBonds = 2 * carbonAtoms

def fattyAcidFormula (acid : FattyAcidModel) : MolecularFormula where
  carbon := acid.carbonAtoms
  hydrogen := acid.hydrogenAtoms
  oxygen := 2
  fluorine := 0
  chlorine := 0
  bromine := 0
  iodine := 0

/-! ## Page-1 component and connectivity recount -/

inductive PL1FragmentKind
  | terminalHydrogen
  | phosphate
  | glycerol
  | acylResidue
deriving DecidableEq, Fintype, Repr

/-- Multiplicities printed below the page-1 PL1 assembly: `n`, 2, 3, and 4. -/
def pl1FragmentMultiplicity (n : ℕ) : PL1FragmentKind → ℕ
  | .terminalHydrogen => n
  | .phosphate => 2
  | .glycerol => 3
  | .acylResidue => 4

/-- Connector degrees visible on fragments a--d: 1, 2, 3, and 1. -/
def pl1FragmentConnectorDegree : PL1FragmentKind → ℕ
  | .terminalHydrogen => 1
  | .phosphate => 2
  | .glycerol => 3
  | .acylResidue => 1

def pl1ConnectorEndCount (n : ℕ) : ℕ := n + 2 * 2 + 3 * 3 + 4

def pl1FragmentCount (n : ℕ) : ℕ := n + 2 + 3 + 4

/-- The source calls cardiolipins acyclic.  For a connected acyclic assembly,
`v - 1` joining bonds consume two connector ends apiece. -/
def PL1AcyclicAssemblyConnectorLedger (n : ℕ) : Prop :=
  pl1ConnectorEndCount n = 2 * (pl1FragmentCount n - 1)

def PL1NoPeroxideLedger (oxygenOxygenBondCount : ℕ) : Prop :=
  oxygenOxygenBondCount = 0

theorem terminalHydrogenFragmentCount_from_image
    {n : ℕ} (h : PL1AcyclicAssemblyConnectorLedger n) : n = 1 := by
  simp only [PL1AcyclicAssemblyConnectorLedger, pl1ConnectorEndCount,
    pl1FragmentCount] at h
  omega

/-- Three glycerol fragments contribute nine carbon atoms and four copies of
the fatty-acid skeleton contribute the remainder. -/
def pl1CarbonAtomCount (acid : FattyAcidModel) : ℕ :=
  3 * 3 + 4 * acid.carbonAtoms

/-- The H inventory is `n + 2 + 3·5 + 4(h-1)`: terminal H, two phosphate
OH hydrogens, three glycerol backbones, and four acyl residues. -/
def pl1HydrogenAtomCount (n : ℕ) (acid : FattyAcidModel) : ℕ :=
  n + 2 + 3 * 5 + 4 * (acid.hydrogenAtoms - 1)

/-- Oxygen inventory `2·2 + 3·3 + 4 = 17`, plus two phosphorus atoms. -/
def pl1OxygenAtomCount : ℕ := 2 * 2 + 3 * 3 + 4
def pl1PhosphorusAtomCount : ℕ := 2

def pl1TotalAtomCount (n : ℕ) (acid : FattyAcidModel) : ℕ :=
  pl1CarbonAtomCount acid + pl1HydrogenAtomCount n acid +
    pl1OxygenAtomCount + pl1PhosphorusAtomCount

/-- A connected acyclic molecular graph with `A` atoms has `A-1` sigma bonds. -/
def pl1SigmaBondCount (n : ℕ) (acid : FattyAcidModel) : ℕ :=
  pl1TotalAtomCount n acid - 1

/-- Two P=O bonds, four acyl C=O bonds, and four copies of the `u` C=C bonds. -/
def pl1PiBondCount (acid : FattyAcidModel) : ℕ :=
  2 + 4 + 4 * acid.carbonCarbonDoubleBonds

def pl1SigmaAndPiBondCount (n : ℕ) (acid : FattyAcidModel) : ℕ :=
  pl1SigmaBondCount n acid + pl1PiBondCount acid

/-! ## Rootless derivation of the T5-A3 prerequisite -/

/-- The page-3 readout contains three product types and states that their
amounts are equal.  Relative amount 1 is merely a normalization; no product
formula or identity is invented. -/
structure ReductiveOzonolysisReadout where
  productTypeCount : ℕ
  productTypeCount_pos : 0 < productTypeCount
  relativeMolarAmount : Fin productTypeCount → ℕ
  relativeMolarAmount_pos : ∀ i, 0 < relativeMolarAmount i
  equimolar : ∀ i j, relativeMolarAmount i = relativeMolarAmount j

def boundOzonolysisReadout : ReductiveOzonolysisReadout where
  productTypeCount := 3
  productTypeCount_pos := by norm_num
  relativeMolarAmount := fun _ => 1
  relativeMolarAmount_pos := by intro i; norm_num
  equimolar := by intro i j; rfl

/-- Ordinary reductive-ozonolysis cleavage ledger for one acyclic chain.

`u` C=C cuts give `u+1` connected organic fragments.  The source gives three
*types* in equal molar amounts; it does not state that each type occurs only
once per acid molecule.  Thus a positive common multiplicity is retained as a
variable and the honest source consequence is `u+1 = 3*m`, not `u+1 = 3`. -/
def ReductiveOzonolysisCleavageLedger
    (acid : FattyAcidModel) (readout : ReductiveOzonolysisReadout)
    (commonProductMultiplicity : ℕ) : Prop :=
  0 < commonProductMultiplicity ∧
    acid.carbonCarbonDoubleBonds + 1 =
      readout.productTypeCount * commonProductMultiplicity

/-- Candidate-independent conjunction of the page-1/page-3 facts used for
T5-A3.  `n`, the O--O count, and the acid are all variables to be filtered. -/
def PreviousPartSourceConstraints
    (n oxygenOxygenBondCount commonProductMultiplicity : ℕ)
    (acid : FattyAcidModel) : Prop :=
  PL1AcyclicAssemblyConnectorLedger n ∧
    PL1NoPeroxideLedger oxygenOxygenBondCount ∧
    ReductiveOzonolysisCleavageLedger acid boundOzonolysisReadout
      commonProductMultiplicity ∧
    pl1SigmaAndPiBondCount n acid = 255

def sourceDerivedFattyAcid : FattyAcidModel where
  carbonAtoms := 18
  hydrogenAtoms := 32
  carbonCarbonDoubleBonds := 2
  carbonAtoms_pos := by norm_num
  hydrogenAtoms_pos := by norm_num
  acyclicMonocarboxylicValence := by norm_num

def sourceDerivedFattyAcidFormula : MolecularFormula where
  carbon := 18
  hydrogen := 32
  oxygen := 2
  fluorine := 0
  chlorine := 0
  bromine := 0
  iodine := 0

theorem sourceDerivedFattyAcid_satisfies_previous_part :
    PreviousPartSourceConstraints 1 0 1 sourceDerivedFattyAcid := by
  norm_num [PreviousPartSourceConstraints, PL1AcyclicAssemblyConnectorLedger,
    PL1NoPeroxideLedger, ReductiveOzonolysisCleavageLedger,
    boundOzonolysisReadout, pl1ConnectorEndCount, pl1FragmentCount,
    pl1SigmaAndPiBondCount, pl1SigmaBondCount, pl1TotalAtomCount,
    pl1CarbonAtomCount, pl1HydrogenAtomCount, pl1OxygenAtomCount,
    pl1PhosphorusAtomCount, pl1PiBondCount, sourceDerivedFattyAcid]

/-! ## Exact activation of the bounded “similar way” interpretation -/

inductive BenchmarkReagentReference
  | elementalIodine
deriving DecidableEq, Repr

inductive ComparisonWording
  | sameWay
  | similarWay
  | analogousWay
deriving DecidableEq, Repr

inductive SubstrateBinding
  | sameRCOOH
  | differentSubstrate
deriving DecidableEq, Repr

inductive RequestedOutputKind
  | molecularFormula
  | scalarAmount
deriving DecidableEq, Repr

inductive QuantitativeContext
  | adductIodineMassFraction
  | qualitativeObservation
deriving DecidableEq, Repr

inductive ProblemOverrideStatus
  | noContraryStatement
  | contraryStatementPresent
deriving DecidableEq, Repr

/-- Typed bindings for every activation cue returned by the pinned
`analogous_halogen_addition` policy. -/
structure AnalogousHalogenSourceCues where
  sourceLocator : String
  benchmarkReagent : BenchmarkReagentReference
  comparisonWording : ComparisonWording
  substrateBinding : SubstrateBinding
  requestedOutput : RequestedOutputKind
  quantitativeContext : QuantitativeContext
  overrideStatus : ProblemOverrideStatus
deriving DecidableEq, Repr

def boundAnalogousHalogenSourceCues : AnalogousHalogenSourceCues where
  sourceLocator := "T5_page-3.png, paragraph immediately preceding box 5.4"
  benchmarkReagent := .elementalIodine
  comparisonWording := .similarWay
  substrateBinding := .sameRCOOH
  requestedOutput := .molecularFormula
  quantitativeContext := .adductIodineMassFraction
  overrideStatus := .noContraryStatement

def AnalogousHalogenPolicyActivation
    (cues : AnalogousHalogenSourceCues) : Prop :=
  cues.sourceLocator =
      "T5_page-3.png, paragraph immediately preceding box 5.4" ∧
    cues.benchmarkReagent = .elementalIodine ∧
    cues.comparisonWording = .similarWay ∧
    cues.substrateBinding = .sameRCOOH ∧
    cues.requestedOutput = .molecularFormula ∧
    cues.quantitativeContext = .adductIodineMassFraction ∧
    cues.overrideStatus = .noContraryStatement

theorem bound_source_activates_analogous_halogen_policy :
    AnalogousHalogenPolicyActivation boundAnalogousHalogenSourceCues := by
  simp [AnalogousHalogenPolicyActivation, boundAnalogousHalogenSourceCues]

inductive HalogenElement
  | fluorine
  | chlorine
  | bromine
  | iodine
deriving DecidableEq, Fintype, Repr

inductive UnsaturatedSiteKind
  | twoCenterUnsaturatedSite
deriving DecidableEq, Repr

inductive AdditionRetention
  | allReagentAddendsRetained
deriving DecidableEq, Repr

inductive PairElementPermission
  | sameOrDifferentElements
deriving DecidableEq, Repr

/-- Exact non-empirical interpretation returned by the policy receipt. -/
structure AnalogousHalogenPolicyInterpretation where
  policyId : String
  datasetVersion : String
  datasetSHA256 : String
  recordSHA256 : String
  authorityKind : String
  reactionTemplateId : String
  ordinaryElementDomain : Finset HalogenElement
  formalCharge : ℤ
  atomsPerReagentMolecule : ℕ
  reagentMoleculesPerSite : ℕ
  addendsDeliveredPerSite : ℕ
  sitesConsumedPerEvent : ℕ
  siteKind : UnsaturatedSiteKind
  retention : AdditionRetention
  pairPermission : PairElementPermission
  requiresAllSourceCues : Bool
  requiresExactProblemTextLocator : Bool
  requiresNoContraryProblemStatement : Bool
  missingOrAmbiguousCueFailsClosed : Bool
  doesNotIdentifySpecificReagent : Bool
  problemWordingOverridesPolicy : Bool
  notUniversalInverseClaim : Bool
  automaticProblemInstantiation : Bool
deriving DecidableEq

def pinnedAnalogousHalogenPolicy : AnalogousHalogenPolicyInterpretation where
  policyId := "analogous_halogen_addition"
  datasetVersion := chemistryDatasetVersion
  datasetSHA256 := chemistryDatasetSHA256
  recordSHA256 := analogousHalogenPolicyRecordSHA256
  authorityKind := "contest_semantics_policy"
  reactionTemplateId := "binary_two_fragment_electrophilic_addition"
  ordinaryElementDomain := Finset.univ
  formalCharge := 0
  atomsPerReagentMolecule := 2
  reagentMoleculesPerSite := 1
  addendsDeliveredPerSite := 2
  sitesConsumedPerEvent := 1
  siteKind := .twoCenterUnsaturatedSite
  retention := .allReagentAddendsRetained
  pairPermission := .sameOrDifferentElements
  requiresAllSourceCues := true
  requiresExactProblemTextLocator := true
  requiresNoContraryProblemStatement := true
  missingOrAmbiguousCueFailsClosed := true
  doesNotIdentifySpecificReagent := true
  problemWordingOverridesPolicy := true
  notUniversalInverseClaim := true
  automaticProblemInstantiation := false

/-- Generic formula over the entire four-element domain returned by the
policy.  It is deliberately not restricted to the eventual answer. -/
structure HalogenReagentFormula where
  fluorineAtoms : ℕ
  chlorineAtoms : ℕ
  bromineAtoms : ℕ
  iodineAtoms : ℕ
  formalCharge : ℤ
deriving DecidableEq, Repr

def HalogenReagentFormula.atomCount (x : HalogenReagentFormula) : ℕ :=
  x.fluorineAtoms + x.chlorineAtoms + x.bromineAtoms + x.iodineAtoms

def HalogenReagentFormula.toMolecularFormula
    (x : HalogenReagentFormula) : MolecularFormula where
  carbon := 0
  hydrogen := 0
  oxygen := 0
  fluorine := x.fluorineAtoms
  chlorine := x.chlorineAtoms
  bromine := x.bromineAtoms
  iodine := x.iodineAtoms

/-- Uniform filter supplied by the activated policy: a neutral, two-atom
halogen/interhalogen formula over F/Cl/Br/I. -/
def PolicyAuthorizedCandidate (x : HalogenReagentFormula) : Prop :=
  x.formalCharge = pinnedAnalogousHalogenPolicy.formalCharge ∧
    x.atomCount = pinnedAnalogousHalogenPolicy.atomsPerReagentMolecule

/-- Auditable binding between the copied policy interpretation and its exact
offline-registry receipt. -/
def PinnedAnalogousHalogenPolicyReceiptMatches : Prop :=
  pinnedAnalogousHalogenPolicy.policyId = "analogous_halogen_addition" ∧
    pinnedAnalogousHalogenPolicy.datasetVersion = chemistryDatasetVersion ∧
    pinnedAnalogousHalogenPolicy.datasetSHA256 = chemistryDatasetSHA256 ∧
    pinnedAnalogousHalogenPolicy.recordSHA256 =
      analogousHalogenPolicyRecordSHA256 ∧
    pinnedAnalogousHalogenPolicy.authorityKind =
      "contest_semantics_policy" ∧
    pinnedAnalogousHalogenPolicy.reactionTemplateId =
      "binary_two_fragment_electrophilic_addition" ∧
    pinnedAnalogousHalogenPolicy.ordinaryElementDomain = Finset.univ ∧
    pinnedAnalogousHalogenPolicy.formalCharge = 0 ∧
    pinnedAnalogousHalogenPolicy.atomsPerReagentMolecule = 2 ∧
    pinnedAnalogousHalogenPolicy.reagentMoleculesPerSite = 1 ∧
    pinnedAnalogousHalogenPolicy.addendsDeliveredPerSite = 2 ∧
    pinnedAnalogousHalogenPolicy.sitesConsumedPerEvent = 1 ∧
    pinnedAnalogousHalogenPolicy.siteKind = .twoCenterUnsaturatedSite ∧
    pinnedAnalogousHalogenPolicy.retention = .allReagentAddendsRetained ∧
    pinnedAnalogousHalogenPolicy.pairPermission = .sameOrDifferentElements ∧
    pinnedAnalogousHalogenPolicy.requiresAllSourceCues = true ∧
    pinnedAnalogousHalogenPolicy.requiresExactProblemTextLocator = true ∧
    pinnedAnalogousHalogenPolicy.requiresNoContraryProblemStatement = true ∧
    pinnedAnalogousHalogenPolicy.missingOrAmbiguousCueFailsClosed = true ∧
    pinnedAnalogousHalogenPolicy.doesNotIdentifySpecificReagent = true ∧
    pinnedAnalogousHalogenPolicy.problemWordingOverridesPolicy = true ∧
    pinnedAnalogousHalogenPolicy.notUniversalInverseClaim = true ∧
    pinnedAnalogousHalogenPolicy.automaticProblemInstantiation = false

theorem pinned_analogous_halogen_policy_receipt_matches :
    PinnedAnalogousHalogenPolicyReceiptMatches := by
  simp [PinnedAnalogousHalogenPolicyReceiptMatches,
    pinnedAnalogousHalogenPolicy]

/-- One linked source-to-domain bridge: exact receipt, every activation cue,
and the uniform formula restriction all have to hold together. -/
def ActivatedPolicyAuthorizedCandidate (x : HalogenReagentFormula) : Prop :=
  PinnedAnalogousHalogenPolicyReceiptMatches ∧
    AnalogousHalogenPolicyActivation boundAnalogousHalogenSourceCues ∧
    PolicyAuthorizedCandidate x

def diiodineFormula : HalogenReagentFormula where
  fluorineAtoms := 0
  chlorineAtoms := 0
  bromineAtoms := 0
  iodineAtoms := 2
  formalCharge := 0

/-- Ordinary elemental iodine in the page-3 benchmark is represented by the
neutral molecular formula I₂.  The cue and every atom count are exposed. -/
def ElementalIodineFormulaBridge : Prop :=
  boundAnalogousHalogenSourceCues.benchmarkReagent = .elementalIodine ∧
    diiodineFormula.fluorineAtoms = 0 ∧
    diiodineFormula.chlorineAtoms = 0 ∧
    diiodineFormula.bromineAtoms = 0 ∧
    diiodineFormula.iodineAtoms = 2 ∧
    diiodineFormula.formalCharge = 0

theorem elemental_iodine_formula_bridge : ElementalIodineFormulaBridge := by
  norm_num [ElementalIodineFormulaBridge, boundAnalogousHalogenSourceCues,
    diiodineFormula]

/-- Candidate named only at the conclusion/witness boundary. -/
def iodineBromideFormula : HalogenReagentFormula where
  fluorineAtoms := 0
  chlorineAtoms := 0
  bromineAtoms := 1
  iodineAtoms := 1
  formalCharge := 0

def iodineBromideMolecularFormula : MolecularFormula :=
  iodineBromideFormula.toMolecularFormula

theorem diiodine_policy_authorized : PolicyAuthorizedCandidate diiodineFormula := by
  norm_num [PolicyAuthorizedCandidate, pinnedAnalogousHalogenPolicy,
    HalogenReagentFormula.atomCount, diiodineFormula]

theorem iodineBromide_policy_authorized :
    PolicyAuthorizedCandidate iodineBromideFormula := by
  norm_num [PolicyAuthorizedCandidate, pinnedAnalogousHalogenPolicy,
    HalogenReagentFormula.atomCount, iodineBromideFormula]

/-! ## Quantitative material stages and conservation carriers -/

inductive StagedTransformationClassification
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  | notStagedTransformation
deriving DecidableEq, Repr

def selectedStageClassification : StagedTransformationClassification :=
  .quantitativeMaterialStage

/-- Conventional central atomic weights, treated as exact olympiad inputs. -/
def atomicWeightC : ℝ := 12.011
def atomicWeightH : ℝ := 1.0080
def atomicWeightO : ℝ := 15.999
def atomicWeightF : ℝ := 18.998
def atomicWeightCl : ℝ := 35.45
def atomicWeightBr : ℝ := 79.904
def atomicWeightI : ℝ := 126.90

/-- Auditable source-to-number bridge for every conventional atomic weight
used in either finite-domain branch calculation. -/
def PinnedAtomicWeightTableReceiptMatches : Prop :=
  chemistryDatasetVersion =
      "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1" ∧
    chemistryDatasetSHA256 =
      "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5" ∧
    atomicWeightCRecordSHA256 =
      "0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a" ∧
    atomicWeightC = 12.011 ∧
    atomicWeightHRecordSHA256 =
      "8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5" ∧
    atomicWeightH = 1.0080 ∧
    atomicWeightORecordSHA256 =
      "d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588" ∧
    atomicWeightO = 15.999 ∧
    atomicWeightFRecordSHA256 =
      "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb" ∧
    atomicWeightF = 18.998 ∧
    atomicWeightClRecordSHA256 =
      "8f8a36c33295a00c3869eb35edc210319378ef30e7224aa9aea7368d73d287c8" ∧
    atomicWeightCl = 35.45 ∧
    atomicWeightBrRecordSHA256 =
      "dbf8e7117c46a2f42658cb13979799052784f339befe8d9e6e45a8b1da93c568" ∧
    atomicWeightBr = 79.904 ∧
    atomicWeightIRecordSHA256 =
      "8938a0102ab270e66ebacf9c20e8315c50df879a2baffbcc7c8646b6035b025b" ∧
    atomicWeightI = 126.90

theorem pinned_atomic_weight_table_receipt_matches :
    PinnedAtomicWeightTableReceiptMatches := by
  norm_num [PinnedAtomicWeightTableReceiptMatches, chemistryDatasetVersion,
    chemistryDatasetSHA256, atomicWeightCRecordSHA256,
    atomicWeightHRecordSHA256, atomicWeightORecordSHA256,
    atomicWeightFRecordSHA256, atomicWeightClRecordSHA256,
    atomicWeightBrRecordSHA256, atomicWeightIRecordSHA256, atomicWeightC,
    atomicWeightH, atomicWeightO, atomicWeightF, atomicWeightCl,
    atomicWeightBr, atomicWeightI]

def molarMass (formula : MolecularFormula) : ℝ :=
  formula.carbon * atomicWeightC +
    formula.hydrogen * atomicWeightH +
    formula.oxygen * atomicWeightO +
    formula.fluorine * atomicWeightF +
    formula.chlorine * atomicWeightCl +
    formula.bromine * atomicWeightBr +
    formula.iodine * atomicWeightI

/-- The policy coefficient is source-independent: it is read from the pinned
policy record and multiplied by the number of unsaturated sites. -/
def policyReagentCoefficient (acid : FattyAcidModel) : ℕ :=
  acid.carbonCarbonDoubleBonds *
    pinnedAnalogousHalogenPolicy.reagentMoleculesPerSite

/-- Formula predicted by the activated contest interpretation: one complete
binary reagent molecule is retained at each C=C site. -/
def additionAdductFormula
    (acid : FattyAcidModel) (x : HalogenReagentFormula) : MolecularFormula :=
  MolecularFormula.add (fattyAcidFormula acid)
    (MolecularFormula.scale (policyReagentCoefficient acid)
      x.toMolecularFormula)

/-- Complete finite species domain actually used by the two calculations. -/
inductive AdditionStageSpecies
  | fattyAcid
  | diiodine
  | iodineAdduct
  | reagentX
  | xAdduct
deriving DecidableEq, Fintype, Repr

def additionStageFormula
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (iodineAdduct xAdduct : MolecularFormula) :
    AdditionStageSpecies → MolecularFormula
  | .fattyAcid => fattyAcidFormula acid
  | .diiodine => diiodineFormula.toMolecularFormula
  | .iodineAdduct => iodineAdduct
  | .reagentX => x.toMolecularFormula
  | .xAdduct => xAdduct

/-- Atom ledger for an arbitrary product carrier.  It is not true by
definition of the product: the ledger constrains that carrier to the complete
retained-addend formula supplied by the activated policy. -/
def AdditionAtomLedger
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (product : MolecularFormula) : Prop :=
  product = additionAdductFormula acid x

/-- Mass ledger obtained from that element-by-element atom ledger. -/
def AdditionMassLedger
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (product : MolecularFormula) : Prop :=
  molarMass product =
    molarMass (fattyAcidFormula acid) +
      policyReagentCoefficient acid * molarMass x.toMolecularFormula

/-- Both the fatty acid and the adduct are neutral.  Charge is included only
because neutrality is an outcome-decisive policy restriction. -/
def AdditionChargeLedger
    (acid : FattyAcidModel) (x : HalogenReagentFormula) : Prop :=
  (policyReagentCoefficient acid : ℤ) * x.formalCharge = 0

theorem addition_mass_ledger_of_atom_ledger
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (product : MolecularFormula)
    (hatom : AdditionAtomLedger acid x product) :
    AdditionMassLedger acid x product := by
  rw [AdditionAtomLedger] at hatom
  subst product
  simp only [AdditionMassLedger, molarMass, additionAdductFormula,
    MolecularFormula.add, MolecularFormula.scale, fattyAcidFormula,
    HalogenReagentFormula.toMolecularFormula, policyReagentCoefficient]
  push_cast
  ring

theorem addition_charge_ledger_of_authorized
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (hx : PolicyAuthorizedCandidate x) : AdditionChargeLedger acid x := by
  rcases hx with ⟨hq, _⟩
  have hq0 : x.formalCharge = 0 := by
    simpa [pinnedAnalogousHalogenPolicy] using hq
  simp [AdditionChargeLedger, hq0]

/-- An activated quantitative addition stage.  Receipt validity and every
problem-text cue authorize the candidate domain and retained-addend ledger;
the atom, mass, and neutral-charge checks are then all explicit. -/
def ActivatedAdditionStage
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (product : MolecularFormula) : Prop :=
  ActivatedPolicyAuthorizedCandidate x ∧
    AdditionAtomLedger acid x product ∧
    AdditionMassLedger acid x product ∧
    AdditionChargeLedger acid x

/-- For a stated acid mass, the iodine-stage reagent mass.  Dividing by acid
molar mass gives the acid amount; the policy coefficient and `M(I₂)` then give
the complete mass of iodine consumed at all C=C sites. -/
def benchmarkIodineMassForFattyAcidMass
    (acidMass : ℝ) (acid : FattyAcidModel) : ℝ :=
  acidMass / molarMass (fattyAcidFormula acid) *
    policyReagentCoefficient acid *
    molarMass diiodineFormula.toMolecularFormula

/-- Numerator of the whole-adduct iodine mass fraction. -/
def adductIodineMass (adduct : MolecularFormula) : ℝ :=
  adduct.iodine * atomicWeightI

/-- Denominator of the whole-adduct iodine mass fraction. -/
def adductTotalMass (adduct : MolecularFormula) : ℝ :=
  molarMass adduct

def adductIodineMassPercent (adduct : MolecularFormula) : ℝ :=
  100 * adductIodineMass adduct / adductTotalMass adduct

def IodineBenchmarkConstraint (acid : FattyAcidModel) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    (benchmarkIodineMassForFattyAcidMass 100 acid) 181.0 0.1

def XAdductIodineFractionConstraint
    (xAdduct : MolecularFormula) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    (adductIodineMassPercent xAdduct) 36.57 0.01

/-- Rootless derivation of the T5-A3 prerequisite using all source data
available before the A4 request.  The ozonolysis multiplicity is not fixed in
advance: the independent iodine-consumption interval is what forces `u = 2`,
after which the structural and bond ledgers force `C18H32O2`. -/
theorem fattyAcidFormula_from_all_bound_source
    {n oxygenOxygenBondCount commonProductMultiplicity : ℕ}
    {acid : FattyAcidModel}
    (hprevious : PreviousPartSourceConstraints n oxygenOxygenBondCount
      commonProductMultiplicity acid)
    (_hatomicWeights : PinnedAtomicWeightTableReceiptMatches)
    (hiodine : IodineBenchmarkConstraint acid) :
    n = 1 ∧
      oxygenOxygenBondCount = 0 ∧
      commonProductMultiplicity = 1 ∧
      acid.carbonCarbonDoubleBonds = 2 ∧
      acid.carbonAtoms = 18 ∧
      acid.hydrogenAtoms = 32 ∧
      fattyAcidFormula acid = sourceDerivedFattyAcidFormula := by
  rcases acid with ⟨c, h, u, hcpos, hhpos, hvalence⟩
  rcases hprevious with ⟨hconnect, hperoxide, hozone, hbonds⟩
  have hn : n = 1 := terminalHydrogenFragmentCount_from_image hconnect
  have hoo : oxygenOxygenBondCount = 0 := hperoxide
  rcases hozone with ⟨hmultiplicityPos, hozoneCount⟩
  have hb := hbonds
  simp only [pl1SigmaAndPiBondCount, pl1SigmaBondCount, pl1TotalAtomCount,
    pl1CarbonAtomCount, pl1HydrogenAtomCount, pl1OxygenAtomCount,
    pl1PhosphorusAtomCount, pl1PiBondCount, hn] at hb
  have hsum : c + h + u = 52 := by omega
  have hmass :
      molarMass (fattyAcidFormula
        { carbonAtoms := c
          hydrogenAtoms := h
          carbonCarbonDoubleBonds := u
          carbonAtoms_pos := hcpos
          hydrogenAtoms_pos := hhpos
          acyclicMonocarboxylicValence := hvalence }) =
        ((825398 : ℝ) + 7979 * (u : ℝ)) / 3000 := by
    simp only [molarMass, fattyAcidFormula, atomicWeightC, atomicWeightH,
      atomicWeightO, atomicWeightF, atomicWeightCl, atomicWeightBr,
      atomicWeightI]
    push_cast
    norm_num
    have hsumR : (c : ℝ) + (h : ℝ) + (u : ℝ) = 52 := by
      exact_mod_cast hsum
    have hvalenceR : (h : ℝ) + 2 * (u : ℝ) = 2 * (c : ℝ) := by
      exact_mod_cast hvalence
    nlinarith
  have hden : 0 < (825398 : ℝ) + 7979 * (u : ℝ) := by positivity
  have hactual :
      benchmarkIodineMassForFattyAcidMass 100
        { carbonAtoms := c
          hydrogenAtoms := h
          carbonCarbonDoubleBonds := u
          carbonAtoms_pos := hcpos
          hydrogenAtoms_pos := hhpos
          acyclicMonocarboxylicValence := hvalence } =
        76140000 * (u : ℝ) / ((825398 : ℝ) + 7979 * (u : ℝ)) := by
    unfold benchmarkIodineMassForFattyAcidMass
    rw [hmass]
    simp only [policyReagentCoefficient, pinnedAnalogousHalogenPolicy, molarMass,
      HalogenReagentFormula.toMolecularFormula, diiodineFormula,
      atomicWeightC, atomicWeightH, atomicWeightO, atomicWeightF,
      atomicWeightCl, atomicWeightBr, atomicWeightI]
    field_simp [ne_of_gt hden] ; ring
  rcases hiodine with ⟨_hquantum, hmeasurement⟩
  have hmeasurementBounds := abs_le.mp hmeasurement
  have hlower :
      (3619 / 20 : ℝ) ≤
        benchmarkIodineMassForFattyAcidMass 100
          { carbonAtoms := c
            hydrogenAtoms := h
            carbonCarbonDoubleBonds := u
            carbonAtoms_pos := hcpos
            hydrogenAtoms_pos := hhpos
            acyclicMonocarboxylicValence := hvalence } := by
    norm_num at hmeasurementBounds ⊢
    linarith [hmeasurementBounds.1]
  have hupper :
      benchmarkIodineMassForFattyAcidMass 100
          { carbonAtoms := c
            hydrogenAtoms := h
            carbonCarbonDoubleBonds := u
            carbonAtoms_pos := hcpos
            hydrogenAtoms_pos := hhpos
            acyclicMonocarboxylicValence := hvalence } ≤
        (3621 / 20 : ℝ) := by
    norm_num at hmeasurementBounds ⊢
    linarith [hmeasurementBounds.2]
  rw [hactual] at hlower hupper
  have hlowerMul := (le_div_iff₀ hden).mp hlower
  have hupperMul := (div_le_iff₀ hden).mp hupper
  have huGtOne : (1 : ℝ) < (u : ℝ) := by
    nlinarith [hlowerMul]
  have huLtThree : (u : ℝ) < (3 : ℝ) := by
    nlinarith [hupperMul]
  have hu : u = 2 := by
    have huGtOneNat : 1 < u := by exact_mod_cast huGtOne
    have huLtThreeNat : u < 3 := by exact_mod_cast huLtThree
    omega
  have hc : c = 18 := by omega
  have hh : h = 32 := by omega
  have hmultiplicity : commonProductMultiplicity = 1 := by
    simp only [boundOzonolysisReadout] at hozoneCount
    omega
  refine ⟨hn, hoo, hmultiplicity, hu, hc, hh, ?_⟩
  simp [fattyAcidFormula, sourceDerivedFattyAcidFormula, hc, hh]

/-- One candidate-independent audit predicate.  It starts from arbitrary
fragment counts, acid, and F/Cl/Br/I formula; then every source observation,
policy restriction, conservation ledger, denominator side condition, and
measurement interval is applied uniformly. -/
def SatisfiesBoundExperiments
    (n oxygenOxygenBondCount commonProductMultiplicity : ℕ)
    (acid : FattyAcidModel) (x : HalogenReagentFormula)
    (iodineAdduct xAdduct : MolecularFormula) : Prop :=
  PreviousPartSourceConstraints n oxygenOxygenBondCount
      commonProductMultiplicity acid ∧
    PinnedAtomicWeightTableReceiptMatches ∧
    ElementalIodineFormulaBridge ∧
    ActivatedAdditionStage acid diiodineFormula iodineAdduct ∧
    ActivatedAdditionStage acid x xAdduct ∧
    0 < molarMass (fattyAcidFormula acid) ∧
    0 < adductTotalMass xAdduct ∧
    IodineBenchmarkConstraint acid ∧
    XAdductIodineFractionConstraint xAdduct

def sourceDerivedIodineAdductFormula : MolecularFormula where
  carbon := 18
  hydrogen := 32
  oxygen := 2
  fluorine := 0
  chlorine := 0
  bromine := 0
  iodine := 4

def sourceDerivedXAdductFormula : MolecularFormula where
  carbon := 18
  hydrogen := 32
  oxygen := 2
  fluorine := 0
  chlorine := 0
  bromine := 2
  iodine := 2

theorem candidate_iodine_adduct_formula_recombination :
    additionAdductFormula sourceDerivedFattyAcid diiodineFormula =
      sourceDerivedIodineAdductFormula := by
  rfl

theorem candidate_x_adduct_formula_recombination :
    additionAdductFormula sourceDerivedFattyAcid iodineBromideFormula =
      sourceDerivedXAdductFormula := by
  rfl

theorem sourceDerivedFattyAcid_molarMass :
    molarMass (fattyAcidFormula sourceDerivedFattyAcid) = 280.452 := by
  norm_num [molarMass, fattyAcidFormula, sourceDerivedFattyAcid,
    atomicWeightC, atomicWeightH, atomicWeightO, atomicWeightF,
    atomicWeightCl, atomicWeightBr, atomicWeightI]

theorem candidate_x_adduct_iodine_mass :
    adductIodineMass sourceDerivedXAdductFormula = 253.8 := by
  norm_num [adductIodineMass, sourceDerivedXAdductFormula, atomicWeightI]

theorem candidate_x_adduct_total_mass :
    adductTotalMass sourceDerivedXAdductFormula = 694.06 := by
  norm_num [adductTotalMass, molarMass, sourceDerivedXAdductFormula,
    atomicWeightC, atomicWeightH, atomicWeightO, atomicWeightF,
    atomicWeightCl, atomicWeightBr, atomicWeightI]

theorem candidate_satisfies_bound_experiments :
    SatisfiesBoundExperiments 1 0 1 sourceDerivedFattyAcid
      iodineBromideFormula sourceDerivedIodineAdductFormula
      sourceDerivedXAdductFormula := by
  have hiAtom : AdditionAtomLedger sourceDerivedFattyAcid diiodineFormula
      sourceDerivedIodineAdductFormula := by rfl
  have hxAtom : AdditionAtomLedger sourceDerivedFattyAcid iodineBromideFormula
      sourceDerivedXAdductFormula := by rfl
  have hiStage : ActivatedAdditionStage sourceDerivedFattyAcid diiodineFormula
      sourceDerivedIodineAdductFormula := by
    exact ⟨⟨pinned_analogous_halogen_policy_receipt_matches,
        bound_source_activates_analogous_halogen_policy,
        diiodine_policy_authorized⟩,
      hiAtom,
      addition_mass_ledger_of_atom_ledger sourceDerivedFattyAcid
        diiodineFormula sourceDerivedIodineAdductFormula hiAtom,
      addition_charge_ledger_of_authorized sourceDerivedFattyAcid
        diiodineFormula diiodine_policy_authorized⟩
  have hxStage : ActivatedAdditionStage sourceDerivedFattyAcid
      iodineBromideFormula sourceDerivedXAdductFormula := by
    exact ⟨⟨pinned_analogous_halogen_policy_receipt_matches,
        bound_source_activates_analogous_halogen_policy,
        iodineBromide_policy_authorized⟩,
      hxAtom,
      addition_mass_ledger_of_atom_ledger sourceDerivedFattyAcid
        iodineBromideFormula sourceDerivedXAdductFormula hxAtom,
      addition_charge_ledger_of_authorized sourceDerivedFattyAcid
        iodineBromideFormula iodineBromide_policy_authorized⟩
  refine ⟨sourceDerivedFattyAcid_satisfies_previous_part,
    pinned_atomic_weight_table_receipt_matches,
    elemental_iodine_formula_bridge, hiStage, hxStage, ?_, ?_, ?_, ?_⟩
  · norm_num [molarMass, fattyAcidFormula, sourceDerivedFattyAcid,
      atomicWeightC, atomicWeightH, atomicWeightO, atomicWeightF,
      atomicWeightCl, atomicWeightBr, atomicWeightI]
  · norm_num [adductTotalMass, molarMass, sourceDerivedXAdductFormula,
      atomicWeightC, atomicWeightH, atomicWeightO,
      atomicWeightF, atomicWeightCl, atomicWeightBr, atomicWeightI]
  · norm_num [IodineBenchmarkConstraint,
      IChO2026Chem.Reporting.ConsistentMeasurement,
      benchmarkIodineMassForFattyAcidMass, policyReagentCoefficient,
      pinnedAnalogousHalogenPolicy, molarMass, fattyAcidFormula,
      HalogenReagentFormula.toMolecularFormula, sourceDerivedFattyAcid,
      diiodineFormula, atomicWeightC, atomicWeightH, atomicWeightO,
      atomicWeightF, atomicWeightCl, atomicWeightBr, atomicWeightI,
      abs_of_nonpos, abs_of_nonneg]
  · norm_num [XAdductIodineFractionConstraint,
      IChO2026Chem.Reporting.ConsistentMeasurement,
      adductIodineMassPercent, adductIodineMass, adductTotalMass,
      molarMass, sourceDerivedXAdductFormula, atomicWeightC,
      atomicWeightH, atomicWeightO, atomicWeightF, atomicWeightCl,
      atomicWeightBr, atomicWeightI, abs_of_nonpos, abs_of_nonneg]

/-! ## Requested exact-symbolic output -/

/-- The candidate satisfies every source constraint, and a uniform audit of
every policy-authorized F/Cl/Br/I two-atom formula leaves exactly the atom
counts F₀Cl₀Br₁I₁. -/
def CompoundXRawResult : Prop :=
  SatisfiesBoundExperiments 1 0 1 sourceDerivedFattyAcid
      iodineBromideFormula sourceDerivedIodineAdductFormula
      sourceDerivedXAdductFormula ∧
    ∀ (n oxygenOxygenBondCount commonProductMultiplicity : ℕ)
        (acid : FattyAcidModel) (x : HalogenReagentFormula)
        (iodineAdduct xAdduct : MolecularFormula),
      SatisfiesBoundExperiments n oxygenOxygenBondCount
          commonProductMultiplicity acid x iodineAdduct xAdduct →
        n = 1 ∧
        oxygenOxygenBondCount = 0 ∧
        commonProductMultiplicity = 1 ∧
        fattyAcidFormula acid = sourceDerivedFattyAcidFormula ∧
        x.fluorineAtoms = 0 ∧
        x.chlorineAtoms = 0 ∧
        x.bromineAtoms = 1 ∧
        x.iodineAtoms = 1 ∧
        x.formalCharge = 0 ∧
        iodineAdduct = sourceDerivedIodineAdductFormula ∧
        xAdduct = sourceDerivedXAdductFormula

/-- Reporting is exact-symbolic: every admissible `X` equals the transparent
formula carrier `iodineBromideFormula`. -/
def CompoundXReportedResult : Prop :=
  SatisfiesBoundExperiments 1 0 1 sourceDerivedFattyAcid
      iodineBromideFormula sourceDerivedIodineAdductFormula
      sourceDerivedXAdductFormula ∧
    ∀ (n oxygenOxygenBondCount commonProductMultiplicity : ℕ)
        (acid : FattyAcidModel) (x : HalogenReagentFormula)
        (iodineAdduct xAdduct : MolecularFormula),
      SatisfiesBoundExperiments n oxygenOxygenBondCount
          commonProductMultiplicity acid x iodineAdduct xAdduct →
        x = iodineBromideFormula

theorem compound_x_raw_result : CompoundXRawResult := by
  refine ⟨candidate_satisfies_bound_experiments, ?_⟩
  intro n oxygenOxygenBondCount commonProductMultiplicity acid x
    iodineAdduct xAdduct hsource
  rcases hsource with
    ⟨hprev, hatomicWeights, _hiodineFormula, hiStage, hxStage, _hacidMassPos,
      _hadductMassPos, hiodineBenchmark, hxFraction⟩
  rcases hiStage with ⟨_hiActivated, hiAtom, _hiMass, _hiCharge⟩
  rcases hxStage with ⟨hactivated, hxAtom, _hxMass, _hxCharge⟩
  rcases hactivated with ⟨_hpolicyReceipt, _hactivation, hpolicy⟩
  rcases fattyAcidFormula_from_all_bound_source hprev hatomicWeights
      hiodineBenchmark with
    ⟨hn, hoo, hmultiplicity, hu, hc, hh, hacidFormula⟩
  rw [AdditionAtomLedger] at hiAtom hxAtom
  rw [hxAtom] at hxFraction
  rcases x with ⟨f, c, b, i, q⟩
  change q = 0 ∧ f + c + b + i = 2 at hpolicy
  rcases hpolicy with ⟨hq, hcount⟩
  have hf_le : f ≤ 2 := by omega
  have hc_le : c ≤ 2 := by omega
  have hb_le : b ≤ 2 := by omega
  have hi_le : i ≤ 2 := by omega
  have hformula :
      f = 0 ∧ c = 0 ∧ b = 1 ∧ i = 1 := by
    interval_cases f <;> interval_cases c <;> interval_cases b <;>
      interval_cases i <;> try omega
    all_goals
      norm_num [XAdductIodineFractionConstraint,
        IChO2026Chem.Reporting.ConsistentMeasurement,
        adductIodineMassPercent, adductIodineMass, adductTotalMass,
        additionAdductFormula, MolecularFormula.add, MolecularFormula.scale,
        policyReagentCoefficient, pinnedAnalogousHalogenPolicy,
        molarMass, fattyAcidFormula,
        HalogenReagentFormula.toMolecularFormula, atomicWeightC,
        atomicWeightH, atomicWeightO, atomicWeightF, atomicWeightCl,
        atomicWeightBr, atomicWeightI, hu, hc, hh, abs_of_nonpos,
        abs_of_nonneg] at hxFraction
  rcases hformula with ⟨hf, hcl, hbr, hi⟩
  have hiProduct : iodineAdduct = sourceDerivedIodineAdductFormula := by
    rw [hiAtom]
    simp [additionAdductFormula, policyReagentCoefficient,
      pinnedAnalogousHalogenPolicy, MolecularFormula.add,
      MolecularFormula.scale, fattyAcidFormula,
      HalogenReagentFormula.toMolecularFormula, diiodineFormula,
      sourceDerivedIodineAdductFormula, hu, hc, hh]
  have hxProduct : xAdduct = sourceDerivedXAdductFormula := by
    rw [hxAtom]
    simp [additionAdductFormula, policyReagentCoefficient,
      pinnedAnalogousHalogenPolicy, MolecularFormula.add,
      MolecularFormula.scale, fattyAcidFormula,
      HalogenReagentFormula.toMolecularFormula,
      sourceDerivedXAdductFormula, hu, hc, hh, hf, hcl, hbr, hi]
  exact ⟨hn, hoo, hmultiplicity, hacidFormula, hf, hcl, hbr, hi, hq,
    hiProduct, hxProduct⟩

theorem compound_x_reported_result : CompoundXReportedResult := by
  rcases compound_x_raw_result with ⟨hsatisfies, hunique⟩
  refine ⟨hsatisfies, ?_⟩
  intro n oxygenOxygenBondCount commonProductMultiplicity acid x
    iodineAdduct xAdduct hsource
  rcases hunique n oxygenOxygenBondCount commonProductMultiplicity acid x
      iodineAdduct xAdduct hsource with
    ⟨_hn, _hoo, _hmultiplicity, _hacid, hf, hcl, hbr, hi, hq,
      _hiProduct, _hxProduct⟩
  cases x with
  | mk f c b i q =>
      simp only at hf hcl hbr hi hq
      subst f
      subst c
      subst b
      subst i
      subst q
      rfl

/- Result-payload-bound declarations are synchronized with
`blind_candidates/icho_2026_t5_a4.json`. -/
theorem compoundXRawResultContract :
    ("2e1de8d2af011c7c581eac394a6937f9fc221cd6b852d26268d3922e4cd93aee" : String) =
      "2e1de8d2af011c7c581eac394a6937f9fc221cd6b852d26268d3922e4cd93aee" ∧
      CompoundXRawResult := by
  exact ⟨rfl, compound_x_raw_result⟩

theorem compoundXReportedResultContract :
    ("ac241a744b4790805468e3345b2265260492f6c3bb063c8dae159d0d0de83cb1" : String) =
      "ac241a744b4790805468e3345b2265260492f6c3bb063c8dae159d0d0de83cb1" ∧
      CompoundXReportedResult := by
  exact ⟨rfl, compound_x_reported_result⟩

end
end ProblemIcho2026T5A4
end IChO2026Problems
