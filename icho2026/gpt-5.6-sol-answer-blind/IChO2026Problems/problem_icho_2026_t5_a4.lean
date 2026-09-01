import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T5-A4: identification of the analogous halogen reagent

This file is an answer-blind formalization of the data printed on pages T5-1
through T5-3.  The preceding fatty-acid formula is re-derived here rather than
imported from T5-A3.  The final answer is an exact molecular formula, while all
displayed experimental masses and mass fractions are kept as measurement
intervals at their printed quanta.
-/

namespace IChO2026Problems.Icho2026T5A4

noncomputable section

/-! ## Provenance carriers -/

/-- The only provenance classes admitted by this target's source report. -/
inductive EvidenceOrigin where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- A reproducible receipt from the closed offline chemistry registry. -/
structure OfflineReceipt where
  operation : String
  query : String
  recordSHA256 : String
  deriving DecidableEq, Repr

def offlineDatasetVersion : String :=
  "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+" ++
    "contest-interpretation-v1+trusted-empirical-rules-v1"

def offlineDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def fattyAcidMolarMassReceipt : OfflineReceipt :=
  ⟨"molar_mass", "C18H32O2",
    "c00a572bf7289a75e3a77dda888547e4181b1e03c2babf5585b51c37e04c1800"⟩

def iodineMolarMassReceipt : OfflineReceipt :=
  ⟨"molar_mass", "I2",
    "8f6817916aba04d63494f9842ad85e96a902bbf28dbc6ddd6a673a5775240361"⟩

def fluorineAtomicWeightReceipt : OfflineReceipt :=
  ⟨"atomic_weight", "F",
    "96f1d50213dac1410f593d656038a9faa513227e1fd342c16b54096aa2e3b1bb"⟩

def chlorineAtomicWeightReceipt : OfflineReceipt :=
  ⟨"atomic_weight", "Cl",
    "8f8a36c33295a00c3869eb35edc210319378ef30e7224aa9aea7368d73d287c8"⟩

def bromineAtomicWeightReceipt : OfflineReceipt :=
  ⟨"atomic_weight", "Br",
    "dbf8e7117c46a2f42658cb13979799052784f339befe8d9e6e45a8b1da93c568"⟩

def iodineAtomicWeightReceipt : OfflineReceipt :=
  ⟨"atomic_weight", "I",
    "8938a0102ab270e66ebacf9c20e8315c50df879a2baffbcc7c8646b6035b025b"⟩

def binaryAdditionTemplateReceipt : OfflineReceipt :=
  ⟨"reaction_template", "binary_two_fragment_electrophilic_addition",
    "5457da93c91682da2ead97d6600b3de8cca83461005397299519ce11cea80791"⟩

def analogousAdditionPolicyReceipt : OfflineReceipt :=
  ⟨"contest_interpretation", "analogous_halogen_addition",
    "15887cce8fd742825ce406fccd5cc7a2daeb54d417361a7d7a7423a4313458c5"⟩

/-! ## Formulae and the previous-part derivation -/

/-- Atom counts sufficient for every species used in this subproblem. -/
structure MolecularFormula where
  carbon : ℕ := 0
  hydrogen : ℕ := 0
  oxygen : ℕ := 0
  phosphorus : ℕ := 0
  fluorine : ℕ := 0
  chlorine : ℕ := 0
  bromine : ℕ := 0
  iodine : ℕ := 0
  deriving DecidableEq, Repr

/-- Carbon, hydrogen, and C=C-site counts for the acyclic monocarboxylic acid. -/
structure FattyAcidParameters where
  carbon : ℕ
  hydrogen : ℕ
  unsaturationSites : ℕ
  deriving DecidableEq, Repr

/-- Source-image component ledger for non-ionised PL1.

The three glycerol fragments expose nine oxygen attachment ports.  Four ports
attach the four acyl fragments and four attach the two two-port phosphate
fragments.  Because the problem forbids peroxide bonds, the one remaining
glycerol-oxygen port is terminated by the single type-a hydrogen fragment.
-/
structure PL1FragmentLedger where
  terminalHydrogenFragments : ℕ
  phosphateFragments : ℕ
  glycerolFragments : ℕ
  acylFragments : ℕ
  glycerolOxygenPorts : ℕ
  phosphateAttachmentPorts : ℕ
  acylAttachmentPorts : ℕ
  deriving DecidableEq, Repr

def pl1FragmentLedger : PL1FragmentLedger where
  terminalHydrogenFragments := 3 * 3 - (2 * 2 + 4)
  phosphateFragments := 2
  glycerolFragments := 3
  acylFragments := 4
  glycerolOxygenPorts := 3 * 3
  phosphateAttachmentPorts := 2 * 2
  acylAttachmentPorts := 4

/-- Exact visual-port accounting for fragments a--d on T5 page 1. -/
def PL1FragmentLedgerSpec : Prop :=
  pl1FragmentLedger.terminalHydrogenFragments = 1 ∧
  pl1FragmentLedger.phosphateFragments = 2 ∧
  pl1FragmentLedger.glycerolFragments = 3 ∧
  pl1FragmentLedger.acylFragments = 4 ∧
  pl1FragmentLedger.glycerolOxygenPorts =
    pl1FragmentLedger.phosphateAttachmentPorts +
      pl1FragmentLedger.acylAttachmentPorts +
      pl1FragmentLedger.terminalHydrogenFragments

theorem pl1_fragment_ledger_from_image : PL1FragmentLedgerSpec := by
  norm_num [PL1FragmentLedgerSpec, pl1FragmentLedger]

/-- Recombination of the source-image fragments for an acid `C_c H_h O₂`.

Four acyl fragments, three `C₃H₅O₃` glycerol fragments, two `HPO₂`
phosphate fragments, and one terminal H give
`C_(4c+9) H_(4h+14) O₁₇ P₂`.
-/
def pl1Composition (acid : FattyAcidParameters) : MolecularFormula where
  carbon := 4 * acid.carbon + 9
  hydrogen := 4 * acid.hydrogen + 14
  oxygen := 17
  phosphorus := 2

/-- A nontrivial component-by-component recombination check.  The `+ 4` on
the hydrogen ledger records removal of one hydroxyl hydrogen from each of the
four fatty acids when the four acyl fragments are formed. -/
def PL1AssemblyRecombinationSpec (acid : FattyAcidParameters) : Prop :=
  (pl1Composition acid).carbon =
      4 * acid.carbon + 3 * 3 ∧
  (pl1Composition acid).hydrogen + 4 =
      4 * acid.hydrogen + 3 * 5 + 2 * 1 +
        pl1FragmentLedger.terminalHydrogenFragments ∧
  (pl1Composition acid).oxygen = 4 * 1 + 3 * 3 + 2 * 2 ∧
  (pl1Composition acid).phosphorus = 2

theorem pl1_assembly_recombination (acid : FattyAcidParameters) :
    PL1AssemblyRecombinationSpec acid := by
  norm_num [PL1AssemblyRecombinationSpec, pl1Composition, pl1FragmentLedger]

/-- Sum of ordinary bond-order valences.  Carbon, hydrogen, oxygen, and the
depicted `P=O` phosphate phosphorus contribute 4, 1, 2, and 5 respectively.
Twice the number of sigma-plus-pi bonds equals this sum. -/
def bondValenceSum (formula : MolecularFormula) : ℕ :=
  4 * formula.carbon + formula.hydrogen + 2 * formula.oxygen +
    5 * formula.phosphorus

/-- The source states that reductive ozonolysis gives three distinct products
in equimolar (1:1:1) amounts. -/
def ozonolysisRelativeAmount (_ : Fin 3) : ℕ := 1

/-- All problem-side relations used to re-derive T5-A3 inside this target.

For an acyclic monocarboxylic acid with `u` C=C sites,
`H + 2u = 2C`; reductive cleavage produces `u+1` chain fragments; and the
source gives 255 sigma-plus-pi bonds for assembled neutral PL1.
-/
def FattyAcidPrerequisiteSpec (acid : FattyAcidParameters) : Prop :=
  0 < acid.carbon ∧
  acid.unsaturationSites + 1 = 3 ∧
  (∀ j : Fin 3, ozonolysisRelativeAmount j = 1) ∧
  acid.hydrogen + 2 * acid.unsaturationSites = 2 * acid.carbon ∧
  bondValenceSum (pl1Composition acid) = 2 * 255

/-- Candidate obtained by solving the prerequisite equations, not assumed as
a premise of any result theorem. -/
def derivedFattyAcid : FattyAcidParameters where
  carbon := 18
  hydrogen := 32
  unsaturationSites := 2

def derivedFattyAcidFormula : MolecularFormula where
  carbon := derivedFattyAcid.carbon
  hydrogen := derivedFattyAcid.hydrogen
  oxygen := 2

/-- Raw inline derivation and uniqueness specification for the preceding part. -/
def FattyAcidRawDerivation : Prop :=
  FattyAcidPrerequisiteSpec derivedFattyAcid ∧
  ∀ acid : FattyAcidParameters,
    FattyAcidPrerequisiteSpec acid → acid = derivedFattyAcid

theorem fatty_acid_formula_derived_inline : FattyAcidRawDerivation := by
  constructor
  · norm_num [FattyAcidPrerequisiteSpec, derivedFattyAcid,
      ozonolysisRelativeAmount, bondValenceSum, pl1Composition]
  · rintro ⟨carbon, hydrogen, unsaturationSites⟩ hspec
    dsimp [FattyAcidPrerequisiteSpec] at hspec
    rcases hspec with ⟨_, hsites, _, hhydrogen, hbonds⟩
    dsimp [bondValenceSum, pl1Composition] at hbonds
    have hsites' : unsaturationSites = 2 := by omega
    have hcarbon : carbon = 18 := by omega
    have hhydrogen' : hydrogen = 32 := by omega
    subst unsaturationSites
    subst carbon
    subst hydrogen
    rfl

/-- The recombined PL1 composition at the derived acid counts. -/
def derivedPL1Formula : MolecularFormula where
  carbon := 81
  hydrogen := 142
  oxygen := 17
  phosphorus := 2

def DerivedPL1BondAudit : Prop :=
  pl1Composition derivedFattyAcid = derivedPL1Formula ∧
  bondValenceSum derivedPL1Formula = 510

theorem derived_pl1_bond_audit : DerivedPL1BondAudit := by
  norm_num [DerivedPL1BondAudit, derivedPL1Formula, pl1Composition,
    derivedFattyAcid, bondValenceSum]

/-! ## Benchmark iodine uptake and analogous-addition policy -/

/-- Exact conventional molar masses (g mol⁻¹) from the pinned registry. -/
def fattyAcidMolarMass : ℝ := 280452 / 1000
def iodineAtomicWeight : ℝ := 12690 / 100
def iodineMolarMass : ℝ := 2538 / 10

/-- Problem-side mass basis and displayed iodine uptake (grams). -/
def sourceFattyAcidMass : ℝ := 100
def sourceIodineUptake : ℝ := 1810 / 10
def sourceIodineUptakeQuantum : ℝ := 1 / 10

def predictedIodineUptake : ℝ :=
  sourceFattyAcidMass / fattyAcidMolarMass *
    (derivedFattyAcid.unsaturationSites : ℝ) * iodineMolarMass

/-- The two-site prerequisite prediction lies in the half-last-place interval
represented by the printed 181.0 g uptake. -/
def IodineUptakeCalculationSpec : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
    predictedIodineUptake sourceIodineUptake sourceIodineUptakeQuantum

theorem iodine_uptake_calculation : IodineUptakeCalculationSpec := by
  norm_num [IodineUptakeCalculationSpec,
    IChO2026Chem.Reporting.ConsistentMeasurement, predictedIodineUptake,
    sourceFattyAcidMass, fattyAcidMolarMass, derivedFattyAcid,
    iodineMolarMass, sourceIodineUptake, sourceIodineUptakeQuantum]

/-- The five controller-authorized source cues for interpreting “reacts in
similar way” as analogous halogen addition on the same two C=C sites. -/
inductive AnalogousAdditionCue where
  | iodineBenchmark
  | similarWayWording
  | sameUnsaturatedFattyAcid
  | quantitativeAdductFraction
  | unknownMolecularFormulaRequested
  deriving DecidableEq, Fintype, Repr

def sourceAnalogousAdditionCues : Finset AnalogousAdditionCue := Finset.univ

def AnalogousAdditionCueSpec : Prop :=
  ∀ cue : AnalogousAdditionCue, cue ∈ sourceAnalogousAdditionCues

theorem analogous_addition_source_cues : AnalogousAdditionCueSpec := by
  intro cue
  simp [sourceAnalogousAdditionCues]

/-! ## Closed, policy-bounded identification of X -/

/-- Ordinary olympiad halogen domain returned by the pinned contest policy. -/
inductive Halogen where
  | F
  | Cl
  | Br
  | I
  deriving DecidableEq, Fintype, Repr

def atomicWeight : Halogen → ℝ
  | .F => 18998 / 1000
  | .Cl => 3545 / 100
  | .Br => 79904 / 1000
  | .I => iodineAtomicWeight

def halogenMultiplicity (target actual : Halogen) : ℕ :=
  if actual = target then 1 else 0

def formulaOfHalogenPair (pair : Halogen × Halogen) : MolecularFormula where
  fluorine :=
    halogenMultiplicity .F pair.1 + halogenMultiplicity .F pair.2
  chlorine :=
    halogenMultiplicity .Cl pair.1 + halogenMultiplicity .Cl pair.2
  bromine :=
    halogenMultiplicity .Br pair.1 + halogenMultiplicity .Br pair.2
  iodine :=
    halogenMultiplicity .I pair.1 + halogenMultiplicity .I pair.2

/-- Candidate-independent finite domain: all neutral diatomic halogens and
interhalogens over F, Cl, Br, and I.  Ordered pairs are retained, while
uniqueness is proved at the molecular-formula level. -/
def halogenPairCandidateDomain : Finset (Halogen × Halogen) := Finset.univ

def halogenPairCandidateDomainOrigin : EvidenceOrigin :=
  .trustedGeneralLaw

def HalogenPairCandidateDomainSpec : Prop :=
  ∀ pair : Halogen × Halogen, pair ∈ halogenPairCandidateDomain

theorem halogen_pair_candidate_domain_complete :
    HalogenPairCandidateDomainSpec := by
  intro pair
  simp [halogenPairCandidateDomain]

def iodineAtomCount (pair : Halogen × Halogen) : ℕ :=
  halogenMultiplicity .I pair.1 + halogenMultiplicity .I pair.2

/-- The analogous policy and binary-addition template deliver one reagent
molecule per C=C site and retain both reagent atoms in the adduct. -/
def analogousReagentMoleculesPerAcid : ℕ :=
  derivedFattyAcid.unsaturationSites

def adductMolarMass (pair : Halogen × Halogen) : ℝ :=
  fattyAcidMolarMass + (analogousReagentMoleculesPerAcid : ℝ) *
    (atomicWeight pair.1 + atomicWeight pair.2)

def iodineMassInAdduct (pair : Halogen × Halogen) : ℝ :=
  (analogousReagentMoleculesPerAcid : ℝ) *
    (iodineAtomCount pair : ℝ) * iodineAtomicWeight

def predictedAdductIodineFraction (pair : Halogen × Halogen) : ℝ :=
  iodineMassInAdduct pair / adductMolarMass pair

/-- 36.57% as a mass fraction, with a 0.01%-point displayed quantum. -/
def sourceAdductIodineFraction : ℝ := 3657 / 10000
def sourceAdductIodineFractionQuantum : ℝ := 1 / 10000

def PairMatchesAdductMeasurement (pair : Halogen × Halogen) : Prop :=
  0 < adductMolarMass pair ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
    (predictedAdductIodineFraction pair)
    sourceAdductIodineFraction
    sourceAdductIodineFractionQuantum

/-- The concrete source-derived candidate pair.  It is not a premise: the raw
result below proves both its fit and uniform uniqueness over the independently
constructed domain. -/
def compoundXCandidatePair : Halogen × Halogen := (.I, .Br)

def compoundXFormula : MolecularFormula :=
  formulaOfHalogenPair compoundXCandidatePair

def iodineBromideFormula : MolecularFormula where
  bromine := 1
  iodine := 1

/-- Raw exact calculation and uniform finite-domain identification contract. -/
def CompoundXRawResult : Prop :=
  compoundXCandidatePair ∈ halogenPairCandidateDomain ∧
  iodineMassInAdduct compoundXCandidatePair = 1269 / 5 ∧
  adductMolarMass compoundXCandidatePair = 34703 / 50 ∧
  predictedAdductIodineFraction compoundXCandidatePair = 12690 / 34703 ∧
  PairMatchesAdductMeasurement compoundXCandidatePair ∧
  formulaOfHalogenPair compoundXCandidatePair = compoundXFormula ∧
  (∀ pair : Halogen × Halogen,
    pair ∈ halogenPairCandidateDomain →
    PairMatchesAdductMeasurement pair →
    formulaOfHalogenPair pair = compoundXFormula)

/-- Exact-symbolic reporting preserves the raw identification and exposes the
requested molecular formula without a numeric rounding boundary. -/
def CompoundXReportedResult : Prop :=
  CompoundXRawResult ∧ compoundXFormula = iodineBromideFormula

/-- Raw answer-blind result contract for `compound_x_formula`. -/
theorem compound_x_formula_raw : CompoundXRawResult := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [compoundXCandidatePair, halogenPairCandidateDomain]
  · norm_num [iodineMassInAdduct, analogousReagentMoleculesPerAcid,
      derivedFattyAcid, iodineAtomCount, compoundXCandidatePair,
      halogenMultiplicity, iodineAtomicWeight]
  · norm_num [adductMolarMass, fattyAcidMolarMass,
      analogousReagentMoleculesPerAcid, derivedFattyAcid,
      compoundXCandidatePair, atomicWeight, iodineAtomicWeight]
  · norm_num [predictedAdductIodineFraction, iodineMassInAdduct,
      adductMolarMass, fattyAcidMolarMass, analogousReagentMoleculesPerAcid,
      derivedFattyAcid, iodineAtomCount, compoundXCandidatePair,
      halogenMultiplicity, atomicWeight, iodineAtomicWeight]
  · norm_num [PairMatchesAdductMeasurement,
      IChO2026Chem.Reporting.ConsistentMeasurement,
      predictedAdductIodineFraction, iodineMassInAdduct, adductMolarMass,
      fattyAcidMolarMass, analogousReagentMoleculesPerAcid, derivedFattyAcid,
      iodineAtomCount, compoundXCandidatePair, halogenMultiplicity,
      atomicWeight, iodineAtomicWeight, sourceAdductIodineFraction,
      sourceAdductIodineFractionQuantum]
  · rfl
  · rintro ⟨first, second⟩ _ hmatch
    cases first <;> cases second <;>
      norm_num [PairMatchesAdductMeasurement,
        IChO2026Chem.Reporting.ConsistentMeasurement,
        predictedAdductIodineFraction, iodineMassInAdduct, adductMolarMass,
        fattyAcidMolarMass, analogousReagentMoleculesPerAcid,
        derivedFattyAcid, iodineAtomCount, halogenMultiplicity, atomicWeight,
        iodineAtomicWeight, sourceAdductIodineFraction,
        sourceAdductIodineFractionQuantum, formulaOfHalogenPair,
        compoundXFormula, compoundXCandidatePair] at hmatch
    all_goals
      simp [formulaOfHalogenPair, halogenMultiplicity, compoundXFormula,
        compoundXCandidatePair]

/-- Reported answer-blind result contract for `compound_x_formula`. -/
theorem compound_x_formula_reported : CompoundXReportedResult := by
  refine ⟨compound_x_formula_raw, ?_⟩
  rfl

end

end IChO2026Problems.Icho2026T5A4
