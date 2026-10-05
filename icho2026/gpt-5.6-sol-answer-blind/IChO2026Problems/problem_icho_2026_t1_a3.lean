import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T1, part A3 (measurement-aware contract)

This file formalizes both requested outputs from problem-only evidence.  The
displayed mass-spectral ratio is treated as a measured display: its last-place
quantum is one, so the shared reporting policy gives a half-quantum interval.
The isotope calculation is performed before the positive integral atom-count
constraint is applied.

The identification of `W` is a concrete witness in the finite table printed on
page 2.  The aqueous Fe(III)-phenol bridge is used only in its approved forward
compatibility direction; no colour-implies-phenol inverse or open-world
uniqueness claim is made.  No previous-part answer is used.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T1A3

noncomputable section

/-- Provenance classes allowed by the problem's candidate-domain policy. -/
inductive EvidenceProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The atom counts printed beside each structure in the source table. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- The ten distinct numbered compounds in the source table.  Compound 3 is
shown under three plants, but it is one numbered chemical substance. -/
inductive ExtractableCompound where
  | compound1
  | compound2
  | compound3
  | compound4
  | compound5
  | compound6
  | compound7
  | compound8
  | compound9
  | compound10
  deriving DecidableEq, Fintype, Repr

/-- Formula transcription from `T1_page-2.png`. -/
def molecularFormula : ExtractableCompound → MolecularFormula
  | .compound1 => ⟨11, 14, 3⟩
  | .compound2 => ⟨10, 18, 1⟩
  | .compound3 => ⟨10, 18, 1⟩
  | .compound4 => ⟨6, 12, 1⟩
  | .compound5 => ⟨10, 12, 2⟩
  | .compound6 => ⟨10, 18, 1⟩
  | .compound7 => ⟨14, 16, 0⟩
  | .compound8 => ⟨15, 24, 0⟩
  | .compound9 => ⟨10, 16, 1⟩
  | .compound10 => ⟨10, 18, 1⟩

/-- The response-relevant functionality visible in each complete structure.
These five classes are used only for the closed audit of the pictured table;
they are not asserted to classify arbitrary organic molecules. -/
inductive ResponseRelevantFunctionality where
  | accessiblePhenolicHydroxyl
  | unactivatedAliphaticAlcohol
  | saturatedEther
  | hydrocarbon
  | simpleNonchelatingMonoketone
  deriving DecidableEq, Repr

/-- Visual functional-group transcription from `T1_page-2.png`. -/
def responseRelevantFunctionality :
    ExtractableCompound → ResponseRelevantFunctionality
  | .compound1 => .accessiblePhenolicHydroxyl
  | .compound2 => .unactivatedAliphaticAlcohol
  | .compound3 => .saturatedEther
  | .compound4 => .unactivatedAliphaticAlcohol
  | .compound5 => .accessiblePhenolicHydroxyl
  | .compound6 => .unactivatedAliphaticAlcohol
  | .compound7 => .hydrocarbon
  | .compound8 => .hydrocarbon
  | .compound9 => .simpleNonchelatingMonoketone
  | .compound10 => .simpleNonchelatingMonoketone

/-- Number of structurally accessible phenolic OH groups visible in the
source drawing.  A natural-valued carrier avoids an unconstrained Boolean
test flag. -/
def accessiblePhenolicOHCount : ExtractableCompound → ℕ
  | .compound1 | .compound5 => 1
  | _ => 0

/-- The table-derived candidate domain for an already determined carbon
count.  Its provenance is the finite table in `T1_page-2.png`. -/
def carbonCountCandidateDomain (n : ℕ) : Finset ExtractableCompound :=
  Finset.univ.filter fun c => (molecularFormula c).carbon = n

def carbonCountCandidateDomainProvenance : EvidenceProvenance :=
  .problemImage

/-! ## Carbon-isotope mass-spectrum model -/

/-- Source-stipulated natural abundance of carbon-12, written as an exact
fraction rather than an intermediate decimal approximation. -/
def carbon12Fraction : ℝ := 989 / 1000

/-- Since the source stipulates that carbon has only carbon-12 and carbon-13,
the carbon-13 abundance is derived as the complement. -/
def carbon13Fraction : ℝ := 1 - carbon12Fraction

theorem isotope_abundance_complement :
    carbon13Fraction = 11 / 1000 ∧
      carbon12Fraction + carbon13Fraction = 1 := by
  norm_num [carbon12Fraction, carbon13Fraction]

/-- The observed molecular-ion to M+1 intensity ratio `9 : 1`. -/
def observedMToMPlusOneRatio : ℝ := 9

/-- The displayed ratio is the integer `9`, so its last-place quantum is one. -/
def observedRatioDisplayQuantum : ℝ := 1

/-- Measurement semantics from the source report: the unknown actual ratio is
within half of the last displayed quantum. -/
def ObservedRatioMeasurementSpec (actualRatio : ℝ) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement actualRatio
    observedMToMPlusOneRatio observedRatioDisplayQuantum

/-- Relative abundance of the all-carbon-12 isotopologue for a molecule with
`n` carbon atoms. -/
def molecularIonRelativeIntensity (n : ℕ) : ℝ :=
  carbon12Fraction ^ n

/-- Relative abundance of isotopologues containing exactly one carbon-13.
The factor `n` chooses which carbon atom is carbon-13.  The problem's
monoisotopic assumption for every other element ensures no non-carbon term is
present at M+1. -/
def mPlusOneRelativeIntensity (n : ℕ) : ℝ :=
  (n : ℝ) * carbon13Fraction * carbon12Fraction ^ (n - 1)

/-- Binomial-model prediction of `[M]⁺/[M+1]⁺`. -/
def predictedMToMPlusOneRatio (n : ℕ) : ℝ :=
  molecularIonRelativeIntensity n / mPlusOneRelativeIntensity n

/-- The continuous carbon-count estimate at an arbitrary positive ratio. -/
def rawCarbonCountEstimateAtRatio (ratio : ℝ) : ℝ :=
  carbon12Fraction / (ratio * carbon13Fraction)

/-- The unrounded central estimate obtained from the displayed ratio. -/
def centralRawCarbonCountEstimate : ℝ :=
  rawCarbonCountEstimateAtRatio observedMToMPlusOneRatio

/-- Governing equation obtained after cancelling the common
`abundance(12C)^(n-1)` factor in the two isotopologue intensities. -/
def CarbonCountEquationAtRatio (ratio count : ℝ) : Prop :=
  ratio * count * carbon13Fraction = carbon12Fraction

/-- Exact propagated lower endpoint from actual ratio `19/2`. -/
def propagatedRawCountLower : ℝ := 1978 / 209

/-- Exact propagated upper endpoint from actual ratio `17/2`. -/
def propagatedRawCountUpper : ℝ := 1978 / 187

/-- Source-measurement interval propagated through the exact, unrounded
isotope expression. -/
def RawCarbonEstimateUncertaintySpec : Prop :=
  ∀ actualRatio : ℝ,
    ObservedRatioMeasurementSpec actualRatio →
      propagatedRawCountLower ≤
          rawCarbonCountEstimateAtRatio actualRatio ∧
        rawCarbonCountEstimateAtRatio actualRatio ≤
          propagatedRawCountUpper

/-- For positive carbon count, the full binomial intensity quotient reduces
to the equation used for the continuous estimate. -/
theorem predicted_ratio_formula (n : ℕ) (hn : 0 < n) :
    predictedMToMPlusOneRatio n =
      carbon12Fraction / ((n : ℝ) * carbon13Fraction) := by
  unfold predictedMToMPlusOneRatio molecularIonRelativeIntensity
    mPlusOneRelativeIntensity
  have hpow : carbon12Fraction ^ n =
      carbon12Fraction ^ (n - 1) * carbon12Fraction := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hpow]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hn0r : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  field_simp [carbon12Fraction, carbon13Fraction, hn0r]

/-- The displayed quantum gives the actual-ratio interval `[17/2, 19/2]`. -/
theorem observed_ratio_measurement_interval
    {actualRatio : ℝ} (h : ObservedRatioMeasurementSpec actualRatio) :
    (17 : ℝ) / 2 ≤ actualRatio ∧ actualRatio ≤ (19 : ℝ) / 2 := by
  unfold ObservedRatioMeasurementSpec
    IChO2026Chem.Reporting.ConsistentMeasurement at h
  rcases h with ⟨_, h⟩
  rw [abs_le] at h
  norm_num [observedMToMPlusOneRatio, observedRatioDisplayQuantum] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Exact propagation of the source-derived ratio interval; no tolerance is
chosen after the candidate count is known. -/
theorem raw_carbon_estimate_uncertainty_spec :
    RawCarbonEstimateUncertaintySpec := by
  intro actualRatio hmeasurement
  have hinterval := observed_ratio_measurement_interval hmeasurement
  have hactual : 0 < actualRatio := by nlinarith [hinterval.1]
  have h13 : 0 < carbon13Fraction := by
    norm_num [carbon13Fraction, carbon12Fraction]
  have hden : 0 < actualRatio * carbon13Fraction := mul_pos hactual h13
  constructor
  · unfold propagatedRawCountLower rawCarbonCountEstimateAtRatio
    rw [le_div_iff₀ hden]
    norm_num [carbon12Fraction, carbon13Fraction]
    nlinarith [hinterval.2]
  · unfold propagatedRawCountUpper rawCarbonCountEstimateAtRatio
    rw [div_le_iff₀ hden]
    norm_num [carbon12Fraction, carbon13Fraction]
    nlinarith [hinterval.1]

/-- Exact central arithmetic, kept separate from interval propagation. -/
theorem central_raw_carbon_count_estimate_spec :
    CarbonCountEquationAtRatio observedMToMPlusOneRatio
        centralRawCarbonCountEstimate ∧
      centralRawCarbonCountEstimate = 989 / 99 := by
  norm_num [CarbonCountEquationAtRatio, centralRawCarbonCountEstimate,
    rawCarbonCountEstimateAtRatio, carbon12Fraction, carbon13Fraction,
    observedMToMPlusOneRatio]

/-- A positive integral count is consistent with the displayed mass-spectrum
measurement when its exact binomial prediction lies in the source-derived
measurement interval. -/
def MassSpectrumConsistentCount (n : ℕ) : Prop :=
  0 < n ∧ ObservedRatioMeasurementSpec (predictedMToMPlusOneRatio n)

/-- Candidate output for the requested number of carbon atoms. -/
def derivedCarbonAtomCount : ℕ := 10

/-- The candidate is consistent with the measured display, and the propagated
interval excludes every other positive integral atom count. -/
theorem carbon_atom_count_spec :
    MassSpectrumConsistentCount derivedCarbonAtomCount ∧
      ∀ n : ℕ,
        MassSpectrumConsistentCount n → n = derivedCarbonAtomCount := by
  constructor
  · refine ⟨by norm_num [MassSpectrumConsistentCount, derivedCarbonAtomCount], ?_⟩
    rw [predicted_ratio_formula derivedCarbonAtomCount
      (by norm_num [derivedCarbonAtomCount])]
    norm_num [ObservedRatioMeasurementSpec,
      IChO2026Chem.Reporting.ConsistentMeasurement,
      observedMToMPlusOneRatio, observedRatioDisplayQuantum,
      derivedCarbonAtomCount, carbon12Fraction, carbon13Fraction]
  · intro n hn
    rcases hn with ⟨hnpos, hmeasurement⟩
    have hinterval := observed_ratio_measurement_interval hmeasurement
    rw [predicted_ratio_formula n hnpos] at hinterval
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have h13 : 0 < carbon13Fraction := by
      norm_num [carbon13Fraction, carbon12Fraction]
    have hden : 0 < (n : ℝ) * carbon13Fraction := mul_pos hnr h13
    have hupperCount := (le_div_iff₀ hden).mp hinterval.1
    have hlowerCount := (div_le_iff₀ hden).mp hinterval.2
    have hnltR : (n : ℝ) < 11 := by
      norm_num [carbon12Fraction, carbon13Fraction] at hupperCount
      nlinarith
    have hngtR : (9 : ℝ) < n := by
      norm_num [carbon12Fraction, carbon13Fraction] at hlowerCount
      nlinarith
    have hnlt : n < 11 := by exact_mod_cast hnltR
    have hngt : 9 < n := by exact_mod_cast hngtR
    norm_num [derivedCarbonAtomCount]
    omega

/-- Exact-integer reporting plus the unit-quantum relation for the central
unrounded isotope estimate. -/
def CarbonCountReportingSpec : Prop :=
  derivedCarbonAtomCount = 10 ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      centralRawCarbonCountEstimate 10 1

theorem carbon_count_reporting_spec : CarbonCountReportingSpec := by
  constructor
  · rfl
  · unfold IChO2026Chem.Reporting.ReportsAtQuantum
    refine ⟨by norm_num, ⟨10, by norm_num⟩, ?_⟩
    norm_num [
      centralRawCarbonCountEstimate, rawCarbonCountEstimateAtRatio,
      observedMToMPlusOneRatio, carbon12Fraction, carbon13Fraction]

/-! ## Source-bounded Fe(III) compatibility audit -/

/-- Medium explicitly stated for the qualitative iron(III) test. -/
inductive TestMedium where
  | aqueous
  deriving DecidableEq, Repr

/-- “Characteristic colour change” states a change after addition and is thus
distinct from the initial aqueous Fe(III) solution. -/
inductive TestResponse where
  | characteristicColourChangeAfterAddition
  deriving DecidableEq, Repr

/-- Source observation, kept separate from the unknown molecular identity. -/
structure IronIIITestObservation where
  medium : TestMedium
  availableIronOxidationState : ℕ
  response : TestResponse
  deriving DecidableEq, Repr

def sourceIronIIITest : IronIIITestObservation :=
  ⟨.aqueous, 3, .characteristicColourChangeAfterAddition⟩

/-- Auditable metadata for the approved forward aqueous Fe(III)-phenol rule.
These are data returned by the pinned offline registry, not a locally
postulated chemistry implication. -/
structure EmpiricalRuleReceipt where
  ruleId : String
  claim : String
  applicabilityConditions : List String
  exclusions : List String
  datasetVersion : String
  datasetSHA256 : String
  recordSHA256 : String
  baseDatasetSHA256 : String
  pinnedRuleRecordSHA256 : String
  empiricalRegistryManifestSHA256 : String
  sourceURL : String
  sourceDOI : String
  sourceLocator : String
  sourceContentSHA256 : String
  approvalStatus : String
  authorityKind : String
  automaticProblemInstantiation : Bool
  deriving DecidableEq, Repr

def ferricPhenolForwardRuleReceipt : EmpiricalRuleReceipt where
  ruleId := "aqueous_feiii_phenol_colored_complex"
  claim :=
    "In aqueous media where iron(III) remains available for coordination, \
      an accessible phenolic hydroxy group can form a visibly colored \
      iron(III)-phenol or iron(III)-phenolate complex."
  applicabilityConditions := [
    "The test medium is aqueous and contains available iron(III).",
    "The phenolic hydroxy group is structurally accessible.",
    "The observed colour is distinct from the iron(III) reagent blank."
  ]
  exclusions := [
    "This forward rule is not an unconditional colour-implies-phenol inverse.",
    "A negative result does not exclude every phenol.",
    "Precipitation, incompatible pH, or competing strong ligands are outside scope.",
    "The rule does not identify a particular molecule."
  ]
  datasetVersion :=
    "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+\
      contest-interpretation-v1+trusted-empirical-rules-v1"
  datasetSHA256 :=
    "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
  recordSHA256 :=
    "67fd6f821dcb2c53846e3e084e6a336f170b5dfd9d5fe9584743c4b301f74faf"
  baseDatasetSHA256 :=
    "3f9ac23f3515cf263275c244772de895c5402fb59a12061aa81c65ede91c094f"
  pinnedRuleRecordSHA256 :=
    "6485cda7ae7d9289f5046b238be831dd3fd55e7dc81ae87310390a8f7db68d22"
  empiricalRegistryManifestSHA256 :=
    "801783bce40546c54633e6292f62aee68706a2bc4bd359dda70085321ed49808"
  sourceURL := "https://www.nature.com/articles/1651012b0"
  sourceDOI := "10.1038/1651012b0"
  sourceLocator :=
    "Nature 165 (1950) 1012, complete one-page letter; absorption and \
      titration study of freshly prepared aqueous ferric chloride-phenol \
      coloured complexes."
  sourceContentSHA256 :=
    "b8b2efefde3c552cde5211e865462bef4add50e3422ed45edd0b46554b250aae"
  approvalStatus := "approved"
  authorityKind := "peer_reviewed_literature"
  automaticProblemInstantiation := false

/-- Applicability carrier for the *forward* aqueous Fe(III)-phenol
compatibility rule.  Registry provenance:

* dataset SHA-256
  `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`;
* rule record SHA-256
  `67fd6f821dcb2c53846e3e084e6a336f170b5dfd9d5fe9584743c4b301f74faf`.

This definition says only that a pictured candidate instantiates that known
forward route.  It does not assert the excluded universal inverse “every
colour response implies a phenol”. -/
def FerricPhenolForwardCompatible (c : ExtractableCompound) : Prop :=
  sourceIronIIITest.medium = .aqueous ∧
    sourceIronIIITest.availableIronOxidationState = 3 ∧
    sourceIronIIITest.response =
      .characteristicColourChangeAfterAddition ∧
    0 < accessiblePhenolicOHCount c

/-- A table entry explains both decisive observations when its carbon count
matches the independently derived mass-spectrum count and its complete source
structure instantiates the forward ferric-phenol compatibility route. -/
def SourceBoundedIdentificationWitness
    (n : ℕ) (c : ExtractableCompound) : Prop :=
  carbonCountCandidateDomainProvenance = .problemImage ∧
    c ∈ carbonCountCandidateDomain n ∧
    FerricPhenolForwardCompatible c

/-- Independent enumeration of the domain selected by the ten-carbon mass
spectrum result. -/
theorem carbon_ten_candidate_audit (c : ExtractableCompound) :
    c ∈ carbonCountCandidateDomain 10 ↔
      c = .compound2 ∨ c = .compound3 ∨ c = .compound5 ∨
      c = .compound6 ∨ c = .compound9 ∨ c = .compound10 := by
  cases c <;> decide

/-- Uniform structural-feature audit of every ten-carbon table candidate. -/
def CarbonTenStructuralAuditSpec : Prop :=
  ∀ c : ExtractableCompound,
    c ∈ carbonCountCandidateDomain 10 →
      (0 < accessiblePhenolicOHCount c ↔ c = .compound5)

theorem carbon_ten_structural_audit : CarbonTenStructuralAuditSpec := by
  intro c hc
  cases c <;>
    simp_all [carbonCountCandidateDomain, molecularFormula,
      accessiblePhenolicOHCount]

/-- Candidate output for W: numbered compound 5 in the source table (formula
`C10H12O2`, structurally 4-allyl-2-methoxyphenol). -/
def identifiedW : ExtractableCompound := .compound5

/-- Compound 5 is a concrete evidence-supported witness.  This theorem does
not elevate the forward empirical rule into an inverse or an open-world
uniqueness statement. -/
theorem compound_identity_witness :
    SourceBoundedIdentificationWitness derivedCarbonAtomCount identifiedW ∧
      molecularFormula identifiedW = ⟨10, 12, 2⟩ ∧
      responseRelevantFunctionality identifiedW =
        .accessiblePhenolicHydroxyl := by
  norm_num [SourceBoundedIdentificationWitness,
    carbonCountCandidateDomainProvenance, carbonCountCandidateDomain,
    FerricPhenolForwardCompatible, sourceIronIIITest,
    derivedCarbonAtomCount, identifiedW, molecularFormula,
    accessiblePhenolicOHCount, responseRelevantFunctionality]

/-! ## Mixed raw and reported result contracts -/

/-- Raw numerical derivation, including the source-derived measurement
quantum, propagated interval, and discrete uniqueness step. -/
def CarbonCountRawDerivation : Prop :=
  CarbonCountEquationAtRatio observedMToMPlusOneRatio
      centralRawCarbonCountEstimate ∧
    centralRawCarbonCountEstimate = 989 / 99 ∧
    RawCarbonEstimateUncertaintySpec ∧
    MassSpectrumConsistentCount derivedCarbonAtomCount ∧
    (∀ n : ℕ,
      MassSpectrumConsistentCount n → n = derivedCarbonAtomCount)

/-- Raw identification derivation: a candidate-independent table domain,
uniform structural audit, and concrete forward-compatible witness. -/
def CompoundIdentityRawDerivation : Prop :=
  CarbonTenStructuralAuditSpec ∧
    SourceBoundedIdentificationWitness derivedCarbonAtomCount identifiedW ∧
    molecularFormula identifiedW = ⟨10, 12, 2⟩ ∧
    responseRelevantFunctionality identifiedW =
      .accessiblePhenolicHydroxyl

/-- Problem-specific semantic proposition covering both requested outputs. -/
def RawResult : Prop :=
  CarbonCountRawDerivation ∧ CompoundIdentityRawDerivation

/-- Exact output contract.  The integer and symbolic classification are exact;
the unit-quantum relation records how the unrounded central estimate selects
the integral report. -/
def ReportedResult : Prop :=
  RawResult ∧
    CarbonCountReportingSpec ∧
    derivedCarbonAtomCount = 10 ∧
    identifiedW = .compound5 ∧
    molecularFormula identifiedW = ⟨10, 12, 2⟩

/- The result theorem types are augmented below with target-local payload
hashes after the blind candidate record has been regenerated. -/

/-- Named carrier for the source-derived raw mixed result. -/
theorem raw_result :
    ("919644534bc677da3480e2e255dd69fa0d2b2dbff795d4ef0bab4fa1ccbe7487" :
        String) =
        "919644534bc677da3480e2e255dd69fa0d2b2dbff795d4ef0bab4fa1ccbe7487" ∧
      RawResult := by
  constructor
  · rfl
  · rcases central_raw_carbon_count_estimate_spec with
      ⟨hequation, hcentral⟩
    rcases carbon_atom_count_spec with ⟨hconsistent, hunique⟩
    rcases compound_identity_witness with
      ⟨hwitness, hformula, hfunction⟩
    exact ⟨⟨hequation, hcentral, raw_carbon_estimate_uncertainty_spec,
      hconsistent, hunique⟩,
      ⟨carbon_ten_structural_audit, hwitness, hformula, hfunction⟩⟩

/-- Named carrier for the exact reported mixed result. -/
theorem reported_result :
    ("b6c1743af9cefd9bc4275c8f9cf2c997010317dce677dbec8c884b9fd0825493" :
        String) =
        "b6c1743af9cefd9bc4275c8f9cf2c997010317dce677dbec8c884b9fd0825493" ∧
      ReportedResult := by
  exact ⟨rfl, raw_result.2, carbon_count_reporting_spec, rfl, rfl, rfl⟩

end
end ProblemIcho2026T1A3
end IChO2026Problems
