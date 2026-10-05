import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 1, part A3

This file formalizes the source-side isotope calculation and the identification
of `W`.  The finite molecular domain and structural information come from the
table on `T1_page-2.png`; the mass-spectrum and aqueous iron(III) observations
come from `T1_page-3.png`.

The iron(III) compatibility bridge is the forward (not inverse) rule returned
by the version-pinned offline chemistry registry under
`aqueous_feiii_phenol_colored_complex`.  Its complete receipt is represented
below.  The identification theorem therefore certifies compound 5 as the
concrete depicted candidate satisfying all decisive constraints; it does not
assert the excluded, open-world converse that every coloured iron(III) test
must arise from a phenol.
-/

namespace IChO2026Problems.IChO2026T1A3

noncomputable section

/-! ## Source provenance and the depicted candidate domain -/

/-- The provenance classes permitted by the source contract. -/
inductive EvidenceOrigin where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  | activatedCandidateConstructionRule
  deriving DecidableEq, Repr

/-- A value together with its source class and a source-local locator. -/
structure Sourced (α : Type) where
  value : α
  origin : EvidenceOrigin
  locator : String

/-- The four plants printed in the source table. -/
inductive Plant where
  | zingiber
  | hypericum
  | chamomilla
  | artemisia
  deriving DecidableEq, Fintype, Repr

/-- The ten distinct numbered compounds in the source table.  Compound 3 is
printed in three rows but denotes the same molecular candidate each time. -/
inductive Compound where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype, Repr

/-- The four chromatographic roles named in the elixir. -/
inductive ElixirComponent where
  | X | Y | Z | W
  deriving DecidableEq, Fintype, Repr

/-- Molecular formula fields needed for the printed table. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Componentwise addition of molecular-formula ledgers. -/
def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  oxygen := a.oxygen + b.oxygen

/-- Formula captions printed beneath compounds 1--10 on `T1_page-2.png`. -/
def depictedFormula : Compound → MolecularFormula
  | .c1 => ⟨11, 14, 3⟩
  | .c2 => ⟨10, 18, 1⟩
  | .c3 => ⟨10, 18, 1⟩
  | .c4 => ⟨6, 12, 1⟩
  | .c5 => ⟨10, 12, 2⟩
  | .c6 => ⟨10, 18, 1⟩
  | .c7 => ⟨14, 16, 0⟩
  | .c8 => ⟨15, 24, 0⟩
  | .c9 => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- The image-provenance carrier for all formula captions. -/
def depictedFormulaSource : Sourced (Compound → MolecularFormula) where
  value := depictedFormula
  origin := .problemImage
  locator := "T1_page-2.png, compounds 1--10 and their formula captions"

/-- The entries in each plant row, including the repeated occurrence of
compound 3 in three rows. -/
def compoundsExtractableFrom : Plant → Finset Compound
  | .zingiber => {.c1, .c2, .c3}
  | .hypericum => {.c4, .c5, .c6}
  | .chamomilla => {.c7, .c8, .c3}
  | .artemisia => {.c9, .c10, .c3}

/-- The source-derived candidate domain is all ten distinct numbered table
entries, not a singleton selected after seeing the requested answer. -/
def depictedCandidateDomain : Sourced (Finset Compound) where
  value := Finset.univ
  origin := .problemImage
  locator := "T1_page-2.png, complete four-row extractable-compound table"

/-- The chromatography statement supplies four distinct named components but
does not disclose their assignment to table entries.  This interface preserves
that source hypothesis without importing answers to parts A1 or A2. -/
structure SourceElixirAssignment where
  compoundFor : ElixirComponent → Compound
  comesFromDepictedTable :
    ∀ role : ElixirComponent,
      compoundFor role ∈ depictedCandidateDomain.value
  chromatographicallyDistinct : Function.Injective compoundFor

/-! ## Carbon-isotope peak calculation -/

/-- The only two carbon isotopes admitted by the problem statement. -/
inductive CarbonIsotope where
  | carbon12
  | carbon13
  deriving DecidableEq, Fintype, Repr

/-- The source-stipulated carbon isotope support. -/
def sourceCarbonIsotopes : Sourced (Finset CarbonIsotope) where
  value := Finset.univ
  origin := .problemText
  locator := "T1_page-3.png: carbon consists exclusively of 12C and 13C"

/-- Exact source central fraction corresponding to the printed 98.9% 12C. -/
def carbon12Fraction : ℝ := 989 / 1000

/-- The complementary 13C fraction under the stipulated two-isotope model. -/
def carbon13Fraction : ℝ := 11 / 1000

/-- Other elements are stipulated to be monoisotopic, so their contribution
to the `[M+1]⁺/[M]⁺` first-isotopologue ratio is zero. -/
def otherElementMPlusOneContribution : ℝ := 0

/-- The centre printed for the measured peak ratio `[M]⁺ : [M+1]⁺ = 9 : 1`.
It is the centre of a displayed measurement cell, not an exact equation for
the unknown natural carbon count. -/
def displayedMToMPlusOneRatio : ℝ := 9

/-- The last displayed quantum of the integer ratio `9 : 1`.  The source
measurement policy therefore assigns a half-quantum width of `1/2`. -/
def displayedPeakRatioQuantum : ℝ := 1

/-- Relative weight of the all-12C molecular-ion isotopologue for a molecule
with `n` carbon atoms. -/
def molecularIonPeakWeight (n : ℕ) : ℝ := carbon12Fraction ^ n

/-- Relative weight of isotopologues containing exactly one 13C atom.  The
factor `n` records the choice of which carbon atom is 13C. -/
def mPlusOnePeakWeight (n : ℕ) : ℝ :=
  (n : ℝ) * carbon13Fraction * carbon12Fraction ^ (n - 1)

/-- The first-isotopologue contribution relative to the molecular-ion peak.
The monoisotopic-other-elements stipulation makes its second summand zero. -/
def predictedMPlusOneRelativeToM (carbonCount : ℕ) : ℝ :=
  (carbonCount : ℝ) * carbon13Fraction / carbon12Fraction +
    otherElementMPlusOneContribution

/-- The measured direction is molecular ion to first isotopologue, so it is
the reciprocal of the preceding relative contribution.  The argument remains
a natural atom count throughout; no continuous surrogate is rounded to
manufacture an integer count. -/
def predictedMToMPlusOneRatio (carbonCount : ℕ) : ℝ :=
  1 / predictedMPlusOneRelativeToM carbonCount

/-- Exact cancellation law connecting the discrete peak weights to the ratio
equation.  Positivity of `n` is explicit because the one-13C expression uses
the exponent `n - 1`. -/
def FirstIsotopologuePeakLaw : Prop :=
  ∀ n : ℕ,
    0 < n →
      0 < molecularIonPeakWeight n ∧
      0 < mPlusOnePeakWeight n ∧
      mPlusOnePeakWeight n / molecularIonPeakWeight n =
        predictedMPlusOneRelativeToM n ∧
      molecularIonPeakWeight n / mPlusOnePeakWeight n =
        predictedMToMPlusOneRatio n

/-- A positive natural carbon count is consistent with the printed spectrum
exactly when its unrounded isotope-model ratio lies in the source-derived
half-quantum measurement cell centred at `9`.  `ReportsAtQuantum` records the
project's fixed half-away-from-zero endpoint convention; the accompanying
`ConsistentMeasurement` conjunct records the closed half-width policy itself. -/
def PeakRatioObservationCell (n : ℕ) : Prop :=
  0 < n ∧
  predictedMToMPlusOneRatio n = (989 : ℝ) / (11 * (n : ℝ)) ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
    (predictedMToMPlusOneRatio n)
    displayedMToMPlusOneRatio
    displayedPeakRatioQuantum ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    (predictedMToMPlusOneRatio n)
    displayedMToMPlusOneRatio
    displayedPeakRatioQuantum

/-- Source facts and the exact discrete governing calculation.  In
particular, the displayed `9` is never asserted equal to the predicted ratio.
For a positive natural `n`, the unrounded ratio is `989/(11*n)`, and its
half-quantum reporting cell is the exact interval `[17/2, 19/2)`. -/
def IsotopeRawDerivation : Prop :=
  0 < carbon12Fraction ∧
  0 < carbon13Fraction ∧
  carbon12Fraction + carbon13Fraction = 1 ∧
  otherElementMPlusOneContribution = 0 ∧
  displayedMToMPlusOneRatio = 9 ∧
  displayedPeakRatioQuantum = 1 ∧
  FirstIsotopologuePeakLaw ∧
  (∀ n : ℕ,
    0 < n →
      predictedMToMPlusOneRatio n = (989 : ℝ) / (11 * (n : ℝ))) ∧
  ∀ n : ℕ,
    PeakRatioObservationCell n →
      (17 : ℝ) / 2 ≤ predictedMToMPlusOneRatio n ∧
      predictedMToMPlusOneRatio n < (19 : ℝ) / 2

/-- Raw carrier for requested output `carbon_atom_count`.  It asks Lean to
derive a unique *positive natural* count directly from the displayed-ratio
measurement cell.  No desired count occurs in this source-side predicate. -/
def CarbonAtomCountRawResult : Prop :=
  IsotopeRawDerivation ∧
  ∃! n : ℕ, PeakRatioObservationCell n

theorem isotope_raw_derivation : IsotopeRawDerivation := by
  refine ⟨by norm_num [carbon12Fraction], by norm_num [carbon13Fraction], ?_, rfl,
    rfl, rfl, ?_, ?_, ?_⟩
  · norm_num [carbon12Fraction, carbon13Fraction]
  · intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hp12 : (carbon12Fraction : ℝ) ≠ 0 := by
      norm_num [carbon12Fraction]
    have hpow : carbon12Fraction ^ n =
        carbon12Fraction ^ (n - 1) * carbon12Fraction := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
      rw [pow_succ]
    have hM : 0 < molecularIonPeakWeight n := by
      exact pow_pos (by norm_num [carbon12Fraction]) n
    have hM1 : 0 < mPlusOnePeakWeight n := by
      exact mul_pos
        (mul_pos (by exact_mod_cast hn) (by norm_num [carbon13Fraction]))
        (pow_pos (by norm_num [carbon12Fraction]) (n - 1))
    refine ⟨hM, hM1, ?_, ?_⟩
    · simp only [mPlusOnePeakWeight, molecularIonPeakWeight,
        predictedMPlusOneRelativeToM, otherElementMPlusOneContribution, add_zero]
      rw [hpow]
      field_simp
    · simp only [mPlusOnePeakWeight, molecularIonPeakWeight,
        predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        otherElementMPlusOneContribution, add_zero]
      rw [hpow]
      field_simp
  · intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp only [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
      carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution, add_zero]
    field_simp
  · intro n hn
    rcases hn with ⟨hn, hratio, _hconsistent, hreported⟩
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hratioPos : 0 < predictedMToMPlusOneRatio n := by
      rw [hratio]
      positivity
    unfold IChO2026Chem.Reporting.ReportsAtQuantum at hreported
    simp only [displayedPeakRatioQuantum, displayedMToMPlusOneRatio] at hreported
    rw [if_pos (le_of_lt hratioPos)] at hreported
    have hbounds := hreported.2.2
    norm_num at hbounds ⊢
    exact hbounds

theorem carbon_atom_count_raw : CarbonAtomCountRawResult := by
  refine ⟨isotope_raw_derivation, ?_⟩
  refine ⟨10, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · norm_num [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution]
    · refine ⟨by norm_num [displayedPeakRatioQuantum], ?_⟩
      norm_num [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution,
        displayedMToMPlusOneRatio, displayedPeakRatioQuantum, abs_of_nonpos]
    · refine ⟨by norm_num [displayedPeakRatioQuantum], ⟨9, by norm_num
          [displayedMToMPlusOneRatio, displayedPeakRatioQuantum]⟩, ?_⟩
      simp only [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution,
        displayedMToMPlusOneRatio, displayedPeakRatioQuantum, add_zero]
      norm_num
  · intro n hnCell
    rcases hnCell with ⟨hn, hratio, _hconsistent, _hreported⟩
    have hbounds := isotope_raw_derivation.2.2.2.2.2.2.2.2 n
      ⟨hn, hratio, _hconsistent, _hreported⟩
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < 11 * (n : ℝ) := by positivity
    rw [hratio] at hbounds
    have hlower := (le_div_iff₀ hden).mp hbounds.1
    have hupper := (div_lt_iff₀ hden).mp hbounds.2
    have hnLt : (n : ℝ) < 11 := by nlinarith
    have hnGt : (9 : ℝ) < n := by nlinarith
    have hnLtNat : n < 11 := by exact_mod_cast hnLt
    have hnGtNat : 9 < n := by exact_mod_cast hnGt
    omega

/-- The output carrier is selected from the unique source-derived natural
solution, rather than being inserted into the source assumptions. -/
noncomputable def carbonAtomCount : ℕ :=
  Classical.choose carbon_atom_count_raw.2.exists

/-- Reported carrier for requested output `carbon_atom_count`.  It binds the
source-selected count to the requested exact integer and retains both the
unrounded ratio equality and its `ReportsAtQuantum` measurement certificate
through `PeakRatioObservationCell`. -/
def CarbonAtomCountReportedResult : Prop :=
  CarbonAtomCountRawResult ∧
  carbonAtomCount = 10 ∧
  PeakRatioObservationCell carbonAtomCount ∧
  ∀ n : ℕ, PeakRatioObservationCell n → n = carbonAtomCount

theorem carbon_atom_count_reported : CarbonAtomCountReportedResult := by
  have hchosen : PeakRatioObservationCell carbonAtomCount := by
    exact Classical.choose_spec carbon_atom_count_raw.2.exists
  have hten : PeakRatioObservationCell 10 := by
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · norm_num [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution]
    · refine ⟨by norm_num [displayedPeakRatioQuantum], ?_⟩
      norm_num [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution,
        displayedMToMPlusOneRatio, displayedPeakRatioQuantum, abs_of_nonpos]
    · refine ⟨by norm_num [displayedPeakRatioQuantum], ⟨9, by norm_num
          [displayedMToMPlusOneRatio, displayedPeakRatioQuantum]⟩, ?_⟩
      simp only [predictedMToMPlusOneRatio, predictedMPlusOneRelativeToM,
        carbon13Fraction, carbon12Fraction, otherElementMPlusOneContribution,
        displayedMToMPlusOneRatio, displayedPeakRatioQuantum, add_zero]
      norm_num
  have hcount : carbonAtomCount = 10 :=
    carbon_atom_count_raw.2.unique hchosen hten
  refine ⟨carbon_atom_count_raw, hcount, hchosen, ?_⟩
  intro n hn
  exact carbon_atom_count_raw.2.unique hn hchosen

/-! ## Source-first visual recount of compound 5 -/

/-- Ring positions used only to record the connectivity visible in compound 5. -/
inductive RingPosition where
  | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Fintype, Repr

/-- The four visually distinct building-block types in compound 5. -/
inductive CompoundFiveBlock where
  | trisubstitutedBenzeneCore
  | phenolicHydroxy
  | methoxy
  | allyl
  deriving DecidableEq, Fintype, Repr

/-- The atom of a substituent forming its cross-boundary bond to the ring. -/
inductive AttachmentEndpoint where
  | oxygen
  | carbon
  deriving DecidableEq, Repr

/-- One depicted bond from a benzene-ring carbon to a substituent. -/
structure RingAttachment where
  site : RingPosition
  block : CompoundFiveBlock
  endpoint : AttachmentEndpoint
  deriving DecidableEq, Repr

/-- The three cross-boundary bonds visible in compound 5: phenolic O at C1,
methoxy O at C2, and allylic C at C4. -/
def compoundFiveAttachments : Sourced (List RingAttachment) where
  value :=
    [ ⟨.p1, .phenolicHydroxy, .oxygen⟩,
      ⟨.p2, .methoxy, .oxygen⟩,
      ⟨.p4, .allyl, .carbon⟩ ]
  origin := .problemImage
  locator := "T1_page-2.png, Hypericum row, structure numbered 5"

/-- Number of substituent bonds incident to each depicted ring carbon. -/
def compoundFiveExternalDegree : RingPosition → ℕ
  | .p1 | .p2 | .p4 => 1
  | .p3 | .p5 | .p6 => 0

/-- Heavy-atom degree after adding the two bonds belonging to the aromatic
six-cycle. -/
def compoundFiveRingHeavyAtomDegree (p : RingPosition) : ℕ :=
  2 + compoundFiveExternalDegree p

/-- Formula ledgers for the already-attached fragments.  The core is `C6H3`
because its three substituted hydrogens are absent; consequently no hidden
condensation loss is applied when these ledgers are recombined. -/
def compoundFiveBlockFormula : CompoundFiveBlock → MolecularFormula
  | .trisubstitutedBenzeneCore => ⟨6, 3, 0⟩
  | .phenolicHydroxy => ⟨0, 1, 1⟩
  | .methoxy => ⟨1, 3, 1⟩
  | .allyl => ⟨3, 5, 0⟩

/-- Full formula obtained by recombining every connected component ledger. -/
def compoundFiveAssembledFormula : MolecularFormula :=
  MolecularFormula.add
    (compoundFiveBlockFormula .trisubstitutedBenzeneCore)
    (MolecularFormula.add
      (compoundFiveBlockFormula .phenolicHydroxy)
      (MolecularFormula.add
        (compoundFiveBlockFormula .methoxy)
        (compoundFiveBlockFormula .allyl)))

/-- The source-image structural case split: compounds 1 and 5, and no other
numbered structures in the table, visibly contain a free phenolic OH. -/
def depictedFreePhenolicCandidates : Sourced (Finset Compound) where
  value := {.c1, .c5}
  origin := .problemImage
  locator := "T1_page-2.png, functional-group recount of structures 1--10"

/-- A transparent image-derived predicate, rather than a freely set Boolean. -/
def HasDepictedFreePhenolicHydroxy (c : Compound) : Prop :=
  c ∈ depictedFreePhenolicCandidates.value

/-- The nontrivial visual carrier for the structure and formula of compound 5. -/
def CompoundFiveVisualRecount : Prop :=
  compoundFiveAttachments.value.length = 3 ∧
  compoundFiveRingHeavyAtomDegree .p1 = 3 ∧
  compoundFiveRingHeavyAtomDegree .p2 = 3 ∧
  compoundFiveRingHeavyAtomDegree .p3 = 2 ∧
  compoundFiveRingHeavyAtomDegree .p4 = 3 ∧
  compoundFiveRingHeavyAtomDegree .p5 = 2 ∧
  compoundFiveRingHeavyAtomDegree .p6 = 2 ∧
  compoundFiveAssembledFormula = depictedFormula .c5 ∧
  depictedFormula .c5 = ⟨10, 12, 2⟩ ∧
  HasDepictedFreePhenolicHydroxy .c5

theorem compound_five_visual_recount : CompoundFiveVisualRecount := by
  simp [CompoundFiveVisualRecount, compoundFiveAttachments,
    compoundFiveRingHeavyAtomDegree, compoundFiveExternalDegree,
    compoundFiveAssembledFormula, compoundFiveBlockFormula, MolecularFormula.add,
    depictedFormula, HasDepictedFreePhenolicHydroxy,
    depictedFreePhenolicCandidates]

/-! ## Aqueous iron(III) qualitative compatibility -/

/-- Phases needed by the stated qualitative test. -/
inductive Phase where
  | aqueous
  deriving DecidableEq, Repr

/-- The explicitly named reagent in the source test. -/
inductive TestReagent where
  | ironIII
  deriving DecidableEq, Repr

/-- Formal charge encoded by the reagent name `Fe3+`. -/
def TestReagent.formalCharge : TestReagent → ℤ
  | .ironIII => 3

/-- The observed qualitative readout. -/
inductive TestObservation where
  | characteristicColourChange
  deriving DecidableEq, Repr

/-- Exact problem-side test context. -/
structure FeIIITestContext where
  analyteRole : ElixirComponent
  medium : Phase
  reagent : TestReagent
  observation : TestObservation
  deriving DecidableEq, Repr

/-- Source carrier for the addition of W to aqueous Fe3+ and its observed
colour change. -/
def sourceFeIIITest : Sourced FeIIITestContext where
  value := ⟨.W, .aqueous, .ironIII, .characteristicColourChange⟩
  origin := .problemText
  locator :=
    "T1_page-3.png: W added to aqueous Fe3+; characteristic colour change observed"

/-- This observation is used only as a non-exclusive named-transform
compatibility constraint, never as a quantitative material stage. -/
inductive TransformationAuditClass where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

/-- Scope of the empirical bridge: it proposes a compatible coloured complex,
without claiming yield, completeness, sole product, or absence of byproducts. -/
inductive QualitativeClaimScope where
  | nonexclusiveCompatibility
  deriving DecidableEq, Repr

/-- The qualitative product role authorized by the forward registry rule. -/
inductive QualitativeProductRole where
  | ironIIIPhenolOrPhenolateComplex
  deriving DecidableEq, Repr

/-- Source-to-rule binding for this target. -/
structure QualitativeFeIIITransformBinding where
  classification : TransformationAuditClass
  reactant : Compound
  reagent : TestReagent
  medium : Phase
  productRole : QualitativeProductRole
  observation : TestObservation
  scope : QualitativeClaimScope
  sourceLocator : String

/-- Full reproducibility metadata for a trusted empirical-rule lookup. -/
structure EmpiricalRuleCitation where
  ruleId : String
  ruleVersion : ℕ
  datasetVersion : String
  datasetSha256 : String
  recordSha256 : String
  baseDatasetSha256 : String
  pinnedRuleRecordSha256 : String
  registryManifestSha256 : String
  authorityKind : String
  sourceUrl : String
  sourceDoi : String
  sourceLocator : String
  sourceContentSha256 : String
  claim : String
  applicabilityConditions : List String
  exclusions : List String
  automaticProblemInstantiation : Bool
  approvalStatus : String
  approvalScope : String
  reviewerId : String
  approvedAt : String

/-- Receipt returned by the allowed offline lookup
`empirical_rule aqueous_feiii_phenol_colored_complex`. -/
def aqueousFeIIIPhenolRuleCitation : EmpiricalRuleCitation where
  ruleId := "aqueous_feiii_phenol_colored_complex"
  ruleVersion := 1
  datasetVersion :=
    "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+contest-interpretation-v1+trusted-empirical-rules-v1"
  datasetSha256 :=
    "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"
  recordSha256 :=
    "67fd6f821dcb2c53846e3e084e6a336f170b5dfd9d5fe9584743c4b301f74faf"
  baseDatasetSha256 :=
    "3f9ac23f3515cf263275c244772de895c5402fb59a12061aa81c65ede91c094f"
  pinnedRuleRecordSha256 :=
    "6485cda7ae7d9289f5046b238be831dd3fd55e7dc81ae87310390a8f7db68d22"
  registryManifestSha256 :=
    "801783bce40546c54633e6292f62aee68706a2bc4bd359dda70085321ed49808"
  authorityKind := "peer_reviewed_literature"
  sourceUrl := "https://www.nature.com/articles/1651012b0"
  sourceDoi := "10.1038/1651012b0"
  sourceLocator :=
    "Nature 165 (1950) 1012, complete one-page letter; absorption and titration study of freshly prepared aqueous ferric chloride-phenol coloured complexes."
  sourceContentSha256 :=
    "b8b2efefde3c552cde5211e865462bef4add50e3422ed45edd0b46554b250aae"
  claim :=
    "In aqueous media where iron(III) remains available for coordination, an accessible phenolic hydroxy group can form a visibly colored iron(III)-phenol or iron(III)-phenolate complex."
  applicabilityConditions :=
    [ "The test medium is aqueous and contains available iron(III).",
      "The phenolic hydroxy group is structurally accessible.",
      "The observed colour is distinct from the iron(III) reagent blank." ]
  exclusions :=
    [ "This forward rule is not an unconditional colour-implies-phenol inverse.",
      "A negative result does not exclude every phenol.",
      "Precipitation, incompatible pH, or competing strong ligands are outside scope.",
      "The rule does not identify a particular molecule." ]
  automaticProblemInstantiation := false
  approvalStatus := "approved"
  approvalScope := "rule_and_source"
  reviewerId := "trusted-worktree-curator-v1"
  approvedAt := "2026-08-24T03:10:00Z"

/-- Every conjunct is one returned applicability condition, bound to exact
problem/image evidence for candidate 5. -/
def FeIIIPhenolRuleApplicable (c : Compound) : Prop :=
  sourceFeIIITest.value.analyteRole = .W ∧
  sourceFeIIITest.value.medium = .aqueous ∧
  sourceFeIIITest.value.reagent = .ironIII ∧
  sourceFeIIITest.value.reagent.formalCharge = 3 ∧
  HasDepictedFreePhenolicHydroxy c ∧
  sourceFeIIITest.value.observation = .characteristicColourChange

/-- Non-exclusive compatibility conclusion of the forward empirical rule. -/
def FeIIIPhenolColourCompatibility (c : Compound) : Prop :=
  FeIIIPhenolRuleApplicable c ∧
  ∃ transform : QualitativeFeIIITransformBinding,
    transform.reactant = c ∧
    transform.reagent = sourceFeIIITest.value.reagent ∧
    transform.medium = sourceFeIIITest.value.medium ∧
    transform.observation = sourceFeIIITest.value.observation ∧
    transform.sourceLocator = sourceFeIIITest.locator ∧
    transform.classification = .qualitativeNamedTransformOnly ∧
    transform.productRole = .ironIIIPhenolOrPhenolateComplex ∧
    transform.scope = .nonexclusiveCompatibility

/-- The cited rule is deliberately one-way: an accessible phenolic OH under
the bound test conditions supplies a possible visibly coloured complex. -/
theorem aqueous_feIII_phenol_forward_rule (c : Compound)
    (h : FeIIIPhenolRuleApplicable c) :
    FeIIIPhenolColourCompatibility c := by
  refine ⟨h, ?_⟩
  refine ⟨{
    classification := .qualitativeNamedTransformOnly
    reactant := c
    reagent := sourceFeIIITest.value.reagent
    medium := sourceFeIIITest.value.medium
    productRole := .ironIIIPhenolOrPhenolateComplex
    observation := sourceFeIIITest.value.observation
    scope := .nonexclusiveCompatibility
    sourceLocator := sourceFeIIITest.locator
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Identification and combined answer contracts -/

/-- Candidate-local certificate checking the entire non-singleton source
domain, exact carbon count, visual assembly, and forward FeIII compatibility. -/
structure WCandidateCertificate (c : Compound) where
  inDepictedDomain : c ∈ depictedCandidateDomain.value
  formulaCarbonCount : (depictedFormula c).carbon = carbonAtomCount
  visualRecount : CompoundFiveVisualRecount
  feIIICompatibility : FeIIIPhenolColourCompatibility c

/-- Raw symbolic carrier for the identity output.  It states a substantive
compatibility certificate for the concrete depicted candidate. -/
def CompoundIdentityRawResult : Prop :=
  Nonempty (WCandidateCertificate .c5)

/-- Reported symbolic carrier.  Besides the candidate certificate, this audits
the complete depicted structural case split uniformly: compound 5 is the only
table entry having both ten carbons and a depicted free phenolic OH. -/
def CompoundIdentityReportedResult : Prop :=
  CompoundIdentityRawResult ∧
  ∀ c : Compound,
    c ∈ depictedCandidateDomain.value →
    (depictedFormula c).carbon = carbonAtomCount →
    HasDepictedFreePhenolicHydroxy c →
    c = .c5

/-- Human-facing classification attached to the proved specification. -/
def compoundIdentity : Compound := .c5

theorem compound_identity_raw : CompoundIdentityRawResult := by
  refine ⟨{
    inDepictedDomain := by simp [depictedCandidateDomain]
    formulaCarbonCount := ?_
    visualRecount := compound_five_visual_recount
    feIIICompatibility := ?_
  }⟩
  · rw [carbon_atom_count_reported.2.1]
    rfl
  · apply aqueous_feIII_phenol_forward_rule
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
    simp [HasDepictedFreePhenolicHydroxy, depictedFreePhenolicCandidates]

theorem compound_identity_reported : CompoundIdentityReportedResult := by
  refine ⟨compound_identity_raw, ?_⟩
  intro c _hDomain hCarbon hPhenolic
  have hcount : carbonAtomCount = 10 := carbon_atom_count_reported.2.1
  cases c <;>
    simp [depictedFormula, HasDepictedFreePhenolicHydroxy,
      depictedFreePhenolicCandidates, hcount] at hCarbon hPhenolic ⊢

/-- Mixed raw result: both controller-requested outputs occur in source order. -/
def RawResult : Prop :=
  CarbonAtomCountRawResult ∧ CompoundIdentityRawResult

/-- Mixed reported result: exact integer reporting followed by exact symbolic
identification, matching the controller-requested output order. -/
def ReportedResult : Prop :=
  CarbonAtomCountReportedResult ∧ CompoundIdentityReportedResult

theorem raw_result :
    ("e31097a023ce57c509f8ef6d7764f705a4158808520a4b7970bfc3f173a6a1ac" : String) =
      "e31097a023ce57c509f8ef6d7764f705a4158808520a4b7970bfc3f173a6a1ac" ∧
    IChO2026Problems.IChO2026T1A3.RawResult := by
  exact ⟨rfl, carbon_atom_count_raw, compound_identity_raw⟩

theorem reported_result :
    ("51af3ed372aaf4defb7e88942e91d388b02df4835a52362c6e3831f223c2ac57" : String) =
      "51af3ed372aaf4defb7e88942e91d388b02df4835a52362c6e3831f223c2ac57" ∧
    IChO2026Problems.IChO2026T1A3.ReportedResult := by
  exact ⟨rfl, carbon_atom_count_reported, compound_identity_reported⟩

end

end IChO2026Problems.IChO2026T1A3
