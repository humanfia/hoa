import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T9-A5: structure of intermediate L

The upper scheme on source page 3 starts from beta-cyclodextrin: seven
alpha-D-glucopyranoside units, seven primary `CH2OH` groups, and fourteen
secondary hydroxyl groups.  The first source arrow lists `NaH (30 equiv.)`,
`BnCl (30 equiv.)`, then `DIBAL-H (2 equiv.)`.  The paragraph immediately
above the scheme states that one protic group at unit 1 directs the *next*
primary reductive debenzylation to unit 4, using unit 3 only when unit 4 is not
available.

This file treats that arrow as `qualitativeNamedTransformOnly`: no yield,
phase, completeness of a material balance, or unpictured byproduct is claimed.
The reagent-to-pattern bridge is not inferred from equivalents alone.  It is
bound to the two relevant statements in Sarabia-Vallejo et al.,
*Pharmaceutics* 2023, 15, 2345, DOI 10.3390/pharmaceutics15092345: section
9.4 records perbenzylation of alpha- and beta-cyclodextrins with benzyl
chloride/sodium hydride, while section 9.2.2 records DIBAL-H-mediated primary
A,D bis-debenzylation of perbenzylated alpha-, beta-, and gamma-cyclodextrins.
The problem paragraph supplies the target-local numbering and branch: an OH at
unit 1 directs the next primary cleavage to unit 4, with unit 3 used only when
unit 4 is unavailable.  These qualitative claims drive uniform transformations
of the complete 21-site substitution pattern.

The output is not a chemical name or a string.  `structureL` is a finite
atom-labelled graph with every hydrogen explicit, single/double bond orders,
formal charges, radical-electron counts, and all 35 glucose stereocentres.
The source-facing template carrier then records every primary and secondary
box separately.
-/

namespace IChO2026Problems
namespace T9A5

/-! ## Source provenance and reaction-arrow inventory -/

/-- Origins admitted by the source report for this target. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | publicLiterature
  | derivedTheorem
deriving DecidableEq, Repr

/-- Exact source-local regions used in the derivation. -/
inductive SourceLocator where
  | page3DirectingParagraph
  | page3StartingBetaCDTemplate
  | page3ReagentArrowToL
  | page2AlphaDGlucopyranosideTemplate
deriving DecidableEq, Repr

/-- Exact locators in the peer-reviewed public source used to bridge the two
named transformations. -/
inductive LiteratureLocator where
  | pharmaceutics2023Section9_2_2
  | pharmaceutics2023Section9_4
deriving DecidableEq, Repr

/-- The staged transformation is used only as a structural compatibility
constraint; omitted phases, coefficients, yields, and byproducts stay unknown. -/
inductive StagedTransformationUse where
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

def stagedTransformationUse : StagedTransformationUse :=
  .qualitativeNamedTransformOnly

/-- Reagents explicitly printed over or under the arrow leading to `L`. -/
inductive Reagent where
  | sodiumHydride
  | benzylChloride
  | diisobutylaluminiumHydride
deriving DecidableEq, Fintype, Repr

/-- Cyclodextrin classes explicitly included in the literature claims. -/
inductive CyclodextrinClass where
  | alpha
  | beta
  | gamma
deriving DecidableEq, Fintype, Repr

/-- A structural transformation asserted by a cited source.  This is an
enumerated semantic carrier, rather than a freely set `Bool` or opaque `Prop`.
Its interpretation on substitution patterns is defined below. -/
inductive QualitativePatternTransform where
  | perbenzylateAllAlcoholOxygens
  | primaryADBisDebenzylation
deriving DecidableEq, Fintype, Repr

/-- Citation and applicability data for one public-literature chemistry
bridge.  The exact prose is retained for independent scope review, while the
structured fields are what the Lean trace consumes. -/
structure LiteratureAuthority where
  title : String
  doi : String
  stableURL : String
  fullTextXMLSha256 : String
  locator : LiteratureLocator
  exactScopedClaim : String
  supportedCyclodextrins : List CyclodextrinClass
  requiredReagents : List Reagent
  transformation : QualitativePatternTransform
  useClass : StagedTransformationUse
  provenance : Provenance
  quantitativeClaimsAuthorized : Bool
deriving DecidableEq, Repr

def literatureTitle : String :=
  "Cyclodextrin Inclusion Complexes for Improved Drug Bioavailability and Activity: Synthetic and Analytical Aspects"

def literatureDOI : String := "10.3390/pharmaceutics15092345"

def literatureStableURL : String :=
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC10534465/"

/-- SHA-256 of the Europe PMC full-text XML retrieved from the stable public
record during this answer-blind derivation. -/
def literatureFullTextXMLSha256 : String :=
  "fd5e5a55f0403bf06d6e599abff9eb3ff5f7ae78457d2b10b9c47a208fb16756"

/-- Section 9.4: perbenzylation of alpha and beta CDs with BnCl/NaH.  The
reported `>90%` yield is deliberately omitted from the usable claim because
this target uses the transformation only qualitatively. -/
def perbenzylationAuthority : LiteratureAuthority :=
  { title := literatureTitle
    doi := literatureDOI
    stableURL := literatureStableURL
    fullTextXMLSha256 := literatureFullTextXMLSha256
    locator := .pharmaceutics2023Section9_4
    exactScopedClaim :=
      "Perbenzylation of α and β-cyclodextrins is performed in excellent yield (>90%) by treatment with benzyl chloride and sodium hydride."
    supportedCyclodextrins := [.alpha, .beta]
    requiredReagents := [.sodiumHydride, .benzylChloride]
    transformation := .perbenzylateAllAlcoholOxygens
    useClass := .qualitativeNamedTransformOnly
    provenance := .publicLiterature
    quantitativeClaimsAuthorized := false }

/-- Section 9.2.2: DIBAL-H-mediated primary A,D bis-debenzylation of
perbenzylated alpha, beta, and gamma CDs.  Protocol, yield, and exclusivity are
not imported. -/
def adBisDebenzylationAuthority : LiteratureAuthority :=
  { title := literatureTitle
    doi := literatureDOI
    stableURL := literatureStableURL
    fullTextXMLSha256 := literatureFullTextXMLSha256
    locator := .pharmaceutics2023Section9_2_2
    exactScopedClaim :=
      "The selective synthesis of AD diols at the primary side is achieved through a DIBAL-H-mediated regioselective deprotection of the primary hydroxyl groups of perbenzylated α, β, and γ cyclodextrins."
    supportedCyclodextrins := [.alpha, .beta, .gamma]
    requiredReagents := [.diisobutylaluminiumHydride]
    transformation := .primaryADBisDebenzylation
    useClass := .qualitativeNamedTransformOnly
    provenance := .publicLiterature
    quantitativeClaimsAuthorized := false }

/-- A literature claim applies only within its structured cyclodextrin,
reagent, transformation, and qualitative-use scope. -/
def LiteratureAuthority.Applies
    (authority : LiteratureAuthority) (cd : CyclodextrinClass)
    (reagents : List Reagent) (transformation : QualitativePatternTransform) : Prop :=
  cd ∈ authority.supportedCyclodextrins ∧
  authority.requiredReagents = reagents ∧
  authority.transformation = transformation ∧
  authority.useClass = .qualitativeNamedTransformOnly ∧
  authority.provenance = .publicLiterature ∧
  authority.quantitativeClaimsAuthorized = false

/-- Citation-bound applicability audit for both chemistry bridges used by this
target.  It does not contain a product pattern or a candidate structure. -/
def LiteratureBridgeSpec : Prop :=
  perbenzylationAuthority.title = literatureTitle ∧
  perbenzylationAuthority.doi = literatureDOI ∧
  perbenzylationAuthority.stableURL = literatureStableURL ∧
  perbenzylationAuthority.fullTextXMLSha256 = literatureFullTextXMLSha256 ∧
  perbenzylationAuthority.locator = .pharmaceutics2023Section9_4 ∧
  perbenzylationAuthority.exactScopedClaim =
    "Perbenzylation of α and β-cyclodextrins is performed in excellent yield (>90%) by treatment with benzyl chloride and sodium hydride." ∧
  perbenzylationAuthority.Applies .beta
    [.sodiumHydride, .benzylChloride]
    .perbenzylateAllAlcoholOxygens ∧
  adBisDebenzylationAuthority.title = literatureTitle ∧
  adBisDebenzylationAuthority.doi = literatureDOI ∧
  adBisDebenzylationAuthority.stableURL = literatureStableURL ∧
  adBisDebenzylationAuthority.fullTextXMLSha256 = literatureFullTextXMLSha256 ∧
  adBisDebenzylationAuthority.locator = .pharmaceutics2023Section9_2_2 ∧
  adBisDebenzylationAuthority.exactScopedClaim =
    "The selective synthesis of AD diols at the primary side is achieved through a DIBAL-H-mediated regioselective deprotection of the primary hydroxyl groups of perbenzylated α, β, and γ cyclodextrins." ∧
  adBisDebenzylationAuthority.Applies .beta
    [.diisobutylaluminiumHydride]
    .primaryADBisDebenzylation

theorem literatureBridge_spec : LiteratureBridgeSpec := by
  unfold LiteratureBridgeSpec LiteratureAuthority.Applies
  native_decide

/-- A problem-printed reagent amount in equivalents. -/
structure ReagentAmount where
  reagent : Reagent
  equivalents : ℕ
deriving DecidableEq, Repr

/-- The two ordered stages printed on page 3. -/
def sourceReagentSchedule : List (List ReagentAmount) :=
  [ [⟨.sodiumHydride, 30⟩, ⟨.benzylChloride, 30⟩],
    [⟨.diisobutylaluminiumHydride, 2⟩] ]

/-- Source roles and direction of the qualitative arrow, without supplying a
product structure as a field. -/
structure QualitativeSourceArrow where
  reactantRole : String
  productRole : String
  directionLeftToRight : Bool
  schedule : List (List ReagentAmount)
  locator : SourceLocator
  useClass : StagedTransformationUse
deriving DecidableEq, Repr

def arrowToL : QualitativeSourceArrow :=
  { reactantRole := "beta-CD template with 21 hydroxyl groups"
    productRole := "L"
    directionLeftToRight := true
    schedule := sourceReagentSchedule
    locator := .page3ReagentArrowToL
    useClass := .qualitativeNamedTransformOnly }

/-- Source-only specification of the depicted arrow.  It records no candidate
connectivity or substitution assignment. -/
def SourceArrowSpec : Prop :=
  arrowToL.reactantRole = "beta-CD template with 21 hydroxyl groups" ∧
  arrowToL.productRole = "L" ∧
  arrowToL.directionLeftToRight = true ∧
  arrowToL.schedule =
    [ [⟨.sodiumHydride, 30⟩, ⟨.benzylChloride, 30⟩],
      [⟨.diisobutylaluminiumHydride, 2⟩] ] ∧
  arrowToL.locator = .page3ReagentArrowToL ∧
  arrowToL.useClass = .qualitativeNamedTransformOnly

theorem sourceArrow_spec : SourceArrowSpec := by
  unfold SourceArrowSpec
  native_decide

/-- The reagent names in the two problem-arrow stages exactly match the
reagent applicability fields of the two literature authorities.  Equivalents
are retained in `sourceReagentSchedule` but are not consumed by this
qualitative matching relation. -/
def SourceScheduleAuthorityMatch : Prop :=
  (sourceReagentSchedule[0]?).map
      (fun stage => stage.map fun amount => amount.reagent) =
        some perbenzylationAuthority.requiredReagents ∧
  (sourceReagentSchedule[1]?).map
      (fun stage => stage.map fun amount => amount.reagent) =
        some adBisDebenzylationAuthority.requiredReagents

theorem sourceSchedule_authorityMatch : SourceScheduleAuthorityMatch := by
  unfold SourceScheduleAuthorityMatch
  native_decide

/-! ## The 21 hydroxyl-site domain and the directed reaction trace -/

/-- Seven source-labelled glucopyranoside positions.  Lean value `0` is the
box printed as unit 1, and so on. -/
abbrev BetaCDUnit := Fin 7

def unit1 : BetaCDUnit := ⟨0, by omega⟩
def unit2 : BetaCDUnit := ⟨1, by omega⟩
def unit3 : BetaCDUnit := ⟨2, by omega⟩
def unit4 : BetaCDUnit := ⟨3, by omega⟩
def unit5 : BetaCDUnit := ⟨4, by omega⟩
def unit6 : BetaCDUnit := ⟨5, by omega⟩
def unit7 : BetaCDUnit := ⟨6, by omega⟩

/-- Move by `offset` units around the seven-membered beta-CD ring. -/
def unitAtOffset (unit : BetaCDUnit) (offset : ℕ) : BetaCDUnit :=
  ⟨(unit.val + offset) % 7, Nat.mod_lt _ (by omega)⟩

/-- The preceding unit in the alpha-1,4-linked cycle. -/
def precedingUnit (unit : BetaCDUnit) : BetaCDUnit := unitAtOffset unit 6

/-- The three alcohol-derived oxygen sites in each glucose residue. -/
inductive HydroxylKind where
  | secondaryC2
  | secondaryC3
  | primaryC6
deriving DecidableEq, Fintype, Repr

/-- Protic directing groups explicitly named by the problem paragraph. -/
inductive ProticGroupKind where
  | amine
  | hydroxyl
deriving DecidableEq, Fintype, Repr

def HydroxylKind.isPrimary : HydroxylKind → Bool
  | .primaryC6 => true
  | _ => false

/-- One address among the `7 * 3 = 21` alcohol-derived oxygen sites. -/
structure HydroxylAddress where
  unit : BetaCDUnit
  kind : HydroxylKind
deriving DecidableEq, Fintype, Repr

/-- Whether the oxygen bears hydrogen or a benzyl carbon in a given stage. -/
inductive OxygenSubstituent where
  | hydrogen
  | benzyl
deriving DecidableEq, Fintype, Repr

abbrev SubstitutionPattern := HydroxylAddress → OxygenSubstituent

/-- The unmodified beta-CD pattern depicted at the left of the arrow. -/
def startingPattern : SubstitutionPattern := fun _ => .hydrogen

/-- Uniform O-benzylation of every alcohol-derived oxygen. -/
def benzylateEveryAlcohol (_before : SubstitutionPattern) : SubstitutionPattern :=
  fun _ => .benzyl

/-- Reductive cleavage at one primary site, leaving every other site fixed. -/
def cleavePrimaryAt
    (before : SubstitutionPattern) (unit : BetaCDUnit) : SubstitutionPattern :=
  fun address =>
    if address.unit = unit ∧ address.kind = .primaryC6 then
      .hydrogen
    else
      before address

/-- A primary O-benzyl position is available for reductive debenzylation. -/
def PrimaryPositionAvailable
    (pattern : SubstitutionPattern) (unit : BetaCDUnit) : Prop :=
  pattern ⟨unit, .primaryC6⟩ = .benzyl

/-- Structured transcription of the problem's directing paragraph.  The
source's unit labels are represented both as one-based labels and as offsets
from the anchor so that the ensuing pattern transformation is auditable. -/
structure DirectedRuleSourceData where
  anchorUnitLabel : ℕ
  preferredTargetUnitLabel : ℕ
  fallbackTargetUnitLabel : ℕ
  preferredOffset : ℕ
  fallbackOffset : ℕ
  supportedProticGroups : List ProticGroupKind
  targetKind : HydroxylKind
  fallbackOnlyWhenPreferredUnavailable : Bool
  nextCleavageOnly : Bool
  locator : SourceLocator
  provenance : Provenance
deriving DecidableEq, Repr

def directedRuleSourceData : DirectedRuleSourceData :=
  { anchorUnitLabel := 1
    preferredTargetUnitLabel := 4
    fallbackTargetUnitLabel := 3
    preferredOffset := 3
    fallbackOffset := 2
    supportedProticGroups := [.amine, .hydroxyl]
    targetKind := .primaryC6
    fallbackOnlyWhenPreferredUnavailable := true
    nextCleavageOnly := true
    locator := .page3DirectingParagraph
    provenance := .problemText }

/-- The page-3 directing rule: try relative unit 4 (offset three from unit 1),
and use relative unit 3 only if the unit-4 primary position is unavailable. -/
noncomputable def directedTarget
    (pattern : SubstitutionPattern) (anchor : BetaCDUnit) : BetaCDUnit := by
  classical
  exact
    if PrimaryPositionAvailable pattern
        (unitAtOffset anchor directedRuleSourceData.preferredOffset) then
      unitAtOffset anchor directedRuleSourceData.preferredOffset
    else
      unitAtOffset anchor directedRuleSourceData.fallbackOffset

/-- Source-to-model bridge for every branch and scope restriction stated in
the directing paragraph.  It contains no final pattern. -/
noncomputable def SourceDirectedRuleSpec : Prop := by
  classical
  exact
    directedRuleSourceData.anchorUnitLabel = 1 ∧
    directedRuleSourceData.preferredTargetUnitLabel = 4 ∧
    directedRuleSourceData.fallbackTargetUnitLabel = 3 ∧
    directedRuleSourceData.preferredOffset = 3 ∧
    directedRuleSourceData.fallbackOffset = 2 ∧
    directedRuleSourceData.supportedProticGroups = [.amine, .hydroxyl] ∧
    directedRuleSourceData.targetKind = .primaryC6 ∧
    directedRuleSourceData.fallbackOnlyWhenPreferredUnavailable = true ∧
    directedRuleSourceData.nextCleavageOnly = true ∧
    directedRuleSourceData.locator = .page3DirectingParagraph ∧
    directedRuleSourceData.provenance = .problemText ∧
    ∀ (pattern : SubstitutionPattern) (anchor : BetaCDUnit),
      directedTarget pattern anchor =
        if PrimaryPositionAvailable pattern (unitAtOffset anchor 3) then
          unitAtOffset anchor 3
        else
          unitAtOffset anchor 2

theorem sourceDirectedRule_spec : SourceDirectedRuleSpec := by
  classical
  unfold SourceDirectedRuleSpec
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro pattern anchor
  rfl

/-- One protic primary group and no other protic group remain after the first
DIBAL-H cleavage. -/
def HasSinglePrimaryProticGroup
    (pattern : SubstitutionPattern) (anchor : BetaCDUnit) : Prop :=
  pattern ⟨anchor, .primaryC6⟩ = .hydrogen ∧
  (∀ unit : BetaCDUnit, unit ≠ anchor →
    pattern ⟨unit, .primaryC6⟩ = .benzyl) ∧
  (∀ unit : BetaCDUnit,
    pattern ⟨unit, .secondaryC2⟩ = .benzyl ∧
    pattern ⟨unit, .secondaryC3⟩ = .benzyl)

/-- Generic exhaustive O-benzylation relation used uniformly on all 21 sites. -/
def ExhaustiveBenzylation
    (before after : SubstitutionPattern) : Prop :=
  after = benzylateEveryAlcohol before

/-- Generic first primary reductive-debenzylation step. -/
def FirstPrimaryDebenzylation
    (before : SubstitutionPattern) (anchor : BetaCDUnit)
    (after : SubstitutionPattern) : Prop :=
  PrimaryPositionAvailable before anchor ∧
  after = cleavePrimaryAt before anchor ∧
  HasSinglePrimaryProticGroup after anchor

/-- Generic directed *next* cleavage implementing exactly the source's
unit-4-else-unit-3 branch. -/
def DirectedNextDebenzylation
    (before : SubstitutionPattern) (anchor : BetaCDUnit)
    (after : SubstitutionPattern) : Prop :=
  HasSinglePrimaryProticGroup before anchor ∧
  let target := directedTarget before anchor
  PrimaryPositionAvailable before target ∧
  after = cleavePrimaryAt before target

/-- Interpret a structured, citation-bound qualitative transformation on the
complete substitution-pattern carrier.  The first case is uniform on all 21
addresses.  The second exposes both the first primary cleavage and the
problem-directed next cleavage, including its fallback branch. -/
def QualitativePatternTransform.Realizes
    (transformation : QualitativePatternTransform)
    (before : SubstitutionPattern) (anchor : BetaCDUnit)
    (after : SubstitutionPattern) : Prop :=
  match transformation with
  | .perbenzylateAllAlcoholOxygens =>
      ExhaustiveBenzylation before after
  | .primaryADBisDebenzylation =>
      ∃ afterFirstCleavage : SubstitutionPattern,
        FirstPrimaryDebenzylation before anchor afterFirstCleavage ∧
        DirectedNextDebenzylation afterFirstCleavage anchor after

/-- The source paragraph labels the protic directing site as unit 1. -/
def CanonicallyNumberedFirstSite (anchor : BetaCDUnit) : Prop :=
  anchor = unit1

/-- Complete qualitative trace from the depicted starting template to a final
substitution pattern.  The cited claims select generic transformation
constructors, the pattern interpreter supplies their sitewise meaning, and all
intermediate patterns are quantified.  No final box value occurs as a premise. -/
def SourceReactionTrace (finalPattern : SubstitutionPattern) : Prop :=
  ∃ (anchor : BetaCDUnit)
    (fullyBenzylated : SubstitutionPattern),
    CanonicallyNumberedFirstSite anchor ∧
    SourceDirectedRuleSpec ∧
    LiteratureBridgeSpec ∧
    SourceScheduleAuthorityMatch ∧
    perbenzylationAuthority.Applies .beta
      [.sodiumHydride, .benzylChloride]
      .perbenzylateAllAlcoholOxygens ∧
    perbenzylationAuthority.transformation.Realizes
      startingPattern anchor fullyBenzylated ∧
    adBisDebenzylationAuthority.Applies .beta
      [.diisobutylaluminiumHydride]
      .primaryADBisDebenzylation ∧
    adBisDebenzylationAuthority.transformation.Realizes
      fullyBenzylated anchor finalPattern

/-- Candidate pattern obtained by executing the two generic transformations,
not by postulating any requested box value. -/
noncomputable def patternL : SubstitutionPattern :=
  let allBenzyl := benzylateEveryAlcohol startingPattern
  let afterFirst := cleavePrimaryAt allBenzyl unit1
  cleavePrimaryAt afterFirst (directedTarget afterFirst unit1)

/-- Source-first recount of the starting figure: seven units, fourteen
secondary sites, seven primary sites, hence twenty-one hydroxyl sites. -/
def SourceFigureRecount : Prop :=
  Fintype.card BetaCDUnit = 7 ∧
  Fintype.card HydroxylAddress = 21 ∧
  (Finset.univ.filter fun address : HydroxylAddress =>
      !address.kind.isPrimary).card = 14 ∧
  (Finset.univ.filter fun address : HydroxylAddress =>
      address.kind.isPrimary).card = 7 ∧
  ∀ address : HydroxylAddress, startingPattern address = .hydrogen

theorem sourceFigure_recount : SourceFigureRecount := by
  unfold SourceFigureRecount
  native_decide

/-- Exact arithmetic/schedule audit of the printed equivalents.  In
particular, this proposition does *not* infer a number of cleavages from two
DIBAL-H equivalents; the qualitative bis-debenzylation classification comes
from the citation-bound transformation claim above. -/
def ReagentCountCompatibility : Prop :=
  21 ≤ 30 ∧
  sourceReagentSchedule[0]?
      = some [⟨.sodiumHydride, 30⟩, ⟨.benzylChloride, 30⟩] ∧
  sourceReagentSchedule[1]?
      = some [⟨.diisobutylaluminiumHydride, 2⟩]

theorem reagentCount_compatibility : ReagentCountCompatibility := by
  unfold ReagentCountCompatibility
  native_decide

/-- With relative unit 4 still protected after the first cleavage, the branch
printed in the paragraph selects source-labelled unit 4, not fallback unit 3. -/
theorem directedTarget_after_first :
    directedTarget
      (cleavePrimaryAt (benzylateEveryAlcohol startingPattern) unit1) unit1 =
      unit4 := by
  simp [directedTarget, PrimaryPositionAvailable, cleavePrimaryAt,
    benzylateEveryAlcohol, directedRuleSourceData, unitAtOffset, unit1, unit4]

/-- The transparent reaction trace determines the candidate pattern. -/
theorem sourceReactionTrace_patternL : SourceReactionTrace patternL := by
  refine ⟨unit1, benzylateEveryAlcohol startingPattern,
    rfl, sourceDirectedRule_spec, literatureBridge_spec,
    sourceSchedule_authorityMatch, ?_, rfl, ?_, ?_⟩
  · unfold LiteratureAuthority.Applies
    native_decide
  · unfold LiteratureAuthority.Applies
    native_decide
  · change ∃ afterFirstCleavage : SubstitutionPattern,
      FirstPrimaryDebenzylation
          (benzylateEveryAlcohol startingPattern) unit1 afterFirstCleavage ∧
        DirectedNextDebenzylation afterFirstCleavage unit1 patternL
    refine ⟨cleavePrimaryAt (benzylateEveryAlcohol startingPattern) unit1,
      ?_, ?_⟩
    · simp [FirstPrimaryDebenzylation, PrimaryPositionAvailable,
      HasSinglePrimaryProticGroup, cleavePrimaryAt, benzylateEveryAlcohol]
    · have h41 : unit4 ≠ unit1 := by decide
      simp [DirectedNextDebenzylation, PrimaryPositionAvailable,
        HasSinglePrimaryProticGroup, cleavePrimaryAt, benzylateEveryAlcohol,
        patternL, directedTarget_after_first, h41]

/-- Any final pattern satisfying this canonically numbered source trace has
the same 21 box assignments.  This is trace determinism, not an open-world
uniqueness claim about every possible chemical pathway. -/
theorem sourceReactionTrace_determines_pattern
    {pattern : SubstitutionPattern} (h : SourceReactionTrace pattern) :
    pattern = patternL := by
  rcases h with ⟨anchor, fullyBenzylated, hanchor, _hdirectedRule,
    _hliterature, _hscheduleMatch, _hperAuthority, hperRealizes,
    _hadAuthority, hadRealizes⟩
  unfold CanonicallyNumberedFirstSite at hanchor
  subst anchor
  change ExhaustiveBenzylation startingPattern fullyBenzylated at hperRealizes
  unfold ExhaustiveBenzylation at hperRealizes
  subst fullyBenzylated
  change ∃ afterFirstCleavage : SubstitutionPattern,
      FirstPrimaryDebenzylation
          (benzylateEveryAlcohol startingPattern) unit1 afterFirstCleavage ∧
        DirectedNextDebenzylation afterFirstCleavage unit1 pattern at hadRealizes
  rcases hadRealizes with ⟨afterFirstCleavage, hfirst, hnext⟩
  rcases hfirst with ⟨_, hafterFirstCleavage, _⟩
  subst afterFirstCleavage
  unfold DirectedNextDebenzylation at hnext
  dsimp only at hnext
  rcases hnext with ⟨_, _, hpattern⟩
  rw [hpattern]
  rfl

/-- An explicit computable form of the source-derived substitution pattern. -/
theorem patternL_eq_explicit :
    patternL =
      cleavePrimaryAt
        (cleavePrimaryAt (benzylateEveryAlcohol startingPattern) unit1) unit4 := by
  dsimp only [patternL]
  rw [directedTarget_after_first]

/-- Every secondary oxygen is benzylated, and the primary oxygen is protic
exactly at units 1 and 4. -/
theorem patternL_site_classification :
    (∀ unit : BetaCDUnit,
      patternL ⟨unit, .secondaryC2⟩ = .benzyl ∧
      patternL ⟨unit, .secondaryC3⟩ = .benzyl) ∧
    (∀ unit : BetaCDUnit,
      patternL ⟨unit, .primaryC6⟩ = .hydrogen ↔
        unit = unit1 ∨ unit = unit4) := by
  rw [patternL_eq_explicit]
  constructor
  · intro unit
    simp [cleavePrimaryAt, benzylateEveryAlcohol]
  · intro unit
    fin_cases unit <;>
      simp [cleavePrimaryAt, benzylateEveryAlcohol, unit1, unit4]

/-- Two protic sites and nineteen O-benzyl sites result. -/
theorem patternL_substituent_counts :
    (Finset.univ.filter fun address : HydroxylAddress =>
      patternL address = .hydrogen).card = 2 ∧
    (Finset.univ.filter fun address : HydroxylAddress =>
      patternL address = .benzyl).card = 19 := by
  rw [patternL_eq_explicit]
  native_decide

/-! ## Explicit finite atom and bond vocabulary -/

inductive Element where
  | carbon
  | hydrogen
  | oxygen
deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | none
  | single
  | double
deriving DecidableEq, Fintype, Repr

/-- Atom data include every source-required electronic annotation. -/
structure AtomLabel where
  element : Element
  isotope : Option ℕ := none
  formalCharge : ℤ := 0
  radicalElectrons : ℕ := 0
deriving DecidableEq, Repr

inductive GlucoseCarbon where
  | c1 | c2 | c3 | c4 | c5 | c6
deriving DecidableEq, Fintype, Repr

/-- Seven explicit C-H hydrogens per glucose residue. -/
inductive CoreHydrogen where
  | c1H | c2H | c3H | c4H | c5H | c6Ha | c6Hb
deriving DecidableEq, Fintype, Repr

def coreHydrogenParent : CoreHydrogen → GlucoseCarbon
  | .c1H => .c1
  | .c2H => .c2
  | .c3H => .c3
  | .c4H => .c4
  | .c5H => .c5
  | .c6Ha | .c6Hb => .c6

/-- The benzyl methylene followed by the six cyclic phenyl positions. -/
inductive BenzylCarbon where
  | methylene
  | ring0 | ring1 | ring2 | ring3 | ring4 | ring5
deriving DecidableEq, Fintype, Repr

/-- The seven hydrogens in one `C7H7` benzyl substituent. -/
inductive BenzylHydrogen where
  | methyleneA | methyleneB
  | ring1H | ring2H | ring3H | ring4H | ring5H
deriving DecidableEq, Fintype, Repr

def benzylHydrogenParent : BenzylHydrogen → BenzylCarbon
  | .methyleneA | .methyleneB => .methylene
  | .ring1H => .ring1
  | .ring2H => .ring2
  | .ring3H => .ring3
  | .ring4H => .ring4
  | .ring5H => .ring5

/-- A finite universe of all possible atoms.  Pattern-dependent atoms have a
separate presence bit below; this avoids hiding an answer in a candidate-sized
vertex type. -/
inductive Atom where
  | glucoseCarbon (unit : BetaCDUnit) (position : GlucoseCarbon)
  | ringOxygen (unit : BetaCDUnit)
  | glycosidicOxygen (unit : BetaCDUnit)
  | substituentOxygen (address : HydroxylAddress)
  | coreHydrogen (unit : BetaCDUnit) (position : CoreHydrogen)
  | hydroxylHydrogen (address : HydroxylAddress)
  | benzylCarbon (address : HydroxylAddress) (position : BenzylCarbon)
  | benzylHydrogen (address : HydroxylAddress) (position : BenzylHydrogen)
deriving DecidableEq, Fintype, Repr

def atomLabel : Atom → AtomLabel
  | .glucoseCarbon _ _ | .benzylCarbon _ _ => { element := .carbon }
  | .ringOxygen _ | .glycosidicOxygen _ | .substituentOxygen _ =>
      { element := .oxygen }
  | .coreHydrogen _ _ | .hydroxylHydrogen _ | .benzylHydrogen _ _ =>
      { element := .hydrogen }

/-- Actual atom membership for a generic substitution pattern. -/
def atomPresent (pattern : SubstitutionPattern) : Atom → Bool
  | .glucoseCarbon _ _
  | .ringOxygen _
  | .glycosidicOxygen _
  | .substituentOxygen _
  | .coreHydrogen _ _ => true
  | .hydroxylHydrogen address =>
      decide (pattern address = .hydrogen)
  | .benzylCarbon address _
  | .benzylHydrogen address _ =>
      decide (pattern address = .benzyl)

/-- Equality up to the ordering of endpoints. -/
def IsPair (a b x y : Atom) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

/-- Carbon-chain adjacency within one glucopyranose ring skeleton. -/
def ConsecutiveGlucoseCarbons
    (a b : GlucoseCarbon) : Prop :=
  (a = .c1 ∧ b = .c2) ∨ (a = .c2 ∧ b = .c1) ∨
  (a = .c2 ∧ b = .c3) ∨ (a = .c3 ∧ b = .c2) ∨
  (a = .c3 ∧ b = .c4) ∨ (a = .c4 ∧ b = .c3) ∨
  (a = .c4 ∧ b = .c5) ∨ (a = .c5 ∧ b = .c4) ∨
  (a = .c5 ∧ b = .c6) ∨ (a = .c6 ∧ b = .c5)

def hydroxylCarbon : HydroxylKind → GlucoseCarbon
  | .secondaryC2 => .c2
  | .secondaryC3 => .c3
  | .primaryC6 => .c6

/-- Every pattern-independent single bond in the cyclic beta-CD core,
including all explicitly represented carbon hydrogens. -/
def CoreSingleBond (a b : Atom) : Prop :=
  (∃ (unit : BetaCDUnit) (x y : GlucoseCarbon),
    ConsecutiveGlucoseCarbons x y ∧
    IsPair a b (.glucoseCarbon unit x) (.glucoseCarbon unit y)) ∨
  (∃ unit : BetaCDUnit,
    IsPair a b (.ringOxygen unit) (.glucoseCarbon unit .c1)) ∨
  (∃ unit : BetaCDUnit,
    IsPair a b (.ringOxygen unit) (.glucoseCarbon unit .c5)) ∨
  (∃ unit : BetaCDUnit,
    IsPair a b (.glycosidicOxygen unit) (.glucoseCarbon unit .c1)) ∨
  (∃ unit : BetaCDUnit,
    IsPair a b (.glycosidicOxygen (unitAtOffset unit 6))
      (.glucoseCarbon unit .c4)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.substituentOxygen address)
      (.glucoseCarbon address.unit (hydroxylCarbon address.kind))) ∨
  (∃ (unit : BetaCDUnit) (hydrogen : CoreHydrogen),
    IsPair a b (.coreHydrogen unit hydrogen)
      (.glucoseCarbon unit (coreHydrogenParent hydrogen)))

/-- Pattern-dependent O-H and O-CH2Ph bonds. -/
def SubstituentSingleBond
    (pattern : SubstitutionPattern) (a b : Atom) : Prop :=
  (∃ address : HydroxylAddress,
    pattern address = .hydrogen ∧
    IsPair a b (.substituentOxygen address) (.hydroxylHydrogen address)) ∨
  (∃ address : HydroxylAddress,
    pattern address = .benzyl ∧
    IsPair a b (.substituentOxygen address)
      (.benzylCarbon address .methylene))

/-- Single bonds internal to every present benzyl substituent. -/
def BenzylSingleBond (a b : Atom) : Prop :=
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .methylene)
      (.benzylCarbon address .ring0)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring1)
      (.benzylCarbon address .ring2)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring3)
      (.benzylCarbon address .ring4)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring5)
      (.benzylCarbon address .ring0)) ∨
  (∃ (address : HydroxylAddress) (hydrogen : BenzylHydrogen),
    IsPair a b (.benzylHydrogen address hydrogen)
      (.benzylCarbon address (benzylHydrogenParent hydrogen)))

/-- The three alternating double bonds explicitly drawn in the source's `Bn`
legend. -/
def BenzylDoubleBond (a b : Atom) : Prop :=
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring0)
      (.benzylCarbon address .ring1)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring2)
      (.benzylCarbon address .ring3)) ∨
  (∃ address : HydroxylAddress,
    IsPair a b (.benzylCarbon address .ring4)
      (.benzylCarbon address .ring5))

/-- Exhaustive bond-order lookup.  No potential atom that is absent under the
pattern can carry a bond. -/
noncomputable def molecularBondOrder
    (pattern : SubstitutionPattern) (a b : Atom) : BondOrder := by
  classical
  exact
    if atomPresent pattern a && atomPresent pattern b then
      if BenzylDoubleBond a b then .double
      else if CoreSingleBond a b ∨
          SubstituentSingleBond pattern a b ∨ BenzylSingleBond a b then
        .single
      else .none
    else .none

/-! ## Explicit alpha-D-glucopyranoside stereochemistry -/

inductive GlucoseStereocentre where
  | c1 | c2 | c3 | c4 | c5
deriving DecidableEq, Fintype, Repr

/-- Face of the fixed chair/template plane used by the source figures. -/
inductive TemplateFace where
  | above
  | below
deriving DecidableEq, Fintype, Repr

/-- All four ligand atoms at a tetrahedral carbon plus the face of the
distinguished non-ring substituent.  The fixed ordering makes the descriptor
unambiguous without relying on a chemical-name string. -/
structure StereoDescriptor where
  centre : Atom
  firstRingLigand : Atom
  secondRingLigand : Atom
  distinguishedSubstituent : Atom
  hydrogenLigand : Atom
  distinguishedFace : TemplateFace
deriving DecidableEq, Repr

def alphaDGlucoseStereo
    (unit : BetaCDUnit) : GlucoseStereocentre → StereoDescriptor
  | .c1 =>
      { centre := .glucoseCarbon unit .c1
        firstRingLigand := .ringOxygen unit
        secondRingLigand := .glucoseCarbon unit .c2
        distinguishedSubstituent := .glycosidicOxygen unit
        hydrogenLigand := .coreHydrogen unit .c1H
        distinguishedFace := .below }
  | .c2 =>
      { centre := .glucoseCarbon unit .c2
        firstRingLigand := .glucoseCarbon unit .c1
        secondRingLigand := .glucoseCarbon unit .c3
        distinguishedSubstituent :=
          .substituentOxygen ⟨unit, .secondaryC2⟩
        hydrogenLigand := .coreHydrogen unit .c2H
        distinguishedFace := .below }
  | .c3 =>
      { centre := .glucoseCarbon unit .c3
        firstRingLigand := .glucoseCarbon unit .c2
        secondRingLigand := .glucoseCarbon unit .c4
        distinguishedSubstituent :=
          .substituentOxygen ⟨unit, .secondaryC3⟩
        hydrogenLigand := .coreHydrogen unit .c3H
        distinguishedFace := .above }
  | .c4 =>
      { centre := .glucoseCarbon unit .c4
        firstRingLigand := .glucoseCarbon unit .c3
        secondRingLigand := .glucoseCarbon unit .c5
        distinguishedSubstituent := .glycosidicOxygen (precedingUnit unit)
        hydrogenLigand := .coreHydrogen unit .c4H
        distinguishedFace := .below }
  | .c5 =>
      { centre := .glucoseCarbon unit .c5
        firstRingLigand := .glucoseCarbon unit .c4
        secondRingLigand := .ringOxygen unit
        distinguishedSubstituent := .glucoseCarbon unit .c6
        hydrogenLigand := .coreHydrogen unit .c5H
        distinguishedFace := .above }

/-- Source-side topology and stereochemical data read from the beta-CD and
alpha-D-glucopyranoside templates.  It contains no product substitution
pattern. -/
structure BetaCDTemplateSourceData where
  unitCount : ℕ
  linkageDonor : GlucoseCarbon
  linkageAcceptor : GlucoseCarbon
  cyclic : Bool
  primarySitesPerUnit : ℕ
  secondarySitesPerUnit : ℕ
  distinguishedFace : GlucoseStereocentre → TemplateFace
  provenance : Provenance
  locators : List SourceLocator

def betaCDTemplateSourceData : BetaCDTemplateSourceData :=
  { unitCount := 7
    linkageDonor := .c1
    linkageAcceptor := .c4
    cyclic := true
    primarySitesPerUnit := 1
    secondarySitesPerUnit := 2
    distinguishedFace := fun centre =>
      match centre with
      | .c1 | .c2 | .c4 => .below
      | .c3 | .c5 => .above
    provenance := .problemImage
    locators :=
      [.page2AlphaDGlucopyranosideTemplate, .page3StartingBetaCDTemplate] }

/-- Source-to-Lean bridge for the cyclic alpha-1,4 connectivity and all five
stereochemical face assignments in every one of the seven residues. -/
def SourceBetaCDTemplateSpec : Prop :=
  betaCDTemplateSourceData.unitCount = 7 ∧
  betaCDTemplateSourceData.linkageDonor = .c1 ∧
  betaCDTemplateSourceData.linkageAcceptor = .c4 ∧
  betaCDTemplateSourceData.cyclic = true ∧
  betaCDTemplateSourceData.primarySitesPerUnit = 1 ∧
  betaCDTemplateSourceData.secondarySitesPerUnit = 2 ∧
  betaCDTemplateSourceData.provenance = .problemImage ∧
  betaCDTemplateSourceData.locators =
    [.page2AlphaDGlucopyranosideTemplate, .page3StartingBetaCDTemplate] ∧
  (∀ unit : BetaCDUnit,
    CoreSingleBond (.glycosidicOxygen unit)
      (.glucoseCarbon unit betaCDTemplateSourceData.linkageDonor) ∧
    CoreSingleBond (.glycosidicOxygen unit)
      (.glucoseCarbon (unitAtOffset unit 1)
        betaCDTemplateSourceData.linkageAcceptor)) ∧
  (∀ (unit : BetaCDUnit) (centre : GlucoseStereocentre),
    (alphaDGlucoseStereo unit centre).distinguishedFace =
      betaCDTemplateSourceData.distinguishedFace centre)

theorem sourceBetaCDTemplate_spec : SourceBetaCDTemplateSpec := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro unit
    constructor
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨unit, Or.inl ⟨rfl, rfl⟩⟩)))
    · have hcycle :
          unitAtOffset (unitAtOffset unit 1) 6 = unit := by
        apply Fin.ext
        simp only [unitAtOffset]
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨unitAtOffset unit 1,
          Or.inl ⟨congrArg Atom.glycosidicOxygen hcycle.symm, rfl⟩⟩))))
  · intro unit centre
    cases centre <;> rfl

private theorem isPair_comm (a b x y : Atom) :
    IsPair a b x y ↔ IsPair b a x y := by
  constructor <;>
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    simp [IsPair]

private theorem coreSingleBond_comm (a b : Atom) :
    CoreSingleBond a b ↔ CoreSingleBond b a := by
  simp only [CoreSingleBond, isPair_comm]

private theorem substituentSingleBond_comm
    (pattern : SubstitutionPattern) (a b : Atom) :
    SubstituentSingleBond pattern a b ↔ SubstituentSingleBond pattern b a := by
  simp only [SubstituentSingleBond, isPair_comm]

private theorem benzylSingleBond_comm (a b : Atom) :
    BenzylSingleBond a b ↔ BenzylSingleBond b a := by
  simp only [BenzylSingleBond, isPair_comm]

private theorem benzylDoubleBond_comm (a b : Atom) :
    BenzylDoubleBond a b ↔ BenzylDoubleBond b a := by
  simp only [BenzylDoubleBond, isPair_comm]

private theorem isPair_self_forces_eq {a x y : Atom}
    (h : IsPair a a x y) : x = y := by
  rcases h with ⟨hax, hay⟩ | ⟨hay, hax⟩
  · exact hax.symm.trans hay
  · exact hax.symm.trans hay

private theorem benzylDoubleBond_irrefl (a : Atom) :
    ¬ BenzylDoubleBond a a := by
  intro h
  rcases h with ⟨address, hpair⟩ | ⟨address, hpair⟩ | ⟨address, hpair⟩
  all_goals
    have heq := isPair_self_forces_eq hpair
    simp at heq

private theorem coreSingleBond_irrefl (a : Atom) :
    ¬ CoreSingleBond a a := by
  intro h
  rcases h with h | h | h | h | h | h | h
  · rcases h with ⟨unit, x, y, hxy, hpair⟩
    have heq := isPair_self_forces_eq hpair
    have hcarbon : x = y := by simpa using heq
    subst y
    cases x <;> simp [ConsecutiveGlucoseCarbons] at hxy
  · rcases h with ⟨unit, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases h with ⟨unit, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases h with ⟨unit, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases h with ⟨unit, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases h with ⟨address, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases h with ⟨unit, hydrogen, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq

private theorem substituentSingleBond_irrefl
    (pattern : SubstitutionPattern) (a : Atom) :
    ¬ SubstituentSingleBond pattern a a := by
  intro h
  rcases h with ⟨address, _, hpair⟩ | ⟨address, _, hpair⟩
  all_goals
    have heq := isPair_self_forces_eq hpair
    simp at heq

private theorem benzylSingleBond_irrefl (a : Atom) :
    ¬ BenzylSingleBond a a := by
  intro h
  rcases h with h | h | h | h | h
  all_goals
    rcases h with ⟨address, hpair⟩
  · have heq := isPair_self_forces_eq hpair
    simp at heq
  · have heq := isPair_self_forces_eq hpair
    simp at heq
  · have heq := isPair_self_forces_eq hpair
    simp at heq
  · have heq := isPair_self_forces_eq hpair
    simp at heq
  · rcases hpair with ⟨hydrogen, hpair⟩
    have heq := isPair_self_forces_eq hpair
    simp at heq

private theorem coreSingleBond_glucose
    (unit : BetaCDUnit) (x y : GlucoseCarbon)
    (h : ConsecutiveGlucoseCarbons x y) :
    CoreSingleBond (.glucoseCarbon unit x) (.glucoseCarbon unit y) :=
  Or.inl ⟨unit, x, y, h, Or.inl ⟨rfl, rfl⟩⟩

private theorem coreSingleBond_c1_ringOxygen (unit : BetaCDUnit) :
    CoreSingleBond (.glucoseCarbon unit .c1) (.ringOxygen unit) :=
  Or.inr (Or.inl ⟨unit, Or.inr ⟨rfl, rfl⟩⟩)

private theorem coreSingleBond_c5_ringOxygen (unit : BetaCDUnit) :
    CoreSingleBond (.glucoseCarbon unit .c5) (.ringOxygen unit) :=
  Or.inr (Or.inr (Or.inl ⟨unit, Or.inr ⟨rfl, rfl⟩⟩))

private theorem coreSingleBond_c1_glycosidicOxygen (unit : BetaCDUnit) :
    CoreSingleBond (.glucoseCarbon unit .c1) (.glycosidicOxygen unit) :=
  Or.inr (Or.inr (Or.inr (Or.inl
    ⟨unit, Or.inr ⟨rfl, rfl⟩⟩)))

private theorem coreSingleBond_c4_precedingGlycosidicOxygen
    (unit : BetaCDUnit) :
    CoreSingleBond (.glucoseCarbon unit .c4)
      (.glycosidicOxygen (precedingUnit unit)) := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨unit, Or.inr ⟨rfl, rfl⟩⟩))))

private theorem coreSingleBond_substituentOxygen
    (address : HydroxylAddress) :
    CoreSingleBond (.glucoseCarbon address.unit (hydroxylCarbon address.kind))
      (.substituentOxygen address) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨address, Or.inr ⟨rfl, rfl⟩⟩)))))

private theorem coreSingleBond_coreHydrogen
    (unit : BetaCDUnit) (hydrogen : CoreHydrogen) :
    CoreSingleBond (.glucoseCarbon unit (coreHydrogenParent hydrogen))
      (.coreHydrogen unit hydrogen) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨unit, hydrogen, Or.inr ⟨rfl, rfl⟩⟩)))))

private theorem molecularBondOrder_eq_single_of_core
    (pattern : SubstitutionPattern) (a b : Atom)
    (ha : atomPresent pattern a = true)
    (hb : atomPresent pattern b = true)
    (hdouble : ¬ BenzylDoubleBond a b)
    (hcore : CoreSingleBond a b) :
    molecularBondOrder pattern a b = .single := by
  classical
  simp [molecularBondOrder, ha, hb, hdouble, hcore]

/-! ## A complete finite molecular structure -/

structure MolecularStructure where
  pattern : SubstitutionPattern
  present : Atom → Bool
  atom : Atom → AtomLabel
  bondOrder : Atom → Atom → BondOrder
  stereochemistry : BetaCDUnit → GlucoseStereocentre → StereoDescriptor
  bondOrder_symm : ∀ a b, bondOrder a b = bondOrder b a
  noSelfBond : ∀ a, bondOrder a a = .none
  absentAtomUnbonded : ∀ a b,
    (present a = false ∨ present b = false) → bondOrder a b = .none

/-- Generic graph construction from an arbitrary substitution pattern. -/
noncomputable def molecularStructureOfPattern
    (pattern : SubstitutionPattern) : MolecularStructure where
  pattern := pattern
  present := atomPresent pattern
  atom := atomLabel
  bondOrder := molecularBondOrder pattern
  stereochemistry := alphaDGlucoseStereo
  bondOrder_symm := by
    intro a b
    classical
    simp only [molecularBondOrder, Bool.and_comm,
      benzylDoubleBond_comm, coreSingleBond_comm,
      substituentSingleBond_comm, benzylSingleBond_comm]
  noSelfBond := by
    intro a
    classical
    simp [molecularBondOrder, benzylDoubleBond_irrefl,
      coreSingleBond_irrefl, substituentSingleBond_irrefl,
      benzylSingleBond_irrefl]
  absentAtomUnbonded := by
    intro a b h
    rcases h with ha | hb
    · simp [molecularBondOrder, ha]
    · simp [molecularBondOrder, hb]

/-- Candidate L obtained only after executing the source-bounded trace. -/
noncomputable def structureL : MolecularStructure :=
  molecularStructureOfPattern patternL

def structureElementCount (m : MolecularStructure) (element : Element) : ℕ :=
  ∑ atom : Atom,
    if m.present atom then
      if (m.atom atom).element = element then 1 else 0
    else 0

def structureFormalCharge (m : MolecularStructure) : ℤ :=
  ∑ atom : Atom, if m.present atom then (m.atom atom).formalCharge else 0

def structureRadicalElectrons (m : MolecularStructure) : ℕ :=
  ∑ atom : Atom, if m.present atom then (m.atom atom).radicalElectrons else 0

/-- A graph realizes its own reaction-derived pattern pointwise. -/
def GraphRealizesPattern (m : MolecularStructure) : Prop :=
  (∀ atom : Atom, m.present atom = atomPresent m.pattern atom) ∧
  (∀ atom : Atom, m.atom atom = atomLabel atom) ∧
  (∀ a b : Atom, m.bondOrder a b = molecularBondOrder m.pattern a b) ∧
  (∀ (unit : BetaCDUnit) (centre : GlucoseStereocentre),
    m.stereochemistry unit centre = alphaDGlucoseStereo unit centre)

/-- All 35 source-inherited stereocentres have present centres and four
present, singly bonded ligand atoms with the fixed alpha-D face descriptor. -/
def CompleteStereochemistry (m : MolecularStructure) : Prop :=
  Fintype.card (BetaCDUnit × GlucoseStereocentre) = 35 ∧
  ∀ (unit : BetaCDUnit) (centre : GlucoseStereocentre),
    let descriptor := m.stereochemistry unit centre
    m.present descriptor.centre = true ∧
    m.present descriptor.firstRingLigand = true ∧
    m.present descriptor.secondRingLigand = true ∧
    m.present descriptor.distinguishedSubstituent = true ∧
    m.present descriptor.hydrogenLigand = true ∧
    m.bondOrder descriptor.centre descriptor.firstRingLigand = .single ∧
    m.bondOrder descriptor.centre descriptor.secondRingLigand = .single ∧
    m.bondOrder descriptor.centre descriptor.distinguishedSubstituent = .single ∧
    m.bondOrder descriptor.centre descriptor.hydrogenLigand = .single ∧
    descriptor = alphaDGlucoseStereo unit centre

/-- Formula and electronic-state recount from the explicit atoms of L.
`C175H184O35` is independently obtained as the beta-CD core plus nineteen
`C7H7` benzyl substituents and two hydroxyl hydrogens. -/
def StructureLInventory (m : MolecularStructure) : Prop :=
  structureElementCount m .carbon = 175 ∧
  structureElementCount m .hydrogen = 184 ∧
  structureElementCount m .oxygen = 35 ∧
  structureFormalCharge m = 0 ∧
  structureRadicalElectrons m = 0

theorem structureL_graph_realizes_pattern :
    GraphRealizesPattern structureL := by
  simp [GraphRealizesPattern, structureL, molecularStructureOfPattern]

theorem structureL_complete_stereochemistry :
    CompleteStereochemistry structureL := by
  constructor
  · native_decide
  · intro unit centre
    cases centre with
    | c1 =>
        dsimp only [structureL, molecularStructureOfPattern,
          alphaDGlucoseStereo]
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_c1_ringOxygen unit
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c1 .c2 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_c1_glycosidicOxygen unit
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_coreHydrogen unit .c1H
    | c2 =>
        dsimp only [structureL, molecularStructureOfPattern,
          alphaDGlucoseStereo]
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c2 .c1 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c2 .c3 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_substituentOxygen
              ⟨unit, .secondaryC2⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_coreHydrogen unit .c2H
    | c3 =>
        dsimp only [structureL, molecularStructureOfPattern,
          alphaDGlucoseStereo]
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c3 .c2 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c3 .c4 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_substituentOxygen
              ⟨unit, .secondaryC3⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_coreHydrogen unit .c3H
    | c4 =>
        dsimp only [structureL, molecularStructureOfPattern,
          alphaDGlucoseStereo]
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c4 .c3 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c4 .c5 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_c4_precedingGlycosidicOxygen unit
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_coreHydrogen unit .c4H
    | c5 =>
        dsimp only [structureL, molecularStructureOfPattern,
          alphaDGlucoseStereo]
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c5 .c4 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_c5_ringOxygen unit
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_glucose unit .c5 .c6 (by
              simp [ConsecutiveGlucoseCarbons])
        · apply molecularBondOrder_eq_single_of_core
          · rfl
          · rfl
          · simp [BenzylDoubleBond, IsPair]
          · exact coreSingleBond_coreHydrogen unit .c5H

theorem structureL_inventory : StructureLInventory structureL := by
  change
    (∑ atom : Atom,
      if atomPresent patternL atom then
        if (atomLabel atom).element = .carbon then 1 else 0
      else 0) = 175 ∧
    (∑ atom : Atom,
      if atomPresent patternL atom then
        if (atomLabel atom).element = .hydrogen then 1 else 0
      else 0) = 184 ∧
    (∑ atom : Atom,
      if atomPresent patternL atom then
        if (atomLabel atom).element = .oxygen then 1 else 0
      else 0) = 35 ∧
    (∑ atom : Atom,
      if atomPresent patternL atom then (atomLabel atom).formalCharge else 0) = 0 ∧
    (∑ atom : Atom,
      if atomPresent patternL atom then (atomLabel atom).radicalElectrons else 0) = 0
  rw [patternL_eq_explicit]
  native_decide

/-! ## Filling every source template box -/

inductive TemplateBoxLabel where
  | OH
  | CH2OH
  | CH2OBn
  | OBn
deriving DecidableEq, Fintype, Repr

inductive SecondarySite where
  | c2
  | c3
deriving DecidableEq, Fintype, Repr

def secondaryHydroxylKind : SecondarySite → HydroxylKind
  | .c2 => .secondaryC2
  | .c3 => .secondaryC3

structure BetaCDTemplateDisplay where
  primaryBox : BetaCDUnit → TemplateBoxLabel
  secondaryBox : BetaCDUnit → SecondarySite → TemplateBoxLabel

def primaryBoxFromPattern
    (pattern : SubstitutionPattern) (unit : BetaCDUnit) : TemplateBoxLabel :=
  match pattern ⟨unit, .primaryC6⟩ with
  | .hydrogen => .CH2OH
  | .benzyl => .CH2OBn

def secondaryBoxFromPattern
    (pattern : SubstitutionPattern) (unit : BetaCDUnit)
    (site : SecondarySite) : TemplateBoxLabel :=
  match pattern ⟨unit, secondaryHydroxylKind site⟩ with
  | .hydrogen => .OH
  | .benzyl => .OBn

/-- The exact source-template rendering computed from `structureL.pattern`. -/
noncomputable def structureLTemplate : BetaCDTemplateDisplay :=
  { primaryBox := primaryBoxFromPattern structureL.pattern
    secondaryBox := secondaryBoxFromPattern structureL.pattern }

/-- Every one of the seven primary boxes and all fourteen secondary boxes are
covered. -/
def ExactTemplateDisplay
    (m : MolecularStructure) (display : BetaCDTemplateDisplay) : Prop :=
  (∀ unit : BetaCDUnit,
    display.primaryBox unit = primaryBoxFromPattern m.pattern unit) ∧
  (∀ (unit : BetaCDUnit) (site : SecondarySite),
    display.secondaryBox unit site =
      secondaryBoxFromPattern m.pattern unit site) ∧
  display.primaryBox unit1 = .CH2OH ∧
  display.primaryBox unit2 = .CH2OBn ∧
  display.primaryBox unit3 = .CH2OBn ∧
  display.primaryBox unit4 = .CH2OH ∧
  display.primaryBox unit5 = .CH2OBn ∧
  display.primaryBox unit6 = .CH2OBn ∧
  display.primaryBox unit7 = .CH2OBn ∧
  (∀ (unit : BetaCDUnit) (site : SecondarySite),
    display.secondaryBox unit site = .OBn)

theorem structureL_template_exact :
    ExactTemplateDisplay structureL structureLTemplate := by
  change
    (∀ unit : BetaCDUnit,
      primaryBoxFromPattern patternL unit = primaryBoxFromPattern patternL unit) ∧
    (∀ (unit : BetaCDUnit) (site : SecondarySite),
      secondaryBoxFromPattern patternL unit site =
        secondaryBoxFromPattern patternL unit site) ∧
    primaryBoxFromPattern patternL unit1 = .CH2OH ∧
    primaryBoxFromPattern patternL unit2 = .CH2OBn ∧
    primaryBoxFromPattern patternL unit3 = .CH2OBn ∧
    primaryBoxFromPattern patternL unit4 = .CH2OH ∧
    primaryBoxFromPattern patternL unit5 = .CH2OBn ∧
    primaryBoxFromPattern patternL unit6 = .CH2OBn ∧
    primaryBoxFromPattern patternL unit7 = .CH2OBn ∧
    (∀ (unit : BetaCDUnit) (site : SecondarySite),
      secondaryBoxFromPattern patternL unit site = .OBn)
  rw [patternL_eq_explicit]
  native_decide

/-! ## Assumption/target split and answer-blind result carriers -/

/-- The source-side and citation-side evidence used by the derivation.  The
candidate structure and its box assignment are absent from this proposition. -/
def ProblemEvidence : Prop :=
  SourceArrowSpec ∧
  SourceFigureRecount ∧
  SourceBetaCDTemplateSpec ∧
  ReagentCountCompatibility ∧
  SourceDirectedRuleSpec ∧
  LiteratureBridgeSpec ∧
  SourceScheduleAuthorityMatch ∧
  stagedTransformationUse = .qualitativeNamedTransformOnly

/-- The requested structural target: a source-derived trace, its complete
atom/bond/electronic graph, and all inherited stereochemistry. -/
def StructureLSpecification (m : MolecularStructure) : Prop :=
  SourceReactionTrace m.pattern ∧
  GraphRealizesPattern m ∧
  CompleteStereochemistry m ∧
  StructureLInventory m ∧
  (∀ unit : BetaCDUnit,
    m.pattern ⟨unit, .secondaryC2⟩ = .benzyl ∧
    m.pattern ⟨unit, .secondaryC3⟩ = .benzyl) ∧
  (∀ unit : BetaCDUnit,
    m.pattern ⟨unit, .primaryC6⟩ = .hydrogen ↔
      unit = unit1 ∨ unit = unit4)

/-- Raw exact-symbolic result for the sole requested output. -/
def RawResult : Prop :=
  ProblemEvidence ∧ StructureLSpecification structureL

/-- Reported result: exact symbolic reporting adds the complete template
rendering and performs no rounding. -/
def ReportedResult : Prop :=
  RawResult ∧ ExactTemplateDisplay structureL structureLTemplate

theorem structureL_raw_result : RawResult := by
  refine ⟨?_, ?_⟩
  · exact ⟨sourceArrow_spec, sourceFigure_recount, sourceBetaCDTemplate_spec,
      reagentCount_compatibility, sourceDirectedRule_spec,
      literatureBridge_spec, sourceSchedule_authorityMatch, rfl⟩
  · rcases patternL_site_classification with ⟨hsecondary, hprimary⟩
    exact ⟨sourceReactionTrace_patternL, structureL_graph_realizes_pattern,
      structureL_complete_stereochemistry, structureL_inventory,
      hsecondary, hprimary⟩

theorem structureL_reported_result : ReportedResult := by
  exact ⟨structureL_raw_result, structureL_template_exact⟩

/-- Hash-bound raw-result contract for the answer-blind solve artifact. -/
theorem structureLRawResultContract :
    ("da49df851735d40996c2e8b18d924e64e0d800010dcec2157cf44065932e761b" : String) =
        "da49df851735d40996c2e8b18d924e64e0d800010dcec2157cf44065932e761b" ∧
      IChO2026Problems.T9A5.RawResult := by
  exact ⟨rfl, structureL_raw_result⟩

/-- Hash-bound exact-symbolic reported-result contract. -/
theorem structureLReportedResultContract :
    ("db580819a56226620a55582f88f38c9a48ea9e268f280c373b7300421edf29f8" : String) =
        "db580819a56226620a55582f88f38c9a48ea9e268f280c373b7300421edf29f8" ∧
      IChO2026Problems.T9A5.ReportedResult := by
  exact ⟨rfl, structureL_reported_result⟩

end T9A5
end IChO2026Problems
