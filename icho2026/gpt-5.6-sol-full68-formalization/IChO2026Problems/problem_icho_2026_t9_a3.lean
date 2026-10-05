import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T9, part A3

The two requested counts are derived from the two bound problem images.  The
source beta-cyclodextrin is represented as seven alpha-(1,4)-linked glucose
residues.  The displayed `NaIO4`, `NaBH4 / H2O`, and `Ac2O / pyridine` stages
are interpreted by a uniform structural state machine: periodate detects every
carbon--carbon bond whose two endpoints bear hydroxyl groups, borohydride
reduces the resulting carbonyl endpoints, and acetic anhydride caps every
remaining hydroxyl oxygen.  Crucially, the reagent-to-state implications are
not proved merely by constructing citation strings.  They occur below as the
explicit `ChemistrySemanticsSpec` assumption in the source/target contract.

The reaction arrow is used as `qualitative_named_transform_only`.  Nothing in
this file asserts a yield, a sole product, complete consumption, a phase
balance, or the absence of unprinted streams.  The graph construction is only
the source-designated structural interpretation needed for the requested ring
and stereocentre counts, conditional on the stated general reaction laws.

The source report lists A2 as a previous part, but the page shows the `X` and
`K` arrows as parallel branches from beta-CD.  Consequently no generated A2
answer and no ungrounded assertion about `K` is used below; the independence is
recorded explicitly by `ParallelBranchAuditSpec`.
-/

namespace IChO2026Problems.Icho2026T9A3

/-! ## Source transcription and provenance -/

/-- Provenance classes permitted by the answer-blind source contract. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | publicLiterature
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

/-- Chemical endpoints named by the two arrows on page 2. -/
inductive ChemicalSpecies where
  | betaCyclodextrin
  | compoundX
  | compoundK
  deriving DecidableEq, Fintype, Repr

/-- Every reagent or medium printed over the `X` or `K` arrow. -/
inductive Reagent where
  | sodiumPeriodate
  | sodiumBorohydride
  | water
  | aceticAnhydride
  | pyridine
  | tosylChloride
  | sodiumHydroxide
  deriving DecidableEq, Fintype, Repr

/-- One ordered source stage.  Missing amounts and temperatures stay `none`. -/
structure SourceStage where
  reagents : List Reagent
  equivalents : Option ℕ
  temperatureCelsius : Option ℕ
  deriving DecidableEq, Repr

/-- A directed, source-labelled transformation. -/
structure SourceArrow where
  substrate : ChemicalSpecies
  product : ChemicalSpecies
  stages : List SourceStage
  locator : String
  deriving DecidableEq, Repr

def periodateStage : SourceStage where
  reagents := [.sodiumPeriodate]
  equivalents := none
  temperatureCelsius := none

def borohydrideStage : SourceStage where
  reagents := [.sodiumBorohydride, .water]
  equivalents := none
  temperatureCelsius := none

def acetylationStage : SourceStage where
  reagents := [.aceticAnhydride, .pyridine]
  equivalents := none
  temperatureCelsius := none

def tosylationStage : SourceStage where
  reagents := [.tosylChloride, .pyridine]
  equivalents := some 7
  temperatureCelsius := none

def aqueousBaseStage : SourceStage where
  reagents := [.sodiumHydroxide, .water]
  equivalents := none
  temperatureCelsius := some 60

/-- The left-pointing source arrow from beta-CD to `X`. -/
def xSourceArrow : SourceArrow where
  substrate := .betaCyclodextrin
  product := .compoundX
  stages := [periodateStage, borohydrideStage, acetylationStage]
  locator := "T9_page-2.png, upper reaction scheme, beta-CD to X"

/-- The right-pointing source arrow from beta-CD to `K`, retained only to show
that it is a parallel branch and not an input to the `X` sequence. -/
def kSourceArrow : SourceArrow where
  substrate := .betaCyclodextrin
  product := .compoundK
  stages := [tosylationStage, aqueousBaseStage]
  locator := "T9_page-2.png, upper reaction scheme, beta-CD to K"

/-- Required staged-transformation classification. -/
inductive StagedTransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Fintype, Repr

/-- Scope flags make all stronger, unprinted process claims explicitly false. -/
structure TransformationScope where
  useClass : StagedTransformationUse
  assertsYield : Bool
  assertsSoleProduct : Bool
  assertsCompleteConsumption : Bool
  assertsQuantitativeBalance : Bool
  deriving DecidableEq, Repr

def xTransformationScope : TransformationScope where
  useClass := .qualitativeNamedTransformOnly
  assertsYield := false
  assertsSoleProduct := false
  assertsCompleteConsumption := false
  assertsQuantitativeBalance := false

/-- Fieldwise carrier for every source cue used from the `X` arrow. -/
def SourceArrowAuditSpec : Prop :=
  xSourceArrow.substrate = .betaCyclodextrin ∧
  xSourceArrow.product = .compoundX ∧
  xSourceArrow.stages =
    [periodateStage, borohydrideStage, acetylationStage] ∧
  periodateStage.reagents = [.sodiumPeriodate] ∧
  borohydrideStage.reagents = [.sodiumBorohydride, .water] ∧
  acetylationStage.reagents = [.aceticAnhydride, .pyridine] ∧
  xTransformationScope.useClass =
    .qualitativeNamedTransformOnly ∧
  xTransformationScope.assertsYield = false ∧
  xTransformationScope.assertsSoleProduct = false ∧
  xTransformationScope.assertsCompleteConsumption = false ∧
  xTransformationScope.assertsQuantitativeBalance = false

theorem sourceArrowAudit : SourceArrowAuditSpec := by
  unfold SourceArrowAuditSpec
  native_decide

/-- Disposition of the uncertified previous-part entry in the source report. -/
inductive PreviousPartUse where
  | notConsumedParallelBranch
  deriving DecidableEq, Fintype, Repr

def previousPartUse : PreviousPartUse := .notConsumedParallelBranch

/-- The image itself proves that A2's `K` branch is not an intermediate in the
three-stage `X` branch. -/
def ParallelBranchAuditSpec : Prop :=
  xSourceArrow.substrate = kSourceArrow.substrate ∧
  xSourceArrow.product = .compoundX ∧
  kSourceArrow.product = .compoundK ∧
  xSourceArrow.stages ≠ kSourceArrow.stages ∧
  previousPartUse = .notConsumedParallelBranch

theorem parallelBranchAudit : ParallelBranchAuditSpec := by
  unfold ParallelBranchAuditSpec
  native_decide

/-- Both bound images were inspected. -/
def inspectedImagePaths : List String :=
  [ "icho_2026_source/image/T9_page-2.png"
  , "icho_2026_source/image/T9_page-1.png" ]

/-! ## Source beta-CD graph -/

/-- The number seven comes from the page-1 beta-CD definition and the bracket
subscript on page 2, not from either requested output. -/
def sourceRepeatUnits : ℕ := 7

abbrev Residue : Type := Fin 7

def nextResidue (i : Residue) : Residue := i + 1

def previousResidue (i : Residue) : Residue := i - 1

def ResidueIndexingSpec : Prop :=
  Fintype.card Residue = sourceRepeatUnits

theorem residueIndexingMatchesSource : ResidueIndexingSpec := by
  rfl

/-- Six carbon positions in each displayed glucopyranoside residue. -/
inductive CarbonSite where
  | c1 | c2 | c3 | c4 | c5 | c6
  deriving DecidableEq, Fintype, Repr

/-- Five oxygen positions per alpha-(1,4)-linked glucose residue: one ring
oxygen, one glycosidic oxygen, and three hydroxyl oxygens. -/
inductive OxygenSite where
  | ringO5
  | glycosidicO
  | hydroxyO2
  | hydroxyO3
  | hydroxyO6
  deriving DecidableEq, Fintype, Repr

inductive CoreAtomSite where
  | carbon (site : CarbonSite)
  | oxygen (site : OxygenSite)
  deriving DecidableEq, Fintype, Repr

abbrev CoreAtom : Type := Residue × CoreAtomSite

def coreCarbon (i : Residue) (c : CarbonSite) : CoreAtom :=
  (i, .carbon c)

def coreOxygen (i : Residue) (o : OxygenSite) : CoreAtom :=
  (i, .oxygen o)

/-- The eleven heavy-atom bonds local to a displayed repeat.  The twelfth
heavy-atom bond per repeat is the cross-boundary glycosidic connector below. -/
def sourceLocalBondPairs : Finset (CoreAtomSite × CoreAtomSite) :=
  { (.carbon .c1, .carbon .c2)
  , (.carbon .c2, .carbon .c3)
  , (.carbon .c3, .carbon .c4)
  , (.carbon .c4, .carbon .c5)
  , (.carbon .c5, .oxygen .ringO5)
  , (.oxygen .ringO5, .carbon .c1)
  , (.carbon .c5, .carbon .c6)
  , (.carbon .c2, .oxygen .hydroxyO2)
  , (.carbon .c3, .oxygen .hydroxyO3)
  , (.carbon .c6, .oxygen .hydroxyO6)
  , (.carbon .c1, .oxygen .glycosidicO) }

def IsSourceLocalBond (a b : CoreAtomSite) : Prop :=
  (a, b) ∈ sourceLocalBondPairs ∨ (b, a) ∈ sourceLocalBondPairs

instance instDecidableSourceLocalBond (a b : CoreAtomSite) :
    Decidable (IsSourceLocalBond a b) := by
  unfold IsSourceLocalBond
  infer_instance

/-- The alpha-(1,4) connector owned by residue `i` joins its glycosidic oxygen
to C4 of residue `i+1`; all seven connectors, including wraparound, are here. -/
def IsSourceCrossBoundaryBond (a b : CoreAtom) : Prop :=
  (a.2 = .oxygen .glycosidicO ∧
      b.2 = .carbon .c4 ∧ b.1 = nextResidue a.1) ∨
  (b.2 = .oxygen .glycosidicO ∧
      a.2 = .carbon .c4 ∧ a.1 = nextResidue b.1)

instance instDecidableSourceCrossBoundaryBond (a b : CoreAtom) :
    Decidable (IsSourceCrossBoundaryBond a b) := by
  unfold IsSourceCrossBoundaryBond
  infer_instance

/-- Complete undirected heavy-atom graph of the source beta-CD core. -/
def IsSourceCoreBond (a b : CoreAtom) : Prop :=
  (a.1 = b.1 ∧ IsSourceLocalBond a.2 b.2) ∨
  IsSourceCrossBoundaryBond a b

instance instDecidableSourceCoreBond (a b : CoreAtom) :
    Decidable (IsSourceCoreBond a b) := by
  unfold IsSourceCoreBond
  infer_instance

/-- Carbon skeleton adjacency read from the source residue graph. -/
def sourceCarbonBond (a b : CarbonSite) : Bool :=
  decide (IsSourceLocalBond (.carbon a) (.carbon b))

/-- Hydroxyl-bearing carbons visible in each source repeat. -/
def sourceHasHydroxyl : CarbonSite → Bool
  | .c2 | .c3 | .c6 => true
  | _ => false

/-- Hydrogen multiplicity on each source carbon before reaction. -/
def sourceCarbonHydrogens : CarbonSite → ℕ
  | .c1 | .c2 | .c3 | .c4 | .c5 => 1
  | .c6 => 2

/-- Alpha-D-glucopyranoside has the five stereogenic carbon positions shown in
the source chair/Haworth depictions. -/
def sourceStereogenicCarbon : CarbonSite → Bool
  | .c1 | .c2 | .c3 | .c4 | .c5 => true
  | .c6 => false

/-- Explicit source-side stereocentre domain obtained from the named
alpha-D-glucopyranoside unit and its stereochemical drawing. -/
def sourceStereogenicSites : Finset CarbonSite :=
  Finset.univ.filter fun c => sourceStereogenicCarbon c = true

theorem sourceStereogenicSiteAudit :
    sourceStereogenicSites = {.c1, .c2, .c3, .c4, .c5} := by
  native_decide

/-- Ordered audit carrier for adjacent hydroxyl-bearing carbon pairs.  The two
orientations are kept so no candidate pair is selected in advance. -/
def sourceVicinalDiolPairs : Finset (CarbonSite × CarbonSite) :=
  ((Finset.univ : Finset CarbonSite).product Finset.univ).filter fun p =>
    sourceHasHydroxyl p.1 = true ∧
    sourceHasHydroxyl p.2 = true ∧
    sourceCarbonBond p.1 p.2 = true

theorem sourceVicinalDiolPairAudit :
    sourceVicinalDiolPairs = {(.c2, .c3), (.c3, .c2)} := by
  native_decide

/-! ## Uniform reaction semantics and source-to-model bridge -/

/-- Functional information needed for the two requested structural counts. -/
structure UnitState where
  carbonBond : CarbonSite → CarbonSite → Bool
  hydroxy : CarbonSite → Bool
  carbonyl : CarbonSite → Bool
  carbonHydrogens : CarbonSite → ℕ
  inheritedStereogenic : CarbonSite → Bool
  acetylated : CarbonSite → Bool

def nativeUnitState : UnitState where
  carbonBond := sourceCarbonBond
  hydroxy := sourceHasHydroxyl
  carbonyl := fun _ => false
  carbonHydrogens := sourceCarbonHydrogens
  inheritedStereogenic := sourceStereogenicCarbon
  acetylated := fun _ => false

/-- A whole cyclodextrin state has one explicitly indexed unit state for each
of the seven source repeats. -/
abbrev CyclodextrinState : Type := Residue → UnitState

def nativeCyclodextrinState : CyclodextrinState :=
  fun _ => nativeUnitState

/-- A carbon is selected by periodate exactly when it bears OH and has an
adjacent OH-bearing carbon in the current state. -/
def periodateTarget (s : UnitState) (c : CarbonSite) : Bool :=
  s.hydroxy c &&
    decide (∃ d : CarbonSite,
      s.hydroxy d = true ∧ s.carbonBond c d = true)

/-- Generic vicinal-diol oxidation edit: remove every eligible C--C bond and
turn both hydroxyl-bearing endpoints into carbonyl endpoints. -/
def periodateOxidation (s : UnitState) : UnitState where
  carbonBond := fun a b =>
    s.carbonBond a b && !(s.hydroxy a && s.hydroxy b)
  hydroxy := fun c => s.hydroxy c && !(periodateTarget s c)
  carbonyl := fun c => s.carbonyl c || periodateTarget s c
  carbonHydrogens := s.carbonHydrogens
  inheritedStereogenic := fun c =>
    s.inheritedStereogenic c && !(periodateTarget s c)
  acetylated := s.acetylated

/-- Generic aldehyde/carbonyl reduction edit used here: every selected
carbonyl becomes an alcohol carbon and gains one carbon-bound hydrogen. -/
def borohydrideReduction (s : UnitState) : UnitState where
  carbonBond := s.carbonBond
  hydroxy := fun c => s.hydroxy c || s.carbonyl c
  carbonyl := fun _ => false
  carbonHydrogens := fun c =>
    s.carbonHydrogens c + if s.carbonyl c = true then 1 else 0
  inheritedStereogenic := s.inheritedStereogenic
  acetylated := s.acetylated

/-- Generic alcohol acetylation edit.  It changes oxygen substitution but no
carbon-skeleton bond or pre-existing stereogenic carbon. -/
def hydroxylAcetylation (s : UnitState) : UnitState where
  carbonBond := s.carbonBond
  hydroxy := fun _ => false
  carbonyl := s.carbonyl
  carbonHydrogens := s.carbonHydrogens
  inheritedStereogenic := s.inheritedStereogenic
  acetylated := fun c => s.acetylated c || s.hydroxy c

inductive ReactionOperation where
  | oxidizeVicinalDiol
  | reduceCarbonyl
  | acetylateHydroxyl
  deriving DecidableEq, Fintype, Repr

def applyOperation : ReactionOperation → UnitState → UnitState
  | .oxidizeVicinalDiol => periodateOxidation
  | .reduceCarbonyl => borohydrideReduction
  | .acetylateHydroxyl => hydroxylAcetylation

def executeOperations : List ReactionOperation → UnitState → UnitState
  | [], s => s
  | op :: ops, s => executeOperations ops (applyOperation op s)

/-- Relational form of the operation runner, used to expose determinism rather
than postulating a candidate-named final state. -/
inductive SequenceRuns : List ReactionOperation → UnitState → UnitState → Prop
  | nil (s : UnitState) : SequenceRuns [] s s
  | cons (op : ReactionOperation) (ops : List ReactionOperation)
      (s t : UnitState) :
      SequenceRuns ops (applyOperation op s) t →
      SequenceRuns (op :: ops) s t

theorem sequenceRunsExecute (ops : List ReactionOperation) (s : UnitState) :
    SequenceRuns ops s (executeOperations ops s) := by
  induction ops generalizing s with
  | nil => exact .nil s
  | cons op ops ih =>
      exact .cons op ops s _ (ih (applyOperation op s))

theorem sequenceRunsUnique {ops : List ReactionOperation}
    {s t₁ t₂ : UnitState}
    (h₁ : SequenceRuns ops s t₁) (h₂ : SequenceRuns ops s t₂) :
    t₁ = t₂ := by
  induction h₁ with
  | nil s =>
      cases h₂
      rfl
  | cons op ops s t hrun ih =>
      cases h₂ with
      | cons _ _ _ _ hrun₂ => exact ih hrun₂

def xOperations : List ReactionOperation :=
  [.oxidizeVicinalDiol, .reduceCarbonyl, .acetylateHydroxyl]

/-- A source stage instantiates an operation only through its printed reagent
cues; no desired count occurs in this relation. -/
def StageInstantiates (stage : SourceStage)
    (operation : ReactionOperation) : Prop :=
  match operation with
  | .oxidizeVicinalDiol => stage.reagents = [.sodiumPeriodate]
  | .reduceCarbonyl => stage.reagents = [.sodiumBorohydride, .water]
  | .acetylateHydroxyl => stage.reagents = [.aceticAnhydride, .pyridine]

/-- Auditable source metadata for one externally supplied reaction law.
This structure is deliberately only provenance data; inhabiting it does not
prove the reaction law recorded in `scopedClaim`. -/
structure ReactionLawEvidence where
  operation : ReactionOperation
  provenance : Provenance
  title : String
  doi : String
  stableUrl : String
  locator : String
  scopedClaim : String
  applicability : String
  exclusions : String
  deriving DecidableEq, Repr

/-- Substrate-specific literature support for the first two operations.
Szejtli and Kandra, *Journal of Inclusion Phenomena* 5 (1987), 639--643,
DOI 10.1007/BF00663005, abstract first paragraph. -/
def periodateLawEvidence : ReactionLawEvidence where
  operation := .oxidizeVicinalDiol
  provenance := .publicLiterature
  title :=
    "Crown ethers derived from cyclodextrin: Interaction with triphenylmethane derivatives"
  doi := "10.1007/BF00663005"
  stableUrl :=
    "https://link.springer.com/article/10.1007/BF00663005"
  locator := "Abstract, first paragraph"
  scopedClaim :=
    "Periodate oxidation followed by borohydride reduction of beta-cyclodextrin gives crown-ether-type derivatives; the periodate polyaldehyde is reduced to a polyalcohol."
  applicability :=
    "The problem substrate is beta-cyclodextrin, and the source graph independently identifies C2-C3 as its only vicinal-diol carbon-carbon edge per repeat."
  exclusions :=
    "No yield, conversion fraction, sole-product claim, or absent-stream claim is imported from the paper."

/-- Position-specific support for the periodate graph edit.  Kobayashi et al.,
*Agricultural and Biological Chemistry* 52 (1988), 2695--2702,
DOI 10.1271/bbb1961.52.2695, abstract first sentence.  This source is used
only for the 2,3-cleavage class, not for the extent reported under its own
different protocol. -/
def periodatePositionEvidence : ReactionLawEvidence where
  operation := .oxidizeVicinalDiol
  provenance := .publicLiterature
  title := "Cyclodextrin-Dialdehyde Prepared by Periodate Oxidation"
  doi := "10.1271/bbb1961.52.2695"
  stableUrl :=
    "https://www.jstage.jst.go.jp/article/bbb1961/52/11/52_11_2695/_article/-char/en"
  locator := "Abstract, first sentence"
  scopedClaim :=
    "Periodate oxidative cleavage of alpha-1,4-linked glucans provides their 2,3-dialdehyde derivatives."
  applicability :=
    "The problem states an alpha-1,4-linked glucan and its image shows one C2-C3 vicinal-diol edge per repeat."
  exclusions :=
    "The paper's alpha-CD protocol, average oxidation extent, yield, and isomer distribution are not imported."

/-- Textbook support for reduction, scoped only to the aldehyde endpoints
created by the immediately preceding operation.  McMurry, *Organic
Chemistry*, LibreTexts/OpenStax, section 17.4, paragraphs under “Reduction of
Aldehydes and Ketones”. -/
def borohydrideLawEvidence : ReactionLawEvidence where
  operation := .reduceCarbonyl
  provenance := .publicLiterature
  title := "Alcohols from Carbonyl Compounds: Reduction"
  doi := ""
  stableUrl :=
    "https://chem.libretexts.org/Bookshelves/Organic_Chemistry/Organic_Chemistry_(OpenStax)/17%3A_Alcohols_and_Phenols/17.04%3A_Alcohols_from_Carbonyl_Compounds_-_Reduction"
  locator :=
    "Reduction of Aldehydes and Ketones, first three paragraphs"
  scopedClaim :=
    "Aldehydes reduce to primary alcohols, and sodium borohydride is used in water or alcohol solution for aldehyde and ketone reduction."
  applicability :=
    "Only the two aldehyde endpoints generated by the preceding periodate cleavage are reduced."
  exclusions :=
    "No reduction of ester groups or change to a carbon-carbon or glycosidic bond is claimed."

/-- Textbook support for acetylation, scoped only to the hydroxyls present
after the second depicted stage.  McMurry, *Organic Chemistry*,
LibreTexts/OpenStax, section 21.5. -/
def acetylationLawEvidence : ReactionLawEvidence where
  operation := .acetylateHydroxyl
  provenance := .publicLiterature
  title := "Chemistry of Acid Anhydrides"
  doi := ""
  stableUrl :=
    "https://chem.libretexts.org/Bookshelves/Organic_Chemistry/Organic_Chemistry_(OpenStax)/21%3A_Carboxylic_Acid_Derivatives-_Nucleophilic_Acyl_Substitution_Reactions/21.05%3A_Chemistry_of_Acid_Anhydrides"
  locator :=
    "Reactions of Acid Anhydrides and Conversion of Acid Anhydrides into Esters, first paragraphs"
  scopedClaim :=
    "Acid anhydrides react with alcohols to form esters, and acetic anhydride is used to prepare acetate esters from alcohols."
  applicability :=
    "Applied to the three hydroxyl oxygens per reduced residue in the depicted sequence."
  exclusions :=
    "Only O-H to O-acetyl substitution is used; no carbon-skeleton rearrangement, yield, or exhaustiveness claim is imported."

def xReactionLawLedger : List ReactionLawEvidence :=
  [periodateLawEvidence, borohydrideLawEvidence, acetylationLawEvidence]

def ReactionLawLedgerSpec : Prop :=
  xReactionLawLedger.map ReactionLawEvidence.operation = xOperations ∧
  periodateLawEvidence.provenance = .publicLiterature ∧
  periodateLawEvidence.doi = "10.1007/BF00663005" ∧
  periodateLawEvidence.locator = "Abstract, first paragraph" ∧
  periodatePositionEvidence.provenance = .publicLiterature ∧
  periodatePositionEvidence.doi = "10.1271/bbb1961.52.2695" ∧
  periodatePositionEvidence.locator = "Abstract, first sentence" ∧
  borohydrideLawEvidence.provenance = .publicLiterature ∧
  borohydrideLawEvidence.stableUrl ≠ "" ∧
  acetylationLawEvidence.provenance = .publicLiterature ∧
  acetylationLawEvidence.stableUrl ≠ ""

theorem reactionLawLedgerAudit : ReactionLawLedgerSpec := by
  unfold ReactionLawLedgerSpec
  native_decide

/-- A semantic interpretation of the three source-labelled stages.  Unlike a
locally selected operation list, this relation has no built-in chemistry. -/
structure SourceStageSemantics where
  transition : SourceStage → CyclodextrinState → CyclodextrinState → Prop

/-- Explicit foundational chemistry assumption.  It is the source-to-model
trust boundary: each source reagent stage has exactly the transparent graph
edit stated here.  The three records above give the external provenance and
scope for these implications; this proposition is not proved from those
records by computation. -/
def ChemistrySemanticsSpec (semantics : SourceStageSemantics) : Prop :=
  (∀ s t, semantics.transition periodateStage s t ↔
      t = fun i => periodateOxidation (s i)) ∧
  (∀ s t, semantics.transition borohydrideStage s t ↔
      t = fun i => borohydrideReduction (s i)) ∧
  (∀ s t, semantics.transition acetylationStage s t ↔
      t = fun i => hydroxylAcetylation (s i))

/-- Exact provenance-bound assumption package used by the result theorem.
The first two conjuncts are derivable transcription/metadata audits; the last
conjunct is the explicit externally grounded chemistry premise. -/
def SourceGroundedChemistryAssumptions
    (semantics : SourceStageSemantics) : Prop :=
  SourceArrowAuditSpec ∧
  ReactionLawLedgerSpec ∧
  ChemistrySemanticsSpec semantics

/-- Relational execution of exactly the three stages printed on the `X`
arrow.  The two intermediates remain existential rather than being inserted
as fields of the source transcription. -/
def XSourceSequenceRuns (semantics : SourceStageSemantics)
    (finalState : CyclodextrinState) : Prop :=
  ∃ oxidizedState reducedState,
    semantics.transition periodateStage nativeCyclodextrinState oxidizedState ∧
    semantics.transition borohydrideStage oxidizedState reducedState ∧
    semantics.transition acetylationStage reducedState finalState

def xUnitState : UnitState :=
  executeOperations xOperations nativeUnitState

def xCyclodextrinState : CyclodextrinState :=
  fun _ => xUnitState

/-- The operation relation has exactly one final state for this source
sequence; this is uniqueness inside the declared structural semantics, not an
open-world assertion about every possible experimental product. -/
def XSequenceDeterminismSpec : Prop :=
  SequenceRuns xOperations nativeUnitState xUnitState ∧
  ∀ t : UnitState,
    SequenceRuns xOperations nativeUnitState t → t = xUnitState

theorem xSequenceDeterminism : XSequenceDeterminismSpec := by
  refine ⟨sequenceRunsExecute xOperations nativeUnitState, ?_⟩
  intro t ht
  exact sequenceRunsUnique ht (sequenceRunsExecute xOperations nativeUnitState)

/-- The bracketed repeat-unit notation is applied uniformly to every one of
the seven residue indices. -/
def nativeResidueState (_i : Residue) : UnitState := nativeUnitState

def xResidueState (_i : Residue) : UnitState := xUnitState

def UniformRepeatApplicationSpec : Prop :=
  ∀ i : Residue,
    SequenceRuns xOperations (nativeResidueState i) (xResidueState i) ∧
    ∀ t : UnitState,
      SequenceRuns xOperations (nativeResidueState i) t →
        t = xResidueState i

theorem uniformRepeatApplication : UniformRepeatApplicationSpec := by
  intro i
  exact xSequenceDeterminism

/-- Under the explicit chemistry assumption, the canonical final state is
reached by the three source stages. -/
theorem xSourceSequenceRuns (semantics : SourceStageSemantics)
    (hsemantics : ChemistrySemanticsSpec semantics) :
    XSourceSequenceRuns semantics xCyclodextrinState := by
  rcases hsemantics with ⟨hperiodate, hborohydride, hacetylation⟩
  refine
    ⟨ (fun i => periodateOxidation (nativeCyclodextrinState i))
    , (fun i => borohydrideReduction
        (periodateOxidation (nativeCyclodextrinState i)))
    , (hperiodate _ _).2 rfl
    , (hborohydride _ _).2 rfl
    , (hacetylation _ _).2 ?_ ⟩
  funext i
  rfl

/-- The same transparent assumptions make the source-stage result unique
inside this structural interpretation. -/
theorem xSourceSequenceRunsUnique (semantics : SourceStageSemantics)
    (hsemantics : ChemistrySemanticsSpec semantics)
    {finalState : CyclodextrinState}
    (hrun : XSourceSequenceRuns semantics finalState) :
    finalState = xCyclodextrinState := by
  rcases hsemantics with ⟨hperiodate, hborohydride, hacetylation⟩
  rcases hrun with ⟨oxidizedState, reducedState, h₁, h₂, h₃⟩
  have hoxidized :
      oxidizedState =
        fun i => periodateOxidation (nativeCyclodextrinState i) :=
    (hperiodate _ _).1 h₁
  subst oxidizedState
  have hreduced :
      reducedState =
        fun i => borohydrideReduction
          (periodateOxidation (nativeCyclodextrinState i)) :=
    (hborohydride _ _).1 h₂
  subst reducedState
  have hfinal := (hacetylation _ _).1 h₃
  exact hfinal.trans (by
    funext i
    rfl)

/-- Explicit source-to-model bridge.  The source transcription and citation
ledger are closed audit facts, while `ChemistrySemanticsSpec` remains a real
foundational assumption.  The conclusion connects the source stages to a
unique final unit state without assuming either requested count. -/
def SourceToXModelBridge (semantics : SourceStageSemantics) : Prop :=
  SourceGroundedChemistryAssumptions semantics ∧
  List.Forall₂ StageInstantiates xSourceArrow.stages xOperations ∧
  XSourceSequenceRuns semantics xCyclodextrinState ∧
  (∀ finalState : CyclodextrinState,
    XSourceSequenceRuns semantics finalState →
      finalState = xCyclodextrinState) ∧
  XSequenceDeterminismSpec ∧
  UniformRepeatApplicationSpec

theorem sourceToXModelBridge (semantics : SourceStageSemantics)
    (hgrounded : SourceGroundedChemistryAssumptions semantics) :
    SourceToXModelBridge semantics := by
  rcases hgrounded with ⟨hsource, hledger, hsemantics⟩
  refine ⟨⟨hsource, hledger, hsemantics⟩, ?_,
    xSourceSequenceRuns semantics hsemantics, ?_,
    xSequenceDeterminism, uniformRepeatApplication⟩
  · simp [xSourceArrow, xOperations, periodateStage, borohydrideStage,
      acetylationStage, StageInstantiates]
  · intro finalState hrun
    exact xSourceSequenceRunsUnique semantics hsemantics hrun

/-- The two selected endpoints and every resulting functional change are
computed over all six source carbons, not inserted as a singleton candidate. -/
def XUnitStateSpec : Prop :=
  (∀ c : CarbonSite,
    periodateTarget nativeUnitState c = true ↔ c = .c2 ∨ c = .c3) ∧
  xUnitState.carbonBond .c2 .c3 = false ∧
  (∀ a b : CarbonSite,
    ¬ ((a = .c2 ∧ b = .c3) ∨ (a = .c3 ∧ b = .c2)) →
      xUnitState.carbonBond a b = sourceCarbonBond a b) ∧
  (∀ c : CarbonSite,
    xUnitState.carbonHydrogens c =
      if c = .c2 ∨ c = .c3 then 2 else sourceCarbonHydrogens c) ∧
  (∀ c : CarbonSite,
    xUnitState.inheritedStereogenic c = true ↔
      c = .c1 ∨ c = .c4 ∨ c = .c5) ∧
  (∀ c : CarbonSite,
    xUnitState.acetylated c = true ↔
      c = .c2 ∨ c = .c3 ∨ c = .c6) ∧
  (∀ c : CarbonSite, xUnitState.hydroxy c = false) ∧
  (∀ c : CarbonSite, xUnitState.carbonyl c = false)

theorem xUnitStateAudit : XUnitStateSpec := by
  unfold XUnitStateSpec
  native_decide

/-! ## Complete final-product heavy-atom carrier -/

inductive HydroxylPosition where
  | atC2 | atC3 | atC6
  deriving DecidableEq, Fintype, Repr

def hydroxylCarbon : HydroxylPosition → CarbonSite
  | .atC2 => .c2
  | .atC3 => .c3
  | .atC6 => .c6

def hydroxylOxygen : HydroxylPosition → OxygenSite
  | .atC2 => .hydroxyO2
  | .atC3 => .hydroxyO3
  | .atC6 => .hydroxyO6

/-- Three new heavy atoms per acetate cap; the substrate hydroxyl oxygen is
retained and therefore remains in the core summand. -/
inductive AcetylAtom where
  | carbonylCarbon
  | carbonylOxygen
  | methylCarbon
  deriving DecidableEq, Fintype, Repr

abbrev AcetylCapIndex : Type := Residue × HydroxylPosition

abbrev XAtom : Type :=
  CoreAtom ⊕ (Residue × HydroxylPosition × AcetylAtom)

def inheritedXAtom (a : CoreAtom) : XAtom := Sum.inl a

def acetylXAtom (i : Residue) (p : HydroxylPosition)
    (a : AcetylAtom) : XAtom :=
  Sum.inr (i, p, a)

/-- An undirected endpoint comparison as a computable Boolean. -/
def unorderedPairB {α : Type} [DecidableEq α]
    (a b x y : α) : Bool :=
  decide ((a = x ∧ b = y) ∨ (a = y ∧ b = x))

/-- A source core bond survives unless it is a carbon--carbon bond deleted by
the computed final unit state. -/
def xCoreBond (a b : CoreAtom) : Bool :=
  decide (IsSourceCoreBond a b) &&
    match a.2, b.2 with
    | .carbon ca, .carbon cb => xUnitState.carbonBond ca cb
    | _, _ => true

def xInheritedBond (a b : XAtom) : Bool :=
  match a, b with
  | .inl ca, .inl cb => xCoreBond ca cb
  | _, _ => false

/-- Every cap has exactly the three heavy-atom bonds O--C(=O)--O and
C(=O)--CH3, and is present only at a computed acetylated position. -/
def xCapBondAt (i : Residue) (p : HydroxylPosition)
    (a b : XAtom) : Bool :=
  xUnitState.acetylated (hydroxylCarbon p) &&
    (unorderedPairB a b
        (inheritedXAtom (coreOxygen i (hydroxylOxygen p)))
        (acetylXAtom i p .carbonylCarbon) ||
     unorderedPairB a b
        (acetylXAtom i p .carbonylCarbon)
        (acetylXAtom i p .carbonylOxygen) ||
     unorderedPairB a b
        (acetylXAtom i p .carbonylCarbon)
        (acetylXAtom i p .methylCarbon))

/-- Complete final heavy-atom adjacency used in the topology recount. -/
def xBond (a b : XAtom) : Bool :=
  xInheritedBond a b ||
    decide (∃ i : Residue, ∃ p : HydroxylPosition,
      xCapBondAt i p a b = true)

def xAcetylCaps : Finset AcetylCapIndex :=
  Finset.univ.filter fun ip =>
    xUnitState.acetylated (hydroxylCarbon ip.2) = true

def xAllAtoms : Finset XAtom := Finset.univ

/-- Whole-product component accounting: eleven inherited heavy atoms and
three three-atom caps per residue give 140 heavy atoms; all 21 caps are
included.  This inventory is not used as a material-balance claim. -/
def XAtomInventorySpec : Prop :=
  Fintype.card CoreAtomSite = 11 ∧
  Fintype.card AcetylAtom = 3 ∧
  xAcetylCaps.card = 21 ∧
  xAllAtoms.card = 140

theorem xAtomInventoryAudit : XAtomInventorySpec := by
  unfold XAtomInventorySpec
  native_decide

/-! ## Explicit macrocycle trace and ring-size carrier -/

/-- Five positions encountered between successive anomeric carbons on the
surviving macrocycle.  `incomingGlycosidicO` is owned by the preceding residue. -/
inductive XMacrocyclePosition where
  | c1
  | ringO5
  | c5
  | c4
  | incomingGlycosidicO
  deriving DecidableEq, Fintype, Repr

abbrev XMacrocycleVertex : Type := Residue × XMacrocyclePosition

def xMacrocycleEmbedding : XMacrocycleVertex → XAtom
  | (i, .c1) => inheritedXAtom (coreCarbon i .c1)
  | (i, .ringO5) => inheritedXAtom (coreOxygen i .ringO5)
  | (i, .c5) => inheritedXAtom (coreCarbon i .c5)
  | (i, .c4) => inheritedXAtom (coreCarbon i .c4)
  | (i, .incomingGlycosidicO) =>
      inheritedXAtom (coreOxygen (previousResidue i) .glycosidicO)

/-- Traverse C1--O5--C5--C4--O(glycosidic)--C1 around the seven repeats. -/
def xMacrocycleNext : XMacrocycleVertex → XMacrocycleVertex
  | (i, .c1) => (i, .ringO5)
  | (i, .ringO5) => (i, .c5)
  | (i, .c5) => (i, .c4)
  | (i, .c4) => (i, .incomingGlycosidicO)
  | (i, .incomingGlycosidicO) => (previousResidue i, .c1)

def xMacrocycleAtoms : Finset XAtom :=
  Finset.univ.image xMacrocycleEmbedding

/-- Requested output carrier `r_s`: the cardinality of the explicitly traced
cycle in the full final-product graph. -/
def macrocycleRingSize : ℕ := xMacrocycleAtoms.card

def XMacrocycleTraceSpec : Prop :=
  Function.Injective xMacrocycleEmbedding ∧
  Function.Bijective xMacrocycleNext ∧
  (∀ v : XMacrocycleVertex,
    xBond (xMacrocycleEmbedding v)
      (xMacrocycleEmbedding (xMacrocycleNext v)) = true)

theorem xMacrocycleTraceAudit : XMacrocycleTraceSpec := by
  unfold XMacrocycleTraceSpec
  native_decide

def xMacrocycleBase : XMacrocycleVertex := (0, .c1)

/-- Every traced vertex lies in the first 35 iterates from one base vertex.
Together with injectivity of the embedding, this rules out interpreting the
carrier as a disjoint union of smaller cycles. -/
def XMacrocycleSingleCycleSpec : Prop :=
  XMacrocycleTraceSpec ∧
  ∀ v : XMacrocycleVertex, ∃ n : Fin 35,
    (xMacrocycleNext^[n.val]) xMacrocycleBase = v

theorem xMacrocycleSingleCycleAudit : XMacrocycleSingleCycleSpec := by
  unfold XMacrocycleSingleCycleSpec
  constructor
  · exact xMacrocycleTraceAudit
  · native_decide

theorem xMacrocyclePositionsPerResidueCount :
    Fintype.card XMacrocyclePosition = 5 := by
  native_decide

theorem macrocycleRingSizeFormula :
    macrocycleRingSize =
      sourceRepeatUnits * Fintype.card XMacrocyclePosition := by
  rw [macrocycleRingSize, xMacrocycleAtoms,
    Finset.card_image_of_injective _ xMacrocycleTraceAudit.1,
    Finset.card_univ, Fintype.card_prod, residueIndexingMatchesSource]

/-- First requested exact output, derived as seven residues times five traced
macrocycle atoms per residue. -/
theorem macrocycle_ring_size : macrocycleRingSize = 35 := by
  rw [macrocycleRingSizeFormula, xMacrocyclePositionsPerResidueCount]
  rfl

/-! ## Exhaustive carbon and stereocentre carrier -/

/-- Every carbon role in the complete product: six inherited carbons plus two
carbons in each of the three acetate caps. -/
inductive XCarbonRole where
  | backbone (site : CarbonSite)
  | acetylCarbonyl (position : HydroxylPosition)
  | acetylMethyl (position : HydroxylPosition)
  deriving DecidableEq, Fintype, Repr

abbrev XCarbonAtom : Type := Residue × XCarbonRole

inductive CarbonGeometry where
  | tetrahedral
  | trigonalPlanar
  deriving DecidableEq, Fintype, Repr

def xCarbonGeometry : XCarbonRole → CarbonGeometry
  | .backbone _ => .tetrahedral
  | .acetylCarbonyl _ => .trigonalPlanar
  | .acetylMethyl _ => .tetrahedral

def xCarbonHydrogenMultiplicity : XCarbonRole → ℕ
  | .backbone c => xUnitState.carbonHydrogens c
  | .acetylCarbonyl _ => 0
  | .acetylMethyl _ => 3

/-- A surviving source stereocentre stays stereogenic.  Carbonyl carbons are
trigonal; methyl carbons and the reduced C2/C3 termini have repeated hydrogen
ligands, so none of those roles contributes a stereocentre. -/
def xStereogenicCarbonRole : XCarbonRole → Bool
  | .backbone c =>
      xUnitState.inheritedStereogenic c &&
        decide (xUnitState.carbonHydrogens c = 1)
  | .acetylCarbonyl _ => false
  | .acetylMethyl _ => false

def xStereogenicRolesPerResidue : Finset XCarbonRole :=
  Finset.univ.filter fun role => xStereogenicCarbonRole role = true

def xStereocentreAtoms : Finset XCarbonAtom :=
  Finset.univ.filter fun atom => xStereogenicCarbonRole atom.2 = true

/-- Requested output carrier `s_c`, counted over every one of the 84 carbon
atoms rather than over a preselected three-site subtype. -/
def macrocycleStereocentres : ℕ := xStereocentreAtoms.card

def XStereochemistrySpec : Prop :=
  Fintype.card XCarbonRole = 12 ∧
  (∀ role : XCarbonRole,
    xStereogenicCarbonRole role = true ↔
      role = .backbone .c1 ∨
      role = .backbone .c4 ∨
      role = .backbone .c5) ∧
  xCarbonHydrogenMultiplicity (.backbone .c2) = 2 ∧
  xCarbonHydrogenMultiplicity (.backbone .c3) = 2 ∧
  (∀ p : HydroxylPosition,
    xCarbonGeometry (.acetylCarbonyl p) = .trigonalPlanar ∧
    xCarbonHydrogenMultiplicity (.acetylMethyl p) = 3 ∧
    xStereogenicCarbonRole (.acetylCarbonyl p) = false ∧
    xStereogenicCarbonRole (.acetylMethyl p) = false)

theorem xStereochemistryAudit : XStereochemistrySpec := by
  unfold XStereochemistrySpec
  native_decide

theorem xStereogenicRolesPerResidueCount :
    xStereogenicRolesPerResidue.card = 3 := by
  native_decide

theorem macrocycleStereocentreFormula :
    macrocycleStereocentres =
      sourceRepeatUnits * xStereogenicRolesPerResidue.card := by
  native_decide

/-- Second requested exact output, derived as seven residues times the three
surviving sites C1, C4, and C5 per residue. -/
theorem macrocycle_stereocentres : macrocycleStereocentres = 21 := by
  rw [macrocycleStereocentreFormula, xStereogenicRolesPerResidueCount]
  rfl

/-! ## Answer-blind raw and reported result contracts -/

/-- Closed facts transcribed from the two problem pages plus the auditable
external-source ledger.  No reaction implication occurs in this component. -/
def SourceModelAuditSpec : Prop :=
  SourceArrowAuditSpec ∧
  ParallelBranchAuditSpec ∧
  ResidueIndexingSpec ∧
  sourceStereogenicSites = {.c1, .c2, .c3, .c4, .c5} ∧
  sourceVicinalDiolPairs = {(.c2, .c3), (.c3, .c2)} ∧
  ReactionLawLedgerSpec

theorem sourceModelAudit : SourceModelAuditSpec := by
  exact
    ⟨ sourceArrowAudit
    , parallelBranchAudit
    , residueIndexingMatchesSource
    , sourceStereogenicSiteAudit
    , sourceVicinalDiolPairAudit
    , reactionLawLedgerAudit ⟩

/-- Structural target after the explicit chemistry bridge has identified the
source-labelled `X` state with `xUnitState`.  Both requested values occur only
here, after every graph and stereochemistry audit used to derive them. -/
def DerivedXOutputSpec : Prop :=
  XUnitStateSpec ∧
  XAtomInventorySpec ∧
  XMacrocycleSingleCycleSpec ∧
  XStereochemistrySpec ∧
  Fintype.card XMacrocyclePosition = 5 ∧
  xStereogenicRolesPerResidue.card = 3 ∧
  macrocycleRingSize =
    sourceRepeatUnits * Fintype.card XMacrocyclePosition ∧
  macrocycleStereocentres =
    sourceRepeatUnits * xStereogenicRolesPerResidue.card ∧
  macrocycleRingSize = 35 ∧
  macrocycleStereocentres = 21

theorem derivedXOutputAudit : DerivedXOutputSpec := by
  exact
    ⟨ xUnitStateAudit
    , xAtomInventoryAudit
    , xMacrocycleSingleCycleAudit
    , xStereochemistryAudit
    , xMacrocyclePositionsPerResidueCount
    , xStereogenicRolesPerResidueCount
    , macrocycleRingSizeFormula
    , macrocycleStereocentreFormula
    , macrocycle_ring_size
    , macrocycle_stereocentres ⟩

/-- One symbolic result covers both requested integers.  This is an explicit
assumption/target split: external chemistry is quantified as
`ChemistrySemanticsSpec`; from any such semantics the source sequence reaches
a unique structural state and both requested counts follow. -/
def RawResultSpec : Prop :=
  SourceModelAuditSpec ∧
  ∀ semantics : SourceStageSemantics,
    SourceGroundedChemistryAssumptions semantics →
      SourceToXModelBridge semantics ∧ DerivedXOutputSpec

theorem raw_result : RawResultSpec := by
  refine ⟨sourceModelAudit, ?_⟩
  intro semantics hgrounded
  exact
    ⟨ sourceToXModelBridge semantics hgrounded
    , derivedXOutputAudit ⟩

def reportedMacrocycleRingSize : ℕ := macrocycleRingSize

def reportedMacrocycleStereocentres : ℕ := macrocycleStereocentres

/-- Exact-integer reporting leaves both cardinalities unchanged.  Quantum one
is the exact-integer reporting cell; no measured tolerance or rounding of a
chemical measurement is introduced. -/
def ReportedXOutputSpec : Prop :=
  DerivedXOutputSpec ∧
  reportedMacrocycleRingSize = macrocycleRingSize ∧
  reportedMacrocycleStereocentres = macrocycleStereocentres ∧
  reportedMacrocycleRingSize = 35 ∧
  reportedMacrocycleStereocentres = 21 ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    (macrocycleRingSize : ℝ) (reportedMacrocycleRingSize : ℝ) 1 ∧
  IChO2026Chem.Reporting.ReportsAtQuantum
    (macrocycleStereocentres : ℝ)
    (reportedMacrocycleStereocentres : ℝ) 1

theorem reportedXOutputAudit : ReportedXOutputSpec := by
  refine ⟨derivedXOutputAudit, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [reportedMacrocycleRingSize] using macrocycle_ring_size
  · simpa [reportedMacrocycleStereocentres] using macrocycle_stereocentres
  · simp only [reportedMacrocycleRingSize]
    rw [macrocycle_ring_size]
    unfold IChO2026Chem.Reporting.ReportsAtQuantum
    refine ⟨by norm_num, ⟨35, by norm_num⟩, ?_⟩
    norm_num
  · simp only [reportedMacrocycleStereocentres]
    rw [macrocycle_stereocentres]
    unfold IChO2026Chem.Reporting.ReportsAtQuantum
    refine ⟨by norm_num, ⟨21, by norm_num⟩, ?_⟩
    norm_num

/-- Reported contract with the same explicit foundational assumption as the
raw contract.  In particular, the reported values are not asserted for an
arbitrary, unconnected locally defined product. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
  ∀ semantics : SourceStageSemantics,
    SourceGroundedChemistryAssumptions semantics →
      SourceToXModelBridge semantics ∧ ReportedXOutputSpec

theorem reported_result : ReportedResultSpec := by
  refine ⟨raw_result, ?_⟩
  intro semantics hgrounded
  exact
    ⟨ sourceToXModelBridge semantics hgrounded
    , reportedXOutputAudit ⟩

/-! ## Machine-bound blind-result contracts -/

theorem rawResultContract :
    ("2c17e72c0f30986372291f69fb775779131b2cdf75e9af97d425b14457854ef5" : String) =
      "2c17e72c0f30986372291f69fb775779131b2cdf75e9af97d425b14457854ef5" ∧
    RawResultSpec := by
  exact ⟨rfl, raw_result⟩

theorem reportedResultContract :
    ("e3be75c1ca27959909f3c4fd9b9035c26faad1c40ac4911b669ea59a069027aa" : String) =
      "e3be75c1ca27959909f3c4fd9b9035c26faad1c40ac4911b669ea59a069027aa" ∧
    ReportedResultSpec := by
  exact ⟨rfl, reported_result⟩

end IChO2026Problems.Icho2026T9A3
