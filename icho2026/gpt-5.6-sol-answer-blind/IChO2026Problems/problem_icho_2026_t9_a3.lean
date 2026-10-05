import Mathlib
import IChO2026Chem.Core

/-!
# IChO 2026, problem T9-A3: periodate opening of beta-cyclodextrin

The source gives a cyclic heptamer of alpha-1,4-linked D-glucopyranoside
residues and the directed sequence `NaIO4`, then `NaBH4/H2O`, then
`Ac2O/pyridine`, leading to `X`.  This file classifies that arrow as
`qualitative_named_transform_only`: it audits a compatible product graph and
chirality pattern, but asserts no yield, completion, sole-product status,
phase, coefficient, or absent byproduct.

The graph rewrite is grounded by four source-scoped generic bridges whose
full locators and applicability conditions are encoded below: periodate
cleavage of an accessible 2,3-diol in a 1→4-linked glucopyranosyl residue;
NaBH4 reduction of aldehydes to primary alcohols; O-acetylation of alcohols by
acetic anhydride; and the four-different-substituent stereocentre criterion.
-/

namespace IChO2026Problems.ProblemIcho2026T9A3

/-- Permitted origins for the finite structural data used in this target. -/
inductive EvidenceProvenance
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Authority class of a generic source-to-model chemistry bridge. -/
inductive BridgeAuthority
  | peerReviewedLiterature
  | authoritativeTextbook
  deriving DecidableEq, Repr

/-- Auditable metadata for a generic chemistry bridge.

This is provenance data, not a freely selectable chemical proposition.  The
corresponding graph and ligand rewrites, together with their source-side
applicability checks, occur later in the file.
-/
structure LiteratureBridge where
  authority : BridgeAuthority
  title : String
  persistentLocator : String
  exactLocator : String
  scopedClaim : String
  applicabilityConditions : List String
  deriving Repr

/-- Periodate rule used only at the displayed C2--C3 vicinal diol. -/
def periodateLiteratureBridge : LiteratureBridge :=
  { authority := .peerReviewedLiterature
    title := "Polysaccharide Aldehydes and Ketones: Synthesis and Reactivity"
    persistentLocator := "https://doi.org/10.1021/acs.biomac.4c00020"
    exactLocator := "Section 2.1.1 and Scheme 2(a)"
    scopedClaim :=
      "Periodate cleaves an accessible vicinal 2,3-diol of a 1→4-linked glucopyranosyl residue to two aldehydes and opens that monosaccharide ring."
    applicabilityConditions :=
      [ "a polysaccharide residue bearing a vicinal diol"
      , "equatorial-equatorial or axial-equatorial hydroxyl geometry, not opposing diaxial"
      , "a 1→4-linked glucopyranosyl residue for the Scheme 2(a) instantiation" ] }

/-- Sodium-borohydride rule used only for the two aldehydes made above. -/
def borohydrideLiteratureBridge : LiteratureBridge :=
  { authority := .authoritativeTextbook
    title := "Organic Chemistry"
    persistentLocator :=
      "https://openstax.org/books/organic-chemistry/pages/17-4-alcohols-from-carbonyl-compounds-reduction"
    exactLocator := "Section 17.4, Reduction of Aldehydes and Ketones"
    scopedClaim :=
      "Aldehydes are reduced to primary alcohols; sodium borohydride is a standard reagent and may be used in water."
    applicabilityConditions :=
      [ "the substrate functional group is an aldehyde"
      , "sodium borohydride is the reducing reagent"
      , "water is an admitted solvent" ] }

/-- Acetic-anhydride rule used only to audit possible acetate substituents. -/
def acetylationLiteratureBridge : LiteratureBridge :=
  { authority := .authoritativeTextbook
    title := "Organic Chemistry"
    persistentLocator :=
      "https://openstax.org/books/organic-chemistry/pages/21-5-chemistry-of-acid-anhydrides"
    exactLocator := "Section 21.5, Conversion of Acid Anhydrides into Esters"
    scopedClaim :=
      "Acetic anhydride converts alcohols into acetate esters by O-acylation."
    applicabilityConditions :=
      [ "an alcohol oxygen is present"
      , "acetic anhydride is the acylating reagent" ] }

/-- Criterion used for every carbon in the product audit envelope. -/
def stereocentreLiteratureBridge : LiteratureBridge :=
  { authority := .authoritativeTextbook
    title := "Organic Chemistry"
    persistentLocator :=
      "https://openstax.org/books/organic-chemistry/pages/5-1-enantiomers-and-the-tetrahedral-carbon"
    exactLocator := "Section 5.1, Enantiomers and the Tetrahedral Carbon"
    scopedClaim :=
      "A tetrahedral carbon with four different substituents is stereogenic; a CH2XY carbon is not handed."
    applicabilityConditions :=
      [ "the candidate atom is tetrahedral"
      , "the complete four-substituent audit is used" ] }

/-- The problem text and the page-1 beta-CD drawing both specify seven units. -/
def betaCDUnitCount : ℕ := 7

/-- One of the seven glucopyranoside residues in beta-cyclodextrin. -/
abbrev Residue := Fin betaCDUnitCount

/-- Reagents explicitly printed over or under the three stages of the arrow to `X`. -/
inductive Reagent
  | sodiumPeriodate
  | sodiumBorohydride
  | water
  | aceticAnhydride
  | pyridine
  deriving DecidableEq, Repr

/-- Structural effects used from the displayed reaction sequence.

The periodate step opens the C2--C3 vicinal diol, borohydride converts the two
resulting aldehyde termini to primary alcohol termini, and acetylation changes
hydroxy substituents without changing the carbon/ether macrocycle skeleton.
-/
inductive StructuralOperation
  | cleaveC2C3VicinalDiol
  | reduceAldehydeTerminiToPrimaryAlcohols
  | acetylateHydroxyGroups
  deriving DecidableEq, Repr

/-- The ordered operations represented by the three source-arrow stages. -/
def xReactionOperations : List StructuralOperation :=
  [ .cleaveC2C3VicinalDiol
  , .reduceAldehydeTerminiToPrimaryAlcohols
  , .acetylateHydroxyGroups ]

/-- The reagents printed for each source-arrow stage, in order. -/
def xReactionReagents : List (Finset Reagent) :=
  [ {.sodiumPeriodate}
  , {.sodiumBorohydride, .water}
  , {.aceticAnhydride, .pyridine} ]

/-- Classification required by the chemistry audit for the depicted arrow. -/
inductive TransformationUse
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

/-- T9-A3 uses the arrow only to determine compatible connectivity and chirality. -/
def xTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-- Named roles and direction of the left-pointing source arrow. -/
inductive ArrowSpecies
  | betaCyclodextrin
  | productX
  deriving DecidableEq, Repr

/-- Exact source-arrow carrier required by the qualitative transformation audit. -/
structure SourceArrow where
  imagePath : String
  input : ArrowSpecies
  output : ArrowSpecies
  reagents : List (Finset Reagent)
  operations : List StructuralOperation
  use : TransformationUse

def xSourceArrow : SourceArrow :=
  { imagePath := "icho_2026_source/image/T9_page-2.png"
    input := .betaCyclodextrin
    output := .productX
    reagents := xReactionReagents
    operations := xReactionOperations
    use := .qualitativeNamedTransformOnly }

/-! ## Source-derived macrocycle topology -/

/-- Sites in one repeated portion of the cyclodextrin cycle network.

The six sites `c1`--`o5` form the glucopyranose ring.  `glycosidicO` is the
alpha-1,4 oxygen connecting C1 of one residue to C4 of the next residue.
-/
inductive CDNetworkSite
  | c1
  | c2
  | c3
  | c4
  | c5
  | o5
  | glycosidicO
  deriving DecidableEq, Fintype, Repr

/-- C2 and C3 form the other arc of each pyranose ring; they are not atoms of
the large alpha-1,4 macrocycle even before the reaction.  Periodate deletes
their mutual bond, not either atom. -/
def c2c3PyranoseArcSites : Finset CDNetworkSite :=
  {.c2, .c3}

/-- The five positions encountered once per residue on the retained macrocycle. -/
inductive XRingSite
  | c1
  | glycosidicO
  | c4
  | c5
  | o5
  deriving DecidableEq, Fintype, Repr

/-- Embed a large-macrocycle position into the original cyclodextrin network. -/
def XRingSite.toNetworkSite : XRingSite → CDNetworkSite
  | .c1 => .c1
  | .glycosidicO => .glycosidicO
  | .c4 => .c4
  | .c5 => .c5
  | .o5 => .o5

/-- Source-topology decomposition: the large-ring positions are exactly the
five local sites outside the C2/C3 pyranose arc.  This theorem does not delete
C2 or C3 from the product. -/
theorem macrocycleSites_are_complementary_arc :
    Set.range XRingSite.toNetworkSite =
      {s : CDNetworkSite | s ∉ c2c3PyranoseArcSites} := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    fin_cases x <;>
      simp [XRingSite.toNetworkSite, c2c3PyranoseArcSites]
  · intro hs
    fin_cases s
    · exact ⟨.c1, rfl⟩
    · simp [c2c3PyranoseArcSites] at hs
    · simp [c2c3PyranoseArcSites] at hs
    · exact ⟨.c4, rfl⟩
    · exact ⟨.c5, rfl⟩
    · exact ⟨.o5, rfl⟩
    · exact ⟨.glycosidicO, rfl⟩

/-- Atoms in the retained macrocycle of `X`, indexed by residue and local site. -/
abbrev XMacrocycleAtom := Residue × XRingSite

/-- Advance to the next beta-CD residue, cyclically. -/
def nextResidue (i : Residue) : Residue :=
  ⟨(i.val + 1) % betaCDUnitCount,
    Nat.mod_lt _ (by norm_num [betaCDUnitCount])⟩

/-- Atoms of the source carbohydrate cycle network. -/
abbrev NetworkAtom := Residue × CDNetworkSite

/-- Undirected bonds drawn within one glucopyranoside repeat. -/
def sameResidueNetworkBond : CDNetworkSite → CDNetworkSite → Bool
  | .c1, .c2 | .c2, .c1
  | .c2, .c3 | .c3, .c2
  | .c3, .c4 | .c4, .c3
  | .c4, .c5 | .c5, .c4
  | .c5, .o5 | .o5, .c5
  | .o5, .c1 | .c1, .o5
  | .c1, .glycosidicO | .glycosidicO, .c1 => true
  | _, _ => false

/-- Complete source network, including the cross-boundary
`glycosidicO(i)--C4(i+1)` connector. -/
def betaCDNetworkBond (a b : NetworkAtom) : Bool :=
  (decide (a.1 = b.1) && sameResidueNetworkBond a.2 b.2) ||
    (decide (a.2 = .glycosidicO) && decide (b.2 = .c4) &&
      decide (b.1 = nextResidue a.1)) ||
    (decide (b.2 = .glycosidicO) && decide (a.2 = .c4) &&
      decide (a.1 = nextResidue b.1))

/-- The only core bond selected by the scoped periodate rule. -/
def isC2C3Bond (a b : NetworkAtom) : Bool :=
  decide (a.1 = b.1) &&
    ((decide (a.2 = .c2) && decide (b.2 = .c3)) ||
      (decide (a.2 = .c3) && decide (b.2 = .c2)))

/-- Qualitative periodate graph rewrite: break C2--C3 and preserve every
other bond of the carbohydrate cycle network. -/
def periodateOpenedNetworkBond (a b : NetworkAtom) : Bool :=
  betaCDNetworkBond a b && !isC2C3Bond a b

/-- Stages at which the carbohydrate core is inspected. -/
inductive ReactionStage
  | source
  | afterPeriodate
  | afterBorohydride
  | afterAcetylation
  deriving DecidableEq, Fintype, Repr

/-- Reduction and O-acetylation alter functional groups but not the opened
carbohydrate network. -/
def stageNetworkBond : ReactionStage → NetworkAtom → NetworkAtom → Bool
  | .source => betaCDNetworkBond
  | .afterPeriodate | .afterBorohydride | .afterAcetylation =>
      periodateOpenedNetworkBond

/-- The source image shows secondary hydroxyls at C2 and C3. -/
def sourceSecondaryHydroxylSites : Finset CDNetworkSite :=
  {.c2, .c3}

/-- Geometry condition required by the peer-reviewed periodate bridge. -/
inductive VicinalDiolGeometry
  | equatorialEquatorial
  | axialEquatorial
  | opposingDiaxial
  deriving DecidableEq, Fintype, Repr

/-- Reconstructed from the favorable chair depicted in the source template. -/
def sourceC2C3DiolGeometry : VicinalDiolGeometry :=
  .equatorialEquatorial

/-- The earlier chair task is rederived only to the extent used here.  No
answer about `K` is imported. -/
structure PreviousPartRelevantInput : Prop where
  sevenResidues : betaCDUnitCount = 7
  c2c3Geometry : sourceC2C3DiolGeometry = .equatorialEquatorial

theorem previousPartA2_reconstructed : PreviousPartRelevantInput := by
  exact ⟨rfl, rfl⟩

/-- All applicability conditions for the scoped periodate rule, tied to
problem-side topology, hydroxyl, geometry, reagent, and direction carriers. -/
structure PeriodateApplicability : Prop where
  directedArrow :
    xSourceArrow.input = .betaCyclodextrin ∧
      xSourceArrow.output = .productX
  orderedReagents : xSourceArrow.reagents = xReactionReagents
  c2Hydroxyl : .c2 ∈ sourceSecondaryHydroxylSites
  c3Hydroxyl : .c3 ∈ sourceSecondaryHydroxylSites
  vicinalBond : ∀ i : Residue,
    betaCDNetworkBond (i, .c2) (i, .c3) = true
  admittedGeometry : sourceC2C3DiolGeometry ≠ .opposingDiaxial

theorem periodate_applicable : PeriodateApplicability := by
  refine
    { directedArrow := ⟨rfl, rfl⟩
      orderedReagents := rfl
      c2Hydroxyl := by simp [sourceSecondaryHydroxylSites]
      c3Hydroxyl := by simp [sourceSecondaryHydroxylSites]
      vicinalBond := ?_
      admittedGeometry := by decide }
  intro i
  simp [betaCDNetworkBond, sameResidueNetworkBond]

/-- The directed successor around the retained ring.

Within a residue the path is C4--C5--O5--C1--glycosidic O; the glycosidic
oxygen then leads to C4 of the next residue.  This explicitly records the
cross-boundary bond in the bracketed seven-unit source drawing.
-/
def nextRingAtom : XMacrocycleAtom → XMacrocycleAtom
  | (i, .c1) => (i, .glycosidicO)
  | (i, .glycosidicO) => (nextResidue i, .c4)
  | (i, .c4) => (i, .c5)
  | (i, .c5) => (i, .o5)
  | (i, .o5) => (i, .c1)

/-- Embed a large-ring atom into the complete source/product network. -/
def XMacrocycleAtom.toNetworkAtom : XMacrocycleAtom → NetworkAtom
  | (i, s) => (i, s.toNetworkSite)

/-- Every successor edge is present before periodate and after every displayed
stage, so the generic C2--C3 cleavage does not sever the large ring. -/
theorem xMacrocycle_successor_bond :
    ∀ stage : ReactionStage, ∀ a : XMacrocycleAtom,
      stageNetworkBond stage a.toNetworkAtom
        (nextRingAtom a).toNetworkAtom = true := by
  decide

/-- Direct disjointness certificate for the periodate-selected edges. -/
theorem periodate_cleavage_disjoint_from_macrocycle :
    ∀ a : XMacrocycleAtom,
      isC2C3Bond a.toNetworkAtom (nextRingAtom a).toNetworkAtom = false := by
  decide

/-- Undirected bonding relation on the retained ring. -/
def XRingBond (a b : XMacrocycleAtom) : Prop :=
  nextRingAtom a = b ∨ nextRingAtom b = a

/-- A finite successor system consists of one cycle when its successor is a
bijection and every vertex occurs in the bounded orbit of every other vertex. -/
def IsSingleCycle {α : Type} [Fintype α] (next : α → α) : Prop :=
  Function.Bijective next ∧
    ∀ a b : α, ∃ n : ℕ, n < Fintype.card α ∧ (next^[n]) a = b

/-- The source-derived successor traverses one macrocycle, rather than several
disconnected smaller rings. -/
theorem xMacrocycle_singleCycle : IsSingleCycle nextRingAtom := by
  have everyVertexOccurs :
      ∀ a b : XMacrocycleAtom,
        ∃ n : Fin (Fintype.card XMacrocycleAtom),
          (nextRingAtom^[n.val]) a = b := by
    set_option maxRecDepth 2000 in
      decide
  constructor
  · decide
  · intro a b
    obtain ⟨n, hn⟩ := everyVertexOccurs a b
    exact ⟨n.val, n.isLt, hn⟩

/-- The requested ring size is the number of atoms in that single cycle. -/
def macrocycleRingSize : ℕ := Fintype.card XMacrocycleAtom

/-! ## Source-derived functional-group and stereocentre audit -/

/-- Carbon positions in one glucopyranoside residue. -/
inductive CarbonSite
  | c1 | c2 | c3 | c4 | c5 | c6
  deriving DecidableEq, Fintype, Repr

/-- Functional states needed to connect the three generic reaction bridges. -/
inductive CarbonFunctionalState
  | acetalOrEtherBearing
  | secondaryAlcohol
  | primaryAlcohol
  | aldehyde
  | alcoholOrAcetateEster
  deriving DecidableEq, Fintype, Repr

def sourceCarbonState : CarbonSite → CarbonFunctionalState
  | .c2 | .c3 => .secondaryAlcohol
  | .c6 => .primaryAlcohol
  | .c1 | .c4 | .c5 => .acetalOrEtherBearing

/-- The final state deliberately leaves O-acetylation extent unknown; the
subsequent carbon envelope proves that every possible acetate is achiral. -/
def stageCarbonState : ReactionStage → CarbonSite → CarbonFunctionalState
  | .source, s => sourceCarbonState s
  | .afterPeriodate, .c2 | .afterPeriodate, .c3 => .aldehyde
  | .afterPeriodate, s => sourceCarbonState s
  | .afterBorohydride, .c2 | .afterBorohydride, .c3 => .primaryAlcohol
  | .afterBorohydride, s => sourceCarbonState s
  | .afterAcetylation, .c2
  | .afterAcetylation, .c3
  | .afterAcetylation, .c6 => .alcoholOrAcetateEster
  | .afterAcetylation, s => sourceCarbonState s

/-- Exact compatibility bridge produced by composing the three scoped rules. -/
structure XFunctionalGroupSequence : Prop where
  periodateC2 : stageCarbonState .afterPeriodate .c2 = .aldehyde
  periodateC3 : stageCarbonState .afterPeriodate .c3 = .aldehyde
  borohydrideC2 : stageCarbonState .afterBorohydride .c2 = .primaryAlcohol
  borohydrideC3 : stageCarbonState .afterBorohydride .c3 = .primaryAlcohol
  c2FinalScope :
    stageCarbonState .afterAcetylation .c2 = .alcoholOrAcetateEster
  c3FinalScope :
    stageCarbonState .afterAcetylation .c3 = .alcoholOrAcetateEster
  c6FinalScope :
    stageCarbonState .afterAcetylation .c6 = .alcoholOrAcetateEster
  laterCorePreserved :
    stageNetworkBond .afterBorohydride = stageNetworkBond .afterPeriodate ∧
      stageNetworkBond .afterAcetylation = stageNetworkBond .afterPeriodate

theorem xFunctionalGroupSequence : XFunctionalGroupSequence := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

/-- Alcohol-derived sites at which Ac2O may contribute an acetate group. -/
inductive AlcoholOrigin
  | c2 | c3 | c6
  deriving DecidableEq, Fintype, Repr

/-- The two carbon positions of an acetate substituent. -/
inductive AcetylCarbonSite
  | carbonyl | methyl
  deriving DecidableEq, Fintype, Repr

/-- Per-residue product-carbon audit envelope.

It contains the six scaffold carbons and all carbons that any extent of the
final O-acetylation can add.  Therefore omitted acetylation completeness cannot
change the count.
-/
inductive LocalXCarbon
  | scaffold (site : CarbonSite)
  | possibleAcetyl (origin : AlcoholOrigin) (site : AcetylCarbonSite)
  deriving DecidableEq, Fintype, Repr

inductive CarbonGeometry
  | tetrahedral | trigonalPlanar
  deriving DecidableEq, Fintype, Repr

inductive LigandSlot
  | first | second | third | fourth
  deriving DecidableEq, Fintype, Repr

/-- Rooted substituent descriptors obtained from the explicit network. -/
inductive LigandClass
  | hydrogen
  | hydroxyOrAcetoxyO
  | towardC1 | towardC2 | towardC3 | towardC4 | towardC5 | towardC6
  | viaO5ToC1 | viaO5ToC5
  | viaGlycosidicOToC1 | viaGlycosidicOToNextC4
  | towardAcetylCarbonyl | carbonylO | esterO | towardAcetylMethyl
  deriving DecidableEq, Fintype, Repr

def fourLigands
    (a b c d : LigandClass) : LigandSlot → LigandClass
  | .first => a
  | .second => b
  | .third => c
  | .fourth => d

/-- Four substituents in the source glucopyranoside drawing. -/
def sourceLigands : CarbonSite → LigandSlot → LigandClass
  | .c1 =>
      fourLigands .hydrogen .towardC2 .viaO5ToC5
        .viaGlycosidicOToNextC4
  | .c2 =>
      fourLigands .hydrogen .hydroxyOrAcetoxyO .towardC1 .towardC3
  | .c3 =>
      fourLigands .hydrogen .hydroxyOrAcetoxyO .towardC2 .towardC4
  | .c4 =>
      fourLigands .hydrogen .towardC3 .towardC5 .viaGlycosidicOToC1
  | .c5 =>
      fourLigands .hydrogen .towardC4 .towardC6 .viaO5ToC1
  | .c6 =>
      fourLigands .hydrogen .hydrogen .hydroxyOrAcetoxyO .towardC5

def xCarbonGeometry : LocalXCarbon → CarbonGeometry
  | .scaffold _ => .tetrahedral
  | .possibleAcetyl _ .carbonyl => .trigonalPlanar
  | .possibleAcetyl _ .methyl => .tetrahedral

/-- Complete product ligand table.  Reduction gives C2 and C3 two hydrogen
ligands; possible acetate carbonyls are planar and acetate methyls have three
identical hydrogen ligands. -/
def xLigands : LocalXCarbon → LigandSlot → LigandClass
  | .scaffold .c1 =>
      fourLigands .hydrogen .towardC2 .viaO5ToC5
        .viaGlycosidicOToNextC4
  | .scaffold .c2 =>
      fourLigands .hydrogen .hydrogen .hydroxyOrAcetoxyO .towardC1
  | .scaffold .c3 =>
      fourLigands .hydrogen .hydrogen .hydroxyOrAcetoxyO .towardC4
  | .scaffold .c4 =>
      fourLigands .hydrogen .towardC3 .towardC5 .viaGlycosidicOToC1
  | .scaffold .c5 =>
      fourLigands .hydrogen .towardC4 .towardC6 .viaO5ToC1
  | .scaffold .c6 =>
      fourLigands .hydrogen .hydrogen .hydroxyOrAcetoxyO .towardC5
  | .possibleAcetyl _ .carbonyl =>
      fourLigands .carbonylO .carbonylO .esterO .towardAcetylMethyl
  | .possibleAcetyl _ .methyl =>
      fourLigands .hydrogen .hydrogen .hydrogen .towardAcetylCarbonyl

/-- Explicit six-pair test that the four rooted substituents differ. -/
def fourDifferent (f : LigandSlot → LigandClass) : Bool :=
  decide
    (f .first ≠ f .second ∧
      f .first ≠ f .third ∧
      f .first ≠ f .fourth ∧
      f .second ≠ f .third ∧
      f .second ≠ f .fourth ∧
      f .third ≠ f .fourth)

/-- Authoritative four-different-substituent criterion applied to the table. -/
def IsStereocentreByLigands (c : LocalXCarbon) : Prop :=
  xCarbonGeometry c = .tetrahedral ∧ fourDifferent (xLigands c) = true

def isXStereocentre (c : LocalXCarbon) : Bool :=
  decide (xCarbonGeometry c = .tetrahedral) && fourDifferent (xLigands c)

theorem isXStereocentre_iff_ligand_criterion (c : LocalXCarbon) :
    isXStereocentre c = true ↔ IsStereocentreByLigands c := by
  simp [isXStereocentre, IsStereocentreByLigands]

/-- Initial sites are computed, rather than asserted, from the source ligands. -/
def initialStereocentreSites : Finset CarbonSite :=
  Finset.univ.filter fun s => fourDifferent (sourceLigands s)

/-- Sites selected independently by the periodate 2,3-diol rule. -/
def periodateAffectedStereocentreSites : Finset CarbonSite :=
  {.c2, .c3}

/-- Surviving stereocentres across all source residues and every possible
acetate-carbon site. -/
abbrev LocalXStereocentre :=
  {c : LocalXCarbon // isXStereocentre c = true}

abbrev XStereocentre := Residue × LocalXStereocentre

/-- Exhaustive local audit: only scaffold C1, C4, and C5 survive. -/
theorem xStereocentre_complete_audit :
    ∀ c : LocalXCarbon,
      isXStereocentre c = true ↔
        c = .scaffold .c1 ∨ c = .scaffold .c4 ∨ c = .scaffold .c5 := by
  decide

/-- The ligand audit derives the two-site loss rather than assuming it. -/
theorem xScaffoldStereocentres_are_source_minus_periodate_sites :
    (Finset.univ.filter fun s : CarbonSite =>
      isXStereocentre (.scaffold s)) =
      initialStereocentreSites \ periodateAffectedStereocentreSites := by
  decide

/-- Every carbon that Ac2O can add fails the stereocentre criterion. -/
theorem possibleAcetylCarbons_are_not_stereocentres :
    ∀ origin : AlcoholOrigin, ∀ site : AcetylCarbonSite,
      isXStereocentre (.possibleAcetyl origin site) = false := by
  decide

/-- Requested number of stereocentres in the full product audit envelope. -/
def macrocycleStereocentreCount : ℕ := Fintype.card XStereocentre

/-! ## Assumption/target split and exact-integer outputs -/

/-- End-to-end raw specification.  Its fields expose every decisive
source-to-model bridge, the whole-ring topology, the complete carbon envelope,
and both unrounded count formulae.  No requested value is a premise. -/
structure RawResult : Prop where
  transformationClassification :
    xTransformationUse = .qualitativeNamedTransformOnly
  sourceArrowDirection :
    xSourceArrow.input = .betaCyclodextrin ∧
      xSourceArrow.output = .productX
  previousPartReconstruction : PreviousPartRelevantInput
  periodateApplicability : PeriodateApplicability
  functionalGroupSequence : XFunctionalGroupSequence
  connectedMacrocycle : IsSingleCycle nextRingAtom
  macrocycleEdgesPresent :
    ∀ a : XMacrocycleAtom,
      stageNetworkBond .afterAcetylation a.toNetworkAtom
        (nextRingAtom a).toNetworkAtom = true
  selectedCleavageOffMacrocycle :
    ∀ a : XMacrocycleAtom,
      isC2C3Bond a.toNetworkAtom (nextRingAtom a).toNetworkAtom = false
  completeCarbonAudit :
    ∀ c : LocalXCarbon,
      isXStereocentre c = true ↔
        c = .scaffold .c1 ∨ c = .scaffold .c4 ∨ c = .scaffold .c5
  acetateEnvelopeAchiral :
    ∀ origin : AlcoholOrigin, ∀ site : AcetylCarbonSite,
      isXStereocentre (.possibleAcetyl origin site) = false
  ringFormula :
    macrocycleRingSize = betaCDUnitCount * Fintype.card XRingSite
  stereocentreFormula :
    macrocycleStereocentreCount =
      betaCDUnitCount *
        (initialStereocentreSites.card -
          periodateAffectedStereocentreSites.card)

/-- Exact-integer results requested in T9-A3, in source order. -/
structure ReportedResult : Prop where
  macrocycleRingSizeExact : macrocycleRingSize = 35
  macrocycleStereocentresExact : macrocycleStereocentreCount = 21

/-- Unhashed semantic derivation used by the answer-blind raw contract. -/
theorem rawSemanticResult : RawResult := by
  refine
    { transformationClassification := rfl
      sourceArrowDirection := ⟨rfl, rfl⟩
      previousPartReconstruction := previousPartA2_reconstructed
      periodateApplicability := periodate_applicable
      functionalGroupSequence := xFunctionalGroupSequence
      connectedMacrocycle := xMacrocycle_singleCycle
      macrocycleEdgesPresent := ?_
      selectedCleavageOffMacrocycle :=
        periodate_cleavage_disjoint_from_macrocycle
      completeCarbonAudit := xStereocentre_complete_audit
      acetateEnvelopeAchiral :=
        possibleAcetylCarbons_are_not_stereocentres
      ringFormula := by decide
      stereocentreFormula := by decide }
  intro a
  exact xMacrocycle_successor_bond .afterAcetylation a

/-- Requested output carrier: ring size of macrocycle `X`. -/
theorem macrocycle_ring_size : macrocycleRingSize = 35 := by
  decide

/-- Requested output carrier: total number of stereocentres in `X`. -/
theorem macrocycle_stereocentres : macrocycleStereocentreCount = 21 := by
  decide

/-- Unhashed reporting semantics, preserving source output order. -/
theorem reportedSemanticResult : ReportedResult := by
  exact ⟨macrocycle_ring_size, macrocycle_stereocentres⟩

/-- Hash-bound raw declaration required by the answer-blind protocol. -/
theorem rawResult :
    ("86d354b3f99951e2c443d0053e339614345f74c40145b81fb54f67390c71d6d8" : String) =
        "86d354b3f99951e2c443d0053e339614345f74c40145b81fb54f67390c71d6d8" ∧
      RawResult := by
  exact ⟨rfl, rawSemanticResult⟩

/-- Hash-bound reported declaration required by the answer-blind protocol. -/
theorem reportedResult :
    ("6e55f04ecf966eb66dd17c999f5c9241ea9e1bff6015fd31b5630794a9c6b7c0" : String) =
        "6e55f04ecf966eb66dd17c999f5c9241ea9e1bff6015fd31b5630794a9c6b7c0" ∧
      ReportedResult := by
  exact ⟨rfl, reportedSemanticResult⟩

end IChO2026Problems.ProblemIcho2026T9A3
