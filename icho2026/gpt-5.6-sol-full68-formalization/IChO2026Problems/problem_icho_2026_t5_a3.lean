import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5-A3: molecular formula of the cardiolipin fatty acid

This file is an answer-blind formalization of the fragment and bond-count
argument printed in the problem.  It deliberately does not import the files
for T5-A1 or T5-A2: the hydrogen-cap count and the part of the PL1 structure
needed here are reconstructed from the bound page-1 fragment diagram.

The reductive-ozonolysis observation is used only as a non-exclusive
compatibility constraint: for an acyclic chain whose unsaturations are C=C
bonds, cleavage at `d` such bonds gives `d + 1` carbon-containing fragment
roles.  No yield, product identity, phase, or unprinted byproduct claim is
made.
-/

namespace IChO2026Problems.ProblemIcho2026T5A3

/-- Provenance tags used by the source-first audit in this target. -/
inductive Provenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Chemical entities whose identities matter to the observations used here. -/
inductive Species where
  | pl1
  | fattyAcidRCOOH
  | ozonolysisProduct (index : Fin 3)
  deriving DecidableEq, Repr

inductive IonisationState where
  | nonIonised
  | monoanion
  | dianion
  deriving DecidableEq, Repr

inductive BondAccountingMode where
  | sigmaPlusPi
  deriving DecidableEq, Repr

/-- The exact bond observation in T5-A3, kept attached to PL1 and its state. -/
structure TotalBondObservation where
  species : Species
  ionisationState : IonisationState
  accountingMode : BondAccountingMode
  count : ℕ
  sourceLocator : String
  provenance : Provenance
  deriving DecidableEq, Repr

def sourcePL1BondObservation : TotalBondObservation :=
  { species := .pl1
    ionisationState := .nonIonised
    accountingMode := .sigmaPlusPi
    count := 255
    sourceLocator := "T5_page-3.png, box 5.3"
    provenance := .problemText }

inductive BiologicalMaterial where
  | mammalianHeart
  deriving DecidableEq, Repr

inductive PrevalenceQualifier where
  | predominant
  deriving DecidableEq, Repr

/-- The named biological sample to which the experimental identification refers. -/
structure FattyAcidSampleContext where
  lipid : Species
  residue : Species
  material : BiologicalMaterial
  prevalence : PrevalenceQualifier
  provenance : Provenance
  deriving DecidableEq, Repr

def sourceFattyAcidSampleContext : FattyAcidSampleContext :=
  { lipid := .pl1
    residue := .fattyAcidRCOOH
    material := .mammalianHeart
    prevalence := .predominant
    provenance := .problemText }

inductive OzonolysisWorkup where
  | reductive
  deriving DecidableEq, Repr

inductive ReactionDirection where
  | forward
  deriving DecidableEq, Repr

/--
The stated ozonolysis readout.  `relativeMolesPerProduct = 1` records the
1 : 1 : 1 meaning of “equimolar”; it is not an absolute amount or yield.
-/
structure OzonolysisObservation where
  substrate : Species
  workup : OzonolysisWorkup
  direction : ReactionDirection
  distinctOrganicProductKinds : ℕ
  relativeMolesPerProduct : ℕ
  sourceLocator : String
  provenance : Provenance
  deriving DecidableEq, Repr

def sourceOzonolysisObservation : OzonolysisObservation :=
  { substrate := .fattyAcidRCOOH
    workup := .reductive
    direction := .forward
    distinctOrganicProductKinds := 3
    relativeMolesPerProduct := 1
    sourceLocator := "T5_page-3.png, paragraph before box 5.3"
    provenance := .problemText }

/-- Atom counts in a neutral molecular formula. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
  deriving DecidableEq, Repr

/-- The requested fatty-acid formula has no phosphorus field. -/
structure FattyAcidFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- A structural model adds the number of C=C bonds to the molecular formula. -/
structure FattyAcidModel where
  formula : FattyAcidFormula
  carbonCarbonDoubleBonds : ℕ
  deriving DecidableEq, Repr

/-! ## Source-first recount of the page-1 fragments -/

inductive FragmentKind where
  | aHydrogenCap
  | bPhosphate
  | cGlycerol
  | dAcyl
  deriving DecidableEq, Fintype, Repr

/-- One row of the explicit visual component ledger. -/
structure FragmentDiagramRow where
  kind : FragmentKind
  visualDescriptor : String
  multiplicity : ℕ
  openSitesPerUnit : ℕ
  provenance : Provenance
  deriving DecidableEq, Repr

/-- All four visually distinct building-block types on page 1. -/
def sourceFragmentDiagramLedger (hydrogenCaps : ℕ) : List FragmentDiagramRow :=
  [ { kind := .aHydrogenCap
      visualDescriptor := "one H atom on one wavy attachment"
      multiplicity := hydrogenCaps
      openSitesPerUnit := 1
      provenance := .problemImage },
    { kind := .bPhosphate
      visualDescriptor := "P(=O)(OH) with two wavy P attachments"
      multiplicity := 2
      openSitesPerUnit := 2
      provenance := .problemImage },
    { kind := .cGlycerol
      visualDescriptor := "three-carbon glycerol skeleton with three O attachments"
      multiplicity := 3
      openSitesPerUnit := 3
      provenance := .problemImage },
    { kind := .dAcyl
      visualDescriptor := "one wavy attachment to the carbonyl C of R-C(=O)-"
      multiplicity := 4
      openSitesPerUnit := 1
      provenance := .problemImage } ]

def fragmentDiagramSourceLocator : String :=
  "T5_page-1.png, PL1 a-d fragment row"

/-- Multiplicities printed below the PL1 fragment diagram. -/
def fragmentMultiplicity (hydrogenCaps : ℕ) : FragmentKind → ℕ
  | .aHydrogenCap => hydrogenCaps
  | .bPhosphate => 2
  | .cGlycerol => 3
  | .dAcyl => 4

/-- Number of wavy cross-boundary attachment sites drawn on each fragment. -/
def openSitesPerFragment : FragmentKind → ℕ
  | .aHydrogenCap => 1
  | .bPhosphate => 2
  | .cGlycerol => 3
  | .dAcyl => 1

/--
Each open site of a type-c glycerol terminates at oxygen.  Since PL1 has no
O-O bond, the nine such sites must be paired with the sites on a, b, or d.
This is the page-1 closure equation, not a previous-part answer premise.
-/
def FragmentSiteClosure (hydrogenCaps : ℕ) : Prop :=
  fragmentMultiplicity hydrogenCaps .cGlycerol *
      openSitesPerFragment .cGlycerol =
    fragmentMultiplicity hydrogenCaps .aHydrogenCap *
        openSitesPerFragment .aHydrogenCap +
      fragmentMultiplicity hydrogenCaps .bPhosphate *
        openSitesPerFragment .bPhosphate +
      fragmentMultiplicity hydrogenCaps .dAcyl *
        openSitesPerFragment .dAcyl

/-- Blind derivation of the numerical content needed from T5-A1. -/
theorem hydrogenCapCount_unique {hydrogenCaps : ℕ}
    (hclosure : FragmentSiteClosure hydrogenCaps) :
    hydrogenCaps = 1 := by
  simp [FragmentSiteClosure, fragmentMultiplicity, openSitesPerFragment] at hclosure
  omega

/-- Thus the correct T5-A1 parity branch is odd, derived rather than imported. -/
theorem hydrogenCapCount_isOdd {hydrogenCaps : ℕ}
    (hclosure : FragmentSiteClosure hydrogenCaps) :
    ∃ k : ℕ, hydrogenCaps = 2 * k + 1 := by
  refine ⟨0, ?_⟩
  simpa using hydrogenCapCount_unique hclosure

/-!
The following ten-node witness makes the cross-boundary topology explicit.
It is one admissible PL1 assembly; the A3 atom and bond totals depend only on
the audited degrees, not on a uniqueness claim about this drawing.
-/

inductive PL1Node where
  | hydrogenCap
  | phosphateLeft
  | phosphateRight
  | glycerolLeft
  | glycerolCentre
  | glycerolRight
  | acylOne
  | acylTwo
  | acylThree
  | acylFour
  deriving DecidableEq, Fintype, Repr

abbrev PL1Attachment := PL1Node × PL1Node

/-- The nine bonds crossing fragment boundaries in one assembled PL1. -/
def pl1Attachments : List PL1Attachment :=
  [ (.glycerolLeft, .acylOne),
    (.glycerolLeft, .acylTwo),
    (.glycerolLeft, .phosphateLeft),
    (.glycerolCentre, .phosphateLeft),
    (.glycerolCentre, .hydrogenCap),
    (.glycerolCentre, .phosphateRight),
    (.glycerolRight, .phosphateRight),
    (.glycerolRight, .acylThree),
    (.glycerolRight, .acylFour) ]

def expectedAttachmentDegree : PL1Node → ℕ
  | .glycerolLeft | .glycerolCentre | .glycerolRight => 3
  | .phosphateLeft | .phosphateRight => 2
  | .hydrogenCap | .acylOne | .acylTwo | .acylThree | .acylFour => 1

def incidenceMultiplicity (node : PL1Node) (edge : PL1Attachment) : ℕ :=
  (if node = edge.1 then 1 else 0) + (if node = edge.2 then 1 else 0)

def attachmentDegree (node : PL1Node) : ℕ :=
  (pl1Attachments.map (incidenceMultiplicity node)).sum

def IsGlycerolNode : PL1Node → Prop
  | .glycerolLeft | .glycerolCentre | .glycerolRight => True
  | _ => False

/-- Every assembly edge joins a glycerol O site to a non-glycerol site. -/
def CrossesGlycerolBoundary (edge : PL1Attachment) : Prop :=
  (IsGlycerolNode edge.1 ∧ ¬ IsGlycerolNode edge.2) ∨
    (IsGlycerolNode edge.2 ∧ ¬ IsGlycerolNode edge.1)

def pl1Adjacent (u v : PL1Node) : Prop :=
  (u, v) ∈ pl1Attachments ∨ (v, u) ∈ pl1Attachments

def PL1Connected : Prop :=
  ∀ node : PL1Node,
    Relation.ReflTransGen pl1Adjacent .glycerolCentre node

/--
Nontrivial topology carrier for the visual recount: 10 distinct components,
9 distinct cross-boundary bonds, all printed open valences saturated, no
glycerol-O/glycerol-O boundary, and one connected assembly.
-/
def PL1TopologyAudit : Prop :=
  Fintype.card PL1Node = 10 ∧
    pl1Attachments.length = 9 ∧
    pl1Attachments.Nodup ∧
    (∀ edge ∈ pl1Attachments, CrossesGlycerolBoundary edge) ∧
    (∀ node : PL1Node, attachmentDegree node = expectedAttachmentDegree node) ∧
    PL1Connected

def pl1TopologyProvenance : Provenance :=
  .problemStatedFallback

/-- Reconstruction of the A3-relevant structural content of T5-A2. -/
theorem pl1Topology_fromSourceFragments : PL1TopologyAudit := by
  unfold PL1TopologyAudit
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · simp [pl1Attachments, CrossesGlycerolBoundary, IsGlycerolNode]
  constructor
  · intro node
    cases node <;> native_decide
  · intro node
    have hcentre : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .glycerolCentre := Relation.ReflTransGen.refl
    have hhydrogen : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .hydrogenCap :=
      Relation.ReflTransGen.tail hcentre (by
        simp [pl1Adjacent, pl1Attachments])
    have hphosphateLeft : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .phosphateLeft :=
      Relation.ReflTransGen.tail hcentre (by
        simp [pl1Adjacent, pl1Attachments])
    have hphosphateRight : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .phosphateRight :=
      Relation.ReflTransGen.tail hcentre (by
        simp [pl1Adjacent, pl1Attachments])
    have hglycerolLeft : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .glycerolLeft :=
      Relation.ReflTransGen.tail hphosphateLeft (by
        simp [pl1Adjacent, pl1Attachments])
    have hglycerolRight : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .glycerolRight :=
      Relation.ReflTransGen.tail hphosphateRight (by
        simp [pl1Adjacent, pl1Attachments])
    have hacylOne : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .acylOne :=
      Relation.ReflTransGen.tail hglycerolLeft (by
        simp [pl1Adjacent, pl1Attachments])
    have hacylTwo : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .acylTwo :=
      Relation.ReflTransGen.tail hglycerolLeft (by
        simp [pl1Adjacent, pl1Attachments])
    have hacylThree : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .acylThree :=
      Relation.ReflTransGen.tail hglycerolRight (by
        simp [pl1Adjacent, pl1Attachments])
    have hacylFour : Relation.ReflTransGen pl1Adjacent
        .glycerolCentre .acylFour :=
      Relation.ReflTransGen.tail hglycerolRight (by
        simp [pl1Adjacent, pl1Attachments])
    cases node <;> assumption

/-! ## Atom and bond ledgers -/

/--
Direct atom recombination of 3 glycerol fragments, 2 phosphate fragments,
4 identical acyl fragments, and the one hydrogen cap.  The formula is
`C_(9+4c) H_(14+4h) O_17 P_2` when the free acid is `C_c H_h O_2`.
-/
def assembledPL1Formula (acid : FattyAcidFormula) : MolecularFormula :=
  { carbon := 9 + 4 * acid.carbon
    hydrogen := 14 + 4 * acid.hydrogen
    oxygen := 17
    phosphorus := 2 }

/--
Independent precursor ledger: 3 C3H8O3 + 2 H3PO4 + 4 fatty acids, followed by
8 condensations (four acyl esters and four phosphate esters), loses 8 H2O.
-/
def condensedPrecursorPL1Formula (acid : FattyAcidFormula) : MolecularFormula :=
  { carbon := 3 * 3 + 4 * acid.carbon
    hydrogen := 3 * 8 + 2 * 3 + 4 * acid.hydrogen - 2 * 8
    oxygen := 3 * 3 + 2 * 4 + 4 * acid.oxygen - 8
    phosphorus := 2 }

/-- The image-fragment and eight-water condensation atom ledgers agree. -/
theorem atomRecombination_crosscheck (acid : FattyAcidFormula)
    (hoxygen : acid.oxygen = 2) :
    condensedPrecursorPL1Formula acid = assembledPL1Formula acid := by
  cases acid with
  | mk carbon hydrogen oxygen =>
      change oxygen = 2 at hoxygen
      subst oxygen
      simp [condensedPrecursorPL1Formula, assembledPL1Formula]
      omega

/--
For the four type-d acyl fragments together, the valence sum after removing
four acid OH groups and reserving four open ester bonds gives
`8 * carbon + 2 * hydrogen` internal sigma-plus-pi bonds.
-/
def fourAcylInternalBondCount (acid : FattyAcidFormula) : ℕ :=
  8 * acid.carbon + 2 * acid.hydrogen

/--
Fragment bond ledger.  A phosphate b contains 4 sigma-plus-pi bonds, a
glycerol c contains 10, the H cap contains none, and assembly contributes the
9 cross-boundary single bonds listed in `pl1Attachments`.
-/
def pl1SigmaPiBondCountFromFragments (acid : FattyAcidFormula) : ℕ :=
  2 * 4 + 3 * 10 + fourAcylInternalBondCount acid + pl1Attachments.length

/-- Simplified end-to-end bond equation, before substituting the observation. -/
theorem pl1BondLedger (acid : FattyAcidFormula) :
    pl1SigmaPiBondCountFromFragments acid =
      47 + 8 * acid.carbon + 2 * acid.hydrogen := by
  simp [pl1SigmaPiBondCountFromFragments, fourAcylInternalBondCount,
    pl1Attachments]
  omega

/--
Independent valence-sum check using the bond orders depicted by the fragments:
C contributes 4, H 1, O 2, and pentavalent phosphate P contributes 5.
-/
def sigmaPiBondCountFromValences (formula : MolecularFormula) : ℕ :=
  (4 * formula.carbon + formula.hydrogen + 2 * formula.oxygen +
      5 * formula.phosphorus) / 2

theorem fragmentAndValenceBondLedgersAgree (acid : FattyAcidFormula) :
    sigmaPiBondCountFromValences (assembledPL1Formula acid) =
      pl1SigmaPiBondCountFromFragments acid := by
  simp [sigmaPiBondCountFromValences, assembledPL1Formula,
    pl1SigmaPiBondCountFromFragments, fourAcylInternalBondCount,
    pl1Attachments]
  omega

/-! ## Uniform source-compatible model and requested exact formula -/

/--
Primitive compatibility ledger for the stated reductive ozonolysis.  In this
acyclic-chain model, cutting `d` C=C edges creates `d + 1` fragment roles.  The
second conjunct retains the stated equimolar 1 : 1 : 1 readout.
-/
def ReductiveOzonolysisCompatibility (model : FattyAcidModel) : Prop :=
  sourceOzonolysisObservation.distinctOrganicProductKinds =
      model.carbonCarbonDoubleBonds + 1 ∧
    sourceOzonolysisObservation.relativeMolesPerProduct = 1

def reductiveOzonolysisCompatibilityProvenance : Provenance :=
  .trustedGeneralLaw

/--
Valence ledger for an acyclic monocarboxylic acid whose hydrocarbon
unsaturations are the C=C bonds counted above: `H + 2d = 2C` and `O = 2`.
-/
def AcyclicFattyAcidValenceLedger (model : FattyAcidModel) : Prop :=
  model.formula.oxygen = 2 ∧
    model.formula.hydrogen + 2 * model.carbonCarbonDoubleBonds =
      2 * model.formula.carbon

def acyclicFattyAcidValenceLedgerProvenance : Provenance :=
  .trustedGeneralLaw

/--
All decisive constraints are applied uniformly over the unbounded natural
number model space; there is no candidate-shaped finite search domain.
-/
def SourceCompatibleFattyAcid (model : FattyAcidModel) : Prop :=
  0 < model.formula.carbon ∧
    0 < model.formula.hydrogen ∧
    (∃ hydrogenCaps : ℕ, FragmentSiteClosure hydrogenCaps) ∧
    ReductiveOzonolysisCompatibility model ∧
    AcyclicFattyAcidValenceLedger model ∧
    pl1SigmaPiBondCountFromFragments model.formula =
      sourcePL1BondObservation.count

/-- Candidate obtained by solving the displayed fragment, ozonolysis, and valence ledgers. -/
def derivedFattyAcidModel : FattyAcidModel :=
  { formula := { carbon := 18, hydrogen := 32, oxygen := 2 }
    carbonCarbonDoubleBonds := 2 }

/-- The exact molecular formula requested for RCOOH. -/
def derivedFattyAcidFormula : FattyAcidFormula :=
  derivedFattyAcidModel.formula

/-- Raw symbolic result: the uniform source constraints characterize one model. -/
def fattyAcidFormulaRawResult : Prop :=
  ∀ model : FattyAcidModel,
    SourceCompatibleFattyAcid model ↔ model = derivedFattyAcidModel

/--
Reported symbolic result: exact formulas are not rounded, and every compatible
model has the displayed formula while the displayed witness is compatible.
-/
def fattyAcidFormulaReportedResult : Prop :=
  SourceCompatibleFattyAcid derivedFattyAcidModel ∧
    ∀ model : FattyAcidModel,
      SourceCompatibleFattyAcid model → model.formula = derivedFattyAcidFormula

/-- Raw answer-blind result carrier. -/
theorem fattyAcidFormula_raw : fattyAcidFormulaRawResult := by
  intro model
  constructor
  · intro hmodel
    rcases model with ⟨⟨carbon, hydrogen, oxygen⟩, doubleBonds⟩
    simp only [SourceCompatibleFattyAcid,
      ReductiveOzonolysisCompatibility, sourceOzonolysisObservation,
      AcyclicFattyAcidValenceLedger,
      pl1SigmaPiBondCountFromFragments, fourAcylInternalBondCount,
      pl1Attachments, sourcePL1BondObservation]
      at hmodel
    rcases hmodel with
      ⟨_, _, _, ⟨hozonolysis, _⟩, ⟨hoxygen, hvalence⟩, hbonds⟩
    norm_num at hbonds
    have hdoubleBonds : doubleBonds = 2 := by omega
    subst doubleBonds
    have hcarbon : carbon = 18 := by omega
    subst carbon
    have hhydrogen : hydrogen = 32 := by omega
    subst hydrogen
    have hoxygen' : oxygen = 2 := by omega
    subst oxygen
    rfl
  · intro hmodel
    subst model
    norm_num [SourceCompatibleFattyAcid, FragmentSiteClosure,
      fragmentMultiplicity, openSitesPerFragment,
      ReductiveOzonolysisCompatibility, sourceOzonolysisObservation,
      AcyclicFattyAcidValenceLedger, pl1SigmaPiBondCountFromFragments,
      fourAcylInternalBondCount, pl1Attachments, sourcePL1BondObservation,
      derivedFattyAcidModel]
    exact ⟨1, rfl⟩

/-- Reported exact-symbolic result carrier (`C18H32O2`, with no rounding). -/
theorem fattyAcidFormula_reported : fattyAcidFormulaReportedResult := by
  have hraw := fattyAcidFormula_raw
  constructor
  · exact (hraw derivedFattyAcidModel).2 rfl
  · intro model hmodel
    have hmodel' := (hraw model).1 hmodel
    subst model
    rfl

end IChO2026Problems.ProblemIcho2026T5A3
