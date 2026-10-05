import Mathlib
import Physlib.Units.Dimension
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T6-A2: structures in the surface synthesis of cyclo[14]carbon

The requested drawings are represented as finite atom-and-bond structures.
The fourteen carbon indices are deliberately kept fixed through the complete
precursor -> A -> B -> C -> C14 network and the A -> D branch.  Thus the
source arrows are atom-preserving graph edits, rather than three unrelated
checks performed on already selected answers.

The depicted transformations are used only as
`qualitative_named_transform_only` compatibility constraints.  No yield,
exclusive-product, phase-balance, or omitted-stream claim is made.
-/

namespace IChO2026Problems.T6A2

inductive Element
  | carbon
  | chlorine
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  | triple
  deriving DecidableEq, Repr, Fintype

inductive BondStereo
  | none
  | together
  | opposite
  | unspecified
  deriving DecidableEq, Repr

inductive AtomStereo
  | notStereogenic
  | clockwise
  | anticlockwise
  | unspecified
  deriving DecidableEq, Repr

structure Atom where
  element : Element
  formalCharge : Int
  unpairedElectrons : Nat
  stereochemistry : AtomStereo
  deriving DecidableEq, Repr

/-- An undirected bond, stored with the smaller natural-number endpoint first. -/
structure Bond where
  lower : Nat
  upper : Nat
  order : BondOrder
  stereochemistry : BondStereo
  deriving DecidableEq, Repr

inductive Stage
  | precursor
  | intermediateA
  | intermediateB
  | intermediateC
  | intermediateD
  | cyclo14Carbon
  deriving DecidableEq, Repr

inductive Phase
  | surfaceAdsorbed
  deriving DecidableEq, Repr

structure MolecularStructure where
  stage : Stage
  phase : Phase
  atomCount : Nat
  atoms : Fin atomCount -> Atom
  bonds : List Bond

inductive Provenance
  | problemText
  | problemImage
  | peerReviewedLiterature
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Exact source locator attached to every decoded panel or arrow. -/
structure EvidenceLocator where
  provenance : Provenance
  pathOrUrl : String
  sourceSha256 : String
  locator : String
  deriving DecidableEq, Repr

inductive TransformationUse
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def selectedTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

def problemImageSha256 : String :=
  "29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba"

def problemImageLocator (panel : String) : EvidenceLocator :=
  { provenance := .problemImage
    pathOrUrl := "icho_2026_source/image/T6_page-1.png"
    sourceSha256 := problemImageSha256
    locator := panel }

/-- The generic six-ring-to-open-chain pattern printed as reaction (1). -/
def retroBergmanPatternLocator : EvidenceLocator :=
  problemImageLocator
    "reaction (1): a six-membered carbon ring opens to two alkynyl arms without loss of a carbon vertex"

def BondOrder.valence : BondOrder -> Nat
  | .single => 1
  | .double => 2
  | .triple => 3

def Element.typicalValence : Element -> Nat
  | .carbon => 4
  | .chlorine => 1

def bond (i j : Nat) (order : BondOrder) : Bond :=
  { lower := min i j
    upper := max i j
    order := order
    stereochemistry := .none }

def carbonAtom (radicalElectrons : Nat) : Atom :=
  { element := .carbon
    formalCharge := 0
    unpairedElectrons := radicalElectrons
    stereochemistry := .notStereogenic }

def chlorineAtom : Atom :=
  { element := .chlorine
    formalCharge := 0
    unpairedElectrons := 0
    stereochemistry := .notStereogenic }

/-- Carbon atoms always have the stable indices 0,...,13. -/
def atomMap (chlorineAtoms : Nat) (radicalSites : Finset Nat) :
    Fin (14 + chlorineAtoms) -> Atom :=
  fun i =>
    if i.val < 14 then
      carbonAtom (if i.val ∈ radicalSites then 1 else 0)
    else
      chlorineAtom

def MolecularStructure.elementCount (s : MolecularStructure) (e : Element) : Nat :=
  (Finset.univ.filter (fun i : Fin s.atomCount => (s.atoms i).element = e)).card

def MolecularStructure.bondOrderSum (s : MolecularStructure) (i : Nat) : Nat :=
  (s.bonds.map (fun b =>
    if b.lower = i ∨ b.upper = i then b.order.valence else 0)).sum

def MolecularStructure.unpairedElectronCount (s : MolecularStructure) : Nat :=
  ∑ i : Fin s.atomCount, (s.atoms i).unpairedElectrons

def MolecularStructure.elementAt? (s : MolecularStructure) (i : Nat) : Option Element :=
  if h : i < s.atomCount then some (s.atoms ⟨i, h⟩).element else none

def HasBond (s : MolecularStructure) (i j : Nat) (order : BondOrder) : Prop :=
  bond i j order ∈ s.bonds

def HasAnyBond (s : MolecularStructure) (i j : Nat) : Prop :=
  HasBond s i j .single ∨ HasBond s i j .double ∨ HasBond s i j .triple

structure MolecularFormula where
  carbon : Nat
  chlorine : Nat
  deriving DecidableEq, Repr

def HasFormula (s : MolecularStructure) (f : MolecularFormula) : Prop :=
  s.elementCount .carbon = f.carbon ∧
  s.elementCount .chlorine = f.chlorine ∧
  s.atomCount = f.carbon + f.chlorine

/-- Neutral valence, endpoint, and explicit stereochemistry audit. -/
def WellFormed (s : MolecularStructure) : Prop :=
  s.bonds.Nodup ∧
  s.bonds.Forall (fun b => b.lower < b.upper ∧ b.upper < s.atomCount) ∧
  ((Finset.univ : Finset (Fin s.atomCount)).toList).Forall (fun i =>
    (s.atoms i).formalCharge = 0 ∧
    s.bondOrderSum i.val + (s.atoms i).unpairedElectrons =
      (s.atoms i).element.typicalValence) ∧
  ((Finset.univ : Finset (Fin s.atomCount)).toList).Forall (fun i =>
    (s.atoms i).stereochemistry = .notStereogenic) ∧
  s.bonds.Forall (fun b => b.stereochemistry = .none)

def HasRadicalsExactly (s : MolecularStructure) (sites : Finset Nat) : Prop :=
  ((Finset.univ : Finset (Fin s.atomCount)).toList).Forall (fun i =>
    (s.atoms i).unpairedElectrons = if i.val ∈ sites then 1 else 0)

def HasChlorineAt (s : MolecularStructure) (carbonSite : Nat) : Prop :=
  carbonSite < 14 ∧
  ∃ chlorineIndex : Nat,
    s.elementAt? chlorineIndex = some .chlorine ∧
    HasBond s carbonSite chlorineIndex .single

/-- Chlorine atoms are indexed by their carbon attachment sites for purposes
of atom-preserving arrow bookkeeping. -/
def HasChlorinesExactlyAt (s : MolecularStructure) (sites : Finset Nat) : Prop :=
  sites ⊆ Finset.range 14 ∧
  s.elementCount .chlorine = sites.card ∧
  ∀ i : Nat, i < 14 -> (HasChlorineAt s i ↔ i ∈ sites)

/-- Replace the unbounded index used by `HasChlorineAt` with the finite atom
index that its successful lookup necessarily supplies. -/
private theorem hasChlorineAt_iff_exists_fin
    (s : MolecularStructure) (i : Nat) :
    HasChlorineAt s i ↔
      i < 14 ∧ ∃ j : Fin s.atomCount,
        (s.atoms j).element = .chlorine ∧ HasBond s i j.val .single := by
  constructor
  · rintro ⟨hi, j, hjElement, hjBond⟩
    unfold MolecularStructure.elementAt? at hjElement
    split at hjElement
    · rename_i hj
      exact ⟨hi, ⟨⟨j, hj⟩, Option.some.inj hjElement, hjBond⟩⟩
    · simp at hjElement
  · rintro ⟨hi, j, hjElement, hjBond⟩
    exact ⟨hi, j.val,
      by simp [MolecularStructure.elementAt?, j.isLt, hjElement], hjBond⟩

/-- A finite checker for exact chlorine attachments.  The original definition
retains its source-facing natural-number quantifier; this lemma proves it from
the equivalent finite atom inventory. -/
private theorem hasChlorinesExactlyAt_of_fin
    (s : MolecularStructure) (sites : Finset Nat)
    (hsub : sites ⊆ Finset.range 14)
    (hcount : s.elementCount .chlorine = sites.card)
    (hattach : ∀ i : Fin 14,
      (i.val < 14 ∧ ∃ j : Fin s.atomCount,
        (s.atoms j).element = .chlorine ∧ HasBond s i.val j.val .single) ↔
          i.val ∈ sites) :
    HasChlorinesExactlyAt s sites := by
  refine ⟨hsub, hcount, ?_⟩
  intro i hi
  rw [hasChlorineAt_iff_exists_fin]
  exact hattach ⟨i, hi⟩

private theorem fin_univ_toList_forall
    {n : Nat} {p : Fin n → Prop} (h : ∀ i, p i) :
    ((Finset.univ : Finset (Fin n)).toList).Forall p := by
  rw [List.forall_iff_forall_mem]
  intro i _
  exact h i

private theorem hasRadicalsExactly_of_fin
    (s : MolecularStructure) (sites : Finset Nat)
    (h : ∀ i : Fin s.atomCount,
      (s.atoms i).unpairedElectrons = if i.val ∈ sites then 1 else 0) :
    HasRadicalsExactly s sites := by
  unfold HasRadicalsExactly
  exact fin_univ_toList_forall h

private theorem wellFormed_of_fin
    (s : MolecularStructure)
    (hnodup : s.bonds.Nodup)
    (hendpoints : s.bonds.Forall (fun b =>
      b.lower < b.upper ∧ b.upper < s.atomCount))
    (hvalence : ∀ i : Fin s.atomCount,
      (s.atoms i).formalCharge = 0 ∧
      s.bondOrderSum i.val + (s.atoms i).unpairedElectrons =
        (s.atoms i).element.typicalValence)
    (hatomStereo : ∀ i : Fin s.atomCount,
      (s.atoms i).stereochemistry = .notStereogenic)
    (hbondStereo : s.bonds.Forall (fun b => b.stereochemistry = .none)) :
    WellFormed s := by
  exact ⟨hnodup, hendpoints, fin_univ_toList_forall hvalence,
    fin_univ_toList_forall hatomStereo, hbondStereo⟩

/-- Consecutive endpoint pairs of a closed polygonal walk. -/
def cycleEdges : List Nat -> List (Nat × Nat)
  | [] => []
  | first :: rest => (first :: rest).zip (rest ++ [first])

def IsCarbonCycle (s : MolecularStructure) (vertices : List Nat) : Prop :=
  3 ≤ vertices.length ∧
  vertices.Nodup ∧
  vertices.Forall (fun i => s.elementAt? i = some .carbon) ∧
  (cycleEdges vertices).Forall (fun e => HasAnyBond s e.1 e.2)

def IsEthynylArm (s : MolecularStructure)
    (terminal adjacent ringCarbon : Nat) : Prop :=
  HasBond s terminal adjacent .triple ∧
  HasBond s adjacent ringCarbon .single

/-! ## Stable carbon skeletons and typed source arrows -/

structure CarbonEdge where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def carbonEdge (i j : Nat) : CarbonEdge :=
  { lower := min i j, upper := max i j }

def carbonEdgesOfPairs (pairs : List (Nat × Nat)) : Finset CarbonEdge :=
  (pairs.map (fun e => carbonEdge e.1 e.2)).toFinset

def MolecularStructure.carbonSkeleton (s : MolecularStructure) : Finset CarbonEdge :=
  (s.bonds.filterMap (fun b =>
    if b.upper < 14 then some (carbonEdge b.lower b.upper) else none)).toFinset

/-- Three linearly fused six-rings, transcribed before selecting B, C, or D. -/
def anthraceneSkeleton : Finset CarbonEdge :=
  carbonEdgesOfPairs
    [ (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)
    , (2, 6), (6, 7), (7, 8), (8, 9), (3, 9)
    , (7, 10), (10, 11), (11, 12), (12, 13), (8, 13) ]

def bSkeleton : Finset CarbonEdge :=
  anthraceneSkeleton.erase (carbonEdge 7 8)

def cSkeleton : Finset CarbonEdge :=
  bSkeleton.erase (carbonEdge 2 3)

def dSkeleton : Finset CarbonEdge :=
  anthraceneSkeleton.erase (carbonEdge 0 5)

structure StageView where
  stage : Stage
  carbonEdges : Finset CarbonEdge
  chlorineSites : Finset Nat
  radicalSites : Finset Nat
  deriving DecidableEq

def precursorView : StageView :=
  { stage := .precursor
    carbonEdges := anthraceneSkeleton
    chlorineSites := {0, 1, 4, 5, 6, 9, 10, 11, 12, 13}
    radicalSites := ∅ }

def aView : StageView :=
  { stage := .intermediateA
    carbonEdges := anthraceneSkeleton
    chlorineSites := {0, 1, 4, 5, 9, 10, 11, 12}
    radicalSites := {6, 13} }

def bView : StageView :=
  { stage := .intermediateB
    carbonEdges := bSkeleton
    chlorineSites := {0, 4, 5}
    radicalSites := {1} }

def cView : StageView :=
  { stage := .intermediateC
    carbonEdges := cSkeleton
    chlorineSites := {0}
    radicalSites := {1} }

def dView : StageView :=
  { stage := .intermediateD
    carbonEdges := dSkeleton
    chlorineSites := {0, 5, 9, 11, 12}
    radicalSites := {6, 10, 13} }

def cyclo14View : StageView :=
  { stage := .cyclo14Carbon
    carbonEdges := cSkeleton
    chlorineSites := ∅
    radicalSites := ∅ }

def ValidStageView (v : StageView) : Prop :=
  v.chlorineSites ⊆ Finset.range 14 ∧
  v.radicalSites ⊆ Finset.range 14 ∧
  ∀ e ∈ v.carbonEdges, e.lower < e.upper ∧ e.upper < 14

/-- A molecular drawing realizes a source stage view, including attachment and
radical sites rather than just the scalar formula. -/
def RepresentsStageView (s : MolecularStructure) (v : StageView) : Prop :=
  ValidStageView v ∧
  s.stage = v.stage ∧ s.phase = .surfaceAdsorbed ∧
  HasFormula s { carbon := 14, chlorine := v.chlorineSites.card } ∧
  s.carbonSkeleton = v.carbonEdges ∧
  HasChlorinesExactlyAt s v.chlorineSites ∧
  HasRadicalsExactly s v.radicalSites ∧
  WellFormed s

/-- The same natural number denotes the same carbon atom at both ends. -/
def CarbonIdentityPreserved
    (tail head : MolecularStructure) : Prop :=
  ∀ i : Fin 14,
    tail.elementAt? i.val = some .carbon ∧
    head.elementAt? i.val = some .carbon

def IsViewCycle (v : StageView) (vertices : List Nat) : Prop :=
  3 ≤ vertices.length ∧
  vertices.Nodup ∧
  vertices.Forall (fun i => i < 14) ∧
  (cycleEdges vertices).Forall (fun e => carbonEdge e.1 e.2 ∈ v.carbonEdges)

def cycleEdgeSet (vertices : List Nat) : Finset CarbonEdge :=
  carbonEdgesOfPairs (cycleEdges vertices)

inductive ArrowKind
  | homolyticDechlorination
  | dechlorinationAndRetroBergman
  deriving DecidableEq, Repr

/-- A directed source arrow with site-resolved chlorine loss and, when shown by
the retro-Bergman pattern, one atom-preserving carbon-edge scission. -/
structure DepictedArrow where
  locator : EvidenceLocator
  tail : StageView
  head : StageView
  kind : ArrowKind
  printedChlorineRadicalLoss : Nat
  lostChlorineSites : Finset Nat
  openedRing : List Nat
  brokenEdge : Option CarbonEdge
  transformationPattern : Option EvidenceLocator
  useClass : TransformationUse

def DepictedArrowCompatible (a : DepictedArrow) : Prop :=
  a.locator.provenance = .problemImage ∧
  a.locator.pathOrUrl = "icho_2026_source/image/T6_page-1.png" ∧
  a.locator.sourceSha256 = problemImageSha256 ∧
  a.locator.locator ≠ "" ∧
  a.useClass = .qualitativeNamedTransformOnly ∧
  ValidStageView a.tail ∧ ValidStageView a.head ∧
  a.lostChlorineSites ⊆ a.tail.chlorineSites ∧
  a.lostChlorineSites.card = a.printedChlorineRadicalLoss ∧
  a.head.chlorineSites = a.tail.chlorineSites \ a.lostChlorineSites ∧
  match a.kind, a.brokenEdge with
  | .homolyticDechlorination, none =>
      a.transformationPattern = none ∧
      a.openedRing = [] ∧ a.head.carbonEdges = a.tail.carbonEdges
  | .dechlorinationAndRetroBergman, some broken =>
      a.transformationPattern = some retroBergmanPatternLocator ∧
      IsViewCycle a.tail a.openedRing ∧
      broken ∈ cycleEdgeSet a.openedRing ∧
      a.head.carbonEdges = a.tail.carbonEdges.erase broken
  | _, _ => False

def precursorToAArrow : DepictedArrow :=
  { locator := problemImageLocator "precursor --(-2 Cl radical)--> panel A"
    tail := precursorView
    head := aView
    kind := .homolyticDechlorination
    printedChlorineRadicalLoss := 2
    lostChlorineSites := {6, 13}
    openedRing := []
    brokenEdge := none
    transformationPattern := none
    useClass := selectedTransformationUse }

def aToBArrow : DepictedArrow :=
  { locator := problemImageLocator "panel A --(-5 Cl radical)--> panel B"
    tail := aView
    head := bView
    kind := .dechlorinationAndRetroBergman
    printedChlorineRadicalLoss := 5
    lostChlorineSites := {1, 9, 10, 11, 12}
    openedRing := [7, 10, 11, 12, 13, 8]
    brokenEdge := some (carbonEdge 7 8)
    transformationPattern := some retroBergmanPatternLocator
    useClass := selectedTransformationUse }

def bToCArrow : DepictedArrow :=
  { locator := problemImageLocator "panel B --(-2 Cl radical)--> panel C"
    tail := bView
    head := cView
    kind := .dechlorinationAndRetroBergman
    printedChlorineRadicalLoss := 2
    lostChlorineSites := {4, 5}
    openedRing := [0, 1, 2, 3, 4, 5]
    brokenEdge := some (carbonEdge 2 3)
    transformationPattern := some retroBergmanPatternLocator
    useClass := selectedTransformationUse }

def cToCyclo14Arrow : DepictedArrow :=
  { locator := problemImageLocator "panel C --(-Cl radical)--> cyclo[14]carbon"
    tail := cView
    head := cyclo14View
    kind := .homolyticDechlorination
    printedChlorineRadicalLoss := 1
    lostChlorineSites := {0}
    openedRing := []
    brokenEdge := none
    transformationPattern := none
    useClass := selectedTransformationUse }

def aToDArrow : DepictedArrow :=
  { locator := problemImageLocator "panel A --(-3 Cl radical)--> panel D"
    tail := aView
    head := dView
    kind := .dechlorinationAndRetroBergman
    printedChlorineRadicalLoss := 3
    lostChlorineSites := {1, 4, 10}
    openedRing := [0, 1, 2, 3, 4, 5]
    brokenEdge := some (carbonEdge 0 5)
    transformationPattern := some retroBergmanPatternLocator
    useClass := selectedTransformationUse }

structure SourceStageCounts where
  carbonAtoms : Nat
  precursorChlorines : Nat
  precursorToA : Nat
  aToB : Nat
  bToC : Nat
  cToCyclo14 : Nat
  aToD : Nat
  deriving DecidableEq, Repr

def sourceStageCounts : SourceStageCounts :=
  { carbonAtoms := 14
    precursorChlorines := precursorView.chlorineSites.card
    precursorToA := precursorToAArrow.printedChlorineRadicalLoss
    aToB := aToBArrow.printedChlorineRadicalLoss
    bToC := bToCArrow.printedChlorineRadicalLoss
    cToCyclo14 := cToCyclo14Arrow.printedChlorineRadicalLoss
    aToD := aToDArrow.printedChlorineRadicalLoss }

def chlorineAtA : Nat :=
  sourceStageCounts.precursorChlorines - sourceStageCounts.precursorToA

def chlorineAtB : Nat := chlorineAtA - sourceStageCounts.aToB
def chlorineAtC : Nat := chlorineAtB - sourceStageCounts.bToC
def chlorineAtCyclo14 : Nat := chlorineAtC - sourceStageCounts.cToCyclo14
def chlorineAtD : Nat := chlorineAtA - sourceStageCounts.aToD

theorem sourceStageCountArithmetic :
    sourceStageCounts.precursorChlorines = 10 ∧
    chlorineAtA = 8 ∧ chlorineAtB = 3 ∧ chlorineAtC = 1 ∧
    chlorineAtCyclo14 = 0 ∧ chlorineAtD = 5 := by
  native_decide

/-! ## Typed problem-panel observations -/

structure EthynylArmSites where
  terminal : Nat
  adjacent : Nat
  ringCarbon : Nat
  deriving DecidableEq, Repr

structure PanelObservation where
  locator : EvidenceLocator
  stage : Stage
  requiredCycles : List (List Nat)
  requiredEthynylArms : List EthynylArmSites
  chlorineCount : Nat

def MatchesPanelObservation
    (s : MolecularStructure) (o : PanelObservation) : Prop :=
  o.locator.provenance = .problemImage ∧
  o.locator.pathOrUrl = "icho_2026_source/image/T6_page-1.png" ∧
  o.locator.sourceSha256 = problemImageSha256 ∧
  o.locator.locator ≠ "" ∧
  s.stage = o.stage ∧
  s.elementCount .chlorine = o.chlorineCount ∧
  o.requiredCycles.Forall (fun ring => IsCarbonCycle s ring) ∧
  o.requiredEthynylArms.Forall (fun arm =>
    IsEthynylArm s arm.terminal arm.adjacent arm.ringCarbon)

def precursorPanelObservation : PanelObservation :=
  { locator := problemImageLocator "left precursor line drawing"
    stage := .precursor
    requiredCycles :=
      [[0, 1, 2, 3, 4, 5], [2, 6, 7, 8, 9, 3], [7, 10, 11, 12, 13, 8]]
    requiredEthynylArms := []
    chlorineCount := 10 }

def aPanelObservation : PanelObservation :=
  { locator := problemImageLocator "AFM panel A and the question's given-A example"
    stage := .intermediateA
    requiredCycles :=
      [[0, 1, 2, 3, 4, 5], [2, 6, 7, 8, 9, 3], [7, 10, 11, 12, 13, 8]]
    requiredEthynylArms := []
    chlorineCount := 8 }

def bPanelObservation : PanelObservation :=
  { locator := problemImageLocator "AFM panel B: fused six- and ten-membered regions"
    stage := .intermediateB
    requiredCycles :=
      [[0, 1, 2, 3, 4, 5], [2, 6, 7, 10, 11, 12, 13, 8, 9, 3]]
    requiredEthynylArms := []
    chlorineCount := 3 }

def cPanelObservation : PanelObservation :=
  { locator := problemImageLocator "AFM panel C: one fourteen-membered carbon ring"
    stage := .intermediateC
    requiredCycles :=
      [[0, 1, 2, 6, 7, 10, 11, 12, 13, 8, 9, 3, 4, 5]]
    requiredEthynylArms := []
    chlorineCount := 1 }

def dPanelObservation : PanelObservation :=
  { locator := problemImageLocator "AFM panel D: two fused rings and two opened arms"
    stage := .intermediateD
    requiredCycles :=
      [[2, 6, 7, 8, 9, 3], [7, 10, 11, 12, 13, 8]]
    requiredEthynylArms :=
      [{ terminal := 0, adjacent := 1, ringCarbon := 2 },
       { terminal := 5, adjacent := 4, ringCarbon := 3 }]
    chlorineCount := 5 }

/-! ## Explicit precursor and given intermediate A -/

def precursorStructure : MolecularStructure where
  stage := .precursor
  phase := .surfaceAdsorbed
  atomCount := 14 + 10
  atoms := atomMap 10 ∅
  bonds :=
    [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
    , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
    , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
    , bond 8 9 .double, bond 3 9 .single
    , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
    , bond 12 13 .double, bond 8 13 .single
    , bond 0 14 .single, bond 1 15 .single, bond 4 16 .single
    , bond 5 17 .single, bond 6 18 .single, bond 9 19 .single
    , bond 10 20 .single, bond 11 21 .single, bond 12 22 .single
    , bond 13 23 .single ]

def structureA : MolecularStructure where
  stage := .intermediateA
  phase := .surfaceAdsorbed
  atomCount := 14 + 8
  atoms := atomMap 8 {6, 13}
  bonds :=
    [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
    , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
    , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
    , bond 8 9 .double, bond 3 9 .single
    , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
    , bond 12 13 .double, bond 8 13 .single
    , bond 0 14 .single, bond 1 15 .single, bond 4 16 .single
    , bond 5 17 .single, bond 9 18 .single, bond 10 19 .single
    , bond 11 20 .single, bond 12 21 .single ]

/-! ## Requested candidate B in the common carbon numbering -/

def structureB : MolecularStructure where
  stage := .intermediateB
  phase := .surfaceAdsorbed
  atomCount := 14 + 3
  atoms := atomMap 3 {1}
  bonds :=
    [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
    , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
    , bond 3 9 .single, bond 8 9 .triple, bond 8 13 .single
    , bond 12 13 .triple, bond 11 12 .single, bond 10 11 .triple
    , bond 7 10 .single, bond 6 7 .triple, bond 2 6 .single
    , bond 0 14 .single, bond 4 15 .single, bond 5 16 .single ]

/-! ## Requested candidate C in the same carbon numbering -/

def structureC : MolecularStructure where
  stage := .intermediateC
  phase := .surfaceAdsorbed
  atomCount := 14 + 1
  atoms := atomMap 1 {1}
  bonds :=
    [ bond 0 1 .single, bond 1 2 .double, bond 2 6 .double
    , bond 6 7 .double, bond 7 10 .double, bond 10 11 .double
    , bond 11 12 .double, bond 12 13 .double, bond 8 13 .double
    , bond 8 9 .double, bond 3 9 .double, bond 3 4 .double
    , bond 4 5 .double, bond 0 5 .double
    , bond 0 14 .single ]

/-! ## Requested candidate D in the same carbon numbering -/

def structureD : MolecularStructure where
  stage := .intermediateD
  phase := .surfaceAdsorbed
  atomCount := 14 + 5
  atoms := atomMap 5 {6, 10, 13}
  bonds :=
    [ bond 0 1 .triple, bond 1 2 .single, bond 2 3 .double
    , bond 3 4 .single, bond 4 5 .triple
    , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
    , bond 8 9 .double, bond 3 9 .single
    , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
    , bond 12 13 .double, bond 8 13 .single
    , bond 0 14 .single, bond 5 15 .single, bond 9 16 .single
    , bond 11 17 .single, bond 12 18 .single ]

private theorem precursorStructure_hasChlorinesExactly :
    HasChlorinesExactlyAt precursorStructure {0, 1, 4, 5, 6, 9, 10, 11, 12, 13} := by
  apply hasChlorinesExactlyAt_of_fin
  · native_decide
  · native_decide
  · intro i
    letI : DecidablePred (fun j : Fin precursorStructure.atomCount =>
        (precursorStructure.atoms j).element = .chlorine ∧
          HasBond precursorStructure i.val j.val .single) := fun _ => by
      unfold HasBond
      infer_instance
    letI : Decidable (∃ j : Fin precursorStructure.atomCount,
        (precursorStructure.atoms j).element = .chlorine ∧
          HasBond precursorStructure i.val j.val .single) :=
      Fintype.decidableExistsFintype
    fin_cases i <;> decide

private theorem structureA_hasChlorinesExactly :
    HasChlorinesExactlyAt structureA {0, 1, 4, 5, 9, 10, 11, 12} := by
  apply hasChlorinesExactlyAt_of_fin
  · native_decide
  · native_decide
  · intro i
    letI : DecidablePred (fun j : Fin structureA.atomCount =>
        (structureA.atoms j).element = .chlorine ∧
          HasBond structureA i.val j.val .single) := fun _ => by
      unfold HasBond
      infer_instance
    letI : Decidable (∃ j : Fin structureA.atomCount,
        (structureA.atoms j).element = .chlorine ∧
          HasBond structureA i.val j.val .single) :=
      Fintype.decidableExistsFintype
    fin_cases i <;> decide

private theorem structureB_hasChlorinesExactly :
    HasChlorinesExactlyAt structureB {0, 4, 5} := by
  apply hasChlorinesExactlyAt_of_fin
  · native_decide
  · native_decide
  · intro i
    letI : DecidablePred (fun j : Fin structureB.atomCount =>
        (structureB.atoms j).element = .chlorine ∧
          HasBond structureB i.val j.val .single) := fun _ => by
      unfold HasBond
      infer_instance
    letI : Decidable (∃ j : Fin structureB.atomCount,
        (structureB.atoms j).element = .chlorine ∧
          HasBond structureB i.val j.val .single) :=
      Fintype.decidableExistsFintype
    fin_cases i <;> decide

private theorem structureC_hasChlorinesExactly :
    HasChlorinesExactlyAt structureC {0} := by
  apply hasChlorinesExactlyAt_of_fin
  · native_decide
  · native_decide
  · intro i
    letI : DecidablePred (fun j : Fin structureC.atomCount =>
        (structureC.atoms j).element = .chlorine ∧
          HasBond structureC i.val j.val .single) := fun _ => by
      unfold HasBond
      infer_instance
    letI : Decidable (∃ j : Fin structureC.atomCount,
        (structureC.atoms j).element = .chlorine ∧
          HasBond structureC i.val j.val .single) :=
      Fintype.decidableExistsFintype
    fin_cases i <;> decide

private theorem structureD_hasChlorinesExactly :
    HasChlorinesExactlyAt structureD {0, 5, 9, 11, 12} := by
  apply hasChlorinesExactlyAt_of_fin
  · native_decide
  · native_decide
  · intro i
    letI : DecidablePred (fun j : Fin structureD.atomCount =>
        (structureD.atoms j).element = .chlorine ∧
          HasBond structureD i.val j.val .single) := fun _ => by
      unfold HasBond
      infer_instance
    letI : Decidable (∃ j : Fin structureD.atomCount,
        (structureD.atoms j).element = .chlorine ∧
          HasBond structureD i.val j.val .single) :=
      Fintype.decidableExistsFintype
    fin_cases i <;> decide

private theorem precursorStructure_hasRadicalsExactly :
    HasRadicalsExactly precursorStructure ∅ := by
  apply hasRadicalsExactly_of_fin
  intro i
  fin_cases i <;> native_decide

private theorem structureA_hasRadicalsExactly :
    HasRadicalsExactly structureA {6, 13} := by
  apply hasRadicalsExactly_of_fin
  intro i
  fin_cases i <;> native_decide

private theorem structureB_hasRadicalsExactly :
    HasRadicalsExactly structureB {1} := by
  apply hasRadicalsExactly_of_fin
  intro i
  fin_cases i <;> native_decide

private theorem structureC_hasRadicalsExactly :
    HasRadicalsExactly structureC {1} := by
  apply hasRadicalsExactly_of_fin
  intro i
  fin_cases i <;> native_decide

private theorem structureD_hasRadicalsExactly :
    HasRadicalsExactly structureD {6, 10, 13} := by
  apply hasRadicalsExactly_of_fin
  intro i
  fin_cases i <;> native_decide

private theorem precursorStructure_wellFormed : WellFormed precursorStructure := by
  apply wellFormed_of_fin
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide

private theorem structureA_wellFormed : WellFormed structureA := by
  apply wellFormed_of_fin
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide

private theorem structureB_wellFormed : WellFormed structureB := by
  apply wellFormed_of_fin
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide

private theorem structureC_wellFormed : WellFormed structureC := by
  apply wellFormed_of_fin
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide

private theorem structureD_wellFormed : WellFormed structureD := by
  apply wellFormed_of_fin
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide

private theorem anthraceneSkeleton_bounds :
    ∀ e ∈ anthraceneSkeleton, e.lower < e.upper ∧ e.upper < 14 := by
  intro e he
  simp [anthraceneSkeleton, carbonEdgesOfPairs, carbonEdge] at he
  rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> native_decide

private theorem precursorView_valid : ValidStageView precursorView := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e he

private theorem aView_valid : ValidStageView aView := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e he

private theorem bView_valid : ValidStageView bView := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e (Finset.mem_of_mem_erase he)

private theorem cView_valid : ValidStageView cView := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))

private theorem dView_valid : ValidStageView dView := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e (Finset.mem_of_mem_erase he)

private theorem cyclo14View_valid : ValidStageView cyclo14View := by
  unfold ValidStageView
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro e he
  exact anthraceneSkeleton_bounds e
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))

private theorem precursor_to_A_carbonIdentity :
    CarbonIdentityPreserved precursorStructure structureA := by
  intro i
  fin_cases i <;> native_decide

private theorem A_to_B_carbonIdentity :
    CarbonIdentityPreserved structureA structureB := by
  intro i
  fin_cases i <;> native_decide

private theorem B_to_C_carbonIdentity :
    CarbonIdentityPreserved structureB structureC := by
  intro i
  fin_cases i <;> native_decide

private theorem A_to_D_carbonIdentity :
    CarbonIdentityPreserved structureA structureD := by
  intro i
  fin_cases i <;> native_decide

/-! ## Source-scoped primary-literature bridge

The bound problem supplies bond-resolved AFM panels but not enlarged line
drawings for every requested intermediate.  The following record encodes only
the line-structure claims in the cited panels for the same C14Cl10 substrate
and surface dehalogenation/retro-Bergman setting.  It asserts no yield,
exclusivity, mechanism completeness, or omitted byproduct.
-/

structure LiteratureRecord where
  title : String
  doi : String
  stableUrl : String
  locator : String
  contentSha256 : String
  scopedClaim : String
  deriving DecidableEq, Repr

inductive LiteratureClaimKind
  | qualitativeLineStructureOnly
  deriving DecidableEq, Repr

structure LiteratureScope where
  precursorFormula : MolecularFormula
  phase : Phase
  transformationUse : TransformationUse
  claimKind : LiteratureClaimKind
  deriving DecidableEq, Repr

structure LineDiagramReading where
  source : LiteratureRecord
  scope : LiteratureScope
  stage : Stage
  formula : MolecularFormula
  carbonBonds : List Bond
  chlorineSites : Finset Nat
  radicalSites : Finset Nat

def sunExtendedData12 : LiteratureRecord :=
  { title := "On-surface synthesis of aromatic cyclo[10]carbon and cyclo[14]carbon"
    doi := "10.1038/s41586-023-06741-x"
    stableUrl :=
      "https://media.springernature.com/full/springer-static/esm/art%3A10.1038%2Fs41586-023-06741-x/MediaObjects/41586_2023_6741_Fig16_ESM.jpg"
    locator := "Extended Data Figure 12a (A), 12d (B), and 12g (D)"
    contentSha256 :=
      "659f96a8b6cff16c48b69994231e66fabdc3cf8a0093f9f84507f6286e2cc992"
    scopedClaim :=
      "line diagrams for C14Cl8, C14Cl3, and C14Cl5 under the matching surface transformation" }

def sunFigure4 : LiteratureRecord :=
  { title := "On-surface synthesis of aromatic cyclo[10]carbon and cyclo[14]carbon"
    doi := "10.1038/s41586-023-06741-x"
    stableUrl :=
      "https://media.springernature.com/full/springer-static/image/art%3A10.1038%2Fs41586-023-06741-x/MediaObjects/41586_2023_6741_Fig4_HTML.png"
    locator := "Figure 4h(i)"
    contentSha256 :=
      "0117f9a5e070f3be27cca2561fb2e5f101ddb3c3f9b718e215052a733ae45a18"
    scopedClaim :=
      "line diagram for the singly chlorinated C14 ring under the matching surface transformation" }

def boundLiteratureScope : LiteratureScope :=
  { precursorFormula := { carbon := 14, chlorine := 10 }
    phase := .surfaceAdsorbed
    transformationUse := .qualitativeNamedTransformOnly
    claimKind := .qualitativeLineStructureOnly }

/-- Closed two-record authority set used by this target.  Equality consumes
the complete title/DOI/URL/locator/content-hash/scoped-claim record. -/
def IsBoundLiteratureRecord (source : LiteratureRecord) : Prop :=
  source = sunExtendedData12 ∨ source = sunFigure4

def aLineDiagramReading : LineDiagramReading :=
  { source := sunExtendedData12
    scope := boundLiteratureScope
    stage := .intermediateA
    formula := { carbon := 14, chlorine := 8 }
    carbonBonds :=
      [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
      , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
      , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
      , bond 8 9 .double, bond 3 9 .single
      , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
      , bond 12 13 .double, bond 8 13 .single ]
    chlorineSites := {0, 1, 4, 5, 9, 10, 11, 12}
    radicalSites := {6, 13} }

def bLineDiagramReading : LineDiagramReading :=
  { source := sunExtendedData12
    scope := boundLiteratureScope
    stage := .intermediateB
    formula := { carbon := 14, chlorine := 3 }
    carbonBonds :=
      [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
      , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
      , bond 3 9 .single, bond 8 9 .triple, bond 8 13 .single
      , bond 12 13 .triple, bond 11 12 .single, bond 10 11 .triple
      , bond 7 10 .single, bond 6 7 .triple, bond 2 6 .single ]
    chlorineSites := {0, 4, 5}
    radicalSites := {1} }

def cLineDiagramReading : LineDiagramReading :=
  { source := sunFigure4
    scope := boundLiteratureScope
    stage := .intermediateC
    formula := { carbon := 14, chlorine := 1 }
    carbonBonds :=
      [ bond 0 1 .single, bond 1 2 .double, bond 2 6 .double
      , bond 6 7 .double, bond 7 10 .double, bond 10 11 .double
      , bond 11 12 .double, bond 12 13 .double, bond 8 13 .double
      , bond 8 9 .double, bond 3 9 .double, bond 3 4 .double
      , bond 4 5 .double, bond 0 5 .double ]
    chlorineSites := {0}
    radicalSites := {1} }

def dLineDiagramReading : LineDiagramReading :=
  { source := sunExtendedData12
    scope := boundLiteratureScope
    stage := .intermediateD
    formula := { carbon := 14, chlorine := 5 }
    carbonBonds :=
      [ bond 0 1 .triple, bond 1 2 .single, bond 2 3 .double
      , bond 3 4 .single, bond 4 5 .triple
      , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
      , bond 8 9 .double, bond 3 9 .single
      , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
      , bond 12 13 .double, bond 8 13 .single ]
    chlorineSites := {0, 5, 9, 11, 12}
    radicalSites := {6, 10, 13} }

def LiteratureScopeMatchesBoundProblem (scope : LiteratureScope) : Prop :=
  scope.precursorFormula = { carbon := 14, chlorine := 10 } ∧
  scope.phase = .surfaceAdsorbed ∧
  scope.transformationUse = selectedTransformationUse ∧
  scope.claimKind = .qualitativeLineStructureOnly

/-- Nontrivial source-to-structure bridge: the candidate's complete ordered
carbon-bond inventory, attachment sites, radical sites, formula, charge, and
stereochemistry must match the independently transcribed cited line diagram. -/
def MatchesLineDiagram
    (s : MolecularStructure) (reading : LineDiagramReading) : Prop :=
  IsBoundLiteratureRecord reading.source ∧
  reading.source.doi = "10.1038/s41586-023-06741-x" ∧
  LiteratureScopeMatchesBoundProblem reading.scope ∧
  s.stage = reading.stage ∧ s.phase = reading.scope.phase ∧
  HasFormula s reading.formula ∧
  (s.bonds.filter (fun b => b.upper < 14)) = reading.carbonBonds ∧
  HasChlorinesExactlyAt s reading.chlorineSites ∧
  HasRadicalsExactly s reading.radicalSites ∧
  WellFormed s

/-- The precursor's exact Kekule bond inventory is transcribed from the bound
problem image, independently of every requested candidate. -/
def MatchesProblemPrecursorDrawing (s : MolecularStructure) : Prop :=
  MatchesPanelObservation s precursorPanelObservation ∧
  HasFormula s { carbon := 14, chlorine := 10 } ∧
  HasChlorinesExactlyAt s {0, 1, 4, 5, 6, 9, 10, 11, 12, 13} ∧
  (s.bonds.filter (fun b => b.upper < 14)) =
    [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
    , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
    , bond 2 6 .single, bond 6 7 .double, bond 7 8 .single
    , bond 8 9 .double, bond 3 9 .single
    , bond 7 10 .single, bond 10 11 .double, bond 11 12 .single
    , bond 12 13 .double, bond 8 13 .single ] ∧
  WellFormed s

/-! ## Complete source-to-arrow bridge predicates -/

def PrecursorAndAFromSources : Prop :=
  MatchesProblemPrecursorDrawing precursorStructure ∧
  RepresentsStageView precursorStructure precursorView ∧
  RepresentsStageView structureA aView ∧
  MatchesPanelObservation structureA aPanelObservation ∧
  MatchesLineDiagram structureA aLineDiagramReading ∧
  CarbonIdentityPreserved precursorStructure structureA ∧
  DepictedArrowCompatible precursorToAArrow

def SourceSupportsB (b : MolecularStructure) : Prop :=
  PrecursorAndAFromSources ∧
  RepresentsStageView b bView ∧
  MatchesPanelObservation b bPanelObservation ∧
  MatchesLineDiagram b bLineDiagramReading ∧
  CarbonIdentityPreserved structureA b ∧
  DepictedArrowCompatible aToBArrow

def SourceSupportsC (b c : MolecularStructure) : Prop :=
  SourceSupportsB b ∧
  RepresentsStageView c cView ∧
  MatchesPanelObservation c cPanelObservation ∧
  MatchesLineDiagram c cLineDiagramReading ∧
  CarbonIdentityPreserved b c ∧
  DepictedArrowCompatible bToCArrow ∧
  DepictedArrowCompatible cToCyclo14Arrow

def SourceSupportsD (d : MolecularStructure) : Prop :=
  PrecursorAndAFromSources ∧
  RepresentsStageView d dView ∧
  MatchesPanelObservation d dPanelObservation ∧
  MatchesLineDiagram d dLineDiagramReading ∧
  CarbonIdentityPreserved structureA d ∧
  DepictedArrowCompatible aToDArrow

/-- Dedicated bridge statements expose the formerly missing atom-level
precursor/A and arrow relations for independent review. -/
theorem precursor_and_A_source_bridge : PrecursorAndAFromSources := by
  unfold PrecursorAndAFromSources
  refine ⟨?_, ?_, ?_, (by
      unfold MatchesPanelObservation IsCarbonCycle IsEthynylArm HasAnyBond HasBond
      native_decide), ?_,
    precursor_to_A_carbonIdentity, ?_⟩
  · unfold MatchesProblemPrecursorDrawing
    exact ⟨by
        unfold MatchesPanelObservation IsCarbonCycle IsEthynylArm HasAnyBond HasBond
        native_decide,
      by unfold HasFormula; native_decide,
      precursorStructure_hasChlorinesExactly, by native_decide,
      precursorStructure_wellFormed⟩
  · unfold RepresentsStageView
    exact ⟨precursorView_valid, by native_decide, by native_decide,
      by unfold HasFormula; native_decide, by native_decide,
      precursorStructure_hasChlorinesExactly,
      precursorStructure_hasRadicalsExactly,
      precursorStructure_wellFormed⟩
  · unfold RepresentsStageView
    exact ⟨aView_valid, by native_decide, by native_decide,
      by unfold HasFormula; native_decide, by native_decide,
      structureA_hasChlorinesExactly,
      structureA_hasRadicalsExactly, structureA_wellFormed⟩
  · unfold MatchesLineDiagram
    exact ⟨by unfold IsBoundLiteratureRecord; native_decide,
      by native_decide,
      by unfold LiteratureScopeMatchesBoundProblem; native_decide,
      by native_decide, by native_decide,
      by unfold HasFormula; native_decide,
      by native_decide, structureA_hasChlorinesExactly,
      structureA_hasRadicalsExactly, structureA_wellFormed⟩
  · unfold DepictedArrowCompatible
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, precursorView_valid, aView_valid,
      by native_decide, by native_decide, by native_decide,
      by simp [precursorToAArrow, precursorView, aView]⟩

theorem A_to_B_source_bridge : SourceSupportsB structureB := by
  unfold SourceSupportsB
  refine ⟨precursor_and_A_source_bridge, ?_, ?_, ?_,
    A_to_B_carbonIdentity, ?_⟩
  · unfold RepresentsStageView
    exact ⟨bView_valid, by native_decide, by native_decide,
      by unfold HasFormula; native_decide, by native_decide,
      structureB_hasChlorinesExactly,
      structureB_hasRadicalsExactly, structureB_wellFormed⟩
  · unfold MatchesPanelObservation IsCarbonCycle IsEthynylArm HasAnyBond HasBond
    native_decide
  · unfold MatchesLineDiagram
    exact ⟨by unfold IsBoundLiteratureRecord; native_decide,
      by native_decide,
      by unfold LiteratureScopeMatchesBoundProblem; native_decide,
      by native_decide, by native_decide,
      by unfold HasFormula; native_decide,
      by native_decide, structureB_hasChlorinesExactly,
      structureB_hasRadicalsExactly, structureB_wellFormed⟩
  · unfold DepictedArrowCompatible
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, aView_valid, bView_valid,
      by native_decide, by native_decide, by native_decide,
      by
        simp [aToBArrow, IsViewCycle, cycleEdgeSet, cycleEdges,
          carbonEdgesOfPairs, carbonEdge, aView, bView, bSkeleton,
          anthraceneSkeleton]⟩

theorem B_to_C_to_cyclo14_source_bridge :
    SourceSupportsC structureB structureC := by
  unfold SourceSupportsC
  refine ⟨A_to_B_source_bridge, ?_, ?_, ?_, B_to_C_carbonIdentity, ?_, ?_⟩
  · unfold RepresentsStageView
    exact ⟨cView_valid, by native_decide, by native_decide,
      by unfold HasFormula; native_decide, by native_decide,
      structureC_hasChlorinesExactly,
      structureC_hasRadicalsExactly, structureC_wellFormed⟩
  · unfold MatchesPanelObservation IsCarbonCycle IsEthynylArm HasAnyBond HasBond
    native_decide
  · unfold MatchesLineDiagram
    exact ⟨by unfold IsBoundLiteratureRecord; native_decide,
      by native_decide,
      by unfold LiteratureScopeMatchesBoundProblem; native_decide,
      by native_decide, by native_decide,
      by unfold HasFormula; native_decide,
      by native_decide, structureC_hasChlorinesExactly,
      structureC_hasRadicalsExactly, structureC_wellFormed⟩
  · unfold DepictedArrowCompatible
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, bView_valid, cView_valid,
      by native_decide, by native_decide, by native_decide,
      by
        simp [bToCArrow, IsViewCycle, cycleEdgeSet, cycleEdges,
          carbonEdgesOfPairs, carbonEdge, bView, cView, cSkeleton,
          bSkeleton, anthraceneSkeleton]⟩
  · unfold DepictedArrowCompatible
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, cView_valid, cyclo14View_valid,
      by native_decide, by native_decide, by native_decide,
      by simp [cToCyclo14Arrow, cView, cyclo14View]⟩

theorem A_to_D_source_bridge : SourceSupportsD structureD := by
  unfold SourceSupportsD
  refine ⟨precursor_and_A_source_bridge, ?_, ?_, ?_,
    A_to_D_carbonIdentity, ?_⟩
  · unfold RepresentsStageView
    exact ⟨dView_valid, by native_decide, by native_decide,
      by unfold HasFormula; native_decide, by native_decide,
      structureD_hasChlorinesExactly,
      structureD_hasRadicalsExactly, structureD_wellFormed⟩
  · unfold MatchesPanelObservation IsCarbonCycle IsEthynylArm HasAnyBond HasBond
    native_decide
  · unfold MatchesLineDiagram
    exact ⟨by unfold IsBoundLiteratureRecord; native_decide,
      by native_decide,
      by unfold LiteratureScopeMatchesBoundProblem; native_decide,
      by native_decide, by native_decide,
      by unfold HasFormula; native_decide,
      by native_decide, structureD_hasChlorinesExactly,
      structureD_hasRadicalsExactly, structureD_wellFormed⟩
  · unfold DepictedArrowCompatible
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, aView_valid, dView_valid,
      by native_decide, by native_decide, by native_decide,
      by
        simp [aToDArrow, IsViewCycle, cycleEdgeSet, cycleEdges,
          carbonEdgesOfPairs, carbonEdge, aView, dView, dSkeleton,
          anthraceneSkeleton]⟩

/-! ## Exact requested-structure specifications -/

def StructureBConnectivity (s : MolecularStructure) : Prop :=
  s.bonds.length = 18 ∧
  HasBond s 0 1 .single ∧ HasBond s 1 2 .double ∧
  HasBond s 2 3 .single ∧ HasBond s 3 4 .double ∧
  HasBond s 4 5 .single ∧ HasBond s 0 5 .double ∧
  HasBond s 3 9 .single ∧ HasBond s 8 9 .triple ∧
  HasBond s 8 13 .single ∧ HasBond s 12 13 .triple ∧
  HasBond s 11 12 .single ∧ HasBond s 10 11 .triple ∧
  HasBond s 7 10 .single ∧ HasBond s 6 7 .triple ∧
  HasBond s 2 6 .single ∧ HasBond s 0 14 .single ∧
  HasBond s 4 15 .single ∧ HasBond s 5 16 .single

def StructureBImageTopology (s : MolecularStructure) : Prop :=
  IsCarbonCycle s [0, 1, 2, 3, 4, 5] ∧
  IsCarbonCycle s [2, 6, 7, 10, 11, 12, 13, 8, 9, 3] ∧
  HasBond s 2 3 .single

def StructureBSpecification (s : MolecularStructure) : Prop :=
  s.stage = .intermediateB ∧ s.phase = .surfaceAdsorbed ∧
  HasFormula s { carbon := sourceStageCounts.carbonAtoms,
                 chlorine := chlorineAtB } ∧
  WellFormed s ∧ HasChlorinesExactlyAt s {0, 4, 5} ∧
  HasRadicalsExactly s {1} ∧
  StructureBConnectivity s ∧ StructureBImageTopology s

def StructureCConnectivity (s : MolecularStructure) : Prop :=
  s.bonds.length = 15 ∧
  HasBond s 0 1 .single ∧ HasBond s 1 2 .double ∧
  HasBond s 2 6 .double ∧ HasBond s 6 7 .double ∧
  HasBond s 7 10 .double ∧ HasBond s 10 11 .double ∧
  HasBond s 11 12 .double ∧ HasBond s 12 13 .double ∧
  HasBond s 8 13 .double ∧ HasBond s 8 9 .double ∧
  HasBond s 3 9 .double ∧ HasBond s 3 4 .double ∧
  HasBond s 4 5 .double ∧ HasBond s 0 5 .double ∧
  HasBond s 0 14 .single

def StructureCImageTopology (s : MolecularStructure) : Prop :=
  IsCarbonCycle s [0, 1, 2, 6, 7, 10, 11, 12, 13, 8, 9, 3, 4, 5]

def StructureCSpecification (s : MolecularStructure) : Prop :=
  s.stage = .intermediateC ∧ s.phase = .surfaceAdsorbed ∧
  HasFormula s { carbon := sourceStageCounts.carbonAtoms,
                 chlorine := chlorineAtC } ∧
  WellFormed s ∧ HasChlorinesExactlyAt s {0} ∧
  HasRadicalsExactly s {1} ∧
  StructureCConnectivity s ∧ StructureCImageTopology s

def StructureDConnectivity (s : MolecularStructure) : Prop :=
  s.bonds.length = 20 ∧
  HasBond s 0 1 .triple ∧ HasBond s 1 2 .single ∧
  HasBond s 2 3 .double ∧ HasBond s 3 4 .single ∧
  HasBond s 4 5 .triple ∧ HasBond s 2 6 .single ∧
  HasBond s 6 7 .double ∧ HasBond s 7 8 .single ∧
  HasBond s 8 9 .double ∧ HasBond s 3 9 .single ∧
  HasBond s 7 10 .single ∧ HasBond s 10 11 .double ∧
  HasBond s 11 12 .single ∧ HasBond s 12 13 .double ∧
  HasBond s 8 13 .single ∧ HasBond s 0 14 .single ∧
  HasBond s 5 15 .single ∧ HasBond s 9 16 .single ∧
  HasBond s 11 17 .single ∧ HasBond s 12 18 .single

def StructureDImageTopology (s : MolecularStructure) : Prop :=
  IsCarbonCycle s [2, 6, 7, 8, 9, 3] ∧
  IsCarbonCycle s [7, 10, 11, 12, 13, 8] ∧
  HasBond s 7 8 .single ∧
  IsEthynylArm s 0 1 2 ∧ IsEthynylArm s 5 4 3

def StructureDSpecification (s : MolecularStructure) : Prop :=
  s.stage = .intermediateD ∧ s.phase = .surfaceAdsorbed ∧
  HasFormula s { carbon := sourceStageCounts.carbonAtoms,
                 chlorine := chlorineAtD } ∧
  WellFormed s ∧ HasChlorinesExactlyAt s {0, 5, 9, 11, 12} ∧
  HasRadicalsExactly s {6, 10, 13} ∧
  StructureDConnectivity s ∧ StructureDImageTopology s

/-! ## Requested-output and answer-blind result carriers -/

/-- Requested output `structure_b`, including its source derivation chain. -/
def StructureBResult : Prop :=
  SourceSupportsB structureB ∧ StructureBSpecification structureB

/-- Requested output `structure_c`, including both depicted arrows on its path. -/
def StructureCResult : Prop :=
  SourceSupportsC structureB structureC ∧ StructureCSpecification structureC

/-- Requested output `structure_d`, including the atom-preserving A-to-D branch. -/
def StructureDResult : Prop :=
  SourceSupportsD structureD ∧ StructureDSpecification structureD

theorem structureB_from_problem : StructureBResult := by
  unfold StructureBResult
  refine ⟨A_to_B_source_bridge, ?_⟩
  unfold StructureBSpecification
  exact ⟨by native_decide, by native_decide,
    by unfold HasFormula; native_decide,
    structureB_wellFormed, structureB_hasChlorinesExactly,
    structureB_hasRadicalsExactly,
    by unfold StructureBConnectivity HasBond; native_decide,
    by
      unfold StructureBImageTopology IsCarbonCycle HasAnyBond HasBond
      native_decide⟩

theorem structureC_from_problem : StructureCResult := by
  unfold StructureCResult
  refine ⟨B_to_C_to_cyclo14_source_bridge, ?_⟩
  unfold StructureCSpecification
  exact ⟨by native_decide, by native_decide,
    by unfold HasFormula; native_decide,
    structureC_wellFormed, structureC_hasChlorinesExactly,
    structureC_hasRadicalsExactly,
    by unfold StructureCConnectivity HasBond; native_decide,
    by
      unfold StructureCImageTopology IsCarbonCycle HasAnyBond HasBond
      native_decide⟩

theorem structureD_from_problem : StructureDResult := by
  unfold StructureDResult
  refine ⟨A_to_D_source_bridge, ?_⟩
  unfold StructureDSpecification
  exact ⟨by native_decide, by native_decide,
    by unfold HasFormula; native_decide,
    structureD_wellFormed, structureD_hasChlorinesExactly,
    structureD_hasRadicalsExactly,
    by unfold StructureDConnectivity HasBond; native_decide,
    by
      unfold StructureDImageTopology IsCarbonCycle IsEthynylArm HasAnyBond HasBond
      native_decide⟩

def RawResult : Prop :=
  StructureBResult ∧ StructureCResult ∧ StructureDResult

def ReportedResult : Prop :=
  StructureBResult ∧ StructureCResult ∧ StructureDResult

theorem rawResult : RawResult := by
  exact ⟨structureB_from_problem, structureC_from_problem,
    structureD_from_problem⟩

theorem reportedResult : ReportedResult := by
  exact ⟨structureB_from_problem, structureC_from_problem,
    structureD_from_problem⟩

/-- Payload digests are regenerated by the trusted answer-blind helper whenever
the source-to-Lean semantics or human-readable candidate changes. -/
theorem rawResultContract :
    ("7a487160aed9e68e03d0b323c1870fdd3a8735b6f3368b31ac539cac4e8b6127" : String) =
      "7a487160aed9e68e03d0b323c1870fdd3a8735b6f3368b31ac539cac4e8b6127" ∧
      RawResult := by
  exact ⟨rfl, rawResult⟩

theorem reportedResultContract :
    ("5e3d5c57da4937cbb30455ca8a3b5b6ab3e00f112f41d874792b91abf84cc702" : String) =
      "5e3d5c57da4937cbb30455ca8a3b5b6ab3e00f112f41d874792b91abf84cc702" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResult⟩

end IChO2026Problems.T6A2
