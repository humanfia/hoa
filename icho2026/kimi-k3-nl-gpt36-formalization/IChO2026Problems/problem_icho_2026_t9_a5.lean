import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 9.5

This file formalizes the requested structure of intermediate `L` on the
seven-unit beta-cyclodextrin template.  The product is not represented by a
name or a string: `molecularGraph` expands the complete heavy-atom
connectivity (including every benzyl group), stores charge, radical, bond
order, and attached-hydrogen data, and `ExpandedAtom` exposes each hydrogen as
an individual atom.  The five retained stereocentres in every glucose residue
are recorded separately and checked against the graph.

The two depicted transformations are used only as a
`qualitativeNamedTransformOnly` source-arrow constraint.  No yield,
completion percentage, phase, unprinted byproduct, or material stream is
asserted.
-/

namespace IChO2026Problems.T9A5

/-! ## Atom- and bond-level vocabulary -/

inductive Element where
  | hydrogen
  | carbon
  | oxygen
  deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | single
  | double
  deriving DecidableEq, Fintype, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2

structure AtomSpec where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  deriving DecidableEq, Repr

def neutralAtom (element : Element) (attachedHydrogens : ℕ) : AtomSpec where
  element := element
  formalCharge := 0
  radicalElectrons := 0
  attachedHydrogens := attachedHydrogens

structure Bond (α : Type) where
  left : α
  right : α
  order : BondOrder
  deriving DecidableEq, Repr

def bond {α : Type} (left right : α)
    (order : BondOrder := .single) : Bond α :=
  { left := left, right := right, order := order }

def Bond.Connects {α : Type} (e : Bond α) (a b : α) : Prop :=
  (e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)

structure MolecularGraph (α : Type) where
  atom : α → AtomSpec
  bonds : List (Bond α)

def MolecularGraph.Bonded {α : Type} (g : MolecularGraph α)
    (a b : α) (order : BondOrder) : Prop :=
  ∃ e ∈ g.bonds, e.Connects a b ∧ e.order = order

/-- Bond existence is decidable by searching the graph's finite bond list. -/
private instance instDecidableBonded {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) (order : BondOrder) :
    Decidable (g.Bonded a b order) := by
  unfold MolecularGraph.Bonded Bond.Connects
  infer_instance

/-- Every attached hydrogen has its own vertex in this expanded carrier. -/
def ExpandedAtom {α : Type} (g : MolecularGraph α) : Type :=
  Sum α (Σ a : α, Fin (g.atom a).attachedHydrogens)

def ExpandedAtom.element {α : Type} {g : MolecularGraph α} :
    ExpandedAtom g → Element
  | .inl a => (g.atom a).element
  | .inr _ => .hydrogen

def MolecularGraph.ExpandedBonded {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (x y : ExpandedAtom g)
    (order : BondOrder) : Prop :=
  match x, y with
  | .inl a, .inl b => g.Bonded a b order
  | .inl a, .inr ⟨b, _⟩ => a = b ∧ order = .single
  | .inr ⟨a, _⟩, .inl b => a = b ∧ order = .single
  | .inr _, .inr _ => False

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def MolecularGraph.formula {α : Type} [Fintype α]
    (g : MolecularGraph α) : MolecularFormula where
  carbon := ∑ a : α, if (g.atom a).element = .carbon then 1 else 0
  hydrogen := ∑ a : α,
    ((g.atom a).attachedHydrogens +
      if (g.atom a).element = .hydrogen then 1 else 0)
  oxygen := ∑ a : α, if (g.atom a).element = .oxygen then 1 else 0

def Element.neutralValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2

def MolecularGraph.incidentValence {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a : α) : ℕ :=
  (g.bonds.map fun e =>
    if e.left = a ∨ e.right = a then e.order.valence else 0).sum

def MolecularGraph.NoSelfBonds {α : Type}
    (g : MolecularGraph α) : Prop :=
  ∀ e ∈ g.bonds, e.left ≠ e.right

def MolecularGraph.NoDuplicateBonds {α : Type}
    (g : MolecularGraph α) : Prop :=
  g.bonds.Pairwise (fun e f => ¬ e.Connects f.left f.right)

def MolecularGraph.NeutralClosedValence {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  ∀ a,
    (g.atom a).formalCharge = 0 ∧
    (g.atom a).radicalElectrons = 0 ∧
    g.incidentValence a + (g.atom a).attachedHydrogens =
      (g.atom a).element.neutralValence

inductive MolecularGraph.Reachable {α : Type}
    (g : MolecularGraph α) : α → α → Prop
  | refl (a : α) : g.Reachable a a
  | tail {a b c : α} (h : g.Reachable a b) (order : BondOrder)
      (hbond : g.Bonded b c order) : g.Reachable a c

def MolecularGraph.Connected {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ a b, g.Reachable a b

def MolecularGraph.WellFormedClosed {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  g.NoSelfBonds ∧
  g.NoDuplicateBonds ∧
  g.NeutralClosedValence ∧
  g.Connected

private theorem bonded_symm {α : Type} {g : MolecularGraph α}
    {a b : α} {order : BondOrder} (h : g.Bonded a b order) :
    g.Bonded b a order := by
  rcases h with ⟨e, he, hconn, horder⟩
  refine ⟨e, he, ?_, horder⟩
  rcases hconn with hconn | hconn
  · exact Or.inr hconn
  · exact Or.inl hconn

private theorem reachable_of_bonded {α : Type} {g : MolecularGraph α}
    {a b : α} {order : BondOrder} (h : g.Bonded a b order) :
    g.Reachable a b :=
  .tail (.refl a) order h

private theorem reachable_trans {α : Type} {g : MolecularGraph α}
    {a b c : α} (hab : g.Reachable a b) (hbc : g.Reachable b c) :
    g.Reachable a c := by
  induction hbc with
  | refl => exact hab
  | tail _ order hbond ih => exact .tail ih order hbond

private theorem reachable_symm {α : Type} {g : MolecularGraph α}
    {a b : α} (h : g.Reachable a b) : g.Reachable b a := by
  induction h with
  | refl => exact .refl _
  | tail _ order hbond ih =>
      exact reachable_trans (reachable_of_bonded (bonded_symm hbond)) ih

/-! ## Seven-unit beta-CD template and source provenance -/

/-- The seven numbered primary boxes and the `(OH)₁₄` secondary-rim label on
page 3 give this residue carrier. -/
abbrev Residue := Fin 7

def nextResidue (i : Residue) : Residue := i + 1

def previousResidue (i : Residue) : Residue := i + 6

inductive HydroxylPosition where
  | atC2
  | atC3
  | atC6
  deriving DecidableEq, Fintype, Repr

abbrev HydroxylSite := Residue × HydroxylPosition

inductive SiteState where
  | freeHydroxyl
  | benzylEther
  deriving DecidableEq, Fintype, Repr

inductive SourceProvenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

def residueCarrierProvenance : SourceProvenance := .problemImage

def hydroxylPositionProvenance : SourceProvenance := .problemImage

def directingRuleProvenance : SourceProvenance := .problemText

def primarySite (i : Residue) : HydroxylSite := (i, .atC6)

def secondarySite2 (i : Residue) : HydroxylSite := (i, .atC2)

def secondarySite3 (i : Residue) : HydroxylSite := (i, .atC3)

inductive CoreLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | oxygenAtC2
  | oxygenAtC3
  | oxygenAtC6
  deriving DecidableEq, Fintype, Repr

abbrev CoreAtom := Residue × CoreLocalAtom

def oxygenAtom : HydroxylSite → CoreAtom
  | (i, .atC2) => (i, .oxygenAtC2)
  | (i, .atC3) => (i, .oxygenAtC3)
  | (i, .atC6) => (i, .oxygenAtC6)

inductive BenzylAtom where
  | methylene
  | ipso
  | orthoA
  | metaA
  | para
  | metaB
  | orthoB
  deriving DecidableEq, Fintype, Repr

/-- Benzyl atoms exist exactly at sites whose computed state is
`benzylEther`; no dummy atoms are introduced at free-OH sites. -/
abbrev ProtectedSite (state : HydroxylSite → SiteState) :=
  { s : HydroxylSite // state s = .benzylEther }

abbrev MoleculeAtom (state : HydroxylSite → SiteState) :=
  Sum CoreAtom (ProtectedSite state × BenzylAtom)

def coreAtomSpec (state : HydroxylSite → SiteState) :
    CoreAtom → AtomSpec
  | (_, .c1) | (_, .c2) | (_, .c3) | (_, .c4) | (_, .c5) =>
      neutralAtom .carbon 1
  | (_, .c6) => neutralAtom .carbon 2
  | (_, .ringO5) | (_, .glycosidicO) => neutralAtom .oxygen 0
  | (i, .oxygenAtC2) =>
      neutralAtom .oxygen (if state (secondarySite2 i) = .freeHydroxyl then 1 else 0)
  | (i, .oxygenAtC3) =>
      neutralAtom .oxygen (if state (secondarySite3 i) = .freeHydroxyl then 1 else 0)
  | (i, .oxygenAtC6) =>
      neutralAtom .oxygen (if state (primarySite i) = .freeHydroxyl then 1 else 0)

def benzylAtomSpec : BenzylAtom → AtomSpec
  | .methylene => neutralAtom .carbon 2
  | .ipso => neutralAtom .carbon 0
  | .orthoA | .metaA | .para | .metaB | .orthoB => neutralAtom .carbon 1

def moleculeAtomSpec (state : HydroxylSite → SiteState) :
    MoleculeAtom state → AtomSpec
  | .inl a => coreAtomSpec state a
  | .inr (_, a) => benzylAtomSpec a

def coreBonds (state : HydroxylSite → SiteState) :
    List (Bond (MoleculeAtom state)) :=
  (List.ofFn fun i : Residue =>
    [ bond (Sum.inl (i, .ringO5)) (Sum.inl (i, .c1))
    , bond (Sum.inl (i, .c1)) (Sum.inl (i, .c2))
    , bond (Sum.inl (i, .c2)) (Sum.inl (i, .c3))
    , bond (Sum.inl (i, .c3)) (Sum.inl (i, .c4))
    , bond (Sum.inl (i, .c4)) (Sum.inl (i, .c5))
    , bond (Sum.inl (i, .c5)) (Sum.inl (i, .ringO5))
    , bond (Sum.inl (i, .c5)) (Sum.inl (i, .c6))
    , bond (Sum.inl (i, .c2)) (Sum.inl (i, .oxygenAtC2))
    , bond (Sum.inl (i, .c3)) (Sum.inl (i, .oxygenAtC3))
    , bond (Sum.inl (i, .c6)) (Sum.inl (i, .oxygenAtC6))
    , bond (Sum.inl (i, .c1)) (Sum.inl (i, .glycosidicO))
    , bond (Sum.inl (i, .glycosidicO))
        (Sum.inl (nextResidue i, .c4)) ]).flatten

/-- One O-CH2 bond, one CH2-phenyl bond, and an alternating Kekule cycle for
one site, with an empty list when that site is a free hydroxyl. -/
def benzylBondsAt (state : HydroxylSite → SiteState)
    (site : HydroxylSite) : List (Bond (MoleculeAtom state)) :=
  if h : state site = .benzylEther then
    let s : ProtectedSite state := ⟨site, h⟩
    [ bond (Sum.inl (oxygenAtom s.1)) (Sum.inr (s, .methylene))
    , bond (Sum.inr (s, .methylene)) (Sum.inr (s, .ipso))
    , bond (Sum.inr (s, .ipso)) (Sum.inr (s, .orthoA)) .double
    , bond (Sum.inr (s, .orthoA)) (Sum.inr (s, .metaA))
    , bond (Sum.inr (s, .metaA)) (Sum.inr (s, .para)) .double
    , bond (Sum.inr (s, .para)) (Sum.inr (s, .metaB))
    , bond (Sum.inr (s, .metaB)) (Sum.inr (s, .orthoB)) .double
    , bond (Sum.inr (s, .orthoB)) (Sum.inr (s, .ipso)) ]
  else
    []

def benzylBonds (state : HydroxylSite → SiteState) :
    List (Bond (MoleculeAtom state)) :=
  (List.ofFn fun i : Residue =>
    benzylBondsAt state (secondarySite2 i) ++
    benzylBondsAt state (secondarySite3 i) ++
    benzylBondsAt state (primarySite i)).flatten

def graphForState (state : HydroxylSite → SiteState) :
    MolecularGraph (MoleculeAtom state) where
  atom := moleculeAtomSpec state
  bonds := coreBonds state ++ benzylBonds state

/-! ## Stereochemical template -/

inductive Chair where
  | fourCOne
  deriving DecidableEq, Fintype, Repr

inductive ResidueConfiguration where
  | alphaDGlucopyranoside
  deriving DecidableEq, Fintype, Repr

inductive RingCarbon where
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

inductive Face where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

def Face.opposite : Face → Face
  | .up => .down
  | .down => .up

inductive Disposition where
  | axial
  | equatorial
  deriving DecidableEq, Fintype, Repr

structure StereoCentre where
  center : CoreAtom
  ringBack : CoreAtom
  ringForward : CoreAtom
  externalLigand : CoreAtom
  attachedHydrogenParent : CoreAtom
  externalFace : Face
  hydrogenFace : Face
  externalDisposition : Disposition
  deriving DecidableEq, Repr

def sourceExternalFace : RingCarbon → Face
  | .c1 => .down
  | .c2 => .down
  | .c3 => .up
  | .c4 => .down
  | .c5 => .up

def fourCOneDisposition : RingCarbon → Disposition
  | .c1 => .axial
  | .c2 => .equatorial
  | .c3 => .equatorial
  | .c4 => .equatorial
  | .c5 => .equatorial

def templateStereo (i : Residue) : RingCarbon → StereoCentre
  | .c1 =>
      { center := (i, .c1)
        ringBack := (i, .ringO5)
        ringForward := (i, .c2)
        externalLigand := (i, .glycosidicO)
        attachedHydrogenParent := (i, .c1)
        externalFace := sourceExternalFace .c1
        hydrogenFace := (sourceExternalFace .c1).opposite
        externalDisposition := fourCOneDisposition .c1 }
  | .c2 =>
      { center := (i, .c2)
        ringBack := (i, .c1)
        ringForward := (i, .c3)
        externalLigand := (i, .oxygenAtC2)
        attachedHydrogenParent := (i, .c2)
        externalFace := sourceExternalFace .c2
        hydrogenFace := (sourceExternalFace .c2).opposite
        externalDisposition := fourCOneDisposition .c2 }
  | .c3 =>
      { center := (i, .c3)
        ringBack := (i, .c2)
        ringForward := (i, .c4)
        externalLigand := (i, .oxygenAtC3)
        attachedHydrogenParent := (i, .c3)
        externalFace := sourceExternalFace .c3
        hydrogenFace := (sourceExternalFace .c3).opposite
        externalDisposition := fourCOneDisposition .c3 }
  | .c4 =>
      { center := (i, .c4)
        ringBack := (i, .c3)
        ringForward := (i, .c5)
        externalLigand := (previousResidue i, .glycosidicO)
        attachedHydrogenParent := (i, .c4)
        externalFace := sourceExternalFace .c4
        hydrogenFace := (sourceExternalFace .c4).opposite
        externalDisposition := fourCOneDisposition .c4 }
  | .c5 =>
      { center := (i, .c5)
        ringBack := (i, .c4)
        ringForward := (i, .ringO5)
        externalLigand := (i, .c6)
        attachedHydrogenParent := (i, .c5)
        externalFace := sourceExternalFace .c5
        hydrogenFace := (sourceExternalFace .c5).opposite
        externalDisposition := fourCOneDisposition .c5 }

structure CyclodextrinTemplate where
  hydroxylState : HydroxylSite → SiteState
  chair : Chair
  residueConfiguration : Residue → ResidueConfiguration
  stereocentre : Residue → RingCarbon → StereoCentre

def molecularGraph (m : CyclodextrinTemplate) :
    MolecularGraph (MoleculeAtom m.hydroxylState) :=
  graphForState m.hydroxylState

def StereoCentre.ValidFor
    (state : HydroxylSite → SiteState)
    (g : MolecularGraph (MoleculeAtom state))
    (carbon : RingCarbon) (s : StereoCentre) : Prop :=
  (g.atom (.inl s.center)).element = .carbon ∧
  (g.atom (.inl s.center)).attachedHydrogens = 1 ∧
  s.attachedHydrogenParent = s.center ∧
  g.Bonded (.inl s.center) (.inl s.ringBack) .single ∧
  g.Bonded (.inl s.center) (.inl s.ringForward) .single ∧
  g.Bonded (.inl s.center) (.inl s.externalLigand) .single ∧
  s.externalFace = sourceExternalFace carbon ∧
  s.hydrogenFace = s.externalFace.opposite ∧
  s.externalDisposition = fourCOneDisposition carbon

def unprotectedBetaCD : CyclodextrinTemplate where
  hydroxylState := fun _ => .freeHydroxyl
  chair := .fourCOne
  residueConfiguration := fun _ => .alphaDGlucopyranoside
  stereocentre := templateStereo

/-! ## Exact source arrow and deterministic derivation -/

inductive Reagent where
  | sodiumHydride
  | benzylChloride
  | dibalH
  deriving DecidableEq, Fintype, Repr

structure ReactionConditions where
  firstReagent : Reagent
  firstEquivalents : ℚ
  secondReagent : Reagent
  secondEquivalents : ℚ
  thirdReagent : Reagent
  thirdEquivalents : ℚ
  deriving DecidableEq, Repr

inductive ReactionDirection where
  | forward
  deriving DecidableEq, Fintype, Repr

inductive ReactionRole where
  | betaCyclodextrinSubstrate
  | intermediateLProduct
  deriving DecidableEq, Fintype, Repr

/-- Named roles, direction, and exact student-visible panel for the source
arrow.  These strings are provenance metadata, never the structure result. -/
structure SourceArrowDescriptor where
  reactantRole : ReactionRole
  productRole : ReactionRole
  direction : ReactionDirection
  imagePath : String
  panelLocator : String
  deriving DecidableEq, Repr

def sourceArrowDescriptor : SourceArrowDescriptor where
  reactantRole := .betaCyclodextrinSubstrate
  productRole := .intermediateLProduct
  direction := .forward
  imagePath := "icho_2026_source/image/T9_page-3.png"
  panelLocator := "upper reaction arrow ending at L"

/-- Exact transcription of the two numbered reagent lines above `L`. -/
def sourceReactionConditions : ReactionConditions where
  firstReagent := .sodiumHydride
  firstEquivalents := 30
  secondReagent := .benzylChloride
  secondEquivalents := 30
  thirdReagent := .dibalH
  thirdEquivalents := 2

def SourceConditionsHold : Prop :=
  sourceReactionConditions.firstReagent = .sodiumHydride ∧
  sourceReactionConditions.firstEquivalents = 30 ∧
  sourceReactionConditions.secondReagent = .benzylChloride ∧
  sourceReactionConditions.secondEquivalents = 30 ∧
  sourceReactionConditions.thirdReagent = .dibalH ∧
  sourceReactionConditions.thirdEquivalents = 2

def SourceArrowBound : Prop :=
  sourceArrowDescriptor.reactantRole = .betaCyclodextrinSubstrate ∧
  sourceArrowDescriptor.productRole = .intermediateLProduct ∧
  sourceArrowDescriptor.direction = .forward ∧
  sourceArrowDescriptor.imagePath =
    "icho_2026_source/image/T9_page-3.png" ∧
  sourceArrowDescriptor.panelLocator = "upper reaction arrow ending at L"

inductive TransformationUse where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Fintype, Repr

def sourceTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-- Sodium hydride/benzyl chloride changes the O-H site state; the carbon and
glycosidic skeleton and all stereocentres are retained. -/
def exhaustiveOBenzylation
    (m : CyclodextrinTemplate) : CyclodextrinTemplate where
  hydroxylState := fun _ => .benzylEther
  chair := m.chair
  residueConfiguration := m.residueConfiguration
  stereocentre := m.stereocentre

/-- A DIBAL-H primary debenzylation changes exactly the selected C6 oxygen
from O-Bn to O-H and leaves the sugar skeleton untouched. -/
def primaryDebenzylation
    (m : CyclodextrinTemplate) (i : Residue) : CyclodextrinTemplate where
  hydroxylState := fun site =>
    if site = primarySite i then .freeHydroxyl else m.hydroxylState site
  chair := m.chair
  residueConfiguration := m.residueConfiguration
  stereocentre := m.stereocentre

def residueAtOffset (i : Residue) (offset : ℕ) : Residue :=
  ⟨(i.val + offset) % 7, Nat.mod_lt _ (by omega)⟩

/-- The first symmetry-equivalent free primary site is called unit 1, as in
the numbered source template. -/
def unitOne : Residue := ⟨0, by omega⟩

def unitThree : Residue := residueAtOffset unitOne 2

def unitFour : Residue := residueAtOffset unitOne 3

def primaryBenzylAvailable
    (m : CyclodextrinTemplate) (i : Residue) : Prop :=
  m.hydroxylState (primarySite i) = .benzylEther

/-- Source-stated Sinay rule: a protic primary group at `director` selects
the 1,4-related primary site, with the 1,3-related site as the printed
fallback only when the former is unavailable. -/
def SinayDirectingRule
    (m : CyclodextrinTemplate) (director target : Residue) : Prop :=
  m.hydroxylState (primarySite director) = .freeHydroxyl ∧
  (primaryBenzylAvailable m (residueAtOffset director 3) →
    target = residueAtOffset director 3) ∧
  (¬ primaryBenzylAvailable m (residueAtOffset director 3) →
    target = residueAtOffset director 2)

def directedTarget (m : CyclodextrinTemplate)
    (director : Residue) : Residue :=
  if m.hydroxylState (primarySite (residueAtOffset director 3)) =
      .benzylEther then
    residueAtOffset director 3
  else
    residueAtOffset director 2

def fullyBenzylated : CyclodextrinTemplate :=
  exhaustiveOBenzylation unprotectedBetaCD

def afterFirstDebenzylation : CyclodextrinTemplate :=
  primaryDebenzylation fullyBenzylated unitOne

def secondDirectedResidue : Residue :=
  directedTarget afterFirstDebenzylation unitOne

/-- The candidate is constructed after applying the source arrow and the
source-stated directing rule; its site pattern is not supplied as a premise. -/
def derivedL : CyclodextrinTemplate :=
  primaryDebenzylation afterFirstDebenzylation secondDirectedResidue

/-- Exact, equation-bearing compatibility contract for the depicted arrow.
Unprinted protocol details and material streams remain unspecified. -/
def SourceReactionCompatible (m : CyclodextrinTemplate) : Prop :=
  sourceTransformationUse = .qualitativeNamedTransformOnly ∧
  SourceArrowBound ∧
  SourceConditionsHold ∧
  fullyBenzylated = exhaustiveOBenzylation unprotectedBetaCD ∧
  afterFirstDebenzylation =
    primaryDebenzylation fullyBenzylated unitOne ∧
  SinayDirectingRule afterFirstDebenzylation unitOne secondDirectedResidue ∧
  m = primaryDebenzylation afterFirstDebenzylation secondDirectedResidue

theorem sourceConditions_hold : SourceConditionsHold := by
  unfold SourceConditionsHold
  decide +kernel

theorem sourceArrow_bound : SourceArrowBound := by
  unfold SourceArrowBound
  decide +kernel

theorem source_directing_rule_selects_unitFour :
    SinayDirectingRule afterFirstDebenzylation unitOne secondDirectedResidue ∧
    secondDirectedResidue = unitFour := by
  unfold SinayDirectingRule primaryBenzylAvailable
  decide +kernel

theorem derivedL_sourceReactionCompatible :
    SourceReactionCompatible derivedL := by
  unfold SourceReactionCompatible
  exact ⟨rfl, sourceArrow_bound, sourceConditions_hold, rfl, rfl,
    source_directing_rule_selects_unitFour.1, rfl⟩

/-! ## Complete template, atom, formula, and result specifications -/

def freeHydroxylSites (m : CyclodextrinTemplate) : Finset HydroxylSite :=
  Finset.univ.filter fun s => m.hydroxylState s = .freeHydroxyl

def benzylEtherSites (m : CyclodextrinTemplate) : Finset HydroxylSite :=
  Finset.univ.filter fun s => m.hydroxylState s = .benzylEther

/-- All fourteen secondary boxes are `OBn`; among the seven primary boxes,
units 1 and 4 are `CH2OH` and the other five are `CH2OBn`. -/
def CompleteTemplateFields (m : CyclodextrinTemplate) : Prop :=
  (∀ i,
    m.hydroxylState (secondarySite2 i) = .benzylEther ∧
    m.hydroxylState (secondarySite3 i) = .benzylEther) ∧
  (∀ i,
    m.hydroxylState (primarySite i) =
      if i = unitOne ∨ i = unitFour then .freeHydroxyl else .benzylEther) ∧
  (freeHydroxylSites m).card = 2 ∧
  (benzylEtherSites m).card = 19

def lFormula : MolecularFormula :=
  { carbon := 175, hydrogen := 184, oxygen := 35 }

def betaCDFormula : MolecularFormula :=
  { carbon := 42, hydrogen := 70, oxygen := 35 }

/-- Component ledger for O-benzylation.  Every O-H -> O-CH2-C6H5
replacement contributes seven carbons and seven benzyl hydrogens while
removing the hydroxyl hydrogen; the oxygen inventory is unchanged. -/
def FormulaAssemblyLedger (m : CyclodextrinTemplate) : Prop :=
  let n := (benzylEtherSites m).card
  let f := (molecularGraph m).formula
  f.carbon = betaCDFormula.carbon + 7 * n ∧
  f.hydrogen + n = betaCDFormula.hydrogen + 7 * n ∧
  f.oxygen = betaCDFormula.oxygen

/-- Full requested structure: source-arrow derivation, every template field,
the retained alpha-D-gluco stereochemistry, and the closed-shell atom graph. -/
def CompleteLSpecification (m : CyclodextrinTemplate) : Prop :=
  SourceReactionCompatible m ∧
  CompleteTemplateFields m ∧
  m.chair = .fourCOne ∧
  (∀ i, m.residueConfiguration i = .alphaDGlucopyranoside) ∧
  (∀ i carbon,
    m.stereocentre i carbon = templateStereo i carbon ∧
    (m.stereocentre i carbon).ValidFor
      m.hydroxylState (molecularGraph m) carbon) ∧
  FormulaAssemblyLedger m ∧
  (molecularGraph m).formula = lFormula ∧
  (molecularGraph m).WellFormedClosed

theorem derivedL_templateFields : CompleteTemplateFields derivedL := by
  unfold CompleteTemplateFields
  decide +kernel

theorem derivedL_formulaAudit :
    FormulaAssemblyLedger derivedL ∧
    (molecularGraph derivedL).formula = lFormula := by
  unfold FormulaAssemblyLedger
  decide +kernel

private abbrev LAtom := MoleculeAtom derivedL.hydroxylState

private abbrev lGraph : MolecularGraph LAtom := molecularGraph derivedL

private instance lAtomDecidableEq : DecidableEq LAtom := by
  unfold LAtom MoleculeAtom ProtectedSite
  infer_instance

/-- A spanning set of bonds in one glucose residue, together with its outgoing
glycosidic bond.  These bonds are read directly from `coreBonds`. -/
private theorem l_core_spanning_bonds :
    ∀ i : Residue,
      lGraph.Bonded (.inl (i, .c2)) (.inl (i, .c1)) .single ∧
      lGraph.Bonded (.inl (i, .c3)) (.inl (i, .c2)) .single ∧
      lGraph.Bonded (.inl (i, .c4)) (.inl (i, .c3)) .single ∧
      lGraph.Bonded (.inl (i, .c5)) (.inl (i, .c4)) .single ∧
      lGraph.Bonded (.inl (i, .ringO5)) (.inl (i, .c1)) .single ∧
      lGraph.Bonded (.inl (i, .c5)) (.inl (i, .ringO5)) .single ∧
      lGraph.Bonded (.inl (i, .c6)) (.inl (i, .c5)) .single ∧
      lGraph.Bonded (.inl (i, .oxygenAtC2)) (.inl (i, .c2)) .single ∧
      lGraph.Bonded (.inl (i, .oxygenAtC3)) (.inl (i, .c3)) .single ∧
      lGraph.Bonded (.inl (i, .oxygenAtC6)) (.inl (i, .c6)) .single ∧
      lGraph.Bonded (.inl (i, .glycosidicO)) (.inl (i, .c1)) .single ∧
      lGraph.Bonded (.inl (i, .glycosidicO))
        (.inl (nextResidue i, .c4)) .single := by
  intro i
  fin_cases i <;> decide +kernel

private theorem l_core_reachable_local (i : Residue) (x : CoreLocalAtom) :
    lGraph.Reachable (.inl (i, x)) (.inl (i, .c1)) := by
  rcases l_core_spanning_bonds i with
    ⟨h21, h32, h43, h54, hO51, _, h65, hO2, hO3, hO6, hG1, _⟩
  have r1 : lGraph.Reachable (.inl (i, .c1)) (.inl (i, .c1)) := .refl _
  have r2 := reachable_of_bonded h21
  have r3 := reachable_trans (reachable_of_bonded h32) r2
  have r4 := reachable_trans (reachable_of_bonded h43) r3
  have r5 := reachable_trans (reachable_of_bonded h54) r4
  have r6 := reachable_trans (reachable_of_bonded h65) r5
  have rO5 := reachable_of_bonded hO51
  have rG := reachable_of_bonded hG1
  have rO2 := reachable_trans (reachable_of_bonded hO2) r2
  have rO3 := reachable_trans (reachable_of_bonded hO3) r3
  have rO6 := reachable_trans (reachable_of_bonded hO6) r6
  cases x <;> assumption

private theorem l_core_reachable_next (i : Residue) :
    lGraph.Reachable (.inl (i, .c1))
      (.inl (nextResidue i, .c1)) := by
  rcases l_core_spanning_bonds i with
    ⟨_, _, _, _, _, _, _, _, _, _, hG1, hGnext⟩
  exact reachable_trans
    (reachable_of_bonded (bonded_symm hG1))
    (reachable_trans (reachable_of_bonded hGnext)
      (l_core_reachable_local (nextResidue i) .c4))

private theorem l_zero_reaches_core_root (i : Residue) :
    lGraph.Reachable (.inl ((0 : Residue), .c1)) (.inl (i, .c1)) := by
  have h01 : lGraph.Reachable (.inl ((0 : Residue), .c1))
      (.inl ((1 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (0 : Residue)
  have h12 : lGraph.Reachable (.inl ((1 : Residue), .c1))
      (.inl ((2 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (1 : Residue)
  have h23 : lGraph.Reachable (.inl ((2 : Residue), .c1))
      (.inl ((3 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (2 : Residue)
  have h34 : lGraph.Reachable (.inl ((3 : Residue), .c1))
      (.inl ((4 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (3 : Residue)
  have h45 : lGraph.Reachable (.inl ((4 : Residue), .c1))
      (.inl ((5 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (4 : Residue)
  have h56 : lGraph.Reachable (.inl ((5 : Residue), .c1))
      (.inl ((6 : Residue), .c1)) := by
    simpa [nextResidue] using l_core_reachable_next (5 : Residue)
  have h02 := reachable_trans h01 h12
  have h03 := reachable_trans h02 h23
  have h04 := reachable_trans h03 h34
  have h05 := reachable_trans h04 h45
  have h06 := reachable_trans h05 h56
  fin_cases i
  · exact .refl _
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · exact h06

private theorem l_core_roots_connected (i j : Residue) :
    lGraph.Reachable (.inl (i, .c1)) (.inl (j, .c1)) :=
  reachable_trans (reachable_symm (l_zero_reaches_core_root i))
    (l_zero_reaches_core_root j)

/-- Every benzyl substituent is attached to its site oxygen and its seven
carbon atoms form a connected methylene/phenyl branch. -/
private theorem l_benzyl_spanning_bonds :
    ∀ s : ProtectedSite derivedL.hydroxylState,
      lGraph.Bonded (.inr (s, .methylene)) (.inl (oxygenAtom s.1)) .single ∧
      lGraph.Bonded (.inr (s, .ipso)) (.inr (s, .methylene)) .single ∧
      lGraph.Bonded (.inr (s, .orthoA)) (.inr (s, .ipso)) .double ∧
      lGraph.Bonded (.inr (s, .metaA)) (.inr (s, .orthoA)) .single ∧
      lGraph.Bonded (.inr (s, .para)) (.inr (s, .metaA)) .double ∧
      lGraph.Bonded (.inr (s, .metaB)) (.inr (s, .para)) .single ∧
      lGraph.Bonded (.inr (s, .orthoB)) (.inr (s, .metaB)) .double := by
  decide +kernel

private theorem l_benzyl_reachable_core
    (s : ProtectedSite derivedL.hydroxylState) (x : BenzylAtom) :
    lGraph.Reachable (.inr (s, x)) (.inl (oxygenAtom s.1)) := by
  rcases l_benzyl_spanning_bonds s with
    ⟨hM, hI, hOA, hMA, hP, hMB, hOB⟩
  have rM := reachable_of_bonded hM
  have rI := reachable_trans (reachable_of_bonded hI) rM
  have rOA := reachable_trans (reachable_of_bonded hOA) rI
  have rMA := reachable_trans (reachable_of_bonded hMA) rOA
  have rP := reachable_trans (reachable_of_bonded hP) rMA
  have rMB := reachable_trans (reachable_of_bonded hMB) rP
  have rOB := reachable_trans (reachable_of_bonded hOB) rMB
  cases x <;> assumption

private theorem l_atom_reaches_residue_root (a : LAtom) :
    ∃ i : Residue, lGraph.Reachable a (.inl (i, .c1)) := by
  rcases a with a | ⟨s, x⟩
  · rcases a with ⟨i, localAtom⟩
    exact ⟨i, l_core_reachable_local i localAtom⟩
  · rcases s with ⟨⟨i, position⟩, hs⟩
    refine ⟨i, reachable_trans
      (l_benzyl_reachable_core ⟨⟨i, position⟩, hs⟩ x) ?_⟩
    cases position
    · exact l_core_reachable_local i .oxygenAtC2
    · exact l_core_reachable_local i .oxygenAtC3
    · exact l_core_reachable_local i .oxygenAtC6

private theorem l_connected : lGraph.Connected := by
  intro a b
  rcases l_atom_reaches_residue_root a with ⟨i, ha⟩
  rcases l_atom_reaches_residue_root b with ⟨j, hb⟩
  exact reachable_trans ha
    (reachable_trans (l_core_roots_connected i j) (reachable_symm hb))

theorem derivedL_graphAudit :
    (molecularGraph derivedL).WellFormedClosed := by
  refine ⟨?_, ?_, ?_, l_connected⟩
  · unfold MolecularGraph.NoSelfBonds
    decide +kernel
  · unfold MolecularGraph.NoDuplicateBonds Bond.Connects
    decide +kernel
  · unfold MolecularGraph.NeutralClosedValence
    decide +kernel

private theorem l_previous_glycosidic_bond (i : Residue) :
    lGraph.Bonded (.inl (i, .c4))
      (.inl (previousResidue i, .glycosidicO)) .single := by
  rcases l_core_spanning_bonds (previousResidue i) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hprev⟩
  have hprev' := bonded_symm hprev
  fin_cases i <;> simpa [nextResidue, previousResidue] using hprev'

private theorem l_stereo_valid (i : Residue) (carbon : RingCarbon) :
    (templateStereo i carbon).ValidFor
      derivedL.hydroxylState (molecularGraph derivedL) carbon := by
  rcases l_core_spanning_bonds i with
    ⟨h21, h32, h43, h54, hO51, h5O, h65, hO2, hO3, _, hG1, _⟩
  cases carbon
  · exact ⟨rfl, rfl, rfl, bonded_symm hO51, bonded_symm h21,
      bonded_symm hG1, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, h21, bonded_symm h32,
      bonded_symm hO2, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, h32, bonded_symm h43,
      bonded_symm hO3, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, h43, bonded_symm h54,
      l_previous_glycosidic_bond i, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, h54, h5O,
      bonded_symm h65, rfl, rfl, rfl⟩

theorem derivedL_complete : CompleteLSpecification derivedL := by
  refine ⟨derivedL_sourceReactionCompatible, derivedL_templateFields, rfl,
    fun _ => rfl, ?_, derivedL_formulaAudit.1, derivedL_formulaAudit.2,
    derivedL_graphAudit⟩
  intro i carbon
  exact ⟨rfl, l_stereo_valid i carbon⟩

/-- Requested output `structure_l`. -/
def StructureLResult : Prop :=
  CompleteLSpecification derivedL

theorem structure_l : StructureLResult := by
  exact derivedL_complete

/-- Exact-symbolic raw result carrier. -/
def RawResult : Prop := StructureLResult

/-- Exact-symbolic reporting does not alter or round a molecular structure. -/
def ReportedResult : Prop := StructureLResult

theorem raw_result : RawResult := by
  exact structure_l

theorem reported_result : ReportedResult := by
  exact structure_l

end IChO2026Problems.T9A5
