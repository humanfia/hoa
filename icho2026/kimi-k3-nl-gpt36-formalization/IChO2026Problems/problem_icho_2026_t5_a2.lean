import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T5.2: cardiolipin structures

The problem permits the symbol `R` for each (identical) hydrocarbon part of a
fatty-acid residue.  Accordingly, `fattyAcidResidueR` below is a typed
pseudo-node with one displayed attachment; atoms hidden inside `R` are not
expanded.  Every atom outside `R`, every covalent bond order, every formal
charge, and every requested stereocentre is represented explicitly.  Ordinary
line-formula hydrogens are recorded by `attachedHydrogens`.

## Assumption/target split

The source-side assumptions are represented by `SourceFragmentAssembly`: the
four fragment multiplicities and port counts read from page 1, complete use of
the ports, and the fact that the assembled phospholipid is connected and
acyclic.  These data imply the previous-part fact that the number of type-`a`
hydrogen caps is one (and hence odd); no previous answer is imported.

The output side consists of the two concrete carriers `structurePL1` and
`structureY`.  Their specifications do not assert equality to an assumed
answer.  They check the displayed atom/bond graph against valence, charge,
radical, peroxide, fragment-contraction, stereochemical, deprotonation, and
hydrogen-bond-relay constraints.
-/

namespace IChO2026Problems
namespace T5A2

/-! ## A small, explicit molecular-structure vocabulary -/

/-- Elements that occur explicitly outside the abbreviated hydrocarbon groups. -/
inductive ChemicalElement
  | hydrogen
  | carbon
  | oxygen
  | phosphorus
  deriving DecidableEq, Repr

/-- Data shown for an ordinary atom in the structural formula. -/
structure AtomData where
  element : ChemicalElement
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  deriving DecidableEq, Repr

/-- A displayed node is either an atom or the problem-authorized abbreviation
`R` for a neutral, radical-free hydrocarbon substituent with one attachment. -/
inductive MolecularNode
  | atom (data : AtomData)
  | fattyAcidResidueR
  deriving DecidableEq, Repr

/-- The covalent bond orders needed by the two requested structures. -/
inductive BondOrder
  | single
  | double
  deriving DecidableEq, Repr

def BondOrder.valenceContribution : BondOrder → ℕ
  | .single => 1
  | .double => 2

/-- One displayed covalent bond. -/
structure CovalentBond (Site : Type) where
  left : Site
  right : Site
  order : BondOrder
  deriving DecidableEq, Repr

/-- A directional `donor-H···acceptor` interaction.  The natural number picks
one of the hydrogens attached to the donor atom. -/
structure HydrogenBond (Site : Type) where
  donor : Site
  donorHydrogenIndex : ℕ
  acceptor : Site
  deriving DecidableEq, Repr

/-- Absolute configuration at a carbon stereocentre. -/
inductive Configuration
  | R
  | S
  deriving DecidableEq, Repr

def Configuration.opposite : Configuration → Configuration
  | .R => .S
  | .S => .R

/-- A finite displayed molecular structure. -/
structure MolecularStructure (Site : Type) where
  node : Site → MolecularNode
  covalentBonds : List (CovalentBond Site)
  configuration : Site → Option Configuration
  hydrogenBonds : List (HydrogenBond Site)

def displayedAtom
    (element : ChemicalElement) (attachedHydrogens : ℕ := 0)
    (formalCharge : ℤ := 0) (radicalElectrons : ℕ := 0) : MolecularNode :=
  .atom { element, formalCharge, radicalElectrons, attachedHydrogens }

def MolecularNode.element? : MolecularNode → Option ChemicalElement
  | .atom data => some data.element
  | .fattyAcidResidueR => none

def MolecularNode.formalCharge : MolecularNode → ℤ
  | .atom data => data.formalCharge
  | .fattyAcidResidueR => 0

def MolecularNode.radicalElectrons : MolecularNode → ℕ
  | .atom data => data.radicalElectrons
  | .fattyAcidResidueR => 0

/-- Hydrogens displayed implicitly on an explicit atom.  This deliberately
does not count hydrogens hidden inside an `R` abbreviation. -/
def MolecularNode.displayedAttachedHydrogens : MolecularNode → ℕ
  | .atom data => data.attachedHydrogens
  | .fattyAcidResidueR => 0

/-- The valence demanded by the displayed atom state.  In particular, a
singly charged phosphate oxygen has covalent valence one. -/
def MolecularNode.expectedDisplayedValence : MolecularNode → ℕ
  | .fattyAcidResidueR => 1
  | .atom data =>
      match data.element with
      | .hydrogen => 1
      | .carbon => 4
      | .oxygen => if data.formalCharge = -1 then 1 else 2
      | .phosphorus => 5

def CovalentBond.incidentContribution {Site : Type} [DecidableEq Site]
    (bond : CovalentBond Site) (site : Site) : ℕ :=
  if bond.left = site then bond.order.valenceContribution
  else if bond.right = site then bond.order.valenceContribution
  else 0

def MolecularStructure.covalentValence {Site : Type} [DecidableEq Site]
    (molecule : MolecularStructure Site) (site : Site) : ℕ :=
  (molecule.covalentBonds.map fun bond => bond.incidentContribution site).sum

def HasCovalentBond {Site : Type} (molecule : MolecularStructure Site)
    (first second : Site) (order : BondOrder) : Prop :=
  ∃ bond ∈ molecule.covalentBonds,
    bond.order = order ∧
      ((bond.left = first ∧ bond.right = second) ∨
       (bond.left = second ∧ bond.right = first))

def HasHydrogenBond {Site : Type} (molecule : MolecularStructure Site)
    (donor : Site) (hydrogenIndex : ℕ) (acceptor : Site) : Prop :=
  ∃ bond ∈ molecule.hydrogenBonds,
    bond.donor = donor ∧ bond.donorHydrogenIndex = hydrogenIndex ∧
      bond.acceptor = acceptor

def CovalentlyAdjacent {Site : Type} (molecule : MolecularStructure Site)
    (first second : Site) : Prop :=
  first ≠ second ∧ ∃ order, HasCovalentBond molecule first second order

theorem covalentlyAdjacent_symm {Site : Type}
    (molecule : MolecularStructure Site) :
    Std.Symm (CovalentlyAdjacent molecule) := by
  constructor
  intro first second adjacency
  rcases adjacency with ⟨different, order, bond, member, bondOrder, endpoints⟩
  refine ⟨different.symm, order, bond, member, bondOrder, ?_⟩
  rcases endpoints with endpoints | endpoints
  · exact Or.inr endpoints
  · exact Or.inl endpoints

/-- The Mathlib simple graph underlying the displayed covalent structure. -/
def MolecularStructure.covalentGraph {Site : Type}
    (molecule : MolecularStructure Site) : SimpleGraph Site where
  Adj := CovalentlyAdjacent molecule
  symm := covalentlyAdjacent_symm molecule
  loopless := by
    constructor
    intro site adjacency
    exact adjacency.1 rfl

def SameUnorderedEndpoints {Site : Type}
    (first second : CovalentBond Site) : Prop :=
  (first.left = second.left ∧ first.right = second.right) ∨
  (first.left = second.right ∧ first.right = second.left)

def NoSelfBonds {Site : Type} (molecule : MolecularStructure Site) : Prop :=
  ∀ bond ∈ molecule.covalentBonds, bond.left ≠ bond.right

def UniqueCovalentPairs {Site : Type}
    (molecule : MolecularStructure Site) : Prop :=
  ∀ first ∈ molecule.covalentBonds, ∀ second ∈ molecule.covalentBonds,
    SameUnorderedEndpoints first second → first = second

def ValencesSatisfied {Site : Type} [DecidableEq Site]
    (molecule : MolecularStructure Site) : Prop :=
  ∀ site,
    molecule.covalentValence site +
        (molecule.node site).displayedAttachedHydrogens =
      (molecule.node site).expectedDisplayedValence

def AllDisplayedNodesRadicalFree {Site : Type}
    (molecule : MolecularStructure Site) : Prop :=
  ∀ site, (molecule.node site).radicalElectrons = 0

def NoPeroxideBond {Site : Type} (molecule : MolecularStructure Site) : Prop :=
  ∀ bond ∈ molecule.covalentBonds,
    ¬ ((molecule.node bond.left).element? = some .oxygen ∧
       (molecule.node bond.right).element? = some .oxygen)

def HydrogenBondWellFormed {Site : Type}
    (molecule : MolecularStructure Site) (bond : HydrogenBond Site) : Prop :=
  (molecule.node bond.donor).element? = some .oxygen ∧
  (molecule.node bond.acceptor).element? = some .oxygen ∧
  bond.donor ≠ bond.acceptor ∧
  bond.donorHydrogenIndex <
    (molecule.node bond.donor).displayedAttachedHydrogens

def AllHydrogenBondsWellFormed {Site : Type}
    (molecule : MolecularStructure Site) : Prop :=
  ∀ bond ∈ molecule.hydrogenBonds, HydrogenBondWellFormed molecule bond

def ValidMolecularStructure {Site : Type} [DecidableEq Site]
    (molecule : MolecularStructure Site) : Prop :=
  NoSelfBonds molecule ∧
  UniqueCovalentPairs molecule ∧
  ValencesSatisfied molecule ∧
  AllDisplayedNodesRadicalFree molecule ∧
  AllHydrogenBondsWellFormed molecule

def TotalFormalCharge {Site : Type} [Fintype Site]
    (molecule : MolecularStructure Site) : ℤ :=
  ∑ site, (molecule.node site).formalCharge

def TotalDisplayedAttachedHydrogens {Site : Type} [Fintype Site]
    (molecule : MolecularStructure Site) : ℕ :=
  ∑ site, (molecule.node site).displayedAttachedHydrogens

inductive SkeletonNodeKind
  | atom (element : ChemicalElement)
  | fattyAcidResidueR
  deriving DecidableEq, Repr

def MolecularNode.skeletonKind : MolecularNode → SkeletonNodeKind
  | .atom data => .atom data.element
  | .fattyAcidResidueR => .fattyAcidResidueR

def CountSkeletonNodes {Site : Type} [Fintype Site] [DecidableEq Site]
    (molecule : MolecularStructure Site) (kind : SkeletonNodeKind) : ℕ :=
  (Finset.univ.filter fun site => (molecule.node site).skeletonKind = kind).card

def ConnectedAcyclic {Site : Type} (molecule : MolecularStructure Site) : Prop :=
  molecule.covalentGraph.IsTree

/-! ## Source fragment inventory and the inline derivation of T5.1 -/

inductive FragmentKind
  | hydrogenCap
  | phosphate
  | glycerol
  | fattyAcyl
  deriving DecidableEq, Repr

def FragmentKind.portCount : FragmentKind → ℕ
  | .hydrogenCap => 1
  | .phosphate => 2
  | .glycerol => 3
  | .fattyAcyl => 1

structure FragmentAssembly (Fragment : Type) where
  kind : Fragment → FragmentKind
  attachmentGraph : SimpleGraph Fragment

def FragmentAssembly.kindCount {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (kind : FragmentKind) : ℕ :=
  (Finset.univ.filter fun fragment => assembly.kind fragment = kind).card

noncomputable def FragmentAssembly.degree {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (fragment : Fragment) : ℕ := by
  classical
  exact (Finset.univ.filter fun other =>
    assembly.attachmentGraph.Adj fragment other).card

/-- Exact multiplicities read from the four boxes `a`--`d` on source page 1. -/
def MatchesSourceFragmentInventory {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (hydrogenCapCount : ℕ) : Prop :=
  assembly.kindCount .hydrogenCap = hydrogenCapCount ∧
  assembly.kindCount .phosphate = 2 ∧
  assembly.kindCount .glycerol = 3 ∧
  assembly.kindCount .fattyAcyl = 4

/-- Every wavy-line port shown in the source figure is used once. -/
def UsesEveryFragmentPort {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) : Prop :=
  ∀ fragment, assembly.degree fragment = (assembly.kind fragment).portCount

/-- The complete source-side fragment assumptions.  `IsTree` is Mathlib's
connected-and-acyclic condition; it is not an answer-shaped topology. -/
def SourceFragmentAssembly {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (hydrogenCapCount : ℕ) : Prop :=
  MatchesSourceFragmentInventory assembly hydrogenCapCount ∧
  UsesEveryFragmentPort assembly ∧
  assembly.attachmentGraph.IsTree

/-- The source fragment degrees and tree identity force `n = 1`. -/
theorem hydrogenCapCount_eq_one {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (hydrogenCapCount : ℕ)
    (source : SourceFragmentAssembly assembly hydrogenCapCount) :
    hydrogenCapCount = 1 := by
  classical
  rcases source with ⟨⟨hydrogenCaps, phosphates, glycerols, fattyAcyls⟩,
    allPortsUsed, tree⟩
  let kinds : Finset FragmentKind :=
    { .hydrogenCap, .phosphate, .glycerol, .fattyAcyl }
  have mapsToKinds : ∀ fragment ∈ (Finset.univ : Finset Fragment),
      assembly.kind fragment ∈ kinds := by
    intro fragment _
    cases assembly.kind fragment <;> simp [kinds]
  have cardByKind :
      Fintype.card Fragment =
        assembly.kindCount .hydrogenCap +
        assembly.kindCount .phosphate +
        assembly.kindCount .glycerol +
        assembly.kindCount .fattyAcyl := by
    have fibers := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset Fragment)) (t := kinds)
      (f := assembly.kind) mapsToKinds
    simpa [kinds, FragmentAssembly.kindCount, add_assoc] using fibers
  have portFiber (fragmentKind : FragmentKind) :
      (∑ fragment ∈ (Finset.univ : Finset Fragment) with
          assembly.kind fragment = fragmentKind,
          (assembly.kind fragment).portCount) =
        assembly.kindCount fragmentKind * fragmentKind.portCount := by
    rw [FragmentAssembly.kindCount]
    apply Finset.sum_const_nat
    intro fragment member
    rw [(Finset.mem_filter.mp member).2]
  have portsByKind :
      (∑ fragment : Fragment, (assembly.kind fragment).portCount) =
        assembly.kindCount .hydrogenCap +
        2 * assembly.kindCount .phosphate +
        3 * assembly.kindCount .glycerol +
        assembly.kindCount .fattyAcyl := by
    have fibers := (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset Fragment)) (t := kinds)
      (g := assembly.kind) mapsToKinds
      (fun fragment => (assembly.kind fragment).portCount)).symm
    simp [kinds] at fibers
    rw [portFiber, portFiber, portFiber, portFiber] at fibers
    simpa [kinds, FragmentKind.portCount, add_assoc, mul_comm] using fibers
  have degree_eq (fragment : Fragment) :
      assembly.degree fragment = assembly.attachmentGraph.degree fragment := by
    unfold FragmentAssembly.degree SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_eq_filter]
  have degreeSum :
      (∑ fragment : Fragment, assembly.degree fragment) =
        2 * assembly.attachmentGraph.edgeFinset.card := by
    simpa only [degree_eq] using
      assembly.attachmentGraph.sum_degrees_eq_twice_card_edges
  have degreeSumFromPorts :
      (∑ fragment : Fragment, assembly.degree fragment) =
        ∑ fragment : Fragment, (assembly.kind fragment).portCount := by
    exact Finset.sum_congr rfl fun fragment _ => allPortsUsed fragment
  have treeCard := tree.card_edgeFinset
  omega

/-- In particular, this rederives the reusable conclusion requested in T5.1. -/
theorem hydrogenCapCount_isOdd {Fragment : Type}
    [Fintype Fragment] [DecidableEq Fragment]
    (assembly : FragmentAssembly Fragment) (hydrogenCapCount : ℕ)
    (source : SourceFragmentAssembly assembly hydrogenCapCount) :
    Odd hydrogenCapCount := by
  rw [hydrogenCapCount_eq_one assembly hydrogenCapCount source]
  norm_num

/-! ## Fully labelled PL1 skeleton -/

/-- Sites of the displayed PL1 skeleton.  The four `...Residue` sites are the
four occurrences of the allowed abbreviation `R`. -/
inductive PL1Site
  | lOuterResidue
  | lOuterCarbonylC
  | lOuterCarbonylO
  | lOuterEsterO
  | lOuterGlycerolC
  | lStereoC
  | lInnerEsterO
  | lInnerCarbonylC
  | lInnerCarbonylO
  | lInnerResidue
  | lPhosphateGlycerolC
  | lGlycerolPhosphateO
  | lPhosphorus
  | lPhosphorylO
  | lAcidO
  | lCentralBridgeO
  | centralLeftC
  | centralC
  | centralHydroxylO
  | centralRightC
  | rCentralBridgeO
  | rPhosphorus
  | rPhosphorylO
  | rAcidO
  | rGlycerolPhosphateO
  | rPhosphateGlycerolC
  | rStereoC
  | rInnerEsterO
  | rInnerCarbonylC
  | rInnerCarbonylO
  | rInnerResidue
  | rOuterGlycerolC
  | rOuterEsterO
  | rOuterCarbonylC
  | rOuterCarbonylO
  | rOuterResidue
  deriving DecidableEq, Fintype, Repr

def pl1NeutralNode : PL1Site → MolecularNode
  | .lOuterResidue | .lInnerResidue | .rInnerResidue | .rOuterResidue =>
      .fattyAcidResidueR
  | .lOuterCarbonylC | .lInnerCarbonylC |
    .rInnerCarbonylC | .rOuterCarbonylC =>
      displayedAtom .carbon
  | .lOuterGlycerolC | .lPhosphateGlycerolC |
    .centralLeftC | .centralRightC |
    .rPhosphateGlycerolC | .rOuterGlycerolC =>
      displayedAtom .carbon 2
  | .lStereoC | .centralC | .rStereoC =>
      displayedAtom .carbon 1
  | .lAcidO | .centralHydroxylO | .rAcidO =>
      displayedAtom .oxygen 1
  | .lOuterCarbonylO | .lOuterEsterO | .lInnerEsterO |
    .lInnerCarbonylO | .lGlycerolPhosphateO | .lPhosphorylO |
    .lCentralBridgeO | .rCentralBridgeO | .rPhosphorylO |
    .rGlycerolPhosphateO | .rInnerEsterO | .rInnerCarbonylO |
    .rOuterEsterO | .rOuterCarbonylO =>
      displayedAtom .oxygen
  | .lPhosphorus | .rPhosphorus =>
      displayedAtom .phosphorus

def singleBond (left right : PL1Site) : CovalentBond PL1Site :=
  { left, right, order := .single }

def doubleBond (left right : PL1Site) : CovalentBond PL1Site :=
  { left, right, order := .double }

/-- The complete covalent edge list for
`RCOO-CH₂-CH(OCOR)-CH₂-O-P-...-P-O-CH₂-CH(OCOR)-CH₂-OCOR`. -/
def pl1CovalentBonds : List (CovalentBond PL1Site) :=
  [ singleBond .lOuterResidue .lOuterCarbonylC,
    doubleBond .lOuterCarbonylC .lOuterCarbonylO,
    singleBond .lOuterCarbonylC .lOuterEsterO,
    singleBond .lOuterEsterO .lOuterGlycerolC,
    singleBond .lOuterGlycerolC .lStereoC,
    singleBond .lStereoC .lInnerEsterO,
    singleBond .lInnerEsterO .lInnerCarbonylC,
    doubleBond .lInnerCarbonylC .lInnerCarbonylO,
    singleBond .lInnerCarbonylC .lInnerResidue,
    singleBond .lStereoC .lPhosphateGlycerolC,
    singleBond .lPhosphateGlycerolC .lGlycerolPhosphateO,
    singleBond .lGlycerolPhosphateO .lPhosphorus,
    doubleBond .lPhosphorus .lPhosphorylO,
    singleBond .lPhosphorus .lAcidO,
    singleBond .lPhosphorus .lCentralBridgeO,
    singleBond .lCentralBridgeO .centralLeftC,
    singleBond .centralLeftC .centralC,
    singleBond .centralC .centralHydroxylO,
    singleBond .centralC .centralRightC,
    singleBond .centralRightC .rCentralBridgeO,
    singleBond .rCentralBridgeO .rPhosphorus,
    doubleBond .rPhosphorus .rPhosphorylO,
    singleBond .rPhosphorus .rAcidO,
    singleBond .rPhosphorus .rGlycerolPhosphateO,
    singleBond .rGlycerolPhosphateO .rPhosphateGlycerolC,
    singleBond .rPhosphateGlycerolC .rStereoC,
    singleBond .rStereoC .rInnerEsterO,
    singleBond .rInnerEsterO .rInnerCarbonylC,
    doubleBond .rInnerCarbonylC .rInnerCarbonylO,
    singleBond .rInnerCarbonylC .rInnerResidue,
    singleBond .rStereoC .rOuterGlycerolC,
    singleBond .rOuterGlycerolC .rOuterEsterO,
    singleBond .rOuterEsterO .rOuterCarbonylC,
    doubleBond .rOuterCarbonylC .rOuterCarbonylO,
    singleBond .rOuterCarbonylC .rOuterResidue ]

def pl1Configuration (left right : Configuration) :
    PL1Site → Option Configuration
  | .lStereoC => some left
  | .rStereoC => some right
  | _ => none

def pl1WithConfigurations (left right : Configuration) :
    MolecularStructure PL1Site where
  node := pl1NeutralNode
  covalentBonds := pl1CovalentBonds
  configuration := pl1Configuration left right
  hydrogenBonds := []

/-- One selected enantiomer, with both terminal glycerol C2 centres `R`. -/
def pl1RR : MolecularStructure PL1Site :=
  pl1WithConfigurations .R .R

/-- Its mirror image. -/
def pl1SS : MolecularStructure PL1Site :=
  pl1WithConfigurations .S .S

/-- The mixed configuration used to encode the source-stated achiral meso form. -/
def pl1RS : MolecularStructure PL1Site :=
  pl1WithConfigurations .R .S

/-! ## Fragment contraction of the displayed structure -/

inductive PL1FragmentSite
  | hydrogenCap
  | phosphateLeft
  | phosphateRight
  | glycerolLeft
  | glycerolCentral
  | glycerolRight
  | fattyAcylLeftOuter
  | fattyAcylLeftInner
  | fattyAcylRightInner
  | fattyAcylRightOuter
  deriving DecidableEq, Fintype, Repr

def pl1FragmentKind : PL1FragmentSite → FragmentKind
  | .hydrogenCap => .hydrogenCap
  | .phosphateLeft | .phosphateRight => .phosphate
  | .glycerolLeft | .glycerolCentral | .glycerolRight => .glycerol
  | .fattyAcylLeftOuter | .fattyAcylLeftInner |
    .fattyAcylRightInner | .fattyAcylRightOuter => .fattyAcyl

def pl1FragmentAdjacent : PL1FragmentSite → PL1FragmentSite → Prop
  | .hydrogenCap, .glycerolCentral
  | .glycerolCentral, .hydrogenCap
  | .phosphateLeft, .glycerolLeft
  | .glycerolLeft, .phosphateLeft
  | .phosphateLeft, .glycerolCentral
  | .glycerolCentral, .phosphateLeft
  | .phosphateRight, .glycerolCentral
  | .glycerolCentral, .phosphateRight
  | .phosphateRight, .glycerolRight
  | .glycerolRight, .phosphateRight
  | .fattyAcylLeftOuter, .glycerolLeft
  | .glycerolLeft, .fattyAcylLeftOuter
  | .fattyAcylLeftInner, .glycerolLeft
  | .glycerolLeft, .fattyAcylLeftInner
  | .fattyAcylRightInner, .glycerolRight
  | .glycerolRight, .fattyAcylRightInner
  | .fattyAcylRightOuter, .glycerolRight
  | .glycerolRight, .fattyAcylRightOuter => True
  | _, _ => False

theorem pl1FragmentAdjacent_symm : Std.Symm pl1FragmentAdjacent := by
  constructor
  intro first second adjacency
  cases first <;> cases second <;>
    simp_all [pl1FragmentAdjacent]

theorem pl1FragmentAdjacent_irrefl : Std.Irrefl pl1FragmentAdjacent := by
  constructor
  intro site adjacency
  cases site <;> simp_all [pl1FragmentAdjacent]

def pl1FragmentGraph : SimpleGraph PL1FragmentSite where
  Adj := pl1FragmentAdjacent
  symm := pl1FragmentAdjacent_symm
  loopless := pl1FragmentAdjacent_irrefl

local instance : DecidableRel pl1FragmentAdjacent := by
  intro first second
  cases first <;> cases second <;>
    simp only [pl1FragmentAdjacent] <;>
    infer_instance

local instance : DecidableRel pl1FragmentGraph.Adj := by
  intro first second
  change Decidable (pl1FragmentAdjacent first second)
  infer_instance

def pl1FragmentAssembly : FragmentAssembly PL1FragmentSite where
  kind := pl1FragmentKind
  attachmentGraph := pl1FragmentGraph

theorem pl1FragmentAssembly_matches_source :
    SourceFragmentAssembly pl1FragmentAssembly 1 := by
  letI : DecidableRel pl1FragmentAssembly.attachmentGraph.Adj := by
    intro first second
    change Decidable (pl1FragmentAdjacent first second)
    infer_instance
  let neighbors : PL1FragmentSite → Finset PL1FragmentSite
    | .hydrogenCap => { .glycerolCentral }
    | .phosphateLeft => { .glycerolLeft, .glycerolCentral }
    | .phosphateRight => { .glycerolCentral, .glycerolRight }
    | .glycerolLeft =>
        { .phosphateLeft, .fattyAcylLeftOuter, .fattyAcylLeftInner }
    | .glycerolCentral => { .hydrogenCap, .phosphateLeft, .phosphateRight }
    | .glycerolRight =>
        { .phosphateRight, .fattyAcylRightInner, .fattyAcylRightOuter }
    | .fattyAcylLeftOuter | .fattyAcylLeftInner => { .glycerolLeft }
    | .fattyAcylRightInner | .fattyAcylRightOuter => { .glycerolRight }
  have neighborFilter (site : PL1FragmentSite) :
      (Finset.univ.filter fun other => pl1FragmentAdjacent site other) =
        neighbors site := by
    ext other
    cases site <;> cases other <;>
      simp [neighbors, pl1FragmentAdjacent]
  have graphDegree (site : PL1FragmentSite) :
      pl1FragmentGraph.degree site = (neighbors site).card := by
    unfold SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_eq_filter]
    exact congrArg Finset.card (neighborFilter site)
  have assemblyDegree (site : PL1FragmentSite) :
      pl1FragmentAssembly.degree site = pl1FragmentGraph.degree site := by
    unfold FragmentAssembly.degree SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_eq_filter]
    apply congrArg Finset.card
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change pl1FragmentAdjacent site other ↔ pl1FragmentAdjacent site other
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [MatchesSourceFragmentInventory]
    decide
  · intro fragment
    rw [assemblyDegree, graphDegree]
    change (neighbors fragment).card = (pl1FragmentKind fragment).portCount
    cases fragment <;> decide
  · change pl1FragmentGraph.IsTree
    have connected : pl1FragmentGraph.Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨.glycerolCentral, ?_⟩
      intro site
      have centralToHydrogen :
          pl1FragmentGraph.Reachable .glycerolCentral .hydrogenCap :=
        (show pl1FragmentGraph.Adj .glycerolCentral .hydrogenCap by trivial).reachable
      have centralToLeftPhosphate :
          pl1FragmentGraph.Reachable .glycerolCentral .phosphateLeft :=
        (show pl1FragmentGraph.Adj .glycerolCentral .phosphateLeft by trivial).reachable
      have centralToRightPhosphate :
          pl1FragmentGraph.Reachable .glycerolCentral .phosphateRight :=
        (show pl1FragmentGraph.Adj .glycerolCentral .phosphateRight by trivial).reachable
      have centralToLeftGlycerol :
          pl1FragmentGraph.Reachable .glycerolCentral .glycerolLeft :=
        centralToLeftPhosphate.trans
          (show pl1FragmentGraph.Adj .phosphateLeft .glycerolLeft by trivial).reachable
      have centralToRightGlycerol :
          pl1FragmentGraph.Reachable .glycerolCentral .glycerolRight :=
        centralToRightPhosphate.trans
          (show pl1FragmentGraph.Adj .phosphateRight .glycerolRight by trivial).reachable
      cases site
      · exact centralToHydrogen
      · exact centralToLeftPhosphate
      · exact centralToRightPhosphate
      · exact centralToLeftGlycerol
      · exact .rfl
      · exact centralToRightGlycerol
      · exact centralToLeftGlycerol.trans
          (show pl1FragmentGraph.Adj .glycerolLeft .fattyAcylLeftOuter by trivial).reachable
      · exact centralToLeftGlycerol.trans
          (show pl1FragmentGraph.Adj .glycerolLeft .fattyAcylLeftInner by trivial).reachable
      · exact centralToRightGlycerol.trans
          (show pl1FragmentGraph.Adj .glycerolRight .fattyAcylRightInner by trivial).reachable
      · exact centralToRightGlycerol.trans
          (show pl1FragmentGraph.Adj .glycerolRight .fattyAcylRightOuter by trivial).reachable
    have degreeSum :
        (∑ site : PL1FragmentSite, pl1FragmentGraph.degree site) = 18 := by
      simp_rw [graphDegree]
      decide
    have handshake := pl1FragmentGraph.sum_degrees_eq_twice_card_edges
    have edgeCard : pl1FragmentGraph.edgeFinset.card = 9 := by
      rw [degreeSum] at handshake
      omega
    apply (SimpleGraph.isTree_iff_connected_and_card).2
    refine ⟨connected, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      pl1FragmentGraph.card_edgeSet, edgeCard]
    decide

def pl1FragmentOfSite : PL1Site → PL1FragmentSite
  | .lOuterResidue | .lOuterCarbonylC | .lOuterCarbonylO =>
      .fattyAcylLeftOuter
  | .lInnerCarbonylC | .lInnerCarbonylO | .lInnerResidue =>
      .fattyAcylLeftInner
  | .rInnerCarbonylC | .rInnerCarbonylO | .rInnerResidue =>
      .fattyAcylRightInner
  | .rOuterCarbonylC | .rOuterCarbonylO | .rOuterResidue =>
      .fattyAcylRightOuter
  | .lOuterEsterO | .lOuterGlycerolC | .lStereoC |
    .lInnerEsterO | .lPhosphateGlycerolC | .lGlycerolPhosphateO =>
      .glycerolLeft
  | .lPhosphorus | .lPhosphorylO | .lAcidO =>
      .phosphateLeft
  | .lCentralBridgeO | .centralLeftC | .centralC |
    .centralHydroxylO | .centralRightC | .rCentralBridgeO =>
      .glycerolCentral
  | .rPhosphorus | .rPhosphorylO | .rAcidO =>
      .phosphateRight
  | .rGlycerolPhosphateO | .rPhosphateGlycerolC | .rStereoC |
    .rInnerEsterO | .rOuterGlycerolC | .rOuterEsterO =>
      .glycerolRight

/-- Contraction of the explicit atom graph back to the source fragments.  The
one type-`a` edge is represented by the single H attached to the central OH. -/
def RealizesFragmentAdjacency (molecule : MolecularStructure PL1Site)
    (first second : PL1FragmentSite) : Prop :=
  first ≠ second ∧
    (((first = .hydrogenCap ∧ second = .glycerolCentral) ∨
      (first = .glycerolCentral ∧ second = .hydrogenCap)) ∧
        (molecule.node .centralHydroxylO).displayedAttachedHydrogens = 1 ∨
     ∃ left right order,
       HasCovalentBond molecule left right order ∧
       ((pl1FragmentOfSite left = first ∧ pl1FragmentOfSite right = second) ∨
        (pl1FragmentOfSite left = second ∧ pl1FragmentOfSite right = first)))

def FragmentContractionMatchesSource
    (molecule : MolecularStructure PL1Site) : Prop :=
  ∀ first second,
    pl1FragmentGraph.Adj first second ↔
      RealizesFragmentAdjacency molecule first second

/-! ## Symmetry and stereochemistry -/

def reflectPL1Site : PL1Site → PL1Site
  | .lOuterResidue => .rOuterResidue
  | .lOuterCarbonylC => .rOuterCarbonylC
  | .lOuterCarbonylO => .rOuterCarbonylO
  | .lOuterEsterO => .rOuterEsterO
  | .lOuterGlycerolC => .rOuterGlycerolC
  | .lStereoC => .rStereoC
  | .lInnerEsterO => .rInnerEsterO
  | .lInnerCarbonylC => .rInnerCarbonylC
  | .lInnerCarbonylO => .rInnerCarbonylO
  | .lInnerResidue => .rInnerResidue
  | .lPhosphateGlycerolC => .rPhosphateGlycerolC
  | .lGlycerolPhosphateO => .rGlycerolPhosphateO
  | .lPhosphorus => .rPhosphorus
  | .lPhosphorylO => .rPhosphorylO
  | .lAcidO => .rAcidO
  | .lCentralBridgeO => .rCentralBridgeO
  | .centralLeftC => .centralRightC
  | .centralC => .centralC
  | .centralHydroxylO => .centralHydroxylO
  | .centralRightC => .centralLeftC
  | .rCentralBridgeO => .lCentralBridgeO
  | .rPhosphorus => .lPhosphorus
  | .rPhosphorylO => .lPhosphorylO
  | .rAcidO => .lAcidO
  | .rGlycerolPhosphateO => .lGlycerolPhosphateO
  | .rPhosphateGlycerolC => .lPhosphateGlycerolC
  | .rStereoC => .lStereoC
  | .rInnerEsterO => .lInnerEsterO
  | .rInnerCarbonylC => .lInnerCarbonylC
  | .rInnerCarbonylO => .lInnerCarbonylO
  | .rInnerResidue => .lInnerResidue
  | .rOuterGlycerolC => .lOuterGlycerolC
  | .rOuterEsterO => .lOuterEsterO
  | .rOuterCarbonylC => .lOuterCarbonylC
  | .rOuterCarbonylO => .lOuterCarbonylO
  | .rOuterResidue => .lOuterResidue

theorem reflectPL1Site_involutive : Function.Involutive reflectPL1Site := by
  intro site
  cases site <;> rfl

def reflectPL1Equiv : PL1Site ≃ PL1Site :=
  reflectPL1Site_involutive.toPerm reflectPL1Site

def SameCovalentSkeletonVia {First Second : Type}
    (equivalence : First ≃ Second)
    (first : MolecularStructure First) (second : MolecularStructure Second) : Prop :=
  (∀ site,
      (second.node (equivalence site)).skeletonKind =
        (first.node site).skeletonKind) ∧
  (∀ left right order,
      HasCovalentBond second (equivalence left) (equivalence right) order ↔
        HasCovalentBond first left right order)

def StructureIsomorphicVia {First Second : Type}
    (equivalence : First ≃ Second)
    (first : MolecularStructure First) (second : MolecularStructure Second) : Prop :=
  (∀ site, second.node (equivalence site) = first.node site) ∧
  (∀ left right order,
      HasCovalentBond second (equivalence left) (equivalence right) order ↔
        HasCovalentBond first left right order) ∧
  (∀ site,
      second.configuration (equivalence site) = first.configuration site) ∧
  (∀ donor hydrogenIndex acceptor,
      HasHydrogenBond second (equivalence donor) hydrogenIndex
          (equivalence acceptor) ↔
        HasHydrogenBond first donor hydrogenIndex acceptor)

def MirrorRelatedVia {First Second : Type}
    (equivalence : First ≃ Second)
    (first : MolecularStructure First) (second : MolecularStructure Second) : Prop :=
  (∀ site, second.node (equivalence site) = first.node site) ∧
  (∀ left right order,
      HasCovalentBond second (equivalence left) (equivalence right) order ↔
        HasCovalentBond first left right order) ∧
  (∀ site,
      second.configuration (equivalence site) =
        (first.configuration site).map Configuration.opposite) ∧
  (∀ donor hydrogenIndex acceptor,
      HasHydrogenBond second (equivalence donor) hydrogenIndex
          (equivalence acceptor) ↔
        HasHydrogenBond first donor hydrogenIndex acceptor)

def IsEnantiomericPair {Site : Type}
    (first second : MolecularStructure Site) : Prop :=
  (∃ equivalence : Site ≃ Site,
      MirrorRelatedVia equivalence first second) ∧
  (∃ site configuration, first.configuration site = some configuration) ∧
  ¬ ∃ equivalence : Site ≃ Site,
      StructureIsomorphicVia equivalence first second

/-- A configured tetrahedral carbon is tied to its three displayed ligands and
its one attached hydrogen; the absolute-configuration datum is therefore not
an unattached chirality flag. -/
def TetrahedralCarbonConfiguration
    (molecule : MolecularStructure PL1Site) (centre : PL1Site)
    (first second third : PL1Site) (configuration : Configuration) : Prop :=
  molecule.node centre = displayedAtom .carbon 1 ∧
  centre ≠ first ∧ centre ≠ second ∧ centre ≠ third ∧
  first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
  HasCovalentBond molecule centre first .single ∧
  HasCovalentBond molecule centre second .single ∧
  HasCovalentBond molecule centre third .single ∧
  molecule.configuration centre = some configuration

def ExactlyTerminalConfigurations (molecule : MolecularStructure PL1Site)
    (left right : Configuration) : Prop :=
  TetrahedralCarbonConfiguration molecule .lStereoC
    .lOuterGlycerolC .lInnerEsterO .lPhosphateGlycerolC left ∧
  TetrahedralCarbonConfiguration molecule .rStereoC
    .rPhosphateGlycerolC .rInnerEsterO .rOuterGlycerolC right ∧
  ∀ site, site ≠ .lStereoC → site ≠ .rStereoC →
    molecule.configuration site = none

/-! ## The monoanion and its cooperative intramolecular hydrogen bonds -/

def yRightNode : PL1Site → MolecularNode
  | .rAcidO => displayedAtom .oxygen 0 (-1)
  | site => pl1NeutralNode site

def yLeftNode : PL1Site → MolecularNode
  | .lAcidO => displayedAtom .oxygen 0 (-1)
  | site => pl1NeutralNode site

/-- `P_L-O-H···O_c-H···O⁻-P_R`. -/
def yRightHydrogenBonds : List (HydrogenBond PL1Site) :=
  [ { donor := .lAcidO, donorHydrogenIndex := 0,
      acceptor := .centralHydroxylO },
    { donor := .centralHydroxylO, donorHydrogenIndex := 0,
      acceptor := .rAcidO } ]

/-- The symmetry-related relay with left and right phosphates exchanged. -/
def yLeftHydrogenBonds : List (HydrogenBond PL1Site) :=
  [ { donor := .rAcidO, donorHydrogenIndex := 0,
      acceptor := .centralHydroxylO },
    { donor := .centralHydroxylO, donorHydrogenIndex := 0,
      acceptor := .lAcidO } ]

def yRightDeprotonated : MolecularStructure PL1Site where
  node := yRightNode
  covalentBonds := pl1CovalentBonds
  configuration := pl1Configuration .R .R
  hydrogenBonds := yRightHydrogenBonds

def yLeftDeprotonated : MolecularStructure PL1Site where
  node := yLeftNode
  covalentBonds := pl1CovalentBonds
  configuration := pl1Configuration .R .R
  hydrogenBonds := yLeftHydrogenBonds

def FirstDeprotonationAt (neutral monoanion : MolecularStructure PL1Site)
    (site : PL1Site) : Prop :=
  SameCovalentSkeletonVia (Equiv.refl PL1Site) neutral monoanion ∧
  neutral.node site = displayedAtom .oxygen 1 0 ∧
  monoanion.node site = displayedAtom .oxygen 0 (-1) ∧
  (∀ other, other ≠ site → monoanion.node other = neutral.node other) ∧
  monoanion.configuration = neutral.configuration

def SecondDeprotonationAt (monoanion dianion : MolecularStructure PL1Site)
    (site : PL1Site) : Prop :=
  SameCovalentSkeletonVia (Equiv.refl PL1Site) monoanion dianion ∧
  monoanion.node site = displayedAtom .oxygen 1 0 ∧
  dianion.node site = displayedAtom .oxygen 0 (-1) ∧
  (∀ other, other ≠ site → dianion.node other = monoanion.node other) ∧
  dianion.configuration = monoanion.configuration

/-- The two H bonds mediated by the central glycerol 2-OH. -/
def CooperativeHydrogenRelay (molecule : MolecularStructure PL1Site)
    (neutralPhosphateO centralAlcoholO anionicPhosphateO : PL1Site) : Prop :=
  molecule.node neutralPhosphateO = displayedAtom .oxygen 1 0 ∧
  molecule.node centralAlcoholO = displayedAtom .oxygen 1 0 ∧
  molecule.node anionicPhosphateO = displayedAtom .oxygen 0 (-1) ∧
  HasHydrogenBond molecule neutralPhosphateO 0 centralAlcoholO ∧
  HasHydrogenBond molecule centralAlcoholO 0 anionicPhosphateO

/-- A list is a covalent path when every successive displayed pair has a
covalent bond of some explicit order. -/
def IsDisplayedCovalentPath (molecule : MolecularStructure PL1Site) :
    List PL1Site → Prop
  | [] => False
  | [_] => True
  | first :: second :: remainder =>
      (∃ order, HasCovalentBond molecule first second order) ∧
        IsDisplayedCovalentPath molecule (second :: remainder)

/-- The covalent side of the left intramolecular ring closed by
`P_L-O-H···O_c`. -/
def leftRelayCovalentPath : List PL1Site :=
  [ .lAcidO, .lPhosphorus, .lCentralBridgeO, .centralLeftC,
    .centralC, .centralHydroxylO ]

/-- The covalent side of the right intramolecular ring closed by
`O_c-H···O⁻-P_R`. -/
def rightRelayCovalentPath : List PL1Site :=
  [ .centralHydroxylO, .centralC, .centralRightC, .rCentralBridgeO,
    .rPhosphorus, .rAcidO ]

/-- Both H bonds close intramolecular rings through the three-carbon central
glycerol tether.  The two covalent paths share the
`centralHydroxylO-centralC` edge, making the displayed relay cooperative. -/
def TwoHydrogenBondedRelayRingClosures
    (molecule : MolecularStructure PL1Site) : Prop :=
  IsDisplayedCovalentPath molecule leftRelayCovalentPath ∧
  IsDisplayedCovalentPath molecule rightRelayCovalentPath ∧
  HasHydrogenBond molecule .lAcidO 0 .centralHydroxylO ∧
  HasHydrogenBond molecule .centralHydroxylO 0 .rAcidO

/-- Structural content of the pKa explanation: removing the remaining
phosphate proton destroys the two-donor relay and leaves two distinct anionic
phosphate oxygens. -/
def SecondDeprotonationPenaltyPattern
    (monoanion : MolecularStructure PL1Site) : Prop :=
  ∀ dianion,
    ValidMolecularStructure dianion →
    SecondDeprotonationAt monoanion dianion .lAcidO →
      TotalFormalCharge dianion = -2 ∧
      dianion.node .lAcidO = displayedAtom .oxygen 0 (-1) ∧
      dianion.node .rAcidO = displayedAtom .oxygen 0 (-1) ∧
      .lAcidO ≠ (.rAcidO : PL1Site) ∧
      ¬ CooperativeHydrogenRelay dianion
          .lAcidO .centralHydroxylO .rAcidO

/-! ## Finite audits of the displayed covalent skeleton -/

/-- A bounded-list form of bond existence.  Keeping the witness in the actual
bond-list index type makes all later finite audits kernel-reducible without
searching the much larger ambient type of arbitrary bonds. -/
private theorem hasCovalentBond_iff_get {Site : Type}
    (molecule : MolecularStructure Site) (first second : Site)
    (order : BondOrder) :
    HasCovalentBond molecule first second order ↔
      ∃ i : Fin molecule.covalentBonds.length,
        let bond := molecule.covalentBonds.get i
        bond.order = order ∧
          ((bond.left = first ∧ bond.right = second) ∨
           (bond.left = second ∧ bond.right = first)) := by
  unfold HasCovalentBond
  exact List.exists_mem_iff_get

/-- Use the bounded witness formulation as the computational decision
procedure for all concrete bond queries below. -/
local instance boundedHasCovalentBondDecidable {Site : Type}
    [DecidableEq Site] (molecule : MolecularStructure Site)
    (first second : Site) (order : BondOrder) :
    Decidable (HasCovalentBond molecule first second order) :=
  decidable_of_iff
    (∃ i : Fin molecule.covalentBonds.length,
      let bond := molecule.covalentBonds.get i
      bond.order = order ∧
        ((bond.left = first ∧ bond.right = second) ∨
         (bond.left = second ∧ bond.right = first)))
    (hasCovalentBond_iff_get molecule first second order).symm

@[reducible] private def bondOrderFintype : Fintype BondOrder where
  elems := { .single, .double }
  complete order := by cases order <;> simp

private def covalentBondEquiv :
    CovalentBond PL1Site ≃ PL1Site × PL1Site × BondOrder where
  toFun bond := (bond.left, bond.right, bond.order)
  invFun data :=
    { left := data.1, right := data.2.1, order := data.2.2 }
  left_inv bond := by cases bond; rfl
  right_inv data := by rcases data with ⟨left, right, order⟩; rfl

@[reducible] private def covalentBondFintype [Fintype BondOrder] :
    Fintype (CovalentBond PL1Site) :=
  Fintype.ofEquiv (PL1Site × PL1Site × BondOrder) covalentBondEquiv.symm

local instance : Fintype BondOrder := bondOrderFintype
local instance : Fintype (CovalentBond PL1Site) := covalentBondFintype
local instance : DecidableRel pl1RR.covalentGraph.Adj := by
  intro first second
  change Decidable (CovalentlyAdjacent pl1RR first second)
  unfold CovalentlyAdjacent HasCovalentBond
  infer_instance

/-- Pairwise exclusion of equal unordered endpoints is a list-sized certificate
for uniqueness; it avoids deciding over the much larger ambient bond type. -/
private theorem uniqueCovalentPairs_of_pairwise
    {Site : Type} (bonds : List (CovalentBond Site))
    (pairwise : bonds.Pairwise
      (fun first second => ¬ SameUnorderedEndpoints first second)) :
    ∀ first ∈ bonds, ∀ second ∈ bonds,
      SameUnorderedEndpoints first second → first = second := by
  intro first firstMem second secondMem sameEndpoints
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp firstMem
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp secondMem
  subst first
  subst second
  rcases lt_trichotomy i j with before | equal | after
  · exact (pairwise.rel_get_of_lt before sameEndpoints).elim
  · cases equal
    rfl
  · exfalso
    apply (pairwise.rel_get_of_lt after)
    rcases sameEndpoints with endpoints | endpoints
    · exact Or.inl ⟨endpoints.1.symm, endpoints.2.symm⟩
    · exact Or.inr ⟨endpoints.2.symm, endpoints.1.symm⟩

private theorem pl1NoSelfBonds : NoSelfBonds pl1RR := by
  unfold NoSelfBonds
  change ∀ bond ∈ pl1CovalentBonds, bond.left ≠ bond.right
  rw [List.forall_mem_iff_get]
  decide

private theorem pl1UniqueCovalentPairs : UniqueCovalentPairs pl1RR := by
  unfold UniqueCovalentPairs
  change ∀ first ∈ pl1CovalentBonds, ∀ second ∈ pl1CovalentBonds,
    SameUnorderedEndpoints first second → first = second
  apply uniqueCovalentPairs_of_pairwise pl1CovalentBonds
  unfold SameUnorderedEndpoints
  decide

private theorem pl1NoPeroxideBond : NoPeroxideBond pl1RR := by
  unfold NoPeroxideBond
  simp only [pl1RR, pl1WithConfigurations]
  rw [List.forall_mem_iff_get]
  decide

/-- Reflection pairs every displayed bond-list entry with another entry of the
same order, up to the chemically irrelevant orientation of an undirected bond. -/
private theorem pl1BondIndex_reflect :
    ∀ i : Fin pl1CovalentBonds.length,
      ∃ j : Fin pl1CovalentBonds.length,
        let first := pl1CovalentBonds.get i
        let reflected := pl1CovalentBonds.get j
        reflected.order = first.order ∧
          ((reflected.left = reflectPL1Site first.left ∧
              reflected.right = reflectPL1Site first.right) ∨
           (reflected.left = reflectPL1Site first.right ∧
              reflected.right = reflectPL1Site first.left)) := by
  decide

private theorem pl1HasCovalentBond_reflect_forward
    {left right : PL1Site} {order : BondOrder}
    (bond : HasCovalentBond pl1RR left right order) :
    HasCovalentBond pl1RR (reflectPL1Site left) (reflectPL1Site right) order := by
  rw [hasCovalentBond_iff_get] at bond ⊢
  rcases bond with ⟨i, orderAtI, endpointsAtI⟩
  obtain ⟨j, reflectedOrder, reflectedEndpoints⟩ := pl1BondIndex_reflect i
  refine ⟨j, reflectedOrder.trans orderAtI, ?_⟩
  rcases endpointsAtI with direct | reversed
  · rcases reflectedEndpoints with reflectedDirect | reflectedReversed
    · exact Or.inl
        ⟨reflectedDirect.1.trans (congrArg reflectPL1Site direct.1),
          reflectedDirect.2.trans (congrArg reflectPL1Site direct.2)⟩
    · exact Or.inr
        ⟨reflectedReversed.1.trans (congrArg reflectPL1Site direct.2),
          reflectedReversed.2.trans (congrArg reflectPL1Site direct.1)⟩
  · rcases reflectedEndpoints with reflectedDirect | reflectedReversed
    · exact Or.inr
        ⟨reflectedDirect.1.trans (congrArg reflectPL1Site reversed.1),
          reflectedDirect.2.trans (congrArg reflectPL1Site reversed.2)⟩
    · exact Or.inl
        ⟨reflectedReversed.1.trans (congrArg reflectPL1Site reversed.2),
          reflectedReversed.2.trans (congrArg reflectPL1Site reversed.1)⟩

private theorem pl1HasCovalentBond_reflection
    (left right : PL1Site) (order : BondOrder) :
    HasCovalentBond pl1RR (reflectPL1Site left) (reflectPL1Site right) order ↔
      HasCovalentBond pl1RR left right order := by
  constructor
  · intro reflectedBond
    have twiceReflected := pl1HasCovalentBond_reflect_forward reflectedBond
    rw [reflectPL1Site_involutive left, reflectPL1Site_involutive right] at twiceReflected
    exact twiceReflected
  · exact pl1HasCovalentBond_reflect_forward

private def covalentBondEdge {Site : Type}
    (bond : CovalentBond Site) : Sym2 Site :=
  s(bond.left, bond.right)

private theorem covalentBondEdge_eq_iff {Site : Type}
    (bond : CovalentBond Site) (first second : Site) :
    covalentBondEdge bond = s(first, second) ↔
      (bond.left = first ∧ bond.right = second) ∨
      (bond.left = second ∧ bond.right = first) := by
  constructor
  · intro equality
    rcases Sym2.exact equality with direct | reversed
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (direct | reversed)
    · change s(bond.left, bond.right) = s(first, second)
      rw [direct.1, direct.2]
    · change s(bond.left, bond.right) = s(first, second)
      rw [reversed.1, reversed.2]
      exact Sym2.sound (.swap second first)

private def pl1CovalentEdgeList : List (Sym2 PL1Site) :=
  pl1CovalentBonds.map covalentBondEdge

private theorem pl1CovalentEdgeList_mem_iff_adj
    (first second : PL1Site) :
    s(first, second) ∈ pl1CovalentEdgeList ↔
      pl1RR.covalentGraph.Adj first second := by
  constructor
  · intro edgeMem
    rw [pl1CovalentEdgeList, List.mem_map] at edgeMem
    rcases edgeMem with ⟨bond, bondMem, edgeEquality⟩
    have endpoints :=
      (covalentBondEdge_eq_iff bond first second).mp edgeEquality
    have noSelf := pl1NoSelfBonds bond bondMem
    rcases endpoints with direct | reversed
    · refine ⟨?_, bond.order, bond, bondMem, rfl, Or.inl direct⟩
      intro equalSites
      exact noSelf (direct.1.trans (equalSites.trans direct.2.symm))
    · refine ⟨?_, bond.order, bond, bondMem, rfl, Or.inr reversed⟩
      intro equalSites
      exact noSelf (reversed.1.trans (equalSites.symm.trans reversed.2.symm))
  · rintro ⟨_, order, bond, bondMem, bondOrder, endpoints⟩
    rw [pl1CovalentEdgeList, List.mem_map]
    exact ⟨bond, bondMem,
      (covalentBondEdge_eq_iff bond first second).mpr endpoints⟩

private def pl1CovalentEdgeFinset : Finset (Sym2 PL1Site) :=
  pl1CovalentEdgeList.toFinset

private theorem pl1CovalentGraph_edgeFinset :
    pl1RR.covalentGraph.edgeFinset = pl1CovalentEdgeFinset := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ first second =>
      simpa [pl1CovalentEdgeFinset] using
        (pl1CovalentEdgeList_mem_iff_adj first second).symm

private theorem pl1CovalentEdgeList_nodup : pl1CovalentEdgeList.Nodup := by
  decide

/-- The displayed covalent graph is connected and has one fewer edge than
vertices.  This is the graph-theoretic acyclicity check for both requested
structures, whose covalent bond lists are identical. -/
theorem pl1CovalentGraph_isTree : pl1RR.covalentGraph.IsTree := by
  have connected : pl1RR.covalentGraph.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨.centralC, ?_⟩
    have reachCentralLeft :
        pl1RR.covalentGraph.Reachable .centralC .centralLeftC :=
      (show pl1RR.covalentGraph.Adj .centralC .centralLeftC by decide).reachable
    have reachCentralHydroxyl :
        pl1RR.covalentGraph.Reachable .centralC .centralHydroxylO :=
      (show pl1RR.covalentGraph.Adj .centralC .centralHydroxylO by decide).reachable
    have reachCentralRight :
        pl1RR.covalentGraph.Reachable .centralC .centralRightC :=
      (show pl1RR.covalentGraph.Adj .centralC .centralRightC by decide).reachable
    have reachLeftBridge :
        pl1RR.covalentGraph.Reachable .centralC .lCentralBridgeO :=
      reachCentralLeft.trans
        (show pl1RR.covalentGraph.Adj .centralLeftC .lCentralBridgeO by
          decide).reachable
    have reachLeftPhosphorus :
        pl1RR.covalentGraph.Reachable .centralC .lPhosphorus :=
      reachLeftBridge.trans
        (show pl1RR.covalentGraph.Adj .lCentralBridgeO .lPhosphorus by
          decide).reachable
    have reachLeftPhosphoryl :
        pl1RR.covalentGraph.Reachable .centralC .lPhosphorylO :=
      reachLeftPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .lPhosphorus .lPhosphorylO by
          decide).reachable
    have reachLeftAcid :
        pl1RR.covalentGraph.Reachable .centralC .lAcidO :=
      reachLeftPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .lPhosphorus .lAcidO by
          decide).reachable
    have reachLeftGlycerolPhosphateO :
        pl1RR.covalentGraph.Reachable .centralC .lGlycerolPhosphateO :=
      reachLeftPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .lPhosphorus .lGlycerolPhosphateO by
          decide).reachable
    have reachLeftPhosphateGlycerolC :
        pl1RR.covalentGraph.Reachable .centralC .lPhosphateGlycerolC :=
      reachLeftGlycerolPhosphateO.trans
        (show pl1RR.covalentGraph.Adj .lGlycerolPhosphateO .lPhosphateGlycerolC by
          decide).reachable
    have reachLeftStereo :
        pl1RR.covalentGraph.Reachable .centralC .lStereoC :=
      reachLeftPhosphateGlycerolC.trans
        (show pl1RR.covalentGraph.Adj .lPhosphateGlycerolC .lStereoC by
          decide).reachable
    have reachLeftOuterGlycerol :
        pl1RR.covalentGraph.Reachable .centralC .lOuterGlycerolC :=
      reachLeftStereo.trans
        (show pl1RR.covalentGraph.Adj .lStereoC .lOuterGlycerolC by
          decide).reachable
    have reachLeftOuterEster :
        pl1RR.covalentGraph.Reachable .centralC .lOuterEsterO :=
      reachLeftOuterGlycerol.trans
        (show pl1RR.covalentGraph.Adj .lOuterGlycerolC .lOuterEsterO by
          decide).reachable
    have reachLeftOuterCarbonyl :
        pl1RR.covalentGraph.Reachable .centralC .lOuterCarbonylC :=
      reachLeftOuterEster.trans
        (show pl1RR.covalentGraph.Adj .lOuterEsterO .lOuterCarbonylC by
          decide).reachable
    have reachLeftOuterCarbonylO :
        pl1RR.covalentGraph.Reachable .centralC .lOuterCarbonylO :=
      reachLeftOuterCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .lOuterCarbonylC .lOuterCarbonylO by
          decide).reachable
    have reachLeftOuterResidue :
        pl1RR.covalentGraph.Reachable .centralC .lOuterResidue :=
      reachLeftOuterCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .lOuterCarbonylC .lOuterResidue by
          decide).reachable
    have reachLeftInnerEster :
        pl1RR.covalentGraph.Reachable .centralC .lInnerEsterO :=
      reachLeftStereo.trans
        (show pl1RR.covalentGraph.Adj .lStereoC .lInnerEsterO by
          decide).reachable
    have reachLeftInnerCarbonyl :
        pl1RR.covalentGraph.Reachable .centralC .lInnerCarbonylC :=
      reachLeftInnerEster.trans
        (show pl1RR.covalentGraph.Adj .lInnerEsterO .lInnerCarbonylC by
          decide).reachable
    have reachLeftInnerCarbonylO :
        pl1RR.covalentGraph.Reachable .centralC .lInnerCarbonylO :=
      reachLeftInnerCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .lInnerCarbonylC .lInnerCarbonylO by
          decide).reachable
    have reachLeftInnerResidue :
        pl1RR.covalentGraph.Reachable .centralC .lInnerResidue :=
      reachLeftInnerCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .lInnerCarbonylC .lInnerResidue by
          decide).reachable
    have reachRightBridge :
        pl1RR.covalentGraph.Reachable .centralC .rCentralBridgeO :=
      reachCentralRight.trans
        (show pl1RR.covalentGraph.Adj .centralRightC .rCentralBridgeO by
          decide).reachable
    have reachRightPhosphorus :
        pl1RR.covalentGraph.Reachable .centralC .rPhosphorus :=
      reachRightBridge.trans
        (show pl1RR.covalentGraph.Adj .rCentralBridgeO .rPhosphorus by
          decide).reachable
    have reachRightPhosphoryl :
        pl1RR.covalentGraph.Reachable .centralC .rPhosphorylO :=
      reachRightPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .rPhosphorus .rPhosphorylO by
          decide).reachable
    have reachRightAcid :
        pl1RR.covalentGraph.Reachable .centralC .rAcidO :=
      reachRightPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .rPhosphorus .rAcidO by
          decide).reachable
    have reachRightGlycerolPhosphateO :
        pl1RR.covalentGraph.Reachable .centralC .rGlycerolPhosphateO :=
      reachRightPhosphorus.trans
        (show pl1RR.covalentGraph.Adj .rPhosphorus .rGlycerolPhosphateO by
          decide).reachable
    have reachRightPhosphateGlycerolC :
        pl1RR.covalentGraph.Reachable .centralC .rPhosphateGlycerolC :=
      reachRightGlycerolPhosphateO.trans
        (show pl1RR.covalentGraph.Adj .rGlycerolPhosphateO .rPhosphateGlycerolC by
          decide).reachable
    have reachRightStereo :
        pl1RR.covalentGraph.Reachable .centralC .rStereoC :=
      reachRightPhosphateGlycerolC.trans
        (show pl1RR.covalentGraph.Adj .rPhosphateGlycerolC .rStereoC by
          decide).reachable
    have reachRightInnerEster :
        pl1RR.covalentGraph.Reachable .centralC .rInnerEsterO :=
      reachRightStereo.trans
        (show pl1RR.covalentGraph.Adj .rStereoC .rInnerEsterO by
          decide).reachable
    have reachRightInnerCarbonyl :
        pl1RR.covalentGraph.Reachable .centralC .rInnerCarbonylC :=
      reachRightInnerEster.trans
        (show pl1RR.covalentGraph.Adj .rInnerEsterO .rInnerCarbonylC by
          decide).reachable
    have reachRightInnerCarbonylO :
        pl1RR.covalentGraph.Reachable .centralC .rInnerCarbonylO :=
      reachRightInnerCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .rInnerCarbonylC .rInnerCarbonylO by
          decide).reachable
    have reachRightInnerResidue :
        pl1RR.covalentGraph.Reachable .centralC .rInnerResidue :=
      reachRightInnerCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .rInnerCarbonylC .rInnerResidue by
          decide).reachable
    have reachRightOuterGlycerol :
        pl1RR.covalentGraph.Reachable .centralC .rOuterGlycerolC :=
      reachRightStereo.trans
        (show pl1RR.covalentGraph.Adj .rStereoC .rOuterGlycerolC by
          decide).reachable
    have reachRightOuterEster :
        pl1RR.covalentGraph.Reachable .centralC .rOuterEsterO :=
      reachRightOuterGlycerol.trans
        (show pl1RR.covalentGraph.Adj .rOuterGlycerolC .rOuterEsterO by
          decide).reachable
    have reachRightOuterCarbonyl :
        pl1RR.covalentGraph.Reachable .centralC .rOuterCarbonylC :=
      reachRightOuterEster.trans
        (show pl1RR.covalentGraph.Adj .rOuterEsterO .rOuterCarbonylC by
          decide).reachable
    have reachRightOuterCarbonylO :
        pl1RR.covalentGraph.Reachable .centralC .rOuterCarbonylO :=
      reachRightOuterCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .rOuterCarbonylC .rOuterCarbonylO by
          decide).reachable
    have reachRightOuterResidue :
        pl1RR.covalentGraph.Reachable .centralC .rOuterResidue :=
      reachRightOuterCarbonyl.trans
        (show pl1RR.covalentGraph.Adj .rOuterCarbonylC .rOuterResidue by
          decide).reachable
    intro site
    cases site
    · exact reachLeftOuterResidue
    · exact reachLeftOuterCarbonyl
    · exact reachLeftOuterCarbonylO
    · exact reachLeftOuterEster
    · exact reachLeftOuterGlycerol
    · exact reachLeftStereo
    · exact reachLeftInnerEster
    · exact reachLeftInnerCarbonyl
    · exact reachLeftInnerCarbonylO
    · exact reachLeftInnerResidue
    · exact reachLeftPhosphateGlycerolC
    · exact reachLeftGlycerolPhosphateO
    · exact reachLeftPhosphorus
    · exact reachLeftPhosphoryl
    · exact reachLeftAcid
    · exact reachLeftBridge
    · exact reachCentralLeft
    · exact .rfl
    · exact reachCentralHydroxyl
    · exact reachCentralRight
    · exact reachRightBridge
    · exact reachRightPhosphorus
    · exact reachRightPhosphoryl
    · exact reachRightAcid
    · exact reachRightGlycerolPhosphateO
    · exact reachRightPhosphateGlycerolC
    · exact reachRightStereo
    · exact reachRightInnerEster
    · exact reachRightInnerCarbonyl
    · exact reachRightInnerCarbonylO
    · exact reachRightInnerResidue
    · exact reachRightOuterGlycerol
    · exact reachRightOuterEster
    · exact reachRightOuterCarbonyl
    · exact reachRightOuterCarbonylO
    · exact reachRightOuterResidue
  have edgeCard : pl1RR.covalentGraph.edgeFinset.card = 35 := by
    rw [pl1CovalentGraph_edgeFinset]
    change pl1CovalentEdgeList.toFinset.card = 35
    rw [List.toFinset_card_of_nodup pl1CovalentEdgeList_nodup]
    decide
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    pl1RR.covalentGraph.card_edgeSet, edgeCard]
  decide

/-! ## Output specifications -/

def PL1StructureSpec (molecule : MolecularStructure PL1Site) : Prop :=
  ValidMolecularStructure molecule ∧
  NoPeroxideBond molecule ∧
  ConnectedAcyclic molecule ∧
  TotalFormalCharge molecule = 0 ∧
  CountSkeletonNodes molecule (.atom .carbon) = 13 ∧
  CountSkeletonNodes molecule (.atom .oxygen) = 17 ∧
  CountSkeletonNodes molecule (.atom .phosphorus) = 2 ∧
  CountSkeletonNodes molecule .fattyAcidResidueR = 4 ∧
  TotalDisplayedAttachedHydrogens molecule = 18 ∧
  FragmentContractionMatchesSource molecule ∧
  ExactlyTerminalConfigurations molecule .R .R ∧
  StructureIsomorphicVia reflectPL1Equiv molecule molecule ∧
  IsEnantiomericPair molecule pl1SS ∧
  MirrorRelatedVia reflectPL1Equiv pl1RS pl1RS

def YStructureSpec (molecule : MolecularStructure PL1Site) : Prop :=
  ValidMolecularStructure molecule ∧
  NoPeroxideBond molecule ∧
  ConnectedAcyclic molecule ∧
  FirstDeprotonationAt pl1RR molecule .rAcidO ∧
  TotalFormalCharge molecule = -1 ∧
  CountSkeletonNodes molecule (.atom .carbon) = 13 ∧
  CountSkeletonNodes molecule (.atom .oxygen) = 17 ∧
  CountSkeletonNodes molecule (.atom .phosphorus) = 2 ∧
  CountSkeletonNodes molecule .fattyAcidResidueR = 4 ∧
  ExactlyTerminalConfigurations molecule .R .R ∧
  CooperativeHydrogenRelay molecule
    .lAcidO .centralHydroxylO .rAcidO ∧
  TwoHydrogenBondedRelayRingClosures molecule ∧
  molecule.hydrogenBonds.length = 2 ∧
  StructureIsomorphicVia reflectPL1Equiv molecule yLeftDeprotonated ∧
  SecondDeprotonationPenaltyPattern molecule

/-- Requested output `structure_pl1`. -/
def structurePL1 : MolecularStructure PL1Site := pl1RR

/-- Requested output `structure_y`. -/
def structureY : MolecularStructure PL1Site := yRightDeprotonated

/-- Problem-specific exact symbolic proposition for the first requested output. -/
def structurePL1Result : Prop := PL1StructureSpec structurePL1

/-- Problem-specific exact symbolic proposition for the second requested output. -/
def structureYResult : Prop := YStructureSpec structureY

/-- Raw exact symbolic result, preserving the controller's requested-output order. -/
def rawResult : Prop := structurePL1Result ∧ structureYResult

/-- Exact-symbolic reporting performs no numerical rounding. -/
def reportedResult : Prop :=
  PL1StructureSpec structurePL1 ∧ YStructureSpec structureY

private theorem structurePL1_valid : ValidMolecularStructure structurePL1 := by
  refine ⟨pl1NoSelfBonds, pl1UniqueCovalentPairs, ?_, ?_, ?_⟩
  · unfold ValencesSatisfied
    intro site
    cases site <;> decide
  · unfold AllDisplayedNodesRadicalFree
    intro site
    cases site <;> decide
  · simp [AllHydrogenBondsWellFormed, structurePL1, pl1RR,
      pl1WithConfigurations]

private theorem structurePL1_scalarFacts :
    TotalFormalCharge structurePL1 = 0 ∧
    CountSkeletonNodes structurePL1 (.atom .carbon) = 13 ∧
    CountSkeletonNodes structurePL1 (.atom .oxygen) = 17 ∧
    CountSkeletonNodes structurePL1 (.atom .phosphorus) = 2 ∧
    CountSkeletonNodes structurePL1 .fattyAcidResidueR = 4 ∧
    TotalDisplayedAttachedHydrogens structurePL1 = 18 := by
  decide

private theorem pl1CrossFragmentBond_iff_get
    (first second : PL1FragmentSite) :
    (∃ left right order,
      HasCovalentBond structurePL1 left right order ∧
      ((pl1FragmentOfSite left = first ∧
          pl1FragmentOfSite right = second) ∨
       (pl1FragmentOfSite left = second ∧
          pl1FragmentOfSite right = first))) ↔
    ∃ i : Fin structurePL1.covalentBonds.length,
      ((pl1FragmentOfSite (structurePL1.covalentBonds.get i).left = first ∧
          pl1FragmentOfSite (structurePL1.covalentBonds.get i).right = second) ∨
       (pl1FragmentOfSite (structurePL1.covalentBonds.get i).left = second ∧
          pl1FragmentOfSite (structurePL1.covalentBonds.get i).right = first)) := by
  constructor
  · rintro ⟨left, right, order, displayedBond, fragmentEndpoints⟩
    rw [hasCovalentBond_iff_get] at displayedBond
    rcases displayedBond with ⟨i, _, bondEndpoints⟩
    refine ⟨i, ?_⟩
    rcases bondEndpoints with direct | reversed
    · rcases fragmentEndpoints with fragmentDirect | fragmentReversed
      · exact Or.inl
          ⟨(congrArg pl1FragmentOfSite direct.1).trans fragmentDirect.1,
            (congrArg pl1FragmentOfSite direct.2).trans fragmentDirect.2⟩
      · exact Or.inr
          ⟨(congrArg pl1FragmentOfSite direct.1).trans fragmentReversed.1,
            (congrArg pl1FragmentOfSite direct.2).trans fragmentReversed.2⟩
    · rcases fragmentEndpoints with fragmentDirect | fragmentReversed
      · exact Or.inr
          ⟨(congrArg pl1FragmentOfSite reversed.1).trans fragmentDirect.2,
            (congrArg pl1FragmentOfSite reversed.2).trans fragmentDirect.1⟩
      · exact Or.inl
          ⟨(congrArg pl1FragmentOfSite reversed.1).trans fragmentReversed.2,
            (congrArg pl1FragmentOfSite reversed.2).trans fragmentReversed.1⟩
  · rintro ⟨i, fragmentEndpoints⟩
    let bond := structurePL1.covalentBonds.get i
    refine ⟨bond.left, bond.right, bond.order, ?_, ?_⟩
    · rw [hasCovalentBond_iff_get]
      exact ⟨i, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact fragmentEndpoints

-- This finite contraction audit normalizes two nested ten-site case splits.
set_option maxRecDepth 100000 in
private theorem structurePL1_fragmentContraction :
    FragmentContractionMatchesSource structurePL1 := by
  unfold FragmentContractionMatchesSource RealizesFragmentAdjacency
  intro first second
  rw [pl1CrossFragmentBond_iff_get first second]
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
private theorem structurePL1_terminalConfigurations :
    ExactlyTerminalConfigurations structurePL1 .R .R := by
  unfold ExactlyTerminalConfigurations TetrahedralCarbonConfiguration
  simp_rw [hasCovalentBond_iff_get]
  decide

private theorem structurePL1_reflectionIso :
    StructureIsomorphicVia reflectPL1Equiv structurePL1 structurePL1 := by
  unfold StructureIsomorphicVia
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · intro left right order
    change HasCovalentBond pl1RR (reflectPL1Site left)
        (reflectPL1Site right) order ↔
      HasCovalentBond pl1RR left right order
    exact pl1HasCovalentBond_reflection left right order
  · decide
  · intro donor hydrogenIndex acceptor
    simp [HasHydrogenBond, structurePL1, pl1RR, pl1WithConfigurations]

private theorem structurePL1_enantiomeric :
    IsEnantiomericPair structurePL1 pl1SS := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨reflectPL1Equiv, ?_⟩
    unfold MirrorRelatedVia
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · intro left right order
      change HasCovalentBond pl1RR (reflectPL1Site left)
          (reflectPL1Site right) order ↔
        HasCovalentBond pl1RR left right order
      exact pl1HasCovalentBond_reflection left right order
    · decide
    · intro donor hydrogenIndex acceptor
      simp [HasHydrogenBond, structurePL1, pl1RR, pl1SS,
        pl1WithConfigurations]
  · exact ⟨.lStereoC, .R, rfl⟩
  · rintro ⟨equivalence, isomorphic⟩
    have configurationAtLeft := isomorphic.2.2.1 .lStereoC
    have noSiteHasR (site : PL1Site) :
        pl1SS.configuration site ≠ some .R := by
      cases site <;> decide
    apply noSiteHasR (equivalence .lStereoC)
    simpa [structurePL1, pl1RR, pl1SS, pl1WithConfigurations,
      pl1Configuration] using configurationAtLeft

private theorem pl1RS_mirrorRelated :
    MirrorRelatedVia reflectPL1Equiv pl1RS pl1RS := by
  unfold MirrorRelatedVia
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · intro left right order
    change HasCovalentBond pl1RR (reflectPL1Site left)
        (reflectPL1Site right) order ↔
      HasCovalentBond pl1RR left right order
    exact pl1HasCovalentBond_reflection left right order
  · decide
  · intro donor hydrogenIndex acceptor
    simp [HasHydrogenBond, pl1RS, pl1WithConfigurations]

theorem structurePL1_satisfies_source : structurePL1Result := by
  unfold structurePL1Result PL1StructureSpec
  exact ⟨structurePL1_valid, pl1NoPeroxideBond,
    (by simpa [ConnectedAcyclic, structurePL1] using pl1CovalentGraph_isTree),
    structurePL1_scalarFacts.1,
    structurePL1_scalarFacts.2.1,
    structurePL1_scalarFacts.2.2.1,
    structurePL1_scalarFacts.2.2.2.1,
    structurePL1_scalarFacts.2.2.2.2.1,
    structurePL1_scalarFacts.2.2.2.2.2,
    structurePL1_fragmentContraction,
    structurePL1_terminalConfigurations,
    structurePL1_reflectionIso,
    structurePL1_enantiomeric,
    pl1RS_mirrorRelated⟩

private theorem structureY_valid : ValidMolecularStructure structureY := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [NoSelfBonds, structureY, yRightDeprotonated, structurePL1,
      pl1RR, pl1WithConfigurations] using pl1NoSelfBonds
  · simpa [UniqueCovalentPairs, structureY, yRightDeprotonated,
      structurePL1, pl1RR, pl1WithConfigurations] using pl1UniqueCovalentPairs
  · unfold ValencesSatisfied
    intro site
    cases site <;> decide
  · unfold AllDisplayedNodesRadicalFree
    intro site
    cases site <;> decide
  · simp [AllHydrogenBondsWellFormed, HydrogenBondWellFormed,
      structureY, yRightDeprotonated, yRightHydrogenBonds, yRightNode,
      pl1NeutralNode, displayedAtom, MolecularNode.element?,
      MolecularNode.displayedAttachedHydrogens]

private theorem structureY_noPeroxide : NoPeroxideBond structureY := by
  unfold NoPeroxideBond
  change ∀ bond ∈ pl1CovalentBonds,
    ¬ ((yRightNode bond.left).element? = some .oxygen ∧
      (yRightNode bond.right).element? = some .oxygen)
  rw [List.forall_mem_iff_get]
  decide

private theorem structureY_connectedAcyclic : ConnectedAcyclic structureY := by
  unfold ConnectedAcyclic
  have sameGraph : structureY.covalentGraph = pl1RR.covalentGraph := by
    ext first second
    rfl
  rw [sameGraph]
  exact pl1CovalentGraph_isTree

private theorem structureY_firstDeprotonation :
    FirstDeprotonationAt pl1RR structureY .rAcidO := by
  unfold FirstDeprotonationAt SameCovalentSkeletonVia
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro site
      cases site <;> rfl
    · intro left right order
      rfl
  · rfl
  · rfl
  · intro other different
    cases other <;> simp_all [structureY, yRightDeprotonated, yRightNode,
      pl1RR, pl1WithConfigurations]
  · rfl

private theorem structureY_scalarFacts :
    TotalFormalCharge structureY = -1 ∧
    CountSkeletonNodes structureY (.atom .carbon) = 13 ∧
    CountSkeletonNodes structureY (.atom .oxygen) = 17 ∧
    CountSkeletonNodes structureY (.atom .phosphorus) = 2 ∧
    CountSkeletonNodes structureY .fattyAcidResidueR = 4 := by
  decide

private theorem structureY_terminalConfigurations :
    ExactlyTerminalConfigurations structureY .R .R := by
  unfold ExactlyTerminalConfigurations TetrahedralCarbonConfiguration
  simp_rw [hasCovalentBond_iff_get]
  decide

private theorem structureY_relay :
    CooperativeHydrogenRelay structureY
      .lAcidO .centralHydroxylO .rAcidO := by
  simp [CooperativeHydrogenRelay, HasHydrogenBond, structureY,
    yRightDeprotonated, yRightHydrogenBonds, yRightNode, pl1NeutralNode]

private theorem structureY_ringClosures :
    TwoHydrogenBondedRelayRingClosures structureY := by
  unfold TwoHydrogenBondedRelayRingClosures
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [leftRelayCovalentPath, IsDisplayedCovalentPath]
    simp_rw [hasCovalentBond_iff_get]
    decide
  · simp only [rightRelayCovalentPath, IsDisplayedCovalentPath]
    simp_rw [hasCovalentBond_iff_get]
    decide
  · simp [HasHydrogenBond, structureY, yRightDeprotonated,
      yRightHydrogenBonds]
  · simp [HasHydrogenBond, structureY, yRightDeprotonated,
      yRightHydrogenBonds]

private theorem structureY_reflectionIso :
    StructureIsomorphicVia reflectPL1Equiv structureY yLeftDeprotonated := by
  unfold StructureIsomorphicVia
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro site
    cases site <;> decide
  · intro left right order
    change HasCovalentBond pl1RR (reflectPL1Site left)
        (reflectPL1Site right) order ↔
      HasCovalentBond pl1RR left right order
    exact pl1HasCovalentBond_reflection left right order
  · intro site
    cases site <;> decide
  · intro donor hydrogenIndex acceptor
    have rightHydrogenBond :
        HasHydrogenBond structureY donor hydrogenIndex acceptor ↔
          (donor = .lAcidO ∧ hydrogenIndex = 0 ∧
              acceptor = .centralHydroxylO) ∨
          (donor = .centralHydroxylO ∧ hydrogenIndex = 0 ∧
              acceptor = .rAcidO) := by
      simp [HasHydrogenBond, structureY, yRightDeprotonated,
        yRightHydrogenBonds]
      aesop
    have leftHydrogenBond :
        HasHydrogenBond yLeftDeprotonated (reflectPL1Equiv donor)
            hydrogenIndex (reflectPL1Equiv acceptor) ↔
          (reflectPL1Equiv donor = .rAcidO ∧ hydrogenIndex = 0 ∧
              reflectPL1Equiv acceptor = .centralHydroxylO) ∨
          (reflectPL1Equiv donor = .centralHydroxylO ∧
              hydrogenIndex = 0 ∧ reflectPL1Equiv acceptor = .lAcidO) := by
      simp [HasHydrogenBond, yLeftDeprotonated, yLeftHydrogenBonds]
      aesop
    rw [leftHydrogenBond, rightHydrogenBond]
    cases donor <;> cases acceptor <;>
      simp [reflectPL1Equiv, reflectPL1Site]

private theorem structureY_secondDeprotonationPenalty :
    SecondDeprotonationPenaltyPattern structureY := by
  unfold SecondDeprotonationPenaltyPattern
  intro dianion _ secondDeprotonation
  rcases secondDeprotonation with ⟨_, _, leftAnion, unchanged, _⟩
  have nodeAt (site : PL1Site) :
      dianion.node site =
        if site = .lAcidO then displayedAtom .oxygen 0 (-1)
        else structureY.node site := by
    by_cases atLeft : site = .lAcidO
    · subst site
      simpa using leftAnion
    · simpa [atLeft] using unchanged site atLeft
  have totalCharge : TotalFormalCharge dianion = -2 := by
    unfold TotalFormalCharge
    simp_rw [nodeAt]
    decide
  have rightAnion :
      dianion.node .rAcidO = displayedAtom .oxygen 0 (-1) := by
    have rightUnchanged := unchanged .rAcidO (by decide)
    simpa [structureY, yRightDeprotonated, yRightNode] using rightUnchanged
  refine ⟨totalCharge, leftAnion, rightAnion, by decide, ?_⟩
  intro relay
  have neutralLeft := relay.1
  rw [leftAnion] at neutralLeft
  have impossibleCharge := congrArg MolecularNode.formalCharge neutralLeft
  norm_num [displayedAtom, MolecularNode.formalCharge] at impossibleCharge

theorem structureY_satisfies_source : structureYResult := by
  unfold structureYResult YStructureSpec
  exact ⟨structureY_valid, structureY_noPeroxide,
    structureY_connectedAcyclic, structureY_firstDeprotonation,
    structureY_scalarFacts.1,
    structureY_scalarFacts.2.1,
    structureY_scalarFacts.2.2.1,
    structureY_scalarFacts.2.2.2.1,
    structureY_scalarFacts.2.2.2.2,
    structureY_terminalConfigurations, structureY_relay,
    structureY_ringClosures, (by decide), structureY_reflectionIso,
    structureY_secondDeprotonationPenalty⟩

theorem rawResult_valid : rawResult := by
  exact ⟨structurePL1_satisfies_source, structureY_satisfies_source⟩

theorem reportedResult_valid : reportedResult := by
  exact ⟨structurePL1_satisfies_source, structureY_satisfies_source⟩

/-- The formalization target for T5.2. -/
theorem problem_icho_2026_t5_a2 :
    PL1StructureSpec structurePL1 ∧ YStructureSpec structureY := by
  exact ⟨structurePL1_satisfies_source, structureY_satisfies_source⟩

end T5A2
end IChO2026Problems
