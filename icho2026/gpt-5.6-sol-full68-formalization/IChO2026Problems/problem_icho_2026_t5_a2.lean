import Mathlib

/-!
# IChO 2026 T5-A2: cardiolipin PL1 and its monoanion

This file is answer-blind: the two structures below are reconstructed from the
fragment inventory and the stereochemical/acidity information printed on
`T5_page-1.png` and `T5_page-2.png`.  In particular, no result from T5-A1 is
imported.  Its needed conclusion is derived again from the attachment ledger.

The molecular representation is deliberately local.  The configured libraries
provide finite graph theory but no atom-labelled molecular graph carrying bond
orders, charges, radicals, implicit hydrogen counts, hydrogen bonds, resonance,
and tetrahedral configurations simultaneously.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T5A2

/-! ## A small explicit molecular-structure language -/

/-- Elements and the problem-authorized abbreviation `R` for one hydrocarbon
fatty-acid residue.  `hydrocarbonResidueR` is a labelled substituent site, not an
assertion about the atoms hidden inside `R`. -/
inductive Element
  | H
  | C
  | O
  | P
  | hydrocarbonResidueR
  deriving DecidableEq, Repr

/-- Atom information needed to audit the skeletal drawings.  Hydrogens shown in
the stabilizing head group are explicit atoms; carbon-bound hydrogens omitted by
skeletal notation are counted in `implicitHydrogens`.  The count is deliberately
unknown for the abbreviated hydrocarbon residue `R`. -/
structure AtomData where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  implicitHydrogens : Option ℕ
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  deriving DecidableEq, Fintype, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2

structure CovalentBond (α : Type) where
  left : α
  right : α
  order : BondOrder
  deriving DecidableEq, Fintype, Repr

namespace CovalentBond

variable {α : Type}

/-- Orientation-free incidence of an explicitly stored covalent bond. -/
def Connects (bond : CovalentBond α) (a b : α) : Prop :=
  (bond.left = a ∧ bond.right = b) ∨ (bond.left = b ∧ bond.right = a)

theorem connects_comm (bond : CovalentBond α) (a b : α) :
    bond.Connects a b ↔ bond.Connects b a := by
  simp only [Connects]
  aesop

instance instDecidableConnects [DecidableEq α]
    (bond : CovalentBond α) (a b : α) : Decidable (bond.Connects a b) := by
  unfold Connects
  infer_instance

def Incident [DecidableEq α] (bond : CovalentBond α) (a : α) : Bool :=
  decide (bond.left = a ∨ bond.right = a)

def SameUndirected [DecidableEq α]
    (bond₁ bond₂ : CovalentBond α) : Prop :=
  bond₁.order = bond₂.order ∧ bond₁.Connects bond₂.left bond₂.right

instance instDecidableSameUndirected [DecidableEq α]
    (bond₁ bond₂ : CovalentBond α) :
    Decidable (bond₁.SameUndirected bond₂) := by
  unfold SameUndirected
  infer_instance

end CovalentBond

/-- A directed donor-H-acceptor description of a noncovalent hydrogen bond. -/
structure HydrogenBond (α : Type) where
  donorOxygen : α
  hydrogen : α
  acceptorOxygen : α
  deriving DecidableEq, Repr

/-- The two oxygens of one displayed phosphate resonance pair. -/
structure ResonanceDelocalization (α : Type) where
  phosphorus : α
  firstOxygen : α
  secondOxygen : α
  deriving DecidableEq, Repr

inductive AbsoluteConfiguration
  | R
  | S
  deriving DecidableEq, Repr

inductive StereoLigand (α : Type)
  | atom (site : α)
  | implicitHydrogen
  deriving DecidableEq, Repr

/-- An explicit tetrahedral stereocentre.  The four ligands are stored in CIP
priority order, followed by the absolute configuration. -/
structure TetrahedralCentre (α : Type) where
  centre : α
  priorityOne : StereoLigand α
  priorityTwo : StereoLigand α
  priorityThree : StereoLigand α
  priorityFour : StereoLigand α
  configuration : AbsoluteConfiguration
  deriving DecidableEq, Repr

/-- A molecular structure with covalent constitution separated from the
noncovalent interactions used to explain monoanion stabilization. -/
structure MolecularStructure (α : Type) [DecidableEq α] where
  presentAtoms : Finset α
  atomData : α → AtomData
  covalentBonds : List (CovalentBond α)
  stereocentres : List (TetrahedralCentre α)
  hydrogenBonds : List (HydrogenBond α)
  resonance : List (ResonanceDelocalization α)

namespace MolecularStructure

variable {α : Type} [DecidableEq α]

def HasBond (m : MolecularStructure α) (a b : α) (order : BondOrder) : Prop :=
  ∃ bond ∈ m.covalentBonds, bond.Connects a b ∧ bond.order = order

instance instDecidableHasBond (m : MolecularStructure α)
    (a b : α) (order : BondOrder) : Decidable (m.HasBond a b order) := by
  unfold HasBond
  exact List.decidableBEx _ _

def HasSingleBond (m : MolecularStructure α) (a b : α) : Prop :=
  m.HasBond a b .single

def HasDoubleBond (m : MolecularStructure α) (a b : α) : Prop :=
  m.HasBond a b .double

def AllPresent (m : MolecularStructure α) (sites : List α) : Prop :=
  ∀ site ∈ sites, site ∈ m.presentAtoms

def BondEndpointsPresent (m : MolecularStructure α) : Prop :=
  ∀ bond ∈ m.covalentBonds,
    bond.left ∈ m.presentAtoms ∧ bond.right ∈ m.presentAtoms

def NoSelfBonds (m : MolecularStructure α) : Prop :=
  ∀ bond ∈ m.covalentBonds, bond.left ≠ bond.right

def NoDuplicateUndirectedBonds (m : MolecularStructure α) : Prop :=
  m.covalentBonds.Pairwise fun bond₁ bond₂ =>
    ¬ bond₁.SameUndirected bond₂

/-- The simple graph underlying the covalent skeleton, restricted to atoms that
are present in this protonation state. -/
def covalentGraph (m : MolecularStructure α) :
    SimpleGraph {a // a ∈ m.presentAtoms} where
  Adj a b :=
    a ≠ b ∧ ∃ bond ∈ m.covalentBonds, bond.Connects a.1 b.1
  symm := ⟨by
    intro a b h
    rcases h with ⟨hne, bond, hmem, hconnects⟩
    exact ⟨hne.symm, bond, hmem,
      (bond.connects_comm a.1 b.1).mp hconnects⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

instance instDecidableCovalentGraphAdj (m : MolecularStructure α) :
    DecidableRel m.covalentGraph.Adj := by
  intro a b
  change Decidable
    (a ≠ b ∧ ∃ bond ∈ m.covalentBonds, bond.Connects a.1 b.1)
  letI : Decidable (∃ bond ∈ m.covalentBonds, bond.Connects a.1 b.1) :=
    List.decidableBEx _ _
  infer_instance

def elementCount (m : MolecularStructure α) (e : Element) : ℕ :=
  (m.presentAtoms.filter fun a => (m.atomData a).element = e).card

def totalFormalCharge (m : MolecularStructure α) : ℤ :=
  ∑ a ∈ m.presentAtoms, (m.atomData a).formalCharge

def incidentValence (m : MolecularStructure α) (a : α) : ℕ :=
  (m.covalentBonds.map fun bond =>
    if bond.Incident a then bond.order.valence else 0).sum +
    (m.atomData a).implicitHydrogens.getD 0

def expectedValence (data : AtomData) : ℕ :=
  match data.element with
  | .H => 1
  | .C => 4
  | .O => if data.formalCharge = -1 then 1 else 2
  | .P => 5
  | .hydrocarbonResidueR => 1

def ValencesCorrect (m : MolecularStructure α) : Prop :=
  ∀ a ∈ m.presentAtoms, m.incidentValence a = expectedValence (m.atomData a)

def NoRadicals (m : MolecularStructure α) : Prop :=
  ∀ a ∈ m.presentAtoms, (m.atomData a).radicalElectrons = 0

def NoPeroxideBond (m : MolecularStructure α) : Prop :=
  ∀ bond ∈ m.covalentBonds,
    ¬ ((m.atomData bond.left).element = .O ∧
       (m.atomData bond.right).element = .O)

def WellFormed (m : MolecularStructure α) : Prop :=
  m.BondEndpointsPresent ∧
  m.NoSelfBonds ∧
  m.NoDuplicateUndirectedBonds ∧
  m.ValencesCorrect ∧
  m.NoRadicals

end MolecularStructure

/-! ## Source fragment ledger and the previous-part prerequisite -/

/-- The four visually distinct building-block types on `T5_page-1.png`. -/
inductive FragmentKind
  | hydrogenCapA
  | phosphateB
  | glycerolC
  | acylD
  deriving DecidableEq, Repr

/-- Candidate-independent endpoint accounting for a connected acyclic assembly.

* `a` has one attachment end and occurs `n` times;
* each of the two `b` fragments has two attachment ends;
* each of the three `c` fragments has three attachment ends;
* each of the four `d` fragments has one attachment end.

Pairing all ends gives the first equation.  A connected acyclic fragment graph
is a tree, giving the second equation. -/
structure FragmentTreeLedger (n : ℕ) where
  assemblyBonds : ℕ
  allAttachmentEndsPaired :
    2 * assemblyBonds = n + 2 * 2 + 3 * 3 + 4
  connectedAcyclicEdgeCount :
    assemblyBonds + 1 = n + 2 + 3 + 4

/-- The source attachment ledger actually determines the number of type `a`
hydrogen caps, rather than merely its parity. -/
theorem source_fragment_tree_forces_one_hydrogen_cap
    (n : ℕ) (ledger : FragmentTreeLedger n) : n = 1 := by
  rcases ledger with ⟨assemblyBonds, hpaired, htree⟩
  omega

/-- T5-A1 is rederived inline: its correct parity branch is `n` odd. -/
theorem previous_part_hydrogen_cap_count_is_odd
    (n : ℕ) (ledger : FragmentTreeLedger n) : Odd n := by
  rw [source_fragment_tree_forces_one_hydrogen_cap n ledger]
  exact odd_one

/-! ## Atom sites reconstructed from the two source pages -/

inductive Arm
  | left
  | right
  deriving DecidableEq, Fintype, Repr

inductive GlycerolUnit
  | outer (arm : Arm)
  | bridge
  deriving DecidableEq, Fintype, Repr

inductive GlycerolPosition
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

inductive AcylPosition
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- Every explicitly drawn atom, plus four problem-authorized `R` residue
sites.  Carbon-bound hydrogens are represented by `AtomData.implicitHydrogens`.
-/
inductive CardiolipinSite
  | glycerolCarbon (unit : GlycerolUnit) (position : GlycerolPosition)
  | glycerolOxygen (unit : GlycerolUnit) (position : GlycerolPosition)
  | phosphorus (arm : Arm)
  | phosphorylOxygen (arm : Arm)
  | acidicOxygen (arm : Arm)
  | acidicHydrogen (arm : Arm)
  | bridgeHydroxylHydrogen
  | acylCarbonylCarbon (arm : Arm) (position : AcylPosition)
  | acylCarbonylOxygen (arm : Arm) (position : AcylPosition)
  | fattyResidueR (arm : Arm) (position : AcylPosition)
  deriving DecidableEq, Fintype, Repr

open CardiolipinSite

def bridgePosition : Arm → GlycerolPosition
  | .left => .one
  | .right => .three

def glycerolPositionOfAcyl : AcylPosition → GlycerolPosition
  | .one => .one
  | .two => .two

def neutralAtomData : CardiolipinSite → AtomData
  | .glycerolCarbon _ .one => ⟨.C, 0, 0, some 2⟩
  | .glycerolCarbon _ .two => ⟨.C, 0, 0, some 1⟩
  | .glycerolCarbon _ .three => ⟨.C, 0, 0, some 2⟩
  | .glycerolOxygen _ _ => ⟨.O, 0, 0, some 0⟩
  | .phosphorus _ => ⟨.P, 0, 0, some 0⟩
  | .phosphorylOxygen _ => ⟨.O, 0, 0, some 0⟩
  | .acidicOxygen _ => ⟨.O, 0, 0, some 0⟩
  | .acidicHydrogen _ => ⟨.H, 0, 0, some 0⟩
  | .bridgeHydroxylHydrogen => ⟨.H, 0, 0, some 0⟩
  | .acylCarbonylCarbon _ _ => ⟨.C, 0, 0, some 0⟩
  | .acylCarbonylOxygen _ _ => ⟨.O, 0, 0, some 0⟩
  | .fattyResidueR _ _ => ⟨.hydrocarbonResidueR, 0, 0, none⟩

def monoanionAtomData (site : CardiolipinSite) : AtomData :=
  if site = .acidicOxygen .left then
    { neutralAtomData site with formalCharge := -1 }
  else
    neutralAtomData site

def singleBond (a b : CardiolipinSite) : CovalentBond CardiolipinSite :=
  ⟨a, b, .single⟩

def doubleBond (a b : CardiolipinSite) : CovalentBond CardiolipinSite :=
  ⟨a, b, .double⟩

/-- Five internal bonds of one type-`c` glycerol fragment. -/
def glycerolFragmentBonds (unit : GlycerolUnit) :
    List (CovalentBond CardiolipinSite) :=
  [ singleBond (glycerolCarbon unit .one) (glycerolCarbon unit .two),
    singleBond (glycerolCarbon unit .two) (glycerolCarbon unit .three),
    singleBond (glycerolCarbon unit .one) (glycerolOxygen unit .one),
    singleBond (glycerolCarbon unit .two) (glycerolOxygen unit .two),
    singleBond (glycerolCarbon unit .three) (glycerolOxygen unit .three) ]

/-- The two internal P-O bonds of `b` and its two P-O assembly bonds to
glycerol oxygen endpoints. -/
def phosphateFragmentAndLinkageBonds (arm : Arm) :
    List (CovalentBond CardiolipinSite) :=
  [ doubleBond (phosphorus arm) (phosphorylOxygen arm),
    singleBond (phosphorus arm) (acidicOxygen arm),
    singleBond (phosphorus arm)
      (glycerolOxygen (.outer arm) .three),
    singleBond (phosphorus arm)
      (glycerolOxygen .bridge (bridgePosition arm)) ]

/-- One type-`d` acyl fragment `C(=O)-R` joined to a glycerol oxygen. -/
def acylFragmentAndEsterBonds (arm : Arm) (position : AcylPosition) :
    List (CovalentBond CardiolipinSite) :=
  [ singleBond
      (glycerolOxygen (.outer arm) (glycerolPositionOfAcyl position))
      (acylCarbonylCarbon arm position),
    doubleBond (acylCarbonylCarbon arm position)
      (acylCarbonylOxygen arm position),
    singleBond (acylCarbonylCarbon arm position)
      (fattyResidueR arm position) ]

/-- All covalent bonds common to neutral PL1 and monoanion Y, except the two
acidic O-H bonds. -/
def cardiolipinCoreBonds : List (CovalentBond CardiolipinSite) :=
  glycerolFragmentBonds (.outer .left) ++
  glycerolFragmentBonds .bridge ++
  glycerolFragmentBonds (.outer .right) ++
  phosphateFragmentAndLinkageBonds .left ++
  phosphateFragmentAndLinkageBonds .right ++
  acylFragmentAndEsterBonds .left .one ++
  acylFragmentAndEsterBonds .left .two ++
  acylFragmentAndEsterBonds .right .one ++
  acylFragmentAndEsterBonds .right .two ++
  [singleBond (glycerolOxygen .bridge .two) bridgeHydroxylHydrogen]

def neutralPL1Bonds : List (CovalentBond CardiolipinSite) :=
  cardiolipinCoreBonds ++
  [ singleBond (acidicOxygen .left) (acidicHydrogen .left),
    singleBond (acidicOxygen .right) (acidicHydrogen .right) ]

def monoanionYBonds : List (CovalentBond CardiolipinSite) :=
  cardiolipinCoreBonds ++
  [singleBond (acidicOxygen .right) (acidicHydrogen .right)]

/-- CIP order at either outer glycerol centre is O-acyl, CH2-O-P,
CH2-O-acyl, H. -/
def outerGlycerolCentre (arm : Arm) (configuration : AbsoluteConfiguration) :
    TetrahedralCentre CardiolipinSite where
  centre := glycerolCarbon (.outer arm) .two
  priorityOne := .atom (glycerolOxygen (.outer arm) .two)
  priorityTwo := .atom (glycerolCarbon (.outer arm) .three)
  priorityThree := .atom (glycerolCarbon (.outer arm) .one)
  priorityFour := .implicitHydrogen
  configuration := configuration

def homochiralRRStereochemistry : List (TetrahedralCentre CardiolipinSite) :=
  [outerGlycerolCentre .left .R, outerGlycerolCentre .right .R]

def homochiralSSStereochemistry : List (TetrahedralCentre CardiolipinSite) :=
  [outerGlycerolCentre .left .S, outerGlycerolCentre .right .S]

/-- One requested enantiomer of neutral PL1. -/
def pl1Enantiomer : MolecularStructure CardiolipinSite where
  presentAtoms := Finset.univ
  atomData := neutralAtomData
  covalentBonds := neutralPL1Bonds
  stereocentres := homochiralRRStereochemistry
  hydrogenBonds := []
  resonance := []

/-- The constitutionally identical mirror of the submitted PL1 enantiomer. -/
def pl1MirrorEnantiomer : MolecularStructure CardiolipinSite where
  presentAtoms := Finset.univ
  atomData := neutralAtomData
  covalentBonds := neutralPL1Bonds
  stereocentres := homochiralSSStereochemistry
  hydrogenBonds := []
  resonance := []

/-- The central OH donates to the deprotonated left phosphate. -/
def centralOHToAnionicPhosphate : HydrogenBond CardiolipinSite where
  donorOxygen := glycerolOxygen .bridge .two
  hydrogen := bridgeHydroxylHydrogen
  acceptorOxygen := acidicOxygen .left

/-- The remaining right P-OH donates back to the central glycerol oxygen. -/
def protonatedPhosphateToCentralO : HydrogenBond CardiolipinSite where
  donorOxygen := acidicOxygen .right
  hydrogen := acidicHydrogen .right
  acceptorOxygen := glycerolOxygen .bridge .two

def anionicLeftPhosphateResonance : ResonanceDelocalization CardiolipinSite where
  phosphorus := phosphorus .left
  firstOxygen := acidicOxygen .left
  secondOxygen := phosphorylOxygen .left

/-- Monoanion Y in the hydrogen-bonded conformation that displays why removal
of its remaining acidic proton is disfavoured. -/
def monoanionY : MolecularStructure CardiolipinSite where
  presentAtoms := (Finset.univ : Finset CardiolipinSite).erase
    (acidicHydrogen .left)
  atomData := monoanionAtomData
  covalentBonds := monoanionYBonds
  stereocentres := homochiralRRStereochemistry
  hydrogenBonds :=
    [centralOHToAnionicPhosphate, protonatedPhosphateToCentralO]
  resonance := [anionicLeftPhosphateResonance]

/-! ## Source-to-structure specifications -/

def IsGlycerolFragment
    (m : MolecularStructure CardiolipinSite) (unit : GlycerolUnit) : Prop :=
  m.AllPresent
      [ glycerolCarbon unit .one, glycerolCarbon unit .two,
        glycerolCarbon unit .three, glycerolOxygen unit .one,
        glycerolOxygen unit .two, glycerolOxygen unit .three ] ∧
  m.HasSingleBond (glycerolCarbon unit .one) (glycerolCarbon unit .two) ∧
  m.HasSingleBond (glycerolCarbon unit .two) (glycerolCarbon unit .three) ∧
  m.HasSingleBond (glycerolCarbon unit .one) (glycerolOxygen unit .one) ∧
  m.HasSingleBond (glycerolCarbon unit .two) (glycerolOxygen unit .two) ∧
  m.HasSingleBond (glycerolCarbon unit .three) (glycerolOxygen unit .three)

def IsPhosphateCore
    (m : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  m.AllPresent [phosphorus arm, phosphorylOxygen arm, acidicOxygen arm] ∧
  m.HasDoubleBond (phosphorus arm) (phosphorylOxygen arm) ∧
  m.HasSingleBond (phosphorus arm) (acidicOxygen arm)

def IsPhosphodiesterLinkage
    (m : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  m.HasSingleBond (phosphorus arm)
      (glycerolOxygen (.outer arm) .three) ∧
  m.HasSingleBond (phosphorus arm)
      (glycerolOxygen .bridge (bridgePosition arm))

def IsProtonatedAcidicGroup
    (m : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  acidicHydrogen arm ∈ m.presentAtoms ∧
  (m.atomData (acidicOxygen arm)).formalCharge = 0 ∧
  m.HasSingleBond (acidicOxygen arm) (acidicHydrogen arm)

def IsDeprotonatedAcidicGroup
    (m : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  acidicHydrogen arm ∉ m.presentAtoms ∧
  (m.atomData (acidicOxygen arm)).formalCharge = -1

def IsAcylResidue
    (m : MolecularStructure CardiolipinSite)
    (arm : Arm) (position : AcylPosition) : Prop :=
  m.AllPresent
      [ acylCarbonylCarbon arm position, acylCarbonylOxygen arm position,
        fattyResidueR arm position ] ∧
  m.HasSingleBond
      (glycerolOxygen (.outer arm) (glycerolPositionOfAcyl position))
      (acylCarbonylCarbon arm position) ∧
  m.HasDoubleBond (acylCarbonylCarbon arm position)
      (acylCarbonylOxygen arm position) ∧
  m.HasSingleBond (acylCarbonylCarbon arm position)
      (fattyResidueR arm position)

def HasCentralHydroxylHydrogenCap
    (m : MolecularStructure CardiolipinSite) : Prop :=
  bridgeHydroxylHydrogen ∈ m.presentAtoms ∧
  m.HasSingleBond (glycerolOxygen .bridge .two) bridgeHydroxylHydrogen

def HasFourIdenticalResiduesAbbreviatedR
    (m : MolecularStructure CardiolipinSite) : Prop :=
  m.elementCount .hydrocarbonResidueR = 4 ∧
  ∀ arm position,
    (m.atomData (fattyResidueR arm position)).element =
      .hydrocarbonResidueR

def HasTwoConstitutionallyIdenticalAcidicGroups
    (m : MolecularStructure CardiolipinSite) : Prop :=
  (m.atomData (acidicOxygen .left)).element = .O ∧
  (m.atomData (acidicOxygen .right)).element = .O ∧
  IsPhosphateCore m .left ∧ IsPhosphateCore m .right ∧
  IsPhosphodiesterLinkage m .left ∧ IsPhosphodiesterLinkage m .right

def HomochiralOuterGlycerols
    (m : MolecularStructure CardiolipinSite) : Prop :=
  m.stereocentres = homochiralRRStereochemistry ∨
  m.stereocentres = homochiralSSStereochemistry

def NoPhosphorusStereocentre
    (m : MolecularStructure CardiolipinSite) : Prop :=
  ∀ centre ∈ m.stereocentres,
    ∀ arm, centre.centre ≠ phosphorus arm

/-- All exact finite counts in neutral PL1.  Together with the fragment-pattern
predicates and the tree condition, these exclude extra atoms and extra bonds. -/
def NeutralPL1Inventory
    (m : MolecularStructure CardiolipinSite) : Prop :=
  m.presentAtoms.card = 39 ∧
  m.covalentBonds.length = 38 ∧
  m.elementCount .C = 13 ∧
  m.elementCount .O = 17 ∧
  m.elementCount .P = 2 ∧
  m.elementCount .H = 3 ∧
  m.elementCount .hydrocarbonResidueR = 4

def PL1SourceSpecification
    (m : MolecularStructure CardiolipinSite) : Prop :=
  m.WellFormed ∧
  m.covalentGraph.IsTree ∧
  m.NoPeroxideBond ∧
  m.totalFormalCharge = 0 ∧
  NeutralPL1Inventory m ∧
  (∀ unit, IsGlycerolFragment m unit) ∧
  (∀ arm, IsPhosphateCore m arm ∧ IsPhosphodiesterLinkage m arm ∧
    IsProtonatedAcidicGroup m arm) ∧
  (∀ arm position, IsAcylResidue m arm position) ∧
  HasCentralHydroxylHydrogenCap m ∧
  HasFourIdenticalResiduesAbbreviatedR m ∧
  HasTwoConstitutionallyIdenticalAcidicGroups m ∧
  HomochiralOuterGlycerols m ∧
  NoPhosphorusStereocentre m

def flipConfiguration : AbsoluteConfiguration → AbsoluteConfiguration
  | .R => .S
  | .S => .R

def flipCentre (centre : TetrahedralCentre CardiolipinSite) :
    TetrahedralCentre CardiolipinSite :=
  { centre with configuration := flipConfiguration centre.configuration }

/-- A non-string stereochemical comparison: same labelled constitution and
opposite configuration at every explicitly represented stereocentre. -/
def AreEnantiomers
    (m₁ m₂ : MolecularStructure CardiolipinSite) : Prop :=
  m₁.presentAtoms = m₂.presentAtoms ∧
  m₁.atomData = m₂.atomData ∧
  m₁.covalentBonds = m₂.covalentBonds ∧
  m₁.stereocentres ≠ [] ∧
  m₂.stereocentres = m₁.stereocentres.map flipCentre

def IsDeprotonationAt
    (acid monoanion : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  monoanion.presentAtoms = acid.presentAtoms.erase (acidicHydrogen arm) ∧
  monoanion.covalentBonds =
    (acid.covalentBonds.filter fun bond =>
      !bond.Incident (acidicHydrogen arm)) ∧
  (monoanion.atomData (acidicOxygen arm)).formalCharge =
    (acid.atomData (acidicOxygen arm)).formalCharge - 1 ∧
  (∀ site, site ≠ acidicOxygen arm →
    monoanion.atomData site = acid.atomData site) ∧
  monoanion.stereocentres = acid.stereocentres

/-- The removed proton can be on either of the constitutionally equivalent
phosphate groups; no branch is inserted as a premise. -/
def IsFirstDeprotonationProduct
    (acid monoanion : MolecularStructure CardiolipinSite) : Prop :=
  ∃ arm, IsDeprotonationAt acid monoanion arm

def IsIntramolecularHydrogenBond
    (m : MolecularStructure CardiolipinSite)
    (hbond : HydrogenBond CardiolipinSite) : Prop :=
  m.AllPresent [hbond.donorOxygen, hbond.hydrogen, hbond.acceptorOxygen] ∧
  (m.atomData hbond.donorOxygen).element = .O ∧
  (m.atomData hbond.hydrogen).element = .H ∧
  (m.atomData hbond.acceptorOxygen).element = .O ∧
  hbond.donorOxygen ≠ hbond.acceptorOxygen ∧
  m.HasSingleBond hbond.donorOxygen hbond.hydrogen

/-- The hydrogen bond closes a ring because its donor and acceptor are already
joined by a covalent path. -/
def HydrogenBondClosesRing
    (m : MolecularStructure CardiolipinSite)
    (hbond : HydrogenBond CardiolipinSite) : Prop :=
  ∃ (hd : hbond.donorOxygen ∈ m.presentAtoms)
    (ha : hbond.acceptorOxygen ∈ m.presentAtoms),
    m.covalentGraph.Reachable
      ⟨hbond.donorOxygen, hd⟩ ⟨hbond.acceptorOxygen, ha⟩

def HasAnionicPhosphateResonance
    (m : MolecularStructure CardiolipinSite) (arm : Arm) : Prop :=
  (m.atomData (acidicOxygen arm)).formalCharge = -1 ∧
  ⟨phosphorus arm, acidicOxygen arm, phosphorylOxygen arm⟩ ∈ m.resonance

/-- The two explicitly directed hydrogen bonds make the classical bicyclic
head-group motif: central OH -> anionic phosphate and protonated phosphate OH
-> central O.  The remaining acidic proton is itself a hydrogen-bond donor. -/
def HasCyclicMonoanionStabilization
    (m : MolecularStructure CardiolipinSite) : Prop :=
  ∃ deprotonated protonated : Arm,
    deprotonated ≠ protonated ∧
    IsDeprotonatedAcidicGroup m deprotonated ∧
    IsProtonatedAcidicGroup m protonated ∧
    let centralToAnion : HydrogenBond CardiolipinSite :=
      ⟨glycerolOxygen .bridge .two, bridgeHydroxylHydrogen,
        acidicOxygen deprotonated⟩
    let acidToCentral : HydrogenBond CardiolipinSite :=
      ⟨acidicOxygen protonated, acidicHydrogen protonated,
        glycerolOxygen .bridge .two⟩
    centralToAnion ∈ m.hydrogenBonds ∧
    acidToCentral ∈ m.hydrogenBonds ∧
    m.hydrogenBonds.length = 2 ∧
    IsIntramolecularHydrogenBond m centralToAnion ∧
    IsIntramolecularHydrogenBond m acidToCentral ∧
    HydrogenBondClosesRing m centralToAnion ∧
    HydrogenBondClosesRing m acidToCentral ∧
    HasAnionicPhosphateResonance m deprotonated

def MonoanionYInventory
    (m : MolecularStructure CardiolipinSite) : Prop :=
  m.presentAtoms.card = 38 ∧
  m.covalentBonds.length = 37 ∧
  m.elementCount .C = 13 ∧
  m.elementCount .O = 17 ∧
  m.elementCount .P = 2 ∧
  m.elementCount .H = 2 ∧
  m.elementCount .hydrocarbonResidueR = 4

def YSourceSpecification
    (neutral monoanion : MolecularStructure CardiolipinSite) : Prop :=
  monoanion.WellFormed ∧
  monoanion.covalentGraph.IsTree ∧
  monoanion.NoPeroxideBond ∧
  monoanion.totalFormalCharge = -1 ∧
  MonoanionYInventory monoanion ∧
  IsFirstDeprotonationProduct neutral monoanion ∧
  (∀ unit, IsGlycerolFragment monoanion unit) ∧
  (∀ arm, IsPhosphateCore monoanion arm ∧
    IsPhosphodiesterLinkage monoanion arm) ∧
  (∀ arm position, IsAcylResidue monoanion arm position) ∧
  HasCentralHydroxylHydrogenCap monoanion ∧
  HasFourIdenticalResiduesAbbreviatedR monoanion ∧
  monoanion.stereocentres = neutral.stereocentres ∧
  NoPhosphorusStereocentre monoanion ∧
  HasCyclicMonoanionStabilization monoanion

/-! ## Requested output carriers -/

/-- Exact graph-and-stereochemistry carrier for requested output
`structure_pl1`. -/
def StructurePL1Output : Prop :=
  PL1SourceSpecification pl1Enantiomer ∧
  PL1SourceSpecification pl1MirrorEnantiomer ∧
  AreEnantiomers pl1Enantiomer pl1MirrorEnantiomer

/-- Exact graph, charge, resonance, and hydrogen-bond carrier for requested
output `structure_y`. -/
def StructureYOutput : Prop :=
  YSourceSpecification pl1Enantiomer monoanionY

/-- The raw symbolic solve contract includes the independently rederived
fragment count as well as both requested molecular outputs. -/
def RawResult : Prop :=
  (∀ n, FragmentTreeLedger n → n = 1) ∧
  StructurePL1Output ∧
  StructureYOutput

/-- Exact-symbolic reporting performs no numerical rounding; both graph
carriers are retained verbatim. -/
def ReportedResult : Prop :=
  StructurePL1Output ∧ StructureYOutput

attribute [local instance] Fintype.decidableForallFintype
attribute [local instance] Fintype.decidableExistsFintype

/-! A rooted spanning-tree certificate for the two concrete covalent graphs.
Every non-root atom is assigned an adjacent parent closer to the central
glycerol carbon.  The numeric depth is proof infrastructure only; adjacency is
still checked against the source-derived bond lists. -/

private def cardiolipinRoot : CardiolipinSite :=
  glycerolCarbon .bridge .two

private def cardiolipinParent : CardiolipinSite → Option CardiolipinSite
  | glycerolCarbon .bridge .one => some cardiolipinRoot
  | glycerolCarbon .bridge .two => none
  | glycerolCarbon .bridge .three => some cardiolipinRoot
  | glycerolCarbon (.outer arm) .one =>
      some (glycerolCarbon (.outer arm) .two)
  | glycerolCarbon (.outer arm) .two =>
      some (glycerolCarbon (.outer arm) .three)
  | glycerolCarbon (.outer arm) .three =>
      some (glycerolOxygen (.outer arm) .three)
  | glycerolOxygen .bridge .one =>
      some (glycerolCarbon .bridge .one)
  | glycerolOxygen .bridge .two => some cardiolipinRoot
  | glycerolOxygen .bridge .three =>
      some (glycerolCarbon .bridge .three)
  | glycerolOxygen (.outer arm) .one =>
      some (glycerolCarbon (.outer arm) .one)
  | glycerolOxygen (.outer arm) .two =>
      some (glycerolCarbon (.outer arm) .two)
  | glycerolOxygen (.outer arm) .three => some (phosphorus arm)
  | phosphorus arm =>
      some (glycerolOxygen .bridge (bridgePosition arm))
  | phosphorylOxygen arm => some (phosphorus arm)
  | acidicOxygen arm => some (phosphorus arm)
  | acidicHydrogen arm => some (acidicOxygen arm)
  | bridgeHydroxylHydrogen =>
      some (glycerolOxygen .bridge .two)
  | acylCarbonylCarbon arm position =>
      some (glycerolOxygen (.outer arm)
        (glycerolPositionOfAcyl position))
  | acylCarbonylOxygen arm position =>
      some (acylCarbonylCarbon arm position)
  | fattyResidueR arm position =>
      some (acylCarbonylCarbon arm position)

private def cardiolipinDepth : CardiolipinSite → ℕ
  | glycerolCarbon .bridge .one => 1
  | glycerolCarbon .bridge .two => 0
  | glycerolCarbon .bridge .three => 1
  | glycerolCarbon (.outer _) .one => 7
  | glycerolCarbon (.outer _) .two => 6
  | glycerolCarbon (.outer _) .three => 5
  | glycerolOxygen .bridge .one => 2
  | glycerolOxygen .bridge .two => 1
  | glycerolOxygen .bridge .three => 2
  | glycerolOxygen (.outer _) .one => 8
  | glycerolOxygen (.outer _) .two => 7
  | glycerolOxygen (.outer _) .three => 4
  | phosphorus _ => 3
  | phosphorylOxygen _ => 4
  | acidicOxygen _ => 4
  | acidicHydrogen _ => 5
  | bridgeHydroxylHydrogen => 2
  | acylCarbonylCarbon _ .one => 9
  | acylCarbonylCarbon _ .two => 8
  | acylCarbonylOxygen _ .one => 10
  | acylCarbonylOxygen _ .two => 9
  | fattyResidueR _ .one => 10
  | fattyResidueR _ .two => 9

private theorem cardiolipinParent_exists_unless_root :
    ∀ site, site ≠ cardiolipinRoot →
      ∃ parent, cardiolipinParent site = some parent := by
  native_decide

private theorem cardiolipinParent_decreases :
    ∀ site parent, cardiolipinParent site = some parent →
      cardiolipinDepth parent < cardiolipinDepth site := by
  native_decide

private theorem cardiolipinParent_bond_neutral :
    ∀ site parent, cardiolipinParent site = some parent →
      ∃ bond ∈ neutralPL1Bonds, bond.Connects site parent := by
  native_decide

private def neutralVertex (site : CardiolipinSite) :
    {a // a ∈ pl1Enantiomer.presentAtoms} :=
  ⟨site, by simp [pl1Enantiomer]⟩

private theorem pl1Enantiomer_reachable_root (site : CardiolipinSite) :
    pl1Enantiomer.covalentGraph.Reachable
      (neutralVertex site) (neutralVertex cardiolipinRoot) := by
  by_cases hroot : site = cardiolipinRoot
  · subst site
    exact .rfl
  · obtain ⟨parent, hparent⟩ :=
      cardiolipinParent_exists_unless_root site hroot
    have hdepth := cardiolipinParent_decreases site parent hparent
    have hadj : pl1Enantiomer.covalentGraph.Adj
        (neutralVertex site) (neutralVertex parent) := by
      change neutralVertex site ≠ neutralVertex parent ∧
        ∃ bond ∈ neutralPL1Bonds, bond.Connects site parent
      constructor
      · intro heq
        have : site = parent := congrArg Subtype.val heq
        subst parent
        exact (Nat.lt_irrefl _ hdepth)
      · exact cardiolipinParent_bond_neutral site parent hparent
    exact hadj.reachable.trans (pl1Enantiomer_reachable_root parent)
termination_by cardiolipinDepth site
decreasing_by exact hdepth

private theorem pl1Enantiomer_connected :
    pl1Enantiomer.covalentGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨neutralVertex cardiolipinRoot, ?_⟩
  intro site
  exact (pl1Enantiomer_reachable_root site.1).symm

private theorem pl1Enantiomer_wellFormed : pl1Enantiomer.WellFormed := by
  unfold MolecularStructure.WellFormed
    MolecularStructure.BondEndpointsPresent MolecularStructure.NoSelfBonds
    MolecularStructure.NoDuplicateUndirectedBonds MolecularStructure.ValencesCorrect
    MolecularStructure.NoRadicals
  refine ⟨by native_decide, by native_decide, ?_, by native_decide, by native_decide⟩
  unfold CovalentBond.SameUndirected CovalentBond.Connects
  native_decide

private theorem pl1Enantiomer_inventory : NeutralPL1Inventory pl1Enantiomer := by
  unfold NeutralPL1Inventory
  native_decide

private theorem pl1Enantiomer_isTree : pl1Enantiomer.covalentGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact pl1Enantiomer_connected
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card]
    native_decide

private theorem pl1Enantiomer_sourceSpecification :
    PL1SourceSpecification pl1Enantiomer := by
  unfold PL1SourceSpecification
  refine ⟨pl1Enantiomer_wellFormed, pl1Enantiomer_isTree, ?_, ?_,
    pl1Enantiomer_inventory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold MolecularStructure.NoPeroxideBond
    native_decide
  · native_decide
  · unfold IsGlycerolFragment MolecularStructure.AllPresent
      MolecularStructure.HasSingleBond MolecularStructure.HasBond
    native_decide
  · unfold IsPhosphateCore IsPhosphodiesterLinkage
      IsProtonatedAcidicGroup MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond
    native_decide
  · unfold IsAcylResidue MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond
    native_decide
  · unfold HasCentralHydroxylHydrogenCap
      MolecularStructure.HasSingleBond MolecularStructure.HasBond
    native_decide
  · unfold HasFourIdenticalResiduesAbbreviatedR
    native_decide
  · unfold HasTwoConstitutionallyIdenticalAcidicGroups IsPhosphateCore
      IsPhosphodiesterLinkage MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond
    native_decide
  · unfold HomochiralOuterGlycerols
    exact Or.inl rfl
  · simp [NoPhosphorusStereocentre, pl1Enantiomer,
      homochiralRRStereochemistry, outerGlycerolCentre]

private theorem pl1_enantiomer_pair :
    AreEnantiomers pl1Enantiomer pl1MirrorEnantiomer := by
  unfold AreEnantiomers
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp [pl1Enantiomer, homochiralRRStereochemistry]
  · rfl

private theorem pl1MirrorEnantiomer_sourceSpecification :
    PL1SourceSpecification pl1MirrorEnantiomer := by
  rcases pl1Enantiomer_sourceSpecification with
    ⟨hwell, htree, hperoxide, hcharge, hinventory, hglycerols,
      hphosphates, hacyls, hcap, hresidues, hacids, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold MolecularStructure.WellFormed
      MolecularStructure.BondEndpointsPresent MolecularStructure.NoSelfBonds
      MolecularStructure.NoDuplicateUndirectedBonds MolecularStructure.ValencesCorrect
      MolecularStructure.NoRadicals MolecularStructure.incidentValence at hwell ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hwell
  · unfold MolecularStructure.covalentGraph at htree ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using htree
  · unfold MolecularStructure.NoPeroxideBond at hperoxide ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hperoxide
  · unfold MolecularStructure.totalFormalCharge at hcharge ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hcharge
  · unfold NeutralPL1Inventory MolecularStructure.elementCount at hinventory ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hinventory
  · unfold IsGlycerolFragment MolecularStructure.AllPresent
      MolecularStructure.HasSingleBond MolecularStructure.HasBond at hglycerols ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hglycerols
  · unfold IsPhosphateCore IsPhosphodiesterLinkage
      IsProtonatedAcidicGroup MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond at hphosphates ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hphosphates
  · unfold IsAcylResidue MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond at hacyls ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hacyls
  · unfold HasCentralHydroxylHydrogenCap MolecularStructure.HasSingleBond
      MolecularStructure.HasBond at hcap ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hcap
  · unfold HasFourIdenticalResiduesAbbreviatedR
      MolecularStructure.elementCount at hresidues ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hresidues
  · unfold HasTwoConstitutionallyIdenticalAcidicGroups IsPhosphateCore
      IsPhosphodiesterLinkage MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond at hacids ⊢
    simpa [pl1Enantiomer, pl1MirrorEnantiomer] using hacids
  · exact Or.inr rfl
  · simp [NoPhosphorusStereocentre, pl1MirrorEnantiomer,
      homochiralSSStereochemistry, outerGlycerolCentre]

private theorem cardiolipinParent_preserves_monoanion_sites :
    ∀ site parent,
      site ≠ acidicHydrogen .left →
      cardiolipinParent site = some parent →
      parent ≠ acidicHydrogen .left := by
  native_decide

private theorem cardiolipinParent_bond_monoanion :
    ∀ site parent,
      site ≠ acidicHydrogen .left →
      cardiolipinParent site = some parent →
      ∃ bond ∈ monoanionYBonds, bond.Connects site parent := by
  native_decide

private def monoanionVertex
    (site : CardiolipinSite) (hsite : site ≠ acidicHydrogen .left) :
    {a // a ∈ monoanionY.presentAtoms} :=
  ⟨site, by simpa [monoanionY] using hsite⟩

private theorem monoanionY_reachable_root
    (site : CardiolipinSite) (hsite : site ≠ acidicHydrogen .left) :
    monoanionY.covalentGraph.Reachable
      (monoanionVertex site hsite)
      (monoanionVertex cardiolipinRoot (by decide)) := by
  by_cases hroot : site = cardiolipinRoot
  · subst site
    exact .rfl
  · obtain ⟨parent, hparent⟩ :=
      cardiolipinParent_exists_unless_root site hroot
    have hparentSite :=
      cardiolipinParent_preserves_monoanion_sites site parent hsite hparent
    have hdepth := cardiolipinParent_decreases site parent hparent
    have hadj : monoanionY.covalentGraph.Adj
        (monoanionVertex site hsite)
        (monoanionVertex parent hparentSite) := by
      change monoanionVertex site hsite ≠ monoanionVertex parent hparentSite ∧
        ∃ bond ∈ monoanionYBonds, bond.Connects site parent
      constructor
      · intro heq
        have : site = parent := congrArg Subtype.val heq
        subst parent
        exact (Nat.lt_irrefl _ hdepth)
      · exact cardiolipinParent_bond_monoanion site parent hsite hparent
    exact hadj.reachable.trans (monoanionY_reachable_root parent hparentSite)
termination_by cardiolipinDepth site
decreasing_by exact hdepth

private theorem monoanionY_reachable
    (a b : CardiolipinSite)
    (ha : a ∈ monoanionY.presentAtoms)
    (hb : b ∈ monoanionY.presentAtoms) :
    monoanionY.covalentGraph.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hna : a ≠ acidicHydrogen .left := by
    simpa [monoanionY] using ha
  have hnb : b ≠ acidicHydrogen .left := by
    simpa [monoanionY] using hb
  have hreach := (monoanionY_reachable_root a hna).trans
    (monoanionY_reachable_root b hnb).symm
  simpa only [monoanionVertex] using hreach

private theorem monoanionY_connected : monoanionY.covalentGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  let hroot : cardiolipinRoot ∈ monoanionY.presentAtoms := by
    simp [monoanionY, cardiolipinRoot]
  refine ⟨⟨cardiolipinRoot, hroot⟩, ?_⟩
  intro site
  exact monoanionY_reachable cardiolipinRoot site.1 hroot site.2

private theorem monoanionY_wellFormed : monoanionY.WellFormed := by
  unfold MolecularStructure.WellFormed
    MolecularStructure.BondEndpointsPresent MolecularStructure.NoSelfBonds
    MolecularStructure.NoDuplicateUndirectedBonds MolecularStructure.ValencesCorrect
    MolecularStructure.NoRadicals
  refine ⟨by native_decide, by native_decide, ?_, by native_decide, by native_decide⟩
  unfold CovalentBond.SameUndirected CovalentBond.Connects
  native_decide

private theorem monoanionY_inventory : MonoanionYInventory monoanionY := by
  unfold MonoanionYInventory
  native_decide

private theorem monoanionY_isTree : monoanionY.covalentGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact monoanionY_connected
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card]
    native_decide

private theorem monoanionY_hydrogenBondClosesRing
    (hbond : HydrogenBond CardiolipinSite)
    (hdonor : hbond.donorOxygen ∈ monoanionY.presentAtoms)
    (hacceptor : hbond.acceptorOxygen ∈ monoanionY.presentAtoms) :
    HydrogenBondClosesRing monoanionY hbond :=
  ⟨hdonor, hacceptor,
    monoanionY_reachable hbond.donorOxygen hbond.acceptorOxygen
      hdonor hacceptor⟩

private theorem monoanionY_isFirstDeprotonationProduct :
    IsFirstDeprotonationProduct pl1Enantiomer monoanionY := by
  unfold IsFirstDeprotonationProduct
  refine ⟨.left, ?_⟩
  unfold IsDeprotonationAt
  native_decide

private theorem monoanionY_hasCyclicStabilization :
    HasCyclicMonoanionStabilization monoanionY := by
  unfold HasCyclicMonoanionStabilization
  refine ⟨.left, .right, by decide, ?_, ?_, ?_⟩
  · unfold IsDeprotonatedAcidicGroup
    native_decide
  · unfold IsProtonatedAcidicGroup MolecularStructure.HasSingleBond
      MolecularStructure.HasBond
    native_decide
  · dsimp
    refine ⟨by native_decide, by native_decide, by native_decide,
      ?_, ?_, ?_, ?_, ?_⟩
    · unfold IsIntramolecularHydrogenBond MolecularStructure.AllPresent
        MolecularStructure.HasSingleBond MolecularStructure.HasBond
      native_decide
    · unfold IsIntramolecularHydrogenBond MolecularStructure.AllPresent
        MolecularStructure.HasSingleBond MolecularStructure.HasBond
      native_decide
    · apply monoanionY_hydrogenBondClosesRing <;> native_decide
    · apply monoanionY_hydrogenBondClosesRing <;> native_decide
    · unfold HasAnionicPhosphateResonance
      native_decide

private theorem monoanionY_sourceSpecification :
    YSourceSpecification pl1Enantiomer monoanionY := by
  unfold YSourceSpecification
  refine ⟨monoanionY_wellFormed, monoanionY_isTree, ?_, ?_,
    monoanionY_inventory, monoanionY_isFirstDeprotonationProduct,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, monoanionY_hasCyclicStabilization⟩
  · unfold MolecularStructure.NoPeroxideBond
    native_decide
  · native_decide
  · unfold IsGlycerolFragment MolecularStructure.AllPresent
      MolecularStructure.HasSingleBond MolecularStructure.HasBond
    native_decide
  · unfold IsPhosphateCore IsPhosphodiesterLinkage
      MolecularStructure.AllPresent MolecularStructure.HasDoubleBond
      MolecularStructure.HasSingleBond MolecularStructure.HasBond
    native_decide
  · unfold IsAcylResidue MolecularStructure.AllPresent
      MolecularStructure.HasDoubleBond MolecularStructure.HasSingleBond
      MolecularStructure.HasBond
    native_decide
  · unfold HasCentralHydroxylHydrogenCap
      MolecularStructure.HasSingleBond MolecularStructure.HasBond
    native_decide
  · unfold HasFourIdenticalResiduesAbbreviatedR
    native_decide
  · rfl
  · simp [NoPhosphorusStereocentre, monoanionY,
      homochiralRRStereochemistry, outerGlycerolCentre]

theorem structure_pl1 : StructurePL1Output := by
  unfold StructurePL1Output
  exact ⟨pl1Enantiomer_sourceSpecification,
    pl1MirrorEnantiomer_sourceSpecification, pl1_enantiomer_pair⟩

theorem structure_y : StructureYOutput := by
  exact monoanionY_sourceSpecification

theorem raw_result : RawResult := by
  exact ⟨source_fragment_tree_forces_one_hydrogen_cap, structure_pl1, structure_y⟩

theorem reported_result : ReportedResult := by
  exact ⟨structure_pl1, structure_y⟩

end ProblemIcho2026T5A2
end IChO2026Problems
