import Mathlib
import IChO2026Chem.Core

/-!
# IChO 2026, theory problem 3, part 4

The problem asks for drawings, so the answer carriers below are finite labelled
chemical graphs rather than names or strings.  Hydrogen atoms are represented
by their exact multiplicity on each heavy atom.  A boundary bond is not an
internal bond: it records one bond crossed by a dashed repeat-unit edge.

The source figures give one tritopic black building block and one ditopic red
building block in both reaction schemes.  As in the printed hexagonal-1
topology, a repeat unit therefore contains one complete black core and three
halves of red linkers.  Each linker half has two cut aromatic bonds, for six
boundary bonds in total.
-/

namespace IChO2026Problems.Icho2026T3A4

inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

inductive Element where
  | H | C | N | O
  deriving DecidableEq, Repr

inductive AtomStereochemistry where
  | notStereogenic
  | unspecified
  | R
  | S
  deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr

inductive BondStereochemistry where
  | notApplicable
  | unspecified
  | E
  | Z
  deriving DecidableEq, Repr

/-- An atom label contains all non-connectivity information required by the
question.  `attachedHydrogens` is an exact count, not an unspecified implicit
valence. -/
structure AtomLabel where
  element : Element
  isotope : Option ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  stereochemistry : AtomStereochemistry
  deriving DecidableEq, Repr

def neutralAtom (element : Element) (attachedHydrogens : ℕ) : AtomLabel :=
  { element := element
    isotope := none
    formalCharge := 0
    radicalElectrons := 0
    attachedHydrogens := attachedHydrogens
    stereochemistry := .notStereogenic }

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def MolecularFormula.scale (n : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := n * a.carbon
    hydrogen := n * a.hydrogen
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen }

def waterFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 2, nitrogen := 0, oxygen := 1 }

def sixHydrogenAtomsFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 6, nitrogen := 0, oxygen := 0 }

/-- Componentwise material balance.  It does not assert a yield or that the
listed fragments are the only macroscopic reaction products. -/
def FormulaBalance
    (input removed output : MolecularFormula) : Prop :=
  input.carbon = output.carbon + removed.carbon ∧
  input.hydrogen = output.hydrogen + removed.hydrogen ∧
  input.nitrogen = output.nitrogen + removed.nitrogen ∧
  input.oxygen = output.oxygen + removed.oxygen

inductive Arm where
  | north
  | southWest
  | southEast
  deriving DecidableEq, Fintype, Repr

def allArms : List Arm := [.north, .southWest, .southEast]

inductive CorePosition where
  | p0 | p1 | p2 | p3 | p4 | p5
  deriving DecidableEq, Fintype, Repr

/-- `ipso` bears N.  `hydroxySide` bears O in the COF-3/4 linker;
`otherSide` bears H.  The latter two positions are the atoms immediately on
the inside of the two dashed cuts. -/
inductive LinkerPosition where
  | ipso
  | hydroxySide
  | otherSide
  deriving DecidableEq, Fintype, Repr

inductive UnitVertex where
  | core (position : CorePosition)
  | bridgeCarbon (arm : Arm)
  | bridgeNitrogen (arm : Arm)
  | linkerCarbon (arm : Arm) (position : LinkerPosition)
  | oxygen (arm : Arm)
  deriving DecidableEq, Fintype, Repr

def armAnchor : Arm → CorePosition
  | .north => .p0
  | .southWest => .p2
  | .southEast => .p4

def adjacentCoreHydroxyl : Arm → CorePosition
  | .north => .p1
  | .southWest => .p3
  | .southEast => .p5

def isArmAnchor : CorePosition → Bool
  | .p0 | .p2 | .p4 => true
  | .p1 | .p3 | .p5 => false

structure Bond where
  left : UnitVertex
  right : UnitVertex
  order : BondOrder
  stereochemistry : BondStereochemistry
  deriving DecidableEq, Repr

def bondStereoForOrder : BondOrder → BondStereochemistry
  | .double => .unspecified
  | _ => .notApplicable

def mkBond (left right : UnitVertex) (order : BondOrder) : Bond :=
  { left := left
    right := right
    order := order
    stereochemistry := bondStereoForOrder order }

inductive BoundarySide where
  | hydroxySide
  | otherSide
  deriving DecidableEq, Fintype, Repr

/-- A bond crossed by a dashed boundary line.  The outside atom belongs to the
complementary half of the same ditopic arene in a neighbouring repeat unit. -/
structure BoundaryBond where
  arm : Arm
  side : BoundarySide
  inside : UnitVertex
  outsidePosition : LinkerPosition
  outsideAtom : AtomLabel
  order : BondOrder
  stereochemistry : BondStereochemistry
  provenance : Provenance
  deriving DecidableEq, Repr

inductive Topology where
  | hexagonalOne
  deriving DecidableEq, Repr

structure RepeatUnit where
  atom : UnitVertex → AtomLabel
  internalBonds : List Bond
  boundaryBonds : List BoundaryBond
  topology : Topology

def sameUndirectedEndpoints (a b : Bond) : Prop :=
  (a.left = b.left ∧ a.right = b.right) ∨
  (a.left = b.right ∧ a.right = b.left)

def HasBond
    (u : RepeatUnit) (x y : UnitVertex) (order : BondOrder) : Prop :=
  ∃ b ∈ u.internalBonds,
    sameUndirectedEndpoints b (mkBond x y order) ∧ b.order = order

def Adjacent (u : RepeatUnit) (x y : UnitVertex) : Prop :=
  ∃ order, HasBond u x y order

def InternallyConnected (u : RepeatUnit) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adjacent u) x y

def NoSelfBonds (u : RepeatUnit) : Prop :=
  ∀ b ∈ u.internalBonds, b.left ≠ b.right

def NoRepeatedInternalBonds (u : RepeatUnit) : Prop :=
  ∀ b₁ ∈ u.internalBonds, ∀ b₂ ∈ u.internalBonds,
    sameUndirectedEndpoints b₁ b₂ → b₁.order = b₂.order → b₁ = b₂

def NeutralClosedShellNoAssignedStereocentres (u : RepeatUnit) : Prop :=
  (∀ v,
    (u.atom v).formalCharge = 0 ∧
    (u.atom v).radicalElectrons = 0 ∧
    (u.atom v).stereochemistry = .notStereogenic) ∧
  ∀ b ∈ u.internalBonds,
    b.stereochemistry = bondStereoForOrder b.order

def bondValenceUnits : BondOrder → ℕ
  | .single => 2
  | .double => 4
  | .triple => 6
  | .aromatic => 3

def ordinaryValenceUnits : Element → ℕ
  | .H => 2
  | .C => 8
  | .N => 6
  | .O => 4

def internalValenceAt (u : RepeatUnit) (v : UnitVertex) : ℕ :=
  (u.internalBonds.map fun b =>
    if b.left = v ∨ b.right = v then bondValenceUnits b.order else 0).sum

def boundaryValenceAt (u : RepeatUnit) (v : UnitVertex) : ℕ :=
  (u.boundaryBonds.map fun b =>
    if b.inside = v then bondValenceUnits b.order else 0).sum

/-- Bond order is doubled so that an aromatic bond contributes three units. -/
def OrdinaryValenceSatisfied (u : RepeatUnit) : Prop :=
  ∀ v,
    internalValenceAt u v + boundaryValenceAt u v +
        2 * (u.atom v).attachedHydrogens =
      ordinaryValenceUnits (u.atom v).element

def elementCount (u : RepeatUnit) (element : Element) : ℕ :=
  (Finset.univ.filter fun v : UnitVertex => (u.atom v).element = element).card

def unitFormula (u : RepeatUnit) : MolecularFormula :=
  { carbon := elementCount u .C
    hydrogen := ∑ v : UnitVertex, (u.atom v).attachedHydrogens
    nitrogen := elementCount u .N
    oxygen := elementCount u .O }

/-! ## Source-side molecular inventory -/

inductive RingSubstituent where
  | aldehyde
  | amine
  | hydroxyl
  | hydrogen
  deriving DecidableEq, Repr

structure SourceMonomer where
  name : String
  sixMemberedRingPattern : List RingSubstituent
  formula : MolecularFormula
  condensationSites : ℕ
  provenance : Provenance
  imagePath : String
  deriving DecidableEq, Repr

/-- The black reactant in the COF-3 scheme: benzene-1,3,5-tricarbaldehyde. -/
def cof34BlackMonomer : SourceMonomer :=
  { name := "benzene-1,3,5-tricarbaldehyde"
    sixMemberedRingPattern :=
      [.aldehyde, .hydrogen, .aldehyde, .hydrogen, .aldehyde, .hydrogen]
    formula := { carbon := 9, hydrogen := 6, nitrogen := 0, oxygen := 3 }
    condensationSites := 3
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

/-- The red reactant in the COF-3 scheme: 2,5-diaminobenzene-1,4-diol. -/
def cof34RedMonomer : SourceMonomer :=
  { name := "2,5-diaminobenzene-1,4-diol"
    sixMemberedRingPattern :=
      [.amine, .hydroxyl, .hydrogen, .amine, .hydroxyl, .hydrogen]
    formula := { carbon := 6, hydrogen := 8, nitrogen := 2, oxygen := 2 }
    condensationSites := 2
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

/-- The black reactant in the COF-5 scheme: the alternating trialdehyde/triol
ring commonly named 1,3,5-triformylphloroglucinol. -/
def cof56BlackMonomer : SourceMonomer :=
  { name := "2,4,6-trihydroxybenzene-1,3,5-tricarbaldehyde"
    sixMemberedRingPattern :=
      [.aldehyde, .hydroxyl, .aldehyde, .hydroxyl, .aldehyde, .hydroxyl]
    formula := { carbon := 9, hydrogen := 6, nitrogen := 0, oxygen := 6 }
    condensationSites := 3
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

/-- The red reactant in the COF-5 scheme: benzene-1,4-diamine. -/
def cof56RedMonomer : SourceMonomer :=
  { name := "benzene-1,4-diamine"
    sixMemberedRingPattern :=
      [.amine, .hydrogen, .hydrogen, .amine, .hydrogen, .hydrogen]
    formula := { carbon := 6, hydrogen := 8, nitrogen := 2, oxygen := 0 }
    condensationSites := 2
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

/-- One half of the red COF-3/4 linker before condensation.  Three copies are
selected by the dashed-boundary convention. -/
def cof34RedHalfBeforeCondensation : MolecularFormula :=
  { carbon := 3, hydrogen := 4, nitrogen := 1, oxygen := 1 }

/-- One half of the red COF-5/6 linker before condensation. -/
def cof56RedHalfBeforeCondensation : MolecularFormula :=
  { carbon := 3, hydrogen := 4, nitrogen := 1, oxygen := 0 }

inductive COFName where
  | cof3 | cof4 | cof5 | cof6
  deriving DecidableEq, Repr

inductive ArrowKind where
  | reversibleCondensation
  | oxidation
  | irreversibleIsomerization
  deriving DecidableEq, Repr

structure SchemeArrow where
  source : Option COFName
  target : COFName
  kind : ArrowKind
  reagentLabel : Option String
  provenance : Provenance
  imagePath : String
  deriving DecidableEq, Repr

def cof3FormationArrow : SchemeArrow :=
  { source := none
    target := .cof3
    kind := .reversibleCondensation
    reagentLabel := none
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

def cof3ToCof4Arrow : SchemeArrow :=
  { source := some .cof3
    target := .cof4
    kind := .oxidation
    reagentLabel := some "[O]"
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

def cof5FormationArrow : SchemeArrow :=
  { source := none
    target := .cof5
    kind := .reversibleCondensation
    reagentLabel := none
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-4.png" }

def cof5ToCof6Arrow : SchemeArrow :=
  { source := some .cof5
    target := .cof6
    kind := .irreversibleIsomerization
    reagentLabel := none
    provenance := .problemText
    imagePath := "icho_2026_source/image/T3_page-4.png" }

inductive IRStatus where
  | present
  | absent
  deriving DecidableEq, Repr

structure IRObservation where
  sample : COFName
  imineStretch : IRStatus
  provenance : Provenance
  locator : String
  deriving DecidableEq, Repr

def cof3IRObservation : IRObservation :=
  { sample := .cof3
    imineStretch := .present
    provenance := .problemText
    locator := "paragraph above the reaction schemes on T3_page-4.png" }

def cof4IRObservation : IRObservation :=
  { sample := .cof4
    imineStretch := .absent
    provenance := .problemText
    locator := "paragraph above the reaction schemes on T3_page-4.png" }

def cof6IRObservation : IRObservation :=
  { sample := .cof6
    imineStretch := .absent
    provenance := .problemText
    locator := "paragraph above the reaction schemes on T3_page-4.png" }

structure ElementalChangeObservation where
  source : COFName
  target : COFName
  carbonChange : ℤ
  hydrogenChange : ℤ
  nitrogenChange : ℤ
  oxygenChange : ℤ
  provenance : Provenance
  locator : String
  deriving DecidableEq, Repr

/-- The signed change is target minus source. -/
def cof3ToCof4ElementalChange : ElementalChangeObservation :=
  { source := .cof3
    target := .cof4
    carbonChange := 0
    hydrogenChange := -6
    nitrogenChange := 0
    oxygenChange := 0
    provenance := .problemText
    locator := "loss of six additional hydrogen atoms per repeat unit as the only change" }

/-! ## The previous-part topology fact, derived again from the bound figures -/

structure PrintedTopologyExample where
  firstBlockDegree : ℕ
  secondBlockDegree : ℕ
  topology : Topology
  provenance : Provenance
  imagePath : String
  deriving DecidableEq, Repr

/-- The filled A2 + B3 cell on page 4 and the page-3 monomer drawings give a
degree-two/degree-three example of hexagonal topology 1. -/
def a3PrintedHexagonalOneExample : PrintedTopologyExample :=
  { firstBlockDegree := 2
    secondBlockDegree := 3
    topology := .hexagonalOne
    provenance := .problemImage
    imagePath := "icho_2026_source/image/T3_page-3.png; icho_2026_source/image/T3_page-4.png" }

def DegreeTwoThreePair (first second : ℕ) : Prop :=
  (first = 2 ∧ second = 3) ∨ (first = 3 ∧ second = 2)

def PreviousPartNeededConclusion : Prop :=
  a3PrintedHexagonalOneExample.topology = .hexagonalOne ∧
  DegreeTwoThreePair
    a3PrintedHexagonalOneExample.firstBlockDegree
    a3PrintedHexagonalOneExample.secondBlockDegree ∧
  DegreeTwoThreePair cof34BlackMonomer.condensationSites cof34RedMonomer.condensationSites ∧
  DegreeTwoThreePair cof56BlackMonomer.condensationSites cof56RedMonomer.condensationSites

theorem previousPartNeededConclusion_derived : PreviousPartNeededConclusion := by
  simp [PreviousPartNeededConclusion, DegreeTwoThreePair,
    a3PrintedHexagonalOneExample, cof34BlackMonomer, cof34RedMonomer,
    cof56BlackMonomer, cof56RedMonomer]

/-! ## Exact atom tables -/

def cof3Atom : UnitVertex → AtomLabel
  | .core p => neutralAtom .C (if isArmAnchor p then 0 else 1)
  | .bridgeCarbon _ => neutralAtom .C 1
  | .bridgeNitrogen _ => neutralAtom .N 0
  | .linkerCarbon _ .ipso => neutralAtom .C 0
  | .linkerCarbon _ .hydroxySide => neutralAtom .C 0
  | .linkerCarbon _ .otherSide => neutralAtom .C 1
  | .oxygen _ => neutralAtom .O 1

def cof4Atom : UnitVertex → AtomLabel
  | .core p => neutralAtom .C (if isArmAnchor p then 0 else 1)
  | .bridgeCarbon _ => neutralAtom .C 0
  | .bridgeNitrogen _ => neutralAtom .N 0
  | .linkerCarbon _ .ipso => neutralAtom .C 0
  | .linkerCarbon _ .hydroxySide => neutralAtom .C 0
  | .linkerCarbon _ .otherSide => neutralAtom .C 1
  | .oxygen _ => neutralAtom .O 0

def cof5Atom : UnitVertex → AtomLabel
  | .core _ => neutralAtom .C 0
  | .bridgeCarbon _ => neutralAtom .C 1
  | .bridgeNitrogen _ => neutralAtom .N 0
  | .linkerCarbon _ .ipso => neutralAtom .C 0
  | .linkerCarbon _ .hydroxySide => neutralAtom .C 1
  | .linkerCarbon _ .otherSide => neutralAtom .C 1
  | .oxygen _ => neutralAtom .O 1

def cof6Atom : UnitVertex → AtomLabel
  | .core _ => neutralAtom .C 0
  | .bridgeCarbon _ => neutralAtom .C 1
  | .bridgeNitrogen _ => neutralAtom .N 1
  | .linkerCarbon _ .ipso => neutralAtom .C 0
  | .linkerCarbon _ .hydroxySide => neutralAtom .C 1
  | .linkerCarbon _ .otherSide => neutralAtom .C 1
  | .oxygen _ => neutralAtom .O 0

/-! ## Exact internal and dashed-boundary bonds -/

def aromaticCoreBonds : List Bond :=
  [ mkBond (.core .p0) (.core .p1) .aromatic
  , mkBond (.core .p1) (.core .p2) .aromatic
  , mkBond (.core .p2) (.core .p3) .aromatic
  , mkBond (.core .p3) (.core .p4) .aromatic
  , mkBond (.core .p4) (.core .p5) .aromatic
  , mkBond (.core .p5) (.core .p0) .aromatic ]

def singleCoreBonds : List Bond :=
  [ mkBond (.core .p0) (.core .p1) .single
  , mkBond (.core .p1) (.core .p2) .single
  , mkBond (.core .p2) (.core .p3) .single
  , mkBond (.core .p3) (.core .p4) .single
  , mkBond (.core .p4) (.core .p5) .single
  , mkBond (.core .p5) (.core .p0) .single ]

def cof3ArmBonds (arm : Arm) : List Bond :=
  [ mkBond (.core (armAnchor arm)) (.bridgeCarbon arm) .single
  , mkBond (.bridgeCarbon arm) (.bridgeNitrogen arm) .double
  , mkBond (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) .single
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .hydroxySide) .aromatic
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .otherSide) .aromatic
  , mkBond (.linkerCarbon arm .hydroxySide) (.oxygen arm) .single ]

def cof3InternalBonds : List Bond :=
  aromaticCoreBonds ++ allArms.flatMap cof3ArmBonds

def oxidativeRingClosureBonds : List Bond :=
  allArms.map fun arm =>
    mkBond (.bridgeCarbon arm) (.oxygen arm) .single

def cof4InternalBonds : List Bond :=
  cof3InternalBonds ++ oxidativeRingClosureBonds

def cof5ArmBonds (arm : Arm) : List Bond :=
  [ mkBond (.core (armAnchor arm)) (.bridgeCarbon arm) .single
  , mkBond (.bridgeCarbon arm) (.bridgeNitrogen arm) .double
  , mkBond (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) .single
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .hydroxySide) .aromatic
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .otherSide) .aromatic
  , mkBond (.core (adjacentCoreHydroxyl arm)) (.oxygen arm) .single ]

def cof5InternalBonds : List Bond :=
  aromaticCoreBonds ++ allArms.flatMap cof5ArmBonds

def cof6ArmBonds (arm : Arm) : List Bond :=
  [ mkBond (.core (armAnchor arm)) (.bridgeCarbon arm) .double
  , mkBond (.bridgeCarbon arm) (.bridgeNitrogen arm) .single
  , mkBond (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) .single
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .hydroxySide) .aromatic
  , mkBond (.linkerCarbon arm .ipso) (.linkerCarbon arm .otherSide) .aromatic
  , mkBond (.core (adjacentCoreHydroxyl arm)) (.oxygen arm) .double ]

def cof6InternalBonds : List Bond :=
  singleCoreBonds ++ allArms.flatMap cof6ArmBonds

def cof34BoundaryForArm (arm : Arm) : List BoundaryBond :=
  [ { arm := arm
      side := .hydroxySide
      inside := .linkerCarbon arm .hydroxySide
      outsidePosition := .otherSide
      outsideAtom := neutralAtom .C 1
      order := .aromatic
      stereochemistry := .notApplicable
      provenance := .problemImage }
  , { arm := arm
      side := .otherSide
      inside := .linkerCarbon arm .otherSide
      outsidePosition := .hydroxySide
      outsideAtom := neutralAtom .C 0
      order := .aromatic
      stereochemistry := .notApplicable
      provenance := .problemImage } ]

def cof56BoundaryForArm (arm : Arm) : List BoundaryBond :=
  [ { arm := arm
      side := .hydroxySide
      inside := .linkerCarbon arm .hydroxySide
      outsidePosition := .otherSide
      outsideAtom := neutralAtom .C 1
      order := .aromatic
      stereochemistry := .notApplicable
      provenance := .problemImage }
  , { arm := arm
      side := .otherSide
      inside := .linkerCarbon arm .otherSide
      outsidePosition := .hydroxySide
      outsideAtom := neutralAtom .C 1
      order := .aromatic
      stereochemistry := .notApplicable
      provenance := .problemImage } ]

def cof34BoundaryBonds : List BoundaryBond :=
  allArms.flatMap cof34BoundaryForArm

def cof56BoundaryBonds : List BoundaryBond :=
  allArms.flatMap cof56BoundaryForArm

def cof3RepeatUnit : RepeatUnit :=
  { atom := cof3Atom
    internalBonds := cof3InternalBonds
    boundaryBonds := cof34BoundaryBonds
    topology := .hexagonalOne }

def cof4RepeatUnit : RepeatUnit :=
  { atom := cof4Atom
    internalBonds := cof4InternalBonds
    boundaryBonds := cof34BoundaryBonds
    topology := .hexagonalOne }

def cof5RepeatUnit : RepeatUnit :=
  { atom := cof5Atom
    internalBonds := cof5InternalBonds
    boundaryBonds := cof56BoundaryBonds
    topology := .hexagonalOne }

def cof6RepeatUnit : RepeatUnit :=
  { atom := cof6Atom
    internalBonds := cof6InternalBonds
    boundaryBonds := cof56BoundaryBonds
    topology := .hexagonalOne }

/-! The following graph lemmas turn the displayed bond lists into explicit
paths.  They avoid assuming any generic chemical connectivity rule: every
edge used below is checked against the corresponding concrete bond list. -/

private theorem adjacent_of_internalBond
    {u : RepeatUnit} {x y : UnitVertex} {order : BondOrder}
    (h : mkBond x y order ∈ u.internalBonds) : Adjacent u x y := by
  refine ⟨order, mkBond x y order, h, ?_, rfl⟩
  exact Or.inl ⟨rfl, rfl⟩

private theorem hasBond_symm
    {u : RepeatUnit} {x y : UnitVertex} {order : BondOrder}
    (h : HasBond u x y order) : HasBond u y x order := by
  rcases h with ⟨b, hb, hendpoints, horder⟩
  refine ⟨b, hb, ?_, horder⟩
  simpa [sameUndirectedEndpoints, mkBond, or_comm] using hendpoints

private theorem adjacent_symm
    {u : RepeatUnit} {x y : UnitVertex} (h : Adjacent u x y) : Adjacent u y x := by
  rcases h with ⟨order, hbond⟩
  exact ⟨order, hasBond_symm hbond⟩

private theorem internallyConnected_of_root
    (u : RepeatUnit) (root : UnitVertex)
    (hroot : ∀ v, Relation.ReflTransGen (Adjacent u) root v) :
    InternallyConnected u := by
  intro x y
  letI : Std.Symm (Adjacent u) := ⟨fun _ _ h => adjacent_symm h⟩
  exact (symm (hroot x)).trans (hroot y)

private theorem coreRootReaches_of_cycle
    (u : RepeatUnit)
    (h01 : Adjacent u (.core .p0) (.core .p1))
    (h12 : Adjacent u (.core .p1) (.core .p2))
    (h23 : Adjacent u (.core .p2) (.core .p3))
    (h34 : Adjacent u (.core .p3) (.core .p4))
    (_h45 : Adjacent u (.core .p4) (.core .p5))
    (h50 : Adjacent u (.core .p5) (.core .p0)) :
    ∀ p, Relation.ReflTransGen (Adjacent u) (.core .p0) (.core p)
  | .p0 => .refl
  | .p1 => Relation.ReflTransGen.single h01
  | .p2 => (Relation.ReflTransGen.single h01).tail h12
  | .p3 => ((Relation.ReflTransGen.single h01).tail h12).tail h23
  | .p4 => (((Relation.ReflTransGen.single h01).tail h12).tail h23).tail h34
  | .p5 => Relation.ReflTransGen.single (adjacent_symm h50)

private theorem rootReaches_of_skeleton
    (u : RepeatUnit)
    (hCore : ∀ p, Relation.ReflTransGen (Adjacent u) (.core .p0) (.core p))
    (hAnchorBridge : ∀ arm,
      Adjacent u (.core (armAnchor arm)) (.bridgeCarbon arm))
    (hBridgeCN : ∀ arm,
      Adjacent u (.bridgeCarbon arm) (.bridgeNitrogen arm))
    (hNitrogenIpso : ∀ arm,
      Adjacent u (.bridgeNitrogen arm) (.linkerCarbon arm .ipso))
    (hIpsoHydroxy : ∀ arm,
      Adjacent u (.linkerCarbon arm .ipso) (.linkerCarbon arm .hydroxySide))
    (hIpsoOther : ∀ arm,
      Adjacent u (.linkerCarbon arm .ipso) (.linkerCarbon arm .otherSide))
    (hOxygen : ∀ arm,
      Relation.ReflTransGen (Adjacent u) (.core .p0) (.oxygen arm)) :
    ∀ v, Relation.ReflTransGen (Adjacent u) (.core .p0) v
  | .core p => hCore p
  | .bridgeCarbon arm =>
      (hCore (armAnchor arm)).tail (hAnchorBridge arm)
  | .bridgeNitrogen arm =>
      ((hCore (armAnchor arm)).tail (hAnchorBridge arm)).tail (hBridgeCN arm)
  | .linkerCarbon arm .ipso =>
      (((hCore (armAnchor arm)).tail (hAnchorBridge arm)).tail (hBridgeCN arm)).tail
        (hNitrogenIpso arm)
  | .linkerCarbon arm .hydroxySide =>
      ((((hCore (armAnchor arm)).tail (hAnchorBridge arm)).tail (hBridgeCN arm)).tail
        (hNitrogenIpso arm)).tail (hIpsoHydroxy arm)
  | .linkerCarbon arm .otherSide =>
      ((((hCore (armAnchor arm)).tail (hAnchorBridge arm)).tail (hBridgeCN arm)).tail
        (hNitrogenIpso arm)).tail (hIpsoOther arm)
  | .oxygen arm => hOxygen arm

private theorem cof3_rootReaches (v : UnitVertex) :
    Relation.ReflTransGen (Adjacent cof3RepeatUnit) (.core .p0) v := by
  have hCore : ∀ p,
      Relation.ReflTransGen (Adjacent cof3RepeatUnit) (.core .p0) (.core p) :=
    coreRootReaches_of_cycle cof3RepeatUnit
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof3RepeatUnit, cof3InternalBonds,
        aromaticCoreBonds])
  have hAnchorBridge : ∀ arm,
      Adjacent cof3RepeatUnit (.core (armAnchor arm)) (.bridgeCarbon arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  have hBridgeCN : ∀ arm,
      Adjacent cof3RepeatUnit (.bridgeCarbon arm) (.bridgeNitrogen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .double) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  have hNitrogenIpso : ∀ arm,
      Adjacent cof3RepeatUnit (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  have hIpsoHydroxy : ∀ arm,
      Adjacent cof3RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .hydroxySide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  have hIpsoOther : ∀ arm,
      Adjacent cof3RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .otherSide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  have hHydroxyO : ∀ arm,
      Adjacent cof3RepeatUnit (.linkerCarbon arm .hydroxySide) (.oxygen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof3RepeatUnit, cof3InternalBonds, allArms, cof3ArmBonds]
  apply rootReaches_of_skeleton cof3RepeatUnit hCore hAnchorBridge hBridgeCN
    hNitrogenIpso hIpsoHydroxy hIpsoOther
  · intro arm
    exact (((((hCore (armAnchor arm)).tail (hAnchorBridge arm)).tail
      (hBridgeCN arm)).tail (hNitrogenIpso arm)).tail (hIpsoHydroxy arm)).tail
        (hHydroxyO arm)

private theorem cof3Adjacency_mono_cof4
    {x y : UnitVertex} (h : Adjacent cof3RepeatUnit x y) :
    Adjacent cof4RepeatUnit x y := by
  rcases h with ⟨order, b, hb, hendpoints, horder⟩
  refine ⟨order, b, ?_, hendpoints, horder⟩
  simpa [cof3RepeatUnit, cof4RepeatUnit, cof4InternalBonds] using
    (List.mem_append_left oxidativeRingClosureBonds hb)

private theorem cof4_rootReaches (v : UnitVertex) :
    Relation.ReflTransGen (Adjacent cof4RepeatUnit) (.core .p0) v :=
  (cof3_rootReaches v).mono (fun _ _ h => cof3Adjacency_mono_cof4 h)

private theorem cof5_rootReaches (v : UnitVertex) :
    Relation.ReflTransGen (Adjacent cof5RepeatUnit) (.core .p0) v := by
  have hCore : ∀ p,
      Relation.ReflTransGen (Adjacent cof5RepeatUnit) (.core .p0) (.core p) :=
    coreRootReaches_of_cycle cof5RepeatUnit
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
      (by apply adjacent_of_internalBond (order := .aromatic); simp [cof5RepeatUnit, cof5InternalBonds,
        aromaticCoreBonds])
  have hAnchorBridge : ∀ arm,
      Adjacent cof5RepeatUnit (.core (armAnchor arm)) (.bridgeCarbon arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  have hBridgeCN : ∀ arm,
      Adjacent cof5RepeatUnit (.bridgeCarbon arm) (.bridgeNitrogen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .double) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  have hNitrogenIpso : ∀ arm,
      Adjacent cof5RepeatUnit (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  have hIpsoHydroxy : ∀ arm,
      Adjacent cof5RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .hydroxySide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  have hIpsoOther : ∀ arm,
      Adjacent cof5RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .otherSide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  have hCoreO : ∀ arm,
      Adjacent cof5RepeatUnit (.core (adjacentCoreHydroxyl arm)) (.oxygen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof5RepeatUnit, cof5InternalBonds, allArms, cof5ArmBonds]
  apply rootReaches_of_skeleton cof5RepeatUnit hCore hAnchorBridge hBridgeCN
    hNitrogenIpso hIpsoHydroxy hIpsoOther
  · intro arm
    exact (hCore (adjacentCoreHydroxyl arm)).tail (hCoreO arm)

private theorem cof6_rootReaches (v : UnitVertex) :
    Relation.ReflTransGen (Adjacent cof6RepeatUnit) (.core .p0) v := by
  have hCore : ∀ p,
      Relation.ReflTransGen (Adjacent cof6RepeatUnit) (.core .p0) (.core p) :=
    coreRootReaches_of_cycle cof6RepeatUnit
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
      (by apply adjacent_of_internalBond (order := .single); simp [cof6RepeatUnit, cof6InternalBonds,
        singleCoreBonds])
  have hAnchorBridge : ∀ arm,
      Adjacent cof6RepeatUnit (.core (armAnchor arm)) (.bridgeCarbon arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .double) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  have hBridgeCN : ∀ arm,
      Adjacent cof6RepeatUnit (.bridgeCarbon arm) (.bridgeNitrogen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  have hNitrogenIpso : ∀ arm,
      Adjacent cof6RepeatUnit (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .single) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  have hIpsoHydroxy : ∀ arm,
      Adjacent cof6RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .hydroxySide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  have hIpsoOther : ∀ arm,
      Adjacent cof6RepeatUnit (.linkerCarbon arm .ipso)
        (.linkerCarbon arm .otherSide) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .aromatic) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  have hCoreO : ∀ arm,
      Adjacent cof6RepeatUnit (.core (adjacentCoreHydroxyl arm)) (.oxygen arm) := by
    intro arm
    fin_cases arm <;> apply adjacent_of_internalBond (order := .double) <;>
      simp [cof6RepeatUnit, cof6InternalBonds, allArms, cof6ArmBonds]
  apply rootReaches_of_skeleton cof6RepeatUnit hCore hAnchorBridge hBridgeCN
    hNitrogenIpso hIpsoHydroxy hIpsoOther
  · intro arm
    exact (hCore (adjacentCoreHydroxyl arm)).tail (hCoreO arm)

private theorem cof3_internallyConnected : InternallyConnected cof3RepeatUnit :=
  internallyConnected_of_root cof3RepeatUnit (.core .p0) cof3_rootReaches

private theorem cof4_internallyConnected : InternallyConnected cof4RepeatUnit :=
  internallyConnected_of_root cof4RepeatUnit (.core .p0) cof4_rootReaches

private theorem cof5_internallyConnected : InternallyConnected cof5RepeatUnit :=
  internallyConnected_of_root cof5RepeatUnit (.core .p0) cof5_rootReaches

private theorem cof6_internallyConnected : InternallyConnected cof6RepeatUnit :=
  internallyConnected_of_root cof6RepeatUnit (.core .p0) cof6_rootReaches

private theorem cof3_noSelfBonds : NoSelfBonds cof3RepeatUnit := by
  simp [NoSelfBonds, cof3RepeatUnit, cof3InternalBonds, aromaticCoreBonds,
    allArms, cof3ArmBonds, mkBond]

private theorem cof4_noSelfBonds : NoSelfBonds cof4RepeatUnit := by
  simp [NoSelfBonds, cof4RepeatUnit, cof4InternalBonds, cof3InternalBonds,
    aromaticCoreBonds, allArms, cof3ArmBonds, oxidativeRingClosureBonds, mkBond]

private theorem cof5_noSelfBonds : NoSelfBonds cof5RepeatUnit := by
  simp [NoSelfBonds, cof5RepeatUnit, cof5InternalBonds, aromaticCoreBonds,
    allArms, cof5ArmBonds, mkBond]

private theorem cof6_noSelfBonds : NoSelfBonds cof6RepeatUnit := by
  simp [NoSelfBonds, cof6RepeatUnit, cof6InternalBonds, singleCoreBonds,
    allArms, cof6ArmBonds, mkBond]

private theorem cof3_noRepeatedInternalBonds :
    NoRepeatedInternalBonds cof3RepeatUnit := by
  simp [NoRepeatedInternalBonds, cof3RepeatUnit, cof3InternalBonds,
    aromaticCoreBonds, allArms, cof3ArmBonds, sameUndirectedEndpoints, mkBond]

private theorem cof4_noRepeatedInternalBonds :
    NoRepeatedInternalBonds cof4RepeatUnit := by
  simp [NoRepeatedInternalBonds, cof4RepeatUnit, cof4InternalBonds,
    cof3InternalBonds, aromaticCoreBonds, allArms, cof3ArmBonds,
    oxidativeRingClosureBonds, sameUndirectedEndpoints, mkBond]

private theorem cof5_noRepeatedInternalBonds :
    NoRepeatedInternalBonds cof5RepeatUnit := by
  simp [NoRepeatedInternalBonds, cof5RepeatUnit, cof5InternalBonds,
    aromaticCoreBonds, allArms, cof5ArmBonds, sameUndirectedEndpoints, mkBond]

private theorem cof6_noRepeatedInternalBonds :
    NoRepeatedInternalBonds cof6RepeatUnit := by
  simp [NoRepeatedInternalBonds, cof6RepeatUnit, cof6InternalBonds,
    singleCoreBonds, allArms, cof6ArmBonds, sameUndirectedEndpoints, mkBond]

private theorem cof3_neutralClosedShell :
    NeutralClosedShellNoAssignedStereocentres cof3RepeatUnit := by
  constructor
  · intro v
    fin_cases v <;> native_decide
  · simp [cof3RepeatUnit, cof3InternalBonds, aromaticCoreBonds, allArms,
      cof3ArmBonds, mkBond]

private theorem cof4_neutralClosedShell :
    NeutralClosedShellNoAssignedStereocentres cof4RepeatUnit := by
  constructor
  · intro v
    fin_cases v <;> native_decide
  · simp [cof4RepeatUnit, cof4InternalBonds, cof3InternalBonds,
      aromaticCoreBonds, allArms, cof3ArmBonds, oxidativeRingClosureBonds, mkBond]

private theorem cof5_neutralClosedShell :
    NeutralClosedShellNoAssignedStereocentres cof5RepeatUnit := by
  constructor
  · intro v
    fin_cases v <;> native_decide
  · simp [cof5RepeatUnit, cof5InternalBonds, aromaticCoreBonds, allArms,
      cof5ArmBonds, mkBond]

private theorem cof6_neutralClosedShell :
    NeutralClosedShellNoAssignedStereocentres cof6RepeatUnit := by
  constructor
  · intro v
    fin_cases v <;> native_decide
  · simp [cof6RepeatUnit, cof6InternalBonds, singleCoreBonds, allArms,
      cof6ArmBonds, mkBond]

private theorem cof3_ordinaryValence : OrdinaryValenceSatisfied cof3RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

private theorem cof4_ordinaryValence : OrdinaryValenceSatisfied cof4RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

private theorem cof5_ordinaryValence : OrdinaryValenceSatisfied cof5RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

private theorem cof6_ordinaryValence : OrdinaryValenceSatisfied cof6RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

/-! ## Structural functional-group classifiers -/

def HasAcyclicImineArm (u : RepeatUnit) (arm : Arm) : Prop :=
  HasBond u (.bridgeCarbon arm) (.bridgeNitrogen arm) .double ∧
  (u.atom (.bridgeCarbon arm)).attachedHydrogens = 1 ∧
  ¬ HasBond u (.bridgeCarbon arm) (.oxygen arm) .single

def HasOxazoleCNArm (u : RepeatUnit) (arm : Arm) : Prop :=
  HasBond u (.bridgeCarbon arm) (.bridgeNitrogen arm) .double ∧
  HasBond u (.bridgeNitrogen arm) (.linkerCarbon arm .ipso) .single ∧
  HasBond u (.linkerCarbon arm .ipso) (.linkerCarbon arm .hydroxySide) .aromatic ∧
  HasBond u (.linkerCarbon arm .hydroxySide) (.oxygen arm) .single ∧
  HasBond u (.oxygen arm) (.bridgeCarbon arm) .single

def HasKetoEnamineArm (u : RepeatUnit) (arm : Arm) : Prop :=
  HasBond u (.core (adjacentCoreHydroxyl arm)) (.oxygen arm) .double ∧
  HasBond u (.core (armAnchor arm)) (.bridgeCarbon arm) .double ∧
  HasBond u (.bridgeCarbon arm) (.bridgeNitrogen arm) .single ∧
  (u.atom (.bridgeNitrogen arm)).attachedHydrogens = 1

def IRObservationCompatible (observation : IRObservation) (u : RepeatUnit) : Prop :=
  match observation.imineStretch with
  | .present => ∃ arm, HasAcyclicImineArm u arm
  | .absent => ¬ ∃ arm, HasAcyclicImineArm u arm

private theorem cof3_hasAcyclicImineArm (arm : Arm) :
    HasAcyclicImineArm cof3RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasAcyclicImineArm, HasBond, sameUndirectedEndpoints, mkBond,
      cof3RepeatUnit, cof3InternalBonds, aromaticCoreBonds, allArms,
      cof3ArmBonds, cof3Atom, neutralAtom]

private theorem cof4_hasOxazoleCNArm (arm : Arm) :
    HasOxazoleCNArm cof4RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasOxazoleCNArm, HasBond, sameUndirectedEndpoints, mkBond,
      cof4RepeatUnit, cof4InternalBonds, cof3InternalBonds, aromaticCoreBonds,
      allArms, cof3ArmBonds, oxidativeRingClosureBonds]

private theorem cof4_hasNoAcyclicImineArm (arm : Arm) :
    ¬ HasAcyclicImineArm cof4RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasAcyclicImineArm, cof4RepeatUnit, cof4Atom, neutralAtom]

private theorem cof5_hasAcyclicImineArm (arm : Arm) :
    HasAcyclicImineArm cof5RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasAcyclicImineArm, HasBond, sameUndirectedEndpoints, mkBond,
      cof5RepeatUnit, cof5InternalBonds, aromaticCoreBonds, allArms,
      cof5ArmBonds, cof5Atom, neutralAtom]

private theorem cof6_hasKetoEnamineArm (arm : Arm) :
    HasKetoEnamineArm cof6RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasKetoEnamineArm, HasBond, sameUndirectedEndpoints, mkBond,
      cof6RepeatUnit, cof6InternalBonds, singleCoreBonds, allArms,
      cof6ArmBonds, cof6Atom, neutralAtom]

private theorem cof6_hasNoAcyclicImineArm (arm : Arm) :
    ¬ HasAcyclicImineArm cof6RepeatUnit arm := by
  fin_cases arm <;>
    simp [HasAcyclicImineArm, HasBond, sameUndirectedEndpoints, mkBond,
      cof6RepeatUnit, cof6InternalBonds, singleCoreBonds, allArms,
      cof6ArmBonds]

/-! ## Source-to-product graph rewrites and ledgers -/

def cof3CondensationInput : MolecularFormula :=
  MolecularFormula.add cof34BlackMonomer.formula
    (MolecularFormula.scale 3 cof34RedHalfBeforeCondensation)

def cof5CondensationInput : MolecularFormula :=
  MolecularFormula.add cof56BlackMonomer.formula
    (MolecularFormula.scale 3 cof56RedHalfBeforeCondensation)

def threeCondensationWaters : MolecularFormula :=
  MolecularFormula.scale 3 waterFormula

/-- Local graph-and-atom statement of the three imine condensations selected by
one repeat unit.  This says nothing about macroscopic yield or sole products. -/
def ImineCondensationProduct
    (central linker : SourceMonomer)
    (input : MolecularFormula)
    (u : RepeatUnit) : Prop :=
  central.condensationSites = 3 ∧
  linker.condensationSites = 2 ∧
  FormulaBalance input threeCondensationWaters (unitFormula u) ∧
  ∀ arm, HasAcyclicImineArm u arm

/-- Outcome-decisive hydrogen ledger for the source-stated oxidation.  The
oxidant identity, phase, mechanism, and molecular byproducts remain unknown. -/
structure OxidationHydrogenLedger where
  beforeHydrogenAtoms : ℕ
  afterHydrogenAtoms : ℕ
  removedHydrogenAtoms : ℕ
  balance : beforeHydrogenAtoms = afterHydrogenAtoms + removedHydrogenAtoms

def cof3ToCof4HydrogenLedger : OxidationHydrogenLedger :=
  { beforeHydrogenAtoms := (unitFormula cof3RepeatUnit).hydrogen
    afterHydrogenAtoms := (unitFormula cof4RepeatUnit).hydrogen
    removedHydrogenAtoms := 6
    balance := by native_decide }

def SameHeavyAtoms (before after : RepeatUnit) : Prop :=
  ∀ v,
    (before.atom v).element = (after.atom v).element ∧
    (before.atom v).isotope = (after.atom v).isotope ∧
    (before.atom v).formalCharge = (after.atom v).formalCharge ∧
    (before.atom v).radicalElectrons = (after.atom v).radicalElectrons

/-- Oxidative closure of each ortho-hydroxy imine into an oxazole C=N ring.
The only atom-count change is the six hydrogens printed in the problem. -/
def OxidativeCyclizationOf (before after : RepeatUnit) : Prop :=
  SameHeavyAtoms before after ∧
  before.topology = after.topology ∧
  before.boundaryBonds = after.boundaryBonds ∧
  after.internalBonds = before.internalBonds ++ oxidativeRingClosureBonds ∧
  FormulaBalance (unitFormula before) sixHydrogenAtomsFormula (unitFormula after) ∧
  (∀ arm,
    (before.atom (.bridgeCarbon arm)).attachedHydrogens = 1 ∧
    (after.atom (.bridgeCarbon arm)).attachedHydrogens = 0 ∧
    (before.atom (.oxygen arm)).attachedHydrogens = 1 ∧
    (after.atom (.oxygen arm)).attachedHydrogens = 0 ∧
    HasOxazoleCNArm after arm)

/-- Atom/formula conservation and the three simultaneous enol-imine to
beta-ketoenamine bond shifts forced by the stated isomerization. -/
def KetoEnamineIsomerizationOf (before after : RepeatUnit) : Prop :=
  SameHeavyAtoms before after ∧
  unitFormula before = unitFormula after ∧
  before.topology = after.topology ∧
  before.boundaryBonds = after.boundaryBonds ∧
  before.internalBonds = cof5InternalBonds ∧
  after.internalBonds = cof6InternalBonds ∧
  (∀ arm,
    HasAcyclicImineArm before arm ∧
    HasKetoEnamineArm after arm ∧
    (before.atom (.oxygen arm)).attachedHydrogens = 1 ∧
    (after.atom (.oxygen arm)).attachedHydrogens = 0 ∧
    (before.atom (.bridgeNitrogen arm)).attachedHydrogens = 0 ∧
    (after.atom (.bridgeNitrogen arm)).attachedHydrogens = 1)

def ExactSixBoundaryBonds (u : RepeatUnit) (expected : List BoundaryBond) : Prop :=
  u.boundaryBonds = expected ∧ u.boundaryBonds.length = 6

def SourceFigureContract : Prop :=
  cof34BlackMonomer.sixMemberedRingPattern =
      [.aldehyde, .hydrogen, .aldehyde, .hydrogen, .aldehyde, .hydrogen] ∧
  cof34RedMonomer.sixMemberedRingPattern =
      [.amine, .hydroxyl, .hydrogen, .amine, .hydroxyl, .hydrogen] ∧
  cof56BlackMonomer.sixMemberedRingPattern =
      [.aldehyde, .hydroxyl, .aldehyde, .hydroxyl, .aldehyde, .hydroxyl] ∧
  cof56RedMonomer.sixMemberedRingPattern =
      [.amine, .hydrogen, .hydrogen, .amine, .hydrogen, .hydrogen] ∧
  cof3FormationArrow.kind = .reversibleCondensation ∧
  cof3ToCof4Arrow.kind = .oxidation ∧
  cof3ToCof4Arrow.reagentLabel = some "[O]" ∧
  cof5FormationArrow.kind = .reversibleCondensation ∧
  cof5ToCof6Arrow.kind = .irreversibleIsomerization ∧
  cof3IRObservation.imineStretch = .present ∧
  cof4IRObservation.imineStretch = .absent ∧
  cof6IRObservation.imineStretch = .absent ∧
  cof3ToCof4ElementalChange.hydrogenChange = -6 ∧
  cof3ToCof4ElementalChange.carbonChange = 0 ∧
  cof3ToCof4ElementalChange.nitrogenChange = 0 ∧
  cof3ToCof4ElementalChange.oxygenChange = 0

theorem sourceFigureContract_derived : SourceFigureContract := by
  simp [SourceFigureContract, cof34BlackMonomer, cof34RedMonomer,
    cof56BlackMonomer, cof56RedMonomer, cof3FormationArrow, cof3ToCof4Arrow,
    cof5FormationArrow, cof5ToCof6Arrow, cof3IRObservation, cof4IRObservation,
    cof6IRObservation, cof3ToCof4ElementalChange]

private theorem cof3_exactSixBoundaryBonds :
    ExactSixBoundaryBonds cof3RepeatUnit cof34BoundaryBonds := by
  constructor
  · rfl
  · native_decide

private theorem cof4_exactSixBoundaryBonds :
    ExactSixBoundaryBonds cof4RepeatUnit cof34BoundaryBonds := by
  constructor
  · rfl
  · native_decide

private theorem cof5_exactSixBoundaryBonds :
    ExactSixBoundaryBonds cof5RepeatUnit cof56BoundaryBonds := by
  constructor
  · rfl
  · native_decide

private theorem cof6_exactSixBoundaryBonds :
    ExactSixBoundaryBonds cof6RepeatUnit cof56BoundaryBonds := by
  constructor
  · rfl
  · native_decide

private theorem cof3_formula :
    unitFormula cof3RepeatUnit =
      { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } := by
  native_decide

private theorem cof4_formula :
    unitFormula cof4RepeatUnit =
      { carbon := 18, hydrogen := 6, nitrogen := 3, oxygen := 3 } := by
  native_decide

private theorem cof5_formula :
    unitFormula cof5RepeatUnit =
      { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } := by
  native_decide

private theorem cof6_formula :
    unitFormula cof6RepeatUnit =
      { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } := by
  native_decide

private theorem cof3_imineCondensation :
    ImineCondensationProduct cof34BlackMonomer cof34RedMonomer
      cof3CondensationInput cof3RepeatUnit := by
  refine ⟨rfl, rfl, ?_, cof3_hasAcyclicImineArm⟩
  unfold FormulaBalance
  native_decide

private theorem cof5_imineCondensation :
    ImineCondensationProduct cof56BlackMonomer cof56RedMonomer
      cof5CondensationInput cof5RepeatUnit := by
  refine ⟨rfl, rfl, ?_, cof5_hasAcyclicImineArm⟩
  unfold FormulaBalance
  native_decide

private theorem cof3_irCompatible :
    IRObservationCompatible cof3IRObservation cof3RepeatUnit := by
  exact ⟨.north, cof3_hasAcyclicImineArm .north⟩

private theorem cof4_irCompatible :
    IRObservationCompatible cof4IRObservation cof4RepeatUnit := by
  rintro ⟨arm, h⟩
  exact cof4_hasNoAcyclicImineArm arm h

private theorem cof6_irCompatible :
    IRObservationCompatible cof6IRObservation cof6RepeatUnit := by
  rintro ⟨arm, h⟩
  exact cof6_hasNoAcyclicImineArm arm h

private theorem cof3Cof4_sameHeavyAtoms :
    SameHeavyAtoms cof3RepeatUnit cof4RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

private theorem cof5Cof6_sameHeavyAtoms :
    SameHeavyAtoms cof5RepeatUnit cof6RepeatUnit := by
  intro v
  fin_cases v <;> native_decide

private theorem cof3Cof4_oxidativeCyclization :
    OxidativeCyclizationOf cof3RepeatUnit cof4RepeatUnit := by
  refine ⟨cof3Cof4_sameHeavyAtoms, rfl, rfl, rfl, ?_, ?_⟩
  · unfold FormulaBalance
    native_decide
  · intro arm
    exact ⟨rfl, rfl, rfl, rfl, cof4_hasOxazoleCNArm arm⟩

private theorem cof5Cof6_ketoEnamineIsomerization :
    KetoEnamineIsomerizationOf cof5RepeatUnit cof6RepeatUnit := by
  refine ⟨cof5Cof6_sameHeavyAtoms, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact cof5_formula.trans cof6_formula.symm
  · intro arm
    exact ⟨cof5_hasAcyclicImineArm arm, cof6_hasKetoEnamineArm arm,
      rfl, rfl, rfl, rfl⟩

/-! ## Per-output derivation specifications -/

def Cof3DerivationSpec (u : RepeatUnit) : Prop :=
  SourceFigureContract ∧
  PreviousPartNeededConclusion ∧
  u.topology = .hexagonalOne ∧
  (∀ v, u.atom v = cof3Atom v) ∧
  u.internalBonds = cof3InternalBonds ∧
  ExactSixBoundaryBonds u cof34BoundaryBonds ∧
  ImineCondensationProduct cof34BlackMonomer cof34RedMonomer cof3CondensationInput u ∧
  IRObservationCompatible cof3IRObservation u ∧
  unitFormula u = { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } ∧
  Fintype.card UnitVertex = 24 ∧
  NoSelfBonds u ∧
  NoRepeatedInternalBonds u ∧
  InternallyConnected u ∧
  NeutralClosedShellNoAssignedStereocentres u ∧
  OrdinaryValenceSatisfied u

def Cof4DerivationSpec (u : RepeatUnit) : Prop :=
  Cof3DerivationSpec cof3RepeatUnit ∧
  u.topology = .hexagonalOne ∧
  (∀ v, u.atom v = cof4Atom v) ∧
  u.internalBonds = cof4InternalBonds ∧
  ExactSixBoundaryBonds u cof34BoundaryBonds ∧
  OxidativeCyclizationOf cof3RepeatUnit u ∧
  cof3ToCof4HydrogenLedger.beforeHydrogenAtoms = 12 ∧
  cof3ToCof4HydrogenLedger.afterHydrogenAtoms = 6 ∧
  cof3ToCof4HydrogenLedger.removedHydrogenAtoms = 6 ∧
  IRObservationCompatible cof4IRObservation u ∧
  (∀ arm, HasOxazoleCNArm u arm) ∧
  unitFormula u = { carbon := 18, hydrogen := 6, nitrogen := 3, oxygen := 3 } ∧
  NoSelfBonds u ∧
  NoRepeatedInternalBonds u ∧
  InternallyConnected u ∧
  NeutralClosedShellNoAssignedStereocentres u ∧
  OrdinaryValenceSatisfied u

def Cof5DerivationSpec (u : RepeatUnit) : Prop :=
  SourceFigureContract ∧
  PreviousPartNeededConclusion ∧
  u.topology = .hexagonalOne ∧
  (∀ v, u.atom v = cof5Atom v) ∧
  u.internalBonds = cof5InternalBonds ∧
  ExactSixBoundaryBonds u cof56BoundaryBonds ∧
  ImineCondensationProduct cof56BlackMonomer cof56RedMonomer cof5CondensationInput u ∧
  (∀ arm, HasAcyclicImineArm u arm) ∧
  unitFormula u = { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } ∧
  NoSelfBonds u ∧
  NoRepeatedInternalBonds u ∧
  InternallyConnected u ∧
  NeutralClosedShellNoAssignedStereocentres u ∧
  OrdinaryValenceSatisfied u

def Cof6DerivationSpec (u : RepeatUnit) : Prop :=
  Cof5DerivationSpec cof5RepeatUnit ∧
  u.topology = .hexagonalOne ∧
  (∀ v, u.atom v = cof6Atom v) ∧
  u.internalBonds = cof6InternalBonds ∧
  ExactSixBoundaryBonds u cof56BoundaryBonds ∧
  KetoEnamineIsomerizationOf cof5RepeatUnit u ∧
  IRObservationCompatible cof6IRObservation u ∧
  (∀ arm, HasKetoEnamineArm u arm) ∧
  unitFormula u = { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 } ∧
  NoSelfBonds u ∧
  NoRepeatedInternalBonds u ∧
  InternallyConnected u ∧
  NeutralClosedShellNoAssignedStereocentres u ∧
  OrdinaryValenceSatisfied u

/-! Each requested drawing has both a concrete graph carrier and a theorem that
it meets its source-derived specification. -/

def Cof3Output : Prop := Cof3DerivationSpec cof3RepeatUnit
def Cof4Output : Prop := Cof4DerivationSpec cof4RepeatUnit
def Cof5Output : Prop := Cof5DerivationSpec cof5RepeatUnit
def Cof6Output : Prop := Cof6DerivationSpec cof6RepeatUnit

theorem cof3_raw_result : Cof3Output := by
  refine ⟨sourceFigureContract_derived, previousPartNeededConclusion_derived,
    rfl, ?_, rfl, cof3_exactSixBoundaryBonds, cof3_imineCondensation,
    cof3_irCompatible, cof3_formula, ?_, cof3_noSelfBonds,
    cof3_noRepeatedInternalBonds, cof3_internallyConnected,
    cof3_neutralClosedShell, cof3_ordinaryValence⟩
  · intro v
    rfl
  · native_decide

theorem cof4_raw_result : Cof4Output := by
  refine ⟨cof3_raw_result, rfl, ?_, rfl, cof4_exactSixBoundaryBonds,
    cof3Cof4_oxidativeCyclization, ?_, ?_, ?_, cof4_irCompatible,
    cof4_hasOxazoleCNArm, cof4_formula, cof4_noSelfBonds,
    cof4_noRepeatedInternalBonds, cof4_internallyConnected,
    cof4_neutralClosedShell, cof4_ordinaryValence⟩
  · intro v
    rfl
  · native_decide
  · native_decide
  · native_decide

theorem cof5_raw_result : Cof5Output := by
  refine ⟨sourceFigureContract_derived, previousPartNeededConclusion_derived,
    rfl, ?_, rfl, cof5_exactSixBoundaryBonds, cof5_imineCondensation,
    cof5_hasAcyclicImineArm, cof5_formula, cof5_noSelfBonds,
    cof5_noRepeatedInternalBonds, cof5_internallyConnected,
    cof5_neutralClosedShell, cof5_ordinaryValence⟩
  intro v
  rfl

theorem cof6_raw_result : Cof6Output := by
  refine ⟨cof5_raw_result, rfl, ?_, rfl, cof6_exactSixBoundaryBonds,
    cof5Cof6_ketoEnamineIsomerization, cof6_irCompatible,
    cof6_hasKetoEnamineArm, cof6_formula, cof6_noSelfBonds,
    cof6_noRepeatedInternalBonds, cof6_internallyConnected,
    cof6_neutralClosedShell, cof6_ordinaryValence⟩
  intro v
  rfl

/-- The exact-symbolic aggregate result, in the controller-requested order. -/
def RawResult : Prop := Cof3Output ∧ Cof4Output ∧ Cof5Output ∧ Cof6Output

/-- Exact-symbolic reporting performs no rounding or lossy conversion. -/
def ReportedResult : Prop := RawResult

theorem raw_result : RawResult := by
  exact ⟨cof3_raw_result, cof4_raw_result, cof5_raw_result, cof6_raw_result⟩

theorem reported_result : ReportedResult := by
  exact raw_result

end IChO2026Problems.Icho2026T3A4
