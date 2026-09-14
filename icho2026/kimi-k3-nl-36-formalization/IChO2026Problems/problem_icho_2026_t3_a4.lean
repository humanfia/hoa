import IChO2026Chem.Core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# IChO 2026, problem 3.4

Atom-level specifications of the repeat-unit drawings of COFs 3--6.

The problem uses the same boundary convention as its drawing of COF-1: a
repeat contains one three-connected black core and one half of each of the
three two-connected red linkers incident to it.  To state this without
creating fractional atoms, `LocalSite` describes the complete local star (the
central core, three complete linkers, and the attachment carbon of each
neighbouring core), while `ownership` assigns weight `1`, `1/2`, or `0` to the
sites.  Each of the three dashed boundary lines cuts the two opposite C--C
bonds of one linker ring.

The molecular graph is deliberately explicit.  Hydrogens are vertices, bond
orders are data, every atom has formal charge and radical-electron fields, and
the absence of requested stereocentres is represented by an everywhere-`none`
assignment rather than by a prose label.
-/

namespace IChO2026Problems.T3A4

inductive Element
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  deriving DecidableEq, BEq, Fintype, Repr

inductive BondOrder
  | single
  | double
  deriving DecidableEq, BEq, Fintype, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2

inductive TetrahedralConfiguration
  | clockwise
  | anticlockwise
  deriving DecidableEq, BEq, Fintype, Repr

structure AtomDescriptor where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  deriving DecidableEq, Repr

def neutralClosedShellAtom (e : Element) : AtomDescriptor :=
  { element := e, formalCharge := 0, radicalElectrons := 0 }

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.count (f : MolecularFormula) : Element → ℕ
  | .hydrogen => f.hydrogen
  | .carbon => f.carbon
  | .nitrogen => f.nitrogen
  | .oxygen => f.oxygen

inductive RingSubstituent
  | aldehyde
  | amine
  | hydroxy
  | hydrogen
  deriving DecidableEq, BEq, Fintype, Repr

/-- A source-depicted benzene precursor.  The six positions retain the cyclic
order in the printed structural formula. -/
structure BenzenePrecursor where
  substituent : Fin 6 → RingSubstituent
  formula : MolecularFormula

def triformylbenzene : BenzenePrecursor where
  substituent i := if i.val % 2 = 0 then .aldehyde else .hydrogen
  formula := { carbon := 9, hydrogen := 6, nitrogen := 0, oxygen := 3 }

def diaminoDihydroxybenzene : BenzenePrecursor where
  substituent i :=
    match i.val with
    | 0 => .amine
    | 1 => .hydroxy
    | 2 => .hydrogen
    | 3 => .amine
    | 4 => .hydroxy
    | _ => .hydrogen
  formula := { carbon := 6, hydrogen := 8, nitrogen := 2, oxygen := 2 }

def triformylphloroglucinol : BenzenePrecursor where
  substituent i := if i.val % 2 = 0 then .aldehyde else .hydroxy
  formula := { carbon := 9, hydrogen := 6, nitrogen := 0, oxygen := 6 }

def paraPhenylenediamine : BenzenePrecursor where
  substituent i := if i.val = 0 ∨ i.val = 3 then .amine else .hydrogen
  formula := { carbon := 6, hydrogen := 8, nitrogen := 2, oxygen := 0 }

def waterFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 2, nitrogen := 0, oxygen := 1 }

def countSubstituent (p : BenzenePrecursor) (s : RingSubstituent) : ℕ :=
  (Finset.univ.filter fun i => p.substituent i = s).card

/-- The atom ledger for one trigonal core, three halves of linear linkers, and
three condensational losses of water. -/
def ImineCondensationBalance
    (core linker product : MolecularFormula) : Prop :=
  ∀ e : Element,
    (core.count e : ℚ) + (3 / 2 : ℚ) * (linker.count e : ℚ) -
        3 * (waterFormula.count e : ℚ) = (product.count e : ℚ)

def HydrogenOnlyLoss
    (before after : MolecularFormula) (lost : ℕ) : Prop :=
  after.carbon = before.carbon ∧
  after.nitrogen = before.nitrogen ∧
  after.oxygen = before.oxygen ∧
  after.hydrogen + lost = before.hydrogen

inductive CofKind
  | cof3
  | cof4
  | cof5
  | cof6
  deriving DecidableEq, BEq, Fintype, Repr

inductive NetTopology
  | hexagonalOne
  deriving DecidableEq, BEq, Fintype, Repr

inductive TransformationKind
  | imineCondensation
  | oxidation
  | ketoEnamineIsomerization
  deriving DecidableEq, BEq, Fintype, Repr

inductive ReactionDirection
  | reversible
  | directed
  | irreversible
  deriving DecidableEq, BEq, Fintype, Repr

/-- Exact arrow-level information printed in the two page-4 schemes.  No
coefficient, phase, yield, or unshown byproduct is added. -/
structure TransformationDescriptor where
  kind : TransformationKind
  direction : ReactionDirection
  oxidantLabelShown : Bool
  deriving DecidableEq, Repr

def cof3FormationArrow : TransformationDescriptor :=
  { kind := .imineCondensation, direction := .reversible,
    oxidantLabelShown := false }

def cof3ToCof4Arrow : TransformationDescriptor :=
  { kind := .oxidation, direction := .directed,
    oxidantLabelShown := true }

def cof5FormationArrow : TransformationDescriptor :=
  { kind := .imineCondensation, direction := .reversible,
    oxidantLabelShown := false }

def cof5ToCof6Arrow : TransformationDescriptor :=
  { kind := .ketoEnamineIsomerization, direction := .irreversible,
    oxidantLabelShown := false }

inductive ImineStretchObservation
  | present
  | absent
  | notReported
  deriving DecidableEq, BEq, Fintype, Repr

def sourceImineStretch : CofKind → ImineStretchObservation
  | .cof3 => .present
  | .cof4 => .absent
  | .cof5 => .notReported
  | .cof6 => .absent

/-- Relevant part of the topology key printed on page 3.  It is intentionally
candidate-independent: a 3-connected planar core and 2-connected linear
linker determine the displayed Hexagonal-1 net. -/
def topologyFromConnectivities (core linker : ℕ) : Option NetTopology :=
  if core = 3 ∧ linker = 2 then some .hexagonalOne else none

/-- Sites in a complete local star.  `nearArmCarbon` is aldehyde-derived from
the central black core.  `farArmCarbon` is aldehyde-derived from a neighbouring
black core, and `neighborCorePort` is its aromatic/core attachment carbon. -/
inductive LocalSite
  | coreCarbon (position : Fin 6)
  | coreHydrogen (arm : Fin 3)
  | coreOxygen (arm : Fin 3)
  | coreOxygenHydrogen (arm : Fin 3)
  | nearArmCarbon (arm : Fin 3)
  | nearArmHydrogen (arm : Fin 3)
  | linkerCarbon (arm : Fin 3) (position : Fin 6)
  | linkerNitrogen (arm : Fin 3) (endIndex : Fin 2)
  | linkerNitrogenHydrogen (arm : Fin 3) (endIndex : Fin 2)
  | linkerOxygen (arm : Fin 3) (endIndex : Fin 2)
  | linkerOxygenHydrogen (arm : Fin 3) (endIndex : Fin 2)
  | linkerRingHydrogen (arm : Fin 3) (slot : Fin 4)
  | farArmCarbon (arm : Fin 3)
  | farArmHydrogen (arm : Fin 3)
  | neighborCorePort (arm : Fin 3)
  deriving DecidableEq, Fintype, Repr

def armCorePosition (a : Fin 3) : Fin 6 :=
  ⟨2 * a.val, by omega⟩

def alternatingCorePosition (a : Fin 3) : Fin 6 :=
  ⟨2 * a.val + 1, by omega⟩

def linkerHydrogenPosition (k : CofKind) (h : Fin 4) : Fin 6 :=
  match k with
  | .cof3 | .cof4 => if h.val = 0 then 2 else 5
  | .cof5 | .cof6 =>
      match h.val with
      | 0 => 1
      | 1 => 2
      | 2 => 4
      | _ => 5

def siteElement : LocalSite → Element
  | .coreCarbon _ => .carbon
  | .coreHydrogen _ => .hydrogen
  | .coreOxygen _ => .oxygen
  | .coreOxygenHydrogen _ => .hydrogen
  | .nearArmCarbon _ => .carbon
  | .nearArmHydrogen _ => .hydrogen
  | .linkerCarbon _ _ => .carbon
  | .linkerNitrogen _ _ => .nitrogen
  | .linkerNitrogenHydrogen _ _ => .hydrogen
  | .linkerOxygen _ _ => .oxygen
  | .linkerOxygenHydrogen _ _ => .hydrogen
  | .linkerRingHydrogen _ _ => .hydrogen
  | .farArmCarbon _ => .carbon
  | .farArmHydrogen _ => .hydrogen
  | .neighborCorePort _ => .carbon

def hasTriformylbenzeneCore : CofKind → Bool
  | .cof3 | .cof4 => true
  | .cof5 | .cof6 => false

def hasCoreOxygen : CofKind → Bool
  | .cof5 | .cof6 => true
  | .cof3 | .cof4 => false

def hasArmHydrogen : CofKind → Bool
  | .cof4 => false
  | .cof3 | .cof5 | .cof6 => true

def hasLinkerOxygen : CofKind → Bool
  | .cof3 | .cof4 => true
  | .cof5 | .cof6 => false

def sitePresent (k : CofKind) : LocalSite → Bool
  | .coreCarbon _ => true
  | .coreHydrogen _ => hasTriformylbenzeneCore k
  | .coreOxygen _ => hasCoreOxygen k
  | .coreOxygenHydrogen _ => k == .cof5
  | .nearArmCarbon _ => true
  | .nearArmHydrogen _ => hasArmHydrogen k
  | .linkerCarbon _ _ => true
  | .linkerNitrogen _ _ => true
  | .linkerNitrogenHydrogen _ _ => k == .cof6
  | .linkerOxygen _ _ => hasLinkerOxygen k
  | .linkerOxygenHydrogen _ _ => k == .cof3
  | .linkerRingHydrogen _ h =>
      match k with
      | .cof3 | .cof4 => h.val < 2
      | .cof5 | .cof6 => true
  | .farArmCarbon _ => true
  | .farArmHydrogen _ => hasArmHydrogen k
  | .neighborCorePort _ => true

def atomAt (k : CofKind) (s : LocalSite) : Option AtomDescriptor :=
  if sitePresent k s then some (neutralClosedShellAtom (siteElement s)) else none

/-- Ownership in the fundamental repeat.  Complete linker atoms have weight
one half because the corresponding linker joins two black cores.  The far arm
and neighbouring core port are displayed only to make every cross-boundary
bond explicit. -/
def ownership : LocalSite → ℚ
  | .linkerCarbon _ _ => 1 / 2
  | .linkerNitrogen _ _ => 1 / 2
  | .linkerNitrogenHydrogen _ _ => 1 / 2
  | .linkerOxygen _ _ => 1 / 2
  | .linkerOxygenHydrogen _ _ => 1 / 2
  | .linkerRingHydrogen _ _ => 1 / 2
  | .farArmCarbon _ => 0
  | .farArmHydrogen _ => 0
  | .neighborCorePort _ => 0
  | _ => 1

def unorderedNatPair (i j : Fin 6) (a b : ℕ) : Bool :=
  (i.val == a && j.val == b) || (i.val == b && j.val == a)

def ringDoublePair (i j : Fin 6) : Bool :=
  unorderedNatPair i j 0 1 ||
  unorderedNatPair i j 2 3 ||
  unorderedNatPair i j 4 5

def ringSinglePair (i j : Fin 6) : Bool :=
  unorderedNatPair i j 1 2 ||
  unorderedNatPair i j 3 4 ||
  unorderedNatPair i j 5 0

def ringAdjacent (i j : Fin 6) : Bool :=
  ringDoublePair i j || ringSinglePair i j

def directedDoubleBond (k : CofKind) : LocalSite → LocalSite → Bool
  | .coreCarbon i, .coreCarbon j =>
      if k == .cof6 then false else ringDoublePair i j
  | .linkerCarbon a i, .linkerCarbon b j =>
      a == b && ringDoublePair i j
  | .coreCarbon i, .coreOxygen a =>
      k == .cof6 && i == alternatingCorePosition a
  | .coreCarbon i, .nearArmCarbon a =>
      k == .cof6 && i == armCorePosition a
  | .nearArmCarbon a, .linkerNitrogen b e =>
      k != .cof6 && a == b && e.val == 0
  | .linkerNitrogen a e, .farArmCarbon b =>
      k != .cof6 && a == b && e.val == 1
  | .farArmCarbon a, .neighborCorePort b =>
      k == .cof6 && a == b
  | _, _ => false

def directedSingleBond (k : CofKind) : LocalSite → LocalSite → Bool
  | .coreCarbon i, .coreCarbon j =>
      if k == .cof6 then ringAdjacent i j else ringSinglePair i j
  | .linkerCarbon a i, .linkerCarbon b j =>
      a == b && ringSinglePair i j
  | .coreCarbon i, .coreHydrogen a =>
      hasTriformylbenzeneCore k && i == alternatingCorePosition a
  | .coreCarbon i, .coreOxygen a =>
      k == .cof5 && i == alternatingCorePosition a
  | .coreOxygen a, .coreOxygenHydrogen b =>
      k == .cof5 && a == b
  | .coreCarbon i, .nearArmCarbon a =>
      k != .cof6 && i == armCorePosition a
  | .nearArmCarbon a, .nearArmHydrogen b =>
      hasArmHydrogen k && a == b
  | .nearArmCarbon a, .linkerNitrogen b e =>
      k == .cof6 && a == b && e.val == 0
  | .linkerNitrogen a e, .linkerCarbon b i =>
      a == b &&
        ((e.val == 0 && i.val == 0) || (e.val == 1 && i.val == 3))
  | .linkerNitrogen a e, .linkerNitrogenHydrogen b f =>
      k == .cof6 && a == b && e == f
  | .linkerCarbon a i, .linkerOxygen b e =>
      hasLinkerOxygen k && a == b &&
        ((e.val == 0 && i.val == 1) || (e.val == 1 && i.val == 4))
  | .linkerOxygen a e, .linkerOxygenHydrogen b f =>
      k == .cof3 && a == b && e == f
  | .nearArmCarbon a, .linkerOxygen b e =>
      k == .cof4 && a == b && e.val == 0
  | .farArmCarbon a, .linkerOxygen b e =>
      k == .cof4 && a == b && e.val == 1
  | .linkerCarbon a i, .linkerRingHydrogen b h =>
      a == b && i == linkerHydrogenPosition k h
  | .linkerNitrogen a e, .farArmCarbon b =>
      k == .cof6 && a == b && e.val == 1
  | .farArmCarbon a, .farArmHydrogen b =>
      hasArmHydrogen k && a == b
  | .farArmCarbon a, .neighborCorePort b =>
      k != .cof6 && a == b
  | _, _ => false

def bondOrder (k : CofKind) (x y : LocalSite) : Option BondOrder :=
  if !(sitePresent k x && sitePresent k y) then none
  else if x == y then none
  else if directedDoubleBond k x y || directedDoubleBond k y x then some .double
  else if directedSingleBond k x y || directedSingleBond k y x then some .single
  else none

/-- The Mathlib graph underlying the bond-order-labelled molecular drawing. -/
def molecularGraph (k : CofKind) : SimpleGraph LocalSite :=
  SimpleGraph.fromRel fun x y => bondOrder k x y ≠ none

inductive BoundaryLocation
  | linkerRingCentre
  deriving DecidableEq, BEq, Fintype, Repr

/-- One dashed boundary line.  The two pairs are the two opposite phenylene
C--C bonds intersected by a line through the ring centre. -/
structure BoundaryCut where
  arm : Fin 3
  location : BoundaryLocation
  firstCrossing : LocalSite × LocalSite
  secondCrossing : LocalSite × LocalSite
  deriving DecidableEq, Repr

def boundaryCut (a : Fin 3) : BoundaryCut where
  arm := a
  location := .linkerRingCentre
  firstCrossing := (.linkerCarbon a 1, .linkerCarbon a 2)
  secondCrossing := (.linkerCarbon a 4, .linkerCarbon a 5)

def repeatHydrogenBond (k : CofKind) (a : Fin 3) : Option (LocalSite × LocalSite) :=
  match k with
  | .cof3 => some (.linkerOxygenHydrogen a 0, .linkerNitrogen a 0)
  | .cof4 => none
  | .cof5 => some (.coreOxygenHydrogen a, .linkerNitrogen a 0)
  | .cof6 => some (.linkerNitrogenHydrogen a 0, .coreOxygen a)

structure RepeatUnitDrawing where
  kind : CofKind
  topology : NetTopology
  coreConnectivity : ℕ
  linkerConnectivity : ℕ
  atoms : LocalSite → Option AtomDescriptor
  bonds : LocalSite → LocalSite → Option BondOrder
  graph : SimpleGraph LocalSite
  ownership : LocalSite → ℚ
  dashedBoundary : Fin 3 → BoundaryCut
  hydrogenBond : Fin 3 → Option (LocalSite × LocalSite)
  stereochemistry : LocalSite → Option TetrahedralConfiguration

def repeatUnit (k : CofKind) : RepeatUnitDrawing where
  kind := k
  topology := .hexagonalOne
  coreConnectivity := 3
  linkerConnectivity := 2
  atoms := atomAt k
  bonds := bondOrder k
  graph := molecularGraph k
  ownership := ownership
  dashedBoundary := boundaryCut
  hydrogenBond := repeatHydrogenBond k
  stereochemistry := fun _ => none

def cof3RepeatUnit : RepeatUnitDrawing := repeatUnit .cof3
def cof4RepeatUnit : RepeatUnitDrawing := repeatUnit .cof4
def cof5RepeatUnit : RepeatUnitDrawing := repeatUnit .cof5
def cof6RepeatUnit : RepeatUnitDrawing := repeatUnit .cof6

def cof3Formula : MolecularFormula :=
  { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 }

def cof4Formula : MolecularFormula :=
  { carbon := 18, hydrogen := 6, nitrogen := 3, oxygen := 3 }

def cof5Formula : MolecularFormula :=
  { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 }

def cof6Formula : MolecularFormula :=
  { carbon := 18, hydrogen := 12, nitrogen := 3, oxygen := 3 }

def ownedElementCount (r : RepeatUnitDrawing) (e : Element) : ℚ :=
  ∑ s : LocalSite,
    match r.atoms s with
    | none => 0
    | some a => if a.element = e then r.ownership s else 0

def FormulaMatches (r : RepeatUnitDrawing) (f : MolecularFormula) : Prop :=
  ∀ e : Element, ownedElementCount r e = (f.count e : ℚ)

def bondValenceAt (r : RepeatUnitDrawing) (s : LocalSite) : ℕ :=
  ∑ t : LocalSite,
    match r.bonds s t with
    | none => 0
    | some order => order.valence

def expectedNeutralValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .nitrogen => 3
  | .oxygen => 2

def IsNeighbourInterface : LocalSite → Prop
  | .neighborCorePort _ => True
  | _ => False

def InteriorValenceValid (r : RepeatUnitDrawing) : Prop :=
  ∀ (s : LocalSite) (a : AtomDescriptor),
    r.atoms s = some a → ¬ IsNeighbourInterface s →
      bondValenceAt r s = expectedNeutralValence a.element

def BondsJoinPresentAtoms (r : RepeatUnitDrawing) : Prop :=
  ∀ (x y : LocalSite) (order : BondOrder),
    r.bonds x y = some order → r.atoms x ≠ none ∧ r.atoms y ≠ none

def NeutralAndRadicalFree (r : RepeatUnitDrawing) : Prop :=
  ∀ (s : LocalSite) (a : AtomDescriptor),
    r.atoms s = some a → a.formalCharge = 0 ∧ a.radicalElectrons = 0

def SameHeavyAtomSites
    (before after : RepeatUnitDrawing) : Prop :=
  ∀ s : LocalSite, siteElement s ≠ .hydrogen →
    (before.atoms s).isSome = (after.atoms s).isSome

def NoAssignedStereocentres (r : RepeatUnitDrawing) : Prop :=
  ∀ s : LocalSite, r.stereochemistry s = none

def HasBond
    (r : RepeatUnitDrawing) (x y : LocalSite) (order : BondOrder) : Prop :=
  r.bonds x y = some order

/-- The ordinary imine motif is distinguished from the endocyclic C=N bond in
a benzoxazole by the aldehyde-derived carbon's retained hydrogen. -/
def HasImineMotif (r : RepeatUnitDrawing) : Prop :=
  ∃ a : Fin 3,
    HasBond r (.nearArmCarbon a) (.nearArmHydrogen a) .single ∧
    HasBond r (.nearArmCarbon a) (.linkerNitrogen a 0) .double

def HasCarbonNitrogenDoubleBond (r : RepeatUnitDrawing) : Prop :=
  ∃ (x y : LocalSite),
    r.atoms x = some (neutralClosedShellAtom .carbon) ∧
    r.atoms y = some (neutralClosedShellAtom .nitrogen) ∧
    HasBond r x y .double

def CompatibleWithImineStretch
    (r : RepeatUnitDrawing) (observation : ImineStretchObservation) : Prop :=
  match observation with
  | .present => HasImineMotif r
  | .absent => ¬ HasImineMotif r
  | .notReported => True

def ThreeImineLinkedArms (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3,
    HasBond r (.coreCarbon (armCorePosition a)) (.nearArmCarbon a) .single ∧
    HasBond r (.nearArmCarbon a) (.nearArmHydrogen a) .single ∧
    HasBond r (.nearArmCarbon a) (.linkerNitrogen a 0) .double ∧
    HasBond r (.linkerNitrogen a 0) (.linkerCarbon a 0) .single ∧
    HasBond r (.linkerCarbon a 3) (.linkerNitrogen a 1) .single ∧
    HasBond r (.linkerNitrogen a 1) (.farArmCarbon a) .double ∧
    HasBond r (.farArmCarbon a) (.farArmHydrogen a) .single ∧
    HasBond r (.farArmCarbon a) (.neighborCorePort a) .single

def OrthoHydroxyGroupsOnLinker (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3,
    HasBond r (.linkerCarbon a 1) (.linkerOxygen a 0) .single ∧
    HasBond r (.linkerOxygen a 0) (.linkerOxygenHydrogen a 0) .single ∧
    HasBond r (.linkerCarbon a 4) (.linkerOxygen a 1) .single ∧
    HasBond r (.linkerOxygen a 1) (.linkerOxygenHydrogen a 1) .single

def CoreHydroxyGroups (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3,
    HasBond r (.coreCarbon (alternatingCorePosition a)) (.coreOxygen a) .single ∧
    HasBond r (.coreOxygen a) (.coreOxygenHydrogen a) .single

/-- Both fused five-membered rings of every complete red linker are explicit:
X=N-C-C-O-X at the near and far ends. -/
def ThreeBisBenzoxazoleLinkers (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3,
    HasBond r (.nearArmCarbon a) (.linkerNitrogen a 0) .double ∧
    HasBond r (.linkerNitrogen a 0) (.linkerCarbon a 0) .single ∧
    HasBond r (.linkerCarbon a 0) (.linkerCarbon a 1) .double ∧
    HasBond r (.linkerCarbon a 1) (.linkerOxygen a 0) .single ∧
    HasBond r (.linkerOxygen a 0) (.nearArmCarbon a) .single ∧
    HasBond r (.farArmCarbon a) (.linkerNitrogen a 1) .double ∧
    HasBond r (.linkerNitrogen a 1) (.linkerCarbon a 3) .single ∧
    HasBond r (.linkerCarbon a 3) (.linkerCarbon a 4) .single ∧
    HasBond r (.linkerCarbon a 4) (.linkerOxygen a 1) .single ∧
    HasBond r (.linkerOxygen a 1) (.farArmCarbon a) .single

def ThreeBetaKetoEnamineArms (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3,
    HasBond r (.coreCarbon (alternatingCorePosition a)) (.coreOxygen a) .double ∧
    HasBond r (.coreCarbon (armCorePosition a)) (.nearArmCarbon a) .double ∧
    HasBond r (.nearArmCarbon a) (.nearArmHydrogen a) .single ∧
    HasBond r (.nearArmCarbon a) (.linkerNitrogen a 0) .single ∧
    HasBond r (.linkerNitrogen a 0) (.linkerNitrogenHydrogen a 0) .single ∧
    HasBond r (.linkerNitrogen a 0) (.linkerCarbon a 0) .single

def ExactDashedBoundary (r : RepeatUnitDrawing) : Prop :=
  ∀ a : Fin 3, r.dashedBoundary a = boundaryCut a

def CommonRepeatAudit
    (r : RepeatUnitDrawing) (f : MolecularFormula) : Prop :=
  r.topology = .hexagonalOne ∧
  r.coreConnectivity = 3 ∧
  r.linkerConnectivity = 2 ∧
  ExactDashedBoundary r ∧
  FormulaMatches r f ∧
  InteriorValenceValid r ∧
  BondsJoinPresentAtoms r ∧
  NeutralAndRadicalFree r ∧
  NoAssignedStereocentres r

def ImineCondensationProduct
    (core linker : BenzenePrecursor)
    (arrow : TransformationDescriptor)
    (r : RepeatUnitDrawing) (f : MolecularFormula) : Prop :=
  arrow.kind = .imineCondensation ∧
  arrow.direction = .reversible ∧
  arrow.oxidantLabelShown = false ∧
  countSubstituent core .aldehyde = 3 ∧
  countSubstituent linker .amine = 2 ∧
  topologyFromConnectivities 3 2 = some .hexagonalOne ∧
  ThreeImineLinkedArms r ∧
  ImineCondensationBalance core.formula linker.formula f

def OxidativeBenzoxazoleClosure
    (arrow : TransformationDescriptor)
    (before after : RepeatUnitDrawing) : Prop :=
  arrow.kind = .oxidation ∧
  arrow.direction = .directed ∧
  arrow.oxidantLabelShown = true ∧
  ThreeBisBenzoxazoleLinkers after ∧
  SameHeavyAtomSites before after ∧
  HasCarbonNitrogenDoubleBond after ∧
  ¬ HasImineMotif after ∧
  (∀ a : Fin 3,
    before.atoms (.nearArmHydrogen a) ≠ none ∧
    after.atoms (.nearArmHydrogen a) = none ∧
    before.atoms (.linkerOxygenHydrogen a 0) ≠ none ∧
    after.atoms (.linkerOxygenHydrogen a 0) = none ∧
    before.atoms (.linkerOxygenHydrogen a 1) ≠ none ∧
    after.atoms (.linkerOxygenHydrogen a 1) = none) ∧
  HydrogenOnlyLoss cof3Formula cof4Formula 6

def BetaKetoEnamineTautomerization
    (arrow : TransformationDescriptor)
    (before after : RepeatUnitDrawing) : Prop :=
  arrow.kind = .ketoEnamineIsomerization ∧
  arrow.direction = .irreversible ∧
  arrow.oxidantLabelShown = false ∧
  ThreeBetaKetoEnamineArms after ∧
  ¬ HasCarbonNitrogenDoubleBond after ∧
  cof6Formula = cof5Formula ∧
  (∀ a : Fin 3,
    before.atoms (.coreOxygenHydrogen a) ≠ none ∧
    after.atoms (.coreOxygenHydrogen a) = none ∧
    before.atoms (.linkerNitrogenHydrogen a 0) = none ∧
    after.atoms (.linkerNitrogenHydrogen a 0) ≠ none ∧
    HasBond before (.coreCarbon (alternatingCorePosition a)) (.coreOxygen a) .single ∧
    HasBond after (.coreCarbon (alternatingCorePosition a)) (.coreOxygen a) .double ∧
    HasBond before (.nearArmCarbon a) (.linkerNitrogen a 0) .double ∧
    HasBond after (.nearArmCarbon a) (.linkerNitrogen a 0) .single)

def Cof3Specification (r : RepeatUnitDrawing) : Prop :=
  CommonRepeatAudit r cof3Formula ∧
  ImineCondensationProduct triformylbenzene diaminoDihydroxybenzene
    cof3FormationArrow r cof3Formula ∧
  OrthoHydroxyGroupsOnLinker r ∧
  CompatibleWithImineStretch r (sourceImineStretch .cof3) ∧
  (∀ a : Fin 3,
    r.hydrogenBond a =
      some (.linkerOxygenHydrogen a 0, .linkerNitrogen a 0))

def Cof4Specification (r : RepeatUnitDrawing) : Prop :=
  CommonRepeatAudit r cof4Formula ∧
  OxidativeBenzoxazoleClosure cof3ToCof4Arrow cof3RepeatUnit r ∧
  CompatibleWithImineStretch r (sourceImineStretch .cof4)

def Cof5Specification (r : RepeatUnitDrawing) : Prop :=
  CommonRepeatAudit r cof5Formula ∧
  ImineCondensationProduct triformylphloroglucinol paraPhenylenediamine
    cof5FormationArrow r cof5Formula ∧
  CoreHydroxyGroups r ∧
  HasImineMotif r ∧
  CompatibleWithImineStretch r (sourceImineStretch .cof5) ∧
  (∀ a : Fin 3,
    r.hydrogenBond a =
      some (.coreOxygenHydrogen a, .linkerNitrogen a 0))

def Cof6Specification (r : RepeatUnitDrawing) : Prop :=
  CommonRepeatAudit r cof6Formula ∧
  BetaKetoEnamineTautomerization cof5ToCof6Arrow cof5RepeatUnit r ∧
  CompatibleWithImineStretch r (sourceImineStretch .cof6) ∧
  (∀ a : Fin 3,
    r.hydrogenBond a =
      some (.linkerNitrogenHydrogen a 0, .coreOxygen a))

/- The page-3 topology prerequisite is re-derived locally from the two
connectivities visible in the page-4 precursor schemes. -/
theorem relevantPreviousPartTopology :
    topologyFromConnectivities 3 2 = some .hexagonalOne := by
  decide

theorem cof3CondensationLedger :
    ImineCondensationBalance
      triformylbenzene.formula diaminoDihydroxybenzene.formula cof3Formula := by
  intro e
  cases e <;>
    norm_num [ImineCondensationBalance, triformylbenzene,
      diaminoDihydroxybenzene, cof3Formula, waterFormula,
      MolecularFormula.count]

theorem cof5CondensationLedger :
    ImineCondensationBalance
      triformylphloroglucinol.formula paraPhenylenediamine.formula cof5Formula := by
  intro e
  cases e <;>
    norm_num [ImineCondensationBalance, triformylphloroglucinol,
      paraPhenylenediamine, cof5Formula, waterFormula,
      MolecularFormula.count]

theorem cof4HydrogenLedger : HydrogenOnlyLoss cof3Formula cof4Formula 6 := by
  norm_num [HydrogenOnlyLoss, cof3Formula, cof4Formula]

theorem cof6FormulaPreserved : cof6Formula = cof5Formula := by
  rfl

/- `InteriorValenceValid` quantifies over every possible atom descriptor, while
the drawing stores at most one descriptor at a site.  This finite check is an
equivalent proof interface for concrete drawings and keeps the exhaustive
calculation independent of irrelevant descriptors. -/
private instance (s : LocalSite) : Decidable (IsNeighbourInterface s) := by
  cases s <;> simp only [IsNeighbourInterface] <;> infer_instance

attribute [local instance] Fintype.decidableForallFintype

set_option maxRecDepth 100000

private def InteriorValenceAt (r : RepeatUnitDrawing) (s : LocalSite) : Prop :=
  match r.atoms s with
  | none => True
  | some a => ¬ IsNeighbourInterface s →
      bondValenceAt r s = expectedNeutralValence a.element

private instance (r : RepeatUnitDrawing) (s : LocalSite) :
    Decidable (InteriorValenceAt r s) := by
  unfold InteriorValenceAt
  split <;> infer_instance

private def InteriorValenceCheck (r : RepeatUnitDrawing) : Prop :=
  ∀ s : LocalSite, InteriorValenceAt r s

private theorem interiorValenceValid_of_check (r : RepeatUnitDrawing)
    (h : InteriorValenceCheck r) : InteriorValenceValid r := by
  intro s a hs hInterior
  have hAtSite := h s
  unfold InteriorValenceAt at hAtSite
  rw [hs] at hAtSite
  exact hAtSite hInterior

private theorem repeatUnit_neutralAndRadicalFree (k : CofKind) :
    NeutralAndRadicalFree (repeatUnit k) := by
  intro s a hs
  change atomAt k s = some a at hs
  unfold atomAt at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst a
    exact ⟨rfl, rfl⟩
  · simp at hs

private theorem repeatUnit_bondsJoinPresentAtoms (k : CofKind) :
    BondsJoinPresentAtoms (repeatUnit k) := by
  intro x y order hBond
  change bondOrder k x y = some order at hBond
  change atomAt k x ≠ none ∧ atomAt k y ≠ none
  unfold bondOrder at hBond
  split at hBond
  · simp at hBond
  · constructor <;> unfold atomAt <;> split <;> simp_all

private theorem commonRepeatAudit_of_checks (k : CofKind) (f : MolecularFormula)
    (hFormula : FormulaMatches (repeatUnit k) f)
    (hValence : InteriorValenceValid (repeatUnit k))
    (hBonds : BondsJoinPresentAtoms (repeatUnit k)) :
    CommonRepeatAudit (repeatUnit k) f := by
  refine ⟨rfl, rfl, rfl, ?_, hFormula, hValence, hBonds,
    repeatUnit_neutralAndRadicalFree k, ?_⟩
  · intro a
    rfl
  · intro s
    rfl

private theorem cof3_commonRepeatAudit :
    CommonRepeatAudit (repeatUnit .cof3) cof3Formula := by
  apply commonRepeatAudit_of_checks
  · unfold FormulaMatches
    decide +kernel
  · apply interiorValenceValid_of_check
    unfold InteriorValenceCheck
    decide +kernel
  · exact repeatUnit_bondsJoinPresentAtoms .cof3

private theorem cof4_commonRepeatAudit :
    CommonRepeatAudit (repeatUnit .cof4) cof4Formula := by
  apply commonRepeatAudit_of_checks
  · unfold FormulaMatches
    decide +kernel
  · apply interiorValenceValid_of_check
    unfold InteriorValenceCheck
    decide +kernel
  · exact repeatUnit_bondsJoinPresentAtoms .cof4

private theorem cof5_commonRepeatAudit :
    CommonRepeatAudit (repeatUnit .cof5) cof5Formula := by
  apply commonRepeatAudit_of_checks
  · unfold FormulaMatches
    decide +kernel
  · apply interiorValenceValid_of_check
    unfold InteriorValenceCheck
    decide +kernel
  · exact repeatUnit_bondsJoinPresentAtoms .cof5

private theorem cof6_commonRepeatAudit :
    CommonRepeatAudit (repeatUnit .cof6) cof6Formula := by
  apply commonRepeatAudit_of_checks
  · unfold FormulaMatches
    decide +kernel
  · apply interiorValenceValid_of_check
    unfold InteriorValenceCheck
    decide +kernel
  · exact repeatUnit_bondsJoinPresentAtoms .cof6

/-! The four concrete output carriers requested by the question.  Their later
proofs must establish the full atom/bond/valence/boundary specifications above;
the candidates do not occur in any premise. -/

theorem cof3_result : Cof3Specification cof3RepeatUnit := by
  change Cof3Specification (repeatUnit .cof3)
  refine ⟨cof3_commonRepeatAudit, ?_, ?_, ?_, ?_⟩
  · unfold ImineCondensationProduct ThreeImineLinkedArms
      ImineCondensationBalance HasBond
    decide +kernel
  · unfold OrthoHydroxyGroupsOnLinker HasBond
    decide +kernel
  · unfold CompatibleWithImineStretch sourceImineStretch HasImineMotif HasBond
    decide +kernel
  · intro a
    rfl

theorem cof4_result : Cof4Specification cof4RepeatUnit := by
  change Cof4Specification (repeatUnit .cof4)
  refine ⟨cof4_commonRepeatAudit, ?_, ?_⟩
  · unfold OxidativeBenzoxazoleClosure ThreeBisBenzoxazoleLinkers
      SameHeavyAtomSites HasCarbonNitrogenDoubleBond HasImineMotif HasBond
      HydrogenOnlyLoss
    decide +kernel
  · unfold CompatibleWithImineStretch sourceImineStretch HasImineMotif HasBond
    decide +kernel

theorem cof5_result : Cof5Specification cof5RepeatUnit := by
  change Cof5Specification (repeatUnit .cof5)
  refine ⟨cof5_commonRepeatAudit, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ImineCondensationProduct ThreeImineLinkedArms
      ImineCondensationBalance HasBond
    decide +kernel
  · unfold CoreHydroxyGroups HasBond
    decide +kernel
  · unfold HasImineMotif HasBond
    decide +kernel
  · trivial
  · intro a
    rfl

theorem cof6_result : Cof6Specification cof6RepeatUnit := by
  change Cof6Specification (repeatUnit .cof6)
  refine ⟨cof6_commonRepeatAudit, ?_, ?_, ?_⟩
  · unfold BetaKetoEnamineTautomerization ThreeBetaKetoEnamineArms
      HasCarbonNitrogenDoubleBond HasBond
    decide +kernel
  · unfold CompatibleWithImineStretch sourceImineStretch HasImineMotif HasBond
    decide +kernel
  · intro a
    rfl

/-- Raw multi-output contract: all four requested repeat drawings and their
source-to-structure derivations. -/
def RawResult : Prop :=
  Cof3Specification cof3RepeatUnit ∧
  Cof4Specification cof4RepeatUnit ∧
  Cof5Specification cof5RepeatUnit ∧
  Cof6Specification cof6RepeatUnit

/-- Exact-symbolic reporting does not round or otherwise modify a structure. -/
def ReportedResult : Prop := RawResult

theorem raw_result : RawResult := by
  exact ⟨cof3_result, cof4_result, cof5_result, cof6_result⟩

theorem reported_result : ReportedResult := by
  exact raw_result

end IChO2026Problems.T3A4
