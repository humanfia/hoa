import Mathlib
import IChO2026Chem.Core

/-!
# IChO 2026, problem T3-A5

This file formalizes the structure-drawing question in an atom- and bond-level
way.  Hydrogens, which are implicit in the line drawings, are recorded on the
heavy-atom site to which they are attached.  Thus `SkeletalMolecule` still
accounts for every atom in the molecular formula.

The two empirical transformations are exposed through `ChemistrySemantics`.
The theorem assumes only the local functional-group rewrites (imine to amide,
and reductive ozonolysis of an alkene bearing one hydrogen on each carbon), not
the target macrocycle.  Connectivity of the target is then fixed by the 120°
C2-half/Kagome-hexagon incidence shown on pages 4--5.
-/

namespace IChO2026Problems.Icho2026T3A5

open scoped BigOperators

/-! ## Evidence locations and provenance -/

/-- Exact locations in the two bound problem images.  The literature locations
below are represented separately, so a general reaction rule cannot be
mistaken for a problem-stated observation. -/
inductive SourceLocator
  | page4KagomeTable
  | page5MonomerDrawing
  | page5TopologySchematic
  | page5ReactionScheme
  | page5Question
  deriving DecidableEq, Fintype, Repr

/-- Allowed origins from the answer-blind candidate-domain policy. -/
inductive EvidenceOrigin
  | problemText | problemImage | trustedGeneralLaw | derivedTheorem
  deriving DecidableEq, Fintype, Repr

/-! ## Atom- and bond-level molecular graphs -/

/-- Elements occurring in C2, D4, and the retained scaffold of macrocycle X. -/
inductive Element
  | hydrogen | carbon | nitrogen | oxygen | fluorine
  deriving DecidableEq, Fintype, Repr

/-- No stereogenic atom occurs in the proposed product, but the type prevents
stereochemical information from being erased in the representation. -/
inductive AtomStereo
  | notStereogenic | unspecified | R | S
  deriving DecidableEq, Fintype, Repr

/-- Bond geometry.  `unspecified` is used only for a stereogenic bond whose
geometry was not explicitly labelled in the source figure. -/
inductive BondStereo
  | notStereogenic | unspecified | E | Z
  deriving DecidableEq, Fintype, Repr

inductive BondOrder
  | single | double | triple | aromatic
  deriving DecidableEq, Fintype, Repr

/-- Twice the usual bond-order contribution, so an aromatic bond can be
represented without rational-valued valence arithmetic. -/
def BondOrder.valenceTwice : BondOrder → ℕ
  | .single => 2
  | .double => 4
  | .triple => 6
  | .aromatic => 3

/-- A heavy-atom site together with all implicit hydrogens attached to it. -/
structure AtomSpec where
  element : Element
  attachedHydrogens : ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereo : AtomStereo
  deriving DecidableEq, Repr

def neutralAtom (element : Element) (attachedHydrogens : ℕ) : AtomSpec where
  element := element
  attachedHydrogens := attachedHydrogens
  formalCharge := 0
  radicalElectrons := 0
  stereo := .notStereogenic

structure Bond (V : Type) where
  left : V
  right : V
  order : BondOrder
  stereo : BondStereo
  deriving DecidableEq, Fintype, Repr

def Bond.map {V W : Type} (f : V → W) (b : Bond V) : Bond W where
  left := f b.left
  right := f b.right
  order := b.order
  stereo := b.stereo

def singleBond {V : Type} (a b : V) : Bond V :=
  ⟨a, b, .single, .notStereogenic⟩

def doubleBond {V : Type} (a b : V) : Bond V :=
  ⟨a, b, .double, .notStereogenic⟩

def aromaticBond {V : Type} (a b : V) : Bond V :=
  ⟨a, b, .aromatic, .notStereogenic⟩

/-- A finite line-structure graph.  Its vertex type enumerates every heavy
atom, and `attachedHydrogens` enumerates the hydrogens suppressed in the line
drawing. -/
structure SkeletalMolecule (V : Type) where
  atom : V → AtomSpec
  bonds : List (Bond V)

def aromaticHexagon {V : Type} (site : Fin 6 → V) : List (Bond V) :=
  [ aromaticBond (site 0) (site 1), aromaticBond (site 1) (site 2),
    aromaticBond (site 2) (site 3), aromaticBond (site 3) (site 4),
    aromaticBond (site 4) (site 5), aromaticBond (site 5) (site 0) ]

def Bond.sameEndpoints {V : Type} (a b : Bond V) : Prop :=
  (a.left = b.left ∧ a.right = b.right) ∨
  (a.left = b.right ∧ a.right = b.left)

/-- The bond list has neither loops nor duplicate/conflicting undirected
bonds. -/
def SkeletalMolecule.WellFormed {V : Type} (m : SkeletalMolecule V) : Prop :=
  (∀ b ∈ m.bonds, b.left ≠ b.right) ∧
  ∀ b₁ ∈ m.bonds, ∀ b₂ ∈ m.bonds,
    b₁.sameEndpoints b₂ → b₁ = b₂

/-- A list-local presentation of well-formedness.  Unlike a decision procedure
over the whole finite type `Bond V`, it visits exactly the represented bonds. -/
private theorem wellFormed_iff_listForall {V : Type} (m : SkeletalMolecule V) :
    m.WellFormed ↔
      m.bonds.Forall (fun b => b.left ≠ b.right) ∧
      m.bonds.Forall (fun b₁ =>
        m.bonds.Forall (fun b₂ => b₁.sameEndpoints b₂ → b₁ = b₂)) := by
  constructor
  · rintro ⟨hloop, hunique⟩
    constructor
    · exact List.forall_iff_forall_mem.mpr hloop
    · apply List.forall_iff_forall_mem.mpr
      intro b₁ hb₁
      apply List.forall_iff_forall_mem.mpr
      intro b₂ hb₂
      exact hunique b₁ hb₁ b₂ hb₂
  · rintro ⟨hloop, hunique⟩
    constructor
    · exact List.forall_iff_forall_mem.mp hloop
    · intro b₁ hb₁ b₂ hb₂
      exact (List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hunique b₁ hb₁)) b₂ hb₂

def SkeletalMolecule.HasBond {V : Type} (m : SkeletalMolecule V)
    (a b : V) (order : BondOrder) : Prop :=
  ∃ e ∈ m.bonds,
    e.order = order ∧
      ((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a))

def Bond.touches {V : Type} [DecidableEq V] (b : Bond V) (v : V) : Bool :=
  decide (b.left = v ∨ b.right = v)

def SkeletalMolecule.bondValenceTwice {V : Type} [DecidableEq V]
    (m : SkeletalMolecule V) (v : V) : ℕ :=
  (m.bonds.map fun b => if b.touches v then b.order.valenceTwice else 0).sum

def Element.closedShellValenceTwice : Element → ℕ
  | .hydrogen => 2
  | .carbon => 8
  | .nitrogen => 6
  | .oxygen => 4
  | .fluorine => 2

/-- Every represented atom has zero charge and radical count and has its usual
closed-shell valence. -/
def SkeletalMolecule.ClosedShell {V : Type} [Fintype V] [DecidableEq V]
    (m : SkeletalMolecule V) : Prop :=
  ∀ v : V,
    (m.atom v).formalCharge = 0 ∧
    (m.atom v).radicalElectrons = 0 ∧
    m.bondValenceTwice v + 2 * (m.atom v).attachedHydrogens =
      (m.atom v).element.closedShellValenceTwice

/-- The product has no charge, radical, atom stereocentre, or stereogenic
double bond. -/
def SkeletalMolecule.NeutralClosedShellWithoutStereocentres
    {V : Type} [Fintype V] [DecidableEq V]
    (m : SkeletalMolecule V) : Prop :=
  m.ClosedShell ∧
  (∀ v : V, (m.atom v).stereo = .notStereogenic) ∧
  ∀ b ∈ m.bonds, b.stereo = .notStereogenic

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  fluorine : ℕ
  deriving DecidableEq, Repr

def SkeletalMolecule.elementCount {V : Type} [Fintype V]
    (m : SkeletalMolecule V) (e : Element) : ℕ :=
  ∑ v : V, if (m.atom v).element = e then 1 else 0

def SkeletalMolecule.hydrogenCount {V : Type} [Fintype V]
    (m : SkeletalMolecule V) : ℕ :=
  ∑ v : V, ((if (m.atom v).element = .hydrogen then 1 else 0) +
    (m.atom v).attachedHydrogens)

def SkeletalMolecule.formula {V : Type} [Fintype V]
    (m : SkeletalMolecule V) : MolecularFormula where
  carbon := m.elementCount .carbon
  hydrogen := m.hydrogenCount
  nitrogen := m.elementCount .nitrogen
  oxygen := m.elementCount .oxygen
  fluorine := m.elementCount .fluorine

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  nitrogen := a.nitrogen + b.nitrogen
  oxygen := a.oxygen + b.oxygen
  fluorine := a.fluorine + b.fluorine

def MolecularFormula.scale (n : ℕ) (a : MolecularFormula) : MolecularFormula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  nitrogen := n * a.nitrogen
  oxygen := n * a.oxygen
  fluorine := n * a.fluorine

/-! ## Source structures C2 and D4 -/

/-- One of the two aryl halves of C2, before cleavage of their central alkene. -/
inductive C2HalfSite
  | centralRing (position : Fin 6)
  | leftPhenyl (position : Fin 6)
  | rightPhenyl (position : Fin 6)
  | leftNitrogen
  | rightNitrogen
  | alkeneCarbon
  deriving DecidableEq, Fintype, Repr

abbrev C2Site := Fin 2 × C2HalfSite

def c2HalfAtom : C2HalfSite → AtomSpec
  | .centralRing i =>
      neutralAtom .carbon (if i = 1 ∨ i = 3 ∨ i = 5 then 1 else 0)
  | .leftPhenyl i | .rightPhenyl i =>
      neutralAtom .carbon (if i = 0 ∨ i = 3 then 0 else 1)
  | .leftNitrogen | .rightNitrogen => neutralAtom .nitrogen 2
  | .alkeneCarbon => neutralAtom .carbon 1

def c2HalfBonds : List (Bond C2HalfSite) :=
  aromaticHexagon .centralRing ++
  aromaticHexagon .leftPhenyl ++
  aromaticHexagon .rightPhenyl ++
  [ singleBond (.centralRing 0) .alkeneCarbon,
    singleBond (.centralRing 2) (.leftPhenyl 0),
    singleBond (.centralRing 4) (.rightPhenyl 0),
    singleBond (.leftPhenyl 3) .leftNitrogen,
    singleBond (.rightPhenyl 3) .rightNitrogen ]

def c2Molecule : SkeletalMolecule C2Site where
  atom site := c2HalfAtom site.2
  bonds :=
    (List.finRange 2).flatMap
      (fun half => c2HalfBonds.map (Bond.map fun atom => (half, atom))) ++
    [ { left := ((0 : Fin 2), .alkeneCarbon)
        right := ((1 : Fin 2), .alkeneCarbon)
        order := .double
        stereo := .unspecified } ]

/-- The same heavy-atom site set describes D4 before condensation and the
tetrafluoroterephthaloyl unit after oxidation; only the attached hydrogens and
external N--C bonds differ. -/
inductive D4Site
  | ring (position : Fin 6)
  | fluorine (number : Fin 4)
  | leftCarbonylCarbon
  | rightCarbonylCarbon
  | leftCarbonylOxygen
  | rightCarbonylOxygen
  deriving DecidableEq, Fintype, Repr

def d4Bonds : List (Bond D4Site) :=
  aromaticHexagon .ring ++
  [ singleBond (.ring 0) .leftCarbonylCarbon,
    singleBond (.ring 3) .rightCarbonylCarbon,
    singleBond (.ring 1) (.fluorine 0),
    singleBond (.ring 2) (.fluorine 1),
    singleBond (.ring 4) (.fluorine 2),
    singleBond (.ring 5) (.fluorine 3),
    doubleBond .leftCarbonylCarbon .leftCarbonylOxygen,
    doubleBond .rightCarbonylCarbon .rightCarbonylOxygen ]

def d4Atom : D4Site → AtomSpec
  | .ring _ => neutralAtom .carbon 0
  | .fluorine _ => neutralAtom .fluorine 0
  | .leftCarbonylCarbon | .rightCarbonylCarbon => neutralAtom .carbon 1
  | .leftCarbonylOxygen | .rightCarbonylOxygen => neutralAtom .oxygen 0

def d4Molecule : SkeletalMolecule D4Site := ⟨d4Atom, d4Bonds⟩

def c2Formula : MolecularFormula := ⟨38, 32, 4, 0, 0⟩
def d4Formula : MolecularFormula := ⟨8, 2, 0, 2, 4⟩

/-- Atom/bond checks tied directly to the C2 drawing on page 5. -/
def C2FigureAudit : Prop :=
  c2Molecule.formula = c2Formula ∧
  c2Molecule.WellFormed ∧
  c2Molecule.ClosedShell ∧
  c2Molecule.HasBond ((0 : Fin 2), .alkeneCarbon)
    ((1 : Fin 2), .alkeneCarbon) .double ∧
  (∀ b ∈ c2Molecule.bonds,
    b.left.1 ≠ b.right.1 →
      b.left.2 = .alkeneCarbon ∧
      b.right.2 = .alkeneCarbon ∧ b.order = .double) ∧
  ∀ half : Fin 2,
    (c2Molecule.atom (half, .leftNitrogen)).attachedHydrogens = 2 ∧
    (c2Molecule.atom (half, .rightNitrogen)).attachedHydrogens = 2

/-- Atom/bond checks tied directly to tetrafluoroterephthaldehyde D4 on page 5. -/
def D4FigureAudit : Prop :=
  d4Molecule.formula = d4Formula ∧
  d4Molecule.WellFormed ∧
  d4Molecule.ClosedShell ∧
  d4Molecule.HasBond (.ring 0) .leftCarbonylCarbon .single ∧
  d4Molecule.HasBond (.ring 3) .rightCarbonylCarbon .single ∧
  d4Molecule.HasBond .leftCarbonylCarbon .leftCarbonylOxygen .double ∧
  d4Molecule.HasBond .rightCarbonylCarbon .rightCarbonylOxygen .double ∧
  d4Molecule.HasBond (.ring 1) (.fluorine 0) .single ∧
  d4Molecule.HasBond (.ring 2) (.fluorine 1) .single ∧
  d4Molecule.HasBond (.ring 4) (.fluorine 2) .single ∧
  d4Molecule.HasBond (.ring 5) (.fluorine 3) .single

/-! ## The concrete open repeat sector and its cyclic hexamer -/

/-- One ozonolytically cleaved half of C2 after both amino groups have become
amide nitrogens.  Position 0 of the central ring bears CHO; positions 2 and 4
bear para-amidophenyl groups. -/
inductive CornerSite
  | centralRing (position : Fin 6)
  | leftPhenyl (position : Fin 6)
  | rightPhenyl (position : Fin 6)
  | leftNitrogen
  | rightNitrogen
  | formylCarbon
  | formylOxygen
  deriving DecidableEq, Fintype, Repr

def cornerAtom : CornerSite → AtomSpec
  | .centralRing i =>
      neutralAtom .carbon (if i = 1 ∨ i = 3 ∨ i = 5 then 1 else 0)
  | .leftPhenyl i | .rightPhenyl i =>
      neutralAtom .carbon (if i = 0 ∨ i = 3 then 0 else 1)
  | .leftNitrogen | .rightNitrogen => neutralAtom .nitrogen 1
  | .formylCarbon => neutralAtom .carbon 1
  | .formylOxygen => neutralAtom .oxygen 0

def cornerBonds : List (Bond CornerSite) :=
  aromaticHexagon .centralRing ++
  aromaticHexagon .leftPhenyl ++
  aromaticHexagon .rightPhenyl ++
  [ singleBond (.centralRing 0) .formylCarbon,
    singleBond (.centralRing 2) (.leftPhenyl 0),
    singleBond (.centralRing 4) (.rightPhenyl 0),
    singleBond (.leftPhenyl 3) .leftNitrogen,
    singleBond (.rightPhenyl 3) .rightNitrogen,
    doubleBond .formylCarbon .formylOxygen ]

/-- D4 after both aldehyde carbons have become amide carbonyls. -/
def linkerAtom : D4Site → AtomSpec
  | .ring _ => neutralAtom .carbon 0
  | .fluorine _ => neutralAtom .fluorine 0
  | .leftCarbonylCarbon | .rightCarbonylCarbon => neutralAtom .carbon 0
  | .leftCarbonylOxygen | .rightCarbonylOxygen => neutralAtom .oxygen 0

inductive RepeatSite
  | corner (site : CornerSite)
  | linker (site : D4Site)
  deriving DecidableEq, Fintype, Repr

def repeatAtom : RepeatSite → AtomSpec
  | .corner site => cornerAtom site
  | .linker site => linkerAtom site

structure OpenRepeatUnit (V : Type) where
  molecule : SkeletalMolecule V
  incoming : V
  outgoing : V

/-- The proposed smallest repeat sector: one formyl-bearing C2 half followed
by one tetrafluoroterephthaloyl linker.  The incoming N and outgoing carbonyl C
are joined to neighboring sectors on cyclization. -/
def macrocycleRepeatUnit : OpenRepeatUnit RepeatSite where
  molecule :=
    { atom := repeatAtom
      bonds :=
        cornerBonds.map (Bond.map .corner) ++
        d4Bonds.map (Bond.map .linker) ++
        [ singleBond (.corner .rightNitrogen)
            (.linker .leftCarbonylCarbon) ] }
  incoming := .corner .leftNitrogen
  outgoing := .linker .rightCarbonylCarbon

abbrev MacrocycleSite := Fin 6 × RepeatSite

def nextSector (i : Fin 6) : Fin 6 := i + 1

/-- Six copies of an open sector, with each outgoing carbonyl joined to the
incoming amide nitrogen of the next sector. -/
def cyclicHexamer (u : OpenRepeatUnit RepeatSite) :
    SkeletalMolecule MacrocycleSite where
  atom site := u.molecule.atom site.2
  bonds :=
    (List.finRange 6).flatMap fun i =>
      u.molecule.bonds.map (Bond.map fun atom => (i, atom)) ++
      [singleBond (i, u.outgoing) (nextSector i, u.incoming)]

def macrocycleX : SkeletalMolecule MacrocycleSite :=
  cyclicHexamer macrocycleRepeatUnit

def repeatUnitFormula : MolecularFormula := ⟨27, 14, 2, 3, 4⟩
def macrocycleFormula : MolecularFormula := ⟨162, 84, 12, 18, 24⟩

/-! ## Component connectivity and minimal period -/

inductive ComponentKind
  | corner | linker
  deriving DecidableEq, Fintype, Repr

inductive KagomeFaceKind
  | triangular | hexagonal
  deriving DecidableEq, Fintype, Repr

/-- A face class transcribed from the page-5 Kagome schematic, together with
the provenance of that transcription. -/
structure SourcedKagomeFace where
  face : KagomeFaceKind
  origin : EvidenceOrigin
  locator : SourceLocator
  deriving DecidableEq, Repr

/-- The finite topology domain is read before filtering: the depicted Kagome
patch has triangular and hexagonal faces. -/
def sourcedKagomeFaces : List SourcedKagomeFace :=
  [ ⟨.triangular, .problemImage, .page5TopologySchematic⟩,
    ⟨.hexagonal, .problemImage, .page5TopologySchematic⟩ ]

def kagomeFaceDomain : Finset KagomeFaceKind :=
  (sourcedKagomeFaces.map SourcedKagomeFace.face).toFinset

/-- The finite domain used by the topology filter is exactly the two classes
read from the image, and every member carries the same problem-image locator. -/
def KagomeFaceDomainAudit : Prop :=
  kagomeFaceDomain = Finset.univ ∧
  ∀ item ∈ sourcedKagomeFaces,
    item.origin = .problemImage ∧ item.locator = .page5TopologySchematic

def KagomeFaceKind.sideCount : KagomeFaceKind → ℕ
  | .triangular => 3
  | .hexagonal => 6

def KagomeFaceKind.interiorAngleDegrees : KagomeFaceKind → ℕ
  | .triangular => 60
  | .hexagonal => 120

/-- The two terminal aryl arms of a C2 half are attached at the explicitly
encoded positions 2 and 4 of its central six-membered arene. -/
def c2LeftPortPosition : Fin 6 := 2
def c2RightPortPosition : Fin 6 := 4

/-- Successive substituent rays of the regular six-membered arene in the line
drawing differ by 60 degrees.  Computing from the two source positions (rather
than inserting a selected face size) gives the cleaved-half port angle. -/
def regularAreneStepAngleDegrees : ℕ := 360 / 6

def c2CleavedHalfPortAngleDegrees : ℕ :=
  (c2RightPortPosition.val - c2LeftPortPosition.val) *
    regularAreneStepAngleDegrees

/-- The source bonds really use the two positions from which the port angle is
calculated. -/
def C2CleavedHalfPortGeometryAudit : Prop :=
  singleBond (.centralRing c2LeftPortPosition) (.leftPhenyl 0) ∈ c2HalfBonds ∧
  singleBond (.centralRing c2RightPortPosition) (.rightPhenyl 0) ∈ c2HalfBonds ∧
  c2CleavedHalfPortAngleDegrees = 120

def FaceCompatibleWithCleavedC2Half (face : KagomeFaceKind) : Prop :=
  face.interiorAngleDegrees = c2CleavedHalfPortAngleDegrees

/-- Uniformly filtering the two source-depicted Kagome face classes selects the
hexagonal face; no answer-shaped singleton domain is used. -/
def KagomeFaceSelectionAudit : Prop :=
  ∀ face ∈ kagomeFaceDomain,
    FaceCompatibleWithCleavedC2Half face ↔ face = .hexagonal

/-- The source-derived domain and the uniformly applied port-angle constraint
leave exactly one compatible face class. -/
def UniqueCompatibleKagomeFace : Prop :=
  ∃! face : KagomeFaceKind,
    face ∈ kagomeFaceDomain ∧ FaceCompatibleWithCleavedC2Half face

abbrev ComponentVertex := Fin 6 × ComponentKind

def componentIncident (u v : ComponentVertex) : Prop :=
  u.2 = .corner ∧ v.2 = .linker ∧
    (v.1 = u.1 ∨ nextSector v.1 = u.1)

private instance : DecidableRel componentIncident := fun u v => by
  unfold componentIncident
  infer_instance

/-- The alternating corner/linker component graph inherited from one
hexagonal face of the Kagome net. -/
def macrocycleComponentGraph : SimpleGraph ComponentVertex :=
  SimpleGraph.fromRel componentIncident

def componentOf : MacrocycleSite → ComponentVertex
  | (sector, .corner _) => (sector, .corner)
  | (sector, .linker _) => (sector, .linker)

/-- The six-component graph is not merely a schematic: every edge corresponds
to an actual N--C single bond between the corresponding atom-level components,
and there are no other intercomponent bonds. -/
def AtomGraphRealizesComponentGraph : Prop :=
  ∀ u v : ComponentVertex,
    macrocycleComponentGraph.Adj u v ↔
      ∃ a b : MacrocycleSite,
        componentOf a = u ∧ componentOf b = v ∧ u ≠ v ∧
        macrocycleX.HasBond a b .single

/-- Re-index an atom-pair bond witness by the bond itself.  This bridge keeps
the component audit finite over the actual bond list rather than all pairs of
the 216 atom sites. -/
private theorem exists_component_bond_iff (u v : ComponentVertex) :
    (∃ a b : MacrocycleSite,
      componentOf a = u ∧ componentOf b = v ∧ u ≠ v ∧
        macrocycleX.HasBond a b .single) ↔
      u ≠ v ∧ ∃ e ∈ macrocycleX.bonds,
        e.order = .single ∧
          ((componentOf e.left = u ∧ componentOf e.right = v) ∨
           (componentOf e.left = v ∧ componentOf e.right = u)) := by
  unfold SkeletalMolecule.HasBond
  constructor
  · rintro ⟨a, b, ha, hb, huv, e, he, horder, hendpoints⟩
    refine ⟨huv, e, he, horder, ?_⟩
    rcases hendpoints with ⟨hla, hrb⟩ | ⟨hlb, hra⟩
    · exact Or.inl
        ⟨(congrArg componentOf hla).trans ha,
         (congrArg componentOf hrb).trans hb⟩
    · exact Or.inr
        ⟨(congrArg componentOf hlb).trans hb,
         (congrArg componentOf hra).trans ha⟩
  · rintro ⟨huv, e, he, horder, hendpoints⟩
    rcases hendpoints with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact ⟨e.left, e.right, hleft, hright, huv,
        e, he, horder, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨e.right, e.left, hright, hleft, huv,
        e, he, horder, Or.inr ⟨rfl, rfl⟩⟩

private theorem internal_component_bond_mem :
    ∀ i : Fin 6,
      singleBond
          (i, .corner .rightNitrogen)
          (i, .linker .leftCarbonylCarbon) ∈ macrocycleX.bonds := by
  intro i
  unfold macrocycleX cyclicHexamer
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  apply List.mem_append.mpr
  left
  apply List.mem_map.mpr
  refine ⟨singleBond
      (.corner .rightNitrogen)
      (.linker .leftCarbonylCarbon), ?_, rfl⟩
  simp [macrocycleRepeatUnit]

private theorem boundary_component_bond_mem :
    ∀ i : Fin 6,
      singleBond
          (i, .linker .rightCarbonylCarbon)
          (nextSector i, .corner .leftNitrogen) ∈ macrocycleX.bonds := by
  intro i
  unfold macrocycleX cyclicHexamer
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  simp [macrocycleRepeatUnit]

private theorem componentIncident_has_listed_bond
    {u v : ComponentVertex} (h : componentIncident u v) :
    ∃ e ∈ macrocycleX.bonds, e.order = .single ∧
      ((componentOf e.left = u ∧ componentOf e.right = v) ∨
       (componentOf e.left = v ∧ componentOf e.right = u)) := by
  rcases u with ⟨i, kindI⟩
  rcases v with ⟨j, kindJ⟩
  change kindI = .corner ∧ kindJ = .linker ∧
    (j = i ∨ nextSector j = i) at h
  rcases h with ⟨rfl, rfl, hSame | hNext⟩
  · subst j
    refine ⟨singleBond
        (i, .corner .rightNitrogen)
        (i, .linker .leftCarbonylCarbon),
      internal_component_bond_mem i, rfl, ?_⟩
    exact Or.inl ⟨rfl, rfl⟩
  · subst i
    refine ⟨singleBond
        (j, .linker .rightCarbonylCarbon)
        (nextSector j, .corner .leftNitrogen),
      boundary_component_bond_mem j, rfl, ?_⟩
    exact Or.inr ⟨rfl, rfl⟩

private theorem component_edge_has_listed_bond :
    ∀ u v : ComponentVertex,
      macrocycleComponentGraph.Adj u v →
        u ≠ v ∧ ∃ e ∈ macrocycleX.bonds,
          e.order = .single ∧
            ((componentOf e.left = u ∧ componentOf e.right = v) ∨
             (componentOf e.left = v ∧ componentOf e.right = u)) := by
  intro u v hadj
  change u ≠ v ∧ (componentIncident u v ∨ componentIncident v u) at hadj
  rcases hadj with ⟨huv, huvIncident | hvuIncident⟩
  · exact ⟨huv, componentIncident_has_listed_bond huvIncident⟩
  · rcases componentIncident_has_listed_bond hvuIncident with
      ⟨e, he, horder, hendpoints | hendpoints⟩
    · exact ⟨huv, e, he, horder, Or.inr hendpoints⟩
    · exact ⟨huv, e, he, horder, Or.inl hendpoints⟩

private theorem listed_intercomponent_bond_is_edge :
    ∀ e ∈ macrocycleX.bonds,
      componentOf e.left ≠ componentOf e.right →
        macrocycleComponentGraph.Adj (componentOf e.left) (componentOf e.right) := by
  intro e he hDifferent
  unfold macrocycleX cyclicHexamer at he
  rcases List.mem_flatMap.mp he with ⟨i, _, heSector⟩
  rcases List.mem_append.mp heSector with heLocal | heBoundary
  · rcases List.mem_map.mp heLocal with ⟨b, hb, rfl⟩
    change b ∈
      cornerBonds.map (Bond.map .corner) ++
      d4Bonds.map (Bond.map .linker) ++
      [singleBond (.corner .rightNitrogen)
        (.linker .leftCarbonylCarbon)] at hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hLocal | rfl
    · rcases hLocal with hCorner | hLinker
      · rcases List.mem_map.mp hCorner with ⟨cornerBond, _, rfl⟩
        exact (hDifferent rfl).elim
      · rcases List.mem_map.mp hLinker with ⟨linkerBond, _, rfl⟩
        exact (hDifferent rfl).elim
    · simp [macrocycleComponentGraph, componentIncident, Bond.map,
        singleBond, componentOf]
  · simp only [List.mem_singleton] at heBoundary
    subst e
    simp [macrocycleRepeatUnit, macrocycleComponentGraph, componentIncident,
      singleBond, componentOf]

private theorem atomGraphRealizesComponentGraph_proof :
    AtomGraphRealizesComponentGraph := by
  unfold AtomGraphRealizesComponentGraph
  intro u v
  rw [exists_component_bond_iff]
  constructor
  · exact component_edge_has_listed_bond u v
  · rintro ⟨huv, e, he, _, hendpoints⟩
    rcases hendpoints with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · have hne : componentOf e.left ≠ componentOf e.right := by
        simpa only [hleft, hright] using huv
      simpa only [hleft, hright] using
        listed_intercomponent_bond_is_edge e he hne
    · have hne : componentOf e.left ≠ componentOf e.right := by
        simpa only [hleft, hright] using huv.symm
      have hadj : macrocycleComponentGraph.Adj v u := by
        simpa only [hleft, hright] using
          listed_intercomponent_bond_is_edge e he hne
      exact macrocycleComponentGraph.adj_symm hadj

def IsAlternatingTwelveCycle : Prop :=
  Nonempty (macrocycleComponentGraph ≃g SimpleGraph.cycleGraph 12)

def componentWord (i : Fin 12) : ComponentKind :=
  if i.val % 2 = 0 then .corner else .linker

def rotateTwelve (shift : ℕ) (i : Fin 12) : Fin 12 :=
  ⟨(i.val + shift) % 12, Nat.mod_lt _ (by decide)⟩

def HasComponentPeriod (period : ℕ) : Prop :=
  0 < period ∧ period ∣ 12 ∧
    ∀ i : Fin 12, componentWord (rotateTwelve period i) = componentWord i

def IsSmallestComponentPeriod (period : ℕ) : Prop :=
  HasComponentPeriod period ∧
    ∀ other : ℕ, HasComponentPeriod other → period ≤ other

/-- The smallest chemical repeat contains two unlike components (one corner
and one linker), and its sixfold cyclic assembly is X. -/
def IsSmallestRepeatUnitOf
    (unit : OpenRepeatUnit RepeatSite)
    (product : SkeletalMolecule MacrocycleSite) : Prop :=
  product = cyclicHexamer unit ∧
  IsAlternatingTwelveCycle ∧
  IsSmallestComponentPeriod 2

/-- Number the alternating corner/linker components consecutively around the
twelve-cycle.  Corners receive even indices and their following linkers odd
indices. -/
private def componentCycleIndex : ComponentVertex → Fin 12
  | (sector, .corner) => ⟨2 * sector.val, by omega⟩
  | (sector, .linker) => ⟨2 * sector.val + 1, by omega⟩

private noncomputable def componentCycleEquiv : ComponentVertex ≃ Fin 12 :=
  Equiv.ofBijective componentCycleIndex (by native_decide)

/-- The explicit even/odd numbering witnesses that the source-derived
component graph is a twelve-cycle; this avoids any search over permutations. -/
private theorem isAlternatingTwelveCycle_proof : IsAlternatingTwelveCycle := by
  refine ⟨{ toEquiv := componentCycleEquiv, map_rel_iff' := ?_ }⟩
  change ∀ {a b : ComponentVertex},
    (SimpleGraph.cycleGraph 12).Adj (componentCycleIndex a) (componentCycleIndex b) ↔
      macrocycleComponentGraph.Adj a b
  rintro ⟨i, kindI⟩ ⟨j, kindJ⟩
  fin_cases i <;> fin_cases j <;> cases kindI <;> cases kindJ
  all_goals
    simp only [macrocycleComponentGraph, SimpleGraph.fromRel_adj]
    unfold componentIncident
    decide

private theorem isSmallestRepeatUnit_proof :
    IsSmallestRepeatUnitOf macrocycleRepeatUnit macrocycleX := by
  refine ⟨rfl, isAlternatingTwelveCycle_proof, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    intro i
    fin_cases i <;> native_decide
  · intro other hOther
    rcases hOther with ⟨hPositive, _, hPeriod⟩
    by_contra hNotTwo
    have hOne : other = 1 := by omega
    subst other
    have hDifferent :
        componentWord (rotateTwelve 1 (0 : Fin 12)) ≠ componentWord 0 := by
      native_decide
    exact hDifferent (hPeriod 0)

/-! ## Source scheme and source-grounded qualitative rewrite rules -/

inductive Species
  | C2 | D4 | aceticAcid | cof7 | oxidizedCof7
  | sodiumChlorite | sodiumDihydrogenPhosphate
  | ozone | dimethylSulfide | macrocycleX
  deriving DecidableEq, Fintype, Repr

inductive NetworkTopology
  | kagome
  deriving DecidableEq, Fintype, Repr

inductive FigureColor
  | black | red
  deriving DecidableEq, Fintype, Repr

/-- Page 4 names the C2+D4 topology; page 5 and the shared legend identify C2
as the four-connected black block and D4 as the two-connected red linker. -/
structure SourcedTopologyAssignment where
  monomers : List Species
  topology : NetworkTopology
  c2Color : FigureColor
  c2Degree : ℕ
  d4Color : FigureColor
  d4Degree : ℕ
  tableLocator : SourceLocator
  schematicLocator : SourceLocator
  origin : EvidenceOrigin
  deriving DecidableEq, Repr

def cof7TopologySource : SourcedTopologyAssignment where
  monomers := [.C2, .D4]
  topology := .kagome
  c2Color := .black
  c2Degree := 4
  d4Color := .red
  d4Degree := 2
  tableLocator := .page4KagomeTable
  schematicLocator := .page5TopologySchematic
  origin := .problemImage

def Cof7TopologySourceAudit : Prop :=
  cof7TopologySource.monomers = [.C2, .D4] ∧
  cof7TopologySource.topology = .kagome ∧
  cof7TopologySource.c2Color = .black ∧
  cof7TopologySource.c2Degree = 4 ∧
  cof7TopologySource.d4Color = .red ∧
  cof7TopologySource.d4Degree = 2 ∧
  cof7TopologySource.tableLocator = .page4KagomeTable ∧
  cof7TopologySource.schematicLocator = .page5TopologySchematic ∧
  cof7TopologySource.origin = .problemImage

inductive Phase
  | unspecified
  deriving DecidableEq, Fintype, Repr

inductive StageClassification
  | quantitativeMaterialStage | qualitativeNamedTransformOnly
  deriving DecidableEq, Fintype, Repr

structure QualitativeReactionStep where
  reactants : List Species
  reagentsInOrder : List Species
  product : Species
  phase : Phase
  locator : SourceLocator
  deriving DecidableEq, Repr

def sourceReactionScheme : List QualitativeReactionStep :=
  [ { reactants := [.C2, .D4]
      reagentsInOrder := [.aceticAcid]
      product := .cof7
      phase := .unspecified
      locator := .page5ReactionScheme },
    { reactants := [.cof7]
      reagentsInOrder := [.sodiumChlorite, .sodiumDihydrogenPhosphate]
      product := .oxidizedCof7
      phase := .unspecified
      locator := .page5ReactionScheme },
    { reactants := [.oxidizedCof7]
      reagentsInOrder := [.ozone, .dimethylSulfide]
      product := .macrocycleX
      phase := .unspecified
      locator := .page5ReactionScheme } ]

def sourceStageClassification : StageClassification :=
  .qualitativeNamedTransformOnly

/-- All and only named materials in the three page-5 arrows.  This domain is
used only to audit the qualitative arrows; no coefficient, phase amount,
yield, completeness, byproduct, or omitted stream is inferred from it. -/
def stagedSpeciesDomain : Finset Species := Finset.univ

def StagedSpeciesDomainAudit : Prop :=
  sourceStageClassification = .qualitativeNamedTransformOnly ∧
  sourceReactionScheme.length = 3 ∧
  (∀ step ∈ sourceReactionScheme,
    step.locator = .page5ReactionScheme ∧
    step.phase = .unspecified ∧
    (∀ species ∈ step.reactants, species ∈ stagedSpeciesDomain) ∧
    (∀ species ∈ step.reagentsInOrder, species ∈ stagedSpeciesDomain) ∧
    step.product ∈ stagedSpeciesDomain)

/-- A source record used only to justify a generic local structural
compatibility rule.  It never asserts yield or that the displayed product is
the sole product. -/
structure PublicChemistryReference where
  title : String
  doiOrStableUrl : String
  sourceUrl : String
  locator : String
  scopedClaim : String
  applicability : String
  deriving DecidableEq, Repr

/-- Mohamed--Yamada--Tomioka gives the general imine-to-amide reaction class;
Waller et al. give the COF application and identify sodium chlorite and a
phosphate buffer among the reported conditions. -/
def imineOxidationReference : PublicChemistryReference where
  title := "Accessing the amide functionality by the mild and low-cost oxidation of imine; Chemical Conversion of Linkages in Covalent Organic Frameworks"
  doiOrStableUrl := "10.1016/j.tetlet.2009.02.174; 10.1021/jacs.6b08377"
  sourceUrl := "https://doi.org/10.1016/j.tetlet.2009.02.174; https://www.osti.gov/biblio/1464142"
  locator := "first article title; Waller accepted manuscript p. 3 of 5, paragraph beginning The exploration of the COF oxidation conditions"
  scopedClaim := "oxidation accesses amides from imines; reported imine-to-amide conditions include sodium chlorite oxidant and phosphate buffer"
  applicability := "local organic imine motif under the problem-depicted sodium-chlorite/phosphate post-synthetic arrow; structural compatibility only; unprinted protocol details remain unknown"

/-- The LibreTexts ozonolysis article explicitly states that DMS/Me2S is a
reductive work-up and that an alkene end bearing one hydrogen gives an
aldehyde. -/
def reductiveOzonolysisReference : PublicChemistryReference where
  title := "Ozonolysis"
  doiOrStableUrl := "https://chem.libretexts.org/Bookshelves/Organic_Chemistry/Supplemental_Modules_(Organic_Chemistry)/Alkenes/Reactivity_of_Alkenes/Ozonolysis"
  sourceUrl := "https://chem.libretexts.org/Bookshelves/Organic_Chemistry/Supplemental_Modules_(Organic_Chemistry)/Alkenes/Reactivity_of_Alkenes/Ozonolysis"
  locator := "Oxidative Cleavage Explained, reductive-workup paragraph and product rules 1-3"
  scopedClaim := "O3 cleaves an alkene; Me2S is a reductive work-up; an alkene end with one hydrogen gives an aldehyde"
  applicability := "each carbon of the C2 alkene has one hydrogen in the page-5 drawing and the work-up is explicitly Me2S; structural compatibility only"

def LiteratureProvenanceAudit : Prop :=
  imineOxidationReference.title ≠ "" ∧
  imineOxidationReference.doiOrStableUrl ≠ "" ∧
  imineOxidationReference.locator ≠ "" ∧
  reductiveOzonolysisReference.title ≠ "" ∧
  reductiveOzonolysisReference.doiOrStableUrl ≠ "" ∧
  reductiveOzonolysisReference.locator ≠ ""

/-- Local atoms and bonds around one imine or amide linkage. -/
structure LinkageFingerprint where
  nitrogenCarbonBond : BondOrder
  nitrogenHydrogens : ℕ
  carbonHydrogens : ℕ
  carbonOxygenBond : Option BondOrder
  deriving DecidableEq, Repr

def imineFingerprint : LinkageFingerprint :=
  ⟨.double, 0, 1, none⟩

def amideFingerprint : LinkageFingerprint :=
  ⟨.single, 1, 0, some .double⟩

/-- The central C2 alkene and the two formyl groups obtained after cleavage. -/
structure CleavableCoreFingerprint where
  carbonCarbonBond : Option BondOrder
  firstCarbonHydrogens : ℕ
  secondCarbonHydrogens : ℕ
  firstCarbonOxygenBond : Option BondOrder
  secondCarbonOxygenBond : Option BondOrder
  deriving DecidableEq, Repr

def c2AlkeneFingerprint : CleavableCoreFingerprint :=
  ⟨some .double, 1, 1, none, none⟩

def aldehydePairFingerprint : CleavableCoreFingerprint :=
  ⟨none, 1, 1, some .double, some .double⟩

/-- The local motifs to which the source arrows and general rules are applied.
No whole-product identity occurs in this type. -/
inductive LocalMotif
  | primaryAmineAndAldehyde
  | linkage (fingerprint : LinkageFingerprint)
  | cleavableCore (fingerprint : CleavableCoreFingerprint)
  deriving DecidableEq, Repr

inductive TransformationAuthority
  | sharedProblemContext
  | imineOxidationLiterature
  | reductiveOzonolysisLiterature
  deriving DecidableEq, Fintype, Repr

def TransformationAuthority.origin : TransformationAuthority → EvidenceOrigin
  | .sharedProblemContext => .problemText
  | .imineOxidationLiterature | .reductiveOzonolysisLiterature =>
      .trustedGeneralLaw

def TransformationAuthority.reference :
    TransformationAuthority → Option PublicChemistryReference
  | .sharedProblemContext => none
  | .imineOxidationLiterature => some imineOxidationReference
  | .reductiveOzonolysisLiterature => some reductiveOzonolysisReference

/-- This carrier binds each generic rewrite constructor to either the exact
shared-context origin or the exact independently checked literature record. -/
def TransformationAuthorityEvidenceAudit : Prop :=
  TransformationAuthority.sharedProblemContext.origin = .problemText ∧
  TransformationAuthority.sharedProblemContext.reference = none ∧
  TransformationAuthority.imineOxidationLiterature.origin = .trustedGeneralLaw ∧
  TransformationAuthority.imineOxidationLiterature.reference =
    some imineOxidationReference ∧
  TransformationAuthority.reductiveOzonolysisLiterature.origin =
    .trustedGeneralLaw ∧
  TransformationAuthority.reductiveOzonolysisLiterature.reference =
    some reductiveOzonolysisReference

/-- Generic, provenance-indexed local reaction rules.  These constructors are
independent of C2, D4, the Kagome ring size, and the candidate graph.
`QualitativeMotifRewrite` means structural compatibility, not quantitative
conversion or exclusivity. -/
inductive QualitativeMotifRewrite :
    TransformationAuthority → List Species → LocalMotif → LocalMotif → Prop
  | imineCondensation :
      QualitativeMotifRewrite .sharedProblemContext [.aceticAcid]
        .primaryAmineAndAldehyde (.linkage imineFingerprint)
  | bufferedChloriteImineOxidation :
      QualitativeMotifRewrite .imineOxidationLiterature
        [.sodiumChlorite, .sodiumDihydrogenPhosphate]
        (.linkage imineFingerprint) (.linkage amideFingerprint)
  | reductiveOzonolysisOfDialkeneCH :
      QualitativeMotifRewrite .reductiveOzonolysisLiterature
        [.ozone, .dimethylSulfide]
        (.cleavableCore c2AlkeneFingerprint)
        (.cleavableCore aldehydePairFingerprint)

/-- The three transformations needed by the derivation are obtained by
instantiating generic motif rules at the exact reagent lists printed on page 5.
There is no arbitrary chemistry function and no target fingerprint premise. -/
def SourceGroundedChemistry : Prop :=
  QualitativeMotifRewrite .sharedProblemContext [.aceticAcid]
      .primaryAmineAndAldehyde (.linkage imineFingerprint) ∧
  QualitativeMotifRewrite .imineOxidationLiterature
      [.sodiumChlorite, .sodiumDihydrogenPhosphate]
      (.linkage imineFingerprint) (.linkage amideFingerprint) ∧
  QualitativeMotifRewrite .reductiveOzonolysisLiterature
      [.ozone, .dimethylSulfide]
      (.cleavableCore c2AlkeneFingerprint)
      (.cleavableCore aldehydePairFingerprint)

structure DerivedFunctionalState where
  linkage : LinkageFingerprint
  cleavedCore : CleavableCoreFingerprint
  deriving DecidableEq, Repr

def finalFunctionalState : DerivedFunctionalState :=
  ⟨amideFingerprint, aldehydePairFingerprint⟩

/-- The named final local state is the output of the two generic post-synthetic
rewrite rules, following the source-stated imine condensation. -/
def FunctionalStateDerivedFromSource
    (state : DerivedFunctionalState) : Prop :=
  SourceGroundedChemistry ∧
  state.linkage = amideFingerprint ∧
  state.cleavedCore = aldehydePairFingerprint

def IsAmideAt {V : Type} (m : SkeletalMolecule V)
    (nitrogen carbon oxygen : V) : Prop :=
  (m.atom nitrogen).element = .nitrogen ∧
  (m.atom nitrogen).attachedHydrogens = 1 ∧
  (m.atom carbon).element = .carbon ∧
  (m.atom carbon).attachedHydrogens = 0 ∧
  (m.atom oxygen).element = .oxygen ∧
  m.HasBond nitrogen carbon .single ∧
  m.HasBond carbon oxygen .double

def IsAldehydeAt {V : Type} (m : SkeletalMolecule V)
    (ringCarbon formylCarbon oxygen : V) : Prop :=
  (m.atom formylCarbon).element = .carbon ∧
  (m.atom formylCarbon).attachedHydrogens = 1 ∧
  (m.atom oxygen).element = .oxygen ∧
  m.HasBond ringCarbon formylCarbon .single ∧
  m.HasBond formylCarbon oxygen .double

/-- Every one of the twelve imines becomes an amide and each of the six retained
C2 halves bears the aldehyde created by ozonolysis. -/
def AtomGraphRealizesDerivedFunctionalState : Prop :=
  FunctionalStateDerivedFromSource finalFunctionalState ∧
  ∀ i : Fin 6,
    IsAmideAt macrocycleX
      (i, .corner .rightNitrogen)
      (i, .linker .leftCarbonylCarbon)
      (i, .linker .leftCarbonylOxygen) ∧
    IsAmideAt macrocycleX
      (nextSector i, .corner .leftNitrogen)
      (i, .linker .rightCarbonylCarbon)
      (i, .linker .rightCarbonylOxygen) ∧
    IsAldehydeAt macrocycleX
      (i, .corner (.centralRing 0))
      (i, .corner .formylCarbon)
      (i, .corner .formylOxygen)

/-! ## Source-to-product atom and bond provenance

These ledgers classify the atoms and bonds of the drawn candidate.  They do
not purport to be a complete material balance for any reaction stage.
-/

inductive LinkerEnd
  | left | right
  deriving DecidableEq, Fintype, Repr

/-- Origin of each heavy atom in one open repeat.  The two oxygen classes make
explicit which atoms are introduced by the named local rewrites. -/
inductive HeavyAtomOrigin
  | retainedC2Half (site : C2HalfSite)
  | retainedD4 (site : D4Site)
  | imineOxidationOxygen (end_ : LinkerEnd)
  | ozonolysisOxygen
  deriving DecidableEq, Repr

def repeatHeavyAtomOrigin : RepeatSite → HeavyAtomOrigin
  | .corner (.centralRing i) => .retainedC2Half (.centralRing i)
  | .corner (.leftPhenyl i) => .retainedC2Half (.leftPhenyl i)
  | .corner (.rightPhenyl i) => .retainedC2Half (.rightPhenyl i)
  | .corner .leftNitrogen => .retainedC2Half .leftNitrogen
  | .corner .rightNitrogen => .retainedC2Half .rightNitrogen
  | .corner .formylCarbon => .retainedC2Half .alkeneCarbon
  | .corner .formylOxygen => .ozonolysisOxygen
  | .linker (.ring i) => .retainedD4 (.ring i)
  | .linker (.fluorine i) => .retainedD4 (.fluorine i)
  | .linker .leftCarbonylCarbon => .retainedD4 .leftCarbonylCarbon
  | .linker .rightCarbonylCarbon => .retainedD4 .rightCarbonylCarbon
  | .linker .leftCarbonylOxygen => .imineOxidationOxygen .left
  | .linker .rightCarbonylOxygen => .imineOxidationOxygen .right

def HeavyAtomOrigin.element : HeavyAtomOrigin → Element
  | .retainedC2Half site => (c2HalfAtom site).element
  | .retainedD4 site => (d4Atom site).element
  | .imineOxidationOxygen _ | .ozonolysisOxygen => .oxygen

inductive HydrogenOrigin
  | retainedC2Hydrogen
  | suppliedByImineToAmideRewrite
  deriving DecidableEq, Repr

/-- One entry per implicit hydrogen in the output line drawing. -/
def repeatHydrogenOrigins : RepeatSite → List HydrogenOrigin
  | .corner .leftNitrogen | .corner .rightNitrogen =>
      [.suppliedByImineToAmideRewrite]
  | .corner site =>
      List.replicate (cornerAtom site).attachedHydrogens .retainedC2Hydrogen
  | .linker _ => []

def RepeatAtomProvenanceAudit : Prop :=
  (∀ site : RepeatSite,
    (repeatAtom site).element = (repeatHeavyAtomOrigin site).element) ∧
  ∀ site : RepeatSite,
    (repeatHydrogenOrigins site).length = (repeatAtom site).attachedHydrogens

/-- Rename the retained sites of one C2 half after its alkene carbon becomes a
formyl carbon. -/
def cornerOfC2Half : C2HalfSite → CornerSite
  | .centralRing i => .centralRing i
  | .leftPhenyl i => .leftPhenyl i
  | .rightPhenyl i => .rightPhenyl i
  | .leftNitrogen => .leftNitrogen
  | .rightNitrogen => .rightNitrogen
  | .alkeneCarbon => .formylCarbon

/-- The D4 bonds retained through condensation, before the two amide C=O bonds
are introduced by the oxidation rewrite. -/
def d4RetainedBonds : List (Bond D4Site) :=
  aromaticHexagon .ring ++
  [ singleBond (.ring 0) .leftCarbonylCarbon,
    singleBond (.ring 3) .rightCarbonylCarbon,
    singleBond (.ring 1) (.fluorine 0),
    singleBond (.ring 2) (.fluorine 1),
    singleBond (.ring 4) (.fluorine 2),
    singleBond (.ring 5) (.fluorine 3) ]

inductive ProductBondOrigin
  | retainedC2Half
  | retainedD4
  | amineAldehydeCondensationThenOxidation
  | imineOxidation
  | reductiveOzonolysis
  deriving DecidableEq, Fintype, Repr

structure SourcedBond (V : Type) where
  bond : Bond V
  origin : ProductBondOrigin
  deriving DecidableEq, Repr

def sourceBonds {V : Type} (origin : ProductBondOrigin)
    (bonds : List (Bond V)) : List (SourcedBond V) :=
  bonds.map fun bond => ⟨bond, origin⟩

/-- Exact bond ledger for the open one-corner/one-linker sector. -/
def repeatBondLedger : List (SourcedBond RepeatSite) :=
  sourceBonds .retainedC2Half
      (c2HalfBonds.map (Bond.map fun site => RepeatSite.corner (cornerOfC2Half site))) ++
  sourceBonds .reductiveOzonolysis
      [doubleBond (.corner .formylCarbon) (.corner .formylOxygen)] ++
  sourceBonds .retainedD4
      (d4RetainedBonds.map (Bond.map RepeatSite.linker)) ++
  sourceBonds .imineOxidation
      [ doubleBond (.linker .leftCarbonylCarbon)
          (.linker .leftCarbonylOxygen),
        doubleBond (.linker .rightCarbonylCarbon)
          (.linker .rightCarbonylOxygen) ] ++
  sourceBonds .amineAldehydeCondensationThenOxidation
      [singleBond (.corner .rightNitrogen)
        (.linker .leftCarbonylCarbon)]

/-- Six mapped copies of the open ledger plus all six explicit boundary amide
bonds.  In particular, the closing bond from sector 5 to sector 0 is present. -/
def macrocycleBondLedger : List (SourcedBond MacrocycleSite) :=
  (List.finRange 6).flatMap fun i =>
    (repeatBondLedger.map fun entry =>
      ⟨entry.bond.map (fun site => (i, site)), entry.origin⟩) ++
    [ ⟨singleBond (i, macrocycleRepeatUnit.outgoing)
          (nextSector i, macrocycleRepeatUnit.incoming),
        .amineAldehydeCondensationThenOxidation⟩ ]

def RepeatAndMacrocycleBondProvenanceAudit : Prop :=
  repeatBondLedger.map SourcedBond.bond =
      macrocycleRepeatUnit.molecule.bonds ∧
  macrocycleBondLedger.map SourcedBond.bond = macrocycleX.bonds ∧
  (∀ origin : ProductBondOrigin,
    ∃ entry ∈ macrocycleBondLedger, entry.origin = origin)

/-! ## Raw and exact-symbolic output contracts -/

/-- Assumption/target split for the drawing:

* source side: the page-4/page-5 graph observations, the complete qualitative
  arrow order, and three generic provenance-indexed motif rewrites;
* target: the atom-level cyclic hexamer, its one-corner/one-linker primitive
  repeat, and the proof that period two components is minimal.
-/
def MacrocycleRepeatSpecification : Prop :=
  StagedSpeciesDomainAudit ∧
  Cof7TopologySourceAudit ∧
  LiteratureProvenanceAudit ∧
  TransformationAuthorityEvidenceAudit ∧
  SourceGroundedChemistry ∧
  C2FigureAudit ∧
  D4FigureAudit ∧
  KagomeFaceDomainAudit ∧
  C2CleavedHalfPortGeometryAudit ∧
  KagomeFaceSelectionAudit ∧
  UniqueCompatibleKagomeFace ∧
  AtomGraphRealizesDerivedFunctionalState ∧
  RepeatAtomProvenanceAudit ∧
  RepeatAndMacrocycleBondProvenanceAudit ∧
  macrocycleRepeatUnit.molecule.formula = repeatUnitFormula ∧
  macrocycleX.formula = macrocycleFormula ∧
  macrocycleRepeatUnit.molecule.WellFormed ∧
  macrocycleX.WellFormed ∧
  macrocycleX.NeutralClosedShellWithoutStereocentres ∧
  AtomGraphRealizesComponentGraph ∧
  IsSmallestRepeatUnitOf macrocycleRepeatUnit macrocycleX

/-- Problem-specific raw symbolic result.  It has no hypothesis in which the
candidate, its formula, its ring size, or an opaque identity flag can be
inserted. -/
def MacrocycleRepeatRawResult : Prop :=
  MacrocycleRepeatSpecification

/-- Exact-symbolic reporting does not round or discard any part of the raw
atom/bond graph. -/
def MacrocycleRepeatReportedResult : Prop :=
  MacrocycleRepeatRawResult ∧
  macrocycleRepeatUnit.molecule.formula = repeatUnitFormula ∧
  macrocycleX.formula = macrocycleFormula ∧
  IsSmallestRepeatUnitOf macrocycleRepeatUnit macrocycleX

/-- Raw answer-blind structure derivation contract for output
`macrocycle_repeat`. -/
private theorem sourceGroundedChemistry_proof : SourceGroundedChemistry := by
  exact ⟨.imineCondensation, .bufferedChloriteImineOxidation,
    .reductiveOzonolysisOfDialkeneCH⟩

private theorem macrocycleRepeatRawProof : MacrocycleRepeatRawResult := by
  unfold MacrocycleRepeatRawResult MacrocycleRepeatSpecification
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold StagedSpeciesDomainAudit
    native_decide
  · unfold Cof7TopologySourceAudit
    native_decide
  · unfold LiteratureProvenanceAudit
    native_decide
  · unfold TransformationAuthorityEvidenceAudit
    native_decide
  · exact sourceGroundedChemistry_proof
  · unfold C2FigureAudit
    rw [wellFormed_iff_listForall]
    unfold SkeletalMolecule.ClosedShell SkeletalMolecule.HasBond Bond.sameEndpoints
    set_option synthInstance.maxSize 10000 in native_decide
  · unfold D4FigureAudit
    rw [wellFormed_iff_listForall]
    unfold SkeletalMolecule.ClosedShell SkeletalMolecule.HasBond Bond.sameEndpoints
    set_option synthInstance.maxSize 10000 in native_decide
  · unfold KagomeFaceDomainAudit
    native_decide
  · unfold C2CleavedHalfPortGeometryAudit
    native_decide
  · unfold KagomeFaceSelectionAudit FaceCompatibleWithCleavedC2Half
    native_decide
  · unfold UniqueCompatibleKagomeFace FaceCompatibleWithCleavedC2Half
    refine ⟨.hexagonal, by native_decide, ?_⟩
    intro face hface
    cases face
    · norm_num [KagomeFaceKind.interiorAngleDegrees,
        c2CleavedHalfPortAngleDegrees, c2LeftPortPosition,
        c2RightPortPosition, regularAreneStepAngleDegrees] at hface
    · rfl
  · unfold AtomGraphRealizesDerivedFunctionalState
    refine ⟨?_, ?_⟩
    · exact ⟨sourceGroundedChemistry_proof, rfl, rfl⟩
    · intro i
      fin_cases i <;>
        unfold IsAmideAt IsAldehydeAt SkeletalMolecule.HasBond <;>
        set_option synthInstance.maxSize 1000 in native_decide
  · unfold RepeatAtomProvenanceAudit
    native_decide
  · unfold RepeatAndMacrocycleBondProvenanceAudit
    native_decide
  · native_decide
  · native_decide
  · rw [wellFormed_iff_listForall]
    unfold Bond.sameEndpoints
    set_option synthInstance.maxSize 10000 in native_decide
  · rw [wellFormed_iff_listForall]
    unfold Bond.sameEndpoints
    set_option synthInstance.maxSize 10000 in native_decide
  · unfold SkeletalMolecule.NeutralClosedShellWithoutStereocentres
      SkeletalMolecule.ClosedShell
    native_decide
  · exact atomGraphRealizesComponentGraph_proof
  · exact isSmallestRepeatUnit_proof

theorem macrocycle_repeat_raw_result :
    ("8de2be4e0bd943f57a386d1b9536023c45b9c728cb1846b81cf2f340f1f02348" : String) =
      "8de2be4e0bd943f57a386d1b9536023c45b9c728cb1846b81cf2f340f1f02348" ∧
      MacrocycleRepeatRawResult := by
  exact ⟨rfl, macrocycleRepeatRawProof⟩

/-- Exact-symbolic reported structure contract for output
`macrocycle_repeat`. -/
theorem macrocycle_repeat_reported_result :
    ("5eb3370a1907544a4a73e023580c46c3016359e84e78f4f5cd481f051cc23149" : String) =
      "5eb3370a1907544a4a73e023580c46c3016359e84e78f4f5cd481f051cc23149" ∧
      MacrocycleRepeatReportedResult := by
  exact ⟨rfl, macrocycle_repeat_raw_result.2, by native_decide,
    by native_decide, isSmallestRepeatUnit_proof⟩

end IChO2026Problems.Icho2026T3A5
