import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem 9.8

This file formalizes the five requested structures `O`--`S` in the
Sollogoub alpha-cyclodextrin sequence.  A structure is represented by a
labelled heavy-atom graph.  Every hydrogen is stored at its heavy-atom parent,
and `ExpandedAtom` turns those counts into individual hydrogen atoms.  Thus the
model fixes atom identity, bond order, formal charge, radical count, all six
primary-rim boxes, the twelve secondary benzyl ethers, the inter-residue
glycosidic bonds, the shared N/O bridge, and the retained sugar
stereochemistry.

The depicted arrows are used only as `qualitativeNamedTransformOnly`
compatibility constraints.  No yield, completeness, sole-product statement,
phase assertion, or unprinted material stream is introduced.
-/

namespace IChO2026Problems.T9A8

/-! ## Finite positions and molecular-graph vocabulary -/

/-- The six alpha-D-glucopyranoside units visible in the alpha-CD template. -/
abbrev Unit := Fin 6

def u1 : Unit := 0
def u2 : Unit := 1
def u3 : Unit := 2
def u4 : Unit := 3
def u5 : Unit := 4
def u6 : Unit := 5

/-- The source explicitly numbers 1,2 modification clockwise. -/
def clockwise12 (i : Unit) : Unit := i + 1

/-- The source explicitly numbers 1,3 modification counterclockwise. -/
def counterclockwise13 (i : Unit) : Unit := i + 4

/-- On a six-unit ring the 1,4-related unit is opposite the director. -/
def opposite14 (i : Unit) : Unit := i + 3

inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | single
  | double
  | triple
  deriving DecidableEq, Fintype, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

/-- Electronic data for a heavy atom, together with the number of separately
bound hydrogen atoms at that site. -/
structure AtomSpec where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  deriving DecidableEq, Repr

def atomSpec (element : Element) (hydrogens : ℕ)
    (charge : ℤ := 0) : AtomSpec where
  element := element
  formalCharge := charge
  radicalElectrons := 0
  attachedHydrogens := hydrogens

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

/-- A finite molecular graph may use one common carrier for several route
intermediates; `present` says which labelled heavy atoms occur in this graph. -/
structure Molecule (α : Type) where
  present : α → Bool
  atom : α → AtomSpec
  bonds : List (Bond α)

def Molecule.Present {α : Type} (m : Molecule α) (a : α) : Prop :=
  m.present a = true

def Molecule.Bonded {α : Type} (m : Molecule α)
    (a b : α) (order : BondOrder) : Prop :=
  ∃ e ∈ m.bonds, e.Connects a b ∧ e.order = order

/-- Present heavy atoms, followed by one separate atom for every stored H. -/
def Molecule.ExpandedAtom {α : Type} (m : Molecule α) : Type :=
  Sum {a : α // m.Present a}
    (Σ a : {a : α // m.Present a}, Fin (m.atom a.1).attachedHydrogens)

def Molecule.ExpandedAtom.element {α : Type} {m : Molecule α} :
    m.ExpandedAtom → Element
  | .inl a => (m.atom a.1).element
  | .inr _ => .hydrogen

def Molecule.ExpandedBonded {α : Type} [DecidableEq α]
    (m : Molecule α) (x y : m.ExpandedAtom) (order : BondOrder) : Prop :=
  match x, y with
  | .inl a, .inl b => m.Bonded a.1 b.1 order
  | .inl a, .inr ⟨b, _⟩ => a.1 = b.1 ∧ order = .single
  | .inr ⟨a, _⟩, .inl b => a.1 = b.1 ∧ order = .single
  | .inr _, .inr _ => False

def Molecule.incidentValence {α : Type} [DecidableEq α]
    (m : Molecule α) (a : α) : ℕ :=
  (m.bonds.map fun e =>
    if e.left = a ∨ e.right = a then e.order.valence else 0).sum

def Molecule.NoBondsToAbsent {α : Type} (m : Molecule α) : Prop :=
  ∀ e ∈ m.bonds, m.Present e.left ∧ m.Present e.right

def Molecule.NoSelfBonds {α : Type} (m : Molecule α) : Prop :=
  ∀ e ∈ m.bonds, e.left ≠ e.right

def Molecule.NoDuplicateBonds {α : Type} (m : Molecule α) : Prop :=
  m.bonds.Pairwise (fun e f => ¬ e.Connects f.left f.right)

/-- The neutral C/O atoms and all three formal-charge forms used by the
canonical organic-azide Lewis representative have their ordinary valence. -/
def AtomSpec.ValidValence (a : AtomSpec) (bondValence : ℕ) : Prop :=
  a.radicalElectrons = 0 ∧
  match a.element with
  | .hydrogen => a.formalCharge = 0 ∧ bondValence + a.attachedHydrogens = 1
  | .carbon => a.formalCharge = 0 ∧ bondValence + a.attachedHydrogens = 4
  | .oxygen => a.formalCharge = 0 ∧ bondValence + a.attachedHydrogens = 2
  | .nitrogen =>
      (a.formalCharge = 0 ∧ bondValence + a.attachedHydrogens = 3) ∨
      (a.formalCharge = 1 ∧ bondValence + a.attachedHydrogens = 4) ∨
      (a.formalCharge = -1 ∧ bondValence + a.attachedHydrogens = 2)

def Molecule.LocalValencesValid {α : Type} [DecidableEq α]
    (m : Molecule α) : Prop :=
  ∀ a, m.Present a → (m.atom a).ValidValence (m.incidentValence a)

def Molecule.netFormalCharge {α : Type} [Fintype α]
    (m : Molecule α) : ℤ :=
  ∑ a : α, if m.present a then (m.atom a).formalCharge else 0

def Molecule.totalRadicalElectrons {α : Type} [Fintype α]
    (m : Molecule α) : ℕ :=
  ∑ a : α, if m.present a then (m.atom a).radicalElectrons else 0

inductive Molecule.Reachable {α : Type} (m : Molecule α) : α → α → Prop
  | refl (a : α) : m.Reachable a a
  | tail {a b c : α} (h : m.Reachable a b) (order : BondOrder)
      (hbond : m.Bonded b c order) : m.Reachable a c

def Molecule.ConnectedPresent {α : Type} (m : Molecule α) : Prop :=
  ∀ a, m.Present a → ∀ b, m.Present b → m.Reachable a b

def Molecule.WellFormedNeutralClosed {α : Type}
    [Fintype α] [DecidableEq α] (m : Molecule α) : Prop :=
  m.NoBondsToAbsent ∧
  m.NoSelfBonds ∧
  m.NoDuplicateBonds ∧
  m.LocalValencesValid ∧
  m.netFormalCharge = 0 ∧
  m.totalRadicalElectrons = 0 ∧
  m.ConnectedPresent

def Molecule.presentHeavyAtomCount {α : Type} [Fintype α]
    (m : Molecule α) : ℕ :=
  ∑ a : α, if m.present a then 1 else 0

/-! ## Complete atom carrier for every O--S intermediate -/

inductive CoreAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | oxygen2
  | oxygen3
  deriving DecidableEq, Fintype, Repr

inductive SecondarySite where
  | atC2
  | atC3
  deriving DecidableEq, Fintype, Repr

inductive BenzylAtom where
  | methylene
  | phenyl (position : Fin 6)
  deriving DecidableEq, Fintype, Repr

inductive AzideAtom where
  | proximal
  | central
  | terminal
  deriving DecidableEq, Fintype, Repr

inductive BridgeCarbon where
  | nitrogenSide
  | central
  | exomethylene
  | oxygenSide
  deriving DecidableEq, Fintype, Repr

inductive BocAtom where
  | carbonylCarbon
  | carbonylOxygen
  | esterOxygen
  | tertButylCarbon
  | methyl (which : Fin 3)
  deriving DecidableEq, Fintype, Repr

/-- One common finite label space lets graph equality compare stages while
`present` removes atoms absent from a particular intermediate. -/
inductive Atom where
  | core (unit : Unit) (atom : CoreAtom)
  | secondaryBenzyl (unit : Unit) (site : SecondarySite) (atom : BenzylAtom)
  | primaryO (unit : Unit)
  | primaryBenzyl (unit : Unit) (atom : BenzylAtom)
  | vinylTerminal (unit : Unit)
  | azide (unit : Unit) (atom : AzideAtom)
  | amineN (unit : Unit)
  | bridgeN
  | bridgeCarbon (atom : BridgeCarbon)
  | boc (atom : BocAtom)
  | nitrogenBenzyl (atom : BenzylAtom)
  deriving DecidableEq, Fintype, Repr

inductive PrimaryEnvironment where
  | benzylEther
  | hydroxymethyl
  | aldehyde
  | vinyl
  | azidomethyl
  | aminomethyl
  | bridgeNitrogenEnd
  | bridgeOxygenEnd
  deriving DecidableEq, Fintype, Repr

inductive BridgeProtection where
  | absent
  | hydrogen
  | boc
  | benzyl
  deriving DecidableEq, Fintype, Repr

/-- The twelve secondary sites are invariantly O-benzylated, so a route state
only needs to record the six changing primary environments and bridge cap. -/
structure AlphaCDState where
  primary : Unit → PrimaryEnvironment
  bridgeProtection : BridgeProtection
  deriving DecidableEq, Repr

def benzylAtomSpec : BenzylAtom → AtomSpec
  | .methylene => atomSpec .carbon 2
  | .phenyl i => atomSpec .carbon (if i = (0 : Fin 6) then 0 else 1)

def bocAtomSpec : BocAtom → AtomSpec
  | .carbonylCarbon => atomSpec .carbon 0
  | .carbonylOxygen => atomSpec .oxygen 0
  | .esterOxygen => atomSpec .oxygen 0
  | .tertButylCarbon => atomSpec .carbon 0
  | .methyl _ => atomSpec .carbon 3

def primaryOIsPresent : PrimaryEnvironment → Bool
  | .benzylEther | .hydroxymethyl | .aldehyde | .bridgeOxygenEnd => true
  | _ => false

def Atom.presentIn (s : AlphaCDState) : Atom → Bool
  | .core _ _ => true
  | .secondaryBenzyl _ _ _ => true
  | .primaryO i => primaryOIsPresent (s.primary i)
  | .primaryBenzyl i _ => s.primary i == .benzylEther
  | .vinylTerminal i => s.primary i == .vinyl
  | .azide i _ => s.primary i == .azidomethyl
  | .amineN i => s.primary i == .aminomethyl
  | .bridgeN | .bridgeCarbon _ => s.bridgeProtection != .absent
  | .boc _ => s.bridgeProtection == .boc
  | .nitrogenBenzyl _ => s.bridgeProtection == .benzyl

def coreAtomSpec (s : AlphaCDState) (i : Unit) : CoreAtom → AtomSpec
  | .c1 | .c2 | .c3 | .c4 | .c5 => atomSpec .carbon 1
  | .c6 =>
      atomSpec .carbon
        (match s.primary i with
        | .aldehyde | .vinyl => 1
        | _ => 2)
  | .ringO5 | .glycosidicO | .oxygen2 | .oxygen3 => atomSpec .oxygen 0

def routeAtomSpec (s : AlphaCDState) : Atom → AtomSpec
  | .core i a => coreAtomSpec s i a
  | .secondaryBenzyl _ _ a => benzylAtomSpec a
  | .primaryO i =>
      atomSpec .oxygen (if s.primary i = .hydroxymethyl then 1 else 0)
  | .primaryBenzyl _ a => benzylAtomSpec a
  | .vinylTerminal _ => atomSpec .carbon 2
  | .azide _ .proximal => atomSpec .nitrogen 0
  | .azide _ .central => atomSpec .nitrogen 0 1
  | .azide _ .terminal => atomSpec .nitrogen 0 (-1)
  | .amineN _ => atomSpec .nitrogen 2
  | .bridgeN =>
      atomSpec .nitrogen (if s.bridgeProtection = .hydrogen then 1 else 0)
  | .bridgeCarbon .nitrogenSide => atomSpec .carbon 2
  | .bridgeCarbon .central => atomSpec .carbon 0
  | .bridgeCarbon .exomethylene => atomSpec .carbon 2
  | .bridgeCarbon .oxygenSide => atomSpec .carbon 2
  | .boc a => bocAtomSpec a
  | .nitrogenBenzyl a => benzylAtomSpec a

def nextUnit (i : Unit) : Unit := i + 1
def previousUnit (i : Unit) : Unit := i + 5

/-- Six pyranose rings and all six cross-boundary alpha-(1→4) glycosidic
links.  O2 and O3 are included here; their benzyl groups are added below. -/
def coreBonds : List (Bond Atom) :=
  (List.ofFn fun i : Unit =>
    [ bond (.core i .ringO5) (.core i .c1)
    , bond (.core i .c1) (.core i .c2)
    , bond (.core i .c2) (.core i .c3)
    , bond (.core i .c3) (.core i .c4)
    , bond (.core i .c4) (.core i .c5)
    , bond (.core i .c5) (.core i .ringO5)
    , bond (.core i .c5) (.core i .c6)
    , bond (.core i .c2) (.core i .oxygen2)
    , bond (.core i .c3) (.core i .oxygen3)
    , bond (.core i .c1) (.core i .glycosidicO)
    , bond (.core i .glycosidicO) (.core (nextUnit i) .c4) ]).flatten

def phenylBondOrder (i : Fin 6) : BondOrder :=
  if i.val % 2 = 0 then .double else .single

/-- A complete O-Bn or N-Bn fragment: anchor-CH2-phenyl plus one explicit
Kekule representative of all six aromatic bonds. -/
def benzylFragmentBonds (embed : BenzylAtom → Atom)
    (anchor : Atom) : List (Bond Atom) :=
  [ bond anchor (embed .methylene)
  , bond (embed .methylene) (embed (.phenyl 0)) ] ++
  List.ofFn fun i : Fin 6 =>
    bond (embed (.phenyl i)) (embed (.phenyl (i + 1))) (phenylBondOrder i)

def secondaryO (i : Unit) : SecondarySite → Atom
  | .atC2 => .core i .oxygen2
  | .atC3 => .core i .oxygen3

/-- The `(OBn)12` label is expanded as two complete benzyl fragments on every
one of the six residues. -/
def secondaryBenzylBonds : List (Bond Atom) :=
  (List.ofFn fun i : Unit =>
    benzylFragmentBonds (.secondaryBenzyl i .atC2) (secondaryO i .atC2) ++
    benzylFragmentBonds (.secondaryBenzyl i .atC3) (secondaryO i .atC3)).flatten

def primaryBondsAt (s : AlphaCDState) (i : Unit) : List (Bond Atom) :=
  match s.primary i with
  | .benzylEther =>
      bond (.core i .c6) (.primaryO i) ::
        benzylFragmentBonds (.primaryBenzyl i) (.primaryO i)
  | .hydroxymethyl =>
      [bond (.core i .c6) (.primaryO i)]
  | .aldehyde =>
      [bond (.core i .c6) (.primaryO i) .double]
  | .vinyl =>
      [bond (.core i .c6) (.vinylTerminal i) .double]
  | .azidomethyl =>
      [ bond (.core i .c6) (.azide i .proximal)
      , bond (.azide i .proximal) (.azide i .central) .double
      , bond (.azide i .central) (.azide i .terminal) .double ]
  | .aminomethyl =>
      [bond (.core i .c6) (.amineN i)]
  | .bridgeNitrogenEnd =>
      [bond (.core i .c6) .bridgeN]
  | .bridgeOxygenEnd =>
      [bond (.core i .c6) (.primaryO i)]

def bocBonds : List (Bond Atom) :=
  [ bond .bridgeN (.boc .carbonylCarbon)
  , bond (.boc .carbonylCarbon) (.boc .carbonylOxygen) .double
  , bond (.boc .carbonylCarbon) (.boc .esterOxygen)
  , bond (.boc .esterOxygen) (.boc .tertButylCarbon)
  , bond (.boc .tertButylCarbon) (.boc (.methyl 0))
  , bond (.boc .tertButylCarbon) (.boc (.methyl 1))
  , bond (.boc .tertButylCarbon) (.boc (.methyl 2)) ]

/-- The single outside-the-box bridge is
unit-C6--N--CH2--C(=CH2)--CH2--O--C6-unit. -/
def bridgeBonds (s : AlphaCDState) : List (Bond Atom) :=
  match s.bridgeProtection with
  | .absent => []
  | protection =>
      [ bond .bridgeN (.bridgeCarbon .nitrogenSide)
      , bond (.bridgeCarbon .nitrogenSide) (.bridgeCarbon .central)
      , bond (.bridgeCarbon .central) (.bridgeCarbon .exomethylene) .double
      , bond (.bridgeCarbon .central) (.bridgeCarbon .oxygenSide) ] ++
      (List.ofFn fun i : Unit =>
        if s.primary i = .bridgeOxygenEnd then
          [bond (.bridgeCarbon .oxygenSide) (.primaryO i)]
        else []).flatten ++
      match protection with
      | .absent => []
      | .hydrogen => []
      | .boc => bocBonds
      | .benzyl => benzylFragmentBonds .nitrogenBenzyl .bridgeN

def routeBonds (s : AlphaCDState) : List (Bond Atom) :=
  coreBonds ++ secondaryBenzylBonds ++
    (List.ofFn fun i : Unit => primaryBondsAt s i).flatten ++
    bridgeBonds s

def molecularGraph (s : AlphaCDState) : Molecule Atom where
  present := Atom.presentIn s
  atom := routeAtomSpec s
  bonds := routeBonds s

/-! ## Retained alpha-D-glucopyranoside stereochemistry -/

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

inductive Chair where
  | fourCOne
  | oneCFour
  deriving DecidableEq, Fintype, Repr

inductive RingCarbon where
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

def axialFace : Chair → RingCarbon → Face
  | .fourCOne, .c1 => .down
  | .fourCOne, .c2 => .up
  | .fourCOne, .c3 => .down
  | .fourCOne, .c4 => .up
  | .fourCOne, .c5 => .down
  | .oneCFour, .c1 => .up
  | .oneCFour, .c2 => .down
  | .oneCFour, .c3 => .up
  | .oneCFour, .c4 => .down
  | .oneCFour, .c5 => .up

/-- Up/down data fixed by the alpha-D-gluco template and unchanged by all
primary-rim operations in the source route. -/
def templateFace : RingCarbon → Face
  | .c1 => .down
  | .c2 => .down
  | .c3 => .up
  | .c4 => .down
  | .c5 => .up

def disposition (chair : Chair) (carbon : RingCarbon) (face : Face) : Disposition :=
  if axialFace chair carbon = face then .axial else .equatorial

inductive ResidueConfiguration where
  | alphaDGlucopyranoside
  deriving DecidableEq, Fintype, Repr

/-- Ordered ring neighbours and an explicit external ligand fix the requested
relative stereochemistry independently of a name or drawing string. -/
structure StereoCentre where
  center : Atom
  ringBack : Atom
  ringForward : Atom
  externalLigand : Atom
  hydrogenParent : Atom
  externalFace : Face
  hydrogenFace : Face
  externalDisposition : Disposition
  deriving DecidableEq, Repr

def stereoCentre (i : Unit) : RingCarbon → StereoCentre
  | .c1 =>
      { center := .core i .c1
        ringBack := .core i .ringO5
        ringForward := .core i .c2
        externalLigand := .core i .glycosidicO
        hydrogenParent := .core i .c1
        externalFace := templateFace .c1
        hydrogenFace := (templateFace .c1).opposite
        externalDisposition := disposition .fourCOne .c1 (templateFace .c1) }
  | .c2 =>
      { center := .core i .c2
        ringBack := .core i .c1
        ringForward := .core i .c3
        externalLigand := .core i .oxygen2
        hydrogenParent := .core i .c2
        externalFace := templateFace .c2
        hydrogenFace := (templateFace .c2).opposite
        externalDisposition := disposition .fourCOne .c2 (templateFace .c2) }
  | .c3 =>
      { center := .core i .c3
        ringBack := .core i .c2
        ringForward := .core i .c4
        externalLigand := .core i .oxygen3
        hydrogenParent := .core i .c3
        externalFace := templateFace .c3
        hydrogenFace := (templateFace .c3).opposite
        externalDisposition := disposition .fourCOne .c3 (templateFace .c3) }
  | .c4 =>
      { center := .core i .c4
        ringBack := .core i .c3
        ringForward := .core i .c5
        externalLigand := .core (previousUnit i) .glycosidicO
        hydrogenParent := .core i .c4
        externalFace := templateFace .c4
        hydrogenFace := (templateFace .c4).opposite
        externalDisposition := disposition .fourCOne .c4 (templateFace .c4) }
  | .c5 =>
      { center := .core i .c5
        ringBack := .core i .c4
        ringForward := .core i .ringO5
        externalLigand := .core i .c6
        hydrogenParent := .core i .c5
        externalFace := templateFace .c5
        hydrogenFace := (templateFace .c5).opposite
        externalDisposition := disposition .fourCOne .c5 (templateFace .c5) }

def StereoCentre.ValidFor (s : StereoCentre) (m : Molecule Atom)
    (carbon : RingCarbon) : Prop :=
  m.Present s.center ∧
  (m.atom s.center).element = .carbon ∧
  (m.atom s.center).attachedHydrogens = 1 ∧
  s.hydrogenParent = s.center ∧
  m.Bonded s.center s.ringBack .single ∧
  m.Bonded s.center s.ringForward .single ∧
  m.Bonded s.center s.externalLigand .single ∧
  s.externalFace = templateFace carbon ∧
  s.hydrogenFace = s.externalFace.opposite ∧
  s.externalDisposition = disposition .fourCOne carbon s.externalFace

structure AlphaCDStructure where
  state : AlphaCDState
  graph : Molecule Atom
  chair : Chair
  residueConfiguration : Unit → ResidueConfiguration
  stereocentre : Unit → RingCarbon → StereoCentre

def structureOf (s : AlphaCDState) : AlphaCDStructure where
  state := s
  graph := molecularGraph s
  chair := .fourCOne
  residueConfiguration := fun _ => .alphaDGlucopyranoside
  stereocentre := stereoCentre

def BenzylFragmentAt (m : Molecule Atom) (anchor : Atom)
    (embed : BenzylAtom → Atom) : Prop :=
  m.Bonded anchor (embed .methylene) .single ∧
  m.Bonded (embed .methylene) (embed (.phenyl 0)) .single ∧
  ∀ i : Fin 6,
    m.Bonded (embed (.phenyl i)) (embed (.phenyl (i + 1)))
      (phenylBondOrder i)

def SecondaryBenzylAt (m : AlphaCDStructure)
    (i : Unit) (site : SecondarySite) : Prop :=
  BenzylFragmentAt m.graph (secondaryO i site) (.secondaryBenzyl i site)

def HasPrimaryBenzylEther (m : AlphaCDStructure) (i : Unit) : Prop :=
  m.state.primary i = .benzylEther ∧
  m.graph.Bonded (.core i .c6) (.primaryO i) .single ∧
  BenzylFragmentAt m.graph (.primaryO i) (.primaryBenzyl i)

def HasHydroxymethyl (m : AlphaCDStructure) (i : Unit) : Prop :=
  m.state.primary i = .hydroxymethyl ∧
  m.graph.Bonded (.core i .c6) (.primaryO i) .single ∧
  (m.graph.atom (.primaryO i)).element = .oxygen ∧
  (m.graph.atom (.primaryO i)).attachedHydrogens = 1

def HasTerminalVinyl (m : AlphaCDStructure) (i : Unit) : Prop :=
  m.state.primary i = .vinyl ∧
  m.graph.Bonded (.core i .c6) (.vinylTerminal i) .double ∧
  (m.graph.atom (.core i .c6)).attachedHydrogens = 1 ∧
  (m.graph.atom (.vinylTerminal i)).attachedHydrogens = 2

def HasAzidomethyl (m : AlphaCDStructure) (i : Unit) : Prop :=
  m.state.primary i = .azidomethyl ∧
  m.graph.Bonded (.core i .c6) (.azide i .proximal) .single ∧
  m.graph.Bonded (.azide i .proximal) (.azide i .central) .double ∧
  m.graph.Bonded (.azide i .central) (.azide i .terminal) .double ∧
  (m.graph.atom (.azide i .proximal)).formalCharge = 0 ∧
  (m.graph.atom (.azide i .central)).formalCharge = 1 ∧
  (m.graph.atom (.azide i .terminal)).formalCharge = -1

def HasAminomethyl (m : AlphaCDStructure) (i : Unit) : Prop :=
  m.state.primary i = .aminomethyl ∧
  m.graph.Bonded (.core i .c6) (.amineN i) .single ∧
  (m.graph.atom (.amineN i)).attachedHydrogens = 2

def BridgeProtectionPresent (m : AlphaCDStructure)
    (protection : BridgeProtection) : Prop :=
  m.state.bridgeProtection = protection ∧
  match protection with
  | .absent => ¬ m.graph.Present .bridgeN
  | .hydrogen => (m.graph.atom .bridgeN).attachedHydrogens = 1
  | .boc =>
      m.graph.Bonded .bridgeN (.boc .carbonylCarbon) .single ∧
      m.graph.Bonded (.boc .carbonylCarbon) (.boc .carbonylOxygen) .double ∧
      m.graph.Bonded (.boc .carbonylCarbon) (.boc .esterOxygen) .single ∧
      m.graph.Bonded (.boc .esterOxygen) (.boc .tertButylCarbon) .single ∧
      (∀ j : Fin 3,
        m.graph.Bonded (.boc .tertButylCarbon) (.boc (.methyl j)) .single)
  | .benzyl => BenzylFragmentAt m.graph .bridgeN .nitrogenBenzyl

/-- Both occupied primary boxes and every atom/bond of the one shared bridge
are explicit. -/
def HasNOBridge (m : AlphaCDStructure) (nUnit oUnit : Unit)
    (protection : BridgeProtection) : Prop :=
  nUnit ≠ oUnit ∧
  m.state.primary nUnit = .bridgeNitrogenEnd ∧
  m.state.primary oUnit = .bridgeOxygenEnd ∧
  BridgeProtectionPresent m protection ∧
  m.graph.Bonded (.core nUnit .c6) .bridgeN .single ∧
  m.graph.Bonded .bridgeN (.bridgeCarbon .nitrogenSide) .single ∧
  m.graph.Bonded (.bridgeCarbon .nitrogenSide) (.bridgeCarbon .central) .single ∧
  m.graph.Bonded (.bridgeCarbon .central) (.bridgeCarbon .exomethylene) .double ∧
  m.graph.Bonded (.bridgeCarbon .central) (.bridgeCarbon .oxygenSide) .single ∧
  m.graph.Bonded (.bridgeCarbon .oxygenSide) (.primaryO oUnit) .single ∧
  m.graph.Bonded (.primaryO oUnit) (.core oUnit .c6) .single

def CompleteAlphaCDStructure (m : AlphaCDStructure) : Prop :=
  m.graph = molecularGraph m.state ∧
  m.graph.WellFormedNeutralClosed ∧
  m.chair = .fourCOne ∧
  (∀ i, m.residueConfiguration i = .alphaDGlucopyranoside) ∧
  (∀ i carbon,
    m.stereocentre i carbon = stereoCentre i carbon ∧
    (m.stereocentre i carbon).ValidFor m.graph carbon) ∧
  (∀ i site, SecondaryBenzylAt m i site)

/-! ## A finite spanning-tree certificate for generated molecular graphs -/

theorem Molecule.bonded_symm {m : Molecule Atom} {a b : Atom}
    {order : BondOrder} (h : m.Bonded a b order) :
    m.Bonded b a order := by
  rcases h with ⟨e, he, hconnects, horder⟩
  refine ⟨e, he, ?_, horder⟩
  rcases hconnects with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inr ⟨hleft, hright⟩
  · exact Or.inl ⟨hleft, hright⟩

theorem Molecule.Reachable.trans {m : Molecule Atom} {a b c : Atom}
    (hab : m.Reachable a b) (hbc : m.Reachable b c) :
    m.Reachable a c := by
  induction hbc with
  | refl => exact hab
  | tail hreach order hbond ih => exact .tail ih order hbond

theorem Molecule.Reachable.symm {m : Molecule Atom} {a b : Atom}
    (h : m.Reachable a b) : m.Reachable b a := by
  induction h with
  | refl => exact .refl _
  | tail hreach order hbond ih =>
      exact (Molecule.Reachable.tail (.refl _) order
        (Molecule.bonded_symm hbond)).trans ih

def rootAtom : Atom := .core u1 .c1

/-- A parent map for a spanning tree of every concrete O--S graph.  Atoms not
present in a given stage are harmless because the certificate quantifies only
over `Present` atoms. -/
def Atom.spanningParent : Atom → Atom
  | .core i .c1 =>
      if i = u1 then rootAtom else .core i .glycosidicO
  | .core i .c2 => .core i .c1
  | .core i .c3 => .core i .c2
  | .core i .c4 => .core i .c3
  | .core i .c5 => .core i .c4
  | .core i .c6 => .core i .c5
  | .core i .ringO5 => .core i .c1
  | .core i .glycosidicO => .core (nextUnit i) .c4
  | .core i .oxygen2 => .core i .c2
  | .core i .oxygen3 => .core i .c3
  | .secondaryBenzyl i site .methylene => secondaryO i site
  | .secondaryBenzyl i site (.phenyl j) =>
      if j = (0 : Fin 6) then
        .secondaryBenzyl i site .methylene
      else .secondaryBenzyl i site (.phenyl (j - 1))
  | .primaryO i => .core i .c6
  | .primaryBenzyl i .methylene => .primaryO i
  | .primaryBenzyl i (.phenyl j) =>
      if j = (0 : Fin 6) then .primaryBenzyl i .methylene
      else .primaryBenzyl i (.phenyl (j - 1))
  | .vinylTerminal i => .core i .c6
  | .azide i .proximal => .core i .c6
  | .azide i .central => .azide i .proximal
  | .azide i .terminal => .azide i .central
  | .amineN i => .core i .c6
  | .bridgeN => .core u2 .c6
  | .bridgeCarbon .nitrogenSide => .bridgeN
  | .bridgeCarbon .central => .bridgeCarbon .nitrogenSide
  | .bridgeCarbon .exomethylene => .bridgeCarbon .central
  | .bridgeCarbon .oxygenSide => .bridgeCarbon .central
  | .boc .carbonylCarbon => .bridgeN
  | .boc .carbonylOxygen => .boc .carbonylCarbon
  | .boc .esterOxygen => .boc .carbonylCarbon
  | .boc .tertButylCarbon => .boc .esterOxygen
  | .boc (.methyl _) => .boc .tertButylCarbon
  | .nitrogenBenzyl .methylene => .bridgeN
  | .nitrogenBenzyl (.phenyl j) =>
      if j = (0 : Fin 6) then .nitrogenBenzyl .methylene
      else .nitrogenBenzyl (.phenyl (j - 1))

def Molecule.Adjacent (m : Molecule Atom) (a b : Atom) : Prop :=
  m.Bonded a b .single ∨ m.Bonded a b .double ∨ m.Bonded a b .triple

instance Bond.instDecidableConnects (e : Bond Atom) (a b : Atom) :
    Decidable (e.Connects a b) := by
  unfold Bond.Connects
  infer_instance

instance Molecule.instDecidableBonded (m : Molecule Atom) (a b : Atom)
    (order : BondOrder) : Decidable (m.Bonded a b order) := by
  unfold Molecule.Bonded
  infer_instance

instance Molecule.instDecidableAdjacent (m : Molecule Atom) (a b : Atom) :
    Decidable (m.Adjacent a b) := by
  unfold Molecule.Adjacent
  infer_instance

instance AtomSpec.instDecidableValidValence (a : AtomSpec) (bondValence : ℕ) :
    Decidable (a.ValidValence bondValence) := by
  unfold AtomSpec.ValidValence
  cases a.element <;> infer_instance

def Molecule.reachesRootWithin (m : Molecule Atom) : ℕ → Atom → Bool
  | 0, a => decide (a = rootAtom)
  | fuel + 1, a =>
      decide (a = rootAtom) ||
        (decide (m.Adjacent a a.spanningParent) &&
          m.reachesRootWithin fuel a.spanningParent)

lemma Molecule.reachesRootWithin_sound {m : Molecule Atom} {fuel : ℕ}
    {a : Atom} (h : m.reachesRootWithin fuel a = true) :
    m.Reachable a rootAtom := by
  induction fuel generalizing a with
  | zero =>
      simp only [Molecule.reachesRootWithin, decide_eq_true_eq] at h
      subst a
      exact .refl rootAtom
  | succ fuel ih =>
      simp only [Molecule.reachesRootWithin, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with hroot | ⟨hadjacent, hparent⟩
      · subst a
        exact .refl rootAtom
      · have hedge : m.Reachable a a.spanningParent := by
          rcases hadjacent with hsingle | hdouble | htriple
          · exact .tail (.refl a) .single hsingle
          · exact .tail (.refl a) .double hdouble
          · exact .tail (.refl a) .triple htriple
        exact hedge.trans (ih hparent)

lemma Molecule.connectedPresent_of_spanning_certificate
    (m : Molecule Atom) (fuel : ℕ)
    (hcertificate :
      ∀ a, m.Present a → m.reachesRootWithin fuel a = true) :
    m.ConnectedPresent := by
  intro a ha b hb
  exact (Molecule.reachesRootWithin_sound (hcertificate a ha)).trans
    (Molecule.reachesRootWithin_sound (hcertificate b hb)).symm

/-! ## Exact transcription of source arrows -/

inductive Reagent where
  | oxalylChloride
  | dimethylSulfoxide
  | methyleneTriphenylphosphorane
  | dibalH
  | methanesulfonylChloride
  | sodiumAzide
  | sodiumHydride
  | dichloroMethylenePropane
  | bocAnhydride
  | trifluoroaceticAcid
  | benzylIodide
  deriving DecidableEq, Fintype, Repr

structure ReagentUse where
  reagent : Reagent
  equivalents : Option ℚ
  deriving DecidableEq, Repr

def use (reagent : Reagent) (equivalents : Option ℚ := none) : ReagentUse :=
  { reagent := reagent, equivalents := equivalents }

inductive RouteStage where
  | nToO
  | oToP
  | pToQ
  | qToR
  | rToS
  deriving DecidableEq, Fintype, Repr

def sourceStageReagents : RouteStage → List ReagentUse
  | .nToO =>
      [use .oxalylChloride, use .dimethylSulfoxide,
        use .methyleneTriphenylphosphorane]
  | .oToP =>
      [use .dibalH (some 1), use .methanesulfonylChloride, use .sodiumAzide]
  | .pToQ =>
      [use .dibalH (some 2), use .sodiumHydride, use .dichloroMethylenePropane]
  | .qToR =>
      [use .dibalH (some 1), use .bocAnhydride (some 1),
        use .methanesulfonylChloride, use .sodiumAzide]
  | .rToS =>
      [use .trifluoroaceticAcid, use .sodiumHydride, use .benzylIodide,
        use .dibalH (some 2)]

inductive TransformationUse where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Fintype, Repr

def sourceTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-- The source N template: unit 1 is CH2OH, units 2--6 are CH2OBn, and all
twelve secondary boxes are represented separately by `secondaryBenzylBonds`. -/
def sourceNState : AlphaCDState where
  primary := ![.hydroxymethyl, .benzylEther, .benzylEther,
    .benzylEther, .benzylEther, .benzylEther]
  bridgeProtection := .absent

def SourceSchemeTranscribed : Prop :=
  sourceTransformationUse = .qualitativeNamedTransformOnly ∧
  sourceStageReagents .nToO =
    [use .oxalylChloride, use .dimethylSulfoxide,
      use .methyleneTriphenylphosphorane] ∧
  sourceStageReagents .oToP =
    [use .dibalH (some 1), use .methanesulfonylChloride, use .sodiumAzide] ∧
  sourceStageReagents .pToQ =
    [use .dibalH (some 2), use .sodiumHydride, use .dichloroMethylenePropane] ∧
  sourceStageReagents .qToR =
    [use .dibalH (some 1), use .bocAnhydride (some 1),
      use .methanesulfonylChloride, use .sodiumAzide] ∧
  sourceStageReagents .rToS =
    [use .trifluoroaceticAcid, use .sodiumHydride, use .benzylIodide,
      use .dibalH (some 2)]

theorem source_scheme_transcribed : SourceSchemeTranscribed := by
  unfold SourceSchemeTranscribed
  native_decide

/-! ## Inline derivation of the T9-A5 prerequisite -/

abbrev BetaUnit := Fin 7

structure BetaRim where
  primary : BetaUnit → PrimaryEnvironment
  secondaryBenzylated : BetaUnit → SecondarySite → Bool
  deriving DecidableEq

def betaU1 : BetaUnit := 0
def betaU4 : BetaUnit := 3

def betaUnprotected : BetaRim where
  primary := fun _ => .hydroxymethyl
  secondaryBenzylated := fun _ _ => false

def betaPerbenzylated : BetaRim where
  primary := fun _ => .benzylEther
  secondaryBenzylated := fun _ _ => true

def betaUpdatePrimary (s : BetaRim) (i : BetaUnit)
    (environment : PrimaryEnvironment) : BetaRim :=
  { s with primary := Function.update s.primary i environment }

/-- Page 3 states the 1,4 target and, only when it is unavailable, the 1,3
fallback.  This target function is applied before any L assignment is stated. -/
def betaProticTarget (s : BetaRim) (director : BetaUnit) : BetaUnit :=
  if s.primary (director + 3) = .benzylEther then director + 3 else director + 2

/-- The page-3 NaH/BnCl arrow benzylates the complete 7 x 3 hydroxyl domain. -/
def BetaGlobalBenzylation (before after : BetaRim) : Prop :=
  before = betaUnprotected ∧ after = betaPerbenzylated

/-- Numbering the symmetry-equivalent first cleavage as unit 1, the printed
protic-directing rule selects unit 4 for the second cleavage. -/
def BetaA5RouteFits (result : BetaRim) : Prop :=
  ∃ perbenzylated afterFirst,
    BetaGlobalBenzylation betaUnprotected perbenzylated ∧
    afterFirst = betaUpdatePrimary perbenzylated betaU1 .hydroxymethyl ∧
    result = betaUpdatePrimary afterFirst
      (betaProticTarget afterFirst betaU1) .hydroxymethyl

def expectedBetaL : BetaRim :=
  let afterFirst := betaUpdatePrimary betaPerbenzylated betaU1 .hydroxymethyl
  betaUpdatePrimary afterFirst (betaProticTarget afterFirst betaU1) .hydroxymethyl

lemma expectedBetaL_fits : BetaA5RouteFits expectedBetaL := by
  refine ⟨betaPerbenzylated,
    betaUpdatePrimary betaPerbenzylated betaU1 .hydroxymethyl, ?_, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem existsUniqueBetaA5Route : ∃! result : BetaRim, BetaA5RouteFits result := by
  refine ⟨expectedBetaL, expectedBetaL_fits, ?_⟩
  intro result hresult
  rcases hresult with
    ⟨perbenzylated, afterFirst, ⟨_, hperbenzylated⟩, hfirst, hresult⟩
  subst perbenzylated
  subst afterFirst
  subst result
  rfl

noncomputable def derivedLPrimaryRim : BetaRim :=
  Classical.choose existsUniqueBetaA5Route

def BetaLSpecification (result : BetaRim) : Prop :=
  result.primary betaU1 = .hydroxymethyl ∧
  result.primary betaU4 = .hydroxymethyl ∧
  (∀ i, i ≠ betaU1 → i ≠ betaU4 → result.primary i = .benzylEther) ∧
  (∀ i site, result.secondaryBenzylated i site = true)

/-- The previous-part conclusion is proved anew from the two source arrows and
the printed directing rule; no sibling certificate or frozen proof is used. -/
def PreviousPartA5Result : Prop :=
  BetaA5RouteFits derivedLPrimaryRim ∧ BetaLSpecification derivedLPrimaryRim

theorem previous_part_a5_derived : PreviousPartA5Result := by
  have hfits : BetaA5RouteFits derivedLPrimaryRim :=
    (Classical.choose_spec existsUniqueBetaA5Route).1
  have heq : derivedLPrimaryRim = expectedBetaL :=
    existsUniqueBetaA5Route.unique hfits expectedBetaL_fits
  refine ⟨hfits, ?_⟩
  rw [heq]
  unfold BetaLSpecification expectedBetaL betaProticTarget betaUpdatePrimary
  native_decide

/-! ## Uniform primary-rim reaction semantics -/

def updatePrimary (s : AlphaCDState) (i : Unit)
    (environment : PrimaryEnvironment) : AlphaCDState :=
  { s with primary := Function.update s.primary i environment }

def updateProtection (s : AlphaCDState)
    (protection : BridgeProtection) : AlphaCDState :=
  { s with bridgeProtection := protection }

def SwernOxidationAt (before after : AlphaCDState) (i : Unit) : Prop :=
  before.primary i = .hydroxymethyl ∧
  after = updatePrimary before i .aldehyde

def SwernOxidation (before after : AlphaCDState) : Prop :=
  ∃ i, SwernOxidationAt before after i

def WittigMethylenationAt (before after : AlphaCDState) (i : Unit) : Prop :=
  before.primary i = .aldehyde ∧
  after = updatePrimary before i .vinyl

def WittigMethylenation (before after : AlphaCDState) : Prop :=
  ∃ i, WittigMethylenationAt before after i

/-- Protic OH/NH sites have strength two, alkene sites strength one, and all
other displayed environments are non-directing. -/
def directingStrength (s : AlphaCDState) (i : Unit) : ℕ :=
  match s.primary i with
  | .hydroxymethyl | .aminomethyl => 2
  | .bridgeNitrogenEnd => if s.bridgeProtection = .hydrogen then 2 else 0
  | .vinyl => 1
  | _ => 0

def ActiveDirector (s : AlphaCDState) (i : Unit) : Prop :=
  0 < directingStrength s i ∧
  ∀ j, directingStrength s j ≤ directingStrength s i

/-- An alkene selects its clockwise 1,2 neighbour.  A protic group selects the
opposite 1,4 position if that position still bears OBn, otherwise the printed
counterclockwise 1,3 fallback. -/
def directedTarget (s : AlphaCDState) (director : Unit) : Unit :=
  if directingStrength s director = 1 then clockwise12 director
  else if s.primary (opposite14 director) = .benzylEther then
    opposite14 director
  else counterclockwise13 director

def DibalDirectedDebenzylation (before after : AlphaCDState) : Prop :=
  ∃ director,
    ActiveDirector before director ∧
    before.primary (directedTarget before director) = .benzylEther ∧
    after = updatePrimary before (directedTarget before director) .hydroxymethyl

def MesylAzideSubstitutionAt (before after : AlphaCDState) (i : Unit) : Prop :=
  before.primary i = .hydroxymethyl ∧
  after = updatePrimary before i .azidomethyl

def MesylAzideSubstitution (before after : AlphaCDState) : Prop :=
  ∃ i, MesylAzideSubstitutionAt before after i

def DibalAzideReductionAt (before after : AlphaCDState) (i : Unit) : Prop :=
  before.primary i = .azidomethyl ∧
  after = updatePrimary before i .aminomethyl

def DibalAzideReduction (before after : AlphaCDState) : Prop :=
  ∃ i, DibalAzideReductionAt before after i

def BridgeClosureAt (before after : AlphaCDState)
    (nUnit oUnit : Unit) : Prop :=
  nUnit ≠ oUnit ∧
  before.bridgeProtection = .absent ∧
  before.primary nUnit = .aminomethyl ∧
  before.primary oUnit = .hydroxymethyl ∧
  after = updateProtection
    (updatePrimary (updatePrimary before nUnit .bridgeNitrogenEnd)
      oUnit .bridgeOxygenEnd) .hydrogen

def BridgeClosure (before after : AlphaCDState) : Prop :=
  ∃ nUnit oUnit, BridgeClosureAt before after nUnit oUnit

def BocProtection (before after : AlphaCDState) : Prop :=
  before.bridgeProtection = .hydrogen ∧
  after = updateProtection before .boc

def TrifluoroaceticDeprotection (before after : AlphaCDState) : Prop :=
  before.bridgeProtection = .boc ∧
  after = updateProtection before .hydrogen

def NitrogenBenzylation (before after : AlphaCDState) : Prop :=
  before.bridgeProtection = .hydrogen ∧
  after = updateProtection before .benzyl

/-- All source-labelled products and every chemically relevant transient state
needed to derive them. -/
structure SourceRoute where
  nAldehyde : AlphaCDState
  o : AlphaCDState
  oDebenzylated : AlphaCDState
  p : AlphaCDState
  pAzideReduced : AlphaCDState
  pDebenzylated : AlphaCDState
  q : AlphaCDState
  qDebenzylated : AlphaCDState
  qBocProtected : AlphaCDState
  r : AlphaCDState
  rDeprotected : AlphaCDState
  rNBenzylated : AlphaCDState
  rAzideReduced : AlphaCDState
  s : AlphaCDState
  deriving DecidableEq, Repr

/-! The following named states are only a readable normal form for the route
relations below.  Each one is obtained by applying the corresponding generic
state update; no product assignment is added as a hypothesis. -/

def expectedNAldehyde : AlphaCDState :=
  updatePrimary sourceNState u1 .aldehyde

def expectedOState : AlphaCDState :=
  updatePrimary expectedNAldehyde u1 .vinyl

def expectedODebenzylated : AlphaCDState :=
  updatePrimary expectedOState u2 .hydroxymethyl

def expectedPState : AlphaCDState :=
  updatePrimary expectedODebenzylated u2 .azidomethyl

def expectedPAzideReduced : AlphaCDState :=
  updatePrimary expectedPState u2 .aminomethyl

def expectedPDebenzylated : AlphaCDState :=
  updatePrimary expectedPAzideReduced u5 .hydroxymethyl

def expectedQState : AlphaCDState :=
  updateProtection
    (updatePrimary
      (updatePrimary expectedPDebenzylated u2 .bridgeNitrogenEnd)
      u5 .bridgeOxygenEnd)
    .hydrogen

def expectedQDebenzylated : AlphaCDState :=
  updatePrimary expectedQState u6 .hydroxymethyl

def expectedQBocProtected : AlphaCDState :=
  updateProtection expectedQDebenzylated .boc

def expectedRState : AlphaCDState :=
  updatePrimary expectedQBocProtected u6 .azidomethyl

def expectedRDeprotected : AlphaCDState :=
  updateProtection expectedRState .hydrogen

def expectedRNBenzylated : AlphaCDState :=
  updateProtection expectedRDeprotected .benzyl

def expectedRAzideReduced : AlphaCDState :=
  updatePrimary expectedRNBenzylated u6 .aminomethyl

def expectedSState : AlphaCDState :=
  updatePrimary expectedRAzideReduced u3 .hydroxymethyl

def expectedRoute : SourceRoute where
  nAldehyde := expectedNAldehyde
  o := expectedOState
  oDebenzylated := expectedODebenzylated
  p := expectedPState
  pAzideReduced := expectedPAzideReduced
  pDebenzylated := expectedPDebenzylated
  q := expectedQState
  qDebenzylated := expectedQDebenzylated
  qBocProtected := expectedQBocProtected
  r := expectedRState
  rDeprotected := expectedRDeprotected
  rNBenzylated := expectedRNBenzylated
  rAzideReduced := expectedRAzideReduced
  s := expectedSState

/-- Assumptions are exactly the bound source scheme, the independently
rederived previous-part prerequisite, and uniform named-transform relations.
No desired primary assignment occurs as a premise. -/
def SourceRouteFits (route : SourceRoute) : Prop :=
  SourceSchemeTranscribed ∧
  PreviousPartA5Result ∧
  SwernOxidation sourceNState route.nAldehyde ∧
  WittigMethylenation route.nAldehyde route.o ∧
  DibalDirectedDebenzylation route.o route.oDebenzylated ∧
  MesylAzideSubstitution route.oDebenzylated route.p ∧
  DibalAzideReduction route.p route.pAzideReduced ∧
  DibalDirectedDebenzylation route.pAzideReduced route.pDebenzylated ∧
  BridgeClosure route.pDebenzylated route.q ∧
  DibalDirectedDebenzylation route.q route.qDebenzylated ∧
  BocProtection route.qDebenzylated route.qBocProtected ∧
  MesylAzideSubstitution route.qBocProtected route.r ∧
  TrifluoroaceticDeprotection route.r route.rDeprotected ∧
  NitrogenBenzylation route.rDeprotected route.rNBenzylated ∧
  DibalAzideReduction route.rNBenzylated route.rAzideReduced ∧
  DibalDirectedDebenzylation route.rAzideReduced route.s

lemma expectedRoute_fits : SourceRouteFits expectedRoute := by
  unfold SourceRouteFits
  refine ⟨source_scheme_transcribed, previous_part_a5_derived, ?_⟩
  unfold expectedRoute
  unfold SwernOxidation WittigMethylenation DibalDirectedDebenzylation
    MesylAzideSubstitution DibalAzideReduction BridgeClosure BocProtection
    TrifluoroaceticDeprotection NitrogenBenzylation
    SwernOxidationAt WittigMethylenationAt MesylAzideSubstitutionAt
    DibalAzideReductionAt BridgeClosureAt ActiveDirector directedTarget
    directingStrength
  native_decide

lemma swern_source_unique {after : AlphaCDState}
    (h : SwernOxidation sourceNState after) :
    after = expectedNAldehyde := by
  unfold SwernOxidation SwernOxidationAt at h
  rcases h with ⟨i, hi, rfl⟩
  have hi' : i = u1 := by
    fin_cases i <;> simp_all [sourceNState, u1]
  subst i
  rfl

lemma wittig_expected_unique {after : AlphaCDState}
    (h : WittigMethylenation expectedNAldehyde after) :
    after = expectedOState := by
  unfold WittigMethylenation WittigMethylenationAt at h
  rcases h with ⟨i, hi, rfl⟩
  have hi' : i = u1 := by
    fin_cases i <;>
      simp_all [expectedNAldehyde, sourceNState, updatePrimary, u1]
  subst i
  rfl

lemma dibal_expectedO_unique {after : AlphaCDState}
    (h : DibalDirectedDebenzylation expectedOState after) :
    after = expectedODebenzylated := by
  unfold DibalDirectedDebenzylation at h
  rcases h with ⟨director, hactive, _, hafter⟩
  have hdirector : director = u1 := by
    fin_cases director <;>
      simp_all [ActiveDirector, directingStrength, expectedOState,
        expectedNAldehyde, sourceNState, updatePrimary, u1]
  subst director
  rw [hafter]
  native_decide

lemma mesyl_expectedODebenzylated_unique {after : AlphaCDState}
    (h : MesylAzideSubstitution expectedODebenzylated after) :
    after = expectedPState := by
  unfold MesylAzideSubstitution MesylAzideSubstitutionAt at h
  rcases h with ⟨i, hi, hafter⟩
  have hsite :
      ∀ j : Unit,
        expectedODebenzylated.primary j = .hydroxymethyl ↔ j = u2 := by
    native_decide
  have hi' : i = u2 := (hsite i).mp hi
  subst i
  rw [hafter]
  rfl

lemma azide_expectedP_unique {after : AlphaCDState}
    (h : DibalAzideReduction expectedPState after) :
    after = expectedPAzideReduced := by
  unfold DibalAzideReduction DibalAzideReductionAt at h
  rcases h with ⟨i, hi, hafter⟩
  have hsite :
      ∀ j : Unit, expectedPState.primary j = .azidomethyl ↔ j = u2 := by
    native_decide
  have hi' : i = u2 := (hsite i).mp hi
  subst i
  rw [hafter]
  rfl

lemma dibal_expectedPAzideReduced_unique {after : AlphaCDState}
    (h : DibalDirectedDebenzylation expectedPAzideReduced after) :
    after = expectedPDebenzylated := by
  unfold DibalDirectedDebenzylation at h
  rcases h with ⟨director, hactive, _, hafter⟩
  have hdirectorSpec :
      ∀ j : Unit, ActiveDirector expectedPAzideReduced j ↔ j = u2 := by
    unfold ActiveDirector directingStrength
    native_decide
  have hdirector : director = u2 := (hdirectorSpec director).mp hactive
  subst director
  rw [hafter]
  native_decide

lemma bridge_expectedPDebenzylated_unique {after : AlphaCDState}
    (h : BridgeClosure expectedPDebenzylated after) :
    after = expectedQState := by
  unfold BridgeClosure BridgeClosureAt at h
  rcases h with ⟨nUnit, oUnit, _, _, hn, ho, hafter⟩
  have hnsite :
      ∀ j : Unit,
        expectedPDebenzylated.primary j = .aminomethyl ↔ j = u2 := by
    native_decide
  have hosite :
      ∀ j : Unit,
        expectedPDebenzylated.primary j = .hydroxymethyl ↔ j = u5 := by
    native_decide
  have hn' : nUnit = u2 := (hnsite nUnit).mp hn
  have ho' : oUnit = u5 := (hosite oUnit).mp ho
  subst nUnit
  subst oUnit
  rw [hafter]
  rfl

lemma dibal_expectedQ_unique {after : AlphaCDState}
    (h : DibalDirectedDebenzylation expectedQState after) :
    after = expectedQDebenzylated := by
  unfold DibalDirectedDebenzylation at h
  rcases h with ⟨director, hactive, _, hafter⟩
  have hdirectorSpec :
      ∀ j : Unit, ActiveDirector expectedQState j ↔ j = u2 := by
    unfold ActiveDirector directingStrength
    native_decide
  have hdirector : director = u2 := (hdirectorSpec director).mp hactive
  subst director
  rw [hafter]
  native_decide

lemma boc_expectedQDebenzylated_unique {after : AlphaCDState}
    (h : BocProtection expectedQDebenzylated after) :
    after = expectedQBocProtected := by
  unfold BocProtection at h
  rw [h.2]
  rfl

lemma mesyl_expectedQBocProtected_unique {after : AlphaCDState}
    (h : MesylAzideSubstitution expectedQBocProtected after) :
    after = expectedRState := by
  unfold MesylAzideSubstitution MesylAzideSubstitutionAt at h
  rcases h with ⟨i, hi, hafter⟩
  have hsite :
      ∀ j : Unit,
        expectedQBocProtected.primary j = .hydroxymethyl ↔ j = u6 := by
    native_decide
  have hi' : i = u6 := (hsite i).mp hi
  subst i
  rw [hafter]
  rfl

lemma tfa_expectedR_unique {after : AlphaCDState}
    (h : TrifluoroaceticDeprotection expectedRState after) :
    after = expectedRDeprotected := by
  unfold TrifluoroaceticDeprotection at h
  rw [h.2]
  rfl

lemma nbenzyl_expectedRDeprotected_unique {after : AlphaCDState}
    (h : NitrogenBenzylation expectedRDeprotected after) :
    after = expectedRNBenzylated := by
  unfold NitrogenBenzylation at h
  rw [h.2]
  rfl

lemma azide_expectedRNBenzylated_unique {after : AlphaCDState}
    (h : DibalAzideReduction expectedRNBenzylated after) :
    after = expectedRAzideReduced := by
  unfold DibalAzideReduction DibalAzideReductionAt at h
  rcases h with ⟨i, hi, hafter⟩
  have hsite :
      ∀ j : Unit,
        expectedRNBenzylated.primary j = .azidomethyl ↔ j = u6 := by
    native_decide
  have hi' : i = u6 := (hsite i).mp hi
  subst i
  rw [hafter]
  rfl

lemma dibal_expectedRAzideReduced_unique {after : AlphaCDState}
    (h : DibalDirectedDebenzylation expectedRAzideReduced after) :
    after = expectedSState := by
  unfold DibalDirectedDebenzylation at h
  rcases h with ⟨director, hactive, _, hafter⟩
  have hdirectorSpec :
      ∀ j : Unit, ActiveDirector expectedRAzideReduced j ↔ j = u6 := by
    unfold ActiveDirector directingStrength
    native_decide
  have hdirector : director = u6 := (hdirectorSpec director).mp hactive
  subst director
  rw [hafter]
  native_decide

/-- Applying every source constraint uniformly leaves one route. -/
theorem existsUniqueSourceRoute : ∃! route : SourceRoute, SourceRouteFits route := by
  refine ⟨expectedRoute, expectedRoute_fits, ?_⟩
  intro route hroute
  unfold SourceRouteFits at hroute
  rcases hroute with
    ⟨_, _, hnAldehyde, ho, hoDebenzylated, hp, hpAzideReduced,
      hpDebenzylated, hq, hqDebenzylated, hqBocProtected, hr,
      hrDeprotected, hrNBenzylated, hrAzideReduced, hs⟩
  have hnAldehydeEq : route.nAldehyde = expectedNAldehyde :=
    swern_source_unique hnAldehyde
  rw [hnAldehydeEq] at ho
  have hoEq : route.o = expectedOState := wittig_expected_unique ho
  rw [hoEq] at hoDebenzylated
  have hoDebenzylatedEq :
      route.oDebenzylated = expectedODebenzylated :=
    dibal_expectedO_unique hoDebenzylated
  rw [hoDebenzylatedEq] at hp
  have hpEq : route.p = expectedPState :=
    mesyl_expectedODebenzylated_unique hp
  rw [hpEq] at hpAzideReduced
  have hpAzideReducedEq :
      route.pAzideReduced = expectedPAzideReduced :=
    azide_expectedP_unique hpAzideReduced
  rw [hpAzideReducedEq] at hpDebenzylated
  have hpDebenzylatedEq :
      route.pDebenzylated = expectedPDebenzylated :=
    dibal_expectedPAzideReduced_unique hpDebenzylated
  rw [hpDebenzylatedEq] at hq
  have hqEq : route.q = expectedQState :=
    bridge_expectedPDebenzylated_unique hq
  rw [hqEq] at hqDebenzylated
  have hqDebenzylatedEq :
      route.qDebenzylated = expectedQDebenzylated :=
    dibal_expectedQ_unique hqDebenzylated
  rw [hqDebenzylatedEq] at hqBocProtected
  have hqBocProtectedEq :
      route.qBocProtected = expectedQBocProtected :=
    boc_expectedQDebenzylated_unique hqBocProtected
  rw [hqBocProtectedEq] at hr
  have hrEq : route.r = expectedRState :=
    mesyl_expectedQBocProtected_unique hr
  rw [hrEq] at hrDeprotected
  have hrDeprotectedEq :
      route.rDeprotected = expectedRDeprotected :=
    tfa_expectedR_unique hrDeprotected
  rw [hrDeprotectedEq] at hrNBenzylated
  have hrNBenzylatedEq :
      route.rNBenzylated = expectedRNBenzylated :=
    nbenzyl_expectedRDeprotected_unique hrNBenzylated
  rw [hrNBenzylatedEq] at hrAzideReduced
  have hrAzideReducedEq :
      route.rAzideReduced = expectedRAzideReduced :=
    azide_expectedRNBenzylated_unique hrAzideReduced
  rw [hrAzideReducedEq] at hs
  have hsEq : route.s = expectedSState :=
    dibal_expectedRAzideReduced_unique hs
  cases route
  simp_all [expectedRoute]

noncomputable def derivedRoute : SourceRoute :=
  Classical.choose existsUniqueSourceRoute

theorem derivedRoute_fits : SourceRouteFits derivedRoute := by
  exact (Classical.choose_spec existsUniqueSourceRoute).1

lemma derivedRoute_eq_expectedRoute : derivedRoute = expectedRoute :=
  existsUniqueSourceRoute.unique derivedRoute_fits expectedRoute_fits

/-- Computed source directions: 1→2 clockwise, 2→5 opposite, the occupied
2→5 direction falls back 2→6 counterclockwise, and 6→3 is opposite. -/
theorem source_direction_audit :
    clockwise12 u1 = u2 ∧
    opposite14 u2 = u5 ∧
    counterclockwise13 u2 = u6 ∧
    opposite14 u6 = u3 := by
  native_decide

/-- This is the candidate output of the uniform route audit, not an input to
`SourceRouteFits`. -/
theorem derivedRoute_primary_assignments :
    derivedRoute.o.primary u1 = .vinyl ∧
    derivedRoute.o.primary u2 = .benzylEther ∧
    derivedRoute.o.primary u3 = .benzylEther ∧
    derivedRoute.o.primary u4 = .benzylEther ∧
    derivedRoute.o.primary u5 = .benzylEther ∧
    derivedRoute.o.primary u6 = .benzylEther ∧
    derivedRoute.p.primary u1 = .vinyl ∧
    derivedRoute.p.primary u2 = .azidomethyl ∧
    derivedRoute.p.primary u3 = .benzylEther ∧
    derivedRoute.p.primary u4 = .benzylEther ∧
    derivedRoute.p.primary u5 = .benzylEther ∧
    derivedRoute.p.primary u6 = .benzylEther ∧
    derivedRoute.q.primary u1 = .vinyl ∧
    derivedRoute.q.primary u2 = .bridgeNitrogenEnd ∧
    derivedRoute.q.primary u3 = .benzylEther ∧
    derivedRoute.q.primary u4 = .benzylEther ∧
    derivedRoute.q.primary u5 = .bridgeOxygenEnd ∧
    derivedRoute.q.primary u6 = .benzylEther ∧
    derivedRoute.q.bridgeProtection = .hydrogen ∧
    derivedRoute.r.primary u1 = .vinyl ∧
    derivedRoute.r.primary u2 = .bridgeNitrogenEnd ∧
    derivedRoute.r.primary u3 = .benzylEther ∧
    derivedRoute.r.primary u4 = .benzylEther ∧
    derivedRoute.r.primary u5 = .bridgeOxygenEnd ∧
    derivedRoute.r.primary u6 = .azidomethyl ∧
    derivedRoute.r.bridgeProtection = .boc ∧
    derivedRoute.s.primary u1 = .vinyl ∧
    derivedRoute.s.primary u2 = .bridgeNitrogenEnd ∧
    derivedRoute.s.primary u3 = .hydroxymethyl ∧
    derivedRoute.s.primary u4 = .benzylEther ∧
    derivedRoute.s.primary u5 = .bridgeOxygenEnd ∧
    derivedRoute.s.primary u6 = .aminomethyl ∧
    derivedRoute.s.bridgeProtection = .benzyl := by
  rw [derivedRoute_eq_expectedRoute]
  native_decide

noncomputable def derivedO : AlphaCDStructure := structureOf derivedRoute.o
noncomputable def derivedP : AlphaCDStructure := structureOf derivedRoute.p
noncomputable def derivedQ : AlphaCDStructure := structureOf derivedRoute.q
noncomputable def derivedR : AlphaCDStructure := structureOf derivedRoute.r
noncomputable def derivedS : AlphaCDStructure := structureOf derivedRoute.s

/-! ## Source-first component and graph audit -/

/-- Heavy-atom and heavy-bond counts obtained only after assembling all six
residues, twelve secondary Bn fragments, six glycosidic cross-boundary bonds,
all primary substituents, and the one shared bridge where present. -/
def DerivedComponentAudit : Prop :=
  derivedO.graph.presentHeavyAtomCount = 185 ∧ derivedO.graph.bonds.length = 208 ∧
  derivedP.graph.presentHeavyAtomCount = 180 ∧ derivedP.graph.bonds.length = 202 ∧
  derivedQ.graph.presentHeavyAtomCount = 175 ∧ derivedQ.graph.bonds.length = 197 ∧
  derivedR.graph.presentHeavyAtomCount = 177 ∧ derivedR.graph.bonds.length = 198 ∧
  derivedS.graph.presentHeavyAtomCount = 168 ∧ derivedS.graph.bonds.length = 189

theorem derived_component_audit : DerivedComponentAudit := by
  unfold DerivedComponentAudit derivedO derivedP derivedQ derivedR derivedS
  rw [derivedRoute_eq_expectedRoute]
  native_decide

def Molecule.LocallyWellFormedNeutral (m : Molecule Atom) : Prop :=
  m.NoBondsToAbsent ∧
  m.NoSelfBonds ∧
  m.NoDuplicateBonds ∧
  m.LocalValencesValid ∧
  m.netFormalCharge = 0 ∧
  m.totalRadicalElectrons = 0

lemma expectedO_local_well_formed :
    (molecularGraph expectedOState).LocallyWellFormedNeutral := by
  unfold Molecule.LocallyWellFormedNeutral
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Molecule.NoBondsToAbsent Molecule.Present
    native_decide
  · unfold Molecule.NoSelfBonds
    native_decide
  · unfold Molecule.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold Molecule.LocalValencesValid Molecule.Present
    native_decide
  · native_decide
  · native_decide

lemma expectedO_connected :
    (molecularGraph expectedOState).ConnectedPresent := by
  apply Molecule.connectedPresent_of_spanning_certificate _ 64
  unfold Molecule.Present
  native_decide

lemma expectedP_local_well_formed :
    (molecularGraph expectedPState).LocallyWellFormedNeutral := by
  unfold Molecule.LocallyWellFormedNeutral
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Molecule.NoBondsToAbsent Molecule.Present
    native_decide
  · unfold Molecule.NoSelfBonds
    native_decide
  · unfold Molecule.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold Molecule.LocalValencesValid Molecule.Present
    native_decide
  · native_decide
  · native_decide

lemma expectedP_connected :
    (molecularGraph expectedPState).ConnectedPresent := by
  apply Molecule.connectedPresent_of_spanning_certificate _ 64
  unfold Molecule.Present
  native_decide

lemma expectedQ_local_well_formed :
    (molecularGraph expectedQState).LocallyWellFormedNeutral := by
  unfold Molecule.LocallyWellFormedNeutral
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Molecule.NoBondsToAbsent Molecule.Present
    native_decide
  · unfold Molecule.NoSelfBonds
    native_decide
  · unfold Molecule.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold Molecule.LocalValencesValid Molecule.Present
    native_decide
  · native_decide
  · native_decide

lemma expectedQ_connected :
    (molecularGraph expectedQState).ConnectedPresent := by
  apply Molecule.connectedPresent_of_spanning_certificate _ 64
  unfold Molecule.Present
  native_decide

lemma expectedR_local_well_formed :
    (molecularGraph expectedRState).LocallyWellFormedNeutral := by
  unfold Molecule.LocallyWellFormedNeutral
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Molecule.NoBondsToAbsent Molecule.Present
    native_decide
  · unfold Molecule.NoSelfBonds
    native_decide
  · unfold Molecule.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold Molecule.LocalValencesValid Molecule.Present
    native_decide
  · native_decide
  · native_decide

lemma expectedR_connected :
    (molecularGraph expectedRState).ConnectedPresent := by
  apply Molecule.connectedPresent_of_spanning_certificate _ 64
  unfold Molecule.Present
  native_decide

lemma expectedS_local_well_formed :
    (molecularGraph expectedSState).LocallyWellFormedNeutral := by
  unfold Molecule.LocallyWellFormedNeutral
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Molecule.NoBondsToAbsent Molecule.Present
    native_decide
  · unfold Molecule.NoSelfBonds
    native_decide
  · unfold Molecule.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold Molecule.LocalValencesValid Molecule.Present
    native_decide
  · native_decide
  · native_decide

lemma expectedS_connected :
    (molecularGraph expectedSState).ConnectedPresent := by
  apply Molecule.connectedPresent_of_spanning_certificate _ 64
  unfold Molecule.Present
  native_decide

lemma Molecule.wellFormedNeutralClosed_of_local
    {m : Molecule Atom} (hlocal : m.LocallyWellFormedNeutral)
    (hconnected : m.ConnectedPresent) : m.WellFormedNeutralClosed := by
  rcases hlocal with ⟨habsent, hself, hduplicate, hvalence, hcharge, hradical⟩
  exact ⟨habsent, hself, hduplicate, hvalence, hcharge, hradical, hconnected⟩

lemma expectedO_complete :
    CompleteAlphaCDStructure (structureOf expectedOState) := by
  unfold CompleteAlphaCDStructure
  refine ⟨rfl,
    Molecule.wellFormedNeutralClosed_of_local expectedO_local_well_formed
      expectedO_connected,
    rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · unfold StereoCentre.ValidFor Molecule.Present
    native_decide
  · unfold SecondaryBenzylAt BenzylFragmentAt
    native_decide

lemma expectedP_complete :
    CompleteAlphaCDStructure (structureOf expectedPState) := by
  unfold CompleteAlphaCDStructure
  refine ⟨rfl,
    Molecule.wellFormedNeutralClosed_of_local expectedP_local_well_formed
      expectedP_connected,
    rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · unfold StereoCentre.ValidFor Molecule.Present
    native_decide
  · unfold SecondaryBenzylAt BenzylFragmentAt
    native_decide

lemma expectedQ_complete :
    CompleteAlphaCDStructure (structureOf expectedQState) := by
  unfold CompleteAlphaCDStructure
  refine ⟨rfl,
    Molecule.wellFormedNeutralClosed_of_local expectedQ_local_well_formed
      expectedQ_connected,
    rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · unfold StereoCentre.ValidFor Molecule.Present
    native_decide
  · unfold SecondaryBenzylAt BenzylFragmentAt
    native_decide

lemma expectedR_complete :
    CompleteAlphaCDStructure (structureOf expectedRState) := by
  unfold CompleteAlphaCDStructure
  refine ⟨rfl,
    Molecule.wellFormedNeutralClosed_of_local expectedR_local_well_formed
      expectedR_connected,
    rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · unfold StereoCentre.ValidFor Molecule.Present
    native_decide
  · unfold SecondaryBenzylAt BenzylFragmentAt
    native_decide

lemma expectedS_complete :
    CompleteAlphaCDStructure (structureOf expectedSState) := by
  unfold CompleteAlphaCDStructure
  refine ⟨rfl,
    Molecule.wellFormedNeutralClosed_of_local expectedS_local_well_formed
      expectedS_connected,
    rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · unfold StereoCentre.ValidFor Molecule.Present
    native_decide
  · unfold SecondaryBenzylAt BenzylFragmentAt
    native_decide

/-! ## One complete specification for each requested structure -/

def StructureOSpecification (m : AlphaCDStructure) : Prop :=
  CompleteAlphaCDStructure m ∧
  HasTerminalVinyl m u1 ∧
  HasPrimaryBenzylEther m u2 ∧
  HasPrimaryBenzylEther m u3 ∧
  HasPrimaryBenzylEther m u4 ∧
  HasPrimaryBenzylEther m u5 ∧
  HasPrimaryBenzylEther m u6 ∧
  BridgeProtectionPresent m .absent

def StructurePSpecification (m : AlphaCDStructure) : Prop :=
  CompleteAlphaCDStructure m ∧
  HasTerminalVinyl m u1 ∧
  HasAzidomethyl m u2 ∧
  HasPrimaryBenzylEther m u3 ∧
  HasPrimaryBenzylEther m u4 ∧
  HasPrimaryBenzylEther m u5 ∧
  HasPrimaryBenzylEther m u6 ∧
  BridgeProtectionPresent m .absent

def StructureQSpecification (m : AlphaCDStructure) : Prop :=
  CompleteAlphaCDStructure m ∧
  HasTerminalVinyl m u1 ∧
  HasNOBridge m u2 u5 .hydrogen ∧
  HasPrimaryBenzylEther m u3 ∧
  HasPrimaryBenzylEther m u4 ∧
  HasPrimaryBenzylEther m u6

def StructureRSpecification (m : AlphaCDStructure) : Prop :=
  CompleteAlphaCDStructure m ∧
  HasTerminalVinyl m u1 ∧
  HasNOBridge m u2 u5 .boc ∧
  HasPrimaryBenzylEther m u3 ∧
  HasPrimaryBenzylEther m u4 ∧
  HasAzidomethyl m u6

def StructureSSpecification (m : AlphaCDStructure) : Prop :=
  CompleteAlphaCDStructure m ∧
  HasTerminalVinyl m u1 ∧
  HasNOBridge m u2 u5 .benzyl ∧
  HasHydroxymethyl m u3 ∧
  HasPrimaryBenzylEther m u4 ∧
  HasAminomethyl m u6

lemma expectedO_specification :
    StructureOSpecification (structureOf expectedOState) := by
  unfold StructureOSpecification
  refine ⟨expectedO_complete, ?_⟩
  unfold HasTerminalVinyl HasPrimaryBenzylEther BridgeProtectionPresent
    BenzylFragmentAt Molecule.Present
  native_decide

lemma expectedP_specification :
    StructurePSpecification (structureOf expectedPState) := by
  unfold StructurePSpecification
  refine ⟨expectedP_complete, ?_⟩
  unfold HasTerminalVinyl HasAzidomethyl HasPrimaryBenzylEther
    BridgeProtectionPresent BenzylFragmentAt Molecule.Present
  native_decide

lemma expectedQ_specification :
    StructureQSpecification (structureOf expectedQState) := by
  unfold StructureQSpecification
  refine ⟨expectedQ_complete, ?_⟩
  unfold HasTerminalVinyl HasNOBridge HasPrimaryBenzylEther
    BridgeProtectionPresent BenzylFragmentAt Molecule.Present
  native_decide

lemma expectedR_specification :
    StructureRSpecification (structureOf expectedRState) := by
  unfold StructureRSpecification
  refine ⟨expectedR_complete, ?_⟩
  unfold HasTerminalVinyl HasNOBridge HasPrimaryBenzylEther HasAzidomethyl
    BridgeProtectionPresent BenzylFragmentAt Molecule.Present
  native_decide

lemma expectedS_specification :
    StructureSSpecification (structureOf expectedSState) := by
  unfold StructureSSpecification
  refine ⟨expectedS_complete, ?_⟩
  unfold HasTerminalVinyl HasNOBridge HasHydroxymethyl
    HasPrimaryBenzylEther HasAminomethyl BridgeProtectionPresent
    BenzylFragmentAt Molecule.Present
  native_decide

def SourceQualitativeCompatibility : Prop :=
  sourceTransformationUse = .qualitativeNamedTransformOnly ∧
  SourceRouteFits derivedRoute

/-- Requested output `structure_o`. -/
def StructureOResult : Prop :=
  SourceQualitativeCompatibility ∧ StructureOSpecification derivedO

/-- Requested output `structure_p`. -/
def StructurePResult : Prop :=
  SourceQualitativeCompatibility ∧ StructurePSpecification derivedP

/-- Requested output `structure_q`. -/
def StructureQResult : Prop :=
  SourceQualitativeCompatibility ∧ StructureQSpecification derivedQ

/-- Requested output `structure_r`. -/
def StructureRResult : Prop :=
  SourceQualitativeCompatibility ∧ StructureRSpecification derivedR

/-- Requested output `structure_s`. -/
def StructureSResult : Prop :=
  SourceQualitativeCompatibility ∧ StructureSSpecification derivedS

theorem structure_o : StructureOResult := by
  unfold StructureOResult SourceQualitativeCompatibility
  refine ⟨⟨rfl, derivedRoute_fits⟩, ?_⟩
  unfold derivedO
  rw [derivedRoute_eq_expectedRoute]
  exact expectedO_specification

theorem structure_p : StructurePResult := by
  unfold StructurePResult SourceQualitativeCompatibility
  refine ⟨⟨rfl, derivedRoute_fits⟩, ?_⟩
  unfold derivedP
  rw [derivedRoute_eq_expectedRoute]
  exact expectedP_specification

theorem structure_q : StructureQResult := by
  unfold StructureQResult SourceQualitativeCompatibility
  refine ⟨⟨rfl, derivedRoute_fits⟩, ?_⟩
  unfold derivedQ
  rw [derivedRoute_eq_expectedRoute]
  exact expectedQ_specification

theorem structure_r : StructureRResult := by
  unfold StructureRResult SourceQualitativeCompatibility
  refine ⟨⟨rfl, derivedRoute_fits⟩, ?_⟩
  unfold derivedR
  rw [derivedRoute_eq_expectedRoute]
  exact expectedR_specification

theorem structure_s : StructureSResult := by
  unfold StructureSResult SourceQualitativeCompatibility
  refine ⟨⟨rfl, derivedRoute_fits⟩, ?_⟩
  unfold derivedS
  rw [derivedRoute_eq_expectedRoute]
  exact expectedS_specification

/-- Exact symbolic raw result in the controller's requested O, P, Q, R, S
order. -/
def RawResult : Prop :=
  StructureOResult ∧ StructurePResult ∧ StructureQResult ∧
    StructureRResult ∧ StructureSResult

/-- Exact-symbolic reporting changes neither structures nor stereochemistry. -/
def ReportedResult : Prop :=
  StructureOResult ∧ StructurePResult ∧ StructureQResult ∧
    StructureRResult ∧ StructureSResult

theorem raw_result : RawResult := by
  exact ⟨structure_o, structure_p, structure_q, structure_r, structure_s⟩

theorem reported_result : ReportedResult := by
  exact ⟨structure_o, structure_p, structure_q, structure_r, structure_s⟩

end IChO2026Problems.T9A8
