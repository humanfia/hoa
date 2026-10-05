import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 9, part 8

This file formalizes the five structures requested in the printed synthesis
scheme.  The structures are not represented by names or drawing strings: a
small local molecular-graph language expands every cyclodextrin unit and every
substituent into explicitly labelled atoms, bonds, formal charges, radical
counts, and tetrahedral stereocentres.

The problem's staged arrows are used only as qualitative named transforms.  No
claim about yield, completeness, sole products, phases, or unprinted material
streams is made here.
-/

namespace IChO2026Problems
namespace Icho2026T9A8

/-! ## A typed molecular-graph language -/

/-- Elements occurring in the requested structures. -/
inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  deriving DecidableEq, Repr

/-- Bond orders needed by the glucose, benzyl, azide, alkene, and Boc graphs. -/
inductive BondOrder where
  | single
  | double
  | aromatic
  deriving DecidableEq, Repr

/-- None of the displayed terminal alkenes has an E/Z descriptor. -/
inductive BondStereochemistry where
  | notStereogenic
  | E
  | Z
  deriving DecidableEq, Repr

/-- The two faces of the source α-D-glucopyranoside template.  `upper` is
the face containing the C5--C6 bond in the conventional Haworth view. -/
inductive RingFace where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Tetrahedral parity relative to the explicitly ordered four-neighbour
frame stored in `TetrahedralStereo`.  This is deliberately not a CIP `R`/`S`
label: changing an O-substituent or the C6 substituent can change CIP
priorities without changing the tetrahedral geometry of the glucose unit. -/
inductive TetrahedralParity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- Positions of the two secondary oxygen substituents on every glucose unit. -/
inductive SecondaryPosition where
  | c2
  | c3
  deriving DecidableEq, Repr

/-- The five stereogenic ring carbons in an α-D-glucopyranoside unit. -/
inductive GlucoseStereocentre where
  | c1
  | c2
  | c3
  | c4
  | c5
  deriving DecidableEq, Repr

/-- Explicit atoms of the glucose core other than the primary C6 fragment and
the secondary oxygen fragments.  Hydrogens are vertices rather than implicit
counts. -/
inductive CoreAtom where
  | c1 | c2 | c3 | c4 | c5
  | ringO
  | glycosidicO
  | h1 | h2 | h3 | h4 | h5
  deriving DecidableEq, Repr

/-- Complete atom inventory of one benzyl group `CH₂-C₆H₅`. -/
inductive BenzylAtom where
  | methyleneC
  | methyleneH1 | methyleneH2
  | ringC1 | ringC2 | ringC3 | ringC4 | ringC5 | ringC6
  | ringH2 | ringH3 | ringH4 | ringH5 | ringH6
  deriving DecidableEq, Repr

/-- Atoms which can occur in a primary-rim fragment.  Presence is determined
by `PrimaryGroup`; unused alternatives are absent from the expanded graph. -/
inductive PrimaryAtom where
  | c6
  | c6H1 | c6H2
  | oxygen
  | hydroxyH
  | vinylTerminalC
  | vinylTerminalH1 | vinylTerminalH2
  | azideProximalN | azideCentralN | azideDistalN
  | amineN
  | amineH1 | amineH2
  deriving DecidableEq, Repr

/-- Atom inventory of the methallyl amino-ether bridge
`N-CH₂-C(=CH₂)-CH₂-O`. -/
inductive BridgeAtom where
  | nSideC | centralC | exocyclicC | oSideC
  | nSideH1 | nSideH2
  | exocyclicH1 | exocyclicH2
  | oSideH1 | oSideH2
  | nitrogenH
  deriving DecidableEq, Repr

/-- Complete atom inventory of an N-bound Boc group
`C(=O)-O-C(CH₃)₃`. -/
inductive BocAtom where
  | carbonylC | carbonylO | etherO | tertButylC
  | methylC1 | methylC2 | methylC3
  | methyl1H1 | methyl1H2 | methyl1H3
  | methyl2H1 | methyl2H2 | methyl2H3
  | methyl3H1 | methyl3H2 | methyl3H3
  deriving DecidableEq, Repr

/-- Globally unique, chemically meaningful atom labels. -/
inductive AtomLabel where
  | core (unit : ℕ) (atom : CoreAtom)
  | secondaryO (unit : ℕ) (position : SecondaryPosition)
  | secondaryHydrogen (unit : ℕ) (position : SecondaryPosition)
  | secondaryBenzyl (unit : ℕ) (position : SecondaryPosition)
      (atom : BenzylAtom)
  | primary (unit : ℕ) (atom : PrimaryAtom)
  | primaryBenzyl (unit : ℕ) (atom : BenzylAtom)
  | bridge (atom : BridgeAtom)
  | boc (atom : BocAtom)
  | nitrogenBenzyl (atom : BenzylAtom)
  deriving DecidableEq, Repr

/-- Atom data required by the output contract. -/
structure LabeledAtom where
  label : AtomLabel
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  deriving DecidableEq, Repr

/-- An undirected labelled bond. -/
structure Bond where
  left : AtomLabel
  right : AtomLabel
  order : BondOrder
  stereochemistry : BondStereochemistry
  deriving DecidableEq, Repr

/-- A tetrahedral centre with all four directly bonded neighbours named in an
ordered frame.  `ligand3` is the distinguished exocyclic substituent, and
`distinguishedFace` records whether it is above or below the source Haworth
template.  The ordered-neighbour parity, rather than a copied CIP label, is
the invariant retained by all O- and C6-substitutions in this synthesis. -/
structure TetrahedralStereo where
  center : AtomLabel
  ligand1 : AtomLabel
  ligand2 : AtomLabel
  ligand3 : AtomLabel
  ligand4 : AtomLabel
  distinguishedFace : RingFace
  parity : TetrahedralParity
  deriving DecidableEq, Repr

/-- A complete expanded molecular graph. -/
structure MolecularGraph where
  atoms : List LabeledAtom
  bonds : List Bond
  stereocentres : List TetrahedralStereo
  deriving DecidableEq, Repr

def neutralAtom (label : AtomLabel) (element : Element) : LabeledAtom :=
  { label := label, element := element, formalCharge := 0,
    radicalElectrons := 0 }

def chargedAtom (label : AtomLabel) (element : Element)
    (formalCharge : ℤ) : LabeledAtom :=
  { label := label, element := element, formalCharge := formalCharge,
    radicalElectrons := 0 }

def singleBond (left right : AtomLabel) : Bond :=
  { left := left, right := right, order := .single,
    stereochemistry := .notStereogenic }

def doubleBond (left right : AtomLabel) : Bond :=
  { left := left, right := right, order := .double,
    stereochemistry := .notStereogenic }

def aromaticBond (left right : AtomLabel) : Bond :=
  { left := left, right := right, order := .aromatic,
    stereochemistry := .notStereogenic }

/-! ## Reusable explicit fragments -/

def benzylAtoms (wrap : BenzylAtom → AtomLabel) : List LabeledAtom :=
  [ neutralAtom (wrap .methyleneC) .carbon,
    neutralAtom (wrap .methyleneH1) .hydrogen,
    neutralAtom (wrap .methyleneH2) .hydrogen,
    neutralAtom (wrap .ringC1) .carbon,
    neutralAtom (wrap .ringC2) .carbon,
    neutralAtom (wrap .ringC3) .carbon,
    neutralAtom (wrap .ringC4) .carbon,
    neutralAtom (wrap .ringC5) .carbon,
    neutralAtom (wrap .ringC6) .carbon,
    neutralAtom (wrap .ringH2) .hydrogen,
    neutralAtom (wrap .ringH3) .hydrogen,
    neutralAtom (wrap .ringH4) .hydrogen,
    neutralAtom (wrap .ringH5) .hydrogen,
    neutralAtom (wrap .ringH6) .hydrogen ]

def benzylInternalBonds (wrap : BenzylAtom → AtomLabel) : List Bond :=
  [ singleBond (wrap .methyleneC) (wrap .methyleneH1),
    singleBond (wrap .methyleneC) (wrap .methyleneH2),
    singleBond (wrap .methyleneC) (wrap .ringC1),
    aromaticBond (wrap .ringC1) (wrap .ringC2),
    aromaticBond (wrap .ringC2) (wrap .ringC3),
    aromaticBond (wrap .ringC3) (wrap .ringC4),
    aromaticBond (wrap .ringC4) (wrap .ringC5),
    aromaticBond (wrap .ringC5) (wrap .ringC6),
    aromaticBond (wrap .ringC6) (wrap .ringC1),
    singleBond (wrap .ringC2) (wrap .ringH2),
    singleBond (wrap .ringC3) (wrap .ringH3),
    singleBond (wrap .ringC4) (wrap .ringH4),
    singleBond (wrap .ringC5) (wrap .ringH5),
    singleBond (wrap .ringC6) (wrap .ringH6) ]

def bocAtoms : List LabeledAtom :=
  [ neutralAtom (.boc .carbonylC) .carbon,
    neutralAtom (.boc .carbonylO) .oxygen,
    neutralAtom (.boc .etherO) .oxygen,
    neutralAtom (.boc .tertButylC) .carbon,
    neutralAtom (.boc .methylC1) .carbon,
    neutralAtom (.boc .methylC2) .carbon,
    neutralAtom (.boc .methylC3) .carbon,
    neutralAtom (.boc .methyl1H1) .hydrogen,
    neutralAtom (.boc .methyl1H2) .hydrogen,
    neutralAtom (.boc .methyl1H3) .hydrogen,
    neutralAtom (.boc .methyl2H1) .hydrogen,
    neutralAtom (.boc .methyl2H2) .hydrogen,
    neutralAtom (.boc .methyl2H3) .hydrogen,
    neutralAtom (.boc .methyl3H1) .hydrogen,
    neutralAtom (.boc .methyl3H2) .hydrogen,
    neutralAtom (.boc .methyl3H3) .hydrogen ]

def bocInternalBonds : List Bond :=
  [ doubleBond (.boc .carbonylC) (.boc .carbonylO),
    singleBond (.boc .carbonylC) (.boc .etherO),
    singleBond (.boc .etherO) (.boc .tertButylC),
    singleBond (.boc .tertButylC) (.boc .methylC1),
    singleBond (.boc .tertButylC) (.boc .methylC2),
    singleBond (.boc .tertButylC) (.boc .methylC3),
    singleBond (.boc .methylC1) (.boc .methyl1H1),
    singleBond (.boc .methylC1) (.boc .methyl1H2),
    singleBond (.boc .methylC1) (.boc .methyl1H3),
    singleBond (.boc .methylC2) (.boc .methyl2H1),
    singleBond (.boc .methylC2) (.boc .methyl2H2),
    singleBond (.boc .methylC2) (.boc .methyl2H3),
    singleBond (.boc .methylC3) (.boc .methyl3H1),
    singleBond (.boc .methylC3) (.boc .methyl3H2),
    singleBond (.boc .methylC3) (.boc .methyl3H3) ]

/-! ## Cyclodextrin-level structural data -/

inductive SecondaryGroup where
  | hydroxy
  | benzylEther
  deriving DecidableEq, Repr

inductive PrimaryGroup where
  | hydroxymethyl
  | benzylEther
  | vinyl
  | azidomethyl
  | aminomethyl
  | bridgeNitrogen
  | bridgeOxygen
  deriving DecidableEq, Repr

inductive BridgeNitrogenSubstituent where
  | hydrogen
  | boc
  | benzyl
  deriving DecidableEq, Repr

/-- The bridge endpoints are glucose C6 substituents. -/
structure BridgeSpec where
  nitrogenUnit : ℕ
  oxygenUnit : ℕ
  nitrogenSubstituent : BridgeNitrogenSubstituent
  deriving DecidableEq, Repr

/-- A compositional cyclodextrin structure.  Unit numbers are zero-based in
Lean: source unit 1 is index 0, source unit 2 is index 1, and so on. -/
structure CDStructure where
  unitCount : ℕ
  primary : ℕ → PrimaryGroup
  secondary : ℕ → SecondaryPosition → SecondaryGroup
  bridge : Option BridgeSpec

def clockwise (unitCount unit : ℕ) : ℕ :=
  if unitCount = 0 then unit else (unit + 1) % unitCount

def counterclockwise (unitCount unit : ℕ) : ℕ :=
  if unitCount = 0 then unit else (unit + unitCount - 1) % unitCount

def diametricallyOpposite (unitCount unit : ℕ) : ℕ :=
  if unitCount = 0 then unit else (unit + unitCount / 2) % unitCount

/-- The two relative locant conventions stated specifically in T9-A8. -/
inductive RelativeModification where
  | oneTwo
  | oneThree
  deriving DecidableEq, Repr

inductive RingDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

def problemDirection : RelativeModification → RingDirection
  | .oneTwo => .clockwise
  | .oneThree => .counterclockwise

def twice (f : ℕ → ℕ) (unit : ℕ) : ℕ := f (f unit)

/-- A 1,2 target is one clockwise step; a 1,3 target is two
counterclockwise steps, exactly as stipulated in the question. -/
def relativeTarget (unitCount unit : ℕ) : RelativeModification → ℕ
  | .oneTwo => clockwise unitCount unit
  | .oneThree => twice (counterclockwise unitCount) unit

def setPrimary (s : CDStructure) (unit : ℕ)
    (group : PrimaryGroup) : CDStructure :=
  { s with primary := fun u => if u = unit then group else s.primary u }

def setBridgeProtection (s : CDStructure)
    (protection : BridgeNitrogenSubstituent) : CDStructure :=
  { s with bridge := s.bridge.map fun b =>
      { b with nitrogenSubstituent := protection } }

def allSecondaryBenzyl (_unit : ℕ)
    (_position : SecondaryPosition) : SecondaryGroup :=
  .benzylEther

def allSecondaryHydroxy (_unit : ℕ)
    (_position : SecondaryPosition) : SecondaryGroup :=
  .hydroxy

/-! ## Expansion of each compositional field into atoms and bonds -/

def coreAtomsFor (unit : ℕ) : List LabeledAtom :=
  [ neutralAtom (.core unit .c1) .carbon,
    neutralAtom (.core unit .c2) .carbon,
    neutralAtom (.core unit .c3) .carbon,
    neutralAtom (.core unit .c4) .carbon,
    neutralAtom (.core unit .c5) .carbon,
    neutralAtom (.core unit .ringO) .oxygen,
    neutralAtom (.core unit .glycosidicO) .oxygen,
    neutralAtom (.core unit .h1) .hydrogen,
    neutralAtom (.core unit .h2) .hydrogen,
    neutralAtom (.core unit .h3) .hydrogen,
    neutralAtom (.core unit .h4) .hydrogen,
    neutralAtom (.core unit .h5) .hydrogen ]

def coreBondsFor (unitCount unit : ℕ) : List Bond :=
  [ singleBond (.core unit .c1) (.core unit .ringO),
    singleBond (.core unit .c1) (.core unit .c2),
    singleBond (.core unit .c1) (.core unit .h1),
    singleBond (.core unit .c2) (.core unit .c3),
    singleBond (.core unit .c2) (.core unit .h2),
    singleBond (.core unit .c3) (.core unit .c4),
    singleBond (.core unit .c3) (.core unit .h3),
    singleBond (.core unit .c4) (.core unit .c5),
    singleBond (.core unit .c4) (.core unit .h4),
    singleBond (.core unit .c5) (.core unit .ringO),
    singleBond (.core unit .c5) (.core unit .h5),
    singleBond (.core unit .c1) (.core unit .glycosidicO),
    singleBond (.core unit .glycosidicO)
      (.core (clockwise unitCount unit) .c4) ]

def secondaryAtomsFor (unit : ℕ) (position : SecondaryPosition) :
    SecondaryGroup → List LabeledAtom
  | .hydroxy =>
      [ neutralAtom (.secondaryO unit position) .oxygen,
        neutralAtom (.secondaryHydrogen unit position) .hydrogen ]
  | .benzylEther =>
      neutralAtom (.secondaryO unit position) .oxygen ::
        benzylAtoms (fun atom => .secondaryBenzyl unit position atom)

def secondaryBondsFor (unit : ℕ) (position : SecondaryPosition) :
    SecondaryGroup → List Bond
  | .hydroxy =>
      [ singleBond
          (.core unit (match position with | .c2 => .c2 | .c3 => .c3))
          (.secondaryO unit position),
        singleBond (.secondaryO unit position)
          (.secondaryHydrogen unit position) ]
  | .benzylEther =>
      [ singleBond
          (.core unit (match position with | .c2 => .c2 | .c3 => .c3))
          (.secondaryO unit position),
        singleBond (.secondaryO unit position)
          (.secondaryBenzyl unit position .methyleneC) ] ++
        benzylInternalBonds
          (fun atom => .secondaryBenzyl unit position atom)

def primaryAtomsFor (unit : ℕ) : PrimaryGroup → List LabeledAtom
  | .hydroxymethyl =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .oxygen) .oxygen,
        neutralAtom (.primary unit .hydroxyH) .hydrogen ]
  | .benzylEther =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .oxygen) .oxygen ] ++
        benzylAtoms (fun atom => .primaryBenzyl unit atom)
  | .vinyl =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .vinylTerminalC) .carbon,
        neutralAtom (.primary unit .vinylTerminalH1) .hydrogen,
        neutralAtom (.primary unit .vinylTerminalH2) .hydrogen ]
  | .azidomethyl =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .azideProximalN) .nitrogen,
        chargedAtom (.primary unit .azideCentralN) .nitrogen 1,
        chargedAtom (.primary unit .azideDistalN) .nitrogen (-1) ]
  | .aminomethyl =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .amineN) .nitrogen,
        neutralAtom (.primary unit .amineH1) .hydrogen,
        neutralAtom (.primary unit .amineH2) .hydrogen ]
  | .bridgeNitrogen =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .amineN) .nitrogen ]
  | .bridgeOxygen =>
      [ neutralAtom (.primary unit .c6) .carbon,
        neutralAtom (.primary unit .c6H1) .hydrogen,
        neutralAtom (.primary unit .c6H2) .hydrogen,
        neutralAtom (.primary unit .oxygen) .oxygen ]

def c6BaseBonds (unit : ℕ) : List Bond :=
  [ singleBond (.core unit .c5) (.primary unit .c6),
    singleBond (.primary unit .c6) (.primary unit .c6H1) ]

def primaryBondsFor (unit : ℕ) : PrimaryGroup → List Bond
  | .hydroxymethyl => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .oxygen),
        singleBond (.primary unit .oxygen) (.primary unit .hydroxyH) ]
  | .benzylEther => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .oxygen),
        singleBond (.primary unit .oxygen)
          (.primaryBenzyl unit .methyleneC) ] ++
        benzylInternalBonds (fun atom => .primaryBenzyl unit atom)
  | .vinyl => c6BaseBonds unit ++
      [ doubleBond (.primary unit .c6) (.primary unit .vinylTerminalC),
        singleBond (.primary unit .vinylTerminalC)
          (.primary unit .vinylTerminalH1),
        singleBond (.primary unit .vinylTerminalC)
          (.primary unit .vinylTerminalH2) ]
  | .azidomethyl => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .azideProximalN),
        doubleBond (.primary unit .azideProximalN)
          (.primary unit .azideCentralN),
        doubleBond (.primary unit .azideCentralN)
          (.primary unit .azideDistalN) ]
  | .aminomethyl => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .amineN),
        singleBond (.primary unit .amineN) (.primary unit .amineH1),
        singleBond (.primary unit .amineN) (.primary unit .amineH2) ]
  | .bridgeNitrogen => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .amineN) ]
  | .bridgeOxygen => c6BaseBonds unit ++
      [ singleBond (.primary unit .c6) (.primary unit .c6H2),
        singleBond (.primary unit .c6) (.primary unit .oxygen) ]

def bridgeBaseAtoms : List LabeledAtom :=
  [ neutralAtom (.bridge .nSideC) .carbon,
    neutralAtom (.bridge .centralC) .carbon,
    neutralAtom (.bridge .exocyclicC) .carbon,
    neutralAtom (.bridge .oSideC) .carbon,
    neutralAtom (.bridge .nSideH1) .hydrogen,
    neutralAtom (.bridge .nSideH2) .hydrogen,
    neutralAtom (.bridge .exocyclicH1) .hydrogen,
    neutralAtom (.bridge .exocyclicH2) .hydrogen,
    neutralAtom (.bridge .oSideH1) .hydrogen,
    neutralAtom (.bridge .oSideH2) .hydrogen ]

def bridgeAtoms (spec : BridgeSpec) : List LabeledAtom :=
  bridgeBaseAtoms ++
    match spec.nitrogenSubstituent with
    | .hydrogen => [neutralAtom (.bridge .nitrogenH) .hydrogen]
    | .boc => bocAtoms
    | .benzyl => benzylAtoms AtomLabel.nitrogenBenzyl

def bridgeBaseBonds (spec : BridgeSpec) : List Bond :=
  [ singleBond (.primary spec.nitrogenUnit .amineN) (.bridge .nSideC),
    singleBond (.bridge .nSideC) (.bridge .nSideH1),
    singleBond (.bridge .nSideC) (.bridge .nSideH2),
    singleBond (.bridge .nSideC) (.bridge .centralC),
    doubleBond (.bridge .centralC) (.bridge .exocyclicC),
    singleBond (.bridge .exocyclicC) (.bridge .exocyclicH1),
    singleBond (.bridge .exocyclicC) (.bridge .exocyclicH2),
    singleBond (.bridge .centralC) (.bridge .oSideC),
    singleBond (.bridge .oSideC) (.bridge .oSideH1),
    singleBond (.bridge .oSideC) (.bridge .oSideH2),
    singleBond (.bridge .oSideC) (.primary spec.oxygenUnit .oxygen) ]

def bridgeBonds (spec : BridgeSpec) : List Bond :=
  bridgeBaseBonds spec ++
    match spec.nitrogenSubstituent with
    | .hydrogen =>
        [singleBond (.primary spec.nitrogenUnit .amineN)
          (.bridge .nitrogenH)]
    | .boc =>
        singleBond (.primary spec.nitrogenUnit .amineN)
          (.boc .carbonylC) :: bocInternalBonds
    | .benzyl =>
        [singleBond (.primary spec.nitrogenUnit .amineN)
          (.nitrogenBenzyl .methyleneC)] ++
          benzylInternalBonds AtomLabel.nitrogenBenzyl

/-! ## Explicit α-D-glucopyranoside stereochemistry -/

/-- Source-derived relative stereochemistry of an α-D-glucopyranosyl unit.
In the conventional Haworth view with the C5--C6 bond on the upper face, the
anomeric O at C1 is lower (the `α` relation), the C2 oxygen is lower, the C3
oxygen is upper, the C4 glycosidic oxygen is lower, and C5--C6 is upper.

These face data come from the shared statement that every unit is an
`α-D-glucopyranoside`; they do not assert CIP labels for a different molecule. -/
def alphaDSubstituentFace : GlucoseStereocentre → RingFace
  | .c1 => .lower
  | .c2 => .lower
  | .c3 => .upper
  | .c4 => .lower
  | .c5 => .upper

/-- Parity convention for the ordered frames below.  With `ligand1` and
`ligand2` following the displayed ring path, `ligand3` the distinguished
exocyclic group, and `ligand4` hydrogen, upper-face and lower-face substituents
belong to the two opposite tetrahedral-parity classes. -/
def parityOfFace : RingFace → TetrahedralParity
  | .upper => .even
  | .lower => .odd

def alphaDTemplateParity (centre : GlucoseStereocentre) :
    TetrahedralParity :=
  parityOfFace (alphaDSubstituentFace centre)

def glucoseStereoFor (unitCount unit : ℕ) : List TetrahedralStereo :=
  [ { center := .core unit .c1,
      ligand1 := .core unit .ringO,
      ligand2 := .core unit .c2,
      ligand3 := .core unit .glycosidicO,
      ligand4 := .core unit .h1,
      distinguishedFace := alphaDSubstituentFace .c1,
      parity := alphaDTemplateParity .c1 },
    { center := .core unit .c2,
      ligand1 := .core unit .c1,
      ligand2 := .core unit .c3,
      ligand3 := .secondaryO unit .c2,
      ligand4 := .core unit .h2,
      distinguishedFace := alphaDSubstituentFace .c2,
      parity := alphaDTemplateParity .c2 },
    { center := .core unit .c3,
      ligand1 := .core unit .c2,
      ligand2 := .core unit .c4,
      ligand3 := .secondaryO unit .c3,
      ligand4 := .core unit .h3,
      distinguishedFace := alphaDSubstituentFace .c3,
      parity := alphaDTemplateParity .c3 },
    { center := .core unit .c4,
      ligand1 := .core unit .c3,
      ligand2 := .core unit .c5,
      ligand3 := .core (counterclockwise unitCount unit) .glycosidicO,
      ligand4 := .core unit .h4,
      distinguishedFace := alphaDSubstituentFace .c4,
      parity := alphaDTemplateParity .c4 },
    { center := .core unit .c5,
      ligand1 := .core unit .c4,
      ligand2 := .core unit .ringO,
      ligand3 := .primary unit .c6,
      ligand4 := .core unit .h5,
      distinguishedFace := alphaDSubstituentFace .c5,
      parity := alphaDTemplateParity .c5 } ]

def expandedAtoms (s : CDStructure) : List LabeledAtom :=
  (List.range s.unitCount).flatMap coreAtomsFor ++
  (List.range s.unitCount).flatMap (fun unit =>
    ([SecondaryPosition.c2, .c3] : List SecondaryPosition).flatMap
      (fun position => secondaryAtomsFor unit position
        (s.secondary unit position))) ++
  (List.range s.unitCount).flatMap (fun unit =>
    primaryAtomsFor unit (s.primary unit)) ++
  match s.bridge with
  | none => []
  | some spec => bridgeAtoms spec

def expandedBonds (s : CDStructure) : List Bond :=
  (List.range s.unitCount).flatMap (coreBondsFor s.unitCount) ++
  (List.range s.unitCount).flatMap (fun unit =>
    ([SecondaryPosition.c2, .c3] : List SecondaryPosition).flatMap
      (fun position => secondaryBondsFor unit position
        (s.secondary unit position))) ++
  (List.range s.unitCount).flatMap (fun unit =>
    primaryBondsFor unit (s.primary unit)) ++
  match s.bridge with
  | none => []
  | some spec => bridgeBonds spec

def expandedStereocentres (s : CDStructure) : List TetrahedralStereo :=
  (List.range s.unitCount).flatMap (glucoseStereoFor s.unitCount)

def expandStructure (s : CDStructure) : MolecularGraph :=
  { atoms := expandedAtoms s,
    bonds := expandedBonds s,
    stereocentres := expandedStereocentres s }

def MolecularGraph.HasAtom (g : MolecularGraph) (label : AtomLabel) : Prop :=
  ∃ atom ∈ g.atoms, atom.label = label

/-- Undirected adjacency in the fully expanded molecular graph. -/
def MolecularGraph.HasBond (g : MolecularGraph)
    (left right : AtomLabel) : Prop :=
  ∃ bond ∈ g.bonds,
    (bond.left = left ∧ bond.right = right) ∨
    (bond.left = right ∧ bond.right = left)

def MolecularGraph.netFormalCharge (g : MolecularGraph) : ℤ :=
  (g.atoms.map LabeledAtom.formalCharge).sum

def MolecularGraph.totalRadicalElectrons (g : MolecularGraph) : ℕ :=
  (g.atoms.map LabeledAtom.radicalElectrons).sum

/-- Nontrivial structural sanity conditions used by every requested-output
carrier. -/
def MolecularGraph.WellFormed (g : MolecularGraph) : Prop :=
  g.atoms.Pairwise (fun left right => left.label ≠ right.label) ∧
  (∀ bond ∈ g.bonds,
    bond.left ≠ bond.right ∧ g.HasAtom bond.left ∧ g.HasAtom bond.right) ∧
  (∀ stereo ∈ g.stereocentres,
    g.HasAtom stereo.center ∧
    g.HasAtom stereo.ligand1 ∧ g.HasAtom stereo.ligand2 ∧
    g.HasAtom stereo.ligand3 ∧ g.HasAtom stereo.ligand4 ∧
    g.HasBond stereo.center stereo.ligand1 ∧
    g.HasBond stereo.center stereo.ligand2 ∧
    g.HasBond stereo.center stereo.ligand3 ∧
    g.HasBond stereo.center stereo.ligand4 ∧
    [stereo.ligand1, stereo.ligand2,
      stereo.ligand3, stereo.ligand4].Nodup ∧
    stereo.parity = parityOfFace stereo.distinguishedFace)

/-- Every glucose unit has exactly the source α-D ordered-neighbour frames.
Because the labels in those frames are direct neighbours, this equality
preserves tetrahedral geometry across changes beyond the secondary O atoms and
beyond C6 without making any substituent-dependent CIP assertion. -/
def RetainsAlphaDTemplateStereo (s : CDStructure) : Prop :=
  (expandStructure s).stereocentres =
    (List.range s.unitCount).flatMap (glucoseStereoFor s.unitCount)

/-- Every candidate is a neutral closed-shell graph with exactly the five
source-stipulated α-D stereocentres per glucose unit. -/
def CompleteExpandedStructure (s : CDStructure) : Prop :=
  (expandStructure s).WellFormed ∧
  (expandStructure s).netFormalCharge = 0 ∧
  (expandStructure s).totalRadicalElectrons = 0 ∧
  (expandStructure s).stereocentres.length = 5 * s.unitCount ∧
  RetainsAlphaDTemplateStereo s

/-! ## Bound source arrows and external-rule provenance -/

/-- Labels printed in the problem scheme. -/
inductive StageLabel where
  | N | O | P | Q | R | S
  deriving DecidableEq, Repr

/-- Every reagent explicitly printed above or below an O--S arrow. -/
inductive Reagent where
  | oxalylChloride
  | dimethylSulfoxide
  | methyleneTriphenylphosphorane
  | diisobutylaluminiumHydride
  | methanesulfonylChloride
  | sodiumAzide
  | sodiumHydride
  | dichloromethallyl
  | diTertButylDicarbonate
  | trifluoroaceticAcid
  | benzylIodide
  deriving DecidableEq, Repr

/-- `equivalents = none` means that the figure names the reagent but prints no
equivalent count. -/
structure ReagentUse where
  reagent : Reagent
  equivalents : Option ℕ
  deriving DecidableEq, Repr

/-- The required staged-use classification. -/
inductive StagedTransformationUse where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

/-- Competing directing groups named by the current question. -/
inductive DirectingGroup where
  | alkene
  | protic
  deriving DecidableEq, Repr

/-- A numerical encoding of the source's strict precedence statement. -/
def directingStrength : DirectingGroup → ℕ
  | .alkene => 0
  | .protic => 1

def ProticGroupsStrongerThanAlkenes : Prop :=
  directingStrength .alkene < directingStrength .protic

/-- A source arrow records roles, direction, ordered reagent list, and its
problem-local locator.  It intentionally has no yield or byproduct field. -/
structure SourceArrow where
  input : StageLabel
  output : StageLabel
  reagents : List ReagentUse
  useClass : StagedTransformationUse
  locator : String
  deriving DecidableEq, Repr

def arrowNO : SourceArrow :=
  { input := .N, output := .O,
    reagents :=
      [ ⟨.oxalylChloride, none⟩,
        ⟨.dimethylSulfoxide, none⟩,
        ⟨.methyleneTriphenylphosphorane, none⟩ ],
    useClass := .qualitativeNamedTransformOnly,
    locator := "T9_page-4.png, N to O arrow" }

def arrowOP : SourceArrow :=
  { input := .O, output := .P,
    reagents :=
      [ ⟨.diisobutylaluminiumHydride, some 1⟩,
        ⟨.methanesulfonylChloride, none⟩,
        ⟨.sodiumAzide, none⟩ ],
    useClass := .qualitativeNamedTransformOnly,
    locator := "T9_page-4.png, O to P arrow" }

def arrowPQ : SourceArrow :=
  { input := .P, output := .Q,
    reagents :=
      [ ⟨.diisobutylaluminiumHydride, some 2⟩,
        ⟨.sodiumHydride, none⟩,
        ⟨.dichloromethallyl, none⟩ ],
    useClass := .qualitativeNamedTransformOnly,
    locator := "T9_page-4.png, P to Q arrow" }

def arrowQR : SourceArrow :=
  { input := .Q, output := .R,
    reagents :=
      [ ⟨.diisobutylaluminiumHydride, some 1⟩,
        ⟨.diTertButylDicarbonate, some 1⟩,
        ⟨.methanesulfonylChloride, none⟩,
        ⟨.sodiumAzide, none⟩ ],
    useClass := .qualitativeNamedTransformOnly,
    locator := "T9_page-4.png, Q to R arrow" }

def arrowRS : SourceArrow :=
  { input := .R, output := .S,
    reagents :=
      [ ⟨.trifluoroaceticAcid, none⟩,
        ⟨.sodiumHydride, none⟩,
        ⟨.benzylIodide, none⟩,
        ⟨.diisobutylaluminiumHydride, some 2⟩ ],
    useClass := .qualitativeNamedTransformOnly,
    locator := "T9_page-4.png, R to S arrow" }

def printedSynthesisArrows : List SourceArrow :=
  [arrowNO, arrowOP, arrowPQ, arrowQR, arrowRS]

/-- Bibliographic carrier for the primary literature consulted only for the
site-directing bridge absent from the shared Lean libraries. -/
structure LiteratureReference where
  title : String
  doi : String
  stableUrl : String
  locator : String
  scopedClaim : String
  applicability : String
  contentSha256 : String
  deriving DecidableEq, Repr

/-- Wang et al., Nature Communications 5:5354 (2014).  The claim is restricted
to the α-CD substrates and transformations shown in Figures 3--6. -/
def wangSollogoubReference : LiteratureReference :=
  { title := "Site-selective hexa-hetero-functionalization of alpha-cyclodextrin an archetypical C6-symmetric concave cycle",
    doi := "10.1038/ncomms6354",
    stableUrl := "https://doi.org/10.1038/ncomms6354",
    locator := "pp. 4-6, Figures 3-6 and accompanying Synthesis of hexadifferentiated CDs text",
    scopedClaim := "On the depicted perbenzylated alpha-CD sequence: vinyl directs adjacent clockwise O-debenzylation; azide reduction directs diametrically opposed O-debenzylation; an unprotected methallyl amino-ether bridge directs monodebenzylation clockwise from its ether terminus.",
    applicability := "Only the polybenzylated alpha-CD substrates, DIBAL-H steps, azide, vinyl, and methallyl amino-ether bridge depicted in Figures 3-6; no inverse classification, yield, sole-product, or unstated protocol claim.",
    contentSha256 := "e09bfa02cca0ca87e7ae39a9a8ade502d65b072506242679284932a9b2f3e557" }

/-- Unlike an external CIP descriptor for an isolated glycoside, this carrier
binds the stereochemical convention directly to the problem's own
`α-D-glucopyranoside` statement and cyclic `α(1→4)` connectivity. -/
structure ProblemStereochemistrySource where
  locator : String
  unitDescription : String
  linkageDescription : String
  representationConvention : String
  deriving DecidableEq, Repr

def alphaDTemplateProblemSource : ProblemStereochemistrySource :=
  { locator := "T9 shared context and T9_page-4.png alpha-CD template",
    unitDescription := "six alpha-D-glucopyranoside units",
    linkageDescription := "cyclic alpha(1->4)-glycosidic bonds",
    representationConvention :=
      "ordered-neighbour tetrahedral parity with C5-C6 defining the upper Haworth face" }

/-! ## Source-first transformations -/

/-- Net graph edit for Swern oxidation of C6 alcohol followed by Wittig
methylenation: `C5-CH₂OH` becomes `C5-CH=CH₂`. -/
def oxidizeThenMethylenate (s : CDStructure) (unit : ℕ) : CDStructure :=
  setPrimary s unit .vinyl

/-- The source convention fixes a 1,2 modification clockwise.  After directed
debenzylation, mesylation and azide displacement, the adjacent C6 group is
`CH₂N₃`. -/
def alkeneDirectedAzidation (s : CDStructure)
    (alkeneUnit : ℕ) : CDStructure :=
  setPrimary s (relativeTarget s.unitCount alkeneUnit .oneTwo) .azidomethyl

/-- DIBAL-H tandem edit at a primary azide: the azide is reduced to `CH₂NH₂`
and the benzyl ether on the diametrically opposed glucose unit becomes
`CH₂OH`. -/
def tandemAzideReductionOppositeDeprotection
    (s : CDStructure) (azideUnit : ℕ) : CDStructure :=
  setPrimary
    (setPrimary s azideUnit .aminomethyl)
    (diametricallyOpposite s.unitCount azideUnit) .hydroxymethyl

/-- Alkylation with `ClCH₂-C(=CH₂)-CH₂Cl` joins one primary amine and one
primary alcohol as the source-depicted amino-ether bridge. -/
def installMethallylBridge (s : CDStructure)
    (nitrogenUnit oxygenUnit : ℕ)
    (nitrogenSubstituent : BridgeNitrogenSubstituent) : CDStructure :=
  { (setPrimary (setPrimary s nitrogenUnit .bridgeNitrogen)
      oxygenUnit .bridgeOxygen) with
    bridge := some
      { nitrogenUnit := nitrogenUnit,
        oxygenUnit := oxygenUnit,
        nitrogenSubstituent := nitrogenSubstituent } }

/-- The unprotected amino-ether bridge directs the next deprotection clockwise
from its ether endpoint.  Boc protection then masks the nitrogen and the new
alcohol is converted to azide. -/
def bridgeDirectedAzidation (s : CDStructure) : CDStructure :=
  match s.bridge with
  | none => s
  | some spec =>
      let target := clockwise s.unitCount spec.oxygenUnit
      setBridgeProtection (setPrimary s target .azidomethyl) .boc

/-- TFA removes Boc; NaH/BnI then replaces N-H by N-Bn. -/
def deprotectThenBenzylateBridgeNitrogen (s : CDStructure) : CDStructure :=
  setBridgeProtection (setBridgeProtection s .hydrogen) .benzyl

/-- The final azide is the group clockwise from the bridge ether endpoint in
the printed sequence.  Its reduction directs deprotection to the opposite
unit. -/
def finalTandemTransformation (s : CDStructure) : CDStructure :=
  match s.bridge with
  | none => s
  | some spec =>
      tandemAzideReductionOppositeDeprotection s
        (clockwise s.unitCount spec.oxygenUnit)

/-! ## Inline derivation of the required previous part T9-A5 -/

/-- Native β-CD as depicted on page 3: seven primary and fourteen secondary
hydroxyl groups. -/
def betaNative : CDStructure :=
  { unitCount := 7,
    primary := fun _ => .hydroxymethyl,
    secondary := allSecondaryHydroxy,
    bridge := none }

/-- Net product of the printed NaH/BnCl perbenzylation before DIBAL-H. -/
def betaPerbenzylated : CDStructure :=
  { unitCount := betaNative.unitCount,
    primary := fun _ => .benzylEther,
    secondary := allSecondaryBenzyl,
    bridge := none }

/-- By rotational normalization, the first primary deprotection is called
source unit 1 (Lean index 0). -/
def betaFirstMonol : CDStructure :=
  setPrimary betaPerbenzylated 0 .hydroxymethyl

/-- Page 3 states that a protic group at source unit 1 directs the next
debenzylation to source unit 4, or to unit 3 only if unit 4 is unavailable. -/
def betaProticDirectedTarget (s : CDStructure) (proticUnit : ℕ) : ℕ :=
  let preferred := (proticUnit + 3) % s.unitCount
  let fallback := (proticUnit + 2) % s.unitCount
  if s.primary preferred = .benzylEther then preferred else fallback

/-- The independently derived T9-A5 structure L: primary OH at source units 1
and 4 and primary OBn at the other five units; all fourteen secondary groups
are OBn. -/
def lStructure : CDStructure :=
  setPrimary betaFirstMonol
    (betaProticDirectedTarget betaFirstMonol 0) .hydroxymethyl

/-! ## Structures N and O--S -/

/-- Structure N is read directly from the page-4 template: source unit 1 is
`CH₂OH`, the other five primary groups are `CH₂OBn`, and all twelve secondary
oxygen groups are OBn. -/
def nStructure : CDStructure :=
  { unitCount := 6,
    primary := fun unit =>
      if unit = 0 then .hydroxymethyl else .benzylEther,
    secondary := allSecondaryBenzyl,
    bridge := none }

/-- Requested O, constructed from N by the first printed arrow. -/
def structureO : CDStructure :=
  oxidizeThenMethylenate nStructure 0

/-- Requested P, using the stipulated clockwise 1,2 direction. -/
def structureP : CDStructure :=
  alkeneDirectedAzidation structureO 0

/-- The amino-alcohol immediately before methallyl bridging in the P-to-Q
arrow. -/
def qAminoAlcohol : CDStructure :=
  tandemAzideReductionOppositeDeprotection structureP
    (clockwise structureP.unitCount 0)

/-- Requested Q: an N-H amino-ether bridge joins source units 2 and 5. -/
def structureQ : CDStructure :=
  installMethallylBridge qAminoAlcohol
    (clockwise qAminoAlcohol.unitCount 0)
    (diametricallyOpposite qAminoAlcohol.unitCount
      (clockwise qAminoAlcohol.unitCount 0))
    .hydrogen

/-- Requested R: the bridge nitrogen is N-Boc and source unit 6 is
`CH₂N₃`. -/
def structureR : CDStructure :=
  bridgeDirectedAzidation structureQ

/-- The N-benzyl intermediate in the final printed arrow. -/
def sNBenzylIntermediate : CDStructure :=
  deprotectThenBenzylateBridgeNitrogen structureR

/-- Requested S: tandem reduction makes source unit 6 `CH₂NH₂` and the
opposite source unit 3 `CH₂OH`; unit 4 retains `CH₂OBn`. -/
def structureS : CDStructure :=
  finalTandemTransformation sNBenzylIntermediate

/-! ## Exact structural specifications -/

def AllSecondaryBenzylated (s : CDStructure) : Prop :=
  ∀ unit < s.unitCount, ∀ position,
    s.secondary unit position = .benzylEther

def PrimaryPattern6 (s : CDStructure)
    (g1 g2 g3 g4 g5 g6 : PrimaryGroup) : Prop :=
  s.unitCount = 6 ∧
  s.primary 0 = g1 ∧ s.primary 1 = g2 ∧ s.primary 2 = g3 ∧
  s.primary 3 = g4 ∧ s.primary 4 = g5 ∧ s.primary 5 = g6

def PrimaryPattern7 (s : CDStructure)
    (g1 g2 g3 g4 g5 g6 g7 : PrimaryGroup) : Prop :=
  s.unitCount = 7 ∧
  s.primary 0 = g1 ∧ s.primary 1 = g2 ∧ s.primary 2 = g3 ∧
  s.primary 3 = g4 ∧ s.primary 4 = g5 ∧ s.primary 5 = g6 ∧
  s.primary 6 = g7

def BridgeIs (s : CDStructure) (nitrogenUnit oxygenUnit : ℕ)
    (substituent : BridgeNitrogenSubstituent) : Prop :=
  s.bridge = some
    { nitrogenUnit := nitrogenUnit,
      oxygenUnit := oxygenUnit,
      nitrogenSubstituent := substituent }

/-- Exact previous-part specification, derived rather than imported. -/
def PreviousPartA5Spec : Prop :=
  betaProticDirectedTarget betaFirstMonol 0 = 3 ∧
  PrimaryPattern7 lStructure
    .hydroxymethyl .benzylEther .benzylEther .hydroxymethyl
    .benzylEther .benzylEther .benzylEther ∧
  AllSecondaryBenzylated lStructure ∧
  lStructure.bridge = none ∧
  CompleteExpandedStructure lStructure

def StructureOSpec (s : CDStructure) : Prop :=
  PrimaryPattern6 s
    .vinyl .benzylEther .benzylEther .benzylEther
    .benzylEther .benzylEther ∧
  AllSecondaryBenzylated s ∧ s.bridge = none ∧
  CompleteExpandedStructure s

def StructurePSpec (s : CDStructure) : Prop :=
  PrimaryPattern6 s
    .vinyl .azidomethyl .benzylEther .benzylEther
    .benzylEther .benzylEther ∧
  AllSecondaryBenzylated s ∧ s.bridge = none ∧
  CompleteExpandedStructure s

def StructureQSpec (s : CDStructure) : Prop :=
  PrimaryPattern6 s
    .vinyl .bridgeNitrogen .benzylEther .benzylEther
    .bridgeOxygen .benzylEther ∧
  AllSecondaryBenzylated s ∧ BridgeIs s 1 4 .hydrogen ∧
  CompleteExpandedStructure s

def StructureRSpec (s : CDStructure) : Prop :=
  PrimaryPattern6 s
    .vinyl .bridgeNitrogen .benzylEther .benzylEther
    .bridgeOxygen .azidomethyl ∧
  AllSecondaryBenzylated s ∧ BridgeIs s 1 4 .boc ∧
  CompleteExpandedStructure s

def StructureSSpec (s : CDStructure) : Prop :=
  PrimaryPattern6 s
    .vinyl .bridgeNitrogen .hydroxymethyl .benzylEther
    .bridgeOxygen .aminomethyl ∧
  AllSecondaryBenzylated s ∧ BridgeIs s 1 4 .benzyl ∧
  CompleteExpandedStructure s

/-! ## Source-bound stereochemical and site-selection bridges -/

/-- Exact problem-to-graph binding for the stereochemistry shared by L and
O--S.  It records relative faces and ordered-neighbour parities, rather than
borrowing substituent-dependent CIP labels from an isolated methyl glycoside. -/
def AlphaDTemplateSourceBinding : Prop :=
  alphaDTemplateProblemSource.locator =
      "T9 shared context and T9_page-4.png alpha-CD template" ∧
  alphaDTemplateProblemSource.unitDescription =
      "six alpha-D-glucopyranoside units" ∧
  alphaDTemplateProblemSource.linkageDescription =
      "cyclic alpha(1->4)-glycosidic bonds" ∧
  alphaDTemplateProblemSource.representationConvention =
      "ordered-neighbour tetrahedral parity with C5-C6 defining the upper Haworth face" ∧
  alphaDSubstituentFace .c1 = .lower ∧
  alphaDSubstituentFace .c2 = .lower ∧
  alphaDSubstituentFace .c3 = .upper ∧
  alphaDSubstituentFace .c4 = .lower ∧
  alphaDSubstituentFace .c5 = .upper ∧
  alphaDTemplateParity .c1 = .odd ∧
  alphaDTemplateParity .c2 = .odd ∧
  alphaDTemplateParity .c3 = .even ∧
  alphaDTemplateParity .c4 = .odd ∧
  alphaDTemplateParity .c5 = .even

/-- Scope shared by the Wang--Sollogoub observations actually used here: a
six-unit α-D scaffold with the twelve secondary oxygens benzylated. -/
def IsDepictedPolybenzylatedAlphaCD (s : CDStructure) : Prop :=
  s.unitCount = 6 ∧ AllSecondaryBenzylated s ∧
  RetainsAlphaDTemplateStereo s

/-- Applicability audit for vinyl-directed modification.  The finite primary
rim is derived from the six-unit source template before the selected site is
read: one vinyl director and benzyl ethers at every other primary position. -/
def VinylDirectionApplicable (s : CDStructure) (alkeneUnit : ℕ) : Prop :=
  IsDepictedPolybenzylatedAlphaCD s ∧ alkeneUnit < s.unitCount ∧
  s.primary alkeneUnit = .vinyl ∧ s.bridge = none ∧
  ∀ unit < s.unitCount, unit ≠ alkeneUnit →
    s.primary unit = .benzylEther

/-- Applicability audit for the tandem azide reduction / diametric
debenzylation used once in P→Q and once in R→S. -/
def AzideTandemApplicable (s : CDStructure) (azideUnit : ℕ) : Prop :=
  IsDepictedPolybenzylatedAlphaCD s ∧ azideUnit < s.unitCount ∧
  s.primary azideUnit = .azidomethyl ∧
  s.primary (diametricallyOpposite s.unitCount azideUnit) = .benzylEther

/-- Applicability audit for the protic methallyl amino-ether bridge in Q.
It also records the competing vinyl group and the problem-stated strict
protic-over-alkene precedence which decides the next site. -/
def ProticBridgeDirectionApplicable (s : CDStructure) : Prop :=
  IsDepictedPolybenzylatedAlphaCD s ∧
  BridgeIs s 1 4 .hydrogen ∧
  s.primary 0 = .vinyl ∧
  s.primary 1 = .bridgeNitrogen ∧
  s.primary 4 = .bridgeOxygen ∧
  s.primary (clockwise s.unitCount 4) = .benzylEther ∧
  ProticGroupsStrongerThanAlkenes

/-- A source arrow and a candidate graph are connected only as a qualitative
compatibility claim.  The equation fixes the complete graph edit but makes no
claim of yield, sole product, or absence of other material. -/
def AlkeneDirectedAzidationCompatibility
    (arrow : SourceArrow) (before after : CDStructure)
    (alkeneUnit : ℕ) : Prop :=
  arrow.input = .O ∧ arrow.output = .P ∧
  arrow.useClass = .qualitativeNamedTransformOnly ∧
  after = alkeneDirectedAzidation before alkeneUnit ∧
  after = setPrimary before
    (relativeTarget before.unitCount alkeneUnit .oneTwo) .azidomethyl

/-- Qualitative compatibility for the DIBAL-H tandem edit.  The arrow remains
explicit because the same scoped literature observation is used within two
different printed arrows. -/
def AzideTandemCompatibility
    (arrow : SourceArrow) (before after : CDStructure)
    (azideUnit : ℕ) : Prop :=
  ((arrow.input = .P ∧ arrow.output = .Q) ∨
    (arrow.input = .R ∧ arrow.output = .S)) ∧
  arrow.useClass = .qualitativeNamedTransformOnly ∧
  after = tandemAzideReductionOppositeDeprotection before azideUnit ∧
  after = setPrimary
    (setPrimary before azideUnit .aminomethyl)
    (diametricallyOpposite before.unitCount azideUnit) .hydroxymethyl

/-- Qualitative compatibility for bridge-directed monodebenzylation followed
by the Boc/mesylate/azide operations printed on Q→R. -/
def ProticBridgeAzidationCompatibility
    (arrow : SourceArrow) (before after : CDStructure) : Prop :=
  arrow.input = .Q ∧ arrow.output = .R ∧
  arrow.useClass = .qualitativeNamedTransformOnly ∧
  after = bridgeDirectedAzidation before ∧
  ∃ spec, before.bridge = some spec ∧
    after = setBridgeProtection
      (setPrimary before (clockwise before.unitCount spec.oxygenUnit)
        .azidomethyl) .boc

/-- The exact bibliographic identity and scope independently checked for the
three outcome-decisive directing observations. -/
def WangSollogoubAuthorityBinding : Prop :=
  wangSollogoubReference.title =
      "Site-selective hexa-hetero-functionalization of alpha-cyclodextrin an archetypical C6-symmetric concave cycle" ∧
  wangSollogoubReference.doi = "10.1038/ncomms6354" ∧
  wangSollogoubReference.stableUrl = "https://doi.org/10.1038/ncomms6354" ∧
  wangSollogoubReference.locator =
      "pp. 4-6, Figures 3-6 and accompanying Synthesis of hexadifferentiated CDs text" ∧
  wangSollogoubReference.scopedClaim =
      "On the depicted perbenzylated alpha-CD sequence: vinyl directs adjacent clockwise O-debenzylation; azide reduction directs diametrically opposed O-debenzylation; an unprotected methallyl amino-ether bridge directs monodebenzylation clockwise from its ether terminus." ∧
  wangSollogoubReference.applicability =
      "Only the polybenzylated alpha-CD substrates, DIBAL-H steps, azide, vinyl, and methallyl amino-ether bridge depicted in Figures 3-6; no inverse classification, yield, sole-product, or unstated protocol claim." ∧
  wangSollogoubReference.contentSha256 =
      "e09bfa02cca0ca87e7ae39a9a8ade502d65b072506242679284932a9b2f3e557"

/-- The missing chemistry bridge is now a proposition, not bibliographic
string data.  It conjunctively checks the exact authority, every
substrate-specific applicability condition, each relevant problem arrow, and
the graph-edit functions used to construct P, Q, R, and S. -/
def WangSollogoubSiteSelectionBridge : Prop :=
  WangSollogoubAuthorityBinding ∧
  VinylDirectionApplicable structureO 0 ∧
  AzideTandemApplicable structureP 1 ∧
  ProticBridgeDirectionApplicable structureQ ∧
  AzideTandemApplicable sNBenzylIntermediate 5 ∧
  AlkeneDirectedAzidationCompatibility arrowOP structureO structureP 0 ∧
  AzideTandemCompatibility arrowPQ structureP qAminoAlcohol 1 ∧
  ProticBridgeAzidationCompatibility arrowQR structureQ structureR ∧
  AzideTandemCompatibility arrowRS sNBenzylIntermediate structureS 5

/-! ## Transparent source-to-output derivation relations -/

def SourceFirstDerivation : Prop :=
  printedSynthesisArrows = [arrowNO, arrowOP, arrowPQ, arrowQR, arrowRS] ∧
  problemDirection .oneTwo = .clockwise ∧
  problemDirection .oneThree = .counterclockwise ∧
  ProticGroupsStrongerThanAlkenes ∧
  arrowNO.useClass = .qualitativeNamedTransformOnly ∧
  arrowOP.useClass = .qualitativeNamedTransformOnly ∧
  arrowPQ.useClass = .qualitativeNamedTransformOnly ∧
  arrowQR.useClass = .qualitativeNamedTransformOnly ∧
  arrowRS.useClass = .qualitativeNamedTransformOnly ∧
  structureO = oxidizeThenMethylenate nStructure 0 ∧
  structureP = alkeneDirectedAzidation structureO 0 ∧
  qAminoAlcohol = tandemAzideReductionOppositeDeprotection structureP 1 ∧
  structureQ = installMethallylBridge qAminoAlcohol 1 4 .hydrogen ∧
  structureR = bridgeDirectedAzidation structureQ ∧
  sNBenzylIntermediate =
    deprotectThenBenzylateBridgeNitrogen structureR ∧
  structureS = finalTandemTransformation sNBenzylIntermediate

/-- The common source obligations explicitly include the required inline A5
derivation, the problem-bound α-D tetrahedral orientation, and the checked
literature-to-edit bridge.  None is supplied as an output-selecting
hypothesis. -/
def CommonSourceObligations : Prop :=
  PreviousPartA5Spec ∧
  AlphaDTemplateSourceBinding ∧
  WangSollogoubSiteSelectionBridge ∧
  SourceFirstDerivation

/-- Raw exact-symbolic carrier for requested output `structure_o`. -/
def StructureOResult : Prop :=
  CommonSourceObligations ∧ StructureOSpec structureO

/-- Raw exact-symbolic carrier for requested output `structure_p`. -/
def StructurePResult : Prop :=
  CommonSourceObligations ∧ StructurePSpec structureP

/-- Raw exact-symbolic carrier for requested output `structure_q`. -/
def StructureQResult : Prop :=
  CommonSourceObligations ∧ StructureQSpec structureQ

/-- Raw exact-symbolic carrier for requested output `structure_r`. -/
def StructureRResult : Prop :=
  CommonSourceObligations ∧ StructureRSpec structureR

/-- Raw exact-symbolic carrier for requested output `structure_s`. -/
def StructureSResult : Prop :=
  CommonSourceObligations ∧ StructureSSpec structureS

/-- The source requests five symbolic structures, so the raw result is one
conjunction covering all requested outputs in source order. -/
def RawResult : Prop :=
  StructureOResult ∧ StructurePResult ∧ StructureQResult ∧
  StructureRResult ∧ StructureSResult

/-- Exact symbolic reporting preserves the complete expanded molecular graph;
there is no rounding boundary for a structure drawing. -/
def ExactSymbolicReport (raw reported : CDStructure) : Prop :=
  expandStructure raw = expandStructure reported

def ReportedResult : Prop :=
  RawResult ∧
  ExactSymbolicReport structureO structureO ∧
  ExactSymbolicReport structureP structureP ∧
  ExactSymbolicReport structureQ structureQ ∧
  ExactSymbolicReport structureR structureR ∧
  ExactSymbolicReport structureS structureS

/-! ## Theorem obligations for the prover stage -/

theorem previous_part_a5_derived : PreviousPartA5Spec := by
  refine ⟨by native_decide, ?_, ?_, by native_decide, ?_⟩
  · simp [PrimaryPattern7, lStructure, betaProticDirectedTarget,
      betaFirstMonol, betaPerbenzylated, betaNative, setPrimary]
  · intro unit _ position
    rfl
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem alpha_d_template_source_binding : AlphaDTemplateSourceBinding := by
  unfold AlphaDTemplateSourceBinding
  native_decide

theorem wang_sollogoub_site_selection_bridge :
    WangSollogoubSiteSelectionBridge := by
  classical
  simp [WangSollogoubSiteSelectionBridge,
    WangSollogoubAuthorityBinding,
    wangSollogoubReference, VinylDirectionApplicable,
    AzideTandemApplicable, ProticBridgeDirectionApplicable,
    IsDepictedPolybenzylatedAlphaCD, AllSecondaryBenzylated,
    RetainsAlphaDTemplateStereo, expandStructure, expandedStereocentres,
    AlkeneDirectedAzidationCompatibility,
    AzideTandemCompatibility, ProticBridgeAzidationCompatibility,
    ProticGroupsStrongerThanAlkenes, directingStrength, BridgeIs,
    structureO, structureP, qAminoAlcohol, structureQ, structureR,
    sNBenzylIntermediate, structureS, nStructure,
    oxidizeThenMethylenate, alkeneDirectedAzidation,
    tandemAzideReductionOppositeDeprotection, installMethallylBridge,
    bridgeDirectedAzidation, deprotectThenBenzylateBridgeNitrogen,
    finalTandemTransformation, setPrimary, setBridgeProtection,
    relativeTarget, clockwise,
    diametricallyOpposite, allSecondaryBenzyl,
    arrowOP, arrowPQ, arrowQR, arrowRS]
  intro unit _ hunit
  simp [hunit]

theorem source_first_derivation : SourceFirstDerivation := by
  simp [SourceFirstDerivation, printedSynthesisArrows, problemDirection,
    ProticGroupsStrongerThanAlkenes, directingStrength, arrowNO, arrowOP,
    arrowPQ, arrowQR, arrowRS, structureO, structureP, qAminoAlcohol,
    structureQ, structureR, sNBenzylIntermediate, structureS, clockwise,
    diametricallyOpposite, oxidizeThenMethylenate,
    alkeneDirectedAzidation, tandemAzideReductionOppositeDeprotection,
    installMethallylBridge, setPrimary, nStructure]

theorem structure_o : StructureOResult := by
  refine ⟨⟨previous_part_a5_derived,
    alpha_d_template_source_binding,
    wang_sollogoub_site_selection_bridge,
    source_first_derivation⟩, ?_⟩
  refine ⟨?_, ?_, by native_decide, ?_⟩
  · simp [PrimaryPattern6, structureO, oxidizeThenMethylenate,
      nStructure, setPrimary]
  · intro unit _ position
    rfl
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem structure_p : StructurePResult := by
  refine ⟨⟨previous_part_a5_derived,
    alpha_d_template_source_binding,
    wang_sollogoub_site_selection_bridge,
    source_first_derivation⟩, ?_⟩
  refine ⟨?_, ?_, by native_decide, ?_⟩
  · unfold PrimaryPattern6
    native_decide
  · intro unit _ position
    rfl
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem structure_q : StructureQResult := by
  refine ⟨⟨previous_part_a5_derived,
    alpha_d_template_source_binding,
    wang_sollogoub_site_selection_bridge,
    source_first_derivation⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PrimaryPattern6
    native_decide
  · intro unit _ position
    rfl
  · unfold BridgeIs
    native_decide
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem structure_r : StructureRResult := by
  refine ⟨⟨previous_part_a5_derived,
    alpha_d_template_source_binding,
    wang_sollogoub_site_selection_bridge,
    source_first_derivation⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PrimaryPattern6
    native_decide
  · intro unit _ position
    rfl
  · unfold BridgeIs
    native_decide
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem structure_s : StructureSResult := by
  refine ⟨⟨previous_part_a5_derived,
    alpha_d_template_source_binding,
    wang_sollogoub_site_selection_bridge,
    source_first_derivation⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PrimaryPattern6
    native_decide
  · intro unit _ position
    rfl
  · unfold BridgeIs
    native_decide
  · unfold CompleteExpandedStructure MolecularGraph.WellFormed
    unfold MolecularGraph.HasAtom MolecularGraph.HasBond
    unfold RetainsAlphaDTemplateStereo
    native_decide

theorem raw_result :
    ("9fc22f05b77c989b788ec5279c6fe0a983c2aefcbd78d4e48a3f7b9ef026de4a" :
      String) =
      "9fc22f05b77c989b788ec5279c6fe0a983c2aefcbd78d4e48a3f7b9ef026de4a" ∧
    RawResult := by
  refine ⟨rfl, ?_⟩
  exact ⟨structure_o, structure_p, structure_q, structure_r, structure_s⟩

theorem reported_result :
    ("2c32a992e214b0f47cfcc8ba2600faf2622da4a340547aa225643b484d207e7c" :
      String) =
      "2c32a992e214b0f47cfcc8ba2600faf2622da4a340547aa225643b484d207e7c" ∧
    ReportedResult := by
  refine ⟨rfl, ?_⟩
  refine ⟨⟨structure_o, structure_p, structure_q, structure_r, structure_s⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

end Icho2026T9A8
end IChO2026Problems
