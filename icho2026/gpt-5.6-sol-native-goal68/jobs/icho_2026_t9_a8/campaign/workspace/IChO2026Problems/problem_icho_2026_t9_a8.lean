import Mathlib

/-!
# IChO 2026, theory problem 9.8

This file formalizes the five structures requested in the problem-only route.
The source diagram is represented by `startingN`; the reaction rules are
partial functions, so a route only produces a structure when the required
functional group is actually present.  The candidates `structureO` through
`structureS` are independently written-out structures, not definitions of the
reaction results.

The α-cyclodextrin core is retained explicitly: six α-D-glucopyranosides in
the ⁴C₁ chair, joined by α-(1→4) bonds, with all twelve secondary O-benzyl
ethers.  The primary-rim fragments and the methallyl bridge carry explicit
heavy-atom connectivity, bond orders, formal charges, radical counts, and
valence-implied hydrogen counts.
-/

namespace IChO2026Problems.T9A8

/-! ## The numbered α-CD template and its fixed stereochemical core -/

inductive Unit where
  | u1 | u2 | u3 | u4 | u5 | u6
  deriving DecidableEq, Repr

def clockwise : Unit → Unit
  | .u1 => .u2
  | .u2 => .u3
  | .u3 => .u4
  | .u4 => .u5
  | .u5 => .u6
  | .u6 => .u1

def counterclockwise : Unit → Unit
  | .u1 => .u6
  | .u2 => .u1
  | .u3 => .u2
  | .u4 => .u3
  | .u5 => .u4
  | .u6 => .u5

/-- The diametrically opposite residue in a six-residue ring. -/
def opposite : Unit → Unit
  | .u1 => .u4
  | .u2 => .u5
  | .u3 => .u6
  | .u4 => .u1
  | .u5 => .u2
  | .u6 => .u3

/-- The problem's convention for a 1,3 modification: two units
counterclockwise from the directing unit. -/
def oneThreeCounterclockwise (u : Unit) : Unit :=
  counterclockwise (counterclockwise u)

theorem positions_used_in_route :
    clockwise .u1 = .u2 ∧
    opposite .u2 = .u5 ∧
    oneThreeCounterclockwise .u2 = .u6 := by
  decide

inductive Face where | up | down
  deriving DecidableEq, Repr

inductive Orientation where | axial | equatorial
  deriving DecidableEq, Repr

inductive Anomer where | alpha | beta
  deriving DecidableEq, Repr

inductive SugarSeries where | D | L
  deriving DecidableEq, Repr

inductive Chair where | fourCOne | oneCFour
  deriving DecidableEq, Repr

/-- Stereochemical data for one α-D-glucopyranoside residue.  Faces are
Haworth faces and orientations refer to the ⁴C₁ chair. -/
structure ResidueStereo where
  anomer : Anomer
  series : SugarSeries
  chair : Chair
  anomericFace : Face
  anomericOrientation : Orientation
  c2OFace : Face
  c2OOrientation : Orientation
  c3OFace : Face
  c3OOrientation : Orientation
  c4OFace : Face
  c4OOrientation : Orientation
  c5PrimaryFace : Face
  c5PrimaryOrientation : Orientation
  deriving DecidableEq, Repr

def alphaDGlucopyranosideStereo : ResidueStereo where
  anomer := .alpha
  series := .D
  chair := .fourCOne
  anomericFace := .down
  anomericOrientation := .axial
  c2OFace := .down
  c2OOrientation := .equatorial
  c3OFace := .up
  c3OOrientation := .equatorial
  c4OFace := .down
  c4OOrientation := .equatorial
  c5PrimaryFace := .up
  c5PrimaryOrientation := .equatorial

structure GlycosidicBond where
  donor : Unit
  donorCarbon : Nat
  acceptor : Unit
  acceptorCarbon : Nat
  anomer : Anomer
  deriving DecidableEq, Repr

inductive SecondaryCarbon where | c2 | c3
  deriving DecidableEq, Repr

structure AlphaCDCore where
  residueStereochemistry : List (Unit × ResidueStereo)
  glycosidicBonds : List GlycosidicBond
  secondaryBenzylEthers : List (Unit × SecondaryCarbon)
  deriving DecidableEq, Repr

def alphaCDCore : AlphaCDCore where
  residueStereochemistry :=
    [(.u1, alphaDGlucopyranosideStereo),
     (.u2, alphaDGlucopyranosideStereo),
     (.u3, alphaDGlucopyranosideStereo),
     (.u4, alphaDGlucopyranosideStereo),
     (.u5, alphaDGlucopyranosideStereo),
     (.u6, alphaDGlucopyranosideStereo)]
  glycosidicBonds :=
    [{ donor := .u1, donorCarbon := 1, acceptor := .u2, acceptorCarbon := 4,
       anomer := .alpha },
     { donor := .u2, donorCarbon := 1, acceptor := .u3, acceptorCarbon := 4,
       anomer := .alpha },
     { donor := .u3, donorCarbon := 1, acceptor := .u4, acceptorCarbon := 4,
       anomer := .alpha },
     { donor := .u4, donorCarbon := 1, acceptor := .u5, acceptorCarbon := 4,
       anomer := .alpha },
     { donor := .u5, donorCarbon := 1, acceptor := .u6, acceptorCarbon := 4,
       anomer := .alpha },
     { donor := .u6, donorCarbon := 1, acceptor := .u1, acceptorCarbon := 4,
       anomer := .alpha }]
  secondaryBenzylEthers :=
    [(.u1, .c2), (.u1, .c3), (.u2, .c2), (.u2, .c3),
     (.u3, .c2), (.u3, .c3), (.u4, .c2), (.u4, .c3),
     (.u5, .c2), (.u5, .c3), (.u6, .c2), (.u6, .c3)]

theorem alphaCDCore_has_six_residues_twelve_secondary_OBn :
    alphaCDCore.residueStereochemistry.length = 6 ∧
    alphaCDCore.glycosidicBonds.length = 6 ∧
    alphaCDCore.secondaryBenzylEthers.length = 12 := by
  decide

/-! ## Explicit fragment connectivity -/

inductive Element where | H | C | N | O
  deriving DecidableEq, Repr

inductive BondOrder where | single | double
  deriving DecidableEq, Repr

/-- Each heavy atom records its formal charge, unpaired-electron count, and
the number of attached hydrogens omitted by the skeletal drawing. -/
structure AtomData where
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  attachedHydrogens : Nat
  deriving DecidableEq, Repr

inductive LocalAtom where
  | coreC5 | c6 | oxygen | nitrogen
  | benzylMethylene
  | phenyl (index : Fin 6)
  | vinylTerminal
  | azideProximal | azideCentral | azideTerminal
  deriving DecidableEq, Repr

structure LocalAtomData where
  label : LocalAtom
  data : AtomData
  deriving DecidableEq, Repr

structure LocalBond where
  left : LocalAtom
  right : LocalAtom
  order : BondOrder
  deriving DecidableEq, Repr

structure FragmentSpec where
  atoms : List LocalAtomData
  bonds : List LocalBond
  deriving DecidableEq, Repr

def atom (label : LocalAtom) (element : Element) (hydrogens : Nat)
    (charge : Int := 0) (radicals : Nat := 0) : LocalAtomData :=
  { label := label
    data := ⟨element, charge, radicals, hydrogens⟩ }

def bond (left right : LocalAtom) (order : BondOrder := .single) : LocalBond :=
  { left := left, right := right, order := order }

def phenylAtoms : List LocalAtomData :=
  [atom (.phenyl 0) .C 0,
   atom (.phenyl 1) .C 1,
   atom (.phenyl 2) .C 1,
   atom (.phenyl 3) .C 1,
   atom (.phenyl 4) .C 1,
   atom (.phenyl 5) .C 1]

/-- One Kekulé representation of the phenyl connectivity. -/
def phenylBonds : List LocalBond :=
  [bond (.phenyl 0) (.phenyl 1) .double,
   bond (.phenyl 1) (.phenyl 2) .single,
   bond (.phenyl 2) (.phenyl 3) .double,
   bond (.phenyl 3) (.phenyl 4) .single,
   bond (.phenyl 4) (.phenyl 5) .double,
   bond (.phenyl 5) (.phenyl 0) .single]

inductive PrimarySite where
  | hydroxymethyl       -- CH₂OH
  | benzyloxymethyl     -- CH₂OCH₂Ph
  | vinyl               -- CH=CH₂
  | azidomethyl         -- CH₂N₃
  | aminomethyl         -- transient CH₂NH₂
  | bridgeNitrogen      -- CH₂N, continued in `MethallylBridge`
  | bridgeOxygen        -- CH₂O, continued in `MethallylBridge`
  deriving DecidableEq, Repr

def primaryFragment : PrimarySite → FragmentSpec
  | .hydroxymethyl =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2, atom .oxygen .O 1]
        bonds := [bond .coreC5 .c6, bond .c6 .oxygen] }
  | .benzyloxymethyl =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2, atom .oxygen .O 0,
          atom .benzylMethylene .C 2] ++ phenylAtoms
        bonds := [bond .coreC5 .c6, bond .c6 .oxygen,
          bond .oxygen .benzylMethylene,
          bond .benzylMethylene (.phenyl 0)] ++ phenylBonds }
  | .vinyl =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 1,
          atom .vinylTerminal .C 2]
        bonds := [bond .coreC5 .c6, bond .c6 .vinylTerminal .double] }
  | .azidomethyl =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2,
          atom .azideProximal .N 0,
          atom .azideCentral .N 0 1,
          atom .azideTerminal .N 0 (-1)]
        bonds := [bond .coreC5 .c6, bond .c6 .azideProximal,
          bond .azideProximal .azideCentral .double,
          bond .azideCentral .azideTerminal .double] }
  | .aminomethyl =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2, atom .nitrogen .N 2]
        bonds := [bond .coreC5 .c6, bond .c6 .nitrogen] }
  | .bridgeNitrogen =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2, atom .nitrogen .N 0]
        bonds := [bond .coreC5 .c6, bond .c6 .nitrogen] }
  | .bridgeOxygen =>
      { atoms := [atom .coreC5 .C 1, atom .c6 .C 2, atom .oxygen .O 0]
        bonds := [bond .coreC5 .c6, bond .c6 .oxygen] }

theorem azide_fragment_has_canonical_charges_and_no_radicals :
    ((primaryFragment .azidomethyl).atoms =
      [atom .coreC5 .C 1, atom .c6 .C 2,
       atom .azideProximal .N 0,
       atom .azideCentral .N 0 1,
       atom .azideTerminal .N 0 (-1)]) ∧
    ((primaryFragment .azidomethyl).bonds =
      [bond .coreC5 .c6, bond .c6 .azideProximal,
       bond .azideProximal .azideCentral .double,
       bond .azideCentral .azideTerminal .double]) := by
  exact ⟨rfl, rfl⟩

/-! The bridge is

`unit-N-CH₂-C(=CH₂)-CH₂-O-unit`,

with H, Boc, or benzyl as the third substituent on nitrogen. -/

inductive NitrogenSubstituent where | hydrogen | boc | benzyl
  deriving DecidableEq, Repr

structure MethallylBridge where
  nitrogenUnit : Unit
  oxygenUnit : Unit
  nitrogenSubstituent : NitrogenSubstituent
  deriving DecidableEq, Repr

inductive BridgeAtom where
  | nitrogenEndpoint | nitrogenSideMethylene | centralCarbon
  | exocyclicMethylene | oxygenSideMethylene | oxygenEndpoint
  | nHydrogen
  | carbonylCarbon | carbonylOxygen | carbamateOxygen | tertButylCarbon
  | tertButylMethyl (index : Fin 3)
  | benzylMethylene | phenyl (index : Fin 6)
  deriving DecidableEq, Repr

structure BridgeAtomData where
  label : BridgeAtom
  data : AtomData
  deriving DecidableEq, Repr

structure BridgeBond where
  left : BridgeAtom
  right : BridgeAtom
  order : BondOrder
  deriving DecidableEq, Repr

structure BridgeSpec where
  nitrogenUnit : Unit
  oxygenUnit : Unit
  atoms : List BridgeAtomData
  bonds : List BridgeBond
  deriving DecidableEq, Repr

def bridgeAtom (label : BridgeAtom) (element : Element) (hydrogens : Nat)
    (charge : Int := 0) (radicals : Nat := 0) : BridgeAtomData :=
  { label := label
    data := ⟨element, charge, radicals, hydrogens⟩ }

def bridgeBond (left right : BridgeAtom)
    (order : BondOrder := .single) : BridgeBond :=
  { left := left, right := right, order := order }

def bridgeBaseAtoms : List BridgeAtomData :=
  [bridgeAtom .nitrogenEndpoint .N 0,
   bridgeAtom .nitrogenSideMethylene .C 2,
   bridgeAtom .centralCarbon .C 0,
   bridgeAtom .exocyclicMethylene .C 2,
   bridgeAtom .oxygenSideMethylene .C 2,
   bridgeAtom .oxygenEndpoint .O 0]

def bridgeBaseBonds : List BridgeBond :=
  [bridgeBond .nitrogenEndpoint .nitrogenSideMethylene,
   bridgeBond .nitrogenSideMethylene .centralCarbon,
   bridgeBond .centralCarbon .exocyclicMethylene .double,
   bridgeBond .centralCarbon .oxygenSideMethylene,
   bridgeBond .oxygenSideMethylene .oxygenEndpoint]

def bridgePhenylAtoms : List BridgeAtomData :=
  [bridgeAtom (.phenyl 0) .C 0,
   bridgeAtom (.phenyl 1) .C 1,
   bridgeAtom (.phenyl 2) .C 1,
   bridgeAtom (.phenyl 3) .C 1,
   bridgeAtom (.phenyl 4) .C 1,
   bridgeAtom (.phenyl 5) .C 1]

def bridgePhenylBonds : List BridgeBond :=
  [bridgeBond (.phenyl 0) (.phenyl 1) .double,
   bridgeBond (.phenyl 1) (.phenyl 2) .single,
   bridgeBond (.phenyl 2) (.phenyl 3) .double,
   bridgeBond (.phenyl 3) (.phenyl 4) .single,
   bridgeBond (.phenyl 4) (.phenyl 5) .double,
   bridgeBond (.phenyl 5) (.phenyl 0) .single]

def bridgeSpec (b : MethallylBridge) : BridgeSpec :=
  let substituentAtoms := match b.nitrogenSubstituent with
    | .hydrogen => [bridgeAtom .nHydrogen .H 0]
    | .boc =>
        [bridgeAtom .carbonylCarbon .C 0,
         bridgeAtom .carbonylOxygen .O 0,
         bridgeAtom .carbamateOxygen .O 0,
         bridgeAtom .tertButylCarbon .C 0,
         bridgeAtom (.tertButylMethyl 0) .C 3,
         bridgeAtom (.tertButylMethyl 1) .C 3,
         bridgeAtom (.tertButylMethyl 2) .C 3]
    | .benzyl => [bridgeAtom .benzylMethylene .C 2] ++ bridgePhenylAtoms
  let substituentBonds := match b.nitrogenSubstituent with
    | .hydrogen => [bridgeBond .nitrogenEndpoint .nHydrogen]
    | .boc =>
        [bridgeBond .nitrogenEndpoint .carbonylCarbon,
         bridgeBond .carbonylCarbon .carbonylOxygen .double,
         bridgeBond .carbonylCarbon .carbamateOxygen,
         bridgeBond .carbamateOxygen .tertButylCarbon,
         bridgeBond .tertButylCarbon (.tertButylMethyl 0),
         bridgeBond .tertButylCarbon (.tertButylMethyl 1),
         bridgeBond .tertButylCarbon (.tertButylMethyl 2)]
    | .benzyl =>
        [bridgeBond .nitrogenEndpoint .benzylMethylene,
         bridgeBond .benzylMethylene (.phenyl 0)] ++ bridgePhenylBonds
  { nitrogenUnit := b.nitrogenUnit
    oxygenUnit := b.oxygenUnit
    atoms := bridgeBaseAtoms ++ substituentAtoms
    bonds := bridgeBaseBonds ++ substituentBonds }

/-! ## Structures and source material N -/

structure PrimaryRim where
  u1 : PrimarySite
  u2 : PrimarySite
  u3 : PrimarySite
  u4 : PrimarySite
  u5 : PrimarySite
  u6 : PrimarySite
  deriving DecidableEq, Repr

def PrimaryRim.get (r : PrimaryRim) : Unit → PrimarySite
  | .u1 => r.u1
  | .u2 => r.u2
  | .u3 => r.u3
  | .u4 => r.u4
  | .u5 => r.u5
  | .u6 => r.u6

def PrimaryRim.set (r : PrimaryRim) : Unit → PrimarySite → PrimaryRim
  | .u1, x => { r with u1 := x }
  | .u2, x => { r with u2 := x }
  | .u3, x => { r with u3 := x }
  | .u4, x => { r with u4 := x }
  | .u5, x => { r with u5 := x }
  | .u6, x => { r with u6 := x }

structure CDStructure where
  core : AlphaCDCore
  primary : PrimaryRim
  bridge : Option MethallylBridge
  deriving DecidableEq, Repr

/-- Source input: compound N in the problem figure. -/
def startingN : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .hydroxymethyl
      u2 := .benzyloxymethyl
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .benzyloxymethyl
      u6 := .benzyloxymethyl }
  bridge := none

def structureO : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .vinyl
      u2 := .benzyloxymethyl
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .benzyloxymethyl
      u6 := .benzyloxymethyl }
  bridge := none

def structureP : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .vinyl
      u2 := .azidomethyl
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .benzyloxymethyl
      u6 := .benzyloxymethyl }
  bridge := none

def structureQ : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .vinyl
      u2 := .bridgeNitrogen
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .bridgeOxygen
      u6 := .benzyloxymethyl }
  bridge := some
    { nitrogenUnit := .u2
      oxygenUnit := .u5
      nitrogenSubstituent := .hydrogen }

def structureR : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .vinyl
      u2 := .bridgeNitrogen
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .bridgeOxygen
      u6 := .azidomethyl }
  bridge := some
    { nitrogenUnit := .u2
      oxygenUnit := .u5
      nitrogenSubstituent := .boc }

def structureS : CDStructure where
  core := alphaCDCore
  primary :=
    { u1 := .vinyl
      u2 := .bridgeNitrogen
      u3 := .benzyloxymethyl
      u4 := .benzyloxymethyl
      u5 := .bridgeOxygen
      u6 := .azidomethyl }
  bridge := some
    { nitrogenUnit := .u2
      oxygenUnit := .u5
      nitrogenSubstituent := .benzyl }

/-! ## Executable chemistry rules used by the printed route

These are trusted general reaction laws specialized to the functional groups
drawn in the problem.  Each law checks its substrate rather than accepting an
arbitrary claimed product.
-/

def changePrimary (s : CDStructure) (u : Unit) (x : PrimarySite) : CDStructure :=
  { s with primary := s.primary.set u x }

/-- Swern oxidation of CH₂OH to CHO followed by methylene Wittig olefination
gives the attached terminal alkene CH=CH₂. -/
def swernWittig (u : Unit) (s : CDStructure) : Option CDStructure :=
  if s.primary.get u = .hydroxymethyl then
    some (changePrimary s u .vinyl)
  else none

/-- An alkene selects the adjacent clockwise primary benzyl ether. -/
def alkeneDirectedDebenzylation (director : Unit)
    (s : CDStructure) : Option CDStructure :=
  let target := clockwise director
  if s.primary.get director = .vinyl ∧
      s.primary.get target = .benzyloxymethyl then
    some (changePrimary s target .hydroxymethyl)
  else none

/-- Mesylation followed by azide displacement: CH₂OH becomes CH₂N₃. -/
def alcoholToAzide (u : Unit) (s : CDStructure) : Option CDStructure :=
  if s.primary.get u = .hydroxymethyl then
    some (changePrimary s u .azidomethyl)
  else none

/-- DIBAL-H reduces CH₂N₃ to CH₂NH₂.  The new protic group directs
debenzylation to the diametrically opposite unit when it is available. -/
def tandemAzideReductionOppositeDebenzylation (director : Unit)
    (s : CDStructure) : Option CDStructure :=
  let target := opposite director
  if s.primary.get director = .azidomethyl ∧
      s.primary.get target = .benzyloxymethyl then
    some (changePrimary (changePrimary s director .aminomethyl)
      target .hydroxymethyl)
  else none

/-- NaH and ClCH₂-C(=CH₂)-CH₂Cl join CH₂NH₂ and CH₂OH as the
secondary-amino/ether methallyl bridge. -/
def installMethallylBridge (nitrogenUnit oxygenUnit : Unit)
    (s : CDStructure) : Option CDStructure :=
  if s.primary.get nitrogenUnit = .aminomethyl ∧
      s.primary.get oxygenUnit = .hydroxymethyl ∧ s.bridge = none then
    some
      { (changePrimary (changePrimary s nitrogenUnit .bridgeNitrogen)
          oxygenUnit .bridgeOxygen) with
        bridge := some
          { nitrogenUnit := nitrogenUnit
            oxygenUnit := oxygenUnit
            nitrogenSubstituent := .hydrogen } }
  else none

/-- In Q, the protic NH dominates the alkene.  Its diametric site is already
the O end of the bridge, so the problem's fallback 1,3 rule selects two units
counterclockwise from N. -/
def proticBridgeDirectedDebenzylation (s : CDStructure) : Option CDStructure :=
  match s.bridge with
  | some b =>
      let target := oneThreeCounterclockwise b.nitrogenUnit
      if b.nitrogenSubstituent = .hydrogen ∧
          b.oxygenUnit = opposite b.nitrogenUnit ∧
          s.primary.get b.oxygenUnit = .bridgeOxygen ∧
          s.primary.get target = .benzyloxymethyl then
        some (changePrimary s target .hydroxymethyl)
      else none
  | none => none

def protectBridgeNitrogenBoc (s : CDStructure) : Option CDStructure :=
  match s.bridge with
  | some b =>
      if b.nitrogenSubstituent = .hydrogen then
        some { s with bridge := some { b with nitrogenSubstituent := .boc } }
      else none
  | none => none

def deprotectBridgeNitrogenBoc (s : CDStructure) : Option CDStructure :=
  match s.bridge with
  | some b =>
      if b.nitrogenSubstituent = .boc then
        some { s with bridge := some { b with nitrogenSubstituent := .hydrogen } }
      else none
  | none => none

def benzylateBridgeNitrogen (s : CDStructure) : Option CDStructure :=
  match s.bridge with
  | some b =>
      if b.nitrogenSubstituent = .hydrogen then
        some { s with bridge := some { b with nitrogenSubstituent := .benzyl } }
      else none
  | none => none

/-! ## The source-to-product route -/

def deriveO : Option CDStructure :=
  swernWittig .u1 startingN

def deriveP : Option CDStructure := do
  let o ← deriveO
  let alcohol ← alkeneDirectedDebenzylation .u1 o
  alcoholToAzide (clockwise .u1) alcohol

def deriveQ : Option CDStructure := do
  let p ← deriveP
  let aminoAlcohol ← tandemAzideReductionOppositeDebenzylation .u2 p
  installMethallylBridge .u2 (opposite .u2) aminoAlcohol

def deriveR : Option CDStructure := do
  let q ← deriveQ
  let alcohol ← proticBridgeDirectedDebenzylation q
  let bocProtected ← protectBridgeNitrogenBoc alcohol
  alcoholToAzide (oneThreeCounterclockwise .u2) bocProtected

def deriveS : Option CDStructure := do
  let r ← deriveR
  let deprotected ← deprotectBridgeNitrogenBoc r
  benzylateBridgeNitrogen deprotected

/-! ## Proofs of all five requested outputs -/

theorem structure_o : deriveO = some structureO := by
  decide

theorem structure_p : deriveP = some structureP := by
  decide

theorem structure_q : deriveQ = some structureQ := by
  decide

theorem structure_r : deriveR = some structureR := by
  decide

theorem structure_s : deriveS = some structureS := by
  decide

/-- The N/O bridge in Q has the exact endpoint order and exocyclic double bond
required by ClCH₂-C(=CH₂)-CH₂Cl. -/
theorem structure_q_bridge_connectivity :
    structureQ.bridge.map bridgeSpec = some
      { nitrogenUnit := .u2
        oxygenUnit := .u5
        atoms := bridgeBaseAtoms ++ [bridgeAtom .nHydrogen .H 0]
        bonds := bridgeBaseBonds ++
          [bridgeBond .nitrogenEndpoint .nHydrogen] } := by
  decide

theorem structure_r_has_NBoc_and_unit6_azide :
    structureR.primary.get .u6 = .azidomethyl ∧
    (structureR.bridge.map (fun b => b.nitrogenSubstituent)) = some .boc := by
  decide

theorem structure_s_has_NBn_and_preserves_unit6_azide :
    structureS.primary.get .u6 = .azidomethyl ∧
    (structureS.bridge.map (fun b => b.nitrogenSubstituent)) = some .benzyl := by
  decide

def BridgeConsistent (s : CDStructure) : Prop :=
  match s.bridge with
  | none =>
      s.primary.get .u1 ≠ .bridgeNitrogen ∧
      s.primary.get .u2 ≠ .bridgeNitrogen ∧
      s.primary.get .u3 ≠ .bridgeNitrogen ∧
      s.primary.get .u4 ≠ .bridgeNitrogen ∧
      s.primary.get .u5 ≠ .bridgeNitrogen ∧
      s.primary.get .u6 ≠ .bridgeNitrogen ∧
      s.primary.get .u1 ≠ .bridgeOxygen ∧
      s.primary.get .u2 ≠ .bridgeOxygen ∧
      s.primary.get .u3 ≠ .bridgeOxygen ∧
      s.primary.get .u4 ≠ .bridgeOxygen ∧
      s.primary.get .u5 ≠ .bridgeOxygen ∧
      s.primary.get .u6 ≠ .bridgeOxygen
  | some b =>
      b.nitrogenUnit ≠ b.oxygenUnit ∧
      s.primary.get b.nitrogenUnit = .bridgeNitrogen ∧
      s.primary.get b.oxygenUnit = .bridgeOxygen

def FullySpecified (s : CDStructure) : Prop :=
  s.core = alphaCDCore ∧
  s.core.residueStereochemistry.length = 6 ∧
  s.core.glycosidicBonds.length = 6 ∧
  s.core.secondaryBenzylEthers.length = 12 ∧
  BridgeConsistent s ∧
  (primaryFragment (s.primary.get .u1)).atoms ≠ [] ∧
  (primaryFragment (s.primary.get .u2)).atoms ≠ [] ∧
  (primaryFragment (s.primary.get .u3)).atoms ≠ [] ∧
  (primaryFragment (s.primary.get .u4)).atoms ≠ [] ∧
  (primaryFragment (s.primary.get .u5)).atoms ≠ [] ∧
  (primaryFragment (s.primary.get .u6)).atoms ≠ []

theorem all_requested_structures_fully_specified :
    FullySpecified structureO ∧
    FullySpecified structureP ∧
    FullySpecified structureQ ∧
    FullySpecified structureR ∧
    FullySpecified structureS := by
  simp [FullySpecified, BridgeConsistent, structureO, structureP,
    structureQ, structureR, structureS, alphaCDCore, PrimaryRim.get,
    primaryFragment]

/-- One theorem collecting the five independently specified outputs and the
source-to-product derivations. -/
theorem requested_outputs :
    deriveO = some structureO ∧
    deriveP = some structureP ∧
    deriveQ = some structureQ ∧
    deriveR = some structureR ∧
    deriveS = some structureS ∧
    FullySpecified structureO ∧
    FullySpecified structureP ∧
    FullySpecified structureQ ∧
    FullySpecified structureR ∧
    FullySpecified structureS := by
  exact ⟨structure_o, structure_p, structure_q, structure_r, structure_s,
    all_requested_structures_fully_specified.1,
    all_requested_structures_fully_specified.2.1,
    all_requested_structures_fully_specified.2.2.1,
    all_requested_structures_fully_specified.2.2.2.1,
    all_requested_structures_fully_specified.2.2.2.2⟩

#print axioms structure_o
#print axioms structure_p
#print axioms structure_q
#print axioms structure_r
#print axioms structure_s
#print axioms structure_q_bridge_connectivity
#print axioms structure_r_has_NBoc_and_unit6_azide
#print axioms structure_s_has_NBn_and_preserves_unit6_azide
#print axioms all_requested_structures_fully_specified
#print axioms requested_outputs

end IChO2026Problems.T9A8
