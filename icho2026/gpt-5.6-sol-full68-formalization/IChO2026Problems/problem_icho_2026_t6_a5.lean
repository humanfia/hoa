import IChO2026Chem

/-!
# IChO 2026, theory problem 6, part 5

The source asks for the structures of intermediates `F`--`L` in the depicted
synthesis of `[5]`cycloparaphenylene.  This file uses a target-local molecular
graph model because the configured libraries do not provide a chemical graph
whose edges carry bond order and whose vertices carry element, charge, radical,
hydrogen, and stereochemical data.

Hydrogens are materialized as vertices by `MolecularDescriptor.expand`; they
are not hidden in a molecular-formula string.  The seven candidates are given
independently of the generic graph rewrites used to specify the reaction arrows.
Thus the result propositions check the candidates against the source-directed
transformations rather than assuming their identities.
-/

namespace IChO2026Problems.Icho2026T6A5

/-! ## Atom- and bond-level molecular graphs -/

inductive Element
  | hydrogen
  | carbon
  | oxygen
  | silicon
  | bromine
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  deriving DecidableEq, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2

/-- The figures do not mark any wedge, dash, `R`/`S`, or alkene geometry.
Potential tetrahedral stereocentres in the masked rings are consequently kept
explicitly source-unspecified rather than silently assigned. -/
inductive LocalStereo
  | notStereogenic
  | sourceUnspecified
  deriving DecidableEq, Repr

structure HeavyAtom where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  stereochemistry : LocalStereo
  deriving DecidableEq, Repr

structure Atom where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereochemistry : LocalStereo
  deriving DecidableEq, Repr

inductive HeavyAtomId
  | ringCarbon (ring position : ℕ)
  | oxygen (slot : ℕ)
  | silicon (slot : ℕ)
  | silylCarbon (slot position : ℕ)
  | bromine (slot : ℕ)
  deriving DecidableEq, Repr

inductive AtomId
  | heavy (id : HeavyAtomId)
  | hydrogen (parent : HeavyAtomId) (position : ℕ)
  deriving DecidableEq, Repr

structure HeavyBond where
  left : HeavyAtomId
  right : HeavyAtomId
  order : BondOrder
  deriving DecidableEq, Repr

structure Bond where
  left : AtomId
  right : AtomId
  order : BondOrder
  deriving DecidableEq, Repr

structure MolecularStructure where
  atoms : List (AtomId × Atom)
  bonds : List Bond
  deriving DecidableEq, Repr

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  silicon : ℕ
  bromine : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.zero : MolecularFormula :=
  { carbon := 0, hydrogen := 0, oxygen := 0, silicon := 0, bromine := 0 }

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    oxygen := a.oxygen + b.oxygen
    silicon := a.silicon + b.silicon
    bromine := a.bromine + b.bromine }

def Atom.formulaContribution (a : Atom) : MolecularFormula :=
  match a.element with
  | .hydrogen => { MolecularFormula.zero with hydrogen := 1 }
  | .carbon => { MolecularFormula.zero with carbon := 1 }
  | .oxygen => { MolecularFormula.zero with oxygen := 1 }
  | .silicon => { MolecularFormula.zero with silicon := 1 }
  | .bromine => { MolecularFormula.zero with bromine := 1 }

def MolecularStructure.formula (s : MolecularStructure) : MolecularFormula :=
  s.atoms.foldl
    (fun total entry => MolecularFormula.add total entry.2.formulaContribution)
    MolecularFormula.zero

def MolecularStructure.atomIds (s : MolecularStructure) : List AtomId :=
  s.atoms.map Prod.fst

def MolecularStructure.totalFormalCharge (s : MolecularStructure) : ℤ :=
  (s.atoms.map (fun entry => entry.2.formalCharge)).sum

def MolecularStructure.totalRadicalElectrons (s : MolecularStructure) : ℕ :=
  (s.atoms.map (fun entry => entry.2.radicalElectrons)).sum

def MolecularStructure.incidentValence (s : MolecularStructure) (id : AtomId) : ℕ :=
  (s.bonds.map fun bond =>
    if bond.left = id then bond.order.valence
    else if bond.right = id then bond.order.valence
    else 0).sum

def MolecularStructure.HasIncidentBondOrder
    (s : MolecularStructure) (id : AtomId) (order : BondOrder) : Prop :=
  ∃ bond ∈ s.bonds,
    (bond.left = id ∨ bond.right = id) ∧ bond.order = order

def MolecularStructure.AtomStereoIs
    (s : MolecularStructure) (id : AtomId)
    (element : Element) (stereo : LocalStereo) : Prop :=
  ∃ atom, (id, atom) ∈ s.atoms ∧
    atom.element = element ∧ atom.stereochemistry = stereo

def Element.expectedValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2
  | .silicon => 4
  | .bromine => 1

def MolecularStructure.BondEndpointsPresent (s : MolecularStructure) : Prop :=
  ∀ bond ∈ s.bonds, bond.left ∈ s.atomIds ∧ bond.right ∈ s.atomIds

def MolecularStructure.NoSelfBonds (s : MolecularStructure) : Prop :=
  ∀ bond ∈ s.bonds, bond.left ≠ bond.right

def MolecularStructure.ValenceCorrect (s : MolecularStructure) : Prop :=
  ∀ id atom, (id, atom) ∈ s.atoms →
    s.incidentValence id = atom.element.expectedValence

/-- `LocalStereo` records atom-centred tetrahedral stereochemistry only.
Consequently every atom incident to a double bond is non-stereogenic in this
carrier, while a source-unspecified atom must be carbon with no incident
double bond. -/
def MolecularStructure.StereoBondOrderCompatible
    (s : MolecularStructure) : Prop :=
  ∀ id atom, (id, atom) ∈ s.atoms →
    (s.HasIncidentBondOrder id .double →
      atom.stereochemistry = .notStereogenic) ∧
    (atom.stereochemistry = .sourceUnspecified →
      atom.element = .carbon ∧ ¬ s.HasIncidentBondOrder id .double)

def MolecularStructure.Adjacent (s : MolecularStructure) (a b : AtomId) : Prop :=
  ∃ bond ∈ s.bonds,
    (bond.left = a ∧ bond.right = b) ∨ (bond.left = b ∧ bond.right = a)

def MolecularStructure.Connected (s : MolecularStructure) : Prop :=
  ∀ a ∈ s.atomIds, ∀ b ∈ s.atomIds,
    Relation.ReflTransGen s.Adjacent a b

def MolecularStructure.FullySpecifiedNeutralClosedShell
    (s : MolecularStructure) : Prop :=
  s.atomIds.Nodup ∧
  s.BondEndpointsPresent ∧
  s.NoSelfBonds ∧
  s.ValenceCorrect ∧
  s.StereoBondOrderCompatible ∧
  s.Connected ∧
  s.totalFormalCharge = 0 ∧
  s.totalRadicalElectrons = 0

/-! ## A compositional descriptor for the structures in the scheme -/

inductive RingKind
  | benzene
  | cyclohexa25Diene
  deriving DecidableEq, Repr

inductive SilylGroup
  | tertButyldimethyl
  | triethyl
  deriving DecidableEq, Repr

inductive OxygenKind
  | hydroxyl
  | carbonyl
  | silylEther (group : SilylGroup)
  deriving DecidableEq, Repr

structure OxygenSite where
  slot : ℕ
  ring : ℕ
  position : ℕ
  kind : OxygenKind
  deriving DecidableEq, Repr

structure BromineSite where
  slot : ℕ
  ring : ℕ
  position : ℕ
  deriving DecidableEq, Repr

/-- Rings are ordered along the para-linked chain.  Consecutive rings are
joined from position 3 of the earlier ring to position 0 of the next one.
When `closed = true`, the final position 3 is additionally joined to position
0 of the first ring. -/
structure MolecularDescriptor where
  rings : List RingKind
  closed : Bool
  bromines : List BromineSite
  oxygens : List OxygenSite
  deriving DecidableEq, Repr

def neutralHeavyAtom (element : Element) (hydrogens : ℕ)
    (stereo : LocalStereo := .notStereogenic) : HeavyAtom :=
  { element := element
    formalCharge := 0
    radicalElectrons := 0
    attachedHydrogens := hydrogens
    stereochemistry := stereo }

def ringCarbonHydrogens (position : ℕ) : ℕ :=
  if position = 0 ∨ position = 3 then 0 else 1

/-- Whether the descriptor gives this ring carbon an explicit C=O bond. -/
def carbonylAt (sites : List OxygenSite) (ring position : ℕ) : Bool :=
  sites.any fun site =>
    decide
      (site.ring = ring ∧ site.position = position ∧ site.kind = .carbonyl)

/-- Potential tetrahedral centres at positions 0 and 3 of a masked ring are
left source-unspecified, except that an explicit carbonyl site is necessarily
trigonal and therefore non-stereogenic. -/
def ringCarbonStereo (sites : List OxygenSite) (ring : ℕ)
    (kind : RingKind) (position : ℕ) : LocalStereo :=
  if kind = .cyclohexa25Diene ∧ (position = 0 ∨ position = 3) ∧
      carbonylAt sites ring position = false then
    .sourceUnspecified
  else
    .notStereogenic

def ringHeavyAtomsAt (sites : List OxygenSite) (ring : ℕ) (kind : RingKind) :
    List (HeavyAtomId × HeavyAtom) :=
  (List.range 6).map fun position =>
    (HeavyAtomId.ringCarbon ring position,
      neutralHeavyAtom .carbon (ringCarbonHydrogens position)
        (ringCarbonStereo sites ring kind position))

def ringHeavyAtomsAux (sites : List OxygenSite) :
    ℕ → List RingKind → List (HeavyAtomId × HeavyAtom)
  | _, [] => []
  | ring, kind :: rest =>
      ringHeavyAtomsAt sites ring kind ++ ringHeavyAtomsAux sites (ring + 1) rest

def oxygenHeavyAtom (site : OxygenSite) : HeavyAtom :=
  neutralHeavyAtom .oxygen (if site.kind = .hydroxyl then 1 else 0)

def silylCarbonHydrogens (group : SilylGroup) (position : ℕ) : ℕ :=
  match group with
  | .triethyl => if position % 2 = 0 then 2 else 3
  | .tertButyldimethyl => if position = 0 then 0 else 3

def silylHeavyAtoms (site : OxygenSite) : List (HeavyAtomId × HeavyAtom) :=
  match site.kind with
  | .silylEther group =>
      (HeavyAtomId.silicon site.slot, neutralHeavyAtom .silicon 0) ::
        (List.range 6).map fun position =>
          (HeavyAtomId.silylCarbon site.slot position,
            neutralHeavyAtom .carbon (silylCarbonHydrogens group position))
  | _ => []

def bromineHeavyAtom (site : BromineSite) : HeavyAtomId × HeavyAtom :=
  (HeavyAtomId.bromine site.slot, neutralHeavyAtom .bromine 0)

def MolecularDescriptor.heavyAtoms (d : MolecularDescriptor) :
    List (HeavyAtomId × HeavyAtom) :=
  ringHeavyAtomsAux d.oxygens 0 d.rings ++
    d.oxygens.map (fun site => (HeavyAtomId.oxygen site.slot, oxygenHeavyAtom site)) ++
    d.oxygens.flatMap silylHeavyAtoms ++
    d.bromines.map bromineHeavyAtom

def heavyBond (left right : HeavyAtomId) (order : BondOrder := .single) : HeavyBond :=
  { left := left, right := right, order := order }

def ringHeavyBondsAt (ring : ℕ) : RingKind → List HeavyBond
  | .benzene =>
      [ heavyBond (.ringCarbon ring 0) (.ringCarbon ring 1) .double
      , heavyBond (.ringCarbon ring 1) (.ringCarbon ring 2)
      , heavyBond (.ringCarbon ring 2) (.ringCarbon ring 3) .double
      , heavyBond (.ringCarbon ring 3) (.ringCarbon ring 4)
      , heavyBond (.ringCarbon ring 4) (.ringCarbon ring 5) .double
      , heavyBond (.ringCarbon ring 5) (.ringCarbon ring 0) ]
  | .cyclohexa25Diene =>
      [ heavyBond (.ringCarbon ring 0) (.ringCarbon ring 1)
      , heavyBond (.ringCarbon ring 1) (.ringCarbon ring 2) .double
      , heavyBond (.ringCarbon ring 2) (.ringCarbon ring 3)
      , heavyBond (.ringCarbon ring 3) (.ringCarbon ring 4)
      , heavyBond (.ringCarbon ring 4) (.ringCarbon ring 5) .double
      , heavyBond (.ringCarbon ring 5) (.ringCarbon ring 0) ]

def ringHeavyBondsAux : ℕ → List RingKind → List HeavyBond
  | _, [] => []
  | ring, kind :: rest =>
      ringHeavyBondsAt ring kind ++ ringHeavyBondsAux (ring + 1) rest

def chainHeavyBonds (rings : List RingKind) : List HeavyBond :=
  (List.range (rings.length - 1)).map fun ring =>
    heavyBond (.ringCarbon ring 3) (.ringCarbon (ring + 1) 0)

def closureHeavyBonds (d : MolecularDescriptor) : List HeavyBond :=
  match d.closed, d.rings with
  | true, _ :: _ =>
      [heavyBond (.ringCarbon (d.rings.length - 1) 3) (.ringCarbon 0 0)]
  | _, _ => []

def bromineHeavyBonds (sites : List BromineSite) : List HeavyBond :=
  sites.map fun site =>
    heavyBond (.ringCarbon site.ring site.position) (.bromine site.slot)

def oxygenHeavyBonds (site : OxygenSite) : List HeavyBond :=
  let carbonOxygen :=
    heavyBond (.ringCarbon site.ring site.position) (.oxygen site.slot)
      (if site.kind = .carbonyl then .double else .single)
  match site.kind with
  | .hydroxyl | .carbonyl => [carbonOxygen]
  | .silylEther group =>
      let oxygenSilicon := heavyBond (.oxygen site.slot) (.silicon site.slot)
      let groupBonds :=
        match group with
        | .triethyl =>
            [ heavyBond (.silicon site.slot) (.silylCarbon site.slot 0)
            , heavyBond (.silylCarbon site.slot 0) (.silylCarbon site.slot 1)
            , heavyBond (.silicon site.slot) (.silylCarbon site.slot 2)
            , heavyBond (.silylCarbon site.slot 2) (.silylCarbon site.slot 3)
            , heavyBond (.silicon site.slot) (.silylCarbon site.slot 4)
            , heavyBond (.silylCarbon site.slot 4) (.silylCarbon site.slot 5) ]
        | .tertButyldimethyl =>
            [ heavyBond (.silicon site.slot) (.silylCarbon site.slot 0)
            , heavyBond (.silicon site.slot) (.silylCarbon site.slot 4)
            , heavyBond (.silicon site.slot) (.silylCarbon site.slot 5)
            , heavyBond (.silylCarbon site.slot 0) (.silylCarbon site.slot 1)
            , heavyBond (.silylCarbon site.slot 0) (.silylCarbon site.slot 2)
            , heavyBond (.silylCarbon site.slot 0) (.silylCarbon site.slot 3) ]
      carbonOxygen :: oxygenSilicon :: groupBonds

def MolecularDescriptor.heavyBonds (d : MolecularDescriptor) : List HeavyBond :=
  ringHeavyBondsAux 0 d.rings ++
    chainHeavyBonds d.rings ++
    closureHeavyBonds d ++
    bromineHeavyBonds d.bromines ++
    d.oxygens.flatMap oxygenHeavyBonds

def HeavyAtom.toAtom (a : HeavyAtom) : Atom :=
  { element := a.element
    formalCharge := a.formalCharge
    radicalElectrons := a.radicalElectrons
    stereochemistry := a.stereochemistry }

def hydrogenAtom : Atom :=
  { element := .hydrogen
    formalCharge := 0
    radicalElectrons := 0
    stereochemistry := .notStereogenic }

def materializedAtomsFor (entry : HeavyAtomId × HeavyAtom) : List (AtomId × Atom) :=
  (AtomId.heavy entry.1, entry.2.toAtom) ::
    (List.range entry.2.attachedHydrogens).map fun position =>
      (AtomId.hydrogen entry.1 position, hydrogenAtom)

def materializedHeavyBond (bond : HeavyBond) : Bond :=
  { left := .heavy bond.left, right := .heavy bond.right, order := bond.order }

def materializedHydrogenBondsFor (entry : HeavyAtomId × HeavyAtom) : List Bond :=
  (List.range entry.2.attachedHydrogens).map fun position =>
    { left := .heavy entry.1
      right := .hydrogen entry.1 position
      order := .single }

def MolecularDescriptor.expand (d : MolecularDescriptor) : MolecularStructure :=
  { atoms := d.heavyAtoms.flatMap materializedAtomsFor
    bonds := d.heavyBonds.map materializedHeavyBond ++
      d.heavyAtoms.flatMap materializedHydrogenBondsFor }

def CandidateChecks (descriptor : MolecularDescriptor)
    (formula : MolecularFormula) : Prop :=
  descriptor.expand.formula = formula ∧
    descriptor.expand.FullySpecifiedNeutralClosedShell

/-! ## Source species, arrows, and qualitative reaction semantics -/

inductive StageLabel
  | startingMaterial
  | f | g | h | i | j | k | l
  | fiveCPP
  deriving DecidableEq, Repr

inductive Reagent
  | sodiumHydride
  | biphenylOTBSOrganolithium
  | triethylsilylChloride
  | imidazole
  | lithiumHydroxide
  | phenyliodineDiacetate
  | water
  | paraBromophenylLithium
  | nickelBisCOD
  | bipyridine
  | tetraNButylammoniumFluoride
  | tinIIChloride
  deriving DecidableEq, Repr

structure ReagentUse where
  reagent : Reagent
  equivalents : Option ℕ
  excess : Bool
  electronsAccepted : ℕ
  deriving DecidableEq, Repr

inductive TransformationUse
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

inductive SourceLocator
  | page3SynthesisScheme
  | page3Legend
  deriving DecidableEq, Repr

structure SourceArrow where
  input : StageLabel
  output : StageLabel
  reagents : List ReagentUse
  transformationUse : TransformationUse
  locator : SourceLocator
  deriving DecidableEq, Repr

def reagentUse (reagent : Reagent) (equivalents : Option ℕ := none)
    (excess : Bool := false) (electronsAccepted : ℕ := 0) : ReagentUse :=
  { reagent := reagent
    equivalents := equivalents
    excess := excess
    electronsAccepted := electronsAccepted }

/-- Exact transcription of the directed arrows and printed equivalents on
`T6_page-3.png`.  The final arrow is included because the depicted `[5]CPP`
fixes the intended connectivity of the ring-closed intermediate `L`. -/
def sourceArrows : List SourceArrow :=
  [ { input := .startingMaterial
      output := .f
      reagents :=
        [reagentUse .sodiumHydride, reagentUse .biphenylOTBSOrganolithium]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .f
      output := .g
      reagents :=
        [reagentUse .triethylsilylChloride (some 2), reagentUse .imidazole]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .g
      output := .h
      reagents := [reagentUse .lithiumHydroxide]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .h
      output := .i
      reagents :=
        [reagentUse .phenyliodineDiacetate none false 2, reagentUse .water]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .i
      output := .j
      reagents :=
        [reagentUse .sodiumHydride, reagentUse .paraBromophenylLithium]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .j
      output := .k
      reagents :=
        [reagentUse .triethylsilylChloride (some 2), reagentUse .imidazole]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .k
      output := .l
      reagents :=
        [reagentUse .nickelBisCOD (some 2), reagentUse .bipyridine (some 2)]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme }
  , { input := .l
      output := .fiveCPP
      reagents :=
        [ reagentUse .tetraNButylammoniumFluoride (some 4)
        , reagentUse .tinIIChloride none true ]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page3SynthesisScheme } ]

def oxygenSite (slot ring position : ℕ) (kind : OxygenKind) : OxygenSite :=
  { slot := slot, ring := ring, position := position, kind := kind }

def bromineSite (slot ring position : ℕ) : BromineSite :=
  { slot := slot, ring := ring, position := position }

/-- Starting 4-(4-bromophenyl)-4-hydroxycyclohexa-2,5-dien-1-one,
read from the left side of the source scheme. -/
def startingMaterial : MolecularDescriptor :=
  { rings := [.benzene, .cyclohexa25Diene]
    closed := false
    bromines := [bromineSite 0 0 0]
    oxygens :=
      [ oxygenSite 0 1 0 .hydroxyl
      , oxygenSite 1 1 3 .carbonyl ] }

/-- The transferred 4'-OTBS-biphenyl fragment.  Position 0 of its first ring
is the carbon bearing lithium in the reagent figure and is the attachment site. -/
def biphenylOTBSFragment : MolecularDescriptor :=
  { rings := [.benzene, .benzene]
    closed := false
    bromines := []
    oxygens :=
      [oxygenSite 0 1 3 (.silylEther .tertButyldimethyl)] }

/-- The transferred para-bromophenyl fragment; position 0 is the carbon bearing
lithium and position 3 retains bromine. -/
def paraBromophenylFragment : MolecularDescriptor :=
  { rings := [.benzene]
    closed := false
    bromines := [bromineSite 0 0 3]
    oxygens := [] }

def shiftOxygenSite (ringOffset slotOffset : ℕ) (site : OxygenSite) : OxygenSite :=
  { site with ring := site.ring + ringOffset, slot := site.slot + slotOffset }

def shiftBromineSite (ringOffset slotOffset : ℕ) (site : BromineSite) : BromineSite :=
  { site with ring := site.ring + ringOffset, slot := site.slot + slotOffset }

/-- Generic addition of an aryl-transfer fragment to the terminal carbonyl.
It changes that C=O into C-OH and connects the transferred aryl carbon at the
same ring position. -/
def terminalCarbonylAddition
    (substrate fragment : MolecularDescriptor) : MolecularDescriptor :=
  let terminalRing := substrate.rings.length - 1
  let changedOxygens := substrate.oxygens.map fun site =>
    if site.ring = terminalRing ∧ site.position = 3 ∧ site.kind = .carbonyl then
      { site with kind := .hydroxyl }
    else
      site
  { rings := substrate.rings ++ fragment.rings
    closed := false
    bromines := substrate.bromines ++
      fragment.bromines.map
        (shiftBromineSite substrate.rings.length substrate.bromines.length)
    oxygens := changedOxygens ++
      fragment.oxygens.map
        (shiftOxygenSite substrate.rings.length substrate.oxygens.length) }

/-- TESCl/imidazole changes every free O-H group into O-SiEt3 while leaving
carbonyls and existing silyl ethers unchanged. -/
def protectHydroxylsWithTES (d : MolecularDescriptor) : MolecularDescriptor :=
  { d with oxygens := d.oxygens.map fun site =>
      if site.kind = .hydroxyl then
        { site with kind := .silylEther .triethyl }
      else
        site }

/-- LiOH selectively removes the single TBS group in `G`; the two TES groups
are retained in the source-directed operation. -/
def cleaveTBS (d : MolecularDescriptor) : MolecularDescriptor :=
  { d with oxygens := d.oxygens.map fun site =>
      if site.kind = .silylEther .tertButyldimethyl then
        { site with kind := .hydroxyl }
      else
        site }

def dearomatizeLastRing : List RingKind → List RingKind
  | [] => []
  | _ :: [] => [.cyclohexa25Diene]
  | kind :: next :: rest => kind :: dearomatizeLastRing (next :: rest)

/-- Aqueous PhI(OAc)2 para-dearomatization of the terminal phenol: the
phenolic carbon becomes a carbonyl and the para carbon (already attached to the
preceding ring) receives hydroxyl. -/
def oxidativeDearomatization (d : MolecularDescriptor) : MolecularDescriptor :=
  let terminalRing := d.rings.length - 1
  let changedPhenol := d.oxygens.map fun site =>
    if site.ring = terminalRing ∧ site.position = 3 ∧ site.kind = .hydroxyl then
      { site with kind := .carbonyl }
    else
      site
  { d with
    rings := dearomatizeLastRing d.rings
    oxygens := changedPhenol ++
      [oxygenSite d.oxygens.length terminalRing 0 .hydroxyl] }

/-- Intramolecular Ni(0) Yamamoto coupling replaces the two terminal C-Br
bonds by the missing para-para C-C bond. -/
def yamamotoRingClosure (d : MolecularDescriptor) : MolecularDescriptor :=
  { d with closed := true, bromines := [] }

/-! The public supporting information used only to ground the qualitative
named-transform bridges is Kayahara--Patel--Yamago, *Synthesis and
Characterization of [5]Cycloparaphenylene*, DOI `10.1021/ja413214q.s001`,
especially pp. S3--S5.  These metadata are provenance, not answer premises. -/

def literatureDOI : String := "10.1021/ja413214q.s001"
def literatureStableURL : String := "https://doi.org/10.1021/ja413214q.s001"
def literatureLocator : String := "pp. S3-S5, syntheses of 5e, 1c, 3c, 3b, and [5]CPP"

/-! ## Independently stated candidates F--L -/

def candidateF : MolecularDescriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .benzene]
    closed := false
    bromines := [bromineSite 0 0 0]
    oxygens :=
      [ oxygenSite 0 1 0 .hydroxyl
      , oxygenSite 1 1 3 .hydroxyl
      , oxygenSite 2 3 3 (.silylEther .tertButyldimethyl) ] }

def candidateG : MolecularDescriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .benzene]
    closed := false
    bromines := [bromineSite 0 0 0]
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 (.silylEther .tertButyldimethyl) ] }

def candidateH : MolecularDescriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .benzene]
    closed := false
    bromines := [bromineSite 0 0 0]
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 .hydroxyl ] }

def candidateI : MolecularDescriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .cyclohexa25Diene]
    closed := false
    bromines := [bromineSite 0 0 0]
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 .carbonyl
      , oxygenSite 3 3 0 .hydroxyl ] }

def candidateJ : MolecularDescriptor :=
  { rings :=
      [ .benzene, .cyclohexa25Diene, .benzene
      , .cyclohexa25Diene, .benzene ]
    closed := false
    bromines := [bromineSite 0 0 0, bromineSite 1 4 3]
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 .hydroxyl
      , oxygenSite 3 3 0 .hydroxyl ] }

def candidateK : MolecularDescriptor :=
  { rings :=
      [ .benzene, .cyclohexa25Diene, .benzene
      , .cyclohexa25Diene, .benzene ]
    closed := false
    bromines := [bromineSite 0 0 0, bromineSite 1 4 3]
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 (.silylEther .triethyl)
      , oxygenSite 3 3 0 (.silylEther .triethyl) ] }

def candidateL : MolecularDescriptor :=
  { rings :=
      [ .benzene, .cyclohexa25Diene, .benzene
      , .cyclohexa25Diene, .benzene ]
    closed := true
    bromines := []
    oxygens :=
      [ oxygenSite 0 1 0 (.silylEther .triethyl)
      , oxygenSite 1 1 3 (.silylEther .triethyl)
      , oxygenSite 2 3 3 (.silylEther .triethyl)
      , oxygenSite 3 3 0 (.silylEther .triethyl) ] }

/-- Requested atom/bond carriers. -/
def structureF : MolecularStructure := candidateF.expand
def structureG : MolecularStructure := candidateG.expand
def structureH : MolecularStructure := candidateH.expand
def structureI : MolecularStructure := candidateI.expand
def structureJ : MolecularStructure := candidateJ.expand
def structureK : MolecularStructure := candidateK.expand
def structureL : MolecularStructure := candidateL.expand

def formulaF : MolecularFormula :=
  { carbon := 30, hydrogen := 33, oxygen := 3, silicon := 1, bromine := 1 }

def formulaG : MolecularFormula :=
  { carbon := 42, hydrogen := 61, oxygen := 3, silicon := 3, bromine := 1 }

/-- This is the formula printed beneath `H` in the problem figure. -/
def formulaH : MolecularFormula :=
  { carbon := 36, hydrogen := 47, oxygen := 3, silicon := 2, bromine := 1 }

def formulaI : MolecularFormula :=
  { carbon := 36, hydrogen := 47, oxygen := 4, silicon := 2, bromine := 1 }

def formulaJ : MolecularFormula :=
  { carbon := 42, hydrogen := 52, oxygen := 4, silicon := 2, bromine := 2 }

def formulaK : MolecularFormula :=
  { carbon := 54, hydrogen := 80, oxygen := 4, silicon := 4, bromine := 2 }

/-- This is the formula printed beneath `L` in the problem figure. -/
def formulaL : MolecularFormula :=
  { carbon := 54, hydrogen := 80, oxygen := 4, silicon := 4, bromine := 0 }

/-! ## Inline derivation of the required previous-part prerequisite (A4) -/

/-- The contest asks for integer atomic masses.  The mass numbers 12, 1, 14,
and 16 are checked against the pinned AME2020 subset; exact isotope masses are
not substituted for the requested integer convention. -/
def integerMassC : ℕ := 12
def integerMassH : ℕ := 1
def integerMassN : ℕ := 14
def integerMassO : ℕ := 16

def pinnedDatasetSHA256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def carbon12RecordSHA256 : String :=
  "2c212258b787c2459da3b2f29c00882f3d8183c37528ace98a83ece308a2decc"

def hydrogen1RecordSHA256 : String :=
  "32ec098d6ab9366a09311d83b4923d0f0120b126eeaacb7cfa4bbd0fa1497ff8"

def nitrogen14RecordSHA256 : String :=
  "2512d93a1393f4bca3ad7f9d94c35cd9bd7179d99d84b4dd258cbd63b95503ba"

def oxygen16RecordSHA256 : String :=
  "e3c31feaf7f8262947f9ffa8f4047dfd5f5c123ff0c136cab1f0fcca919e9c69"

def macrocycleEIntegerMass : ℕ :=
  40 * integerMassC + 34 * integerMassH +
    2 * integerMassN + 3 * integerMassO

def cyclo48CarbonIntegerMass : ℕ := 48 * integerMassC

/-- A no-fragment ion is assembled only from whole C48 rings, whole neutral
macrocycles E, and added protons. -/
structure NoFragmentIon where
  cyclo48Count : ℕ
  macrocycleECount : ℕ
  addedProtons : ℕ
  positiveCharge : ℕ
  deriving DecidableEq, Repr

def NoFragmentIon.integerMass (ion : NoFragmentIon) : ℕ :=
  ion.cyclo48Count * cyclo48CarbonIntegerMass +
    ion.macrocycleECount * macrocycleEIntegerMass +
    ion.addedProtons * integerMassH

def NoFragmentIon.FitsMz (ion : NoFragmentIon) (peak : ℕ) : Prop :=
  0 < ion.positiveCharge ∧ ion.integerMass = peak * ion.positiveCharge

def ion591 : NoFragmentIon :=
  { cyclo48Count := 0, macrocycleECount := 1
    addedProtons := 1, positiveCharge := 1 }

def ion783 : NoFragmentIon :=
  { cyclo48Count := 1, macrocycleECount := 3
    addedProtons := 3, positiveCharge := 3 }

def ion879 : NoFragmentIon :=
  { cyclo48Count := 1, macrocycleECount := 2
    addedProtons := 2, positiveCharge := 2 }

def ion1174 : NoFragmentIon :=
  { cyclo48Count := 1, macrocycleECount := 3
    addedProtons := 2, positiveCharge := 2 }

def PreviousPartA4Result : Prop :=
  macrocycleEIntegerMass = 590 ∧
  cyclo48CarbonIntegerMass = 576 ∧
  ion591.FitsMz 591 ∧
  ion783.FitsMz 783 ∧
  ion879.FitsMz 879 ∧
  ion1174.FitsMz 1174

/-! ## Requested output specifications -/

def SourceSchemeBound : Prop :=
  sourceArrows.length = 8 ∧
    ∀ arrow ∈ sourceArrows,
      arrow.transformationUse = .qualitativeNamedTransformOnly ∧
      arrow.locator = .page3SynthesisScheme

def StructureFResult : Prop :=
  terminalCarbonylAddition startingMaterial biphenylOTBSFragment = candidateF ∧
    CandidateChecks candidateF formulaF

def StructureGResult : Prop :=
  protectHydroxylsWithTES candidateF = candidateG ∧
    CandidateChecks candidateG formulaG

def StructureHResult : Prop :=
  cleaveTBS candidateG = candidateH ∧
    CandidateChecks candidateH formulaH

def StructureIResult : Prop :=
  oxidativeDearomatization candidateH = candidateI ∧
    CandidateChecks candidateI formulaI ∧
    structureI.HasIncidentBondOrder
      (.heavy (.ringCarbon 3 3)) .double ∧
    structureI.AtomStereoIs
      (.heavy (.ringCarbon 3 3)) .carbon .notStereogenic

def StructureJResult : Prop :=
  terminalCarbonylAddition candidateI paraBromophenylFragment = candidateJ ∧
    CandidateChecks candidateJ formulaJ

def StructureKResult : Prop :=
  protectHydroxylsWithTES candidateJ = candidateK ∧
    CandidateChecks candidateK formulaK

def StructureLResult : Prop :=
  yamamotoRingClosure candidateK = candidateL ∧
    CandidateChecks candidateL formulaL

/-- Raw solve-phase symbolic contract.  It includes the independently derived
previous-part prerequisite, the exact source-arrow transcription, and all seven
requested atom/bond structures. -/
def RawResult : Prop :=
  PreviousPartA4Result ∧
  SourceSchemeBound ∧
  StructureFResult ∧
  StructureGResult ∧
  StructureHResult ∧
  StructureIResult ∧
  StructureJResult ∧
  StructureKResult ∧
  StructureLResult

/-- Exact-symbolic reporting does not round or erase any structural field. -/
def ReportedResult : Prop :=
  StructureFResult ∧
  StructureGResult ∧
  StructureHResult ∧
  StructureIResult ∧
  StructureJResult ∧
  StructureKResult ∧
  StructureLResult ∧
  SourceSchemeBound ∧
  PreviousPartA4Result

/-! ## Finite certificates for the expanded molecular graphs

The specifications above deliberately use proposition-valued predicates.  In
particular, their universal quantifiers range over the (infinite) identifier
types and therefore do not acquire executable `Decidable` instances merely
because the atom and bond supports are finite.  The following Boolean
checkers inspect exactly those finite supports.  Their soundness lemmas bridge
the computations back to the accepted proposition-valued specifications.
-/

def MolecularStructure.endpointsPresentB (s : MolecularStructure) : Bool :=
  s.bonds.all fun bond =>
    decide (bond.left ∈ s.atomIds ∧ bond.right ∈ s.atomIds)

def MolecularStructure.noSelfBondsB (s : MolecularStructure) : Bool :=
  s.bonds.all fun bond => decide (bond.left ≠ bond.right)

def MolecularStructure.valenceCorrectB (s : MolecularStructure) : Bool :=
  s.atoms.all fun entry =>
    decide (s.incidentValence entry.1 = entry.2.element.expectedValence)

def MolecularStructure.hasIncidentBondOrderB
    (s : MolecularStructure) (id : AtomId) (order : BondOrder) : Bool :=
  s.bonds.any fun bond =>
    decide ((bond.left = id ∨ bond.right = id) ∧ bond.order = order)

def MolecularStructure.stereoBondOrderCompatibleB
    (s : MolecularStructure) : Bool :=
  s.atoms.all fun entry =>
    decide
      ((s.hasIncidentBondOrderB entry.1 .double = true →
          entry.2.stereochemistry = .notStereogenic) ∧
        (entry.2.stereochemistry = .sourceUnspecified →
          entry.2.element = .carbon ∧
            s.hasIncidentBondOrderB entry.1 .double = false))

def MolecularStructure.adjacentB
    (s : MolecularStructure) (a b : AtomId) : Bool :=
  s.bonds.any fun bond =>
    decide
      ((bond.left = a ∧ bond.right = b) ∨
        (bond.left = b ∧ bond.right = a))

def MolecularStructure.neighbors
    (s : MolecularStructure) (id : AtomId) : List AtomId :=
  s.bonds.foldr
    (fun bond rest =>
      if bond.left = id then bond.right :: rest
      else if bond.right = id then bond.left :: rest
      else rest)
    []

/-- A fuel-bounded depth-first traversal.  Each recursive child tour is
followed by its parent, so the first projection is a genuine graph walk rather
than merely a list of visited vertices. -/
def MolecularStructure.depthFirstTour (s : MolecularStructure) :
    ℕ → AtomId → List AtomId → List AtomId × List AtomId
  | 0, start, seen =>
      ([start], if start ∈ seen then seen else start :: seen)
  | fuel + 1, start, seen =>
      let seen' := if start ∈ seen then seen else start :: seen
      s.neighbors start |>.foldl
        (fun state next =>
          if next ∈ state.2 then
            state
          else
            let child := s.depthFirstTour fuel next state.2
            (state.1 ++ child.1 ++ [start], child.2))
        ([start], seen')

def MolecularStructure.connectivityTour (s : MolecularStructure) : List AtomId :=
  (s.depthFirstTour s.atomIds.length (.heavy (.ringCarbon 0 0)) []).1

def MolecularStructure.walkValidB :
    (s : MolecularStructure) → List AtomId → Bool
  | _, [] => true
  | _, [_] => true
  | s, a :: b :: rest => s.adjacentB a b && s.walkValidB (b :: rest)

def MolecularStructure.tourCoversB
    (s : MolecularStructure) (tour : List AtomId) : Bool :=
  s.atomIds.all fun id => decide (id ∈ tour)

def MolecularStructure.connectedB (s : MolecularStructure) : Bool :=
  let tour := s.connectivityTour
  decide (tour ≠ []) && (s.walkValidB tour && s.tourCoversB tour)

def MolecularStructure.localChecksB (s : MolecularStructure) : Bool :=
  decide s.atomIds.Nodup &&
    (s.endpointsPresentB &&
      (s.noSelfBondsB &&
        (s.valenceCorrectB &&
          (s.stereoBondOrderCompatibleB &&
            (decide (s.totalFormalCharge = 0) &&
              decide (s.totalRadicalElectrons = 0))))))

def CandidateChecksB (descriptor : MolecularDescriptor)
    (formula : MolecularFormula) : Bool :=
  decide (descriptor.expand.formula = formula) &&
    (descriptor.expand.localChecksB && descriptor.expand.connectedB)

theorem MolecularStructure.endpointsPresentB_sound
    {s : MolecularStructure} (h : s.endpointsPresentB = true) :
    s.BondEndpointsPresent := by
  intro bond hb
  exact of_decide_eq_true ((List.all_eq_true.mp h) bond hb)

theorem MolecularStructure.noSelfBondsB_sound
    {s : MolecularStructure} (h : s.noSelfBondsB = true) :
    s.NoSelfBonds := by
  intro bond hb
  exact of_decide_eq_true ((List.all_eq_true.mp h) bond hb)

theorem MolecularStructure.valenceCorrectB_sound
    {s : MolecularStructure} (h : s.valenceCorrectB = true) :
    s.ValenceCorrect := by
  intro id atom hmem
  exact of_decide_eq_true ((List.all_eq_true.mp h) (id, atom) hmem)

theorem MolecularStructure.hasIncidentBondOrderB_eq_true_iff
    {s : MolecularStructure} {id : AtomId} {order : BondOrder} :
    s.hasIncidentBondOrderB id order = true ↔
      s.HasIncidentBondOrder id order := by
  simp [MolecularStructure.hasIncidentBondOrderB,
    MolecularStructure.HasIncidentBondOrder, List.any_eq_true]

theorem MolecularStructure.stereoBondOrderCompatibleB_sound
    {s : MolecularStructure} (h : s.stereoBondOrderCompatibleB = true) :
    s.StereoBondOrderCompatible := by
  intro id atom hmem
  have hentry :=
    of_decide_eq_true ((List.all_eq_true.mp h) (id, atom) hmem)
  constructor
  · intro hdouble
    exact hentry.1
      (MolecularStructure.hasIncidentBondOrderB_eq_true_iff.mpr hdouble)
  · intro hstereo
    have hfinite := hentry.2 hstereo
    refine ⟨hfinite.1, ?_⟩
    intro hdouble
    have htrue : s.hasIncidentBondOrderB id .double = true :=
      MolecularStructure.hasIncidentBondOrderB_eq_true_iff.mpr hdouble
    have hfalse := hfinite.2
    simp [htrue] at hfalse

theorem MolecularStructure.adjacentB_eq_true_iff
    {s : MolecularStructure} {a b : AtomId} :
    s.adjacentB a b = true ↔ s.Adjacent a b := by
  simp [MolecularStructure.adjacentB, MolecularStructure.Adjacent,
    List.any_eq_true]

theorem MolecularStructure.adjacent_symm (s : MolecularStructure) :
    ∀ {a b : AtomId}, s.Adjacent a b → s.Adjacent b a := by
  rintro a b ⟨bond, hb, hab | hba⟩
  · exact ⟨bond, hb, Or.inr hab⟩
  · exact ⟨bond, hb, Or.inl hba⟩

theorem reflTransGen_reverse {α : Type} {r : α → α → Prop}
    (hsymm : ∀ {a b}, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih

theorem MolecularStructure.walkValidB_reaches_head
    (s : MolecularStructure) :
    ∀ {a rest}, s.walkValidB (a :: rest) = true →
      ∀ x ∈ a :: rest, Relation.ReflTransGen s.Adjacent a x := by
  intro a rest
  induction rest generalizing a with
  | nil =>
      intro _ x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact .refl
  | cons b rest ih =>
      intro hvalid x hx
      simp only [MolecularStructure.walkValidB, Bool.and_eq_true] at hvalid
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        exact .refl
      · exact
          (Relation.ReflTransGen.single
            (MolecularStructure.adjacentB_eq_true_iff.mp hvalid.1)).trans
            (ih hvalid.2 x hx)

theorem MolecularStructure.tourCoversB_sound
    {s : MolecularStructure} {tour : List AtomId}
    (h : s.tourCoversB tour = true) :
    ∀ id ∈ s.atomIds, id ∈ tour := by
  intro id hid
  exact of_decide_eq_true ((List.all_eq_true.mp h) id hid)

theorem MolecularStructure.connectedB_sound
    {s : MolecularStructure} (h : s.connectedB = true) : s.Connected := by
  unfold MolecularStructure.connectedB at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hneB, hvalid, hcover⟩
  have hne : s.connectivityTour ≠ [] := of_decide_eq_true hneB
  have hcover' : ∀ id ∈ s.atomIds, id ∈ s.connectivityTour :=
    MolecularStructure.tourCoversB_sound hcover
  intro a ha b hb
  have haTour := hcover' a ha
  have hbTour := hcover' b hb
  obtain ⟨root, rest, htour⟩ := List.exists_cons_of_ne_nil hne
  have hvalid' : s.walkValidB (root :: rest) = true := by
    simpa [htour] using hvalid
  have haTour' : a ∈ root :: rest := by
    simpa [htour] using haTour
  have hbTour' : b ∈ root :: rest := by
    simpa [htour] using hbTour
  have hroota : Relation.ReflTransGen s.Adjacent root a :=
    MolecularStructure.walkValidB_reaches_head s hvalid' a haTour'
  have hrootb : Relation.ReflTransGen s.Adjacent root b :=
    MolecularStructure.walkValidB_reaches_head s hvalid' b hbTour'
  exact
    (reflTransGen_reverse (MolecularStructure.adjacent_symm s) hroota).trans
      hrootb

theorem MolecularStructure.localChecksB_sound
    {s : MolecularStructure} (h : s.localChecksB = true) :
    s.atomIds.Nodup ∧
      s.BondEndpointsPresent ∧
      s.NoSelfBonds ∧
      s.ValenceCorrect ∧
      s.StereoBondOrderCompatible ∧
      s.totalFormalCharge = 0 ∧
      s.totalRadicalElectrons = 0 := by
  simp only [MolecularStructure.localChecksB, Bool.and_eq_true] at h
  rcases h with ⟨hnodup, hendpoints, hself, hvalence, hstereo, hcharge, hradical⟩
  exact
    ⟨ of_decide_eq_true hnodup
    , MolecularStructure.endpointsPresentB_sound hendpoints
    , MolecularStructure.noSelfBondsB_sound hself
    , MolecularStructure.valenceCorrectB_sound hvalence
    , MolecularStructure.stereoBondOrderCompatibleB_sound hstereo
    , of_decide_eq_true hcharge
    , of_decide_eq_true hradical ⟩

theorem candidateChecksB_sound {descriptor : MolecularDescriptor}
    {formula : MolecularFormula} (h : CandidateChecksB descriptor formula = true) :
    CandidateChecks descriptor formula := by
  simp only [CandidateChecksB, Bool.and_eq_true] at h
  rcases h with ⟨hformula, hlocal, hconnected⟩
  refine ⟨of_decide_eq_true hformula, ?_⟩
  rcases MolecularStructure.localChecksB_sound hlocal with
    ⟨hnodup, hendpoints, hself, hvalence, hstereo, hcharge, hradical⟩
  exact
    ⟨ hnodup, hendpoints, hself, hvalence, hstereo
    , MolecularStructure.connectedB_sound hconnected
    , hcharge, hradical ⟩

theorem previous_part_a4_result : PreviousPartA4Result := by
  norm_num [PreviousPartA4Result, NoFragmentIon.FitsMz,
    NoFragmentIon.integerMass, ion591, ion783, ion879, ion1174,
    macrocycleEIntegerMass, cyclo48CarbonIntegerMass, integerMassC,
    integerMassH, integerMassN, integerMassO]

theorem structure_f_output : StructureFResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem structure_g_output : StructureGResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem structure_h_output : StructureHResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem structure_i_output : StructureIResult := by
  refine
    ⟨ by native_decide
    , candidateChecksB_sound (by native_decide)
    , ?_
    , ?_ ⟩
  · exact MolecularStructure.hasIncidentBondOrderB_eq_true_iff.mp (by native_decide)
  · refine
      ⟨ { element := .carbon
          formalCharge := 0
          radicalElectrons := 0
          stereochemistry := .notStereogenic }
      , ?_, rfl, rfl ⟩
    native_decide

theorem structure_j_output : StructureJResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem structure_k_output : StructureKResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem structure_l_output : StructureLResult := by
  refine ⟨by native_decide, candidateChecksB_sound ?_⟩
  native_decide

theorem source_scheme_bound : SourceSchemeBound := by
  simp [SourceSchemeBound, sourceArrows]

theorem raw_result :
    ("54a0b6256a1217250fa109829c2ddd669f7dda7ea8a1075e770382352240fc7f" : String) =
      "54a0b6256a1217250fa109829c2ddd669f7dda7ea8a1075e770382352240fc7f" ∧
    RawResult := by
  constructor
  · rfl
  · exact
      ⟨ previous_part_a4_result
      , source_scheme_bound
      , structure_f_output
      , structure_g_output
      , structure_h_output
      , structure_i_output
      , structure_j_output
      , structure_k_output
      , structure_l_output ⟩

theorem reported_result :
    ("c32f74d1e6a809fe09598fede94d001d115a2c7d2ca5581b1fe5827a52dc87a2" : String) =
      "c32f74d1e6a809fe09598fede94d001d115a2c7d2ca5581b1fe5827a52dc87a2" ∧
    ReportedResult := by
  constructor
  · rfl
  · exact
      ⟨ structure_f_output
      , structure_g_output
      , structure_h_output
      , structure_i_output
      , structure_j_output
      , structure_k_output
      , structure_l_output
      , source_scheme_bound
      , previous_part_a4_result ⟩

end IChO2026Problems.Icho2026T6A5
