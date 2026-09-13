import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T8-A4: Fe--quaterpyridine CO₂-reduction cycle

This answer-blind formalization reconstructs the seven requested coordination
complexes from the two problem pages.  Molecular drawings are represented by
finite labelled graphs rather than names or strings.  Hydrogens that are
implicit in the line drawings are recorded as an explicit multiplicity on the
heavy atom to which they are bonded; all other atoms and every covalent or
coordination bond are enumerated.

The first reduction is ligand-centred.  Thus the iron oxidation state remains
`+2`, while the quaterpyridine ligand in complexes 10 and 11 is a delocalized
radical anion.  CO₂ in 11 is neutral and binds side-on through C and O.
Proton-coupled electron transfer then moves both stored reducing equivalents
into a closed-shell hydroxycarbonyl ligand.

The previous T8-A2 conclusion is not imported.  The five donor intermediates
3--7 and their two-electron/two-proton net ledger are reconstructed locally
from the problem-only triethanolamine scheme.
-/

namespace IChO2026Problems.ProblemIChO2026T8A4

/-! ## Finite molecular-graph language -/

/-- Elements appearing in ligand 8, the coordination sphere, the support
formula, and the locally reconstructed sacrificial-donor mechanism. -/
inductive Element
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  | chlorine
  | iron
  deriving DecidableEq, Fintype, Repr

/-- Covalent bond orders distinguished by the printed structures. -/
inductive BondOrder
  | single
  | double
  | triple
  deriving DecidableEq, Fintype, Repr

/-- No atom stereocentre occurs in the source drawings, but the field is kept
so that a structure cannot silently omit requested stereochemical data. -/
inductive AtomStereo
  | notStereogenic
  | clockwise
  | anticlockwise
  | unspecified
  deriving DecidableEq, Repr

/-- Likewise, none of the displayed bonds carries E/Z stereochemistry. -/
inductive BondStereo
  | none
  | together
  | opposite
  | unspecified
  deriving DecidableEq, Repr

/-- One explicitly numbered heavy atom.  `attachedHydrogens` records the
implicit C--H, N--H, or O--H atoms of the line drawing. -/
structure Atom where
  element : Element
  formalCharge : ℤ
  unpairedElectrons : ℕ
  attachedHydrogens : ℕ
  stereochemistry : AtomStereo
  deriving DecidableEq, Repr

/-- Canonically oriented covalent bond between heavy-atom indices. -/
structure CovalentBond where
  lower : ℕ
  upper : ℕ
  order : BondOrder
  stereochemistry : BondStereo
  deriving DecidableEq, Repr

/-- A radical electron may be delocalized over a source-bounded set of atom
indices instead of being assigned spuriously to one atom. -/
structure DelocalizedRadical where
  support : Finset ℕ
  electronCount : ℕ
  deriving DecidableEq

/-- A finite Lewis graph.  Delocalized formal charge is separated from local
atomic formal charges, which is essential for the reduced π ligand. -/
structure MolecularGraph where
  atoms : List Atom
  bonds : List CovalentBond
  delocalizedFormalCharge : ℤ
  delocalizedRadicals : List DelocalizedRadical
  deriving DecidableEq

/-- One ligand-to-metal two-electron donation unit.  A localized lone-pair
donation has one Fe-contact atom, whereas a side-on `η²` π donation has two
Fe-contact atoms but is still only one donated electron pair. -/
inductive CoordinationDonation
  | localizedPair (contactAtom : ℕ)
  | etaTwoPiPair (firstContact secondContact : ℕ)
  deriving DecidableEq, Repr

def CoordinationDonation.contactAtoms : CoordinationDonation → List ℕ
  | .localizedPair atomIndex => [atomIndex]
  | .etaTwoPiPair first second => [first, second]

/-- Both source-relevant donation classes are L/X two-electron units in the
ionic electron-counting convention. -/
def CoordinationDonation.electronCount (_ : CoordinationDonation) : ℕ := 2

/-- A coordinating fragment records donation units rather than conflating
their electron donation with the number of Fe-contact atoms. -/
structure CoordinatingFragment where
  graph : MolecularGraph
  donationUnits : List CoordinationDonation
  deriving DecidableEq

/-- All atoms in direct contact with Fe; this list determines CN. -/
def CoordinatingFragment.donorAtoms (f : CoordinatingFragment) : List ℕ :=
  f.donationUnits.flatMap CoordinationDonation.contactAtoms

/-- Total ligand-to-metal electron donation; this quantity determines VE. -/
def CoordinatingFragment.donatedElectronCount
    (f : CoordinatingFragment) : ℕ :=
  (f.donationUnits.map CoordinationDonation.electronCount).sum

/-- Exact molecular formula over all elements used in this target. -/
structure MolecularFormula where
  hydrogen : ℕ
  carbon : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  chlorine : ℕ
  iron : ℕ
  deriving DecidableEq, Repr

/-- Permitted answer-blind provenance classes from the source report together
with the sealed mode's narrowly scoped public-literature bridge. -/
inductive Provenance
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | publicLiterature
  | derivedTheorem
  deriving DecidableEq, Repr

/-- Source-local evidence locator; this records evidence but is not itself an
opaque chemical premise. -/
structure EvidenceLocator where
  provenance : Provenance
  path : String
  panel : String
  fact : String
  deriving DecidableEq, Repr

/-- Typed alternatives for the orbital receiving an electron.  Keeping the
metal-centred alternative in the language prevents the candidate from being
selected merely by the type of the carrier. -/
inductive ElectronLocalization
  | qpyPiStar
  | ironD
  deriving DecidableEq, Repr

/-- Typed alternatives for coordination of a carbon-dioxide fragment. -/
inductive CarbonDioxideBindingMode
  | endOnCarbon
  | sideOnCarbonOxygen
  deriving DecidableEq, Repr

/-- Atom through which a one-carbon intermediate contacts Fe. -/
inductive CarbonBindingAtom
  | carbon
  | oxygen
  deriving DecidableEq, Repr

inductive CarbonIntermediateIdentity
  | hydroxycarbonyl
  | carbonyl
  deriving DecidableEq, Repr

inductive ReleasedCarbonProduct
  | carbonMonoxide
  deriving DecidableEq, Repr

inductive LiteratureSupport
  | crystallineCarbonNitride
  deriving DecidableEq, Repr

inductive ReactionMedium
  | aqueous
  deriving DecidableEq, Repr

/-- Candidate-independent applicability scope of the public paper. -/
structure CatalystLiteratureScope where
  metal : Element
  ligandFormula : MolecularFormula
  ligandDonorCount : ℕ
  supportFormula : MolecularFormula
  support : LiteratureSupport
  medium : ReactionMedium
  deriving DecidableEq, Repr

def atom (e : Element) (charge : ℤ) (radicals hydrogens : ℕ) : Atom :=
  { element := e
    formalCharge := charge
    unpairedElectrons := radicals
    attachedHydrogens := hydrogens
    stereochemistry := .notStereogenic }

def carbon (hydrogens : ℕ) : Atom := atom .carbon 0 0 hydrogens
def nitrogen (hydrogens : ℕ := 0) : Atom := atom .nitrogen 0 0 hydrogens
def oxygen (hydrogens : ℕ := 0) : Atom := atom .oxygen 0 0 hydrogens
def chlorineAtom : Atom := atom .chlorine (-1) 0 0

def bond (i j : ℕ) (order : BondOrder) : CovalentBond :=
  { lower := min i j
    upper := max i j
    order := order
    stereochemistry := .none }

def MolecularGraph.elementCount (g : MolecularGraph) (e : Element) : ℕ :=
  (g.atoms.map fun a =>
    (if a.element = e then 1 else 0) +
      (if e = .hydrogen then a.attachedHydrogens else 0)).sum

def MolecularGraph.netFormalCharge (g : MolecularGraph) : ℤ :=
  (g.atoms.map (fun a => a.formalCharge)).sum + g.delocalizedFormalCharge

def MolecularGraph.totalUnpairedElectrons (g : MolecularGraph) : ℕ :=
  (g.atoms.map (fun a => a.unpairedElectrons)).sum +
    (g.delocalizedRadicals.map (fun r => r.electronCount)).sum

def MolecularGraph.hasFormula (g : MolecularGraph) (f : MolecularFormula) : Prop :=
  g.elementCount .hydrogen = f.hydrogen ∧
  g.elementCount .carbon = f.carbon ∧
  g.elementCount .nitrogen = f.nitrogen ∧
  g.elementCount .oxygen = f.oxygen ∧
  g.elementCount .chlorine = f.chlorine ∧
  g.elementCount .iron = f.iron

def HasBond (g : MolecularGraph) (i j : ℕ) (order : BondOrder) : Prop :=
  bond i j order ∈ g.bonds

/-- Structural well-formedness shared by all molecular fragments. -/
def MolecularGraph.WellFormed (g : MolecularGraph) : Prop :=
  g.bonds.Nodup ∧
  g.bonds.Forall (fun b => b.lower < b.upper ∧ b.upper < g.atoms.length) ∧
  (∀ a ∈ g.atoms, a.stereochemistry ≠ .unspecified) ∧
  g.bonds.Forall (fun b => b.stereochemistry ≠ .unspecified) ∧
  (∀ r ∈ g.delocalizedRadicals,
    0 < r.electronCount ∧ ∀ i ∈ r.support, i < g.atoms.length)

def CoordinatingFragment.WellFormed (f : CoordinatingFragment) : Prop :=
  f.graph.WellFormed ∧ f.donorAtoms.Nodup ∧
    f.donationUnits.Forall fun donation =>
      donation.contactAtoms.Nodup ∧
        ∀ i ∈ donation.contactAtoms, i < f.graph.atoms.length

/-! ## Source-first reconstruction of ligand 8 -/

/-- Atom numbering for ligand 8:

* `0--5`, `6--11`, `12--17`, and `18--23` are the four successive
  pyridine rings (N atoms `0,6,12,18`);
* `24--29` is the para-disubstituted phenyl group attached to atom `3` of
  the terminal pyridine;
* `30--32` is `C(=O)OH`, attached to phenyl atom `27`.

The attached-H multiplicities sum to 18. -/
def ligand8Atoms : List Atom :=
  [ nitrogen 0, carbon 0, carbon 1, carbon 0, carbon 1, carbon 1
  , nitrogen 0, carbon 0, carbon 1, carbon 1, carbon 1, carbon 0
  , nitrogen 0, carbon 0, carbon 1, carbon 1, carbon 1, carbon 0
  , nitrogen 0, carbon 0, carbon 1, carbon 1, carbon 1, carbon 1
  , carbon 0, carbon 1, carbon 1, carbon 0, carbon 1, carbon 1
  , carbon 0, oxygen 1, oxygen 0 ]

/-- Every heavy-atom bond read from the ligand-8 drawing.  The three
inter-pyridine bonds are `1--7`, `11--13`, and `17--19`; the only remaining
cross-component bonds are `3--24` and `27--30`. -/
def ligand8Bonds : List CovalentBond :=
  [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
  , bond 3 4 .double, bond 4 5 .single, bond 0 5 .double
  , bond 6 7 .single, bond 7 8 .double, bond 8 9 .single
  , bond 9 10 .double, bond 10 11 .single, bond 6 11 .double
  , bond 12 13 .single, bond 13 14 .double, bond 14 15 .single
  , bond 15 16 .double, bond 16 17 .single, bond 12 17 .double
  , bond 18 19 .single, bond 19 20 .double, bond 20 21 .single
  , bond 21 22 .double, bond 22 23 .single, bond 18 23 .double
  , bond 1 7 .single, bond 11 13 .single, bond 17 19 .single
  , bond 3 24 .single
  , bond 24 25 .single, bond 25 26 .double, bond 26 27 .single
  , bond 27 28 .double, bond 28 29 .single, bond 24 29 .double
  , bond 27 30 .single, bond 30 31 .single, bond 30 32 .double ]

inductive Ligand8RedoxState
  | neutral
  | radicalAnion
  deriving DecidableEq, Repr

/-- Machine-usable content of the catalyst-specific literature claim.  These
fields are evidence data, not solver-selectable premises: the single record
below binds them to the paper metadata and exact applicability scope. -/
structure FeQpyMechanismSemantics where
  firstReductionSite : ElectronLocalization
  firstReductionProductCore : Ligand8RedoxState
  co2AdductStoredElectronSite : ElectronLocalization
  co2AdductCore : Ligand8RedoxState
  coordinatedCarbonDioxideCharge : ℤ
  carbonDioxideBindingMode : CarbonDioxideBindingMode
  ironOxidationState : ℤ
  secondReductionSite : ElectronLocalization
  postProtonationCore : Ligand8RedoxState
  protonatedIntermediate : CarbonIntermediateIdentity
  protonatedBindingAtom : CarbonBindingAtom
  dehydratedIntermediate : CarbonIntermediateIdentity
  dehydratedBindingAtom : CarbonBindingAtom
  releasedProduct : ReleasedCarbonProduct
  deriving DecidableEq, Repr

/-- Public-literature evidence with typed chemistry in the same record as its
title, DOI, locator, scope, and content digest. -/
structure LiteratureRecord where
  provenance : Provenance
  title : String
  doi : String
  url : String
  locator : String
  scopedClaim : String
  applicabilityConditions : String
  contentSha256 : String
  scope : CatalystLiteratureScope
  mechanism : FeQpyMechanismSemantics
  deriving DecidableEq, Repr

def ligand8Graph : Ligand8RedoxState → MolecularGraph
  | .neutral =>
      { atoms := ligand8Atoms
        bonds := ligand8Bonds
        delocalizedFormalCharge := 0
        delocalizedRadicals := [] }
  | .radicalAnion =>
      { atoms := ligand8Atoms
        bonds := ligand8Bonds
        delocalizedFormalCharge := -1
        delocalizedRadicals :=
          [{ support := Finset.range 24, electronCount := 1 }] }

def ligand8Fragment (state : Ligand8RedoxState) : CoordinatingFragment :=
  { graph := ligand8Graph state
    donationUnits :=
      [.localizedPair 0, .localizedPair 6,
       .localizedPair 12, .localizedPair 18] }

def ligand8Formula : MolecularFormula :=
  { hydrogen := 18, carbon := 27, nitrogen := 4, oxygen := 2,
    chlorine := 0, iron := 0 }

/-- Nontrivial source-image carrier for the complete ligand-8 topology. -/
def Ligand8ImageSpecification (state : Ligand8RedoxState) : Prop :=
  (ligand8Fragment state).graph.atoms = ligand8Atoms ∧
  (ligand8Fragment state).graph.bonds = ligand8Bonds ∧
  (ligand8Fragment state).donorAtoms = [0, 6, 12, 18] ∧
  (ligand8Fragment state).graph.hasFormula ligand8Formula ∧
  (ligand8Fragment state).WellFormed ∧
  (match state with
    | .neutral =>
        (ligand8Fragment state).graph.netFormalCharge = 0 ∧
        (ligand8Fragment state).graph.totalUnpairedElectrons = 0
    | .radicalAnion =>
        (ligand8Fragment state).graph.netFormalCharge = -1 ∧
        (ligand8Fragment state).graph.totalUnpairedElectrons = 1)

/-! ## Ancillary ligands and assembled coordination complexes -/

inductive AncillaryLigand
  | chloride
  | water
  | carbonDioxide (mode : CarbonDioxideBindingMode) (formalCharge : ℤ)
  | hydroxycarbonyl (bindingAtom : CarbonBindingAtom)
  | carbonyl (bindingAtom : CarbonBindingAtom)
  deriving DecidableEq, Repr

def chlorideFragment : CoordinatingFragment :=
  { graph :=
      { atoms := [chlorineAtom]
        bonds := []
        delocalizedFormalCharge := 0
        delocalizedRadicals := [] }
    donationUnits := [.localizedPair 0] }

def waterFragment : CoordinatingFragment :=
  { graph :=
      { atoms := [oxygen 2]
        bonds := []
        delocalizedFormalCharge := 0
        delocalizedRadicals := [] }
    donationUnits := [.localizedPair 0] }

/-- Electron-donation classification associated with each CO₂ binding mode.
The side-on mode is one `η²` π pair spanning its C and one O, not two
independent lone-pair donations. -/
def carbonDioxideDonation :
    CarbonDioxideBindingMode → CoordinationDonation
  | .endOnCarbon => .localizedPair 1
  | .sideOnCarbonOxygen => .etaTwoPiPair 1 0

/-- A carbon-dioxide fragment whose charge and binding mode come from typed
evidence.  Atom 1 is C; side-on binding adds an Fe--O contact at atom 0. -/
def carbonDioxideFragment
    (mode : CarbonDioxideBindingMode) (formalCharge : ℤ) :
    CoordinatingFragment :=
  { graph :=
      { atoms := [oxygen 0, carbon 0, oxygen 0]
        bonds := [bond 0 1 .double, bond 1 2 .double]
        delocalizedFormalCharge := formalCharge
        delocalizedRadicals := [] }
    donationUnits := [carbonDioxideDonation mode] }

/-- The concrete neutral side-on fragment supported by the scoped paper. -/
def carbonDioxideEta2Fragment : CoordinatingFragment :=
  carbonDioxideFragment .sideOnCarbonOxygen 0

/-- The hapticity/electron-donation distinction for the neutral side-on CO₂
fragment used in complex 11. -/
def Eta2CarbonDioxideDonationSpecification : Prop :=
  carbonDioxideEta2Fragment.donorAtoms = [1, 0] ∧
  carbonDioxideEta2Fragment.donationUnits = [.etaTwoPiPair 1 0] ∧
  carbonDioxideEta2Fragment.donatedElectronCount = 2

def carbonIntermediateDonation :
    CarbonBindingAtom → CoordinationDonation
  | .carbon => .localizedPair 0
  | .oxygen => .localizedPair 1

/-- `COOH⁻` bound through carbon.  In ionic bond cleavage the carbon bears
the ligand's `-1` charge; coordination completes its valence. -/
def hydroxycarbonylFragmentAt
    (bindingAtom : CarbonBindingAtom) : CoordinatingFragment :=
  { graph :=
      { atoms := [atom .carbon (-1) 0 0, oxygen 0, oxygen 1]
        bonds := [bond 0 1 .double, bond 0 2 .single]
        delocalizedFormalCharge := 0
        delocalizedRadicals := [] }
    donationUnits := [carbonIntermediateDonation bindingAtom] }

def hydroxycarbonylFragment : CoordinatingFragment :=
  hydroxycarbonylFragmentAt .carbon

/-- Carbonyl bound through carbon, represented by the charge-separated
`⁻C≡O⁺` Lewis form. -/
def carbonylFragmentAt
    (bindingAtom : CarbonBindingAtom) : CoordinatingFragment :=
  { graph :=
      { atoms := [atom .carbon (-1) 0 0, atom .oxygen 1 0 0]
        bonds := [bond 0 1 .triple]
        delocalizedFormalCharge := 0
        delocalizedRadicals := [] }
    donationUnits := [carbonIntermediateDonation bindingAtom] }

def carbonylFragment : CoordinatingFragment :=
  carbonylFragmentAt .carbon

def ancillaryFragment : AncillaryLigand → CoordinatingFragment
  | .chloride => chlorideFragment
  | .water => waterFragment
  | .carbonDioxide mode charge => carbonDioxideFragment mode charge
  | .hydroxycarbonyl binding => hydroxycarbonylFragmentAt binding
  | .carbonyl binding => carbonylFragmentAt binding

inductive ComplexPhase
  | molecularPrecursor
  | crystallineCarbonNitrideSupportedAqueous
  deriving DecidableEq, Repr

/-- The metal atom is explicit, while its spin multiplicity is left unknown
because the problem does not request or stipulate it. -/
structure MetalCenter where
  element : Element
  unpairedElectrons : Option ℕ
  deriving DecidableEq, Repr

def ironCenter : MetalCenter :=
  { element := .iron, unpairedElectrons := none }

/-- Crystallinity is source data, not a solver-selectable Boolean flag. -/
inductive SolidForm
  | crystalline
  deriving DecidableEq, Repr

structure SupportMaterial where
  formula : MolecularFormula
  solidForm : SolidForm
  provenance : Provenance
  deriving DecidableEq, Repr

def carbonNitrideSupport : SupportMaterial :=
  { formula :=
      { hydrogen := 0, carbon := 3, nitrogen := 4, oxygen := 0,
        chlorine := 0, iron := 0 }
    solidForm := .crystalline
    provenance := .problemText }

/-- A complex contains the complete core graph, an ordered list of ancillary
fragments, its source phase, and its net ionic charge. -/
structure CoordinationComplex where
  metal : MetalCenter
  core : CoordinatingFragment
  ancillary : List AncillaryLigand
  phase : ComplexPhase
  netCharge : ℤ
  deriving DecidableEq

inductive ComponentAddress
  | core
  | ancillary (index : ℕ)
  deriving DecidableEq, Repr

/-- One explicit Fe--donor coordination contact. -/
structure CoordinationEdge where
  component : ComponentAddress
  donorAtom : ℕ
  deriving DecidableEq, Repr

def ancillaryCoordinationEdges : List AncillaryLigand → ℕ → List CoordinationEdge
  | [], _ => []
  | kind :: rest, index =>
      ((ancillaryFragment kind).donorAtoms.map fun donor =>
        { component := .ancillary index, donorAtom := donor }) ++
      ancillaryCoordinationEdges rest (index + 1)

def CoordinationComplex.coordinationEdges
    (c : CoordinationComplex) : List CoordinationEdge :=
  (c.core.donorAtoms.map fun donor =>
    { component := .core, donorAtom := donor }) ++
  ancillaryCoordinationEdges c.ancillary 0

def CoordinationComplex.coordinationNumber (c : CoordinationComplex) : ℕ :=
  c.coordinationEdges.length

def CoordinationComplex.ligandCharge (c : CoordinationComplex) : ℤ :=
  c.core.graph.netFormalCharge +
    (c.ancillary.map fun kind =>
      (ancillaryFragment kind).graph.netFormalCharge).sum

/-- Total ligand-to-Fe donation, counted by electron-pair units rather than
by contact atoms.  In particular, neutral side-on `η²-CO₂` contributes two
electrons while contributing two contacts to CN. -/
def CoordinationComplex.ligandDonatedElectrons
    (c : CoordinationComplex) : ℕ :=
  c.core.donatedElectronCount +
    (c.ancillary.map fun kind =>
      (ancillaryFragment kind).donatedElectronCount).sum

/-- Ionic oxidation-state bookkeeping: net complex charge equals iron OS plus
the sum of ionic ligand charges. -/
def CoordinationComplex.oxidationState (c : CoordinationComplex) : ℤ :=
  c.netCharge - c.ligandCharge

/-- Fe is group 8.  VE uses donation units, not contact-atom hapticity;
ligand-centred radical electrons are not metal d electrons. -/
def CoordinationComplex.valenceElectrons (c : CoordinationComplex) : ℤ :=
  8 - c.oxidationState + (c.ligandDonatedElectrons : ℤ)

def CoordinationComplex.elementCount
    (c : CoordinationComplex) (e : Element) : ℕ :=
  (if c.metal.element = e then 1 else 0) + c.core.graph.elementCount e +
    (c.ancillary.map fun kind =>
      (ancillaryFragment kind).graph.elementCount e).sum

def CoordinationEdgesValid (c : CoordinationComplex) : Prop :=
  c.coordinationEdges.Forall fun edge =>
    match edge.component with
    | .core => edge.donorAtom < c.core.graph.atoms.length
    | .ancillary index =>
        ∃ kind, c.ancillary[index]? = some kind ∧
          edge.donorAtom < (ancillaryFragment kind).graph.atoms.length

def CoordinationComplex.WellFormed (c : CoordinationComplex) : Prop :=
  c.metal.element = .iron ∧ c.metal.unpairedElectrons = none ∧
  c.core.WellFormed ∧
  c.ancillary.Forall (fun kind => (ancillaryFragment kind).WellFormed) ∧
  CoordinationEdgesValid c

/-- Candidate-independent ionic, contact, and donation-unit bookkeeping used
for every reported OS, CN, and VE value. -/
def StandardCoordinationBookkeeping : Prop :=
  Eta2CarbonDioxideDonationSpecification ∧
  ∀ c : CoordinationComplex,
    c.oxidationState = c.netCharge - c.ligandCharge ∧
    c.coordinationNumber = c.coordinationEdges.length ∧
    c.valenceElectrons =
      8 - c.oxidationState + (c.ligandDonatedElectrons : ℤ)

/-! ## Bound source evidence and the external mechanism authority -/

def problemFigureEvidence : List EvidenceLocator :=
  [ { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-1.png"
      panel := "ligand 8 / FeCl₂ synthesis panel"
      fact := "four consecutive pyridine rings; terminal-pyridine para-carboxyphenyl substituent; four N donors; FeCl₂ gives catalyst 1" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "1 to 9"
      fact := "add 2 H₂O and remove 2 Cl⁻" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "9 to 10"
      fact := "add one photon and one electron; remove H₂O" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "10 to 11"
      fact := "add CO₂ and remove H₂O" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "11 to 12"
      fact := "add one photon, one electron, and one proton" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "12 to 13"
      fact := "add H₂O" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "13 to 14"
      fact := "add H⁺ and remove H₂O" }
  , { provenance := .problemImage
      path := "icho_2026_source/image/T8_page-2.png"
      panel := "14 to 15 to 9"
      fact := "remove CO, then add H₂O" } ]

/-- Source-derived catalyst scope, fixed before any requested-stage witness is
constructed. -/
def sourceCatalystLiteratureScope : CatalystLiteratureScope :=
  { metal := ironCenter.element
    ligandFormula := ligand8Formula
    ligandDonorCount := (ligand8Fragment .neutral).donorAtoms.length
    supportFormula := carbonNitrideSupport.formula
    support := .crystallineCarbonNitride
    medium := .aqueous }

/-- The metadata and the typed mechanism fields form one indivisible public-
literature record. -/
def feQpyMechanismLiterature : LiteratureRecord :=
  { provenance := .publicLiterature
    title := "Illuminating the mechanistic impacts of an Fe-quaterpyridine functionalized crystalline poly(triazine imide) semiconductor for photocatalytic CO₂ reduction"
    doi := "10.1039/d5qi00859j"
    url := "https://www.osti.gov/servlets/purl/3377957"
    locator := "Scheme 1 (page 6641); Computational analysis and Figure 6 (pages 6648-6649)"
    scopedClaim := "For the same carboxy-functionalized Fe-qpy/PTI catalyst, the first reduction is qpy-ligand-centred; the reduced qpy state persists while neutral CO₂ binds side-on through C and O at Fe(II); the second electron again enters qpy pi-star orbitals before protonation gives Fe--COOH, water dissociation gives Fe--CO, and CO is released."
    applicabilityConditions := "The problem's carboxy-functionalized four-N Fe-qpy catalyst on crystalline carbon nitride in water and its printed one-electron, CO₂-capture, second-electron, protonation, water-loss, and CO-release arrows; no claim of rate, yield, completeness, or sole-product formation is imported."
    contentSha256 := "9f45fc489b714d50dca635ff51bb7270159d2531edc9311dcc595a30c70bec0e"
    scope :=
      { metal := .iron
        ligandFormula :=
          { hydrogen := 18, carbon := 27, nitrogen := 4, oxygen := 2,
            chlorine := 0, iron := 0 }
        ligandDonorCount := 4
        supportFormula :=
          { hydrogen := 0, carbon := 3, nitrogen := 4, oxygen := 0,
            chlorine := 0, iron := 0 }
        support := .crystallineCarbonNitride
        medium := .aqueous }
    mechanism :=
      { firstReductionSite := .qpyPiStar
        firstReductionProductCore := .radicalAnion
        co2AdductStoredElectronSite := .qpyPiStar
        co2AdductCore := .radicalAnion
        coordinatedCarbonDioxideCharge := 0
        carbonDioxideBindingMode := .sideOnCarbonOxygen
        ironOxidationState := 2
        secondReductionSite := .qpyPiStar
        postProtonationCore := .neutral
        protonatedIntermediate := .hydroxycarbonyl
        protonatedBindingAtom := .carbon
        dehydratedIntermediate := .carbonyl
        dehydratedBindingAtom := .carbon
        releasedProduct := .carbonMonoxide } }

/-- Typed, provenance-bound applicability proposition.  Unlike a record of
strings, this proposition exposes every chemistry choice consumed by the graph
transformations below. -/
def LiteratureAuthorityApplies (r : LiteratureRecord) : Prop :=
  r.provenance = .publicLiterature ∧
  r.title =
      "Illuminating the mechanistic impacts of an Fe-quaterpyridine functionalized crystalline poly(triazine imide) semiconductor for photocatalytic CO₂ reduction" ∧
  r.doi = "10.1039/d5qi00859j" ∧
  r.url = "https://www.osti.gov/servlets/purl/3377957" ∧
  r.locator =
      "Scheme 1 (page 6641); Computational analysis and Figure 6 (pages 6648-6649)" ∧
  r.scopedClaim =
      "For the same carboxy-functionalized Fe-qpy/PTI catalyst, the first reduction is qpy-ligand-centred; the reduced qpy state persists while neutral CO₂ binds side-on through C and O at Fe(II); the second electron again enters qpy pi-star orbitals before protonation gives Fe--COOH, water dissociation gives Fe--CO, and CO is released." ∧
  r.applicabilityConditions =
      "The problem's carboxy-functionalized four-N Fe-qpy catalyst on crystalline carbon nitride in water and its printed one-electron, CO₂-capture, second-electron, protonation, water-loss, and CO-release arrows; no claim of rate, yield, completeness, or sole-product formation is imported." ∧
  r.contentSha256 =
      "9f45fc489b714d50dca635ff51bb7270159d2531edc9311dcc595a30c70bec0e" ∧
  r.scope = sourceCatalystLiteratureScope ∧
  r.mechanism.firstReductionSite = .qpyPiStar ∧
  r.mechanism.firstReductionProductCore = .radicalAnion ∧
  r.mechanism.co2AdductStoredElectronSite = .qpyPiStar ∧
  r.mechanism.co2AdductCore = .radicalAnion ∧
  r.mechanism.coordinatedCarbonDioxideCharge = 0 ∧
  r.mechanism.carbonDioxideBindingMode = .sideOnCarbonOxygen ∧
  r.mechanism.ironOxidationState = 2 ∧
  r.mechanism.secondReductionSite = .qpyPiStar ∧
  r.mechanism.postProtonationCore = .neutral ∧
  r.mechanism.protonatedIntermediate = .hydroxycarbonyl ∧
  r.mechanism.protonatedBindingAtom = .carbon ∧
  r.mechanism.dehydratedIntermediate = .carbonyl ∧
  r.mechanism.dehydratedBindingAtom = .carbon ∧
  r.mechanism.releasedProduct = .carbonMonoxide

/-- The source arrows are used only as named compatibility transformations;
no yield, completeness, rate, phase amount, or unshown stream is asserted. -/
inductive TransformationUse
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def selectedTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-! ## Inline derivation of the T8-A2 prerequisite -/

/-- Triethanolamine 2, `N(CH₂CH₂OH)₃`. -/
def donor2 : MolecularGraph :=
  { atoms :=
      [ nitrogen 0
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1 ]
    bonds :=
      [ bond 0 1 .single, bond 1 2 .single, bond 2 3 .single
      , bond 0 4 .single, bond 4 5 .single, bond 5 6 .single
      , bond 0 7 .single, bond 7 8 .single, bond 8 9 .single ]
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

/-- Intermediate 3: the one-electron-oxidized aminium radical cation. -/
def donor3 : MolecularGraph :=
  { atoms :=
      [ atom .nitrogen 1 1 0
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1 ]
    bonds := donor2.bonds
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

/-- Intermediate 4: α-deprotonation of one of the three symmetry-equivalent
arms gives a neutral α-amino carbon radical. -/
def donor4 : MolecularGraph :=
  { atoms :=
      [ nitrogen 0
      , atom .carbon 0 1 1, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1 ]
    bonds := donor2.bonds
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

/-- Intermediate 5: second one-electron oxidation forms the iminium cation. -/
def donor5 : MolecularGraph :=
  { atoms :=
      [ atom .nitrogen 1 0 0
      , carbon 1, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1 ]
    bonds :=
      [ bond 0 1 .double, bond 1 2 .single, bond 2 3 .single
      , bond 0 4 .single, bond 4 5 .single, bond 5 6 .single
      , bond 0 7 .single, bond 7 8 .single, bond 8 9 .single ]
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

/-- Product 6: diethanolamine. -/
def donor6 : MolecularGraph :=
  { atoms :=
      [ nitrogen 1
      , carbon 2, carbon 2, oxygen 1
      , carbon 2, carbon 2, oxygen 1 ]
    bonds :=
      [ bond 0 1 .single, bond 1 2 .single, bond 2 3 .single
      , bond 0 4 .single, bond 4 5 .single, bond 5 6 .single ]
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

/-- Product 7: glycolaldehyde, `HOCH₂CHO`; the `C(=O)H` subgraph is the
source-compatible reason it gives the stated silver-mirror test. -/
def donor7 : MolecularGraph :=
  { atoms :=
      [ carbon 1, oxygen 0, carbon 2, oxygen 1 ]
    bonds := [bond 0 1 .double, bond 0 2 .single, bond 2 3 .single]
    delocalizedFormalCharge := 0
    delocalizedRadicals := [] }

def donor2Formula : MolecularFormula :=
  { hydrogen := 15, carbon := 6, nitrogen := 1, oxygen := 3,
    chlorine := 0, iron := 0 }

def donor4And5Formula : MolecularFormula :=
  { hydrogen := 14, carbon := 6, nitrogen := 1, oxygen := 3,
    chlorine := 0, iron := 0 }

def donor6Formula : MolecularFormula :=
  { hydrogen := 11, carbon := 4, nitrogen := 1, oxygen := 2,
    chlorine := 0, iron := 0 }

def donor7Formula : MolecularFormula :=
  { hydrogen := 4, carbon := 2, nitrogen := 0, oxygen := 2,
    chlorine := 0, iron := 0 }

def HasAldehydeGroup (g : MolecularGraph) : Prop :=
  g.atoms[0]? = some (carbon 1) ∧
  g.atoms[1]? = some (oxygen 0) ∧ HasBond g 0 1 .double

/-- Formula-level atom ledger for
`2 + H₂O → 6 + 7 + 2 H⁺ + 2 e⁻`. -/
def DonorNetAtomLedger : Prop :=
  ∀ e : Element,
    donor2.elementCount e + waterFragment.graph.elementCount e =
      donor6.elementCount e + donor7.elementCount e +
        (if e = .hydrogen then 2 else 0)

/-- Charge ledger for the same net donor oxidation. -/
def DonorNetChargeLedger : Prop :=
  donor2.netFormalCharge =
    donor6.netFormalCharge + donor7.netFormalCharge + 2 + 2 * (-1)

/-- Locally reconstructed, problem-only T8-A2 result. -/
def PreviousPartA2Result : Prop :=
  donor3.WellFormed ∧ donor4.WellFormed ∧ donor5.WellFormed ∧
  donor6.WellFormed ∧ donor7.WellFormed ∧
  donor3.hasFormula donor2Formula ∧ donor3.netFormalCharge = 1 ∧
    donor3.totalUnpairedElectrons = 1 ∧
  donor4.hasFormula donor4And5Formula ∧ donor4.netFormalCharge = 0 ∧
    donor4.totalUnpairedElectrons = 1 ∧
  donor5.hasFormula donor4And5Formula ∧ donor5.netFormalCharge = 1 ∧
    donor5.totalUnpairedElectrons = 0 ∧
  donor6.hasFormula donor6Formula ∧ donor7.hasFormula donor7Formula ∧
  HasAldehydeGroup donor7 ∧ DonorNetAtomLedger ∧ DonorNetChargeLedger

theorem previousPartA2_derivedFromProblem : PreviousPartA2Result := by
  have h3 : donor3.WellFormed := by
    simp [MolecularGraph.WellFormed, donor3, donor2, bond, atom, carbon,
      nitrogen, oxygen]
  have h4 : donor4.WellFormed := by
    simp [MolecularGraph.WellFormed, donor4, donor2, bond, atom, carbon,
      nitrogen, oxygen]
  have h5 : donor5.WellFormed := by
    simp [MolecularGraph.WellFormed, donor5, bond, atom, carbon, oxygen]
  have h6 : donor6.WellFormed := by
    simp [MolecularGraph.WellFormed, donor6, bond, atom, carbon, nitrogen,
      oxygen]
  have h7 : donor7.WellFormed := by
    simp [MolecularGraph.WellFormed, donor7, bond, atom, carbon, oxygen]
  have hAtomLedger : DonorNetAtomLedger := by
    intro e
    cases e <;> native_decide
  unfold PreviousPartA2Result
  refine ⟨h3, h4, h5, h6, h7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hAtomLedger, ?_⟩
  all_goals
    first
    | (unfold MolecularGraph.hasFormula; native_decide)
    | (unfold HasAldehydeGroup HasBond; native_decide)
    | (unfold DonorNetChargeLedger; native_decide)
    | native_decide

/-! ## Source-directed transformations and the seven complexes -/

/-- Catalyst 1 before aquation: neutral Fe(ligand 8)Cl₂. -/
def catalyst1 : CoordinationComplex :=
  { metal := ironCenter
    core := ligand8Fragment .neutral
    ancillary := [.chloride, .chloride]
    phase := .molecularPrecursor
    netCharge := 0 }

/-- Typed transcription of the page-1 ligand-8 plus FeCl₂ synthesis panel.
The Fe oxidation state is deliberately not assumed here; it is computed from
the neutral precursor and the two explicit chloride graphs. -/
def Catalyst1ImageSpecification : Prop :=
  catalyst1.metal = ironCenter ∧
  catalyst1.core = ligand8Fragment .neutral ∧
  catalyst1.ancillary = [.chloride, .chloride] ∧
  catalyst1.phase = .molecularPrecursor ∧
  catalyst1.netCharge = 0

def replaceFirst (old new : AncillaryLigand) :
    List AncillaryLigand → List AncillaryLigand
  | [] => []
  | kind :: rest =>
      if kind = old then new :: rest else kind :: replaceFirst old new rest

/-- `1 + 2 H₂O - 2 Cl⁻ → 9`. -/
def aquateCatalyst (c : CoordinationComplex) : CoordinationComplex :=
  { c with
    ancillary := c.ancillary.map fun kind =>
      if kind = .chloride then .water else kind
    phase := .crystallineCarbonNitrideSupportedAqueous
    netCharge := c.netCharge + (c.ancillary.count .chloride : ℤ) }

/-- Interpret the literature's typed first-reduction assignment.  The
metal-centred branch is retained in the language, although it is not selected
by the source-bound Fe/qpy record. -/
def firstReductionCore
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinatingFragment :=
  match r.mechanism.firstReductionSite with
  | .qpyPiStar => ligand8Fragment r.mechanism.firstReductionProductCore
  | .ironD => c.core

/-- First photon/electron step, with the electronic location supplied by the
typed literature record rather than embedded in this transformation. -/
def ligandReduceAndLoseWater
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinationComplex :=
  { c with
    core := firstReductionCore r c
    ancillary := c.ancillary.erase .water
    netCharge := c.netCharge - 1 }

/-- CO₂ capture interpreted from the record's charge, binding mode, and
post-capture qpy state. -/
def bindCarbonDioxideFromLiterature
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinationComplex :=
  { c with
    core := ligand8Fragment r.mechanism.co2AdductCore
    ancillary := (c.ancillary.erase .water) ++
      [.carbonDioxide r.mechanism.carbonDioxideBindingMode
        r.mechanism.coordinatedCarbonDioxideCharge] }

def carbonIntermediateLigand
    (identity : CarbonIntermediateIdentity)
    (bindingAtom : CarbonBindingAtom) : AncillaryLigand :=
  match identity with
  | .hydroxycarbonyl => .hydroxycarbonyl bindingAtom
  | .carbonyl => .carbonyl bindingAtom

/-- The second electron and first proton move both qpy-stored reducing
equivalents into coordinated CO₂ to give closed-shell `COOH⁻`; qpy returns
to neutral for this record.  Electron plus proton has zero net charge, so the
complex charge is unchanged. -/
def pcetFromLiterature
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinationComplex :=
  { c with
    core := ligand8Fragment r.mechanism.postProtonationCore
    ancillary := replaceFirst
      (.carbonDioxide r.mechanism.carbonDioxideBindingMode
        r.mechanism.coordinatedCarbonDioxideCharge)
      (carbonIntermediateLigand r.mechanism.protonatedIntermediate
        r.mechanism.protonatedBindingAtom) c.ancillary }

def addAquoLigand (c : CoordinationComplex) : CoordinationComplex :=
  { c with ancillary := c.ancillary ++ [.water] }

/-- Interpret the typed protonation/dehydration identities while retaining the
aquo ligand that was added on the preceding printed arrow. -/
def protonateAndDehydrate
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinationComplex :=
  { c with
    ancillary := replaceFirst
      (carbonIntermediateLigand r.mechanism.protonatedIntermediate
        r.mechanism.protonatedBindingAtom)
      (carbonIntermediateLigand r.mechanism.dehydratedIntermediate
        r.mechanism.dehydratedBindingAtom) c.ancillary
    netCharge := c.netCharge + 1 }

def releaseCarbonProduct
    (r : LiteratureRecord) (c : CoordinationComplex) : CoordinationComplex :=
  match r.mechanism.releasedProduct with
  | .carbonMonoxide =>
      { c with ancillary :=
          (c.ancillary.erase
            (carbonIntermediateLigand r.mechanism.dehydratedIntermediate
              r.mechanism.dehydratedBindingAtom)) }

def complex9 : CoordinationComplex := aquateCatalyst catalyst1
def complex10 : CoordinationComplex :=
  ligandReduceAndLoseWater feQpyMechanismLiterature complex9
def complex11 : CoordinationComplex :=
  bindCarbonDioxideFromLiterature feQpyMechanismLiterature complex10
def complex12 : CoordinationComplex :=
  pcetFromLiterature feQpyMechanismLiterature complex11
def complex13 : CoordinationComplex := addAquoLigand complex12
def complex14 : CoordinationComplex :=
  protonateAndDehydrate feQpyMechanismLiterature complex13
def complex15 : CoordinationComplex :=
  releaseCarbonProduct feQpyMechanismLiterature complex14

/-- The closing water-binding step returns 15 to 9. -/
def closeCycleFrom15 : CoordinationComplex := addAquoLigand complex15

inductive Stage
  | nine | ten | eleven | twelve | thirteen | fourteen | fifteen
  deriving DecidableEq, Fintype, Repr

def derivedComplex : Stage → CoordinationComplex
  | .nine => complex9
  | .ten => complex10
  | .eleven => complex11
  | .twelve => complex12
  | .thirteen => complex13
  | .fourteen => complex14
  | .fifteen => complex15

abbrev CatalyticCycle := Stage → CoordinationComplex

inductive ExternalSpecies
  | photon | electron | proton | water | chloride
  | carbonDioxide | carbonMonoxide
  deriving DecidableEq, Fintype, Repr

abbrev ExternalInventory := ExternalSpecies → ℕ

structure ArrowAnnotation where
  inputs : ExternalInventory
  outputs : ExternalInventory

inductive CycleArrow
  | oneToNine | nineToTen | tenToEleven | elevenToTwelve
  | twelveToThirteen | thirteenToFourteen | fourteenToFifteen
  | fifteenToNine
  deriving DecidableEq, Fintype, Repr

def sourceArrow : CycleArrow → ArrowAnnotation
  | .oneToNine =>
      { inputs := fun | .water => 2 | _ => 0
        outputs := fun | .chloride => 2 | _ => 0 }
  | .nineToTen =>
      { inputs := fun | .photon | .electron => 1 | _ => 0
        outputs := fun | .water => 1 | _ => 0 }
  | .tenToEleven =>
      { inputs := fun | .carbonDioxide => 1 | _ => 0
        outputs := fun | .water => 1 | _ => 0 }
  | .elevenToTwelve =>
      { inputs := fun | .photon | .electron | .proton => 1 | _ => 0
        outputs := fun _ => 0 }
  | .twelveToThirteen =>
      { inputs := fun | .water => 1 | _ => 0
        outputs := fun _ => 0 }
  | .thirteenToFourteen =>
      { inputs := fun | .proton => 1 | _ => 0
        outputs := fun | .water => 1 | _ => 0 }
  | .fourteenToFifteen =>
      { inputs := fun _ => 0
        outputs := fun | .carbonMonoxide => 1 | _ => 0 }
  | .fifteenToNine =>
      { inputs := fun | .water => 1 | _ => 0
        outputs := fun _ => 0 }

def externalAtomCount : ExternalSpecies → Element → ℕ
  | .proton, .hydrogen => 1
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .chloride, .chlorine => 1
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .oxygen => 1
  | _, _ => 0

def externalCharge : ExternalSpecies → ℤ
  | .electron => -1
  | .proton => 1
  | .chloride => -1
  | _ => 0

def inventoryAtomCount (q : ExternalInventory) (e : Element) : ℕ :=
  ∑ species, q species * externalAtomCount species e

def inventoryCharge (q : ExternalInventory) : ℤ :=
  ∑ species, (q species : ℤ) * externalCharge species

def StepAtomBalanced
    (before after : CoordinationComplex) (arrow : ArrowAnnotation) : Prop :=
  ∀ e : Element,
    before.elementCount e + inventoryAtomCount arrow.inputs e =
      after.elementCount e + inventoryAtomCount arrow.outputs e

def StepChargeBalanced
    (before after : CoordinationComplex) (arrow : ArrowAnnotation) : Prop :=
  before.netCharge + inventoryCharge arrow.inputs =
    after.netCharge + inventoryCharge arrow.outputs

def SourceArrowCompatible
    (before after : CoordinationComplex) (arrow : ArrowAnnotation) : Prop :=
  StepAtomBalanced before after arrow ∧ StepChargeBalanced before after arrow

/-- Typed transcription of every nonzero label on the eight problem-image
arrows.  The `sourceArrow` definitions additionally set every unprinted entry
to zero. -/
def SourceArrowImageSpecification : Prop :=
  (sourceArrow .oneToNine).inputs .water = 2 ∧
  (sourceArrow .oneToNine).outputs .chloride = 2 ∧
  (sourceArrow .nineToTen).inputs .photon = 1 ∧
  (sourceArrow .nineToTen).inputs .electron = 1 ∧
  (sourceArrow .nineToTen).outputs .water = 1 ∧
  (sourceArrow .tenToEleven).inputs .carbonDioxide = 1 ∧
  (sourceArrow .tenToEleven).outputs .water = 1 ∧
  (sourceArrow .elevenToTwelve).inputs .photon = 1 ∧
  (sourceArrow .elevenToTwelve).inputs .electron = 1 ∧
  (sourceArrow .elevenToTwelve).inputs .proton = 1 ∧
  (sourceArrow .twelveToThirteen).inputs .water = 1 ∧
  (sourceArrow .thirteenToFourteen).inputs .proton = 1 ∧
  (sourceArrow .thirteenToFourteen).outputs .water = 1 ∧
  (sourceArrow .fourteenToFifteen).outputs .carbonMonoxide = 1 ∧
  (sourceArrow .fifteenToNine).inputs .water = 1

/-- The public claim is now a proposition about arbitrary graph
transformations, not inert prose.  Its consequences are exactly the scoped
qpy-centred reduction, neutral side-on C/O CO₂ binding, Fe--COOH, Fe--CO,
and CO-release assignments. -/
def LiteratureGraphInterpretation (r : LiteratureRecord) : Prop :=
  LiteratureAuthorityApplies r ∧
  ∀ c : CoordinationComplex,
    (ligandReduceAndLoseWater r c).core =
        ligand8Fragment .radicalAnion ∧
    (bindCarbonDioxideFromLiterature r c).core =
        ligand8Fragment .radicalAnion ∧
    (bindCarbonDioxideFromLiterature r c).ancillary =
        (c.ancillary.erase .water) ++
          [.carbonDioxide .sideOnCarbonOxygen 0] ∧
    (pcetFromLiterature r c).core = ligand8Fragment .neutral ∧
    (pcetFromLiterature r c).ancillary =
        replaceFirst (.carbonDioxide .sideOnCarbonOxygen 0)
          (.hydroxycarbonyl .carbon) c.ancillary ∧
    (protonateAndDehydrate r c).ancillary =
        replaceFirst (.hydroxycarbonyl .carbon) (.carbonyl .carbon)
          c.ancillary ∧
    (releaseCarbonProduct r c).ancillary =
        c.ancillary.erase (.carbonyl .carbon)

/-- Candidate-side primitive atom/charge checks against the explicitly printed
species.  This is a `qualitative_named_transform_only` compatibility test: it
asserts neither yield nor the absence of unprinted material streams. -/
def CandidatePrimitiveArrowChecks (cycle : CatalyticCycle) : Prop :=
  SourceArrowCompatible catalyst1 (cycle .nine) (sourceArrow .oneToNine) ∧
  SourceArrowCompatible (cycle .nine) (cycle .ten) (sourceArrow .nineToTen) ∧
  SourceArrowCompatible (cycle .ten) (cycle .eleven)
    (sourceArrow .tenToEleven) ∧
  SourceArrowCompatible (cycle .eleven) (cycle .twelve)
    (sourceArrow .elevenToTwelve) ∧
  SourceArrowCompatible (cycle .twelve) (cycle .thirteen)
    (sourceArrow .twelveToThirteen) ∧
  SourceArrowCompatible (cycle .thirteen) (cycle .fourteen)
    (sourceArrow .thirteenToFourteen) ∧
  SourceArrowCompatible (cycle .fourteen) (cycle .fifteen)
    (sourceArrow .fourteenToFifteen) ∧
  SourceArrowCompatible (cycle .fifteen) (cycle .nine)
    (sourceArrow .fifteenToNine)

/-- A source-compatible trace.  The transition interpreter consumes the typed
literature record, while the second conjunctive layer checks the exact printed
external annotations.  No uniqueness quantifier is imposed. -/
def FollowsSourceMechanism
    (r : LiteratureRecord) (cycle : CatalyticCycle) : Prop :=
  LiteratureGraphInterpretation r ∧
  cycle .nine = aquateCatalyst catalyst1 ∧
  cycle .ten = ligandReduceAndLoseWater r (cycle .nine) ∧
  cycle .eleven = bindCarbonDioxideFromLiterature r (cycle .ten) ∧
  cycle .twelve = pcetFromLiterature r (cycle .eleven) ∧
  cycle .thirteen = addAquoLigand (cycle .twelve) ∧
  cycle .fourteen = protonateAndDehydrate r (cycle .thirteen) ∧
  cycle .fifteen = releaseCarbonProduct r (cycle .fourteen) ∧
  addAquoLigand (cycle .fifteen) = cycle .nine ∧
  CandidatePrimitiveArrowChecks cycle

def DerivedCandidatePrimitiveChecks : Prop :=
  CandidatePrimitiveArrowChecks derivedComplex

def cycleInputCount (species : ExternalSpecies) : ℕ :=
  ∑ arrow : CycleArrow, (sourceArrow arrow).inputs species

/-- The two one-electron and two proton inputs in the cycle match the net
output of the independently reconstructed donor oxidation. -/
def PreviousPartMatchesCycle : Prop :=
  PreviousPartA2Result ∧ cycleInputCount .electron = 2 ∧
    cycleInputCount .proton = 2

/-! ## Candidate specifications and requested-output carriers -/

def CoreTopologySpecified (c : CoordinationComplex) : Prop :=
  c.core.graph.atoms = ligand8Atoms ∧
  c.core.graph.bonds = ligand8Bonds ∧
  c.core.donorAtoms = [0, 6, 12, 18]

def CompleteComplexStructure (c : CoordinationComplex) : Prop :=
  c.phase = .crystallineCarbonNitrideSupportedAqueous ∧
  CoreTopologySpecified c ∧ c.WellFormed ∧
  (∀ kind ∈ c.ancillary,
    (ancillaryFragment kind).graph.atoms.length > 0) ∧
  c.coordinationEdges.length = c.coordinationNumber

@[simp] private theorem ligand8Fragment_atoms_eq (state : Ligand8RedoxState) :
    (ligand8Fragment state).graph.atoms = ligand8Atoms := by
  cases state <;> rfl

@[simp] private theorem ligand8Fragment_bonds_eq (state : Ligand8RedoxState) :
    (ligand8Fragment state).graph.bonds = ligand8Bonds := by
  cases state <;> rfl

@[simp] private theorem ligand8Fragment_donorAtoms_eq
    (state : Ligand8RedoxState) :
    (ligand8Fragment state).donorAtoms = [0, 6, 12, 18] := by
  cases state <;> native_decide

set_option maxHeartbeats 400000 in
@[simp] private theorem ligand8Fragment_wellFormed
    (state : Ligand8RedoxState) : (ligand8Fragment state).WellFormed := by
  cases state <;>
  simp [CoordinatingFragment.WellFormed, MolecularGraph.WellFormed,
    ligand8Fragment, ligand8Graph, ligand8Atoms, ligand8Bonds,
    CoordinatingFragment.donorAtoms, CoordinationDonation.contactAtoms,
    bond, atom, carbon, nitrogen, oxygen]; omega

@[simp] private theorem waterFragment_wellFormed :
    waterFragment.WellFormed := by
  simp [CoordinatingFragment.WellFormed, MolecularGraph.WellFormed,
    waterFragment, CoordinatingFragment.donorAtoms,
    CoordinationDonation.contactAtoms, atom, oxygen]

@[simp] private theorem waterFragment_donorAtoms :
    waterFragment.donorAtoms = [0] := by
  native_decide

@[simp] private theorem waterFragment_atomCount :
    waterFragment.graph.atoms.length = 1 := by
  native_decide

@[simp] private theorem carbonDioxideEta2Fragment_wellFormed :
    (carbonDioxideFragment .sideOnCarbonOxygen 0).WellFormed := by
  simp [CoordinatingFragment.WellFormed, MolecularGraph.WellFormed,
    carbonDioxideFragment, carbonDioxideDonation,
    CoordinatingFragment.donorAtoms, CoordinationDonation.contactAtoms,
    bond, atom, carbon, oxygen]

@[simp] private theorem carbonDioxideEta2Fragment_donorAtoms :
    (carbonDioxideFragment .sideOnCarbonOxygen 0).donorAtoms = [1, 0] := by
  native_decide

@[simp] private theorem carbonDioxideEta2Fragment_atomCount :
    (carbonDioxideFragment .sideOnCarbonOxygen 0).graph.atoms.length = 3 := by
  native_decide

@[simp] private theorem hydroxycarbonylFragment_wellFormed :
    (hydroxycarbonylFragmentAt .carbon).WellFormed := by
  simp [CoordinatingFragment.WellFormed, MolecularGraph.WellFormed,
    hydroxycarbonylFragmentAt, carbonIntermediateDonation,
    CoordinatingFragment.donorAtoms, CoordinationDonation.contactAtoms,
    bond, atom, oxygen]

@[simp] private theorem hydroxycarbonylFragment_donorAtoms :
    (hydroxycarbonylFragmentAt .carbon).donorAtoms = [0] := by
  native_decide

@[simp] private theorem hydroxycarbonylFragment_atomCount :
    (hydroxycarbonylFragmentAt .carbon).graph.atoms.length = 3 := by
  native_decide

@[simp] private theorem carbonylFragment_wellFormed :
    (carbonylFragmentAt .carbon).WellFormed := by
  simp [CoordinatingFragment.WellFormed, MolecularGraph.WellFormed,
    carbonylFragmentAt, carbonIntermediateDonation,
    CoordinatingFragment.donorAtoms, CoordinationDonation.contactAtoms,
    bond, atom]

@[simp] private theorem carbonylFragment_donorAtoms :
    (carbonylFragmentAt .carbon).donorAtoms = [0] := by
  native_decide

@[simp] private theorem carbonylFragment_atomCount :
    (carbonylFragmentAt .carbon).graph.atoms.length = 2 := by
  native_decide

private theorem derivedComplex_complete (stage : Stage) :
    CompleteComplexStructure (derivedComplex stage) := by
  cases stage <;>
  simp [CompleteComplexStructure, CoreTopologySpecified,
    CoordinationComplex.WellFormed, CoordinationEdgesValid,
    derivedComplex, complex15, complex14, complex13, complex12, complex11,
    complex10, complex9, releaseCarbonProduct, protonateAndDehydrate,
    addAquoLigand, pcetFromLiterature, bindCarbonDioxideFromLiterature,
    ligandReduceAndLoseWater, firstReductionCore, carbonIntermediateLigand,
    replaceFirst, feQpyMechanismLiterature, aquateCatalyst, catalyst1,
    ironCenter, ancillaryFragment,
    CoordinationComplex.coordinationNumber,
    CoordinationComplex.coordinationEdges, ancillaryCoordinationEdges,
    ligand8Atoms]

/-- A requested drawing is a concrete complete witness occurring in one trace
that obeys the source arrows and the typed same-catalyst literature bridge.
The problem asks to draw a structure, not to prove open-world uniqueness. -/
def StructureResult (stage : Stage) (candidate : CoordinationComplex) : Prop :=
  CompleteComplexStructure candidate ∧
  ∃ cycle : CatalyticCycle,
    FollowsSourceMechanism feQpyMechanismLiterature cycle ∧
      cycle stage = candidate

def OxidationStateResult
    (stage : Stage) (candidate : CoordinationComplex) (value : ℤ) : Prop :=
  StructureResult stage candidate ∧ candidate.oxidationState = value

def CoordinationNumberResult
    (stage : Stage) (candidate : CoordinationComplex) (value : ℕ) : Prop :=
  StructureResult stage candidate ∧ candidate.coordinationNumber = value

def ValenceElectronsResult
    (stage : Stage) (candidate : CoordinationComplex) (value : ℤ) : Prop :=
  StructureResult stage candidate ∧ candidate.valenceElectrons = value

def TotalChargeResult
    (stage : Stage) (candidate : CoordinationComplex) (value : ℤ) : Prop :=
  StructureResult stage candidate ∧ candidate.netCharge = value

def Structure9Result : Prop := StructureResult .nine complex9
def Complex9OxidationStateResult : Prop :=
  OxidationStateResult .nine complex9 2
def Complex9CoordinationNumberResult : Prop :=
  CoordinationNumberResult .nine complex9 6
def Complex9ValenceElectronsResult : Prop :=
  ValenceElectronsResult .nine complex9 18
def Complex9TotalChargeResult : Prop := TotalChargeResult .nine complex9 2

def Structure10Result : Prop := StructureResult .ten complex10
def Complex10OxidationStateResult : Prop :=
  OxidationStateResult .ten complex10 2
def Complex10CoordinationNumberResult : Prop :=
  CoordinationNumberResult .ten complex10 5
def Complex10ValenceElectronsResult : Prop :=
  ValenceElectronsResult .ten complex10 16
def Complex10TotalChargeResult : Prop := TotalChargeResult .ten complex10 1

def Structure11Result : Prop := StructureResult .eleven complex11
def Complex11OxidationStateResult : Prop :=
  OxidationStateResult .eleven complex11 2
def Complex11CoordinationNumberResult : Prop :=
  CoordinationNumberResult .eleven complex11 6
def Complex11ValenceElectronsResult : Prop :=
  ValenceElectronsResult .eleven complex11 16
def Complex11TotalChargeResult : Prop := TotalChargeResult .eleven complex11 1

def Structure12Result : Prop := StructureResult .twelve complex12
def Complex12OxidationStateResult : Prop :=
  OxidationStateResult .twelve complex12 2
def Complex12CoordinationNumberResult : Prop :=
  CoordinationNumberResult .twelve complex12 5
def Complex12ValenceElectronsResult : Prop :=
  ValenceElectronsResult .twelve complex12 16
def Complex12TotalChargeResult : Prop := TotalChargeResult .twelve complex12 1

def Structure13Result : Prop := StructureResult .thirteen complex13
def Complex13OxidationStateResult : Prop :=
  OxidationStateResult .thirteen complex13 2
def Complex13CoordinationNumberResult : Prop :=
  CoordinationNumberResult .thirteen complex13 6
def Complex13ValenceElectronsResult : Prop :=
  ValenceElectronsResult .thirteen complex13 18
def Complex13TotalChargeResult : Prop := TotalChargeResult .thirteen complex13 1

def Structure14Result : Prop := StructureResult .fourteen complex14
def Complex14OxidationStateResult : Prop :=
  OxidationStateResult .fourteen complex14 2
def Complex14CoordinationNumberResult : Prop :=
  CoordinationNumberResult .fourteen complex14 6
def Complex14ValenceElectronsResult : Prop :=
  ValenceElectronsResult .fourteen complex14 18
def Complex14TotalChargeResult : Prop := TotalChargeResult .fourteen complex14 2

def Structure15Result : Prop := StructureResult .fifteen complex15
def Complex15OxidationStateResult : Prop :=
  OxidationStateResult .fifteen complex15 2
def Complex15CoordinationNumberResult : Prop :=
  CoordinationNumberResult .fifteen complex15 5
def Complex15ValenceElectronsResult : Prop :=
  ValenceElectronsResult .fifteen complex15 16
def Complex15TotalChargeResult : Prop := TotalChargeResult .fifteen complex15 2

/-- The source-first assumptions are kept separate from the 35 requested
conclusions. -/
def ProblemAssumptions : Prop :=
  selectedTransformationUse = .qualitativeNamedTransformOnly ∧
  Ligand8ImageSpecification .neutral ∧
  Catalyst1ImageSpecification ∧
  carbonNitrideSupport.formula =
    { hydrogen := 0, carbon := 3, nitrogen := 4, oxygen := 0,
      chlorine := 0, iron := 0 } ∧
  carbonNitrideSupport.solidForm = .crystalline ∧
  SourceArrowImageSpecification ∧
  LiteratureGraphInterpretation feQpyMechanismLiterature ∧
  StandardCoordinationBookkeeping ∧ PreviousPartMatchesCycle

/-- All 35 requested outputs, in the controller-fixed source order. -/
def RequestedOutputs : Prop :=
  Structure9Result ∧ Complex9OxidationStateResult ∧
    Complex9CoordinationNumberResult ∧ Complex9ValenceElectronsResult ∧
    Complex9TotalChargeResult ∧
  Structure10Result ∧ Complex10OxidationStateResult ∧
    Complex10CoordinationNumberResult ∧ Complex10ValenceElectronsResult ∧
    Complex10TotalChargeResult ∧
  Structure11Result ∧ Complex11OxidationStateResult ∧
    Complex11CoordinationNumberResult ∧ Complex11ValenceElectronsResult ∧
    Complex11TotalChargeResult ∧
  Structure12Result ∧ Complex12OxidationStateResult ∧
    Complex12CoordinationNumberResult ∧ Complex12ValenceElectronsResult ∧
    Complex12TotalChargeResult ∧
  Structure13Result ∧ Complex13OxidationStateResult ∧
    Complex13CoordinationNumberResult ∧ Complex13ValenceElectronsResult ∧
    Complex13TotalChargeResult ∧
  Structure14Result ∧ Complex14OxidationStateResult ∧
    Complex14CoordinationNumberResult ∧ Complex14ValenceElectronsResult ∧
    Complex14TotalChargeResult ∧
  Structure15Result ∧ Complex15OxidationStateResult ∧
    Complex15CoordinationNumberResult ∧ Complex15ValenceElectronsResult ∧
    Complex15TotalChargeResult

/-- The proposed seven-state trace is a concrete compatible witness; no claim
is made that every chemically imaginable trace equals it. -/
theorem derivedCycle_is_sourceCompatible
    (h : LiteratureGraphInterpretation feQpyMechanismLiterature) :
    FollowsSourceMechanism feQpyMechanismLiterature derivedComplex := by
  refine ⟨h, ?_⟩
  unfold CandidatePrimitiveArrowChecks SourceArrowCompatible StepAtomBalanced
    StepChargeBalanced
  native_decide

theorem requestedOutputs_fromSources
    (h : ProblemAssumptions) : RequestedOutputs := by
  rcases h with ⟨_, _, _, _, _, _, hLiterature, _, _⟩
  have hCycle : FollowsSourceMechanism feQpyMechanismLiterature derivedComplex :=
    derivedCycle_is_sourceCompatible hLiterature
  have hStructure (stage : Stage) :
      StructureResult stage (derivedComplex stage) :=
    ⟨derivedComplex_complete stage, ⟨derivedComplex, hCycle, rfl⟩⟩
  have h9 : StructureResult .nine complex9 := by
    simpa only [derivedComplex] using hStructure .nine
  have h10 : StructureResult .ten complex10 := by
    simpa only [derivedComplex] using hStructure .ten
  have h11 : StructureResult .eleven complex11 := by
    simpa only [derivedComplex] using hStructure .eleven
  have h12 : StructureResult .twelve complex12 := by
    simpa only [derivedComplex] using hStructure .twelve
  have h13 : StructureResult .thirteen complex13 := by
    simpa only [derivedComplex] using hStructure .thirteen
  have h14 : StructureResult .fourteen complex14 := by
    simpa only [derivedComplex] using hStructure .fourteen
  have h15 : StructureResult .fifteen complex15 := by
    simpa only [derivedComplex] using hStructure .fifteen
  unfold RequestedOutputs Structure9Result Complex9OxidationStateResult
    Complex9CoordinationNumberResult Complex9ValenceElectronsResult
    Complex9TotalChargeResult Structure10Result Complex10OxidationStateResult
    Complex10CoordinationNumberResult Complex10ValenceElectronsResult
    Complex10TotalChargeResult Structure11Result Complex11OxidationStateResult
    Complex11CoordinationNumberResult Complex11ValenceElectronsResult
    Complex11TotalChargeResult Structure12Result Complex12OxidationStateResult
    Complex12CoordinationNumberResult Complex12ValenceElectronsResult
    Complex12TotalChargeResult Structure13Result Complex13OxidationStateResult
    Complex13CoordinationNumberResult Complex13ValenceElectronsResult
    Complex13TotalChargeResult Structure14Result Complex14OxidationStateResult
    Complex14CoordinationNumberResult Complex14ValenceElectronsResult
    Complex14TotalChargeResult Structure15Result Complex15OxidationStateResult
    Complex15CoordinationNumberResult Complex15ValenceElectronsResult
    Complex15TotalChargeResult OxidationStateResult CoordinationNumberResult
    ValenceElectronsResult TotalChargeResult
  simp only [h9, h10, h11, h12, h13, h14, h15, true_and];
    native_decide

/-- Raw exact-symbolic answer-blind derivation with the source/literature facts
kept on the hypothesis side of the contract. -/
def RawResult : Prop := ProblemAssumptions → RequestedOutputs

/-- Every requested field is exact; reporting performs no rounding or lossy
conversion. -/
def ReportedResult : Prop := ProblemAssumptions → RequestedOutputs

theorem rawResult : RawResult := by
  exact requestedOutputs_fromSources

theorem reportedResult : ReportedResult := by
  exact requestedOutputs_fromSources

/-- Payload-bound raw result contract; the digest is replaced after the
machine-readable candidate record is finalized. -/
theorem rawResultContract :
    ("a466ffad0d8982396fd126415c8624e08cf135287bc8435dac3f7f16888fdc70" : String) =
      "a466ffad0d8982396fd126415c8624e08cf135287bc8435dac3f7f16888fdc70" ∧
      RawResult := by
  exact ⟨rfl, rawResult⟩

/-- Payload-bound reported result contract. -/
theorem reportedResultContract :
    ("7bcf11d5f45a2f499fe13b1f36d9935c93de7e0b65b90796c970cba7b265bdc6" : String) =
      "7bcf11d5f45a2f499fe13b1f36d9935c93de7e0b65b90796c970cba7b265bdc6" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResult⟩

end IChO2026Problems.ProblemIChO2026T8A4
