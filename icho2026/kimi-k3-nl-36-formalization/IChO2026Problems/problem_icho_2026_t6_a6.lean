import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem.VerifiedA5

/-!
# IChO 2026, problem 6.6: structures M--R

The requested drawings are represented by finite, explicitly indexed
heavy-atom graphs.  An atom records its element, attached-hydrogen count,
formal charge, radical count, and stereochemical descriptor; an edge records
its endpoints and bond order.  In particular, none of the six output carriers
is a molecular-name string or a formula-only surrogate.

The page-4 drawing contains intermediate labels `M`, `N`, `O`, `Q`, and `R`.
There is no intermediate box `P`: the printed `P6` label belongs to the cyclic
six-porphyrin product drawn below the route.  The controller-requested
`structure_p` carrier therefore records both that source-label fact and a full
graph for the displayed P6 nanoring; it does not invent an intermediate P.

Every transformation is used only as a qualitative named transformation.  No
definition below asserts a yield, a sole product, completion, a quantitative
material balance, or the absence of omitted work-up/byproduct streams.
-/

namespace IChO2026Problems
namespace T6A6

/-! ## Explicit molecular graphs -/

/-- Elements present in the requested products.  Hydrogens are stored on their
heavy-atom sites rather than as graph vertices. -/
inductive Element where
  | carbon
  | nitrogen
  | oxygen
  | bromine
  | zinc
deriving DecidableEq, Repr

/-- The source drawing assigns no wedge/dash or E/Z stereochemistry. -/
inductive StereoDescriptor where
  | unspecified
  | rectus
  | sinister
  | entgegen
  | zusammen
deriving DecidableEq, Repr

/-- One indexed heavy-atom site. -/
structure AtomSite where
  element : Element
  hydrogens : ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereo : StereoDescriptor
deriving DecidableEq, Repr

/-- Bond orders needed for the arene, porphyrin, and alkyne drawings.
`coordinate` records each of the four N--Zn coordination edges and contributes
zero to the separate covalent-valence sum. -/
inductive BondOrder where
  | single
  | double
  | triple
  | coordinate
deriving DecidableEq, Repr

def BondOrder.covalentValence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .coordinate => 0

/-- An unordered bond between indices in `MolecularGraph.atoms`. -/
structure Bond where
  first : ℕ
  second : ℕ
  order : BondOrder
deriving DecidableEq, Repr

/-- A finite heavy-atom graph. -/
structure MolecularGraph where
  atoms : List AtomSite
  bonds : List Bond
deriving DecidableEq, Repr

def atomSite (element : Element) (hydrogens : ℕ) (formalCharge : ℤ := 0) :
    AtomSite :=
  { element := element
    hydrogens := hydrogens
    formalCharge := formalCharge
    radicalElectrons := 0
    stereo := .unspecified }

def carbon (hydrogens : ℕ) : AtomSite := atomSite .carbon hydrogens
def nitrogen (formalCharge : ℤ := 0) : AtomSite :=
  atomSite .nitrogen 0 formalCharge
def oxygen : AtomSite := atomSite .oxygen 0
def bromine : AtomSite := atomSite .bromine 0
def zincII : AtomSite := atomSite .zinc 0 2

def bond (first second : ℕ) (order : BondOrder) : Bond :=
  { first := first, second := second, order := order }

def emptyGraph : MolecularGraph := { atoms := [], bonds := [] }

def shiftBond (offset : ℕ) (b : Bond) : Bond :=
  { first := offset + b.first
    second := offset + b.second
    order := b.order }

/-- Disjoint union, with the right-hand bond indices shifted. -/
def appendGraph (left right : MolecularGraph) : MolecularGraph :=
  { atoms := left.atoms ++ right.atoms
    bonds := left.bonds ++ right.bonds.map (shiftBond left.atoms.length) }

def addBond (g : MolecularGraph) (first second : ℕ) (order : BondOrder) :
    MolecularGraph :=
  { g with bonds := g.bonds ++ [bond first second order] }

structure Fragment where
  graph : MolecularGraph
  anchor : Option ℕ

/-- Attach a fragment anchor to a pre-existing atom. -/
def attachFragment (g : MolecularGraph) (parent : ℕ) (fragment : Fragment) :
    MolecularGraph :=
  let offset := g.atoms.length
  let disjoint := appendGraph g fragment.graph
  match fragment.anchor with
  | none => disjoint
  | some anchor => addBond disjoint parent (offset + anchor) .single

/-- Replace only the implicit-hydrogen count at an atom index. -/
def setAtomHydrogens : List AtomSite → ℕ → ℕ → List AtomSite
  | [], _, _ => []
  | atom :: rest, 0, hydrogens => { atom with hydrogens := hydrogens } :: rest
  | atom :: rest, index + 1, hydrogens =>
      atom :: setAtomHydrogens rest index hydrogens

def MolecularGraph.setHydrogens (g : MolecularGraph) (index hydrogens : ℕ) :
    MolecularGraph :=
  { g with atoms := setAtomHydrogens g.atoms index hydrogens }

/-- Two bonds have the same unordered endpoint pair. -/
def SameEndpoints (a b : Bond) : Prop :=
  (a.first = b.first ∧ a.second = b.second) ∨
    (a.first = b.second ∧ a.second = b.first)

/-- All bonds are in range, loopless, and unique as unordered pairs. -/
def GraphWellFormed (g : MolecularGraph) : Prop :=
  g.bonds.Forall
      (fun b =>
        b.first < g.atoms.length ∧ b.second < g.atoms.length ∧
          b.first ≠ b.second) ∧
    g.bonds.Pairwise (fun a b => ¬ SameEndpoints a b)

def elementAt : List AtomSite → ℕ → Option Element
  | [], _ => none
  | atom :: _, 0 => some atom.element
  | _ :: rest, index + 1 => elementAt rest index

/-- Every coordinate edge has exactly one Zn endpoint and one N endpoint. -/
def CoordinateEdgesTyped (g : MolecularGraph) : Prop :=
  g.bonds.Forall fun b =>
    b.order = .coordinate →
      ((elementAt g.atoms b.first = some .zinc ∧
          elementAt g.atoms b.second = some .nitrogen) ∨
        (elementAt g.atoms b.first = some .nitrogen ∧
          elementAt g.atoms b.second = some .zinc))

def incidentCovalentValence (g : MolecularGraph) (index : ℕ) : ℕ :=
  g.bonds.foldl
    (fun total b =>
      if b.first = index ∨ b.second = index then
        total + b.order.covalentValence
      else total)
    0

def incidentCoordinateCount (g : MolecularGraph) (index : ℕ) : ℕ :=
  g.bonds.foldl
    (fun total b =>
      if (b.first = index ∨ b.second = index) ∧ b.order = .coordinate then
        total + 1
      else total)
    0

def expectedCovalentValence (atom : AtomSite) : ℕ :=
  match atom.element with
  | .carbon => 4
  | .oxygen => 2
  | .bromine => 1
  | .zinc => 0
  | .nitrogen => if atom.formalCharge = -1 then 2 else 3

/-- Ordinary covalent valence, with N--Zn coordination audited separately. -/
def CovalentValenceSatisfied (g : MolecularGraph) : Prop :=
  ∀ i : Fin g.atoms.length,
    incidentCovalentValence g i.val + (g.atoms.get i).hydrogens =
      expectedCovalentValence (g.atoms.get i)

/-- Each porphyrin nitrogen has one N--Zn edge and each Zn has four; all other
atoms have no coordinate edge.  The same predicate is vacuous for M and N. -/
def CoordinationSatisfied (g : MolecularGraph) : Prop :=
  ∀ i : Fin g.atoms.length,
    let atom := g.atoms.get i
    if atom.element = .zinc then incidentCoordinateCount g i.val = 4
    else if atom.element = .nitrogen then incidentCoordinateCount g i.val = 1
    else incidentCoordinateCount g i.val = 0

def totalFormalCharge (g : MolecularGraph) : ℤ :=
  g.atoms.foldl (fun total atom => total + atom.formalCharge) 0

/-- The complexes are overall neutral and contain no radical sites. -/
def ClosedShellNeutral (g : MolecularGraph) : Prop :=
  totalFormalCharge g = 0 ∧
    g.atoms.Forall (fun atom => atom.radicalElectrons = 0)

def NoAssignedStereochemistry (g : MolecularGraph) : Prop :=
  g.atoms.Forall (fun atom => atom.stereo = .unspecified)

/-- Element-count carrier for graph audits. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  bromine : ℕ
  zinc : ℕ
deriving DecidableEq, Repr

def countElement (g : MolecularGraph) (element : Element) : ℕ :=
  g.atoms.foldl
    (fun count atom => if atom.element = element then count + 1 else count)
    0

def countHydrogen (g : MolecularGraph) : ℕ :=
  g.atoms.foldl (fun count atom => count + atom.hydrogens) 0

def formulaOfGraph (g : MolecularGraph) : MolecularFormula :=
  { carbon := countElement g .carbon
    hydrogen := countHydrogen g
    nitrogen := countElement g .nitrogen
    oxygen := countElement g .oxygen
    bromine := countElement g .bromine
    zinc := countElement g .zinc }

def MolecularFormula.heavyAtomCount (formula : MolecularFormula) : ℕ :=
  formula.carbon + formula.nitrogen + formula.oxygen + formula.bromine +
    formula.zinc

/-- Connectivity, covalent valence, Zn coordination, charge/radical state,
stereochemical status, formula, and total atom/bond audits for one drawing. -/
def ExactStructure (g : MolecularGraph) (formula : MolecularFormula)
    (bondCount : ℕ) : Prop :=
  GraphWellFormed g ∧
    CoordinateEdgesTyped g ∧
    CovalentValenceSatisfied g ∧
    CoordinationSatisfied g ∧
    ClosedShellNeutral g ∧
    NoAssignedStereochemistry g ∧
    formulaOfGraph g = formula ∧
    g.atoms.length = formula.heavyAtomCount ∧
    g.bonds.length = bondCount

/-! ## Arenes M and N -/

/-- Substitution at one position of the six-membered arene.  `attachmentPort`
is the ipso site through which the 3,5-di-tert-butylphenyl group is attached to
a porphyrin meso carbon. -/
inductive AreneSubstituent where
  | hydrogen
  | methyl
  | tertButyl
  | aldehyde
  | attachmentPort
deriving DecidableEq, Repr

structure ArenePattern where
  sites : List AreneSubstituent
deriving DecidableEq, Repr

def substituentFragment : AreneSubstituent → Fragment
  | .hydrogen => { graph := emptyGraph, anchor := none }
  | .attachmentPort => { graph := emptyGraph, anchor := none }
  | .methyl =>
      { graph := { atoms := [carbon 3], bonds := [] }, anchor := some 0 }
  | .tertButyl =>
      { graph :=
          { atoms := [carbon 0, carbon 3, carbon 3, carbon 3]
            bonds :=
              [ bond 0 1 .single, bond 0 2 .single, bond 0 3 .single ] }
        anchor := some 0 }
  | .aldehyde =>
      { graph :=
          { atoms := [carbon 1, oxygen]
            bonds := [bond 0 1 .double] }
        anchor := some 0 }

def areneRingAtom : AreneSubstituent → AtomSite
  | .hydrogen => carbon 1
  | _ => carbon 0

/-- The fixed Kekule drawing of a six-membered arene. -/
def areneRingGraph (pattern : ArenePattern) : MolecularGraph :=
  { atoms := pattern.sites.map areneRingAtom
    bonds :=
      [ bond 0 1 .double, bond 1 2 .single, bond 2 3 .double
      , bond 3 4 .single, bond 4 5 .double, bond 5 0 .single ] }

def attachAreneSubstituents :
    List AreneSubstituent → ℕ → MolecularGraph → MolecularGraph
  | [], _, graph => graph
  | substituent :: rest, index, graph =>
      attachAreneSubstituents rest (index + 1)
        (attachFragment graph index (substituentFragment substituent))

/-- Realize all six ring sites and every non-hydrogen substituent. -/
def ArenePattern.realize (pattern : ArenePattern) : MolecularGraph :=
  attachAreneSubstituents pattern.sites 0 (areneRingGraph pattern)

def replaceAt {α : Type} : List α → ℕ → α → List α
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | head :: rest, index + 1, value =>
      head :: replaceAt rest index value

def ArenePattern.replace (pattern : ArenePattern) (index : ℕ)
    (substituent : AreneSubstituent) : ArenePattern :=
  { sites := replaceAt pattern.sites index substituent }

/-- Source reactant: toluene, with the methyl carbon at ring site 0. -/
def sourceToluene : ArenePattern :=
  { sites :=
      [.methyl, .hydrogen, .hydrogen, .hydrogen, .hydrogen, .hydrogen] }

/-- Generic graph-edit interpretation of thermodynamic twofold tert-butylation:
the two least-crowded meta sites 2 and 4 (zero-based) replace ring hydrogens. -/
def thermodynamicDiTertButylationProduct (before : ArenePattern) :
    ArenePattern :=
  (before.replace 2 .tertButyl).replace 4 .tertButyl

/-- Generic net edit for the printed NBS/peroxide--HMTA--acidic-water sequence:
a benzylic methyl substituent is converted to an aldehyde. -/
def sommeletFormylationProduct (before : ArenePattern) : ArenePattern :=
  { sites := before.sites.map fun substituent =>
      if substituent = .methyl then .aldehyde else substituent }

/-- Remove an aldehyde carbonyl from the arene descriptor after that carbon has
become a porphyrin meso carbon; its former aryl bond is the attachment port. -/
def aldehydeArylResidue (before : ArenePattern) : ArenePattern :=
  { sites := before.sites.map fun substituent =>
      if substituent = .aldehyde then .attachmentPort else substituent }

/-- M: 1-methyl-3,5-di-tert-butylbenzene. -/
def structureMPattern : ArenePattern :=
  { sites :=
      [.methyl, .hydrogen, .tertButyl, .hydrogen, .tertButyl, .hydrogen] }

/-- N: 3,5-di-tert-butylbenzaldehyde. -/
def structureNPattern : ArenePattern :=
  { sites :=
      [.aldehyde, .hydrogen, .tertButyl, .hydrogen, .tertButyl, .hydrogen] }

def structureM : MolecularGraph := structureMPattern.realize
def structureN : MolecularGraph := structureNPattern.realize

def formulaM : MolecularFormula :=
  { carbon := 15, hydrogen := 24, nitrogen := 0, oxygen := 0
    bromine := 0, zinc := 0 }

def formulaN : MolecularFormula :=
  { carbon := 15, hydrogen := 22, nitrogen := 0, oxygen := 1
    bromine := 0, zinc := 0 }

def hydrogenAt : List AtomSite → ℕ → ℕ
  | [], _ => 0
  | atom :: _, 0 => atom.hydrogens
  | _ :: rest, index + 1 => hydrogenAt rest index

def hydrogenBearingSites (g : MolecularGraph) : List ℕ :=
  (List.range g.atoms.length).filter fun index =>
    0 < hydrogenAt g.atoms index

def protonCountOnSites (g : MolecularGraph) (sites : List ℕ) : ℕ :=
  sites.foldl (fun total index => total + hydrogenAt g.atoms index) 0

/-- Explicit classes for M: tolyl CH3; the two equivalent tert-butyl groups;
the equivalent aryl H pair; and the remaining aryl H singlet. -/
def mProtonEnvironmentSites : List (List ℕ) :=
  [[6], [8, 9, 10, 12, 13, 14], [1, 5], [3]]

/-- The four classes cover every hydrogen-bearing site exactly once and carry
3, 18, 2, and 1 protons, respectively. -/
def MFourProtonEnvironments : Prop :=
  mProtonEnvironmentSites.length = 4 ∧
    mProtonEnvironmentSites.flatten.Perm (hydrogenBearingSites structureM) ∧
    mProtonEnvironmentSites.map (protonCountOnSites structureM) =
      [3, 18, 2, 1] ∧
    countHydrogen structureM = 24

/-! ## Zinc porphyrins O, Q, and R -/

/-- Substitution at one of the four porphyrin meso positions. -/
inductive MesoSubstituent where
  | hydrogen
  | aryl (pattern : ArenePattern)
  | bromine
  | ethynyl
deriving DecidableEq, Repr

/-- Meso sites are listed cyclically; opposite positions are 0/2 and 1/3. -/
structure PorphyrinPattern where
  meso0 : MesoSubstituent
  meso1 : MesoSubstituent
  meso2 : MesoSubstituent
  meso3 : MesoSubstituent
deriving DecidableEq, Repr

def aryl35DiTertButylPattern : ArenePattern :=
  { sites :=
      [.attachmentPort, .hydrogen, .tertButyl, .hydrogen, .tertButyl,
        .hydrogen] }

def mesoHydrogens : MesoSubstituent → ℕ
  | .hydrogen => 1
  | _ => 0

/-- A complete porphyrin core.  Atom indices are:
0--3 N; 4--19 the four alpha/beta carbon quartets; 20--23 meso C;
24 Zn.  N0 and N2 carry -1 and Zn carries +2, so the complex is neutral.
The listed double bonds are one explicit Kekule representative. -/
def porphyrinCore (pattern : PorphyrinPattern) : MolecularGraph :=
  { atoms :=
      [ nitrogen (-1), nitrogen, nitrogen (-1), nitrogen
      , carbon 0, carbon 1, carbon 1, carbon 0
      , carbon 0, carbon 1, carbon 1, carbon 0
      , carbon 0, carbon 1, carbon 1, carbon 0
      , carbon 0, carbon 1, carbon 1, carbon 0
      , carbon (mesoHydrogens pattern.meso0)
      , carbon (mesoHydrogens pattern.meso1)
      , carbon (mesoHydrogens pattern.meso2)
      , carbon (mesoHydrogens pattern.meso3)
      , zincII ]
    bonds :=
      [ bond 0 4 .single, bond 4 5 .double, bond 5 6 .single
      , bond 6 7 .double, bond 7 0 .single
      , bond 1 8 .single, bond 8 9 .single, bond 9 10 .double
      , bond 10 11 .single, bond 11 1 .double
      , bond 2 12 .single, bond 12 13 .single, bond 13 14 .double
      , bond 14 15 .single, bond 15 2 .single
      , bond 3 16 .double, bond 16 17 .single, bond 17 18 .double
      , bond 18 19 .single, bond 19 3 .single
      , bond 7 20 .single, bond 20 8 .double
      , bond 11 21 .single, bond 21 12 .double
      , bond 15 22 .double, bond 22 16 .single
      , bond 19 23 .double, bond 23 4 .single
      , bond 24 0 .coordinate, bond 24 1 .coordinate
      , bond 24 2 .coordinate, bond 24 3 .coordinate ] }

def mesoFragment : MesoSubstituent → Fragment
  | .hydrogen => { graph := emptyGraph, anchor := none }
  | .bromine =>
      { graph := { atoms := [bromine], bonds := [] }, anchor := some 0 }
  | .ethynyl =>
      { graph :=
          { atoms := [carbon 0, carbon 1]
            bonds := [bond 0 1 .triple] }
        anchor := some 0 }
  | .aryl pattern => { graph := pattern.realize, anchor := some 0 }

/-- Realize all four meso substituents.  Core meso indices remain 20--23. -/
def PorphyrinPattern.realize (pattern : PorphyrinPattern) : MolecularGraph :=
  let core := porphyrinCore pattern
  let with0 := attachFragment core 20 (mesoFragment pattern.meso0)
  let with1 := attachFragment with0 21 (mesoFragment pattern.meso1)
  let with2 := attachFragment with1 22 (mesoFragment pattern.meso2)
  attachFragment with2 23 (mesoFragment pattern.meso3)

/-- The two aldehyde-derived aryl groups occupy opposite meso sites, leaving
the other two meso sites as hydrogens. -/
def transA2ZincPorphyrinProduct (aldehyde : ArenePattern) :
    PorphyrinPattern :=
  let aryl := aldehydeArylResidue aldehyde
  { meso0 := .aryl aryl
    meso1 := .hydrogen
    meso2 := .aryl aryl
    meso3 := .hydrogen }

def brominateFreeMeso : MesoSubstituent → MesoSubstituent
  | .hydrogen => .bromine
  | other => other

/-- Net twofold NBS substitution of the remaining meso hydrogens. -/
def mesoDibrominationProduct (before : PorphyrinPattern) :
    PorphyrinPattern :=
  { meso0 := brominateFreeMeso before.meso0
    meso1 := brominateFreeMeso before.meso1
    meso2 := brominateFreeMeso before.meso2
    meso3 := brominateFreeMeso before.meso3 }

def ethynylateMesoBromide : MesoSubstituent → MesoSubstituent
  | .bromine => .ethynyl
  | other => other

/-- Net result of two Sonogashira substitutions with
trihexylsilylacetylene followed by fluoride desilylation. -/
def terminalDiethynylationProduct (before : PorphyrinPattern) :
    PorphyrinPattern :=
  { meso0 := ethynylateMesoBromide before.meso0
    meso1 := ethynylateMesoBromide before.meso1
    meso2 := ethynylateMesoBromide before.meso2
    meso3 := ethynylateMesoBromide before.meso3 }

/-- O: zinc(II) 5,15-bis(3,5-di-tert-butylphenyl)porphyrin, with meso H
at the other two positions. -/
def structureOPattern : PorphyrinPattern :=
  { meso0 := .aryl aryl35DiTertButylPattern
    meso1 := .hydrogen
    meso2 := .aryl aryl35DiTertButylPattern
    meso3 := .hydrogen }

/-- Q: the 10,20-dibromo derivative of O. -/
def structureQPattern : PorphyrinPattern :=
  { meso0 := .aryl aryl35DiTertButylPattern
    meso1 := .bromine
    meso2 := .aryl aryl35DiTertButylPattern
    meso3 := .bromine }

/-- R: the 10,20-diethynyl derivative, with terminal C≡CH groups. -/
def structureRPattern : PorphyrinPattern :=
  { meso0 := .aryl aryl35DiTertButylPattern
    meso1 := .ethynyl
    meso2 := .aryl aryl35DiTertButylPattern
    meso3 := .ethynyl }

def structureO : MolecularGraph := structureOPattern.realize
def structureQ : MolecularGraph := structureQPattern.realize
def structureR : MolecularGraph := structureRPattern.realize

def formulaO : MolecularFormula :=
  { carbon := 48, hydrogen := 52, nitrogen := 4, oxygen := 0
    bromine := 0, zinc := 1 }

def formulaQ : MolecularFormula :=
  { carbon := 48, hydrogen := 50, nitrogen := 4, oxygen := 0
    bromine := 2, zinc := 1 }

def formulaR : MolecularFormula :=
  { carbon := 52, hydrogen := 52, nitrogen := 4, oxygen := 0
    bromine := 0, zinc := 1 }

/-! ## The printed P6 product and the absent intermediate P -/

/-- The two terminal alkyne carbon indices in the fully realized R graph. -/
def rLeftTerminal : ℕ := 40
def rRightTerminal : ℕ := 56

structure BisTerminalAlkyneMonomer where
  graph : MolecularGraph
  leftTerminal : ℕ
  rightTerminal : ℕ
deriving DecidableEq, Repr

def rMonomer : BisTerminalAlkyneMonomer :=
  { graph := structureR
    leftTerminal := rLeftTerminal
    rightTerminal := rRightTerminal }

def dehydrogenateTermini (monomer : BisTerminalAlkyneMonomer) :
    MolecularGraph :=
  (monomer.graph.setHydrogens monomer.leftTerminal 0).setHydrogens
    monomer.rightTerminal 0

def repeatGraph : ℕ → MolecularGraph → MolecularGraph
  | 0, _ => emptyGraph
  | count + 1, graph => appendGraph (repeatGraph count graph) graph

/-- Generic cyclic oxidative homocoupling of six bis-terminal monomers. -/
def oxidativeCyclohexamerizationProduct (monomer : BisTerminalAlkyneMonomer) :
    MolecularGraph :=
  let unit := dehydrogenateTermini monomer
  let size := unit.atoms.length
  let unlinked := repeatGraph 6 unit
  let link0 := addBond unlinked monomer.rightTerminal
    (size + monomer.leftTerminal) .single
  let link1 := addBond link0 (size + monomer.rightTerminal)
    (2 * size + monomer.leftTerminal) .single
  let link2 := addBond link1 (2 * size + monomer.rightTerminal)
    (3 * size + monomer.leftTerminal) .single
  let link3 := addBond link2 (3 * size + monomer.rightTerminal)
    (4 * size + monomer.leftTerminal) .single
  let link4 := addBond link3 (4 * size + monomer.rightTerminal)
    (5 * size + monomer.leftTerminal) .single
  addBond link4 (5 * size + monomer.rightTerminal) monomer.leftTerminal .single

/-- An independently indexed expansion of the P6 repeat drawing.  Each R unit
loses its two terminal alkyne hydrogens, and the six new terminal-C--terminal-C
bonds close six butadiyne links. -/
def structureP6 : MolecularGraph :=
  let unit := dehydrogenateTermini rMonomer
  let unlinked := repeatGraph 6 unit
  let link0 := addBond unlinked 56 97 .single
  let link1 := addBond link0 113 154 .single
  let link2 := addBond link1 170 211 .single
  let link3 := addBond link2 227 268 .single
  let link4 := addBond link3 284 325 .single
  addBond link4 341 40 .single

def formulaP6 : MolecularFormula :=
  { carbon := 312, hydrogen := 300, nitrogen := 24, oxygen := 0
    bromine := 0, zinc := 6 }

/-! The P6 bond list has 402 entries.  Splitting it into six blocks keeps the
kernel reduction used for its pairwise endpoint audit small enough that no
compiler-backed decision procedure is needed. -/

private def p6BondTail0 : List Bond := structureP6.bonds
private def p6BondTail1 : List Bond := p6BondTail0.drop 67
private def p6BondTail2 : List Bond := p6BondTail1.drop 67
private def p6BondTail3 : List Bond := p6BondTail2.drop 67
private def p6BondTail4 : List Bond := p6BondTail3.drop 67
private def p6BondTail5 : List Bond := p6BondTail4.drop 67

private def p6BondChunk0 : List Bond := p6BondTail0.take 67
private def p6BondChunk1 : List Bond := p6BondTail1.take 67
private def p6BondChunk2 : List Bond := p6BondTail2.take 67
private def p6BondChunk3 : List Bond := p6BondTail3.take 67
private def p6BondChunk4 : List Bond := p6BondTail4.take 67

private def BondsSeparate (left right : List Bond) : Prop :=
  left.Forall fun a => right.Forall fun b => ¬ SameEndpoints a b

private theorem bondsSeparate_forall {left right : List Bond}
    (h : BondsSeparate left right) :
    ∀ a ∈ left, ∀ b ∈ right, ¬ SameEndpoints a b := by
  intro a ha b hb
  exact (List.forall_iff_forall_mem.mp
    ((List.forall_iff_forall_mem.mp h) a ha)) b hb

private theorem p6BondChunk0_pairwise :
    p6BondChunk0.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk1_pairwise :
    p6BondChunk1.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk2_pairwise :
    p6BondChunk2.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk3_pairwise :
    p6BondChunk3.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk4_pairwise :
    p6BondChunk4.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondTail5_pairwise :
    p6BondTail5.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  unfold SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk0_separate :
    BondsSeparate p6BondChunk0 p6BondTail1 := by
  unfold BondsSeparate SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk1_separate :
    BondsSeparate p6BondChunk1 p6BondTail2 := by
  unfold BondsSeparate SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk2_separate :
    BondsSeparate p6BondChunk2 p6BondTail3 := by
  unfold BondsSeparate SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk3_separate :
    BondsSeparate p6BondChunk3 p6BondTail4 := by
  unfold BondsSeparate SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondChunk4_separate :
    BondsSeparate p6BondChunk4 p6BondTail5 := by
  unfold BondsSeparate SameEndpoints
  set_option maxRecDepth 100000 in
    decide

private theorem p6BondTail4_pairwise :
    p6BondTail4.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  have combined := List.pairwise_append.mpr
    ⟨p6BondChunk4_pairwise, p6BondTail5_pairwise,
      bondsSeparate_forall p6BondChunk4_separate⟩
  simpa only [p6BondChunk4, p6BondTail5, List.take_append_drop] using combined

private theorem p6BondTail3_pairwise :
    p6BondTail3.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  have combined := List.pairwise_append.mpr
    ⟨p6BondChunk3_pairwise, p6BondTail4_pairwise,
      bondsSeparate_forall p6BondChunk3_separate⟩
  simpa only [p6BondChunk3, p6BondTail4, List.take_append_drop] using combined

private theorem p6BondTail2_pairwise :
    p6BondTail2.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  have combined := List.pairwise_append.mpr
    ⟨p6BondChunk2_pairwise, p6BondTail3_pairwise,
      bondsSeparate_forall p6BondChunk2_separate⟩
  simpa only [p6BondChunk2, p6BondTail3, List.take_append_drop] using combined

private theorem p6BondTail1_pairwise :
    p6BondTail1.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  have combined := List.pairwise_append.mpr
    ⟨p6BondChunk1_pairwise, p6BondTail2_pairwise,
      bondsSeparate_forall p6BondChunk1_separate⟩
  simpa only [p6BondChunk1, p6BondTail2, List.take_append_drop] using combined

private theorem p6BondTail0_pairwise :
    p6BondTail0.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  have combined := List.pairwise_append.mpr
    ⟨p6BondChunk0_pairwise, p6BondTail1_pairwise,
      bondsSeparate_forall p6BondChunk0_separate⟩
  simpa only [p6BondChunk0, p6BondTail1, List.take_append_drop] using combined

private theorem structureP6_bonds_pairwise :
    structureP6.bonds.Pairwise (fun a b => ¬ SameEndpoints a b) := by
  exact p6BondTail0_pairwise

private theorem structureP6_bonds_in_range :
    structureP6.bonds.Forall
      (fun b =>
        b.first < structureP6.atoms.length ∧
          b.second < structureP6.atoms.length ∧ b.first ≠ b.second) := by
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_coordinate_edges_typed :
    CoordinateEdgesTyped structureP6 := by
  unfold CoordinateEdgesTyped
  set_option maxRecDepth 100000 in
    decide

set_option maxHeartbeats 1000000 in
-- The explicit audit scans all 402 bonds at each of 342 atom sites.
private theorem structureP6_covalent_valence :
    CovalentValenceSatisfied structureP6 := by
  unfold CovalentValenceSatisfied
  set_option maxRecDepth 100000 in
    decide

set_option maxHeartbeats 1000000 in
-- The explicit audit scans all 402 bonds at each of 342 atom sites.
private theorem structureP6_coordination :
    CoordinationSatisfied structureP6 := by
  unfold CoordinationSatisfied
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_closed_shell_neutral :
    ClosedShellNeutral structureP6 := by
  unfold ClosedShellNeutral
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_no_assigned_stereochemistry :
    NoAssignedStereochemistry structureP6 := by
  unfold NoAssignedStereochemistry
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_formula :
    formulaOfGraph structureP6 = formulaP6 := by
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_atom_count :
    structureP6.atoms.length = formulaP6.heavyAtomCount := by
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_bond_count : structureP6.bonds.length = 402 := by
  set_option maxRecDepth 100000 in
    decide

private theorem structureP6_exact : ExactStructure structureP6 formulaP6 402 := by
  exact
    ⟨ ⟨structureP6_bonds_in_range, structureP6_bonds_pairwise⟩
    , structureP6_coordinate_edges_typed
    , structureP6_covalent_valence
    , structureP6_coordination
    , structureP6_closed_shell_neutral
    , structureP6_no_assigned_stereochemistry
    , structureP6_formula
    , structureP6_atom_count
    , structureP6_bond_count ⟩

/-- The literal intermediate letters printed above the page-4 reaction arrows. -/
inductive LetterLabel where
  | m
  | n
  | o
  | p
  | q
  | r
deriving DecidableEq, Repr

def page4IntermediateLabels : List LetterLabel := [.m, .n, .o, .q, .r]

/-- Source-label audit: no `P` box is printed, while the cyclic product is
printed as `P6`. -/
def PLabelReservation : Prop :=
  LetterLabel.p ∉ page4IntermediateLabels ∧
    oxidativeCyclohexamerizationProduct rMonomer = structureP6

/-! ## Problem-image source facts and qualitative reaction semantics -/

structure ProblemFigureRef where
  path : String
  sha256 : String
deriving DecidableEq, Repr

def page4Figure : ProblemFigureRef :=
  { path := "icho_2026_source/image/T6_page-4.png"
    sha256 := "fd4ea1325d4a9b1980cce5824fc9878e7607a8cab8572c2e5699ea0d7eab7631" }

def page3Figure : ProblemFigureRef :=
  { path := "icho_2026_source/image/T6_page-3.png"
    sha256 := "7ae1859c62e61f1da4136e4651d0b7f3f15930b9672a36cb31684f02291c34e5" }

def page2Figure : ProblemFigureRef :=
  { path := "icho_2026_source/image/T6_page-2.png"
    sha256 := "d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362" }

inductive StageUseClass where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
deriving DecidableEq, Repr

def stageUseClass : StageUseClass := .qualitativeNamedTransformOnly

inductive RouteNode where
  | sourceToluene
  | m
  | n
  | o
  | q
  | r
  | templatedP6
  | isolatedP6
deriving DecidableEq, Repr

inductive SourceLocator where
  | page4ToM
  | page4MToN
  | page4NToO
  | page4OToQ
  | page4QToR
  | page4RToTemplatedP6
  | page4TemplateRemovalToP6
deriving DecidableEq, Repr

inductive Reagent where
  | tertButylChloride
  | aluminumChloride
  | nbs
  | benzoylPeroxide
  | hmta
  | hydrochloricAcid
  | water
  | dipyrromethane
  | trifluoroaceticAcid
  | ddq
  | zincAcetate
  | palladiumZero
  | triphenylphosphine
  | copperIodide
  | trihexylsilylacetylene
  | tetrabutylammoniumFluoride
  | paraBenzoquinone
  | palladiumDichloride
  | sixfoldPyridylTemplate
  | dabco
deriving DecidableEq, Repr

structure ReagentUse where
  reagent : Reagent
  step : ℕ
  equivalents : Option ℕ
deriving DecidableEq, Repr

def reagentUse (reagent : Reagent) (step : ℕ)
    (equivalents : Option ℕ := none) : ReagentUse :=
  { reagent := reagent, step := step, equivalents := equivalents }

structure SchemeArrow where
  source : ProblemFigureRef
  fromNode : RouteNode
  toNode : RouteNode
  locator : SourceLocator
  reagents : List ReagentUse
deriving DecidableEq, Repr

def arrowToM : SchemeArrow :=
  { source := page4Figure
    fromNode := .sourceToluene
    toNode := .m
    locator := .page4ToM
    reagents :=
      [reagentUse .tertButylChloride 1 (some 2), reagentUse .aluminumChloride 1] }

def arrowToN : SchemeArrow :=
  { source := page4Figure
    fromNode := .m
    toNode := .n
    locator := .page4MToN
    reagents :=
      [ reagentUse .nbs 1, reagentUse .benzoylPeroxide 1
      , reagentUse .hmta 2, reagentUse .hydrochloricAcid 3
      , reagentUse .water 3 ] }

def arrowToO : SchemeArrow :=
  { source := page4Figure
    fromNode := .n
    toNode := .o
    locator := .page4NToO
    reagents :=
      [ reagentUse .dipyrromethane 1, reagentUse .trifluoroaceticAcid 1
      , reagentUse .ddq 2, reagentUse .zincAcetate 3 ] }

def arrowToQ : SchemeArrow :=
  { source := page4Figure
    fromNode := .o
    toNode := .q
    locator := .page4OToQ
    reagents := [reagentUse .nbs 1] }

def arrowToR : SchemeArrow :=
  { source := page4Figure
    fromNode := .q
    toNode := .r
    locator := .page4QToR
    reagents :=
      [ reagentUse .palladiumZero 1, reagentUse .triphenylphosphine 1
      , reagentUse .copperIodide 1, reagentUse .trihexylsilylacetylene 1
      , reagentUse .tetrabutylammoniumFluoride 2 ] }

def arrowToTemplatedP6 : SchemeArrow :=
  { source := page4Figure
    fromNode := .r
    toNode := .templatedP6
    locator := .page4RToTemplatedP6
    reagents :=
      [ reagentUse .paraBenzoquinone 1, reagentUse .palladiumDichloride 1
      , reagentUse .triphenylphosphine 1, reagentUse .copperIodide 1
      , reagentUse .sixfoldPyridylTemplate 1 ] }

def arrowToIsolatedP6 : SchemeArrow :=
  { source := page4Figure
    fromNode := .templatedP6
    toNode := .isolatedP6
    locator := .page4TemplateRemovalToP6
    reagents := [reagentUse .dabco 1] }

def allSchemeArrows : List SchemeArrow :=
  [arrowToM, arrowToN, arrowToO, arrowToQ, arrowToR,
    arrowToTemplatedP6, arrowToIsolatedP6]

def HasReagent (arrow : SchemeArrow) (use : ReagentUse) : Prop :=
  use ∈ arrow.reagents

/-! The following public source is used only to scope the qualitative reaction
bridge.  Its bibliographic metadata was independently checked through Crossref
and PubMed (PMID 17318935); no olympiad answer or marking material was queried. -/

structure LiteratureSource where
  title : String
  doi : String
  stableUrl : String
  locator : String
deriving DecidableEq, Repr

def hoffmannPorphyrinNanoringSource : LiteratureSource :=
  { title := "Template-directed synthesis of a pi-conjugated porphyrin nanoring"
    doi := "10.1002/anie.200604601"
    stableUrl := "https://doi.org/10.1002/anie.200604601"
    locator :=
      "Angew. Chem. Int. Ed. 46 (2007), 3122-3125 and associated synthetic Supporting Information" }

inductive QualitativeRule where
  | thermodynamicDiTertButylation
  | benzylicSommeletFormylation
  | transA2PorphyrinAssemblyAndZincation
  | freeMesoDibromination
  | sonogashiraThenDesilylation
  | templateDirectedOxidativeCyclization
deriving DecidableEq, Repr

structure ReactionRuleCitation where
  source : LiteratureSource
  rule : QualitativeRule
  locator : String
  scopedClaim : String
  applicability : List String
  exclusions : List String
deriving DecidableEq, Repr

/-- Route-local literature scopes.  These authorize only compatibility of the
explicit page-4 substrates with the displayed net graph edits. -/
def reactionRuleCitation : QualitativeRule → ReactionRuleCitation
  | .thermodynamicDiTertButylation =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .thermodynamicDiTertButylation
        locator :=
          "starting-material preparation for the " ++
            "3,5-di-tert-butylphenyl porphyrin monomer"
        scopedClaim :=
          "Under the depicted reversible AlCl3/t-BuCl preparation, the " ++
            "thermodynamic ditert-butyltoluene used by this route has the " ++
            "1,3,5 substitution pattern."
        applicability :=
          ["toluene substrate", "two equivalents tert-butyl chloride",
           "aluminum chloride", "thermodynamic-product instruction"]
        exclusions := ["no yield claim", "no general regioselectivity theorem"] }
  | .benzylicSommeletFormylation =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .benzylicSommeletFormylation
        locator := "preparation of the 3,5-di-tert-butylbenzaldehyde building block"
        scopedClaim :=
          "The displayed NBS/peroxide then HMTA/acidic-water sequence changes " ++
            "the route's benzylic methyl group to an aldehyde while retaining " ++
            "both tert-butyl groups."
        applicability :=
          ["route-specific ditert-butyltoluene", "NBS and benzoyl peroxide",
           "HMTA", "HCl/water work-up"]
        exclusions := ["no yield claim", "no claim for unrelated benzylic substrates"] }
  | .transA2PorphyrinAssemblyAndZincation =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .transA2PorphyrinAssemblyAndZincation
        locator :=
          "porphyrin monomer synthesis; aldehyde/dipyrromethane condensation " ++
            "and zinc insertion"
        scopedClaim :=
          "Two route aldehyde residues and two dipyrromethane residues give " ++
            "the trans-A2 porphyrin skeleton; DDQ oxidation and Zn(OAc)2 give " ++
            "its neutral zinc complex."
        applicability :=
          ["3,5-di-tert-butylbenzaldehyde", "dipyrromethane", "CF3COOH",
           "DDQ", "Zn(OAc)2", "same route skeleton"]
        exclusions := ["no yield claim", "no exhaustive porphyrin-condensation law"] }
  | .freeMesoDibromination =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .freeMesoDibromination
        locator := "dibromination of the trans-A2 zinc porphyrin monomer"
        scopedClaim :=
          "NBS replaces the two remaining meso hydrogens of this trans-A2 " ++
            "zinc porphyrin by bromine."
        applicability :=
          ["two free meso-H sites", "route-specific trans-A2 zinc porphyrin",
           "NBS"]
        exclusions := ["no yield claim", "aryl substituents retained"] }
  | .sonogashiraThenDesilylation =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .sonogashiraThenDesilylation
        locator := "preparation of the bis-terminal-ethynyl zinc porphyrin monomer"
        scopedClaim :=
          "Two Sonogashira substitutions install trihexylsilyl-protected " ++
            "ethynyl groups at the brominated meso sites, and fluoride " ++
            "work-up gives two terminal ethynyl groups."
        applicability :=
          ["route-specific meso dibromide", "Pd(0)/PPh3/CuI",
           "trihexylsilylacetylene", "n-Bu4NF"]
        exclusions := ["no yield claim", "no catalyst-mechanism claim"] }
  | .templateDirectedOxidativeCyclization =>
      { source := hoffmannPorphyrinNanoringSource
        rule := .templateDirectedOxidativeCyclization
        locator := "nanoring-forming scheme in the main article"
        scopedClaim :=
          "Template-directed oxidative homocoupling of six bis-terminal-ethynyl " ++
            "zinc porphyrins forms the displayed cyclic P6 butadiyne-linked " ++
            "nanoring."
        applicability :=
          ["six route-specific bis-terminal-ethynyl monomers",
           "sixfold pyridyl template", "oxidative palladium/copper conditions"]
        exclusions :=
          [ "no yield claim", "no sole-product claim"
          , "template guest omitted only after the displayed removal step" ] }

def RuleCitationBound (rule : QualitativeRule) : Prop :=
  let citation := reactionRuleCitation rule
  citation.source = hoffmannPorphyrinNanoringSource ∧
    citation.rule = rule ∧ citation.locator ≠ "" ∧ citation.scopedClaim ≠ "" ∧
    citation.applicability ≠ []

theorem all_rule_citations_bound (rule : QualitativeRule) :
    RuleCitationBound rule := by
  cases rule <;> unfold RuleCitationBound reactionRuleCitation <;> decide

inductive StructureDescriptor where
  | arene (pattern : ArenePattern)
  | porphyrin (pattern : PorphyrinPattern)
  | explicitGraph (graph : MolecularGraph)
deriving DecidableEq, Repr

def ThermodynamicAlkylationContext (arrow : SchemeArrow)
    (before : ArenePattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4ToM ∧
    HasReagent arrow (reagentUse .tertButylChloride 1 (some 2)) ∧
    HasReagent arrow (reagentUse .aluminumChloride 1) ∧
    before = sourceToluene

def SommeletContext (arrow : SchemeArrow) (before : ArenePattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4MToN ∧
    HasReagent arrow (reagentUse .nbs 1) ∧
    HasReagent arrow (reagentUse .benzoylPeroxide 1) ∧
    HasReagent arrow (reagentUse .hmta 2) ∧
    HasReagent arrow (reagentUse .hydrochloricAcid 3) ∧
    HasReagent arrow (reagentUse .water 3) ∧
    before.sites.count .methyl = 1

def PorphyrinAssemblyContext (arrow : SchemeArrow)
    (before : ArenePattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4NToO ∧
    HasReagent arrow (reagentUse .dipyrromethane 1) ∧
    HasReagent arrow (reagentUse .trifluoroaceticAcid 1) ∧
    HasReagent arrow (reagentUse .ddq 2) ∧
    HasReagent arrow (reagentUse .zincAcetate 3) ∧
    before.sites.count .aldehyde = 1

def MesoBrominationContext (arrow : SchemeArrow)
    (before : PorphyrinPattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4OToQ ∧
    HasReagent arrow (reagentUse .nbs 1) ∧
    [before.meso0, before.meso1, before.meso2, before.meso3].count
      .hydrogen = 2

def TerminalEthynylationContext (arrow : SchemeArrow)
    (before : PorphyrinPattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4QToR ∧
    HasReagent arrow (reagentUse .palladiumZero 1) ∧
    HasReagent arrow (reagentUse .triphenylphosphine 1) ∧
    HasReagent arrow (reagentUse .copperIodide 1) ∧
    HasReagent arrow (reagentUse .trihexylsilylacetylene 1) ∧
    HasReagent arrow (reagentUse .tetrabutylammoniumFluoride 2) ∧
    [before.meso0, before.meso1, before.meso2, before.meso3].count
      .bromine = 2

def P6CyclizationContext (arrow : SchemeArrow)
    (before : PorphyrinPattern) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page4RToTemplatedP6 ∧
    HasReagent arrow (reagentUse .paraBenzoquinone 1) ∧
    HasReagent arrow (reagentUse .palladiumDichloride 1) ∧
    HasReagent arrow (reagentUse .triphenylphosphine 1) ∧
    HasReagent arrow (reagentUse .copperIodide 1) ∧
    HasReagent arrow (reagentUse .sixfoldPyridylTemplate 1) ∧
    before.meso0 = .aryl aryl35DiTertButylPattern ∧
    before.meso1 = .ethynyl ∧
    before.meso2 = .aryl aryl35DiTertButylPattern ∧
    before.meso3 = .ethynyl

/-- Source-scoped, non-exclusive qualitative reaction semantics.  Constructors
take only source substrate/reagent contexts and compute their products; no
constructor takes a requested candidate as a premise. -/
inductive QualitativeReactionStep :
    SchemeArrow → StructureDescriptor → StructureDescriptor → Prop where
  | thermodynamicAlkylation {arrow before}
      (authority : RuleCitationBound .thermodynamicDiTertButylation)
      (context : ThermodynamicAlkylationContext arrow before) :
      QualitativeReactionStep arrow (.arene before)
        (.arene (thermodynamicDiTertButylationProduct before))
  | sommeletFormylation {arrow before}
      (authority : RuleCitationBound .benzylicSommeletFormylation)
      (context : SommeletContext arrow before) :
      QualitativeReactionStep arrow (.arene before)
        (.arene (sommeletFormylationProduct before))
  | porphyrinAssembly {arrow before}
      (authority : RuleCitationBound .transA2PorphyrinAssemblyAndZincation)
      (context : PorphyrinAssemblyContext arrow before) :
      QualitativeReactionStep arrow (.arene before)
        (.porphyrin (transA2ZincPorphyrinProduct before))
  | mesoBromination {arrow before}
      (authority : RuleCitationBound .freeMesoDibromination)
      (context : MesoBrominationContext arrow before) :
      QualitativeReactionStep arrow (.porphyrin before)
        (.porphyrin (mesoDibrominationProduct before))
  | terminalEthynylation {arrow before}
      (authority : RuleCitationBound .sonogashiraThenDesilylation)
      (context : TerminalEthynylationContext arrow before) :
      QualitativeReactionStep arrow (.porphyrin before)
        (.porphyrin (terminalDiethynylationProduct before))
  | p6Cyclization {arrow before}
      (authority : RuleCitationBound .templateDirectedOxidativeCyclization)
      (context : P6CyclizationContext arrow before) :
      QualitativeReactionStep arrow (.porphyrin before)
        (.explicitGraph (oxidativeCyclohexamerizationProduct
          { graph := before.realize
            leftTerminal := rLeftTerminal
            rightTerminal := rRightTerminal }))

/-- Complete page/image and route-domain audit.  Page 3 is the protected A5
route and page 2 supplies earlier shared context; neither is treated as a
chemical cause of the independent page-4 A6 route. -/
def StagedSpeciesDomain : Prop :=
  [page4Figure, page3Figure, page2Figure].length = 3 ∧
    stageUseClass = .qualitativeNamedTransformOnly ∧
    allSchemeArrows.map (fun arrow => (arrow.fromNode, arrow.toNode)) =
      [ (.sourceToluene, .m), (.m, .n), (.n, .o), (.o, .q), (.q, .r)
      , (.r, .templatedP6), (.templatedP6, .isolatedP6) ] ∧
    allSchemeArrows.Forall (fun arrow => arrow.source = page4Figure) ∧
    (∀ rule : QualitativeRule, RuleCitationBound rule)

/-! ## Requested output specifications -/

/-- Requested output `structure_m`. -/
def StructureMResult : Prop :=
  QualitativeReactionStep arrowToM (.arene sourceToluene)
      (.arene structureMPattern) ∧
    ExactStructure structureM formulaM 15 ∧
    MFourProtonEnvironments

/-- Requested output `structure_n`. -/
def StructureNResult : Prop :=
  QualitativeReactionStep arrowToN (.arene structureMPattern)
      (.arene structureNPattern) ∧
    ExactStructure structureN formulaN 16

/-- Requested output `structure_o`. -/
def StructureOResult : Prop :=
  QualitativeReactionStep arrowToO (.arene structureNPattern)
      (.porphyrin structureOPattern) ∧
    ExactStructure structureO formulaO 62

/-- Controller slot `structure_p`: the source has no intermediate P; this
carrier instead verifies the printed P6 reservation and its expanded graph. -/
def StructurePResult : Prop :=
  PLabelReservation ∧
    QualitativeReactionStep arrowToTemplatedP6 (.porphyrin structureRPattern)
      (.explicitGraph structureP6) ∧
    ExactStructure structureP6 formulaP6 402

/-- Requested output `structure_q`. -/
def StructureQResult : Prop :=
  QualitativeReactionStep arrowToQ (.porphyrin structureOPattern)
      (.porphyrin structureQPattern) ∧
    ExactStructure structureQ formulaQ 64

/-- Requested output `structure_r`. -/
def StructureRResult : Prop :=
  QualitativeReactionStep arrowToR (.porphyrin structureQPattern)
      (.porphyrin structureRPattern) ∧
    ExactStructure structureR formulaR 66

theorem structure_m : StructureMResult := by
  refine ⟨?_, ?_, ?_⟩
  · have context : ThermodynamicAlkylationContext arrowToM sourceToluene := by
      unfold ThermodynamicAlkylationContext HasReagent stageUseClass arrowToM
      decide
    rw [show structureMPattern =
        thermodynamicDiTertButylationProduct sourceToluene by decide]
    exact QualitativeReactionStep.thermodynamicAlkylation
      (all_rule_citations_bound .thermodynamicDiTertButylation) context
  · unfold ExactStructure GraphWellFormed CoordinateEdgesTyped
      CovalentValenceSatisfied CoordinationSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide
  · unfold MFourProtonEnvironments
    decide

theorem structure_n : StructureNResult := by
  constructor
  · have context : SommeletContext arrowToN structureMPattern := by
      unfold SommeletContext HasReagent stageUseClass arrowToN
      decide
    rw [show structureNPattern =
        sommeletFormylationProduct structureMPattern by decide]
    exact QualitativeReactionStep.sommeletFormylation
      (all_rule_citations_bound .benzylicSommeletFormylation) context
  · unfold ExactStructure GraphWellFormed CoordinateEdgesTyped
      CovalentValenceSatisfied CoordinationSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

theorem structure_o : StructureOResult := by
  constructor
  · have context : PorphyrinAssemblyContext arrowToO structureNPattern := by
      unfold PorphyrinAssemblyContext HasReagent stageUseClass arrowToO
      decide
    rw [show structureOPattern =
        transA2ZincPorphyrinProduct structureNPattern by decide]
    exact QualitativeReactionStep.porphyrinAssembly
      (all_rule_citations_bound .transA2PorphyrinAssemblyAndZincation) context
  · unfold ExactStructure GraphWellFormed CoordinateEdgesTyped
      CovalentValenceSatisfied CoordinationSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

theorem structure_p : StructurePResult := by
  have labelAudit : PLabelReservation := by
    unfold PLabelReservation
    constructor
    · decide
    · rfl
  refine ⟨labelAudit, ?_, ?_⟩
  · have context : P6CyclizationContext arrowToTemplatedP6 structureRPattern := by
      unfold P6CyclizationContext HasReagent stageUseClass arrowToTemplatedP6
      decide
    rw [← labelAudit.2]
    simpa [rMonomer, structureR] using
      QualitativeReactionStep.p6Cyclization
        (all_rule_citations_bound .templateDirectedOxidativeCyclization) context
  · exact structureP6_exact

theorem structure_q : StructureQResult := by
  constructor
  · have context : MesoBrominationContext arrowToQ structureOPattern := by
      unfold MesoBrominationContext HasReagent stageUseClass arrowToQ
      decide
    rw [show structureQPattern =
        mesoDibrominationProduct structureOPattern by decide]
    exact QualitativeReactionStep.mesoBromination
      (all_rule_citations_bound .freeMesoDibromination) context
  · unfold ExactStructure GraphWellFormed CoordinateEdgesTyped
      CovalentValenceSatisfied CoordinationSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

theorem structure_r : StructureRResult := by
  constructor
  · have context : TerminalEthynylationContext arrowToR structureQPattern := by
      unfold TerminalEthynylationContext HasReagent stageUseClass arrowToR
      decide
    rw [show structureRPattern =
        terminalDiethynylationProduct structureQPattern by decide]
    exact QualitativeReactionStep.terminalEthynylation
      (all_rule_citations_bound .sonogashiraThenDesilylation) context
  · unfold ExactStructure GraphWellFormed CoordinateEdgesTyped
      CovalentValenceSatisfied CoordinationSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Current-part result, ordered exactly as the controller output inventory:
M, N, O, P, Q, R. -/
def CurrentStructuresMToRResult : Prop :=
  StagedSpeciesDomain ∧
    StructureMResult ∧ StructureNResult ∧ StructureOResult ∧
      StructurePResult ∧ StructureQResult ∧ StructureRResult

theorem current_structures_m_to_r : CurrentStructuresMToRResult := by
  refine ⟨?_, structure_m, structure_n, structure_o, structure_p, structure_q,
    structure_r⟩
  unfold StagedSpeciesDomain
  refine ⟨by decide, rfl, ?_, ?_, all_rule_citations_bound⟩
  · decide
  · decide

/-! The verified A5 conjunct is a user-required validation prerequisite only;
it does not assert a causal connection between the A5 and A6 syntheses. -/

/-- Actual combined final result.  The first conjunct is the protected,
hash-bound same-run A5 theorem's exact result type. -/
def StructuresMToRResult : Prop :=
  T6A5.StructuresFToLResult ∧ CurrentStructuresMToRResult

/-- Main combined theorem.  The prerequisite is constructed from the closed
imported theorem, never from a hypothesis or local axiom. -/
theorem structures_m_to_r : StructuresMToRResult := by
  exact ⟨T6A5.structures_f_to_l, current_structures_m_to_r⟩

/-! ## Raw and exact-symbolic reported result carriers -/

def StructuresMToRRawResult : Prop :=
  T6A5.StructuresFToLResult ∧ CurrentStructuresMToRResult

def StructuresMToRReportedResult : Prop :=
  T6A5.StructuresFToLResult ∧ CurrentStructuresMToRResult

/-- Final raw result with actual imported A5 proof use. -/
theorem structures_m_to_r_raw_result : StructuresMToRRawResult := by
  exact ⟨T6A5.structures_f_to_l, current_structures_m_to_r⟩

/-- Exact-symbolic reporting changes no structure; it again constructs the
required A5 conjunct from the protected closed theorem. -/
theorem structures_m_to_r_reported_result : StructuresMToRReportedResult := by
  exact ⟨T6A5.structures_f_to_l, current_structures_m_to_r⟩

end T6A6
end IChO2026Problems
