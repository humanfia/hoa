import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem 6.5: structures F--L

The problem asks for drawings, so a molecular structure is represented below by
an explicit heavy-atom graph.  Every heavy-atom site stores its element,
attached-hydrogen multiplicity, formal charge, radical count, and stereochemical
status.  Every bond is an unordered pair of atom indices carrying a bond order.
Thus the output is not a molecular-name string or a formula-only surrogate.

The source drawing assigns no wedges, dashes, or E/Z labels.  Consequently each
site carries `StereoDescriptor.unspecified`; no stereochemical choice is silently
invented.
-/

namespace IChO2026Problems
namespace T6A5

/-- Elements needed by the drawn substrates and products.  Hydrogens are bound
to their heavy-atom sites through `AtomSite.hydrogens`. -/
inductive Element where
  | carbon
  | oxygen
  | silicon
  | bromine
  | lithium
deriving DecidableEq, Repr

/-- The problem figure gives no stereochemical annotations. -/
inductive StereoDescriptor where
  | unspecified
  | rectus
  | sinister
  | entgegen
  | zusammen
deriving DecidableEq, Repr

/-- One explicitly indexed heavy-atom site. -/
structure AtomSite where
  element : Element
  hydrogens : ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereo : StereoDescriptor
deriving DecidableEq, Repr

/-- Covalent bond orders occurring in the scheme. -/
inductive BondOrder where
  | single
  | double
  | triple
deriving DecidableEq, Repr

def BondOrder.val : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

/-- An unordered heavy-atom bond.  Its endpoints index `MolecularGraph.atoms`. -/
structure Bond where
  first : ℕ
  second : ℕ
  order : BondOrder
deriving DecidableEq, Repr

/-- A finite molecular graph with explicit atom and bond inventories. -/
structure MolecularGraph where
  atoms : List AtomSite
  bonds : List Bond
deriving DecidableEq, Repr

def atomSite (element : Element) (hydrogens : ℕ) : AtomSite :=
  { element := element
    hydrogens := hydrogens
    formalCharge := 0
    radicalElectrons := 0
    stereo := .unspecified }

def carbon (hydrogens : ℕ) : AtomSite := atomSite .carbon hydrogens
def oxygen (hydrogens : ℕ) : AtomSite := atomSite .oxygen hydrogens
def silicon : AtomSite := atomSite .silicon 0
def bromine : AtomSite := atomSite .bromine 0
def lithium : AtomSite := atomSite .lithium 0

def bond (first second : ℕ) (order : BondOrder) : Bond :=
  { first := first, second := second, order := order }

/-- Shift a bond when a graph is appended after `offset` atoms. -/
def shiftBond (offset : ℕ) (b : Bond) : Bond :=
  { first := offset + b.first
    second := offset + b.second
    order := b.order }

/-- Disjoint union of two indexed molecular graphs. -/
def appendGraph (left right : MolecularGraph) : MolecularGraph :=
  { atoms := left.atoms ++ right.atoms
    bonds := left.bonds ++ right.bonds.map (shiftBond left.atoms.length) }

/-- Add a bond between two already indexed atoms. -/
def addBond (g : MolecularGraph) (first second : ℕ) (order : BondOrder) :
    MolecularGraph :=
  { g with bonds := g.bonds ++ [bond first second order] }

/-- Two bonds have the same unordered pair of endpoints. -/
def SameEndpoints (a b : Bond) : Prop :=
  (a.first = b.first ∧ a.second = b.second) ∨
    (a.first = b.second ∧ a.second = b.first)

/-- Every edge is in range, has distinct endpoints, and occurs only once. -/
def GraphWellFormed (g : MolecularGraph) : Prop :=
  g.bonds.Forall
      (fun b =>
        b.first < g.atoms.length ∧
        b.second < g.atoms.length ∧
        b.first ≠ b.second) ∧
    g.bonds.Pairwise (fun a b => ¬ SameEndpoints a b)

def incidentBondOrder (g : MolecularGraph) (index : ℕ) : ℕ :=
  g.bonds.foldl
    (fun total b =>
      if b.first = index ∨ b.second = index then total + b.order.val else total)
    0

def expectedValence : Element → ℕ
  | .carbon => 4
  | .oxygen => 2
  | .silicon => 4
  | .bromine => 1
  | .lithium => 1

/-- Ordinary valence check for every explicitly represented atom. -/
def ValenceSatisfied (g : MolecularGraph) : Prop :=
  ∀ i : Fin g.atoms.length,
    incidentBondOrder g i.val + (g.atoms.get i).hydrogens =
      expectedValence (g.atoms.get i).element

/-- None of the requested intermediates is ionic or radical. -/
def ClosedShellNeutral (g : MolecularGraph) : Prop :=
  g.atoms.Forall (fun a => a.formalCharge = 0 ∧ a.radicalElectrons = 0)

/-- The source does not assign a stereochemical descriptor at any site. -/
def NoAssignedStereochemistry (g : MolecularGraph) : Prop :=
  g.atoms.Forall (fun a => a.stereo = .unspecified)

/-- Element-count carrier used to audit a fully realized graph. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  bromine : ℕ
  oxygen : ℕ
  silicon : ℕ
  lithium : ℕ
deriving DecidableEq, Repr

def countElement (g : MolecularGraph) (element : Element) : ℕ :=
  g.atoms.foldl
    (fun count site => if site.element = element then count + 1 else count)
    0

def countHydrogen (g : MolecularGraph) : ℕ :=
  g.atoms.foldl (fun count site => count + site.hydrogens) 0

def formulaOfGraph (g : MolecularGraph) : MolecularFormula :=
  { carbon := countElement g .carbon
    hydrogen := countHydrogen g
    bromine := countElement g .bromine
    oxygen := countElement g .oxygen
    silicon := countElement g .silicon
    lithium := countElement g .lithium }

def MolecularFormula.heavyAtomCount (f : MolecularFormula) : ℕ :=
  f.carbon + f.bromine + f.oxygen + f.silicon + f.lithium

/-- A fragment has para attachment ports when those ports remain available. -/
structure Fragment where
  graph : MolecularGraph
  leftPort : Option ℕ
  rightPort : Option ℕ

def shiftPort (offset : ℕ) (port : Option ℕ) : Option ℕ :=
  port.map (fun index => offset + index)

/-- Join the right para port of one fragment to the left para port of another. -/
def appendFragments (left right : Fragment) : Fragment :=
  let offset := left.graph.atoms.length
  let disjoint := appendGraph left.graph right.graph
  let joined :=
    match left.rightPort, right.leftPort with
    | some a, some b => addBond disjoint a (offset + b) .single
    | _, _ => disjoint
  { graph := joined
    leftPort := left.leftPort
    rightPort := shiftPort offset right.rightPort }

def emptyFragment : Fragment :=
  { graph := { atoms := [], bonds := [] }, leftPort := none, rightPort := none }

/-- A para-connected phenylene, with Kekule bond orders fixed only to make the
connectivity and valence completely explicit. -/
def phenyleneFragment : Fragment :=
  { graph :=
      { atoms := [carbon 0, carbon 1, carbon 1, carbon 0, carbon 1, carbon 1]
        bonds :=
          [ bond 0 1 .double, bond 1 2 .single, bond 2 3 .double
          , bond 3 4 .single, bond 4 5 .double, bond 5 0 .single ] }
    leftPort := some 0
    rightPort := some 3 }

/-- A 1,4-diarylcyclohexa-2,5-diene-1,4-diol (`D_H`). -/
def diolMaskedRingFragment : Fragment :=
  { graph :=
      { atoms :=
          [ carbon 0, carbon 1, carbon 1, carbon 0, carbon 1, carbon 1
          , oxygen 1, oxygen 1 ]
        bonds :=
          [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
          , bond 3 4 .single, bond 4 5 .double, bond 5 0 .single
          , bond 0 6 .single, bond 3 7 .single ] }
    leftPort := some 0
    rightPort := some 3 }

/-- The same masked ring with both hydroxyls protected as O-SiEt3 (`D_TES`).
Indices 8--14 and 15--21 are the two complete triethylsilyl groups. -/
def tesMaskedRingFragment : Fragment :=
  { graph :=
      { atoms :=
          [ carbon 0, carbon 1, carbon 1, carbon 0, carbon 1, carbon 1
          , oxygen 0, oxygen 0
          , silicon, carbon 2, carbon 3, carbon 2, carbon 3, carbon 2, carbon 3
          , silicon, carbon 2, carbon 3, carbon 2, carbon 3, carbon 2, carbon 3 ]
        bonds :=
          [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
          , bond 3 4 .single, bond 4 5 .double, bond 5 0 .single
          , bond 0 6 .single, bond 3 7 .single
          , bond 6 8 .single, bond 8 9 .single, bond 9 10 .single
          , bond 8 11 .single, bond 11 12 .single
          , bond 8 13 .single, bond 13 14 .single
          , bond 7 15 .single, bond 15 16 .single, bond 16 17 .single
          , bond 15 18 .single, bond 18 19 .single
          , bond 15 20 .single, bond 20 21 .single ] }
    leftPort := some 0
    rightPort := some 3 }

/-- A terminal para-quinol.  Carbon 0 is attached to the preceding ring and
bears OH; carbon 3 is the carbonyl carbon and therefore has no right port. -/
def quinolFragment : Fragment :=
  { graph :=
      { atoms :=
          [ carbon 0, carbon 1, carbon 1, carbon 0, carbon 1, carbon 1
          , oxygen 1, oxygen 0 ]
        bonds :=
          [ bond 0 1 .single, bond 1 2 .double, bond 2 3 .single
          , bond 3 4 .single, bond 4 5 .double, bond 5 0 .single
          , bond 0 6 .single, bond 3 7 .double ] }
    leftPort := some 0
    rightPort := none }

inductive HydroxyProtection where
  | free
  | triethylsilyl
deriving DecidableEq, Repr

/-- Ring-level source notation whose interpretation above is a full graph. -/
inductive RingKind where
  | phenylene
  | maskedDiene (protection : HydroxyProtection)
  | quinol
deriving DecidableEq, Repr

def ringFragment : RingKind → Fragment
  | .phenylene => phenyleneFragment
  | .maskedDiene .free => diolMaskedRingFragment
  | .maskedDiene .triethylsilyl => tesMaskedRingFragment
  | .quinol => quinolFragment

inductive EndCap where
  | none
  | bromine
  | hydroxy
  | tertButyldimethylsilyloxy
  | lithium
deriving DecidableEq, Repr

structure CapFragment where
  graph : MolecularGraph
  anchor : Option ℕ

/-- Explicit cap graphs.  The TBS cap contains O-SiMe2-C(CH3)3 in full. -/
def capFragment : EndCap → CapFragment
  | .none => { graph := { atoms := [], bonds := [] }, anchor := none }
  | .bromine =>
      { graph := { atoms := [bromine], bonds := [] }, anchor := some 0 }
  | .hydroxy =>
      { graph := { atoms := [oxygen 1], bonds := [] }, anchor := some 0 }
  | .lithium =>
      { graph := { atoms := [lithium], bonds := [] }, anchor := some 0 }
  | .tertButyldimethylsilyloxy =>
      { graph :=
          { atoms :=
              [ oxygen 0, silicon, carbon 3, carbon 3
              , carbon 0, carbon 3, carbon 3, carbon 3 ]
            bonds :=
              [ bond 0 1 .single, bond 1 2 .single, bond 1 3 .single
              , bond 1 4 .single, bond 4 5 .single, bond 4 6 .single
              , bond 4 7 .single ] }
        anchor := some 0 }

def attachCap (g : MolecularGraph) (port : Option ℕ) (cap : EndCap) :
    MolecularGraph :=
  let capGraph := capFragment cap
  let offset := g.atoms.length
  let disjoint := appendGraph g capGraph.graph
  match port, capGraph.anchor with
  | some a, some b => addBond disjoint a (offset + b) .single
  | _, _ => disjoint

def assembleRings : List RingKind → Fragment
  | [] => emptyFragment
  | first :: rest =>
      rest.foldl
        (fun assembled next => appendFragments assembled (ringFragment next))
        (ringFragment first)

/-- Complete ring-chain description.  In a cyclic product the two para ports
are joined after both bromine caps have been removed. -/
structure NanoStructure where
  rings : List RingKind
  leftCap : EndCap
  rightCap : EndCap
  cyclic : Bool
deriving DecidableEq, Repr

/-- Interpret the compact ring sequence as the full atom-and-bond graph. -/
def NanoStructure.realize (s : NanoStructure) : MolecularGraph :=
  let core := assembleRings s.rings
  let withLeft := attachCap core.graph core.leftPort s.leftCap
  let withBoth := attachCap withLeft core.rightPort s.rightCap
  if s.cyclic then
    match core.leftPort, core.rightPort with
    | some left, some right => addBond withBoth left right .single
    | _, _ => withBoth
  else
    withBoth

/-- Formula, atom-count, connectivity, valence, charge/radical, and source-level
stereochemical checks for a proposed drawing. -/
def ExactStructure (s : NanoStructure) (formula : MolecularFormula)
    (bondCount : ℕ) : Prop :=
  let graph := s.realize
  GraphWellFormed graph ∧
    ValenceSatisfied graph ∧
    ClosedShellNeutral graph ∧
    NoAssignedStereochemistry graph ∧
    formulaOfGraph graph = formula ∧
    graph.atoms.length = formula.heavyAtomCount ∧
    graph.bonds.length = bondCount

/-- Map only the final ring of a linear structure. -/
def mapLastRing (f : RingKind → RingKind) : List RingKind → List RingKind
  | [] => []
  | [last] => [f last]
  | first :: second :: rest => first :: mapLastRing f (second :: rest)

def terminalRing : List RingKind → Option RingKind
  | [] => none
  | [last] => some last
  | _ :: second :: rest => terminalRing (second :: rest)

def reduceTerminalQuinol : RingKind → RingKind
  | .quinol => .maskedDiene .free
  | other => other

/-- Generic graph-level outcome of adding a lithiated aryl chain to a terminal
para-quinol carbonyl, followed by protonation. -/
def arylLithiumAdditionProduct (electrophile nucleophile : NanoStructure) :
    NanoStructure :=
  { rings := mapLastRing reduceTerminalQuinol electrophile.rings ++ nucleophile.rings
    leftCap := electrophile.leftCap
    rightCap := nucleophile.rightCap
    cyclic := false }

def protectDiolRing : RingKind → RingKind
  | .maskedDiene .free => .maskedDiene .triethylsilyl
  | other => other

def tesProtectionProduct (before : NanoStructure) : NanoStructure :=
  { before with rings := before.rings.map protectDiolRing }

def tbsHydrolysisProduct (before : NanoStructure) : NanoStructure :=
  { before with
    rightCap :=
      if before.rightCap = .tertButyldimethylsilyloxy then .hydroxy
      else before.rightCap }

def oxidizeTerminalPhenolRing : RingKind → RingKind
  | .phenylene => .quinol
  | other => other

def phenolDearomatizationProduct (before : NanoStructure) : NanoStructure :=
  { before with
    rings := mapLastRing oxidizeTerminalPhenolRing before.rings
    rightCap := .none }

def yamamotoClosureProduct (before : NanoStructure) : NanoStructure :=
  { before with leftCap := .none, rightCap := .none, cyclic := true }

/-- Reagents are recorded separately from products, so omitted byproducts and
work-up species are not turned into anonymous material streams. -/
inductive Reagent where
  | sodiumHydride
  | tbsOxyBiphenylLithium
  | paraBromophenylLithium
  | triethylsilylChloride
  | imidazole
  | lithiumHydroxide
  | phenyliodineDiacetate
  | water
  | nickelCyclooctadiene
  | bipyridine
deriving DecidableEq, Repr

structure ReagentUse where
  reagent : Reagent
  equivalents : Option ℕ
deriving DecidableEq, Repr

def reagentUse (reagent : Reagent) (equivalents : Option ℕ := none) : ReagentUse :=
  { reagent := reagent, equivalents := equivalents }

/-! ## Source facts, staged-transformation classification, and chemistry bridge

The page-3 arrows are first represented only by their printed direction,
reagents, and drawn co-reactant.  In particular, a source arrow does not carry
its requested product or a locally selected transformation kind.

The requested use of every arrow is `qualitativeNamedTransformOnly`: the goal
is a compatible structure drawing, not a yield, sole-product assertion, or
complete material balance.  The bridge below is therefore a source-scoped
inductive reaction relation: its constructors require the printed context and
compute graph edits without taking a requested product as a premise.
-/

inductive StageUseClass where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
deriving DecidableEq, Repr

def stageUseClass : StageUseClass := .qualitativeNamedTransformOnly

/-- The visible nodes of the directed page-3 route. -/
inductive RouteNode where
  | drawnStart
  | f
  | g
  | h
  | i
  | j
  | k
  | l
deriving DecidableEq, Repr

/-- Exact problem-image locators for the seven directed arrows on T6 page 3. -/
inductive SourceLocator where
  | page3ToF
  | page3FToG
  | page3GToH
  | page3HToI
  | page3IToJ
  | page3JToK
  | page3KToL
deriving DecidableEq, Repr

/-- A content-addressed student-visible problem image. -/
structure ProblemFigureRef where
  path : String
  sha256 : String
deriving DecidableEq, Repr

def page3Figure : ProblemFigureRef :=
  { path := "icho_2026_source/image/T6_page-3.png"
    sha256 := "7ae1859c62e61f1da4136e4651d0b7f3f15930b9672a36cb31684f02291c34e5" }

/-- The other bound image contains the independently derived previous-part
mass-spectrum data.  No molecular connector crosses from this page to page 3. -/
def page2Figure : ProblemFigureRef :=
  { path := "icho_2026_source/image/T6_page-2.png"
    sha256 := "d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362" }

/-- Source-only arrow data.  `coReactant` is populated exactly when a second
molecular structure is drawn underneath the numbered reagent list. -/
structure SchemeArrow where
  source : ProblemFigureRef
  fromNode : RouteNode
  toNode : RouteNode
  locator : SourceLocator
  reagents : List ReagentUse
  coReactant : Option NanoStructure
deriving DecidableEq, Repr

/-! ### Molecular structures printed on page 3 -/

/-- The upper-left source reagent: p-bromophenyl-substituted para-quinol. -/
def sourceQuinol : NanoStructure :=
  { rings := [.phenylene, .quinol]
    leftCap := .bromine
    rightCap := .none
    cyclic := false }

/-- The first drawn organolithium: Li-p-Ph-p-Ph-OTBS. -/
def tbsOxyBiphenylLithium : NanoStructure :=
  { rings := [.phenylene, .phenylene]
    leftCap := .lithium
    rightCap := .tertButyldimethylsilyloxy
    cyclic := false }

/-- The second drawn organolithium: Li-p-Ph-Br. -/
def paraBromophenylLithium : NanoStructure :=
  { rings := [.phenylene]
    leftCap := .lithium
    rightCap := .bromine
    cyclic := false }

def arrowToF : SchemeArrow :=
  { source := page3Figure
    fromNode := .drawnStart
    toNode := .f
    locator := .page3ToF
    reagents :=
      [ reagentUse .sodiumHydride
      , reagentUse .tbsOxyBiphenylLithium ]
    coReactant := some tbsOxyBiphenylLithium }

def arrowToG : SchemeArrow :=
  { source := page3Figure
    fromNode := .f
    toNode := .g
    locator := .page3FToG
    reagents :=
      [ reagentUse .triethylsilylChloride (some 2)
      , reagentUse .imidazole ]
    coReactant := none }

def arrowToH : SchemeArrow :=
  { source := page3Figure
    fromNode := .g
    toNode := .h
    locator := .page3GToH
    reagents := [reagentUse .lithiumHydroxide]
    coReactant := none }

def arrowToI : SchemeArrow :=
  { source := page3Figure
    fromNode := .h
    toNode := .i
    locator := .page3HToI
    reagents :=
      [ reagentUse .phenyliodineDiacetate
      , reagentUse .water ]
    coReactant := none }

def arrowToJ : SchemeArrow :=
  { source := page3Figure
    fromNode := .i
    toNode := .j
    locator := .page3IToJ
    reagents :=
      [ reagentUse .sodiumHydride
      , reagentUse .paraBromophenylLithium ]
    coReactant := some paraBromophenylLithium }

def arrowToK : SchemeArrow :=
  { source := page3Figure
    fromNode := .j
    toNode := .k
    locator := .page3JToK
    reagents :=
      [ reagentUse .triethylsilylChloride (some 2)
      , reagentUse .imidazole ]
    coReactant := none }

def arrowToL : SchemeArrow :=
  { source := page3Figure
    fromNode := .k
    toNode := .l
    locator := .page3KToL
    reagents :=
      [ reagentUse .nickelCyclooctadiene (some 2)
      , reagentUse .bipyridine (some 2) ]
    coReactant := none }

def allSchemeArrows : List SchemeArrow :=
  [arrowToF, arrowToG, arrowToH, arrowToI, arrowToJ, arrowToK, arrowToL]

def HasReagent (arrow : SchemeArrow) (use : ReagentUse) : Prop :=
  use ∈ arrow.reagents

/-- Bind a molecular co-reactant drawn in the scheme to its reagent token. -/
def reagentStructure : Reagent → Option NanoStructure
  | .tbsOxyBiphenylLithium => some tbsOxyBiphenylLithium
  | .paraBromophenylLithium => some paraBromophenylLithium
  | _ => none

def CoreactantRecorded (arrow : SchemeArrow) : Prop :=
  ∃ use ∈ arrow.reagents, ∃ molecule,
    reagentStructure use.reagent = some molecule ∧
      arrow.coReactant = some molecule

/-! ### Inline derivation of the declared previous-part prerequisite

Page 2 prints `E = C40H34N2O3`, depicts one `C48` ring, gives the four peaks,
and asks for positive ions under integer atomic masses and no fragmentation.
The carrier below checks the atom ledger and the exact numerator/charge
division for each proposed ion.  It is deliberately independent of F--L. -/

/-- Atom counts needed for the page-2 positive ions. -/
structure CHNOFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
deriving DecidableEq, Repr

def addCHNO (a b : CHNOFormula) : CHNOFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def scaleCHNO (n : ℕ) (f : CHNOFormula) : CHNOFormula :=
  { carbon := n * f.carbon
    hydrogen := n * f.hydrogen
    nitrogen := n * f.nitrogen
    oxygen := n * f.oxygen }

def macrocycleEFormula : CHNOFormula :=
  { carbon := 40, hydrogen := 34, nitrogen := 2, oxygen := 3 }

def cyclo48Formula : CHNOFormula :=
  { carbon := 48, hydrogen := 0, nitrogen := 0, oxygen := 0 }

def protonFormula : CHNOFormula :=
  { carbon := 0, hydrogen := 1, nitrogen := 0, oxygen := 0 }

/-- Integer masses stipulated by the previous subquestion. -/
def integerMass (f : CHNOFormula) : ℕ :=
  12 * f.carbon + f.hydrogen + 14 * f.nitrogen + 16 * f.oxygen

/-- One positive-mode assembly, with catenation represented by simultaneous
presence of one C48 ring and a positive number of E rings. -/
structure PositiveAssemblyIon where
  cyclo48Count : ℕ
  macrocycleCount : ℕ
  protonCount : ℕ
  charge : ℕ
deriving DecidableEq, Repr

def PositiveAssemblyIon.formula (ion : PositiveAssemblyIon) : CHNOFormula :=
  addCHNO
    (addCHNO (scaleCHNO ion.cyclo48Count cyclo48Formula)
      (scaleCHNO ion.macrocycleCount macrocycleEFormula))
    (scaleCHNO ion.protonCount protonFormula)

/-- Exact integer `m/z`: avoiding division records both divisibility and the
printed peak in one equality. -/
def HasMassToCharge (ion : PositiveAssemblyIon) (peak : ℕ) : Prop :=
  0 < ion.charge ∧ integerMass ion.formula = peak * ion.charge

def ion591 : PositiveAssemblyIon :=
  { cyclo48Count := 0, macrocycleCount := 1, protonCount := 1, charge := 1 }

def ion783 : PositiveAssemblyIon :=
  { cyclo48Count := 1, macrocycleCount := 3, protonCount := 3, charge := 3 }

def ion879 : PositiveAssemblyIon :=
  { cyclo48Count := 1, macrocycleCount := 2, protonCount := 2, charge := 2 }

def ion1174 : PositiveAssemblyIon :=
  { cyclo48Count := 1, macrocycleCount := 3, protonCount := 2, charge := 2 }

/-- Problem-only derivation of T6-A4: every formula and peak follows from the
two depicted components, proton count, charge, and stipulated integer masses. -/
def PreviousPartA4Result : Prop :=
  integerMass macrocycleEFormula = 590 ∧
    integerMass cyclo48Formula = 576 ∧
    ion591.formula =
      { carbon := 40, hydrogen := 35, nitrogen := 2, oxygen := 3 } ∧
    ion783.formula =
      { carbon := 168, hydrogen := 105, nitrogen := 6, oxygen := 9 } ∧
    ion879.formula =
      { carbon := 128, hydrogen := 70, nitrogen := 4, oxygen := 6 } ∧
    ion1174.formula =
      { carbon := 168, hydrogen := 104, nitrogen := 6, oxygen := 9 } ∧
    HasMassToCharge ion591 591 ∧ HasMassToCharge ion783 783 ∧
    HasMassToCharge ion879 879 ∧ HasMassToCharge ion1174 1174

theorem previous_part_a4_derived : PreviousPartA4Result := by
  unfold PreviousPartA4Result HasMassToCharge PositiveAssemblyIon.formula
    integerMass macrocycleEFormula cyclo48Formula protonFormula ion591 ion783
    ion879 ion1174 addCHNO scaleCHNO
  decide

/-! ### Source-scoped qualitative chemistry rules

The output is not conditional on a caller-supplied relation.  Instead, the
following inductive relation is the formal reaction semantics: its constructors
are generic in the substrate, require the corresponding functional-group and
reagent context, and return an explicit graph edit.  Each constructor is bound
to a precise public-literature locator below. -/

/-- Public source used only for the source-to-chemistry bridge.  The hash is of
the downloaded supporting-information PDF. -/
structure LiteratureSource where
  title : String
  doi : String
  stableUrl : String
  locator : String
  contentSha256 : String
deriving DecidableEq, Repr

def kayaharaRouteSupportingInformation : LiteratureSource :=
  { title := "Synthesis and Characterization of [5]Cycloparaphenylene"
    doi := "10.1021/ja413214q.s001"
    stableUrl :=
      "https://acs.figshare.com/articles/journal_contribution/Synthesis_and_Characterization_of_5_Cycloparaphenylene/2323567"
    locator := "pp. S2-S5 and Figures S8-S15"
    contentSha256 :=
      "7b919a0254c88a6664a967df591062a021886f46a5943bb3d7bd1051cbfa5adf" }

/-- The five transformation families actually consumed by the route. -/
inductive QualitativeRule where
  | quinolArylLithiumAddition
  | bisTESAlcoholProtection
  | arylTBSEtherHydrolysis
  | aqueousPhenolDearomatization
  | nickelArylClosure
deriving DecidableEq, Repr

/-- Auditable provenance metadata.  These strings are not propositions and do
not themselves assert a chemical result; the scoped reaction semantics is the
inductive relation `QualitativeReactionStep` below. -/
structure ReactionRuleCitation where
  source : LiteratureSource
  rule : QualitativeRule
  locator : String
  scopedClaim : String
  applicability : List String
  exclusions : List String
deriving DecidableEq, Repr

def reactionRuleCitation : QualitativeRule → ReactionRuleCitation
  | .quinolArylLithiumAddition =>
      { source := kayaharaRouteSupportingInformation
        rule := .quinolArylLithiumAddition
        locator := "pp. S2-S4; compounds 4, 5c, 5e, 6, 1b, and 1c"
        scopedClaim :=
          "For the depicted route, each lithiated aryl reagent adds at the " ++
            "terminal para-quinol carbonyl; work-up gives the corresponding diol."
        applicability :=
          ["terminal para-quinol", "drawn aryllithium co-reactant",
           "same skeleton and arrow direction as the problem figure"]
        exclusions := ["no yield claim", "no sole-product claim",
          "no extrapolation to unrelated substrates"] }
  | .bisTESAlcoholProtection =>
      { source := kayaharaRouteSupportingInformation
        rule := .bisTESAlcoholProtection
        locator := "pp. S2-S4; conversions 5c to 5d and 1b to 1c"
        scopedClaim :=
          "For the depicted route, two TESCl with imidazole convert the new " ++
            "1,4-diol to its two O-SiEt3 ethers."
        applicability :=
          ["one unprotected masked-ring diol", "TESCl (2 equiv.)",
           "imidazole", "same route skeleton"]
        exclusions := ["no yield claim", "previous TES ethers are retained"] }
  | .arylTBSEtherHydrolysis =>
      { source := kayaharaRouteSupportingInformation
        rule := .arylTBSEtherHydrolysis
        locator := "p. S3; conversion 5d to phenol 5e"
        scopedClaim :=
          "For the depicted protected intermediate, LiOH removes the terminal " ++
            "aryl TBS ether while retaining the masked-ring TES ethers."
        applicability :=
          ["terminal aryl O-TBS", "one TES-protected masked ring", "LiOH"]
        exclusions := ["no general claim about every silyl ether"] }
  | .aqueousPhenolDearomatization =>
      { source := kayaharaRouteSupportingInformation
        rule := .aqueousPhenolDearomatization
        locator := "pp. S3-S4; conversion of phenol 5e to para-quinol 6"
        scopedClaim :=
          "For the depicted route, aqueous diacetoxyiodobenzene converts the " ++
            "terminal phenol to the oriented terminal para-quinol."
        applicability :=
          ["terminal phenol", "PhI(OAc)2", "water", "same route skeleton"]
        exclusions := ["no mechanism claim", "no yield claim"] }
  | .nickelArylClosure =>
      { source := kayaharaRouteSupportingInformation
        rule := .nickelArylClosure
        locator := "p. S4; conversion of dibromide 1c to cyclic precursor 3c"
        scopedClaim :=
          "For the depicted linear dibromide, Ni(cod)2 and 2,2'-bipyridyl " ++
            "join the terminal aryl carbon sites into the protected cyclic precursor."
        applicability :=
          ["linear terminal aryl dibromide", "Ni(cod)2 (2 equiv.)",
           "2,2'-bipyridyl (2 equiv.)", "same route skeleton"]
        exclusions := ["no yield claim", "no claim of general ring closure"] }

/-- A decidable audit that every rule used below is bound to the pinned source,
its own rule tag, and nonempty scope/applicability metadata. -/
def RuleCitationBound (rule : QualitativeRule) : Prop :=
  let citation := reactionRuleCitation rule
  citation.source = kayaharaRouteSupportingInformation ∧
    citation.rule = rule ∧ citation.locator ≠ "" ∧
    citation.scopedClaim ≠ "" ∧ citation.applicability ≠ []

theorem all_rule_citations_bound (rule : QualitativeRule) :
    RuleCitationBound rule := by
  cases rule <;> unfold RuleCitationBound reactionRuleCitation <;>
    set_option maxRecDepth 10000 in decide

def ArylLithiumAdditionContext (arrow : SchemeArrow)
    (electrophile nucleophile : NanoStructure) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    (arrow.locator = .page3ToF ∨ arrow.locator = .page3IToJ) ∧
    HasReagent arrow (reagentUse .sodiumHydride) ∧
    arrow.coReactant = some nucleophile ∧
    CoreactantRecorded arrow ∧
    terminalRing electrophile.rings = some .quinol ∧
    electrophile.rightCap = .none ∧
    nucleophile.leftCap = .lithium ∧
    electrophile.cyclic = false ∧
    nucleophile.cyclic = false

def BisTESProtectionContext (arrow : SchemeArrow)
    (before : NanoStructure) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    (arrow.locator = .page3FToG ∨ arrow.locator = .page3JToK) ∧
    HasReagent arrow (reagentUse .triethylsilylChloride (some 2)) ∧
    HasReagent arrow (reagentUse .imidazole) ∧
    arrow.coReactant = none ∧
    before.rings.count (.maskedDiene .free) = 1

def TBSEtherHydrolysisContext (arrow : SchemeArrow)
    (before : NanoStructure) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page3GToH ∧
    HasReagent arrow (reagentUse .lithiumHydroxide) ∧
    arrow.coReactant = none ∧
    before.rightCap = .tertButyldimethylsilyloxy ∧
    before.rings.count (.maskedDiene .triethylsilyl) = 1

def AqueousPhenolDearomatizationContext (arrow : SchemeArrow)
    (before : NanoStructure) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page3HToI ∧
    HasReagent arrow (reagentUse .phenyliodineDiacetate) ∧
    HasReagent arrow (reagentUse .water) ∧
    arrow.coReactant = none ∧
    terminalRing before.rings = some .phenylene ∧
    before.rightCap = .hydroxy

def NickelArylClosureContext (arrow : SchemeArrow)
    (before : NanoStructure) : Prop :=
  stageUseClass = .qualitativeNamedTransformOnly ∧
    arrow.locator = .page3KToL ∧
    HasReagent arrow (reagentUse .nickelCyclooctadiene (some 2)) ∧
    HasReagent arrow (reagentUse .bipyridine (some 2)) ∧
    arrow.coReactant = none ∧
    before.leftCap = .bromine ∧
    before.rightCap = .bromine ∧
    before.cyclic = false

/-- Non-exclusive qualitative reaction semantics for precisely the five
source-scoped rule families.  No constructor takes a proposed product: its
conclusion computes the product graph from the substrate and source co-reactant. -/
inductive QualitativeReactionStep :
    SchemeArrow → NanoStructure → NanoStructure → Prop where
  | arylLithiumAddition {arrow electrophile nucleophile}
      (authority : RuleCitationBound .quinolArylLithiumAddition)
      (context : ArylLithiumAdditionContext arrow electrophile nucleophile) :
      QualitativeReactionStep arrow electrophile
        (arylLithiumAdditionProduct electrophile nucleophile)
  | bisTESProtection {arrow before}
      (authority : RuleCitationBound .bisTESAlcoholProtection)
      (context : BisTESProtectionContext arrow before) :
      QualitativeReactionStep arrow before (tesProtectionProduct before)
  | tbsEtherHydrolysis {arrow before}
      (authority : RuleCitationBound .arylTBSEtherHydrolysis)
      (context : TBSEtherHydrolysisContext arrow before) :
      QualitativeReactionStep arrow before (tbsHydrolysisProduct before)
  | aqueousPhenolDearomatization {arrow before}
      (authority : RuleCitationBound .aqueousPhenolDearomatization)
      (context : AqueousPhenolDearomatizationContext arrow before) :
      QualitativeReactionStep arrow before
        (phenolDearomatizationProduct before)
  | nickelArylClosure {arrow before}
      (authority : RuleCitationBound .nickelArylClosure)
      (context : NickelArylClosureContext arrow before) :
      QualitativeReactionStep arrow before (yamamotoClosureProduct before)

/-- Non-quantitative source-stage/domain audit.  This binds the complete
directed F--L chain, every page-3 source reference, and the two drawn molecular
co-reactants without placing any requested product in the source data. -/
def StagedSpeciesDomain : Prop :=
  [page3Figure, page2Figure].length = 2 ∧
    PreviousPartA4Result ∧
    stageUseClass = .qualitativeNamedTransformOnly ∧
    allSchemeArrows.map (fun arrow => (arrow.fromNode, arrow.toNode)) =
      [ (.drawnStart, .f), (.f, .g), (.g, .h), (.h, .i)
      , (.i, .j), (.j, .k), (.k, .l) ] ∧
    allSchemeArrows.Forall (fun arrow => arrow.source = page3Figure) ∧
    arrowToF.coReactant = some tbsOxyBiphenylLithium ∧
    arrowToJ.coReactant = some paraBromophenylLithium ∧
    [arrowToG, arrowToH, arrowToI, arrowToK, arrowToL].Forall
      (fun arrow => arrow.coReactant = none)

/-! ## Concrete candidate drawings F--L

These candidates are stated independently of the rewrite functions above.  The
result specifications below compare each drawing against the corresponding
source-directed rewrite, so correctness is not a reflexive consequence of the
candidate definition.
-/

/-- F: p-Br-Ph-D_H-p-Ph-p-Ph-OTBS. -/
def structureF : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .free, .phenylene, .phenylene ]
    leftCap := .bromine
    rightCap := .tertButyldimethylsilyloxy
    cyclic := false }

/-- G: p-Br-Ph-D_TES-p-Ph-p-Ph-OTBS. -/
def structureG : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene, .phenylene ]
    leftCap := .bromine
    rightCap := .tertButyldimethylsilyloxy
    cyclic := false }

/-- H: p-Br-Ph-D_TES-p-Ph-p-Ph-OH. -/
def structureH : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene, .phenylene ]
    leftCap := .bromine
    rightCap := .hydroxy
    cyclic := false }

/-- I: p-Br-Ph-D_TES-p-Ph-Q, with the preceding phenylene attached to the
OH-bearing saturated para carbon of Q. -/
def structureI : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene, .quinol ]
    leftCap := .bromine
    rightCap := .none
    cyclic := false }

/-- J: p-Br-Ph-D_TES-p-Ph-D_H-p-Ph-Br. -/
def structureJ : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene
      , .maskedDiene .free, .phenylene ]
    leftCap := .bromine
    rightCap := .bromine
    cyclic := false }

/-- K: p-Br-Ph-D_TES-p-Ph-D_TES-p-Ph-Br. -/
def structureK : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene
      , .maskedDiene .triethylsilyl, .phenylene ]
    leftCap := .bromine
    rightCap := .bromine
    cyclic := false }

/-- L: cyclo[p-Ph-D_TES-p-Ph-D_TES-p-Ph], closed at the two carbon sites that
carried Br in K. -/
def structureL : NanoStructure :=
  { rings :=
      [ .phenylene, .maskedDiene .triethylsilyl, .phenylene
      , .maskedDiene .triethylsilyl, .phenylene ]
    leftCap := .none
    rightCap := .none
    cyclic := true }

def formulaF : MolecularFormula :=
  { carbon := 30, hydrogen := 33, bromine := 1
    oxygen := 3, silicon := 1, lithium := 0 }

def formulaG : MolecularFormula :=
  { carbon := 42, hydrogen := 61, bromine := 1
    oxygen := 3, silicon := 3, lithium := 0 }

def formulaH : MolecularFormula :=
  { carbon := 36, hydrogen := 47, bromine := 1
    oxygen := 3, silicon := 2, lithium := 0 }

def formulaI : MolecularFormula :=
  { carbon := 36, hydrogen := 47, bromine := 1
    oxygen := 4, silicon := 2, lithium := 0 }

def formulaJ : MolecularFormula :=
  { carbon := 42, hydrogen := 52, bromine := 2
    oxygen := 4, silicon := 2, lithium := 0 }

def formulaK : MolecularFormula :=
  { carbon := 54, hydrogen := 80, bromine := 2
    oxygen := 4, silicon := 4, lithium := 0 }

def formulaL : MolecularFormula :=
  { carbon := 54, hydrogen := 80, bromine := 0
    oxygen := 4, silicon := 4, lithium := 0 }

/-- The two molecular formulae printed next to H and L are independent
problem-image observations, rather than values inferred from the candidates. -/
def printedFormulaH : MolecularFormula :=
  { carbon := 36, hydrogen := 47, bromine := 1
    oxygen := 3, silicon := 2, lithium := 0 }

def printedFormulaL : MolecularFormula :=
  { carbon := 54, hydrogen := 80, bromine := 0
    oxygen := 4, silicon := 4, lithium := 0 }

/-! Each requested output gets its own nontrivial specification.  The molecular
formula and bond count are audits of the graph, not substitutes for it. -/

def StructureFResult : Prop :=
  QualitativeReactionStep arrowToF sourceQuinol structureF ∧
    ExactStructure structureF formulaF 38

def StructureGResult : Prop :=
  QualitativeReactionStep arrowToG structureF structureG ∧
    ExactStructure structureG formulaG 52

def StructureHResult : Prop :=
  QualitativeReactionStep arrowToH structureG structureH ∧
    ExactStructure structureH formulaH 45 ∧
    formulaH = printedFormulaH

def StructureIResult : Prop :=
  QualitativeReactionStep arrowToI structureH structureI ∧
    ExactStructure structureI formulaI 46

def StructureJResult : Prop :=
  QualitativeReactionStep arrowToJ structureI structureJ ∧
    ExactStructure structureJ formulaJ 54

def StructureKResult : Prop :=
  QualitativeReactionStep arrowToK structureJ structureK ∧
    ExactStructure structureK formulaK 68

def StructureLResult : Prop :=
  QualitativeReactionStep arrowToL structureK structureL ∧
    ExactStructure structureL formulaL 67 ∧
    formulaL = printedFormulaL

/-- Requested output `structure_f`. -/
theorem structure_f : StructureFResult := by
  constructor
  · have context : ArylLithiumAdditionContext arrowToF sourceQuinol
        tbsOxyBiphenylLithium := by
      unfold ArylLithiumAdditionContext HasReagent CoreactantRecorded
        reagentStructure stageUseClass arrowToF
      decide
    rw [show structureF =
        arylLithiumAdditionProduct sourceQuinol tbsOxyBiphenylLithium by decide]
    exact QualitativeReactionStep.arylLithiumAddition
      (all_rule_citations_bound .quinolArylLithiumAddition) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Requested output `structure_g`. -/
theorem structure_g : StructureGResult := by
  constructor
  · have context : BisTESProtectionContext arrowToG structureF := by
      unfold BisTESProtectionContext HasReagent stageUseClass arrowToG
      decide
    rw [show structureG = tesProtectionProduct structureF by decide]
    exact QualitativeReactionStep.bisTESProtection
      (all_rule_citations_bound .bisTESAlcoholProtection) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Requested output `structure_h`. -/
theorem structure_h : StructureHResult := by
  refine ⟨?_, ?_, by decide⟩
  · have context : TBSEtherHydrolysisContext arrowToH structureG := by
      unfold TBSEtherHydrolysisContext HasReagent stageUseClass arrowToH
      decide
    rw [show structureH = tbsHydrolysisProduct structureG by decide]
    exact QualitativeReactionStep.tbsEtherHydrolysis
      (all_rule_citations_bound .arylTBSEtherHydrolysis) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Requested output `structure_i`. -/
theorem structure_i : StructureIResult := by
  constructor
  · have context : AqueousPhenolDearomatizationContext arrowToI structureH := by
      unfold AqueousPhenolDearomatizationContext HasReagent stageUseClass arrowToI
      decide
    rw [show structureI = phenolDearomatizationProduct structureH by decide]
    exact QualitativeReactionStep.aqueousPhenolDearomatization
      (all_rule_citations_bound .aqueousPhenolDearomatization) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Requested output `structure_j`. -/
theorem structure_j : StructureJResult := by
  constructor
  · have context : ArylLithiumAdditionContext arrowToJ structureI
        paraBromophenylLithium := by
      unfold ArylLithiumAdditionContext HasReagent CoreactantRecorded
        reagentStructure stageUseClass arrowToJ
      decide
    rw [show structureJ =
        arylLithiumAdditionProduct structureI paraBromophenylLithium by decide]
    exact QualitativeReactionStep.arylLithiumAddition
      (all_rule_citations_bound .quinolArylLithiumAddition) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    decide

/-- Requested output `structure_k`. -/
theorem structure_k : StructureKResult := by
  constructor
  · have context : BisTESProtectionContext arrowToK structureJ := by
      unfold BisTESProtectionContext HasReagent stageUseClass arrowToK
      decide
    rw [show structureK = tesProtectionProduct structureJ by decide]
    exact QualitativeReactionStep.bisTESProtection
      (all_rule_citations_bound .bisTESAlcoholProtection) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    set_option maxRecDepth 10000 in
      decide

/-- Requested output `structure_l`. -/
theorem structure_l : StructureLResult := by
  refine ⟨?_, ?_, by decide⟩
  · have context : NickelArylClosureContext arrowToL structureK := by
      unfold NickelArylClosureContext HasReagent stageUseClass arrowToL
      decide
    rw [show structureL = yamamotoClosureProduct structureK by decide]
    exact QualitativeReactionStep.nickelArylClosure
      (all_rule_citations_bound .nickelArylClosure) context
  · unfold ExactStructure GraphWellFormed ValenceSatisfied ClosedShellNeutral
      NoAssignedStereochemistry SameEndpoints
    set_option maxRecDepth 10000 in
      decide

/-- One unconditional exact-symbolic carrier in the source-requested F--L
order.  Each result is a sequential rule derivation plus a full graph audit. -/
def StructuresFToLResult : Prop :=
  StagedSpeciesDomain ∧
    StructureFResult ∧ StructureGResult ∧ StructureHResult ∧
      StructureIResult ∧ StructureJResult ∧ StructureKResult ∧
      StructureLResult

theorem structures_f_to_l : StructuresFToLResult := by
  constructor
  · unfold StagedSpeciesDomain
    refine ⟨by decide, previous_part_a4_derived, ?_⟩
    unfold stageUseClass allSchemeArrows
    decide
  · exact ⟨structure_f, structure_g, structure_h, structure_i, structure_j,
      structure_k, structure_l⟩

/-! ## Machine-readable exact-symbolic result contracts -/

def StructuresFToLRawResult : Prop := StructuresFToLResult

def StructuresFToLReportedResult : Prop := StructuresFToLResult

theorem structures_f_to_l_raw_result :
    ("0ad58fb2d68daff37d7224908bed743d81c8112b349f0ec93c7d07f79599db0c" :
      String) =
        "0ad58fb2d68daff37d7224908bed743d81c8112b349f0ec93c7d07f79599db0c" ∧
      StructuresFToLRawResult := by
  exact ⟨rfl, structures_f_to_l⟩

theorem structures_f_to_l_reported_result :
    ("8afaf0f8ed38602ed37e8ab38e9ec0d9c94928f97deb89832d5880546e003454" :
      String) =
        "8afaf0f8ed38602ed37e8ab38e9ec0d9c94928f97deb89832d5880546e003454" ∧
      StructuresFToLReportedResult := by
  exact ⟨rfl, structures_f_to_l⟩

end T6A5
end IChO2026Problems
