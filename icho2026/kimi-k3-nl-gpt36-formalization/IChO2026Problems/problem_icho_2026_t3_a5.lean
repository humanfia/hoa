import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 3.5

This file formalizes the structure-drawing answer as a labelled molecular graph.
Hydrogens are stored at their heavy-atom sites, and `ExpandedAtom` turns every
such hydrogen into an individual atom joined to its parent by a single bond.
Thus the compact graph representation does not discard hydrogen connectivity.

The source reaction is used only as a qualitative named transformation.  No
yield, completion, sole-product, phase, or unprinted byproduct claim is made.
-/

namespace IChO2026Problems.ProblemIcho2026T3A5

/-! ## Molecular-graph vocabulary -/

inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  | fluorine
  deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr

/-- Twice the ordinary bond order; an aromatic bond contributes three units. -/
def BondOrder.valenceUnits : BondOrder → ℕ
  | .single => 2
  | .double => 4
  | .triple => 6
  | .aromatic => 3

inductive StereoDescriptor where
  | none
  | alkeneE
  | alkeneZ
  | tetrahedralR
  | tetrahedralS
  deriving DecidableEq, Repr

/-- A heavy-atom site.  `attachedHydrogens` records separately bound H atoms. -/
structure AtomSpec where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  stereochemistry : StereoDescriptor
  deriving DecidableEq, Repr

def neutralAtom (element : Element) (hydrogens : ℕ) : AtomSpec :=
  { element := element
    formalCharge := 0
    radicalElectrons := 0
    attachedHydrogens := hydrogens
    stereochemistry := .none }

/-- One undirected, bond-order-labelled edge. -/
structure BondSpec (α : Type) where
  left : α
  right : α
  order : BondOrder
  deriving Repr

def BondSpec.Connects {α : Type} (e : BondSpec α) (a b : α) : Prop :=
  (e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)

def BondSpec.map {α β : Type} (f : α → β) (e : BondSpec α) : BondSpec β :=
  { left := f e.left, right := f e.right, order := e.order }

def bond {α : Type} (left right : α) (order : BondOrder) : BondSpec α :=
  { left := left, right := right, order := order }

structure MolecularGraph (α : Type) where
  atom : α → AtomSpec
  bonds : List (BondSpec α)

def MolecularGraph.Bonded {α : Type} (g : MolecularGraph α)
    (a b : α) (order : BondOrder) : Prop :=
  ∃ e ∈ g.bonds, e.Connects a b ∧ e.order = order

/-- All hydrogen atoms made explicit. -/
abbrev ExpandedAtom {α : Type} (g : MolecularGraph α) : Type :=
  Sum α (Σ a : α, Fin (g.atom a).attachedHydrogens)

def ExpandedAtom.element {α : Type} {g : MolecularGraph α} : ExpandedAtom g → Element
  | .inl a => (g.atom a).element
  | .inr _ => .hydrogen

/-- Bond relation after expansion of the site-attached hydrogens. -/
def MolecularGraph.ExpandedBonded {α : Type} [DecidableEq α] (g : MolecularGraph α)
    (x y : ExpandedAtom g) (order : BondOrder) : Prop :=
  match x, y with
  | .inl a, .inl b => g.Bonded a b order
  | .inl a, .inr ⟨b, _⟩ => a = b ∧ order = .single
  | .inr ⟨a, _⟩, .inl b => a = b ∧ order = .single
  | .inr _, .inr _ => False

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  fluorine : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    fluorine := a.fluorine + b.fluorine
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen }

def MolecularFormula.scale (n : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := n * a.carbon
    hydrogen := n * a.hydrogen
    fluorine := n * a.fluorine
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen }

/-- Formula bookkeeping for `n` aldehyde/amine condensations, each losing H₂O. -/
def MolecularFormula.removeWaters (n : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon
    hydrogen := a.hydrogen - 2 * n
    fluorine := a.fluorine
    nitrogen := a.nitrogen
    oxygen := a.oxygen - n }

/-- Add only the oxygen atoms installed at the named local oxidation sites. -/
def MolecularFormula.addOxygenAtoms (n : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon
    hydrogen := a.hydrogen
    fluorine := a.fluorine
    nitrogen := a.nitrogen
    oxygen := a.oxygen + n }

def MolecularGraph.formula {α : Type} [Fintype α] (g : MolecularGraph α) : MolecularFormula :=
  { carbon := ∑ a : α, if (g.atom a).element = .carbon then 1 else 0
    hydrogen := ∑ a : α,
      ((g.atom a).attachedHydrogens + if (g.atom a).element = .hydrogen then 1 else 0)
    fluorine := ∑ a : α, if (g.atom a).element = .fluorine then 1 else 0
    nitrogen := ∑ a : α, if (g.atom a).element = .nitrogen then 1 else 0
    oxygen := ∑ a : α, if (g.atom a).element = .oxygen then 1 else 0 }

/-- Cardinality of the fully hydrogen-expanded atom carrier. -/
def MolecularGraph.expandedAtomCount {α : Type} [Fintype α]
    (g : MolecularGraph α) : ℕ :=
  Fintype.card α + ∑ a : α, (g.atom a).attachedHydrogens

def Element.neutralValenceUnits : Element → ℕ
  | .hydrogen => 2
  | .carbon => 8
  | .nitrogen => 6
  | .oxygen => 4
  | .fluorine => 2

def MolecularGraph.incidentValenceUnits {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a : α) : ℕ :=
  (g.bonds.map fun e =>
    if e.left = a ∨ e.right = a then e.order.valenceUnits else 0).sum

def MolecularGraph.NoSelfBonds {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ e ∈ g.bonds, e.left ≠ e.right

def MolecularGraph.UniqueBondOrders {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ e₁ ∈ g.bonds, ∀ e₂ ∈ g.bonds,
    e₁.Connects e₂.left e₂.right → e₁.order = e₂.order

def MolecularGraph.NeutralClosedValence {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  ∀ a,
    (g.atom a).formalCharge = 0 ∧
    (g.atom a).radicalElectrons = 0 ∧
    (g.atom a).stereochemistry = .none ∧
    g.incidentValenceUnits a + 2 * (g.atom a).attachedHydrogens =
      (g.atom a).element.neutralValenceUnits

inductive MolecularGraph.Reachable {α : Type} (g : MolecularGraph α) : α → α → Prop
  | refl (a : α) : g.Reachable a a
  | tail {a b c : α} (h : g.Reachable a b) (order : BondOrder)
      (hbond : g.Bonded b c order) : g.Reachable a c

def MolecularGraph.Connected {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ a b, g.Reachable a b

def MolecularGraph.WellFormedClosed {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  g.NoSelfBonds ∧ g.UniqueBondOrders ∧ g.NeutralClosedValence ∧ g.Connected

/-! ## The explicit `V-L` open repeat fragment -/

/--
Heavy atoms of one `V-L` pair.  The `vCore` atoms form the 1,3,5-substituted
corner ring; `leftPhenyl` and `rightPhenyl` are the two para-phenylene arms;
the final ten constructors form the tetrafluoroterephthalamide edge.
-/
inductive RepeatAtom where
  | vCore0 | vCore1 | vCore2 | vCore3 | vCore4 | vCore5
  | aldehydeC | aldehydeO
  | leftPhenyl0 | leftPhenyl1 | leftPhenyl2
  | leftPhenyl3 | leftPhenyl4 | leftPhenyl5 | leftAmideN
  | rightPhenyl0 | rightPhenyl1 | rightPhenyl2
  | rightPhenyl3 | rightPhenyl4 | rightPhenyl5 | rightAmideN
  | linkerCarbonylLeftC | linkerCarbonylLeftO
  | linkerRing0 | linkerRing1 | linkerRing2
  | linkerRing3 | linkerRing4 | linkerRing5
  | linkerFluorine1 | linkerFluorine2 | linkerFluorine4 | linkerFluorine5
  | linkerCarbonylRightC | linkerCarbonylRightO
  deriving DecidableEq, Fintype, Repr

def repeatAtomSpec : RepeatAtom → AtomSpec
  | .vCore0 => neutralAtom .carbon 0
  | .vCore1 => neutralAtom .carbon 1
  | .vCore2 => neutralAtom .carbon 0
  | .vCore3 => neutralAtom .carbon 1
  | .vCore4 => neutralAtom .carbon 0
  | .vCore5 => neutralAtom .carbon 1
  | .aldehydeC => neutralAtom .carbon 1
  | .aldehydeO => neutralAtom .oxygen 0
  | .leftPhenyl0 => neutralAtom .carbon 0
  | .leftPhenyl1 => neutralAtom .carbon 1
  | .leftPhenyl2 => neutralAtom .carbon 1
  | .leftPhenyl3 => neutralAtom .carbon 0
  | .leftPhenyl4 => neutralAtom .carbon 1
  | .leftPhenyl5 => neutralAtom .carbon 1
  | .leftAmideN => neutralAtom .nitrogen 1
  | .rightPhenyl0 => neutralAtom .carbon 0
  | .rightPhenyl1 => neutralAtom .carbon 1
  | .rightPhenyl2 => neutralAtom .carbon 1
  | .rightPhenyl3 => neutralAtom .carbon 0
  | .rightPhenyl4 => neutralAtom .carbon 1
  | .rightPhenyl5 => neutralAtom .carbon 1
  | .rightAmideN => neutralAtom .nitrogen 1
  | .linkerCarbonylLeftC => neutralAtom .carbon 0
  | .linkerCarbonylLeftO => neutralAtom .oxygen 0
  | .linkerRing0 => neutralAtom .carbon 0
  | .linkerRing1 => neutralAtom .carbon 0
  | .linkerRing2 => neutralAtom .carbon 0
  | .linkerRing3 => neutralAtom .carbon 0
  | .linkerRing4 => neutralAtom .carbon 0
  | .linkerRing5 => neutralAtom .carbon 0
  | .linkerFluorine1 => neutralAtom .fluorine 0
  | .linkerFluorine2 => neutralAtom .fluorine 0
  | .linkerFluorine4 => neutralAtom .fluorine 0
  | .linkerFluorine5 => neutralAtom .fluorine 0
  | .linkerCarbonylRightC => neutralAtom .carbon 0
  | .linkerCarbonylRightO => neutralAtom .oxygen 0

def repeatBonds : List (BondSpec RepeatAtom) :=
  [ bond .vCore0 .vCore1 .aromatic
  , bond .vCore1 .vCore2 .aromatic
  , bond .vCore2 .vCore3 .aromatic
  , bond .vCore3 .vCore4 .aromatic
  , bond .vCore4 .vCore5 .aromatic
  , bond .vCore5 .vCore0 .aromatic
  , bond .vCore0 .aldehydeC .single
  , bond .aldehydeC .aldehydeO .double
  , bond .vCore2 .leftPhenyl0 .single
  , bond .leftPhenyl0 .leftPhenyl1 .aromatic
  , bond .leftPhenyl1 .leftPhenyl2 .aromatic
  , bond .leftPhenyl2 .leftPhenyl3 .aromatic
  , bond .leftPhenyl3 .leftPhenyl4 .aromatic
  , bond .leftPhenyl4 .leftPhenyl5 .aromatic
  , bond .leftPhenyl5 .leftPhenyl0 .aromatic
  , bond .leftPhenyl3 .leftAmideN .single
  , bond .vCore4 .rightPhenyl0 .single
  , bond .rightPhenyl0 .rightPhenyl1 .aromatic
  , bond .rightPhenyl1 .rightPhenyl2 .aromatic
  , bond .rightPhenyl2 .rightPhenyl3 .aromatic
  , bond .rightPhenyl3 .rightPhenyl4 .aromatic
  , bond .rightPhenyl4 .rightPhenyl5 .aromatic
  , bond .rightPhenyl5 .rightPhenyl0 .aromatic
  , bond .rightPhenyl3 .rightAmideN .single
  , bond .rightAmideN .linkerCarbonylLeftC .single
  , bond .linkerCarbonylLeftC .linkerCarbonylLeftO .double
  , bond .linkerCarbonylLeftC .linkerRing0 .single
  , bond .linkerRing0 .linkerRing1 .aromatic
  , bond .linkerRing1 .linkerRing2 .aromatic
  , bond .linkerRing2 .linkerRing3 .aromatic
  , bond .linkerRing3 .linkerRing4 .aromatic
  , bond .linkerRing4 .linkerRing5 .aromatic
  , bond .linkerRing5 .linkerRing0 .aromatic
  , bond .linkerRing1 .linkerFluorine1 .single
  , bond .linkerRing2 .linkerFluorine2 .single
  , bond .linkerRing4 .linkerFluorine4 .single
  , bond .linkerRing5 .linkerFluorine5 .single
  , bond .linkerRing3 .linkerCarbonylRightC .single
  , bond .linkerCarbonylRightC .linkerCarbonylRightO .double ]

def repeatHeavyGraph : MolecularGraph RepeatAtom :=
  { atom := repeatAtomSpec, bonds := repeatBonds }

/-- An open molecular fragment has exactly two bond ports. -/
structure OpenFragment (α : Type) where
  graph : MolecularGraph α
  incomingPort : α
  outgoingPort : α
  incomingOrder : BondOrder
  outgoingOrder : BondOrder

/--
`V = OHC-C₆H₃[-p-C₆H₄-NH-]₂` followed by
`L = -C(O)-C₆F₄-C(O)-`.  The incoming port is the first amide nitrogen and the
outgoing port is the second carbonyl carbon.
-/
def macrocycleRepeat : OpenFragment RepeatAtom :=
  { graph := repeatHeavyGraph
    incomingPort := .leftAmideN
    outgoingPort := .linkerCarbonylRightC
    incomingOrder := .single
    outgoingOrder := .single }

/-! ## Sixfold cyclic assembly and source-first component ledger -/

def nextCell (i : Fin 6) : Fin 6 := i + 1

def sixfoldIntraCellBonds {α : Type} (fragment : OpenFragment α) :
    List (BondSpec (Fin 6 × α)) :=
  (List.ofFn fun i : Fin 6 =>
    fragment.graph.bonds.map (BondSpec.map fun a => (i, a))).flatten

def sixfoldInterCellBonds {α : Type} (fragment : OpenFragment α) :
    List (BondSpec (Fin 6 × α)) :=
  List.ofFn fun i : Fin 6 =>
    bond (i, fragment.outgoingPort) (nextCell i, fragment.incomingPort)
      fragment.outgoingOrder

/-- Generic cyclic assembly of six copies of a two-port molecular fragment. -/
def sixfoldCyclicAssembly {α : Type} (fragment : OpenFragment α) :
    MolecularGraph (Fin 6 × α) :=
  { atom := fun a => fragment.graph.atom a.2
    bonds := sixfoldIntraCellBonds fragment ++ sixfoldInterCellBonds fragment }

def intraCellBonds : List (BondSpec (Fin 6 × RepeatAtom)) :=
  sixfoldIntraCellBonds macrocycleRepeat

def interCellBonds : List (BondSpec (Fin 6 × RepeatAtom)) :=
  sixfoldInterCellBonds macrocycleRepeat

/-- `X = cyclo[V-L]₆`, expanded at heavy-atom level. -/
def macrocycleX : MolecularGraph (Fin 6 × RepeatAtom) :=
  sixfoldCyclicAssembly macrocycleRepeat

inductive BoundaryComponent where
  | cleavedC2Corner
  | oxidizedD4Edge
  deriving DecidableEq, Repr

/-- The central Kagome-pore boundary read clockwise from the source figure. -/
def cof7BoundaryComponent (i : Fin 12) : BoundaryComponent :=
  if i.val % 2 = 0 then .cleavedC2Corner else .oxidizedD4Edge

def boundaryCornerCount : ℕ :=
  (Finset.univ.filter fun i : Fin 12 =>
    cof7BoundaryComponent i = .cleavedC2Corner).card

def boundaryEdgeCount : ℕ :=
  (Finset.univ.filter fun i : Fin 12 =>
    cof7BoundaryComponent i = .oxidizedD4Edge).card

def rotateBoundary (p : ℕ) (i : Fin 12) : Fin 12 :=
  ⟨(i.val + p) % 12, Nat.mod_lt _ (by decide)⟩

def IsBoundaryPeriod (p : ℕ) : Prop :=
  0 < p ∧ p ≤ 12 ∧
    ∀ i : Fin 12, cof7BoundaryComponent (rotateBoundary p i) = cof7BoundaryComponent i

def IsLeastBoundaryPeriod (p : ℕ) : Prop :=
  IsBoundaryPeriod p ∧ ∀ q : ℕ, IsBoundaryPeriod q → p ≤ q

/-- All formyl groups inherit the outward orientation of the cleaved C2 halves. -/
inductive RadialOrientation where
  | inward
  | outward
  deriving DecidableEq, Repr

def aldehydeOrientation (_ : Fin 6) : RadialOrientation := .outward

/-! ## Qualitative reaction trace and independent composition ledger -/

inductive Reagent where
  | aceticAcid
  | sodiumChlorite
  | sodiumDihydrogenPhosphate
  | ozone
  | dimethylSulfide
  deriving DecidableEq, Repr

structure FunctionalInventory where
  imine : ℕ
  amide : ℕ
  cleavableAlkeneCarbons : ℕ
  formyl : ℕ
  deriving DecidableEq, Repr

/-- Generic local rewrite: every selected imine motif is oxidized to an amide. -/
def oxidizeIminesToAmides (s : FunctionalInventory) : FunctionalInventory :=
  { imine := 0
    amide := s.amide + s.imine
    cleavableAlkeneCarbons := s.cleavableAlkeneCarbons
    formyl := s.formyl }

/-- Generic local rewrite: every selected alkene carbon becomes a formyl carbon. -/
def reductiveOzonolysis (s : FunctionalInventory) : FunctionalInventory :=
  { imine := s.imine
    amide := s.amide
    cleavableAlkeneCarbons := 0
    formyl := s.formyl + s.cleavableAlkeneCarbons }

/-- Motifs in one half-C2 plus one D4 edge after the two imine condensations. -/
def cof7RepeatInventory : FunctionalInventory :=
  { imine := 2, amide := 0, cleavableAlkeneCarbons := 1, formyl := 0 }

def depictedPostSyntheticReagents : List Reagent :=
  [.sodiumChlorite, .sodiumDihydrogenPhosphate]

def depictedDegradationReagents : List Reagent :=
  [.ozone, .dimethylSulfide]

/--
This is a compatibility relation, not a completeness or yield assertion.  It
ties the exact source reagent lists to generic, local structural rewrites.
-/
def QualitativeNamedTransformOnly
    (post degradation : List Reagent)
    (start finish : FunctionalInventory) : Prop :=
  post = [.sodiumChlorite, .sodiumDihydrogenPhosphate] ∧
  degradation = [.ozone, .dimethylSulfide] ∧
  finish = reductiveOzonolysis (oxidizeIminesToAmides start)

def finalRepeatInventory : FunctionalInventory :=
  { imine := 0, amide := 2, cleavableAlkeneCarbons := 0, formyl := 1 }

def arene135Formula : MolecularFormula :=
  { carbon := 6, hydrogen := 3, fluorine := 0, nitrogen := 0, oxygen := 0 }

def paraPhenyleneFormula : MolecularFormula :=
  { carbon := 6, hydrogen := 4, fluorine := 0, nitrogen := 0, oxygen := 0 }

def aminoFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 2, fluorine := 0, nitrogen := 1, oxygen := 0 }

def amideNHFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 1, fluorine := 0, nitrogen := 1, oxygen := 0 }

def alkeneHalfFormula : MolecularFormula :=
  { carbon := 1, hydrogen := 1, fluorine := 0, nitrogen := 0, oxygen := 0 }

def formylFormula : MolecularFormula :=
  { carbon := 1, hydrogen := 1, fluorine := 0, nitrogen := 0, oxygen := 1 }

def carbonylFormula : MolecularFormula :=
  { carbon := 1, hydrogen := 0, fluorine := 0, nitrogen := 0, oxygen := 1 }

def tetrafluoroPhenyleneFormula : MolecularFormula :=
  { carbon := 6, hydrogen := 0, fluorine := 4, nitrogen := 0, oxygen := 0 }

/-- One visually separated half of C2 before condensation: C₁₉H₁₆N₂. -/
def c2HalfFormula : MolecularFormula :=
  MolecularFormula.add arene135Formula <|
    MolecularFormula.add (MolecularFormula.scale 2 paraPhenyleneFormula) <|
      MolecularFormula.add (MolecularFormula.scale 2 aminoFormula) alkeneHalfFormula

/-- The depicted tetrafluoroterephthalaldehyde D4: C₈H₂F₄O₂. -/
def d4Formula : MolecularFormula :=
  MolecularFormula.add tetrafluoroPhenyleneFormula
    (MolecularFormula.scale 2 formylFormula)

/-- Atom ledger after joining one C2 half and one D4 by two imine condensations. -/
def cof7CondensedRepeatFormula : MolecularFormula :=
  MolecularFormula.removeWaters 2 (MolecularFormula.add c2HalfFormula d4Formula)

/-- Each of the two imine carbons acquires one oxygen in the amide stage. -/
def postSyntheticRepeatFormula : MolecularFormula :=
  MolecularFormula.addOxygenAtoms 2 cof7CondensedRepeatFormula

/-- The one alkene carbon belonging to this corner acquires oxygen on cleavage. -/
def degradedRepeatFormula : MolecularFormula :=
  MolecularFormula.addOxygenAtoms 1 postSyntheticRepeatFormula

def expectedC2HalfFormula : MolecularFormula :=
  { carbon := 19, hydrogen := 16, fluorine := 0, nitrogen := 2, oxygen := 0 }

def expectedD4Formula : MolecularFormula :=
  { carbon := 8, hydrogen := 2, fluorine := 4, nitrogen := 0, oxygen := 2 }

def expectedCof7CondensedFormula : MolecularFormula :=
  { carbon := 27, hydrogen := 14, fluorine := 4, nitrogen := 2, oxygen := 0 }

def expectedPostSyntheticFormula : MolecularFormula :=
  { carbon := 27, hydrogen := 14, fluorine := 4, nitrogen := 2, oxygen := 2 }

/-- One post-cleavage corner `V`: C₁₉H₁₄N₂O. -/
def cornerVFormula : MolecularFormula :=
  MolecularFormula.add arene135Formula <|
    MolecularFormula.add (MolecularFormula.scale 2 paraPhenyleneFormula) <|
      MolecularFormula.add (MolecularFormula.scale 2 amideNHFormula) formylFormula

/-- One oxidized edge `L`: C₈F₄O₂. -/
def edgeLFormula : MolecularFormula :=
  MolecularFormula.add tetrafluoroPhenyleneFormula
    (MolecularFormula.scale 2 carbonylFormula)

/-- The independently recombined one-corner/one-edge composition. -/
def vlFormula : MolecularFormula := MolecularFormula.add cornerVFormula edgeLFormula

def expectedVLFormula : MolecularFormula :=
  { carbon := 27, hydrogen := 14, fluorine := 4, nitrogen := 2, oxygen := 3 }

/-! ## Structural motif predicates -/

def HasAldehydeMotif {α : Type} (g : MolecularGraph α)
    (aryl carbonyl oxygen : α) : Prop :=
  (g.atom carbonyl).element = .carbon ∧
  (g.atom carbonyl).attachedHydrogens = 1 ∧
  (g.atom oxygen).element = .oxygen ∧
  g.Bonded aryl carbonyl .single ∧
  g.Bonded carbonyl oxygen .double

def HasAmideMotif {α : Type} (g : MolecularGraph α)
    (n nAryl carbonyl oxygen carbonylAryl : α) : Prop :=
  (g.atom n).element = .nitrogen ∧
  (g.atom n).attachedHydrogens = 1 ∧
  (g.atom carbonyl).element = .carbon ∧
  (g.atom oxygen).element = .oxygen ∧
  g.Bonded n nAryl .single ∧
  g.Bonded n carbonyl .single ∧
  g.Bonded carbonyl oxygen .double ∧
  g.Bonded carbonyl carbonylAryl .single

/-- Exact source-to-candidate structure contract for the requested drawing. -/
def MacrocycleRepeatRawResult : Prop :=
  QualitativeNamedTransformOnly depictedPostSyntheticReagents depictedDegradationReagents
      cof7RepeatInventory finalRepeatInventory ∧
  macrocycleRepeat.incomingOrder = macrocycleRepeat.outgoingOrder ∧
  boundaryCornerCount = 6 ∧
  boundaryEdgeCount = 6 ∧
  interCellBonds.length = 6 ∧
  c2HalfFormula = expectedC2HalfFormula ∧
  d4Formula = expectedD4Formula ∧
  cof7CondensedRepeatFormula = expectedCof7CondensedFormula ∧
  postSyntheticRepeatFormula = expectedPostSyntheticFormula ∧
  degradedRepeatFormula = expectedVLFormula ∧
  vlFormula = expectedVLFormula ∧
  repeatHeavyGraph.formula = expectedVLFormula ∧
  Fintype.card (ExpandedAtom repeatHeavyGraph) = 50 ∧
  repeatHeavyGraph.expandedAtomCount = 50 ∧
  macrocycleX.formula = MolecularFormula.scale 6 expectedVLFormula ∧
  macrocycleX.WellFormedClosed ∧
  IsLeastBoundaryPeriod 2 ∧
  (∀ i : Fin 6, aldehydeOrientation i = .outward) ∧
  (∀ i : Fin 6,
    HasAldehydeMotif macrocycleX
      (i, .vCore0) (i, .aldehydeC) (i, .aldehydeO)) ∧
  (∀ i : Fin 6,
    HasAmideMotif macrocycleX
      (i, .rightAmideN) (i, .rightPhenyl3)
      (i, .linkerCarbonylLeftC) (i, .linkerCarbonylLeftO) (i, .linkerRing0)) ∧
  (∀ i : Fin 6,
    HasAmideMotif macrocycleX
      (nextCell i, .leftAmideN) (nextCell i, .leftPhenyl3)
      (i, .linkerCarbonylRightC) (i, .linkerCarbonylRightO) (i, .linkerRing3))

/-- Exact-symbolic reporting makes the reported proposition identical to the raw one. -/
def MacrocycleRepeatReportedResult : Prop := MacrocycleRepeatRawResult

/-! ## Finite graph certificates used by the kernel proof -/

/-- Boolean adjacency check for the finite stored bond list. -/
def MolecularGraph.adjacentCheck {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) : Bool :=
  g.bonds.any (fun e => decide
    ((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)))

/-- Executable adjacency certificate for the finite stored bond list. -/
def MolecularGraph.Adjacent {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) : Prop :=
  g.adjacentCheck a b = true

/-- Executable certificate for a bond with a specified order. -/
def MolecularGraph.bondedCheck {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) (order : BondOrder) : Bool :=
  g.bonds.any (fun e => decide
    (((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)) ∧
      e.order = order))

lemma MolecularGraph.bonded_of_check {α : Type} [DecidableEq α]
    {g : MolecularGraph α} {a b : α} {order : BondOrder}
    (h : g.bondedCheck a b order = true) : g.Bonded a b order := by
  rw [MolecularGraph.bondedCheck, List.any_eq_true] at h
  rcases h with ⟨e, he, hchecked⟩
  have hprops :
      (((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)) ∧
        e.order = order) := of_decide_eq_true hchecked
  exact ⟨e, he, hprops.1, hprops.2⟩

/-- Boolean certificate for the absence of loops in the stored bond list. -/
def MolecularGraph.noSelfBondsCheck {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Bool :=
  g.bonds.all fun e => decide (e.left ≠ e.right)

lemma MolecularGraph.noSelfBonds_of_check {α : Type} [DecidableEq α]
    {g : MolecularGraph α} (h : g.noSelfBondsCheck = true) : g.NoSelfBonds := by
  intro e he
  have hall : ∀ e ∈ g.bonds, decide (e.left ≠ e.right) = true := by
    simpa [MolecularGraph.noSelfBondsCheck] using h
  exact of_decide_eq_true (hall e he)

/-- Boolean certificate that duplicate endpoint pairs never disagree in order. -/
def MolecularGraph.uniqueBondOrdersCheck {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Bool :=
  g.bonds.all fun e₁ =>
    g.bonds.all fun e₂ => decide
      (((e₁.left = e₂.left ∧ e₁.right = e₂.right) ∨
        (e₁.left = e₂.right ∧ e₁.right = e₂.left)) →
        e₁.order = e₂.order)

lemma MolecularGraph.uniqueBondOrders_of_check {α : Type} [DecidableEq α]
    {g : MolecularGraph α} (h : g.uniqueBondOrdersCheck = true) :
    g.UniqueBondOrders := by
  have hall : ∀ e₁ ∈ g.bonds, ∀ e₂ ∈ g.bonds,
      decide
        (((e₁.left = e₂.left ∧ e₁.right = e₂.right) ∨
          (e₁.left = e₂.right ∧ e₁.right = e₂.left)) →
          e₁.order = e₂.order) = true := by
    simpa [MolecularGraph.uniqueBondOrdersCheck] using h
  intro e₁ he₁ e₂ he₂ hconnects
  have himp :
      (((e₁.left = e₂.left ∧ e₁.right = e₂.right) ∨
        (e₁.left = e₂.right ∧ e₁.right = e₂.left)) →
        e₁.order = e₂.order) :=
    of_decide_eq_true (hall e₁ he₁ e₂ he₂)
  exact himp hconnects

/-- Boolean certificate for neutral closed-shell valence at every heavy site. -/
def MolecularGraph.neutralClosedValenceCheck {α : Type}
    [Fintype α] [DecidableEq α] (g : MolecularGraph α) : Bool :=
  @decide
    (∀ a : α,
      (g.atom a).formalCharge = 0 ∧
      (g.atom a).radicalElectrons = 0 ∧
      (g.atom a).stereochemistry = .none ∧
      g.incidentValenceUnits a + 2 * (g.atom a).attachedHydrogens =
        (g.atom a).element.neutralValenceUnits)
    Fintype.decidableForallFintype

lemma MolecularGraph.neutralClosedValence_of_check {α : Type}
    [Fintype α] [DecidableEq α] {g : MolecularGraph α}
    (h : g.neutralClosedValenceCheck = true) : g.NeutralClosedValence := by
  unfold MolecularGraph.neutralClosedValenceCheck at h
  unfold MolecularGraph.NeutralClosedValence
  exact @of_decide_eq_true _ Fintype.decidableForallFintype h

/-- Boolean check for a list of successive vertices. -/
def MolecularGraph.walkCheckFrom {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : α → List α → Bool
  | _, [] => true
  | a, b :: tail => g.adjacentCheck a b && g.walkCheckFrom b tail

/-- A checked walk, with its initial vertex supplied separately. -/
def MolecularGraph.IsWalkFrom {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a : α) (tail : List α) : Prop :=
  g.walkCheckFrom a tail = true

lemma MolecularGraph.bonded_symm {α : Type} {g : MolecularGraph α}
    {a b : α} {order : BondOrder} (h : g.Bonded a b order) :
    g.Bonded b a order := by
  rcases h with ⟨e, he, hconnects, horder⟩
  refine ⟨e, he, ?_, horder⟩
  rcases hconnects with hconnects | hconnects
  · exact Or.inr hconnects
  · exact Or.inl hconnects

lemma MolecularGraph.reachable_transitive {α : Type} {g : MolecularGraph α}
    {a b c : α} (hab : g.Reachable a b) (hbc : g.Reachable b c) :
    g.Reachable a c := by
  induction hbc with
  | refl => exact hab
  | tail h order hbond ih => exact .tail ih order hbond

lemma MolecularGraph.reachable_symmetric {α : Type} {g : MolecularGraph α}
    {a b : α} (h : g.Reachable a b) : g.Reachable b a := by
  induction h with
  | refl => exact .refl _
  | tail h order hbond ih =>
      exact g.reachable_transitive
        (.tail (.refl _) order (g.bonded_symm hbond)) ih

lemma MolecularGraph.reachable_of_adjacent {α : Type} [DecidableEq α]
    {g : MolecularGraph α}
    {a b : α} (h : g.Adjacent a b) : g.Reachable a b := by
  rw [MolecularGraph.Adjacent, MolecularGraph.adjacentCheck,
    List.any_eq_true] at h
  rcases h with ⟨e, he, hconnects⟩
  have hconnects' :
      ((e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)) :=
    of_decide_eq_true hconnects
  exact .tail (.refl _) e.order ⟨e, he, hconnects', rfl⟩

lemma MolecularGraph.reachable_of_walk_mem {α : Type} [DecidableEq α]
    {g : MolecularGraph α}
    {start v : α} {vertices : List α} (hwalk : g.IsWalkFrom start vertices)
    (hv : v = start ∨ v ∈ vertices) : g.Reachable start v := by
  induction vertices generalizing start with
  | nil =>
      simp only [List.not_mem_nil, or_false] at hv
      subst v
      exact .refl _
  | cons head tail ih =>
      have hwalk' : g.Adjacent start head ∧ g.IsWalkFrom head tail := by
        simpa [MolecularGraph.IsWalkFrom, MolecularGraph.walkCheckFrom,
          MolecularGraph.Adjacent] using hwalk
      rcases hwalk' with ⟨hstep, htail⟩
      rcases hv with hv | hv
      · subst v
        exact .refl _
      · have hv' : v = head ∨ v ∈ tail := by
          simpa only [List.mem_cons] using hv
        exact g.reachable_transitive (g.reachable_of_adjacent hstep) (ih htail hv')

/--
A depth-first walk through one `V-L` cell.  Repeated sites are the return legs
from pendant O/F atoms and from the aromatic branches.  Every heavy site occurs.
-/
def repeatWalkTail : List RepeatAtom :=
  [ .leftPhenyl3
  , .leftPhenyl2, .leftPhenyl1, .leftPhenyl0, .leftPhenyl5, .leftPhenyl4
  , .leftPhenyl3, .leftPhenyl2, .leftPhenyl1, .leftPhenyl0
  , .vCore2, .vCore1, .vCore0, .aldehydeC, .aldehydeO, .aldehydeC
  , .vCore0, .vCore5, .vCore4, .vCore3, .vCore2, .vCore3, .vCore4
  , .rightPhenyl0, .rightPhenyl1, .rightPhenyl2, .rightPhenyl3
  , .rightPhenyl4, .rightPhenyl5, .rightPhenyl0, .rightPhenyl1
  , .rightPhenyl2, .rightPhenyl3, .rightAmideN
  , .linkerCarbonylLeftC, .linkerCarbonylLeftO, .linkerCarbonylLeftC
  , .linkerRing0, .linkerRing1, .linkerFluorine1, .linkerRing1
  , .linkerRing2, .linkerFluorine2, .linkerRing2, .linkerRing3
  , .linkerRing4, .linkerFluorine4, .linkerRing4, .linkerRing5
  , .linkerFluorine5, .linkerRing5, .linkerRing0, .linkerRing1
  , .linkerRing2, .linkerRing3, .linkerCarbonylRightC
  , .linkerCarbonylRightO ]

lemma repeatWalkTail_complete (a : RepeatAtom) :
    a = .leftAmideN ∨ a ∈ repeatWalkTail := by
  fin_cases a <;> decide +kernel

def repeatCellWalkTail (i : Fin 6) : List (Fin 6 × RepeatAtom) :=
  repeatWalkTail.map fun a => (i, a)

lemma repeatCellWalkTail_valid (i : Fin 6) :
    macrocycleX.IsWalkFrom (i, .leftAmideN) (repeatCellWalkTail i) := by
  change macrocycleX.walkCheckFrom (i, .leftAmideN) (repeatCellWalkTail i) = true
  fin_cases i <;> decide +kernel

lemma repeatCell_root_reaches (i : Fin 6) (a : RepeatAtom) :
    macrocycleX.Reachable (i, .leftAmideN) (i, a) := by
  apply macrocycleX.reachable_of_walk_mem (repeatCellWalkTail_valid i)
  rcases repeatWalkTail_complete a with ha | ha
  · left
    subst a
    rfl
  · right
    exact List.mem_map_of_mem ha

lemma repeatCell_inter_bond (i : Fin 6) :
    macrocycleX.Bonded (i, .linkerCarbonylRightC)
      (nextCell i, .leftAmideN) .single := by
  apply MolecularGraph.bonded_of_check
  fin_cases i <;> decide +kernel

lemma repeatCell_root_reaches_next (i : Fin 6) :
    macrocycleX.Reachable (i, .leftAmideN) (nextCell i, .leftAmideN) := by
  exact .tail (repeatCell_root_reaches i .linkerCarbonylRightC) .single
    (repeatCell_inter_bond i)

lemma cellZero_root_reaches (j : Fin 6) :
    macrocycleX.Reachable ((0 : Fin 6), .leftAmideN) (j, .leftAmideN) := by
  have h01 : macrocycleX.Reachable ((0 : Fin 6), .leftAmideN)
      ((1 : Fin 6), .leftAmideN) := by
    simpa [nextCell] using repeatCell_root_reaches_next (0 : Fin 6)
  have h12 : macrocycleX.Reachable ((1 : Fin 6), .leftAmideN)
      ((2 : Fin 6), .leftAmideN) := by
    simpa [nextCell] using repeatCell_root_reaches_next (1 : Fin 6)
  have h23 : macrocycleX.Reachable ((2 : Fin 6), .leftAmideN)
      ((3 : Fin 6), .leftAmideN) := by
    simpa [nextCell] using repeatCell_root_reaches_next (2 : Fin 6)
  have h34 : macrocycleX.Reachable ((3 : Fin 6), .leftAmideN)
      ((4 : Fin 6), .leftAmideN) := by
    simpa [nextCell] using repeatCell_root_reaches_next (3 : Fin 6)
  have h45 : macrocycleX.Reachable ((4 : Fin 6), .leftAmideN)
      ((5 : Fin 6), .leftAmideN) := by
    simpa [nextCell] using repeatCell_root_reaches_next (4 : Fin 6)
  fin_cases j
  · exact .refl _
  · exact h01
  · exact macrocycleX.reachable_transitive h01 h12
  · exact macrocycleX.reachable_transitive
      (macrocycleX.reachable_transitive h01 h12) h23
  · exact macrocycleX.reachable_transitive
      (macrocycleX.reachable_transitive
        (macrocycleX.reachable_transitive h01 h12) h23) h34
  · exact macrocycleX.reachable_transitive
      (macrocycleX.reachable_transitive
        (macrocycleX.reachable_transitive
          (macrocycleX.reachable_transitive h01 h12) h23) h34) h45

lemma macrocycleX_roots_connected (i j : Fin 6) :
    macrocycleX.Reachable (i, .leftAmideN) (j, .leftAmideN) := by
  exact macrocycleX.reachable_transitive
    (macrocycleX.reachable_symmetric (cellZero_root_reaches i))
    (cellZero_root_reaches j)

lemma macrocycleX_connected : macrocycleX.Connected := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  exact macrocycleX.reachable_transitive
    (macrocycleX.reachable_symmetric (repeatCell_root_reaches i a))
    (macrocycleX.reachable_transitive (macrocycleX_roots_connected i j)
      (repeatCell_root_reaches j b))

lemma macrocycleX_wellFormedClosed : macrocycleX.WellFormedClosed := by
  refine ⟨macrocycleX.noSelfBonds_of_check (by decide +kernel),
    macrocycleX.uniqueBondOrders_of_check (by decide +kernel),
    macrocycleX.neutralClosedValence_of_check (by decide +kernel), ?_⟩
  exact macrocycleX_connected

lemma two_isLeastBoundaryPeriod : IsLeastBoundaryPeriod 2 := by
  refine ⟨?_, ?_⟩
  · refine ⟨by omega, by omega, ?_⟩
    intro i
    fin_cases i <;> decide +kernel
  intro q hq
  by_contra hnot
  have hpositive : 0 < q := hq.1
  have hq_eq : q = 1 := by omega
  subst q
  have hperiod_at_zero := hq.2.2 (0 : Fin 12)
  norm_num [rotateBoundary, cof7BoundaryComponent] at hperiod_at_zero
  cases hperiod_at_zero

lemma macrocycleX_has_aldehyde_motifs :
    ∀ i : Fin 6,
      HasAldehydeMotif macrocycleX
        (i, .vCore0) (i, .aldehydeC) (i, .aldehydeO) := by
  intro i
  unfold HasAldehydeMotif
  fin_cases i <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel)⟩

lemma macrocycleX_has_internal_amide_motifs :
    ∀ i : Fin 6,
      HasAmideMotif macrocycleX
        (i, .rightAmideN) (i, .rightPhenyl3)
        (i, .linkerCarbonylLeftC) (i, .linkerCarbonylLeftO) (i, .linkerRing0) := by
  intro i
  unfold HasAmideMotif
  fin_cases i <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel)⟩

lemma macrocycleX_has_cross_cell_amide_motifs :
    ∀ i : Fin 6,
      HasAmideMotif macrocycleX
        (nextCell i, .leftAmideN) (nextCell i, .leftPhenyl3)
        (i, .linkerCarbonylRightC) (i, .linkerCarbonylRightO) (i, .linkerRing3) := by
  intro i
  unfold HasAmideMotif
  fin_cases i <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel),
      MolecularGraph.bonded_of_check (by decide +kernel)⟩

/--
The smallest component period is two (`V,L`), hence one `V-L` pair.  The full
product is the sixfold cyclic assembly `cyclo[V-L]₆`, and the pair has formula
`C₂₇H₁₄F₄N₂O₃`.
-/
theorem macrocycle_repeat_raw_result : MacrocycleRepeatRawResult := by
  unfold MacrocycleRepeatRawResult
  exact
    ⟨by
       unfold QualitativeNamedTransformOnly
       decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     by decide +kernel,
     macrocycleX_wellFormedClosed,
     two_isLeastBoundaryPeriod,
     by decide +kernel,
     macrocycleX_has_aldehyde_motifs,
     macrocycleX_has_internal_amide_motifs,
     macrocycleX_has_cross_cell_amide_motifs⟩

theorem macrocycle_repeat_reported_result : MacrocycleRepeatReportedResult := by
  exact macrocycle_repeat_raw_result

end IChO2026Problems.ProblemIcho2026T3A5
