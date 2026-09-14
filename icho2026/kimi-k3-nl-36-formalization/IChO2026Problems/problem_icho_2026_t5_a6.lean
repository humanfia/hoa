import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T5.6: structures of PL2 and PL3

This file is an atom-level formalization of the two requested drawings.  The
problem explicitly asks that the hydrocarbon part of every fatty-acid residue
be abbreviated by `R`; accordingly, `AtomKind.fattyResidueR` is one auditable
pseudoatom whose expansion formula and internal bond order are supplied by the
inline derivation of part 5.3.  Every atom outside `R`, every bond order, every
formal charge, every radical count, every implicit-hydrogen multiplicity, and
every requested tetrahedral configuration is listed below.

The source hydrolyses are used quantitatively.  Their finite material domains
contain only the species printed in the reaction schemes, and the file exposes
both atom and charge ledgers.  No yield, phase, or sole-product claim is added.
-/

namespace IChO2026Problems.IChO2026T5A6

/-! ## Small local chemistry interface -/

/-- Molecular formula over exactly the elements used in T5.6. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

def zero : MolecularFormula := ⟨0, 0, 0, 0⟩

instance : Add MolecularFormula where
  add a b :=
    ⟨a.carbon + b.carbon, a.hydrogen + b.hydrogen,
      a.oxygen + b.oxygen, a.phosphorus + b.phosphorus⟩

def scale (n : ℕ) (f : MolecularFormula) : MolecularFormula :=
  ⟨n * f.carbon, n * f.hydrogen, n * f.oxygen, n * f.phosphorus⟩

end MolecularFormula

/-- The explicitly represented atom types.  `fattyResidueR` is precisely the
hydrocarbon abbreviation authorized by the question. -/
inductive AtomKind
  | hydrogen
  | carbon
  | oxygen
  | phosphorus
  | fattyResidueR
  deriving DecidableEq, Repr

/-- An atom record also accounts for hydrogens suppressed in a line drawing. -/
structure Atom where
  kind : AtomKind
  formalCharge : ℤ
  radicalElectrons : ℕ
  implicitHydrogens : ℕ
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  | triple
  deriving DecidableEq, Repr

def BondOrder.value : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

structure Bond where
  left : ℕ
  right : ℕ
  order : BondOrder
  deriving DecidableEq, Repr

inductive AbsoluteConfiguration
  | R
  | S
  deriving DecidableEq, Repr

inductive LigandRef
  | atom (index : ℕ)
  | implicitHydrogen
  deriving DecidableEq, Repr

/-- Four graph-derived ligand classes suffice for every tetrahedral carbon in
the two requested structures.  The two carbon-rooted classes are separated by
the first atom beyond the glycerol oxygen (carbonyl carbon versus phosphorus),
so merely listing four different atom indices cannot manufacture a stereocentre. -/
inductive LigandClass
  | implicitHydrogen
  | directlyBoundOxygen
  | carbonViaOxygenToAcyl
  | carbonViaOxygenToPhosphate
  deriving DecidableEq, Repr

/-- A ligand certificate carries the complete short path that determines its
class.  Every stored index is checked against the molecular graph below. -/
inductive LigandCertificate
  | implicitHydrogen
  | directlyBoundOxygen (oxygen : ℕ)
  | carbonViaOxygenToAcyl
      (carbon oxygen carbonylCarbon carbonylOxygen residue : ℕ)
  | carbonViaOxygenToPhosphate
      (carbon oxygen phosphorus oxoOxygen : ℕ)
  deriving DecidableEq, Repr

def LigandCertificate.ref : LigandCertificate → LigandRef
  | .implicitHydrogen => .implicitHydrogen
  | .directlyBoundOxygen oxygen => .atom oxygen
  | .carbonViaOxygenToAcyl carbon _ _ _ _ => .atom carbon
  | .carbonViaOxygenToPhosphate carbon _ _ _ => .atom carbon

def LigandCertificate.class : LigandCertificate → LigandClass
  | .implicitHydrogen => .implicitHydrogen
  | .directlyBoundOxygen _ => .directlyBoundOxygen
  | .carbonViaOxygenToAcyl .. => .carbonViaOxygenToAcyl
  | .carbonViaOxygenToPhosphate .. => .carbonViaOxygenToPhosphate

/-- `ligands` records four structurally checked ligand paths.  The absolute
configuration then selects one of the two drawings after stereogenicity has
been established from those paths. -/
structure StereoCentre where
  centre : ℕ
  ligands : List LigandCertificate
  configuration : AbsoluteConfiguration
  deriving DecidableEq, Repr

/-- An explicit abbreviated molecular graph. -/
structure MolecularGraph where
  atoms : List Atom
  bonds : List Bond
  stereocentres : List StereoCentre
  deriving DecidableEq, Repr

def hydrogenAtom : Atom := ⟨.hydrogen, 0, 0, 0⟩
def carbonAtom (h : ℕ) : Atom := ⟨.carbon, 0, 0, h⟩
def oxygenAtom (h : ℕ) : Atom := ⟨.oxygen, 0, 0, h⟩
def anionicOxygen : Atom := ⟨.oxygen, -1, 0, 0⟩
def phosphorusAtom : Atom := ⟨.phosphorus, 0, 0, 0⟩
def residueRAtom : Atom := ⟨.fattyResidueR, 0, 0, 0⟩

def singleBond (i j : ℕ) : Bond := ⟨i, j, .single⟩
def doubleBond (i j : ℕ) : Bond := ⟨i, j, .double⟩

def listGet? {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

def MolecularGraph.atomAt? (m : MolecularGraph) (i : ℕ) : Option Atom :=
  listGet? m.atoms i

theorem listGet?_eq_some_lt {α : Type} {xs : List α} {i : ℕ} {a : α}
    (h : listGet? xs i = some a) : i < xs.length := by
  induction xs generalizing i with
  | nil => simp [listGet?] at h
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [listGet?] at h
          simpa using Nat.succ_lt_succ (ih h)

def MolecularGraph.stereoAtList : List StereoCentre → ℕ → Option AbsoluteConfiguration
  | [], _ => none
  | s :: ss, i =>
      if s.centre = i then some s.configuration else stereoAtList ss i

def MolecularGraph.stereoAt? (m : MolecularGraph) (i : ℕ) : Option AbsoluteConfiguration :=
  stereoAtList m.stereocentres i

def Bond.connects (b : Bond) (i j : ℕ) : Prop :=
  (b.left = i ∧ b.right = j) ∨ (b.left = j ∧ b.right = i)

instance (b : Bond) (i j : ℕ) : Decidable (b.connects i j) := by
  unfold Bond.connects
  infer_instance

def Bond.key (b : Bond) : ℕ × ℕ :=
  (min b.left b.right, max b.left b.right)

def MolecularGraph.hasBond (m : MolecularGraph) (i j : ℕ) (o : BondOrder) : Prop :=
  ∃ b ∈ m.bonds, b.connects i j ∧ b.order = o

def MolecularGraph.bondOrderBetween (m : MolecularGraph) (i j : ℕ) : ℕ :=
  m.bonds.foldl
    (fun total b => if b.connects i j then total + b.order.value else total) 0

def MolecularGraph.incidentBondOrder (m : MolecularGraph) (i : ℕ) : ℕ :=
  m.bonds.foldl
    (fun total b =>
      if b.left = i ∨ b.right = i then total + b.order.value else total) 0

/-- Expansion of one displayed atom.  Hydrogens suppressed in the drawing are
counted by `implicitHydrogens`; an `R` atom expands to the derived hydrocarbon
residue formula. -/
def atomFormula (rFormula : MolecularFormula) (a : Atom) : MolecularFormula :=
  let h : MolecularFormula := ⟨0, a.implicitHydrogens, 0, 0⟩
  h + match a.kind with
    | .hydrogen => ⟨0, 1, 0, 0⟩
    | .carbon => ⟨1, 0, 0, 0⟩
    | .oxygen => ⟨0, 0, 1, 0⟩
    | .phosphorus => ⟨0, 0, 0, 1⟩
    | .fattyResidueR => rFormula

def MolecularGraph.formula (rFormula : MolecularFormula)
    (m : MolecularGraph) : MolecularFormula :=
  m.atoms.foldl (fun total a => total + atomFormula rFormula a) .zero

def Atom.hiddenBondOrder (rInternalBondOrder : ℕ) (a : Atom) : ℕ :=
  a.implicitHydrogens +
    if a.kind = .fattyResidueR then rInternalBondOrder else 0

/-- Total sigma-plus-pi bond count, including the bonds and hydrogens hidden by
the permitted `R` abbreviation. -/
def MolecularGraph.totalBondOrder (rInternalBondOrder : ℕ)
    (m : MolecularGraph) : ℕ :=
  (m.bonds.foldl (fun total b => total + b.order.value) 0) +
    (m.atoms.foldl (fun total a => total + a.hiddenBondOrder rInternalBondOrder) 0)

def MolecularGraph.totalFormalCharge (m : MolecularGraph) : ℤ :=
  m.atoms.foldl (fun total a => total + a.formalCharge) 0

def MolecularGraph.atomKindCount (m : MolecularGraph) (kind : AtomKind) : ℕ :=
  m.atoms.foldl (fun total a => if a.kind = kind then total + 1 else total) 0

def MolecularGraph.RadicalFree (m : MolecularGraph) : Prop :=
  ∀ a ∈ m.atoms, a.radicalElectrons = 0

def MolecularGraph.ContainsOnlyCHO (m : MolecularGraph) : Prop :=
  ∀ a ∈ m.atoms,
    a.kind = .carbon ∨ a.kind = .hydrogen ∨ a.kind = .oxygen

/-- For the finite C/H/O bridge domain in this problem, the printed failure to
react with catalytic hydrogen is represented by the absence of any multiple
bond available for addition. -/
def MolecularGraph.NoHydrogenatableMultipleBond (m : MolecularGraph) : Prop :=
  ∀ b ∈ m.bonds, b.order = .single

def expectedDisplayedValence (a : Atom) : Option ℕ :=
  match a.kind with
  | .hydrogen => if a.formalCharge = 0 then some 1 else none
  | .carbon => if a.formalCharge = 0 then some 4 else none
  | .oxygen =>
      if a.formalCharge = -1 then some 1
      else if a.formalCharge = 0 then some 2 else none
  | .phosphorus => if a.formalCharge = 0 then some 5 else none
  | .fattyResidueR => if a.formalCharge = 0 then some 1 else none

def MolecularGraph.ValenceSatisfied (m : MolecularGraph) : Prop :=
  ∀ i a, m.atomAt? i = some a →
    ∃ v, expectedDisplayedValence a = some v ∧
      m.incidentBondOrder i + a.implicitHydrogens = v

def LigandCertificate.ValidFor (m : MolecularGraph) (centre : ℕ) :
    LigandCertificate → Prop
  | .implicitHydrogen =>
      m.atomAt? centre = some (carbonAtom 1)
  | .directlyBoundOxygen oxygen =>
      m.atomAt? oxygen = some (oxygenAtom 0) ∧
      m.hasBond centre oxygen .single
  | .carbonViaOxygenToAcyl carbon oxygen carbonylCarbon carbonylOxygen residue =>
      m.atomAt? carbon = some (carbonAtom 2) ∧
      m.atomAt? oxygen = some (oxygenAtom 0) ∧
      m.atomAt? carbonylCarbon = some (carbonAtom 0) ∧
      m.atomAt? carbonylOxygen = some (oxygenAtom 0) ∧
      m.atomAt? residue = some residueRAtom ∧
      m.hasBond centre carbon .single ∧
      m.hasBond carbon oxygen .single ∧
      m.hasBond oxygen carbonylCarbon .single ∧
      m.hasBond carbonylCarbon carbonylOxygen .double ∧
      m.hasBond carbonylCarbon residue .single
  | .carbonViaOxygenToPhosphate carbon oxygen phosphorus oxoOxygen =>
      m.atomAt? carbon = some (carbonAtom 2) ∧
      m.atomAt? oxygen = some (oxygenAtom 0) ∧
      m.atomAt? phosphorus = some phosphorusAtom ∧
      m.atomAt? oxoOxygen = some (oxygenAtom 0) ∧
      m.hasBond centre carbon .single ∧
      m.hasBond carbon oxygen .single ∧
      m.hasBond oxygen phosphorus .single ∧
      m.hasBond phosphorus oxoOxygen .double

def StereoCentre.ValidFor (m : MolecularGraph) (s : StereoCentre) : Prop :=
  s.centre < m.atoms.length ∧
  s.ligands.length = 4 ∧
  (s.ligands.map LigandCertificate.ref).Nodup ∧
  (s.ligands.map LigandCertificate.class).Nodup ∧
  (∀ l ∈ s.ligands, l.ValidFor m s.centre) ∧
  m.atomAt? s.centre = some (carbonAtom 1)

def MolecularGraph.WellFormed (m : MolecularGraph) : Prop :=
  (∀ b ∈ m.bonds,
      b.left < m.atoms.length ∧ b.right < m.atoms.length ∧ b.left ≠ b.right) ∧
  (m.bonds.map Bond.key).Nodup ∧
  m.ValenceSatisfied ∧
  (∀ s ∈ m.stereocentres, s.ValidFor m)

def MolecularGraph.Adjacent (m : MolecularGraph) (i j : ℕ) : Prop :=
  ∃ b ∈ m.bonds, b.connects i j

inductive MolecularGraph.Reachable (m : MolecularGraph) : ℕ → ℕ → Prop
  | refl (i : ℕ) : Reachable m i i
  | step {i j k : ℕ} : m.Adjacent i j → Reachable m j k → Reachable m i k

def MolecularGraph.Connected (m : MolecularGraph) : Prop :=
  ∀ i j, i < m.atoms.length → j < m.atoms.length → m.Reachable i j

theorem MolecularGraph.adjacent_symm {m : MolecularGraph} {i j : ℕ}
    (h : m.Adjacent i j) : m.Adjacent j i := by
  rcases h with ⟨b, hb, hconn⟩
  refine ⟨b, hb, ?_⟩
  rcases hconn with hconn | hconn
  · exact Or.inr hconn
  · exact Or.inl hconn

theorem MolecularGraph.reachable_trans {m : MolecularGraph} {i j k : ℕ}
    (hij : m.Reachable i j) (hjk : m.Reachable j k) : m.Reachable i k := by
  induction hij with
  | refl => exact hjk
  | step hadj _ ih => exact .step hadj (ih hjk)

theorem MolecularGraph.reachable_symm {m : MolecularGraph} {i j : ℕ}
    (h : m.Reachable i j) : m.Reachable j i := by
  induction h with
  | refl => exact .refl _
  | @step i j k hij hjk ih =>
      exact reachable_trans ih (.step (adjacent_symm hij) (.refl _))

theorem MolecularGraph.connected_of_decreasing_parent
    (m : MolecularGraph) (parent : ℕ → ℕ)
    (hparent : ∀ i, 0 < i → i < m.atoms.length →
      m.Adjacent i (parent i) ∧ parent i < i) :
    m.Connected := by
  have toRoot : ∀ i, i < m.atoms.length → m.Reachable i 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hi
        by_cases hz : i = 0
        · subst i
          exact .refl 0
        · have hpos : 0 < i := Nat.pos_of_ne_zero hz
          rcases hparent i hpos hi with ⟨hadj, hlt⟩
          exact .step hadj (ih (parent i) hlt (Nat.lt_trans hlt hi))
  intro i j hi hj
  exact reachable_trans (toRoot i hi) (reachable_symm (toRoot j hj))

/-- For a well-formed finite simple connected graph, the edge-count equation
is the standard tree (acyclic connected graph) certificate. -/
def MolecularGraph.AbbreviatedTree (m : MolecularGraph) : Prop :=
  m.WellFormed ∧ m.Connected ∧ m.bonds.length + 1 = m.atoms.length

def MolecularGraph.NoPeroxideBond (m : MolecularGraph) : Prop :=
  ∀ b ∈ m.bonds, ¬ ∃ a₁ a₂,
    m.atomAt? b.left = some a₁ ∧ m.atomAt? b.right = some a₂ ∧
    a₁.kind = .oxygen ∧ a₂.kind = .oxygen

def flipConfiguration : AbsoluteConfiguration → AbsoluteConfiguration
  | .R => .S
  | .S => .R

def MolecularGraph.mirror (m : MolecularGraph) : MolecularGraph :=
  { m with stereocentres := m.stereocentres.map fun s =>
      { s with configuration := flipConfiguration s.configuration } }

def MolecularGraph.ActivePermutation (m : MolecularGraph) (p : ℕ → ℕ) : Prop :=
  (∀ i, i < m.atoms.length → p i < m.atoms.length) ∧
  (∀ i j, i < m.atoms.length → j < m.atoms.length → p i = p j → i = j) ∧
  (∀ j, j < m.atoms.length → ∃ i, i < m.atoms.length ∧ p i = j)

def MolecularGraph.PreservesTo (m n : MolecularGraph) (p : ℕ → ℕ) : Prop :=
  m.atoms.length = n.atoms.length ∧ m.ActivePermutation p ∧
  (∀ i, i < m.atoms.length → m.atomAt? i = n.atomAt? (p i)) ∧
  (∀ i j, i < m.atoms.length → j < m.atoms.length →
    m.bondOrderBetween i j = n.bondOrderBetween (p i) (p j)) ∧
  (∀ i, i < m.atoms.length → m.stereoAt? i = n.stereoAt? (p i))

def MolecularGraph.Isomorphic (m n : MolecularGraph) : Prop :=
  ∃ p : ℕ → ℕ, m.PreservesTo n p

/-- Chirality is represented as failure of stereo-preserving graph
superposition with the mirror, not as a freely assignable Boolean field. -/
def MolecularGraph.IsChiral (m : MolecularGraph) : Prop :=
  m.stereocentres ≠ [] ∧ ¬ m.Isomorphic m.mirror

def MolecularGraph.EnantiomerPair (m n : MolecularGraph) : Prop :=
  n = m.mirror ∧ m.IsChiral

def MolecularGraph.NontrivialAutomorphism (m : MolecularGraph)
    (p : ℕ → ℕ) : Prop :=
  m.PreservesTo m p ∧ ∃ i, i < m.atoms.length ∧ p i ≠ i

def MolecularGraph.oxygenNeighbourCount (m : MolecularGraph) (centre : ℕ) : ℕ :=
  (List.range m.atoms.length).foldl
    (fun total i =>
      if m.bondOrderBetween centre i = 1 ∧
          ∃ a, m.atomAt? i = some a ∧ a.kind = .oxygen
      then total + 1 else total) 0

/-! ## Functional groups and quantitative hydrolysis ledgers -/

def HasAtom (m : MolecularGraph) (i : ℕ) (kind : AtomKind)
    (charge : ℤ) (implicitH : ℕ) : Prop :=
  m.atomAt? i = some ⟨kind, charge, 0, implicitH⟩

structure AcylEsterSite where
  residue : ℕ
  carbonylCarbon : ℕ
  carbonylOxygen : ℕ
  esterOxygen : ℕ
  alcoholCarbon : ℕ
  deriving DecidableEq, Repr

def AcylEsterSite.ValidFor (s : AcylEsterSite) (m : MolecularGraph) : Prop :=
  HasAtom m s.residue .fattyResidueR 0 0 ∧
  HasAtom m s.carbonylCarbon .carbon 0 0 ∧
  HasAtom m s.carbonylOxygen .oxygen 0 0 ∧
  HasAtom m s.esterOxygen .oxygen 0 0 ∧
  (∃ h, HasAtom m s.alcoholCarbon .carbon 0 h) ∧
  m.hasBond s.residue s.carbonylCarbon .single ∧
  m.hasBond s.carbonylCarbon s.carbonylOxygen .double ∧
  m.hasBond s.carbonylCarbon s.esterOxygen .single ∧
  m.hasBond s.esterOxygen s.alcoholCarbon .single

structure PhosphateDiesterSite where
  phosphorus : ℕ
  oxoOxygen : ℕ
  nonEsterOxygen : ℕ
  firstEsterOxygen : ℕ
  firstAlcoholCarbon : ℕ
  secondEsterOxygen : ℕ
  secondAlcoholCarbon : ℕ
  deriving DecidableEq, Repr

def PhosphateDiesterSite.ValidFor (s : PhosphateDiesterSite)
    (m : MolecularGraph) (nonEsterCharge : ℤ) (nonEsterH : ℕ) : Prop :=
  HasAtom m s.phosphorus .phosphorus 0 0 ∧
  HasAtom m s.oxoOxygen .oxygen 0 0 ∧
  HasAtom m s.nonEsterOxygen .oxygen nonEsterCharge nonEsterH ∧
  HasAtom m s.firstEsterOxygen .oxygen 0 0 ∧
  HasAtom m s.secondEsterOxygen .oxygen 0 0 ∧
  (∃ h, HasAtom m s.firstAlcoholCarbon .carbon 0 h) ∧
  (∃ h, HasAtom m s.secondAlcoholCarbon .carbon 0 h) ∧
  m.hasBond s.phosphorus s.oxoOxygen .double ∧
  m.hasBond s.phosphorus s.nonEsterOxygen .single ∧
  m.hasBond s.phosphorus s.firstEsterOxygen .single ∧
  m.hasBond s.firstEsterOxygen s.firstAlcoholCarbon .single ∧
  m.hasBond s.phosphorus s.secondEsterOxygen .single ∧
  m.hasBond s.secondEsterOxygen s.secondAlcoholCarbon .single

structure HydrolysisSiteLedger where
  acylEsters : List AcylEsterSite
  phosphateDiesters : List PhosphateDiesterSite
  deriving DecidableEq, Repr

def HydrolysisSiteLedger.waterCount (l : HydrolysisSiteLedger) : ℕ :=
  l.acylEsters.length + 2 * l.phosphateDiesters.length

def HydrolysisSiteLedger.ValidFor (l : HydrolysisSiteLedger)
    (m : MolecularGraph) (nonEsterCharge : ℤ) (nonEsterH : ℕ) : Prop :=
  l.acylEsters.Nodup ∧ l.phosphateDiesters.Nodup ∧
  (∀ s ∈ l.acylEsters, s.ValidFor m) ∧
  (∀ s ∈ l.phosphateDiesters, s.ValidFor m nonEsterCharge nonEsterH)

inductive SpeciesRole
  | PL1
  | PL2
  | PL3NeutralRepresentative
  | water
  | fattyAcid
  | phosphoricAcid
  | glycerol
  | bridgeZ
  | ethanol
  deriving DecidableEq, Repr

inductive Phase
  | aqueous
  | liquid
  | unspecified
  deriving DecidableEq, Repr

structure MaterialTerm where
  role : SpeciesRole
  coefficient : ℕ
  molecule : MolecularGraph
  phase : Phase
  deriving DecidableEq, Repr

structure MolecularReaction where
  reactants : List MaterialTerm
  products : List MaterialTerm
  deriving DecidableEq, Repr

def MolecularReaction.formulaTotal (rFormula : MolecularFormula)
    (terms : List MaterialTerm) : MolecularFormula :=
  terms.foldl (fun total t =>
    total + MolecularFormula.scale t.coefficient (t.molecule.formula rFormula)) .zero

def MolecularReaction.chargeTotal (terms : List MaterialTerm) : ℤ :=
  terms.foldl (fun total t => total + (t.coefficient : ℤ) * t.molecule.totalFormalCharge) 0

def MolecularReaction.AtomBalanced (rFormula : MolecularFormula)
    (rxn : MolecularReaction) : Prop :=
  formulaTotal rFormula rxn.reactants = formulaTotal rFormula rxn.products

def MolecularReaction.ChargeBalanced (rxn : MolecularReaction) : Prop :=
  chargeTotal rxn.reactants = chargeTotal rxn.products

/-! ## Source-first derivation of the permitted `R` abbreviation

The following equations are the mathematical content derived from the page-1
fragment inventory and the page-3 part-5.3 observations.  They are not a
premise containing the desired T5.6 structures.
-/

/-- The four page-1 fragment multiplicities, kept separate from every proposed
PL2 or PL3 graph. -/
structure PL1FragmentInventory where
  hydrogenCaps : ℕ
  phosphateFragments : ℕ
  glycerolFragments : ℕ
  acylFragments : ℕ
  deriving DecidableEq, Repr

def sourcePL1Inventory (n : ℕ) : PL1FragmentInventory := ⟨n, 2, 3, 4⟩

def PL1FragmentInventory.fragmentCount (f : PL1FragmentInventory) : ℕ :=
  f.hydrogenCaps + f.phosphateFragments + f.glycerolFragments + f.acylFragments

/-- Page 1 shows respectively one, two, three, and one connector stubs. -/
def PL1FragmentInventory.stubCount (f : PL1FragmentInventory) : ℕ :=
  f.hydrogenCaps + 2 * f.phosphateFragments +
    3 * f.glycerolFragments + f.acylFragments

/-- Pairing all stubs into the `fragments - 1` edges of the stated connected
acyclic cardiolipin assembly. -/
def PL1FragmentInventory.FormsAcyclicConnectedAssembly
    (f : PL1FragmentInventory) : Prop :=
  f.stubCount = 2 * (f.fragmentCount - 1)

theorem sourcePL1_cap_count
    {n : ℕ} (h : (sourcePL1Inventory n).FormsAcyclicConnectedAssembly) : n = 1 := by
  simp [PL1FragmentInventory.FormsAcyclicConnectedAssembly,
    PL1FragmentInventory.stubCount, PL1FragmentInventory.fragmentCount,
    sourcePL1Inventory] at h
  omega

theorem sourcePL1_inventory_check :
    (sourcePL1Inventory 1).FormsAcyclicConnectedAssembly := by
  norm_num [PL1FragmentInventory.FormsAcyclicConnectedAssembly,
    PL1FragmentInventory.stubCount, PL1FragmentInventory.fragmentCount,
    sourcePL1Inventory]

def PreviousPartA3Constraints (acidC acidH chainDoubleBonds : ℕ) : Prop :=
  chainDoubleBonds + 1 = 3 ∧
  acidH + 2 * chainDoubleBonds = 2 * acidC ∧
  (4 * acidC + 4 * acidH + 41) + (4 * chainDoubleBonds + 6) = 255

theorem previousPartA3_unique_counts
    {acidC acidH chainDoubleBonds : ℕ}
    (h : PreviousPartA3Constraints acidC acidH chainDoubleBonds) :
    acidC = 18 ∧ acidH = 32 ∧ chainDoubleBonds = 2 := by
  unfold PreviousPartA3Constraints at h
  omega

theorem previousPartA3_candidate_check : PreviousPartA3Constraints 18 32 2 := by
  norm_num [PreviousPartA3Constraints]

/-- Formula of the hydrocarbon substituent in `RCOOH`, after removing COOH
from the source-derived `C18H32O2`. -/
def fattyResidueRFormula : MolecularFormula := ⟨17, 31, 0, 0⟩

/-- Internal sigma-plus-pi bonds hidden inside one `R = C17H31` abbreviation. -/
def fattyResidueRInternalBondOrder : ℕ := 49

theorem fattyResidue_internal_valence_ledger :
    2 * fattyResidueRInternalBondOrder + 1 =
      4 * fattyResidueRFormula.carbon + fattyResidueRFormula.hydrogen := by
  norm_num [fattyResidueRInternalBondOrder, fattyResidueRFormula]

/-! ## Explicit small hydrolysis products -/

def waterMolecule : MolecularGraph :=
  { atoms := [oxygenAtom 2]
    bonds := []
    stereocentres := [] }

def phosphoricAcidMolecule : MolecularGraph :=
  { atoms := [phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 1, oxygenAtom 1]
    bonds := [doubleBond 0 1, singleBond 0 2, singleBond 0 3, singleBond 0 4]
    stereocentres := [] }

def fattyAcidMolecule : MolecularGraph :=
  { atoms := [residueRAtom, carbonAtom 0, oxygenAtom 0, oxygenAtom 1]
    bonds := [singleBond 0 1, doubleBond 1 2, singleBond 1 3]
    stereocentres := [] }

def PreviousPartA3Spec : Prop :=
  (∀ acidC acidH chainDoubleBonds,
      PreviousPartA3Constraints acidC acidH chainDoubleBonds →
      acidC = 18 ∧ acidH = 32 ∧ chainDoubleBonds = 2) ∧
  PreviousPartA3Constraints 18 32 2 ∧
  fattyAcidMolecule.formula fattyResidueRFormula = ⟨18, 32, 2, 0⟩ ∧
  2 * fattyResidueRInternalBondOrder + 1 =
    4 * fattyResidueRFormula.carbon + fattyResidueRFormula.hydrogen

theorem previousPartA3_derived_inline : PreviousPartA3Spec := by
  exact ⟨fun _ _ _ h => previousPartA3_unique_counts h,
    previousPartA3_candidate_check, by decide,
    fattyResidue_internal_valence_ledger⟩

def glycerolMolecule : MolecularGraph :=
  { atoms :=
      [oxygenAtom 1, carbonAtom 2, carbonAtom 1,
       oxygenAtom 1, carbonAtom 2, oxygenAtom 1]
    bonds :=
      [singleBond 0 1, singleBond 1 2, singleBond 2 3,
       singleBond 2 4, singleBond 4 5]
    stereocentres := [] }

/-! The PL1 and PL2 hydrolyses consume the same eight waters and differ only
in replacing one glycerol product by `Z`.  Hence their one-bond difference
transfers to the isolated bridge.  A connected acyclic saturated diol has two
oxygens, `H = 2C + 2`, and bond-order valence sum `2B = 4C + H + 4`. -/

def PL2BridgeSourceConstraints
    (carbon hydrogen totalBondOrder : ℕ) : Prop :=
  255 + totalBondOrder = 254 + 13 ∧
  hydrogen = 2 * carbon + 2 ∧
  2 * totalBondOrder = 4 * carbon + hydrogen + 4

theorem pl2Bridge_unique_counts
    {carbon hydrogen totalBondOrder : ℕ}
    (h : PL2BridgeSourceConstraints carbon hydrogen totalBondOrder) :
    carbon = 3 ∧ hydrogen = 8 ∧ totalBondOrder = 12 := by
  unfold PL2BridgeSourceConstraints at h
  omega

theorem pl2Bridge_candidate_check : PL2BridgeSourceConstraints 3 8 12 := by
  norm_num [PL2BridgeSourceConstraints]

/-- `Z = HO-CH2-CH2-CH2-OH`, with both terminal hydroxyls explicit. -/
def propane13Diol : MolecularGraph :=
  { atoms := [oxygenAtom 1, carbonAtom 2, carbonAtom 2, carbonAtom 2, oxygenAtom 1]
    bonds := [singleBond 0 1, singleBond 1 2, singleBond 2 3, singleBond 3 4]
    stereocentres := [] }

def ethanolMolecule : MolecularGraph :=
  { atoms := [oxygenAtom 1, carbonAtom 2, carbonAtom 3]
    bonds := [singleBond 0 1, singleBond 1 2]
    stereocentres := [] }

/-! ## PL2: the complete non-ionised graph -/

/--
Index ledger for `structurePL2`:

`R0-C1(=O2)-O3-C4-C*5(-O6-C7(=O8)-R9)-C10-O11-P12`
`(=O13)(-O14H)-O15-C16-C17-C18-O19-P20(=O21)(-O22H)-O23-`
`C24-C*25(-O26-C27(=O28)-R29)-C30-O31-C32(=O33)-R34`.

Centres 5 and 25 are both assigned `(R)`; changing both to `(S)` gives the
other member of the enantiomeric pair.
-/
def structurePL2 : MolecularGraph :=
  { atoms :=
      [ residueRAtom, carbonAtom 0, oxygenAtom 0, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, oxygenAtom 0, carbonAtom 0,
        oxygenAtom 0, residueRAtom, carbonAtom 2, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 2, carbonAtom 2, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, oxygenAtom 0, carbonAtom 0,
        oxygenAtom 0, residueRAtom, carbonAtom 2, oxygenAtom 0,
        carbonAtom 0, oxygenAtom 0, residueRAtom ]
    bonds :=
      [ singleBond 0 1, doubleBond 1 2, singleBond 1 3, singleBond 3 4,
        singleBond 4 5, singleBond 5 6, singleBond 6 7, doubleBond 7 8,
        singleBond 7 9, singleBond 5 10, singleBond 10 11, singleBond 11 12,
        doubleBond 12 13, singleBond 12 14, singleBond 12 15,
        singleBond 15 16, singleBond 16 17, singleBond 17 18,
        singleBond 18 19, singleBond 19 20, doubleBond 20 21,
        singleBond 20 22, singleBond 20 23, singleBond 23 24,
        singleBond 24 25, singleBond 25 26, singleBond 26 27,
        doubleBond 27 28, singleBond 27 29, singleBond 25 30,
        singleBond 30 31, singleBond 31 32, doubleBond 32 33,
        singleBond 32 34 ]
    stereocentres :=
      [ { centre := 5
          ligands :=
            [ .directlyBoundOxygen 6,
              .carbonViaOxygenToPhosphate 10 11 12 13,
              .carbonViaOxygenToAcyl 4 3 1 2 0,
              .implicitHydrogen ]
          configuration := .R },
        { centre := 25
          ligands :=
            [ .directlyBoundOxygen 26,
              .carbonViaOxygenToPhosphate 24 23 20 21,
              .carbonViaOxygenToAcyl 30 31 32 33 34,
              .implicitHydrogen ]
          configuration := .R } ] }

def pl2HydrolysisSites : HydrolysisSiteLedger :=
  { acylEsters :=
      [ ⟨0, 1, 2, 3, 4⟩, ⟨9, 7, 8, 6, 5⟩,
        ⟨29, 27, 28, 26, 25⟩, ⟨34, 32, 33, 31, 30⟩ ]
    phosphateDiesters :=
      [ ⟨12, 13, 14, 11, 10, 15, 16⟩,
        ⟨20, 21, 22, 19, 18, 23, 24⟩ ] }

/-- The end-for-end C2 symmetry of the displayed `(R,R)` PL2 graph. -/
def pl2EndExchange : ℕ → ℕ
  | 0 => 34 | 1 => 32 | 2 => 33 | 3 => 31 | 4 => 30
  | 5 => 25 | 6 => 26 | 7 => 27 | 8 => 28 | 9 => 29
  | 10 => 24 | 11 => 23 | 12 => 20 | 13 => 21 | 14 => 22
  | 15 => 19 | 16 => 18 | 17 => 17 | 18 => 16 | 19 => 15
  | 20 => 12 | 21 => 13 | 22 => 14 | 23 => 11 | 24 => 10
  | 25 => 5 | 26 => 6 | 27 => 7 | 28 => 8 | 29 => 9
  | 30 => 4 | 31 => 3 | 32 => 1 | 33 => 2 | 34 => 0
  | n => n

/-- A parent map for the displayed heavy-atom tree.  The PL3 graph below is
the induced initial subtree on indices `0, ..., 17`. -/
def displayedTreeParent : ℕ → ℕ
  | 0 => 0
  | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 4
  | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 7 | 10 => 5
  | 11 => 10 | 12 => 11 | 13 => 12 | 14 => 12 | 15 => 12
  | 16 => 15 | 17 => 16 | 18 => 17 | 19 => 18 | 20 => 19
  | 21 => 20 | 22 => 20 | 23 => 20 | 24 => 23 | 25 => 24
  | 26 => 25 | 27 => 26 | 28 => 27 | 29 => 27 | 30 => 25
  | 31 => 30 | 32 => 31 | 33 => 32 | 34 => 32
  | 35 => 17
  | _ => 0

def displayedTreeParentBond (i : ℕ) : Bond :=
  if i = 2 ∨ i = 8 ∨ i = 13 ∨ i = 21 ∨ i = 28 ∨ i = 33 then
    doubleBond (displayedTreeParent i) i
  else
    singleBond (displayedTreeParent i) i

def MolecularGraph.atomAtDefault (m : MolecularGraph) (i : ℕ) : Atom :=
  (m.atomAt? i).getD hydrogenAtom

theorem structurePL2_parent_certificate :
    ∀ i : Fin 35, 0 < i.1 →
      displayedTreeParentBond i.1 ∈ structurePL2.bonds ∧
      (displayedTreeParentBond i.1).connects i.1 (displayedTreeParent i.1) ∧
      displayedTreeParent i.1 < i.1 := by
  decide

theorem structurePL2_valence_certificate :
    ∀ i : Fin 35,
      structurePL2.atomAt? i.1 = some (structurePL2.atomAtDefault i.1) ∧
      expectedDisplayedValence (structurePL2.atomAtDefault i.1) =
        some (structurePL2.incidentBondOrder i.1 +
          (structurePL2.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem structurePL2_connected : structurePL2.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent structurePL2 displayedTreeParent
  intro i hpos hlt
  have hi35 : i < 35 := by simpa [structurePL2] using hlt
  have hcert := structurePL2_parent_certificate ⟨i, hi35⟩ hpos
  exact ⟨⟨displayedTreeParentBond i, hcert.1, hcert.2.1⟩, hcert.2.2⟩

theorem structurePL2_valenceSatisfied : structurePL2.ValenceSatisfied := by
  intro i a hi
  have hlt : i < structurePL2.atoms.length := listGet?_eq_some_lt hi
  have hi35 : i < 35 := by simpa [structurePL2] using hlt
  rcases structurePL2_valence_certificate ⟨i, hi35⟩ with ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem structurePL2_wellFormed : structurePL2.WellFormed := by
  refine ⟨?_, ?_, structurePL2_valenceSatisfied, ?_⟩
  · simp [structurePL2, singleBond, doubleBond]
  · decide
  · simp [structurePL2, StereoCentre.ValidFor, LigandCertificate.ValidFor,
      LigandCertificate.ref, LigandCertificate.class,
      MolecularGraph.atomAt?, listGet?, MolecularGraph.hasBond,
      Bond.connects, singleBond, doubleBond, carbonAtom, oxygenAtom,
      phosphorusAtom, residueRAtom]

theorem structurePL2_abbreviatedTree : structurePL2.AbbreviatedTree := by
  exact ⟨structurePL2_wellFormed, structurePL2_connected, by decide⟩

theorem structurePL2_isChiral : structurePL2.IsChiral := by
  refine ⟨by simp [structurePL2], ?_⟩
  rintro ⟨p, hp⟩
  have hstereo := hp.2.2.2.2 5 (by decide)
  simp [structurePL2, MolecularGraph.mirror, MolecularGraph.stereoAt?,
    MolecularGraph.stereoAtList, flipConfiguration] at hstereo
  split_ifs at hstereo <;> simp_all

theorem pl2EndExchange_bound_certificate :
    ∀ i : Fin 35, pl2EndExchange i.1 < 35 := by
  decide

theorem pl2EndExchange_involutive_certificate :
    ∀ i : Fin 35, pl2EndExchange (pl2EndExchange i.1) = i.1 := by
  decide

theorem pl2EndExchange_atoms_certificate :
    ∀ i : Fin 35,
      structurePL2.atomAt? i.1 = structurePL2.atomAt? (pl2EndExchange i.1) := by
  decide

theorem pl2EndExchange_bonds_certificate :
    ∀ i : Fin 35, ∀ j : Fin 35,
      structurePL2.bondOrderBetween i.1 j.1 =
        structurePL2.bondOrderBetween (pl2EndExchange i.1) (pl2EndExchange j.1) := by
  decide

theorem pl2EndExchange_stereo_certificate :
    ∀ i : Fin 35,
      structurePL2.stereoAt? i.1 = structurePL2.stereoAt? (pl2EndExchange i.1) := by
  decide

theorem pl2EndExchange_active : structurePL2.ActivePermutation pl2EndExchange := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi35 : i < 35 := by simpa [structurePL2] using hi
    simpa [structurePL2] using pl2EndExchange_bound_certificate ⟨i, hi35⟩
  · intro i j hi hj hij
    have hi35 : i < 35 := by simpa [structurePL2] using hi
    have hj35 : j < 35 := by simpa [structurePL2] using hj
    calc
      i = pl2EndExchange (pl2EndExchange i) :=
        (pl2EndExchange_involutive_certificate ⟨i, hi35⟩).symm
      _ = pl2EndExchange (pl2EndExchange j) := congrArg pl2EndExchange hij
      _ = j := pl2EndExchange_involutive_certificate ⟨j, hj35⟩
  · intro j hj
    have hj35 : j < 35 := by simpa [structurePL2] using hj
    refine ⟨pl2EndExchange j, ?_, ?_⟩
    · simpa [structurePL2] using pl2EndExchange_bound_certificate ⟨j, hj35⟩
    · exact pl2EndExchange_involutive_certificate ⟨j, hj35⟩

theorem pl2EndExchange_preserves : structurePL2.PreservesTo structurePL2 pl2EndExchange := by
  refine ⟨rfl, pl2EndExchange_active, ?_, ?_, ?_⟩
  · intro i hi
    exact pl2EndExchange_atoms_certificate
      ⟨i, by simpa [structurePL2] using hi⟩
  · intro i j hi hj
    exact pl2EndExchange_bonds_certificate
      ⟨i, by simpa [structurePL2] using hi⟩
      ⟨j, by simpa [structurePL2] using hj⟩
  · intro i hi
    exact pl2EndExchange_stereo_certificate
      ⟨i, by simpa [structurePL2] using hi⟩

theorem structurePL2_nontrivialAutomorphism :
    structurePL2.NontrivialAutomorphism pl2EndExchange := by
  exact ⟨pl2EndExchange_preserves, ⟨0, by decide, by decide⟩⟩

def chainParent : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

theorem propane13Diol_parent_certificate :
    ∀ i : Fin 5, 0 < i.1 →
      singleBond (chainParent i.1) i.1 ∈ propane13Diol.bonds ∧
      (singleBond (chainParent i.1) i.1).connects i.1 (chainParent i.1) ∧
      chainParent i.1 < i.1 := by
  decide

theorem propane13Diol_valence_certificate :
    ∀ i : Fin 5,
      propane13Diol.atomAt? i.1 = some (propane13Diol.atomAtDefault i.1) ∧
      expectedDisplayedValence (propane13Diol.atomAtDefault i.1) =
        some (propane13Diol.incidentBondOrder i.1 +
          (propane13Diol.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem propane13Diol_connected : propane13Diol.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent propane13Diol chainParent
  intro i hpos hlt
  have hi5 : i < 5 := by simpa [propane13Diol] using hlt
  have hcert := propane13Diol_parent_certificate ⟨i, hi5⟩ hpos
  exact ⟨⟨singleBond (chainParent i) i, hcert.1, hcert.2.1⟩, hcert.2.2⟩

theorem propane13Diol_valenceSatisfied : propane13Diol.ValenceSatisfied := by
  intro i a hi
  have hlt : i < propane13Diol.atoms.length := listGet?_eq_some_lt hi
  have hi5 : i < 5 := by simpa [propane13Diol] using hlt
  rcases propane13Diol_valence_certificate ⟨i, hi5⟩ with ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem propane13Diol_wellFormed : propane13Diol.WellFormed := by
  refine ⟨?_, ?_, propane13Diol_valenceSatisfied, ?_⟩
  · simp [propane13Diol, singleBond]
  · decide
  · simp [propane13Diol]

theorem propane13Diol_abbreviatedTree : propane13Diol.AbbreviatedTree := by
  exact ⟨propane13Diol_wellFormed, propane13Diol_connected, by decide⟩

/-! ## Independent inline derivation of previous part 5.2

This graph is assembled directly from the page-1 fragment inventory.  In
particular, it is not defined by editing either requested T5.6 output.  The
index order is chosen to make the common phosphatidyl arms easy to audit.
-/

def replaceAt {α : Type} : List α → ℕ → α → List α
  | [], _, _ => []
  | _ :: xs, 0, a => a :: xs
  | x :: xs, n + 1, a => x :: replaceAt xs n a

theorem listGet?_replaceAt_of_ne {α : Type} (xs : List α) (i j : ℕ) (a : α)
    (hij : i ≠ j) : listGet? (replaceAt xs j a) i = listGet? xs i := by
  induction xs generalizing i j with
  | nil => simp [replaceAt, listGet?]
  | cons x xs ih =>
      cases i <;> cases j <;> simp_all [replaceAt, listGet?]

/-- One `(R,R)` non-ionised PL1 assembled independently from four acyl
fragments, two phosphate fragments, and three glycerol fragments.  Atom 35 is
the sole central-glycerol hydroxyl oxygen. -/
def previousPartPL1 : MolecularGraph :=
  { atoms :=
      [ residueRAtom, carbonAtom 0, oxygenAtom 0, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, oxygenAtom 0, carbonAtom 0,
        oxygenAtom 0, residueRAtom, carbonAtom 2, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, carbonAtom 2, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, oxygenAtom 0, carbonAtom 0,
        oxygenAtom 0, residueRAtom, carbonAtom 2, oxygenAtom 0,
        carbonAtom 0, oxygenAtom 0, residueRAtom, oxygenAtom 1 ]
    bonds :=
      [ singleBond 0 1, doubleBond 1 2, singleBond 1 3, singleBond 3 4,
        singleBond 4 5, singleBond 5 6, singleBond 6 7, doubleBond 7 8,
        singleBond 7 9, singleBond 5 10, singleBond 10 11, singleBond 11 12,
        doubleBond 12 13, singleBond 12 14, singleBond 12 15,
        singleBond 15 16, singleBond 16 17, singleBond 17 18,
        singleBond 18 19, singleBond 19 20, doubleBond 20 21,
        singleBond 20 22, singleBond 20 23, singleBond 23 24,
        singleBond 24 25, singleBond 25 26, singleBond 26 27,
        doubleBond 27 28, singleBond 27 29, singleBond 25 30,
        singleBond 30 31, singleBond 31 32, doubleBond 32 33,
        singleBond 32 34, singleBond 17 35 ]
    stereocentres :=
      [ { centre := 5
          ligands :=
            [ .directlyBoundOxygen 6,
              .carbonViaOxygenToPhosphate 10 11 12 13,
              .carbonViaOxygenToAcyl 4 3 1 2 0,
              .implicitHydrogen ]
          configuration := .R },
        { centre := 25
          ligands :=
            [ .directlyBoundOxygen 26,
              .carbonViaOxygenToPhosphate 24 23 20 21,
              .carbonViaOxygenToAcyl 30 31 32 33 34,
              .implicitHydrogen ]
          configuration := .R } ] }

theorem previousPartPL1_parent_certificate :
    ∀ i : Fin 36, 0 < i.1 →
      displayedTreeParentBond i.1 ∈ previousPartPL1.bonds ∧
      (displayedTreeParentBond i.1).connects i.1 (displayedTreeParent i.1) ∧
      displayedTreeParent i.1 < i.1 := by
  decide

theorem previousPartPL1_valence_certificate :
    ∀ i : Fin 36,
      previousPartPL1.atomAt? i.1 =
        some (previousPartPL1.atomAtDefault i.1) ∧
      expectedDisplayedValence (previousPartPL1.atomAtDefault i.1) =
        some (previousPartPL1.incidentBondOrder i.1 +
          (previousPartPL1.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem previousPartPL1_connected : previousPartPL1.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent
    previousPartPL1 displayedTreeParent
  intro i hpos hlt
  have hi36 : i < 36 := by simpa [previousPartPL1] using hlt
  have hcert := previousPartPL1_parent_certificate ⟨i, hi36⟩ hpos
  exact ⟨⟨displayedTreeParentBond i, hcert.1, hcert.2.1⟩, hcert.2.2⟩

theorem previousPartPL1_valenceSatisfied : previousPartPL1.ValenceSatisfied := by
  intro i a hi
  have hlt : i < previousPartPL1.atoms.length := listGet?_eq_some_lt hi
  have hi36 : i < 36 := by simpa [previousPartPL1] using hlt
  rcases previousPartPL1_valence_certificate ⟨i, hi36⟩ with
    ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem previousPartPL1_wellFormed : previousPartPL1.WellFormed := by
  refine ⟨?_, ?_, previousPartPL1_valenceSatisfied, ?_⟩
  · simp [previousPartPL1, singleBond, doubleBond]
  · decide
  · simp [previousPartPL1, StereoCentre.ValidFor,
      LigandCertificate.ValidFor, LigandCertificate.ref,
      LigandCertificate.class, MolecularGraph.atomAt?, listGet?,
      MolecularGraph.hasBond, Bond.connects, singleBond, doubleBond,
      carbonAtom, oxygenAtom, phosphorusAtom, residueRAtom]

theorem previousPartPL1_abbreviatedTree : previousPartPL1.AbbreviatedTree := by
  exact ⟨previousPartPL1_wellFormed, previousPartPL1_connected, by decide⟩

theorem previousPartPL1_noPeroxideBond : previousPartPL1.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, previousPartPL1,
    MolecularGraph.atomAt?, listGet?, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem previousPartPL1_radicalFree : previousPartPL1.RadicalFree := by
  simp [MolecularGraph.RadicalFree, previousPartPL1, residueRAtom,
    carbonAtom, oxygenAtom, phosphorusAtom]

/-- One equivalent representative of monoanion Y: the right phosphate oxygen
22 is deprotonated. -/
def previousPartMonoanionY : MolecularGraph :=
  { previousPartPL1 with
    atoms := replaceAt previousPartPL1.atoms 22 anionicOxygen }

structure HydrogenBond where
  donorOxygen : ℕ
  acceptorOxygen : ℕ
  deriving DecidableEq, Repr

def HydrogenBond.ValidFor (h : HydrogenBond) (m : MolecularGraph) : Prop :=
  (∃ a, m.atomAt? h.donorOxygen = some a ∧
    a.kind = .oxygen ∧ 0 < a.implicitHydrogens) ∧
  (∃ a, m.atomAt? h.acceptorOxygen = some a ∧ a.kind = .oxygen)

def previousPartYProtonRelay : List HydrogenBond :=
  [⟨14, 35⟩, ⟨35, 22⟩]

theorem previousPartPL1_isChiral : previousPartPL1.IsChiral := by
  refine ⟨by simp [previousPartPL1], ?_⟩
  rintro ⟨p, hp⟩
  have hstereo := hp.2.2.2.2 5 (by decide)
  simp [previousPartPL1, MolecularGraph.mirror,
    MolecularGraph.stereoAt?, MolecularGraph.stereoAtList,
    flipConfiguration] at hstereo
  split_ifs at hstereo <;> simp_all

def previousPartPL1HydrolysisSites : HydrolysisSiteLedger :=
  { acylEsters :=
      [ ⟨0, 1, 2, 3, 4⟩, ⟨9, 7, 8, 6, 5⟩,
        ⟨29, 27, 28, 26, 25⟩, ⟨34, 32, 33, 31, 30⟩ ]
    phosphateDiesters :=
      [ ⟨12, 13, 14, 11, 10, 15, 16⟩,
        ⟨20, 21, 22, 19, 18, 23, 24⟩ ] }

def previousPartPL1HydrolysisReaction : MolecularReaction :=
  { reactants :=
      [⟨.PL1, 1, previousPartPL1, .unspecified⟩,
       ⟨.water, 8, waterMolecule, .unspecified⟩]
    products :=
      [⟨.fattyAcid, 4, fattyAcidMolecule, .unspecified⟩,
       ⟨.phosphoricAcid, 2, phosphoricAcidMolecule, .unspecified⟩,
       ⟨.glycerol, 3, glycerolMolecule, .unspecified⟩] }

theorem previousPartPL1HydrolysisSites_valid :
    previousPartPL1HydrolysisSites.ValidFor previousPartPL1 0 1 := by
  simp [HydrolysisSiteLedger.ValidFor, previousPartPL1HydrolysisSites,
    AcylEsterSite.ValidFor, PhosphateDiesterSite.ValidFor, HasAtom,
    previousPartPL1, MolecularGraph.atomAt?, listGet?,
    MolecularGraph.hasBond, Bond.connects, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

def PreviousPartA2Spec : Prop :=
  (sourcePL1Inventory 1).FormsAcyclicConnectedAssembly ∧
  previousPartPL1.AbbreviatedTree ∧ previousPartPL1.NoPeroxideBond ∧
  previousPartPL1.RadicalFree ∧
  previousPartPL1.atomKindCount .fattyResidueR = 4 ∧
  previousPartPL1.atomKindCount .phosphorus = 2 ∧
  previousPartPL1.formula fattyResidueRFormula = ⟨81, 142, 17, 2⟩ ∧
  previousPartPL1.totalBondOrder fattyResidueRInternalBondOrder = 255 ∧
  previousPartPL1.IsChiral ∧
  previousPartPL1HydrolysisSites.ValidFor previousPartPL1 0 1 ∧
  previousPartPL1HydrolysisSites.waterCount = 8 ∧
  previousPartPL1HydrolysisReaction.AtomBalanced fattyResidueRFormula ∧
  previousPartPL1HydrolysisReaction.ChargeBalanced ∧
  previousPartMonoanionY.totalFormalCharge = -1 ∧
  (∀ h ∈ previousPartYProtonRelay, h.ValidFor previousPartMonoanionY) ∧
  previousPartYProtonRelay = [⟨14, 35⟩, ⟨35, 22⟩]

theorem previousPartA2_derived_inline : PreviousPartA2Spec := by
  refine ⟨sourcePL1_inventory_check, previousPartPL1_abbreviatedTree,
    previousPartPL1_noPeroxideBond, previousPartPL1_radicalFree,
    by decide, by decide, by decide, by decide, previousPartPL1_isChiral,
    previousPartPL1HydrolysisSites_valid, by decide,
    by unfold MolecularReaction.AtomBalanced; decide,
    by unfold MolecularReaction.ChargeBalanced; decide,
    by decide, ?_, rfl⟩
  simp [previousPartYProtonRelay, HydrogenBond.ValidFor,
    previousPartMonoanionY, previousPartPL1, replaceAt,
    MolecularGraph.atomAt?, listGet?, oxygenAtom, carbonAtom, anionicOxygen,
    phosphorusAtom, residueRAtom]

/-- A bilateral bridge symmetry is witnessed by an actual graph automorphism
that exchanges the two terminal bridge carbons and fixes the middle carbon. -/
def HasBilateralThreeCarbonBridgeSymmetry (m : MolecularGraph) : Prop :=
  ∃ p : ℕ → ℕ, m.NontrivialAutomorphism p ∧
    p 16 = 18 ∧ p 18 = 16 ∧ p 17 = 17

/-- The source's qualitative “more symmetrical than PL1” is made auditable as
bilateral end exchange together with removal of PL1's unique central bridge
heteroatom branch.  This is a transparent graph comparison, not a Boolean
field that the proposed molecule may set. -/
def MoreSymmetricalThanPL1Witness (m : MolecularGraph) : Prop :=
  HasBilateralThreeCarbonBridgeSymmetry m ∧
  m.atomAt? 17 = some (carbonAtom 2) ∧
  previousPartPL1.atomAt? 17 = some (carbonAtom 1) ∧
  m.oxygenNeighbourCount 17 < previousPartPL1.oxygenNeighbourCount 17

def pl2HydrolysisReaction (m z : MolecularGraph) : MolecularReaction :=
  { reactants :=
      [⟨.PL2, 1, m, .unspecified⟩, ⟨.water, 8, waterMolecule, .unspecified⟩]
    products :=
      [⟨.fattyAcid, 4, fattyAcidMolecule, .unspecified⟩,
       ⟨.phosphoricAcid, 2, phosphoricAcidMolecule, .unspecified⟩,
       ⟨.bridgeZ, 1, z, .unspecified⟩,
       ⟨.glycerol, 2, glycerolMolecule, .unspecified⟩] }

def PL2StructureSpec (m z : MolecularGraph) : Prop :=
  m.AbbreviatedTree ∧ m.NoPeroxideBond ∧ m.RadicalFree ∧
  m.formula fattyResidueRFormula = ⟨81, 142, 16, 2⟩ ∧
  m.totalFormalCharge = 0 ∧
  m.totalBondOrder fattyResidueRInternalBondOrder = 254 ∧
  m.stereocentres.length = 2 ∧
  m.stereoAt? 5 = some .R ∧ m.stereoAt? 25 = some .R ∧ m.IsChiral ∧
  MoreSymmetricalThanPL1Witness m ∧
  (∀ carbon hydrogen totalBondOrder,
      PL2BridgeSourceConstraints carbon hydrogen totalBondOrder →
      carbon = 3 ∧ hydrogen = 8 ∧ totalBondOrder = 12) ∧
  PL2BridgeSourceConstraints 3 8 12 ∧
  z.AbbreviatedTree ∧ z.formula fattyResidueRFormula = ⟨3, 8, 2, 0⟩ ∧
  z.totalBondOrder 0 = 12 ∧
  z.totalFormalCharge = 0 ∧ z.RadicalFree ∧ z.ContainsOnlyCHO ∧
  z.NoHydrogenatableMultipleBond ∧
  pl2HydrolysisSites.ValidFor m 0 1 ∧
  pl2HydrolysisSites.waterCount = 8 ∧
  (pl2HydrolysisReaction m z).AtomBalanced fattyResidueRFormula ∧
  (pl2HydrolysisReaction m z).ChargeBalanced

/-- Raw exact-symbolic carrier for requested output `structure_pl2`. -/
def StructurePL2RawResult : Prop :=
  PreviousPartA2Spec ∧ PreviousPartA3Spec ∧
    PL2StructureSpec structurePL2 propane13Diol

/-- Reported exact-symbolic carrier; exact symbolic outputs perform no
rounding, so it has the same chemical proposition as the raw carrier. -/
def StructurePL2ReportedResult : Prop :=
  PreviousPartA2Spec ∧ PreviousPartA3Spec ∧
    PL2StructureSpec structurePL2 propane13Diol

theorem structurePL2_noPeroxideBond : structurePL2.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, structurePL2,
    MolecularGraph.atomAt?, listGet?, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem structurePL2_radicalFree : structurePL2.RadicalFree := by
  simp [MolecularGraph.RadicalFree, structurePL2, residueRAtom, carbonAtom,
    oxygenAtom, phosphorusAtom]

theorem propane13Diol_radicalFree : propane13Diol.RadicalFree := by
  simp [MolecularGraph.RadicalFree, propane13Diol, carbonAtom, oxygenAtom]

theorem propane13Diol_containsOnlyCHO : propane13Diol.ContainsOnlyCHO := by
  simp [MolecularGraph.ContainsOnlyCHO, propane13Diol, carbonAtom, oxygenAtom]

theorem propane13Diol_noHydrogenatableMultipleBond :
    propane13Diol.NoHydrogenatableMultipleBond := by
  simp [MolecularGraph.NoHydrogenatableMultipleBond, propane13Diol, singleBond]

theorem structurePL2_moreSymmetricalThanPL1 :
    MoreSymmetricalThanPL1Witness structurePL2 := by
  exact ⟨⟨pl2EndExchange, structurePL2_nontrivialAutomorphism,
    by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

theorem pl2HydrolysisSites_valid :
    pl2HydrolysisSites.ValidFor structurePL2 0 1 := by
  simp [HydrolysisSiteLedger.ValidFor, pl2HydrolysisSites,
    AcylEsterSite.ValidFor, PhosphateDiesterSite.ValidFor, HasAtom,
    structurePL2, MolecularGraph.atomAt?, listGet?, MolecularGraph.hasBond,
    Bond.connects, singleBond, doubleBond, residueRAtom, carbonAtom,
    oxygenAtom, phosphorusAtom]

theorem structurePL2_raw_result : StructurePL2RawResult := by
  refine ⟨previousPartA2_derived_inline, previousPartA3_derived_inline, ?_⟩
  exact ⟨structurePL2_abbreviatedTree, structurePL2_noPeroxideBond,
    structurePL2_radicalFree, by decide, by decide,
    by decide, by decide, by decide, by decide,
    structurePL2_isChiral, structurePL2_moreSymmetricalThanPL1,
    (fun _ _ _ h => pl2Bridge_unique_counts h), pl2Bridge_candidate_check,
    propane13Diol_abbreviatedTree, by decide, by decide, by decide,
    propane13Diol_radicalFree, propane13Diol_containsOnlyCHO,
    propane13Diol_noHydrogenatableMultipleBond, pl2HydrolysisSites_valid,
    by decide,
    by unfold MolecularReaction.AtomBalanced; decide,
    by unfold MolecularReaction.ChargeBalanced; decide⟩

theorem structurePL2_reported_result : StructurePL2ReportedResult := by
  exact structurePL2_raw_result

theorem structurePL2_enantiomer_pair :
    structurePL2.EnantiomerPair structurePL2.mirror := by
  exact ⟨rfl, structurePL2_isChiral⟩

/-! ## PL3: neutral hydrolysis representative and physiological monoanion -/

/--
Index ledger for PL3:

`R0-C1(=O2)-O3-C4-C*5(-O6-C7(=O8)-R9)-C10-O11-P12`
`(=O13)(-O14)-O15-C16-C17`.

Atom 14 is `OH` in `structurePL3Neutral` and `O^-` in the requested
physiological structure.  Centre 5 is `(R)` in the displayed enantiomer.
-/
def structurePL3Neutral : MolecularGraph :=
  { atoms :=
      [ residueRAtom, carbonAtom 0, oxygenAtom 0, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, oxygenAtom 0, carbonAtom 0,
        oxygenAtom 0, residueRAtom, carbonAtom 2, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 3 ]
    bonds :=
      [ singleBond 0 1, doubleBond 1 2, singleBond 1 3, singleBond 3 4,
        singleBond 4 5, singleBond 5 6, singleBond 6 7, doubleBond 7 8,
        singleBond 7 9, singleBond 5 10, singleBond 10 11,
        singleBond 11 12, doubleBond 12 13, singleBond 12 14,
        singleBond 12 15, singleBond 15 16, singleBond 16 17 ]
    stereocentres :=
      [ { centre := 5
          ligands :=
            [ .directlyBoundOxygen 6,
              .carbonViaOxygenToPhosphate 10 11 12 13,
              .carbonViaOxygenToAcyl 4 3 1 2 0,
              .implicitHydrogen ]
          configuration := .R } ] }

/-- The structure requested under the printed physiological-pH condition. -/
def structurePL3 : MolecularGraph :=
  { structurePL3Neutral with
    atoms := replaceAt structurePL3Neutral.atoms 14 anionicOxygen }

theorem structurePL3Neutral_parent_certificate :
    ∀ i : Fin 18, 0 < i.1 →
      displayedTreeParentBond i.1 ∈ structurePL3Neutral.bonds ∧
      (displayedTreeParentBond i.1).connects i.1 (displayedTreeParent i.1) ∧
      displayedTreeParent i.1 < i.1 := by
  decide

theorem structurePL3Neutral_valence_certificate :
    ∀ i : Fin 18,
      structurePL3Neutral.atomAt? i.1 =
        some (structurePL3Neutral.atomAtDefault i.1) ∧
      expectedDisplayedValence (structurePL3Neutral.atomAtDefault i.1) =
        some (structurePL3Neutral.incidentBondOrder i.1 +
          (structurePL3Neutral.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem structurePL3_valence_certificate :
    ∀ i : Fin 18,
      structurePL3.atomAt? i.1 = some (structurePL3.atomAtDefault i.1) ∧
      expectedDisplayedValence (structurePL3.atomAtDefault i.1) =
        some (structurePL3.incidentBondOrder i.1 +
          (structurePL3.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem structurePL3Neutral_connected : structurePL3Neutral.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent
    structurePL3Neutral displayedTreeParent
  intro i hpos hlt
  have hi18 : i < 18 := by simpa [structurePL3Neutral] using hlt
  have hcert := structurePL3Neutral_parent_certificate ⟨i, hi18⟩ hpos
  exact ⟨⟨displayedTreeParentBond i, hcert.1, hcert.2.1⟩, hcert.2.2⟩

theorem structurePL3_connected : structurePL3.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent structurePL3 displayedTreeParent
  intro i hpos hlt
  have hi18 : i < 18 := by
    simpa [structurePL3, structurePL3Neutral, replaceAt] using hlt
  have hcert := structurePL3Neutral_parent_certificate ⟨i, hi18⟩ hpos
  refine ⟨⟨displayedTreeParentBond i, ?_, hcert.2.1⟩, hcert.2.2⟩
  simpa [structurePL3] using hcert.1

theorem structurePL3Neutral_valenceSatisfied :
    structurePL3Neutral.ValenceSatisfied := by
  intro i a hi
  have hlt : i < structurePL3Neutral.atoms.length := listGet?_eq_some_lt hi
  have hi18 : i < 18 := by simpa [structurePL3Neutral] using hlt
  rcases structurePL3Neutral_valence_certificate ⟨i, hi18⟩ with
    ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem structurePL3_valenceSatisfied : structurePL3.ValenceSatisfied := by
  intro i a hi
  have hlt : i < structurePL3.atoms.length := listGet?_eq_some_lt hi
  have hi18 : i < 18 := by
    simpa [structurePL3, structurePL3Neutral, replaceAt] using hlt
  rcases structurePL3_valence_certificate ⟨i, hi18⟩ with ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem structurePL3Neutral_wellFormed : structurePL3Neutral.WellFormed := by
  refine ⟨?_, ?_, structurePL3Neutral_valenceSatisfied, ?_⟩
  · simp [structurePL3Neutral, singleBond, doubleBond]
  · decide
  · simp [structurePL3Neutral, StereoCentre.ValidFor,
      LigandCertificate.ValidFor, LigandCertificate.ref,
      LigandCertificate.class,
      MolecularGraph.atomAt?, listGet?, MolecularGraph.hasBond,
      Bond.connects, singleBond, doubleBond, carbonAtom, oxygenAtom,
      phosphorusAtom, residueRAtom]

theorem structurePL3_wellFormed : structurePL3.WellFormed := by
  refine ⟨?_, ?_, structurePL3_valenceSatisfied, ?_⟩
  · simp [structurePL3, structurePL3Neutral, replaceAt, singleBond, doubleBond]
  · decide
  · simp [structurePL3, structurePL3Neutral, replaceAt, StereoCentre.ValidFor,
      LigandCertificate.ValidFor, LigandCertificate.ref,
      LigandCertificate.class, MolecularGraph.atomAt?, listGet?,
      MolecularGraph.hasBond, Bond.connects, singleBond, doubleBond,
      carbonAtom, oxygenAtom, anionicOxygen, phosphorusAtom, residueRAtom]

theorem structurePL3Neutral_abbreviatedTree :
    structurePL3Neutral.AbbreviatedTree := by
  exact ⟨structurePL3Neutral_wellFormed, structurePL3Neutral_connected,
    by decide⟩

theorem structurePL3_abbreviatedTree : structurePL3.AbbreviatedTree := by
  exact ⟨structurePL3_wellFormed, structurePL3_connected, by decide⟩

theorem structurePL3_isChiral : structurePL3.IsChiral := by
  refine ⟨by simp [structurePL3, structurePL3Neutral], ?_⟩
  rintro ⟨p, hp⟩
  have hstereo := hp.2.2.2.2 5 (by decide)
  simp [structurePL3, structurePL3Neutral, MolecularGraph.mirror,
    MolecularGraph.stereoAt?, MolecularGraph.stereoAtList,
    flipConfiguration] at hstereo

def pl3NeutralHydrolysisSites : HydrolysisSiteLedger :=
  { acylEsters := [⟨0, 1, 2, 3, 4⟩, ⟨9, 7, 8, 6, 5⟩]
    phosphateDiesters := [⟨12, 13, 14, 11, 10, 15, 16⟩] }

def IsSingleODeprotonationAt (acid base : MolecularGraph) (oxygenIndex : ℕ) : Prop :=
  acid.atoms.length = base.atoms.length ∧
  acid.bonds = base.bonds ∧ acid.stereocentres = base.stereocentres ∧
  (∀ i, i ≠ oxygenIndex → acid.atomAt? i = base.atomAt? i) ∧
  HasAtom acid oxygenIndex .oxygen 0 1 ∧
  HasAtom base oxygenIndex .oxygen (-1) 0 ∧
  base.totalFormalCharge = acid.totalFormalCharge - 1

def pl3HydrolysisReaction (neutral : MolecularGraph) : MolecularReaction :=
  { reactants :=
      [⟨.PL3NeutralRepresentative, 1, neutral, .unspecified⟩,
       ⟨.water, 4, waterMolecule, .unspecified⟩]
    products :=
      [⟨.fattyAcid, 2, fattyAcidMolecule, .unspecified⟩,
       ⟨.phosphoricAcid, 1, phosphoricAcidMolecule, .unspecified⟩,
       ⟨.ethanol, 1, ethanolMolecule, .unspecified⟩,
       ⟨.glycerol, 1, glycerolMolecule, .unspecified⟩] }

/-- The competing central-phosphate placement from the complete positional
domain generated by the printed hydrolysis products.  Its two terminal
`CH2-O-C(=O)R` arms are identical, so atom 5 is deliberately not marked as a
stereocentre; that fact is checked below by an explicit arm exchange. -/
def structurePL3CentralNeutral : MolecularGraph :=
  { atoms :=
      [ residueRAtom, carbonAtom 0, oxygenAtom 0, oxygenAtom 0,
        carbonAtom 2, carbonAtom 1, carbonAtom 2, oxygenAtom 0,
        carbonAtom 0, oxygenAtom 0, residueRAtom, oxygenAtom 0,
        phosphorusAtom, oxygenAtom 0, oxygenAtom 1, oxygenAtom 0,
        carbonAtom 2, carbonAtom 3 ]
    bonds :=
      [ singleBond 0 1, doubleBond 1 2, singleBond 1 3, singleBond 3 4,
        singleBond 4 5, singleBond 5 6, singleBond 6 7, singleBond 7 8,
        doubleBond 8 9, singleBond 8 10, singleBond 5 11,
        singleBond 11 12, doubleBond 12 13, singleBond 12 14,
        singleBond 12 15, singleBond 15 16, singleBond 16 17 ]
    stereocentres := [] }

def structurePL3Central : MolecularGraph :=
  { structurePL3CentralNeutral with
    atoms := replaceAt structurePL3CentralNeutral.atoms 14 anionicOxygen }

def pl3CentralHydrolysisSites : HydrolysisSiteLedger :=
  { acylEsters := [⟨0, 1, 2, 3, 4⟩, ⟨10, 8, 9, 7, 6⟩]
    phosphateDiesters := [⟨12, 13, 14, 11, 5, 15, 16⟩] }

/-- Exchange of the two identical terminal `CH2-O-C(=O)R` arms in the
central-phosphate alternative. -/
def centralPL3ArmExchange : ℕ → ℕ
  | 0 => 10 | 1 => 8 | 2 => 9 | 3 => 7 | 4 => 6
  | 5 => 5
  | 6 => 4 | 7 => 3 | 8 => 1 | 9 => 2 | 10 => 0
  | n => n

def HasEquivalentGlycerolCarbonArms (m : MolecularGraph) : Prop :=
  ∃ p : ℕ → ℕ,
    m.NontrivialAutomorphism p ∧ p 4 = 6 ∧ p 6 = 4 ∧ p 5 = 5

theorem centralPL3ArmExchange_bound_certificate :
    ∀ i : Fin 18, centralPL3ArmExchange i.1 < 18 := by
  decide

theorem centralPL3ArmExchange_involutive_certificate :
    ∀ i : Fin 18,
      centralPL3ArmExchange (centralPL3ArmExchange i.1) = i.1 := by
  decide

theorem centralPL3ArmExchange_atoms_certificate :
    ∀ i : Fin 18,
      structurePL3Central.atomAt? i.1 =
        structurePL3Central.atomAt? (centralPL3ArmExchange i.1) := by
  decide

theorem centralPL3ArmExchange_bonds_certificate :
    ∀ i : Fin 18, ∀ j : Fin 18,
      structurePL3Central.bondOrderBetween i.1 j.1 =
        structurePL3Central.bondOrderBetween
          (centralPL3ArmExchange i.1) (centralPL3ArmExchange j.1) := by
  decide

theorem centralPL3ArmExchange_stereo_certificate :
    ∀ i : Fin 18,
      structurePL3Central.stereoAt? i.1 =
        structurePL3Central.stereoAt? (centralPL3ArmExchange i.1) := by
  decide

theorem centralPL3ArmExchange_active :
    structurePL3Central.ActivePermutation centralPL3ArmExchange := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi18 : i < 18 := by
      simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hi
    simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using
      centralPL3ArmExchange_bound_certificate ⟨i, hi18⟩
  · intro i j hi hj hij
    have hi18 : i < 18 := by
      simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hi
    have hj18 : j < 18 := by
      simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hj
    calc
      i = centralPL3ArmExchange (centralPL3ArmExchange i) :=
        (centralPL3ArmExchange_involutive_certificate ⟨i, hi18⟩).symm
      _ = centralPL3ArmExchange (centralPL3ArmExchange j) :=
        congrArg centralPL3ArmExchange hij
      _ = j := centralPL3ArmExchange_involutive_certificate ⟨j, hj18⟩
  · intro j hj
    have hj18 : j < 18 := by
      simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hj
    refine ⟨centralPL3ArmExchange j, ?_, ?_⟩
    · simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using
        centralPL3ArmExchange_bound_certificate ⟨j, hj18⟩
    · exact centralPL3ArmExchange_involutive_certificate ⟨j, hj18⟩

theorem centralPL3ArmExchange_preserves :
    structurePL3Central.PreservesTo structurePL3Central
      centralPL3ArmExchange := by
  refine ⟨rfl, centralPL3ArmExchange_active, ?_, ?_, ?_⟩
  · intro i hi
    exact centralPL3ArmExchange_atoms_certificate
      ⟨i, by simpa [structurePL3Central, structurePL3CentralNeutral,
        replaceAt] using hi⟩
  · intro i j hi hj
    exact centralPL3ArmExchange_bonds_certificate
      ⟨i, by simpa [structurePL3Central, structurePL3CentralNeutral,
        replaceAt] using hi⟩
      ⟨j, by simpa [structurePL3Central, structurePL3CentralNeutral,
        replaceAt] using hj⟩
  · intro i hi
    exact centralPL3ArmExchange_stereo_certificate
      ⟨i, by simpa [structurePL3Central, structurePL3CentralNeutral,
        replaceAt] using hi⟩

theorem structurePL3Central_equivalent_carbon_arms :
    HasEquivalentGlycerolCarbonArms structurePL3Central := by
  exact ⟨centralPL3ArmExchange,
    ⟨centralPL3ArmExchange_preserves, ⟨0, by decide, by decide⟩⟩,
    by decide, by decide, by decide⟩

def centralPL3TreeParent : ℕ → ℕ
  | 0 => 0
  | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 3 | 5 => 4
  | 6 => 5 | 7 => 6 | 8 => 7 | 9 => 8 | 10 => 8
  | 11 => 5 | 12 => 11 | 13 => 12 | 14 => 12 | 15 => 12
  | 16 => 15 | 17 => 16
  | _ => 0

def centralPL3TreeParentBond (i : ℕ) : Bond :=
  if i = 2 ∨ i = 9 ∨ i = 13 then
    doubleBond (centralPL3TreeParent i) i
  else
    singleBond (centralPL3TreeParent i) i

theorem structurePL3Central_parent_certificate :
    ∀ i : Fin 18, 0 < i.1 →
      centralPL3TreeParentBond i.1 ∈ structurePL3CentralNeutral.bonds ∧
      (centralPL3TreeParentBond i.1).connects i.1
        (centralPL3TreeParent i.1) ∧
      centralPL3TreeParent i.1 < i.1 := by
  decide

theorem structurePL3CentralNeutral_valence_certificate :
    ∀ i : Fin 18,
      structurePL3CentralNeutral.atomAt? i.1 =
        some (structurePL3CentralNeutral.atomAtDefault i.1) ∧
      expectedDisplayedValence
          (structurePL3CentralNeutral.atomAtDefault i.1) =
        some (structurePL3CentralNeutral.incidentBondOrder i.1 +
          (structurePL3CentralNeutral.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem structurePL3Central_valence_certificate :
    ∀ i : Fin 18,
      structurePL3Central.atomAt? i.1 =
        some (structurePL3Central.atomAtDefault i.1) ∧
      expectedDisplayedValence (structurePL3Central.atomAtDefault i.1) =
        some (structurePL3Central.incidentBondOrder i.1 +
          (structurePL3Central.atomAtDefault i.1).implicitHydrogens) := by
  decide

theorem structurePL3CentralNeutral_connected :
    structurePL3CentralNeutral.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent
    structurePL3CentralNeutral centralPL3TreeParent
  intro i hpos hlt
  have hi18 : i < 18 := by simpa [structurePL3CentralNeutral] using hlt
  have hcert := structurePL3Central_parent_certificate ⟨i, hi18⟩ hpos
  exact ⟨⟨centralPL3TreeParentBond i, hcert.1, hcert.2.1⟩, hcert.2.2⟩

theorem structurePL3Central_connected : structurePL3Central.Connected := by
  apply MolecularGraph.connected_of_decreasing_parent
    structurePL3Central centralPL3TreeParent
  intro i hpos hlt
  have hi18 : i < 18 := by
    simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hlt
  have hcert := structurePL3Central_parent_certificate ⟨i, hi18⟩ hpos
  refine ⟨⟨centralPL3TreeParentBond i, ?_, hcert.2.1⟩, hcert.2.2⟩
  simpa [structurePL3Central] using hcert.1

theorem structurePL3CentralNeutral_valenceSatisfied :
    structurePL3CentralNeutral.ValenceSatisfied := by
  intro i a hi
  have hlt : i < structurePL3CentralNeutral.atoms.length :=
    listGet?_eq_some_lt hi
  have hi18 : i < 18 := by simpa [structurePL3CentralNeutral] using hlt
  rcases structurePL3CentralNeutral_valence_certificate ⟨i, hi18⟩ with
    ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem structurePL3Central_valenceSatisfied :
    structurePL3Central.ValenceSatisfied := by
  intro i a hi
  have hlt : i < structurePL3Central.atoms.length := listGet?_eq_some_lt hi
  have hi18 : i < 18 := by
    simpa [structurePL3Central, structurePL3CentralNeutral, replaceAt] using hlt
  rcases structurePL3Central_valence_certificate ⟨i, hi18⟩ with
    ⟨hatom, hvalence⟩
  rw [hi] at hatom
  injection hatom with ha
  subst a
  exact ⟨_, hvalence, rfl⟩

theorem structurePL3CentralNeutral_wellFormed :
    structurePL3CentralNeutral.WellFormed := by
  refine ⟨?_, ?_, structurePL3CentralNeutral_valenceSatisfied, ?_⟩
  · simp [structurePL3CentralNeutral, singleBond, doubleBond]
  · decide
  · simp [structurePL3CentralNeutral]

theorem structurePL3Central_wellFormed : structurePL3Central.WellFormed := by
  refine ⟨?_, ?_, structurePL3Central_valenceSatisfied, ?_⟩
  · simp [structurePL3Central, structurePL3CentralNeutral, replaceAt,
      singleBond, doubleBond]
  · decide
  · simp [structurePL3Central, structurePL3CentralNeutral, replaceAt]

theorem structurePL3CentralNeutral_abbreviatedTree :
    structurePL3CentralNeutral.AbbreviatedTree := by
  exact ⟨structurePL3CentralNeutral_wellFormed,
    structurePL3CentralNeutral_connected, by decide⟩

theorem structurePL3Central_abbreviatedTree :
    structurePL3Central.AbbreviatedTree := by
  exact ⟨structurePL3Central_wellFormed, structurePL3Central_connected,
    by decide⟩

theorem structurePL3Central_notChiral : ¬ structurePL3Central.IsChiral := by
  intro h
  exact h.1 (by simp [structurePL3Central, structurePL3CentralNeutral])

/-- The source-derived finite positional domain: with two identical acyl
groups and one phosphate diester occupying the three glycerol oxygens, exchange
of the two terminal glycerol positions leaves exactly these two cases. -/
inductive GlycerolSubstitutionPattern
  | phosphateOnTerminal
  | phosphateOnCentral
  deriving DecidableEq, Repr

def GlycerolSubstitutionPattern.neutralGraph :
    GlycerolSubstitutionPattern → MolecularGraph
  | .phosphateOnTerminal => structurePL3Neutral
  | .phosphateOnCentral => structurePL3CentralNeutral

def GlycerolSubstitutionPattern.physiologicalGraph :
    GlycerolSubstitutionPattern → MolecularGraph
  | .phosphateOnTerminal => structurePL3
  | .phosphateOnCentral => structurePL3Central

def GlycerolSubstitutionPattern.hydrolysisSites :
    GlycerolSubstitutionPattern → HydrolysisSiteLedger
  | .phosphateOnTerminal => pl3NeutralHydrolysisSites
  | .phosphateOnCentral => pl3CentralHydrolysisSites

/-- All constraints independent of the printed enantiomer observation are
applied uniformly to both source-derived positional cases. -/
def PL3PatternCoreCompatible (p : GlycerolSubstitutionPattern) : Prop :=
  let neutral := p.neutralGraph
  let physiological := p.physiologicalGraph
  neutral.AbbreviatedTree ∧ physiological.AbbreviatedTree ∧
  neutral.RadicalFree ∧ physiological.RadicalFree ∧
  neutral.NoPeroxideBond ∧ physiological.NoPeroxideBond ∧
  neutral.formula fattyResidueRFormula = ⟨41, 73, 8, 1⟩ ∧
  neutral.totalFormalCharge = 0 ∧
  physiological.formula fattyResidueRFormula = ⟨41, 72, 8, 1⟩ ∧
  physiological.totalFormalCharge = -1 ∧
  p.hydrolysisSites.ValidFor neutral 0 1 ∧
  p.hydrolysisSites.waterCount = 4 ∧
  (pl3HydrolysisReaction neutral).AtomBalanced fattyResidueRFormula ∧
  (pl3HydrolysisReaction neutral).ChargeBalanced

/-- The decisive source observation is represented by actual non-superposition
with the mirror of the concrete graph, not a pattern-indexed truth table. -/
def PL3PatternMatchesSource (p : GlycerolSubstitutionPattern) : Prop :=
  PL3PatternCoreCompatible p ∧ p.physiologicalGraph.IsChiral

theorem enantiomer_pair_selects_terminal_phosphate
    (p : GlycerolSubstitutionPattern) (h : PL3PatternMatchesSource p) :
    p = .phosphateOnTerminal := by
  cases p with
  | phosphateOnTerminal => rfl
  | phosphateOnCentral =>
      exact (structurePL3Central_notChiral h.2).elim

def PL3StructureSpec (physiological neutral : MolecularGraph) : Prop :=
  physiological.AbbreviatedTree ∧ physiological.NoPeroxideBond ∧
  physiological.RadicalFree ∧
  physiological.formula fattyResidueRFormula = ⟨41, 72, 8, 1⟩ ∧
  physiological.totalFormalCharge = -1 ∧
  physiological.stereocentres.length = 1 ∧
  physiological.stereoAt? 5 = some .R ∧ physiological.IsChiral ∧
  physiological.EnantiomerPair physiological.mirror ∧
  neutral.AbbreviatedTree ∧ neutral.RadicalFree ∧
  neutral.formula fattyResidueRFormula = ⟨41, 73, 8, 1⟩ ∧
  neutral.totalFormalCharge = 0 ∧
  IsSingleODeprotonationAt neutral physiological 14 ∧
  pl3NeutralHydrolysisSites.ValidFor neutral 0 1 ∧
  pl3NeutralHydrolysisSites.waterCount = 4 ∧
  (pl3HydrolysisReaction neutral).AtomBalanced fattyResidueRFormula ∧
  (pl3HydrolysisReaction neutral).ChargeBalanced ∧
  HasEquivalentGlycerolCarbonArms structurePL3Central ∧
  PL3PatternMatchesSource .phosphateOnTerminal ∧
  (∀ p, PL3PatternMatchesSource p → p = .phosphateOnTerminal)

/-- Raw exact-symbolic carrier for requested output `structure_pl3`. -/
def StructurePL3RawResult : Prop :=
  PreviousPartA2Spec ∧ PreviousPartA3Spec ∧
    PL3StructureSpec structurePL3 structurePL3Neutral

/-- Reported exact-symbolic carrier; exact symbolic outputs perform no
rounding, so it has the same chemical proposition as the raw carrier. -/
def StructurePL3ReportedResult : Prop :=
  PreviousPartA2Spec ∧ PreviousPartA3Spec ∧
    PL3StructureSpec structurePL3 structurePL3Neutral

theorem structurePL3_noPeroxideBond : structurePL3.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, structurePL3, structurePL3Neutral,
    replaceAt, MolecularGraph.atomAt?, listGet?, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, anionicOxygen, phosphorusAtom]

theorem structurePL3Neutral_noPeroxideBond :
    structurePL3Neutral.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, structurePL3Neutral,
    MolecularGraph.atomAt?, listGet?, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem structurePL3Central_noPeroxideBond :
    structurePL3Central.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, structurePL3Central,
    structurePL3CentralNeutral, replaceAt, MolecularGraph.atomAt?, listGet?,
    singleBond, doubleBond, residueRAtom, carbonAtom, oxygenAtom,
    anionicOxygen, phosphorusAtom]

theorem structurePL3CentralNeutral_noPeroxideBond :
    structurePL3CentralNeutral.NoPeroxideBond := by
  simp [MolecularGraph.NoPeroxideBond, structurePL3CentralNeutral,
    MolecularGraph.atomAt?, listGet?, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem structurePL3_radicalFree : structurePL3.RadicalFree := by
  simp [MolecularGraph.RadicalFree, structurePL3, structurePL3Neutral,
    replaceAt, residueRAtom, carbonAtom, oxygenAtom, anionicOxygen,
    phosphorusAtom]

theorem structurePL3Neutral_radicalFree : structurePL3Neutral.RadicalFree := by
  simp [MolecularGraph.RadicalFree, structurePL3Neutral, residueRAtom,
    carbonAtom, oxygenAtom, phosphorusAtom]

theorem structurePL3Central_radicalFree : structurePL3Central.RadicalFree := by
  simp [MolecularGraph.RadicalFree, structurePL3Central,
    structurePL3CentralNeutral, replaceAt, residueRAtom, carbonAtom,
    oxygenAtom, anionicOxygen, phosphorusAtom]

theorem structurePL3CentralNeutral_radicalFree :
    structurePL3CentralNeutral.RadicalFree := by
  simp [MolecularGraph.RadicalFree, structurePL3CentralNeutral,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem structurePL3_isSingleODeprotonation :
    IsSingleODeprotonationAt structurePL3Neutral structurePL3 14 := by
  refine ⟨by decide, rfl, rfl, ?_, ?_, ?_, by decide⟩
  · intro i hi
    change listGet? structurePL3Neutral.atoms i =
      listGet? (replaceAt structurePL3Neutral.atoms 14 anionicOxygen) i
    exact (listGet?_replaceAt_of_ne structurePL3Neutral.atoms i 14
      anionicOxygen hi).symm
  · unfold HasAtom
    decide
  · unfold HasAtom
    decide

theorem pl3NeutralHydrolysisSites_valid :
    pl3NeutralHydrolysisSites.ValidFor structurePL3Neutral 0 1 := by
  simp [HydrolysisSiteLedger.ValidFor, pl3NeutralHydrolysisSites,
    AcylEsterSite.ValidFor, PhosphateDiesterSite.ValidFor, HasAtom,
    structurePL3Neutral, MolecularGraph.atomAt?, listGet?,
    MolecularGraph.hasBond, Bond.connects, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem pl3CentralHydrolysisSites_valid :
    pl3CentralHydrolysisSites.ValidFor structurePL3CentralNeutral 0 1 := by
  simp [HydrolysisSiteLedger.ValidFor, pl3CentralHydrolysisSites,
    AcylEsterSite.ValidFor, PhosphateDiesterSite.ValidFor, HasAtom,
    structurePL3CentralNeutral, MolecularGraph.atomAt?, listGet?,
    MolecularGraph.hasBond, Bond.connects, singleBond, doubleBond,
    residueRAtom, carbonAtom, oxygenAtom, phosphorusAtom]

theorem pl3_terminal_core_compatible :
    PL3PatternCoreCompatible .phosphateOnTerminal := by
  exact ⟨structurePL3Neutral_abbreviatedTree, structurePL3_abbreviatedTree,
    structurePL3Neutral_radicalFree, structurePL3_radicalFree,
    structurePL3Neutral_noPeroxideBond, structurePL3_noPeroxideBond,
    by decide, by decide, by decide, by decide,
    pl3NeutralHydrolysisSites_valid, by decide,
    by unfold MolecularReaction.AtomBalanced; decide,
    by unfold MolecularReaction.ChargeBalanced; decide⟩

theorem pl3_central_core_compatible :
    PL3PatternCoreCompatible .phosphateOnCentral := by
  exact ⟨structurePL3CentralNeutral_abbreviatedTree,
    structurePL3Central_abbreviatedTree,
    structurePL3CentralNeutral_radicalFree, structurePL3Central_radicalFree,
    structurePL3CentralNeutral_noPeroxideBond,
    structurePL3Central_noPeroxideBond,
    by decide, by decide, by decide, by decide,
    pl3CentralHydrolysisSites_valid, by decide,
    by unfold MolecularReaction.AtomBalanced; decide,
    by unfold MolecularReaction.ChargeBalanced; decide⟩

theorem pl3_all_positional_cases_core_compatible
    (p : GlycerolSubstitutionPattern) : PL3PatternCoreCompatible p := by
  cases p
  · exact pl3_terminal_core_compatible
  · exact pl3_central_core_compatible

theorem pl3_terminal_matches_source :
    PL3PatternMatchesSource .phosphateOnTerminal := by
  exact ⟨pl3_terminal_core_compatible, structurePL3_isChiral⟩

theorem structurePL3_raw_result : StructurePL3RawResult := by
  refine ⟨previousPartA2_derived_inline, previousPartA3_derived_inline, ?_⟩
  exact ⟨structurePL3_abbreviatedTree, structurePL3_noPeroxideBond,
    structurePL3_radicalFree, by decide, by decide,
    by decide, by decide, structurePL3_isChiral,
    ⟨rfl, structurePL3_isChiral⟩, structurePL3Neutral_abbreviatedTree,
    structurePL3Neutral_radicalFree, by decide, by decide,
    structurePL3_isSingleODeprotonation, pl3NeutralHydrolysisSites_valid,
    by decide,
    by unfold MolecularReaction.AtomBalanced; decide,
    by unfold MolecularReaction.ChargeBalanced; decide,
    structurePL3Central_equivalent_carbon_arms,
    pl3_terminal_matches_source,
    fun p hp => enantiomer_pair_selects_terminal_phosphate p hp⟩

theorem structurePL3_reported_result : StructurePL3ReportedResult := by
  exact structurePL3_raw_result

theorem structurePL3_enantiomer_pair :
    structurePL3.EnantiomerPair structurePL3.mirror := by
  exact ⟨rfl, structurePL3_isChiral⟩

/-- One exact-symbolic result proposition covering both requested outputs in
controller order. -/
def RawResult : Prop := StructurePL2RawResult ∧ StructurePL3RawResult

def ReportedResult : Prop :=
  StructurePL2ReportedResult ∧ StructurePL3ReportedResult

/-- Hash-bound raw solve contract for the answer-blind artifact. -/
theorem raw_result :
    ("70518f4214254c8f363a0cbb8aa1ad0b37a3d85d40bd8c401c82d257dbc31f24" : String) =
        "70518f4214254c8f363a0cbb8aa1ad0b37a3d85d40bd8c401c82d257dbc31f24" ∧
      RawResult := by
  exact ⟨rfl, structurePL2_raw_result, structurePL3_raw_result⟩

/-- Hash-bound reported solve contract.  Both outputs are exact structures,
so no rounding operation intervenes. -/
theorem reported_result :
    ("14f0f4d08a7b04f2163ac3c8c48b71b6adb9101dadb271029852c83fcbf9243f" : String) =
        "14f0f4d08a7b04f2163ac3c8c48b71b6adb9101dadb271029852c83fcbf9243f" ∧
      ReportedResult := by
  exact ⟨rfl, structurePL2_reported_result, structurePL3_reported_result⟩

/-- Combined target corresponding to both drawings requested in T5.6. -/
theorem problem_icho_2026_t5_a6 : ReportedResult := by
  exact reported_result.2

end IChO2026Problems.IChO2026T5A6
