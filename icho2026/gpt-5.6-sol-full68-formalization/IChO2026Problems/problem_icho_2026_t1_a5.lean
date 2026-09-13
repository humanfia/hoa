import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T1-A5: structures of E, F, and G

This is an answer-blind formalization.  The molecular drawings are represented
as finite labelled graphs.  Hydrogens that would normally be implicit in a
skeletal drawing are explicit atoms, and the bond-order function is total, so
every omitted pair of atoms is explicitly assigned `BondOrder.none`.

The two reaction arrows are used only as qualitative named-transform
compatibility constraints.  No yield, completeness, phase, unprinted heating
condition, or unprinted byproduct is asserted.
-/

namespace IChO2026Problems.T1A5

noncomputable section

/-! ## A small, target-local molecular-graph interface -/

/-- The elements which occur in the three requested structures. -/
inductive Element where
  | hydrogen
  | carbon
  | oxygen
  deriving DecidableEq, Repr

/-- Bond orders used in the requested Lewis/skeletal structures.  Aromatic
bonds are represented directly instead of choosing a symmetry-breaking Kekulé
form. -/
inductive BondOrder where
  | none
  | single
  | double
  | aromatic
  deriving DecidableEq, Repr

/-- The requested structures have no stereocentres.  The other constructors
make that absence an explicit assignment rather than an omitted field. -/
inductive AtomStereo where
  | achiral
  | rectus
  | sinister
  deriving DecidableEq, Repr

/-- A complete labelled molecular graph on a specified atom type. -/
structure MolecularStructure (Atom : Type) where
  element : Atom → Element
  formalCharge : Atom → ℤ
  radicalElectrons : Atom → ℕ
  stereochemistry : Atom → AtomStereo
  bondOrder : Atom → Atom → BondOrder

/-- A molecular formula over the complete element universe relevant to A5. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Count the explicitly represented atoms to recover a molecular formula. -/
def formulaOf {Atom : Type} [Fintype Atom]
    (m : MolecularStructure Atom) : MolecularFormula where
  carbon := (Finset.univ.filter fun a => m.element a = .carbon).card
  hydrogen := (Finset.univ.filter fun a => m.element a = .hydrogen).card
  oxygen := (Finset.univ.filter fun a => m.element a = .oxygen).card

/-- Two atoms are connected when their explicitly assigned bond order is not
`none`. -/
def Bonded {Atom : Type} (m : MolecularStructure Atom) (a b : Atom) : Prop :=
  m.bondOrder a b ≠ .none

/-- Connectivity of the full atom graph, including explicit hydrogens. -/
def Connected {Atom : Type} (m : MolecularStructure Atom) : Prop :=
  ∀ a b, Relation.ReflTransGen (Bonded m) a b

/-- Structural well-formedness obligations relevant to the drawings: no
self-bonds, undirected bond orders, one connected component, and explicit
neutral/closed-shell/achiral assignments at every atom. -/
def CompleteNeutralClosedShell {Atom : Type}
    (m : MolecularStructure Atom) : Prop :=
  (∀ a, m.bondOrder a a = .none) ∧
  (∀ a b, m.bondOrder a b = m.bondOrder b a) ∧
  Connected m ∧
  (∀ a, m.formalCharge a = 0 ∧
    m.radicalElectrons a = 0 ∧
    m.stereochemistry a = .achiral)

/-- A labelled-graph automorphism; this is the combinatorial carrier for a
rotation of a molecular structure. -/
def PreservesStructure {Atom : Type} (m : MolecularStructure Atom)
    (r : Atom → Atom) : Prop :=
  (∀ a, m.element (r a) = m.element a ∧
    m.formalCharge (r a) = m.formalCharge a ∧
    m.radicalElectrons (r a) = m.radicalElectrons a ∧
    m.stereochemistry (r a) = m.stereochemistry a) ∧
  (∀ a b, m.bondOrder (r a) (r b) = m.bondOrder a b)

/-- `r` has exact positive order `n`, not merely order dividing `n`. -/
def ExactOrder {Atom : Type} (r : Atom → Atom) (n : ℕ) : Prop :=
  0 < n ∧
  (∀ a, Nat.iterate r n a = a) ∧
  (∀ k, 0 < k → k < n → ∃ a, Nat.iterate r k a ≠ a)

/-- An explicit order-`n` rotational symmetry of a molecular graph. -/
def HasRotationalAxisOrder {Atom : Type} (m : MolecularStructure Atom)
    (r : Atom → Atom) (n : ℕ) : Prop :=
  Function.Bijective r ∧ ExactOrder r n ∧ PreservesStructure m r

/-! ## Source-side data and qualitative arrows -/

inductive SpeciesRole where
  | E
  | F
  | G
  deriving DecidableEq, Repr

inductive Reagent where
  | potassiumPermanganate
  | nitricAcid
  | phosphorusPentoxide
  deriving DecidableEq, Repr

inductive ReactionMedium where
  | acidicNitricAcidSolution
  deriving DecidableEq, Repr

inductive SourceLocator where
  | page3Paragraph
  | page3ReactionScheme
  deriving DecidableEq, Repr

/-- Only fields printed in the source are present.  In particular, there is no
field for yield, completeness, coefficients, phases, heating, or byproducts. -/
structure QualitativeArrow where
  reactant : SpeciesRole
  product : SpeciesRole
  reagents : Finset Reagent
  medium : Option ReactionMedium
  locator : SourceLocator
  deriving DecidableEq

inductive SymmetryDescription where
  | highlySymmetricAcid
  | exactAxisOrder (n : ℕ)
  deriving DecidableEq, Repr

inductive CompositionDescription where
  | binaryCompound
  deriving DecidableEq, Repr

inductive GeologicalOrigin where
  | coalDeposit
  deriving DecidableEq, Repr

/-- The complete source-side A5 data used below.  Percentages are percentage
points.  A displayed quantum of `0.01` gives the source-policy half-quantum
measurement interval. -/
structure SourceData where
  stoneOrigin : GeologicalOrigin
  stoneAnionParent : SpeciesRole
  eHydrogenPercentShown : ℝ
  eHydrogenPercentQuantum : ℝ
  eSymmetry : SymmetryDescription
  fSymmetry : SymmetryDescription
  gOxygenPercentShown : ℝ
  gOxygenPercentQuantum : ℝ
  gSymmetry : SymmetryDescription
  gComposition : CompositionDescription
  oxidationArrow : QualitativeArrow
  dehydrationArrow : QualitativeArrow

/-- The source data transcribed from `T1_page-3.png`. -/
def sourceData : SourceData where
  stoneOrigin := .coalDeposit
  stoneAnionParent := .F
  eHydrogenPercentShown := 1118 / 100
  eHydrogenPercentQuantum := 1 / 100
  eSymmetry := .exactAxisOrder 6
  fSymmetry := .highlySymmetricAcid
  gOxygenPercentShown := 4998 / 100
  gOxygenPercentQuantum := 1 / 100
  gSymmetry := .exactAxisOrder 3
  gComposition := .binaryCompound
  oxidationArrow :=
    { reactant := .E
      product := .F
      reagents := {.potassiumPermanganate, .nitricAcid}
      medium := some .acidicNitricAcidSolution
      locator := .page3ReactionScheme }
  dehydrationArrow :=
    { reactant := .F
      product := .G
      reagents := {.phosphorusPentoxide}
      medium := none
      locator := .page3ReactionScheme }

/-- Classification mandated by the use made of the two source arrows. -/
inductive StageUse where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

def stageUse : StageUse := .qualitativeNamedTransformOnly

/-! ## Exact formula and mass carriers -/

/-- Conventional nominal atomic weights from the pinned offline registry
`ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+
contest-interpretation-v1+trusted-empirical-rules-v1`, dataset SHA-256
`11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`.
The source does not stipulate alternative atomic weights. -/
def atomicWeight : Element → ℝ
  | .hydrogen => 1008 / 1000
  | .carbon => 12011 / 1000
  | .oxygen => 15999 / 1000

def MolecularFormula.count (f : MolecularFormula) : Element → ℕ
  | .hydrogen => f.hydrogen
  | .carbon => f.carbon
  | .oxygen => f.oxygen

def formulaMass (f : MolecularFormula) : ℝ :=
  (f.carbon : ℝ) * atomicWeight .carbon +
  (f.hydrogen : ℝ) * atomicWeight .hydrogen +
  (f.oxygen : ℝ) * atomicWeight .oxygen

def elementMassPercent (e : Element) (f : MolecularFormula) : ℝ :=
  100 * ((f.count e : ℝ) * atomicWeight e) / formulaMass f

def MolecularFormula.add (f g : MolecularFormula) : MolecularFormula where
  carbon := f.carbon + g.carbon
  hydrogen := f.hydrogen + g.hydrogen
  oxygen := f.oxygen + g.oxygen

def MolecularFormula.nsmul (n : ℕ) (f : MolecularFormula) : MolecularFormula where
  carbon := n * f.carbon
  hydrogen := n * f.hydrogen
  oxygen := n * f.oxygen

def waterFormula : MolecularFormula :=
  { carbon := 0, hydrogen := 2, oxygen := 1 }

/-! ## Candidate E: an aromatic ring with six methyl substituents -/

inductive EAtom where
  | ring (site : Fin 6)
  | methyl (site : Fin 6)
  | methylHydrogen (site : Fin 6) (which : Fin 3)
  deriving DecidableEq, Fintype, Repr

def cyclicAdjacent (i j : Fin 6) : Bool :=
  decide ((i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val)

def eElement : EAtom → Element
  | .ring _ => .carbon
  | .methyl _ => .carbon
  | .methylHydrogen _ _ => .hydrogen

def eBondOrder : EAtom → EAtom → BondOrder
  | .ring i, .ring j => if cyclicAdjacent i j then .aromatic else .none
  | .ring i, .methyl j => if i = j then .single else .none
  | .methyl j, .ring i => if i = j then .single else .none
  | .methyl i, .methylHydrogen j _ => if i = j then .single else .none
  | .methylHydrogen j _, .methyl i => if i = j then .single else .none
  | _, _ => .none

/-- Output carrier for E: the complete graph of hexamethylbenzene. -/
def structureE : MolecularStructure EAtom where
  element := eElement
  formalCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  stereochemistry := fun _ => .achiral
  bondOrder := eBondOrder

def formulaE : MolecularFormula :=
  { carbon := 12, hydrogen := 18, oxygen := 0 }

def rotateFin6 (step : ℕ) (i : Fin 6) : Fin 6 :=
  ⟨(i.val + step) % 6, Nat.mod_lt _ (by norm_num)⟩

def rotateE : EAtom → EAtom
  | .ring i => .ring (rotateFin6 1 i)
  | .methyl i => .methyl (rotateFin6 1 i)
  | .methylHydrogen i j => .methylHydrogen (rotateFin6 1 i) j

def HasMethylAtEveryRingSite (m : MolecularStructure EAtom) : Prop :=
  ∀ i,
    m.element (.ring i) = .carbon ∧
    m.element (.methyl i) = .carbon ∧
    m.bondOrder (.ring i) (.methyl i) = .single ∧
    ∀ j,
      m.element (.methylHydrogen i j) = .hydrogen ∧
      m.bondOrder (.methyl i) (.methylHydrogen i j) = .single

/-! ## Candidate F: an aromatic ring with six carboxylic-acid groups -/

inductive FAtom where
  | ring (site : Fin 6)
  | carboxylCarbon (site : Fin 6)
  | carbonylOxygen (site : Fin 6)
  | hydroxylOxygen (site : Fin 6)
  | acidicHydrogen (site : Fin 6)
  deriving DecidableEq, Fintype, Repr

def fElement : FAtom → Element
  | .ring _ => .carbon
  | .carboxylCarbon _ => .carbon
  | .carbonylOxygen _ => .oxygen
  | .hydroxylOxygen _ => .oxygen
  | .acidicHydrogen _ => .hydrogen

def fBondOrder : FAtom → FAtom → BondOrder
  | .ring i, .ring j => if cyclicAdjacent i j then .aromatic else .none
  | .ring i, .carboxylCarbon j => if i = j then .single else .none
  | .carboxylCarbon j, .ring i => if i = j then .single else .none
  | .carboxylCarbon i, .carbonylOxygen j => if i = j then .double else .none
  | .carbonylOxygen j, .carboxylCarbon i => if i = j then .double else .none
  | .carboxylCarbon i, .hydroxylOxygen j => if i = j then .single else .none
  | .hydroxylOxygen j, .carboxylCarbon i => if i = j then .single else .none
  | .hydroxylOxygen i, .acidicHydrogen j => if i = j then .single else .none
  | .acidicHydrogen j, .hydroxylOxygen i => if i = j then .single else .none
  | _, _ => .none

/-- Output carrier for F: the complete graph of
benzene-1,2,3,4,5,6-hexacarboxylic (mellitic) acid. -/
def structureF : MolecularStructure FAtom where
  element := fElement
  formalCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  stereochemistry := fun _ => .achiral
  bondOrder := fBondOrder

def formulaF : MolecularFormula :=
  { carbon := 12, hydrogen := 6, oxygen := 12 }

def rotateF : FAtom → FAtom
  | .ring i => .ring (rotateFin6 1 i)
  | .carboxylCarbon i => .carboxylCarbon (rotateFin6 1 i)
  | .carbonylOxygen i => .carbonylOxygen (rotateFin6 1 i)
  | .hydroxylOxygen i => .hydroxylOxygen (rotateFin6 1 i)
  | .acidicHydrogen i => .acidicHydrogen (rotateFin6 1 i)

def HasCarboxylicAcidAtEveryRingSite (m : MolecularStructure FAtom) : Prop :=
  ∀ i,
    m.element (.ring i) = .carbon ∧
    m.element (.carboxylCarbon i) = .carbon ∧
    m.element (.carbonylOxygen i) = .oxygen ∧
    m.element (.hydroxylOxygen i) = .oxygen ∧
    m.element (.acidicHydrogen i) = .hydrogen ∧
    m.bondOrder (.ring i) (.carboxylCarbon i) = .single ∧
    m.bondOrder (.carboxylCarbon i) (.carbonylOxygen i) = .double ∧
    m.bondOrder (.carboxylCarbon i) (.hydroxylOxygen i) = .single ∧
    m.bondOrder (.hydroxylOxygen i) (.acidicHydrogen i) = .single

/-! ## Candidate G: three cyclic anhydrides around the aromatic ring -/

inductive GAtom where
  | ring (site : Fin 6)
  | acylCarbon (site : Fin 6)
  | carbonylOxygen (site : Fin 6)
  | bridgingOxygen (bridge : Fin 3)
  deriving DecidableEq, Fintype, Repr

def evenSite (j : Fin 3) : Fin 6 :=
  ⟨2 * j.val, by omega⟩

def oddSite (j : Fin 3) : Fin 6 :=
  ⟨2 * j.val + 1, by omega⟩

def gElement : GAtom → Element
  | .ring _ => .carbon
  | .acylCarbon _ => .carbon
  | .carbonylOxygen _ => .oxygen
  | .bridgingOxygen _ => .oxygen

def bridgeIncident (site : Fin 6) (bridge : Fin 3) : Bool :=
  decide (site = evenSite bridge ∨ site = oddSite bridge)

def gBondOrder : GAtom → GAtom → BondOrder
  | .ring i, .ring j => if cyclicAdjacent i j then .aromatic else .none
  | .ring i, .acylCarbon j => if i = j then .single else .none
  | .acylCarbon j, .ring i => if i = j then .single else .none
  | .acylCarbon i, .carbonylOxygen j => if i = j then .double else .none
  | .carbonylOxygen j, .acylCarbon i => if i = j then .double else .none
  | .acylCarbon i, .bridgingOxygen j => if bridgeIncident i j then .single else .none
  | .bridgingOxygen j, .acylCarbon i => if bridgeIncident i j then .single else .none
  | _, _ => .none

/-- Output carrier for G: the complete graph of mellitic trianhydride.  Bridge
`j` joins the adjacent acyl carbons at ring sites `2*j` and `2*j+1`. -/
def structureG : MolecularStructure GAtom where
  element := gElement
  formalCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  stereochemistry := fun _ => .achiral
  bondOrder := gBondOrder

def formulaG : MolecularFormula :=
  { carbon := 12, hydrogen := 0, oxygen := 9 }

def rotateFin3 (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩

def rotateG : GAtom → GAtom
  | .ring i => .ring (rotateFin6 2 i)
  | .acylCarbon i => .acylCarbon (rotateFin6 2 i)
  | .carbonylOxygen i => .carbonylOxygen (rotateFin6 2 i)
  | .bridgingOxygen i => .bridgingOxygen (rotateFin3 i)

def HasThreeAnhydrideBridges (m : MolecularStructure GAtom) : Prop :=
  ∀ j,
    m.element (.bridgingOxygen j) = .oxygen ∧
    m.bondOrder (.acylCarbon (evenSite j)) (.bridgingOxygen j) = .single ∧
    m.bondOrder (.bridgingOxygen j) (.acylCarbon (oddSite j)) = .single ∧
    m.bondOrder (.acylCarbon (evenSite j))
      (.carbonylOxygen (evenSite j)) = .double ∧
    m.bondOrder (.acylCarbon (oddSite j))
      (.carbonylOxygen (oddSite j)) = .double

def MolecularFormula.presentElementCount (f : MolecularFormula) : ℕ :=
  (if 0 < f.carbon then 1 else 0) +
  (if 0 < f.hydrogen then 1 else 0) +
  (if 0 < f.oxygen then 1 else 0)

def IsBinaryFormula (f : MolecularFormula) : Prop :=
  f.presentElementCount = 2

/-! ## Non-opaque source-to-candidate transformation audits -/

/-- At each of the six symmetry-related sites, the aromatic-ring carbon and
side-chain carbon are retained while a methyl environment is replaced by an
explicit carboxylic-acid environment.  This records only structural
compatibility with the printed acidic-permanganate arrow. -/
def OxidationConnectivityCorrespondence : Prop :=
  (∀ i j,
    structureE.bondOrder (.ring i) (.ring j) =
      structureF.bondOrder (.ring i) (.ring j)) ∧
  (∀ i,
    structureE.element (.methyl i) = .carbon ∧
    structureF.element (.carboxylCarbon i) = .carbon ∧
    structureE.bondOrder (.ring i) (.methyl i) = .single ∧
    structureF.bondOrder (.ring i) (.carboxylCarbon i) = .single ∧
    structureF.bondOrder (.carboxylCarbon i) (.carbonylOxygen i) = .double ∧
    structureF.bondOrder (.carboxylCarbon i) (.hydroxylOxygen i) = .single)

/-- Candidate-local atom accounting for forming three anhydride bridges: the
F graph and G graph differ by exactly three water formulae.  It does not claim
that the printed reaction is complete or quantitative. -/
def TrianhydrideAtomAccounting : Prop :=
  formulaF = MolecularFormula.add formulaG (MolecularFormula.nsmul 3 waterFormula)

/-- Explicit connectivity correspondence for the three adjacent carboxyl-pair
closures in G. -/
def DehydrationConnectivityCorrespondence : Prop :=
  TrianhydrideAtomAccounting ∧
  (∀ i j,
    structureF.bondOrder (.ring i) (.ring j) =
      structureG.bondOrder (.ring i) (.ring j)) ∧
  (∀ i,
    structureF.element (.carboxylCarbon i) =
      structureG.element (.acylCarbon i) ∧
    structureF.bondOrder (.ring i) (.carboxylCarbon i) =
      structureG.bondOrder (.ring i) (.acylCarbon i) ∧
    structureF.bondOrder (.carboxylCarbon i) (.carbonylOxygen i) =
      structureG.bondOrder (.acylCarbon i) (.carbonylOxygen i)) ∧
  HasThreeAnhydrideBridges structureG

/-- The named roles, direction, reagents, medium, and page locator of the first
arrow, together with its candidate connectivity audit. -/
def OxidationArrowAudit : Prop :=
  stageUse = .qualitativeNamedTransformOnly ∧
  sourceData.oxidationArrow.reactant = .E ∧
  sourceData.oxidationArrow.product = .F ∧
  sourceData.oxidationArrow.reagents =
    {.potassiumPermanganate, .nitricAcid} ∧
  sourceData.oxidationArrow.medium = some .acidicNitricAcidSolution ∧
  sourceData.oxidationArrow.locator = .page3ReactionScheme ∧
  OxidationConnectivityCorrespondence

/-- The named roles, direction, reagent, absent unprinted medium, and page
locator of the second arrow, together with its candidate connectivity audit. -/
def DehydrationArrowAudit : Prop :=
  stageUse = .qualitativeNamedTransformOnly ∧
  sourceData.dehydrationArrow.reactant = .F ∧
  sourceData.dehydrationArrow.product = .G ∧
  sourceData.dehydrationArrow.reagents = {.phosphorusPentoxide} ∧
  sourceData.dehydrationArrow.medium = none ∧
  sourceData.dehydrationArrow.locator = .page3ReactionScheme ∧
  DehydrationConnectivityCorrespondence

/-! ## Finite graph and symmetry verification helpers -/

private theorem reflTransGen_reverse_of_symmetric
    {α : Type} {r : α → α → Prop}
    (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
      exact (Relation.ReflTransGen.single (hr b c hbc)).trans ih

private theorem fin6Cycle_to_zero (i : Fin 6) :
    Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) i (0 : Fin 6) := by
  let p1 : Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) (1 : Fin 6) 0 :=
    Relation.ReflTransGen.single (by native_decide)
  let p2 : Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) (2 : Fin 6) 0 :=
    (Relation.ReflTransGen.single
      (r := fun a b : Fin 6 => cyclicAdjacent a b = true) (by
        native_decide)).trans p1
  let p3 : Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) (3 : Fin 6) 0 :=
    (Relation.ReflTransGen.single
      (r := fun a b : Fin 6 => cyclicAdjacent a b = true) (by
        native_decide)).trans p2
  let p4 : Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) (4 : Fin 6) 0 :=
    (Relation.ReflTransGen.single
      (r := fun a b : Fin 6 => cyclicAdjacent a b = true) (by
        native_decide)).trans p3
  let p5 : Relation.ReflTransGen
      (fun a b : Fin 6 => cyclicAdjacent a b = true) (5 : Fin 6) 0 :=
    Relation.ReflTransGen.single (by native_decide)
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5

private theorem cyclicAdjacent_symmetric (i j : Fin 6) :
    cyclicAdjacent i j = cyclicAdjacent j i := by
  simp only [cyclicAdjacent, or_comm]

private theorem eBondOrder_symmetric (a b : EAtom) :
    eBondOrder a b = eBondOrder b a := by
  cases a <;> cases b <;> simp only [eBondOrder]
  · rw [cyclicAdjacent_symmetric]

private theorem fBondOrder_symmetric (a b : FAtom) :
    fBondOrder a b = fBondOrder b a := by
  cases a <;> cases b <;> simp only [fBondOrder]
  · rw [cyclicAdjacent_symmetric]

private theorem gBondOrder_symmetric (a b : GAtom) :
    gBondOrder a b = gBondOrder b a := by
  cases a <;> cases b <;> simp only [gBondOrder]
  · rw [cyclicAdjacent_symmetric]

private theorem eBonded_symmetric (a b : EAtom) :
    Bonded structureE a b → Bonded structureE b a := by
  intro hab
  change eBondOrder a b ≠ .none at hab
  change eBondOrder b a ≠ .none
  intro hba
  apply hab
  rw [eBondOrder_symmetric a b]
  exact hba

private theorem fBonded_symmetric (a b : FAtom) :
    Bonded structureF a b → Bonded structureF b a := by
  intro hab
  change fBondOrder a b ≠ .none at hab
  change fBondOrder b a ≠ .none
  intro hba
  apply hab
  rw [fBondOrder_symmetric a b]
  exact hba

private theorem gBonded_symmetric (a b : GAtom) :
    Bonded structureG a b → Bonded structureG b a := by
  intro hab
  change gBondOrder a b ≠ .none at hab
  change gBondOrder b a ≠ .none
  intro hba
  apply hab
  rw [gBondOrder_symmetric a b]
  exact hba

private theorem eRing_to_root (i : Fin 6) :
    Relation.ReflTransGen (Bonded structureE) (.ring i) (.ring 0) := by
  exact (fin6Cycle_to_zero i).lift EAtom.ring (by
    intro a b hab
    simp [Bonded, structureE, eBondOrder, hab])

private theorem fRing_to_root (i : Fin 6) :
    Relation.ReflTransGen (Bonded structureF) (.ring i) (.ring 0) := by
  exact (fin6Cycle_to_zero i).lift FAtom.ring (by
    intro a b hab
    simp [Bonded, structureF, fBondOrder, hab])

private theorem gRing_to_root (i : Fin 6) :
    Relation.ReflTransGen (Bonded structureG) (.ring i) (.ring 0) := by
  exact (fin6Cycle_to_zero i).lift GAtom.ring (by
    intro a b hab
    simp [Bonded, structureG, gBondOrder, hab])

private theorem eAtom_to_root :
    ∀ a, Relation.ReflTransGen (Bonded structureE) a (.ring 0)
  | .ring i => eRing_to_root i
  | .methyl i =>
      (Relation.ReflTransGen.single (by
        simp [Bonded, structureE, eBondOrder])).trans (eRing_to_root i)
  | .methylHydrogen i j =>
      (Relation.ReflTransGen.single (show
        Bonded structureE (.methylHydrogen i j) (.methyl i) by
          simp [Bonded, structureE, eBondOrder])).trans
        ((Relation.ReflTransGen.single (by
          simp [Bonded, structureE, eBondOrder])).trans (eRing_to_root i))

private theorem fAtom_to_root :
    ∀ a, Relation.ReflTransGen (Bonded structureF) a (.ring 0)
  | .ring i => fRing_to_root i
  | .carboxylCarbon i =>
      (Relation.ReflTransGen.single (by
        simp [Bonded, structureF, fBondOrder])).trans (fRing_to_root i)
  | .carbonylOxygen i =>
      (Relation.ReflTransGen.single (show
        Bonded structureF (.carbonylOxygen i) (.carboxylCarbon i) by
          simp [Bonded, structureF, fBondOrder])).trans
        ((Relation.ReflTransGen.single (by
          simp [Bonded, structureF, fBondOrder])).trans (fRing_to_root i))
  | .hydroxylOxygen i =>
      (Relation.ReflTransGen.single (show
        Bonded structureF (.hydroxylOxygen i) (.carboxylCarbon i) by
          simp [Bonded, structureF, fBondOrder])).trans
        ((Relation.ReflTransGen.single (by
          simp [Bonded, structureF, fBondOrder])).trans (fRing_to_root i))
  | .acidicHydrogen i =>
      (Relation.ReflTransGen.single (show
        Bonded structureF (.acidicHydrogen i) (.hydroxylOxygen i) by
          simp [Bonded, structureF, fBondOrder])).trans
        ((Relation.ReflTransGen.single (show
          Bonded structureF (.hydroxylOxygen i) (.carboxylCarbon i) by
            simp [Bonded, structureF, fBondOrder])).trans
          ((Relation.ReflTransGen.single (by
            simp [Bonded, structureF, fBondOrder])).trans (fRing_to_root i)))

private theorem gAtom_to_root :
    ∀ a, Relation.ReflTransGen (Bonded structureG) a (.ring 0)
  | .ring i => gRing_to_root i
  | .acylCarbon i =>
      (Relation.ReflTransGen.single (by
        simp [Bonded, structureG, gBondOrder])).trans (gRing_to_root i)
  | .carbonylOxygen i =>
      (Relation.ReflTransGen.single (show
        Bonded structureG (.carbonylOxygen i) (.acylCarbon i) by
          simp [Bonded, structureG, gBondOrder])).trans
        ((Relation.ReflTransGen.single (by
          simp [Bonded, structureG, gBondOrder])).trans (gRing_to_root i))
  | .bridgingOxygen j =>
      (Relation.ReflTransGen.single (show
        Bonded structureG (.bridgingOxygen j) (.acylCarbon (evenSite j)) by
          simp [Bonded, structureG, gBondOrder, bridgeIncident])).trans
        ((Relation.ReflTransGen.single (by
          simp [Bonded, structureG, gBondOrder])).trans
            (gRing_to_root (evenSite j)))

private theorem structureE_connected : Connected structureE := by
  intro a b
  exact (eAtom_to_root a).trans
    (reflTransGen_reverse_of_symmetric eBonded_symmetric (eAtom_to_root b))

private theorem structureF_connected : Connected structureF := by
  intro a b
  exact (fAtom_to_root a).trans
    (reflTransGen_reverse_of_symmetric fBonded_symmetric (fAtom_to_root b))

private theorem structureG_connected : Connected structureG := by
  intro a b
  exact (gAtom_to_root a).trans
    (reflTransGen_reverse_of_symmetric gBonded_symmetric (gAtom_to_root b))

private theorem rotateE_axis : HasRotationalAxisOrder structureE rotateE 6 := by
  refine ⟨by native_decide, ?_, ?_⟩
  · refine ⟨by norm_num, by native_decide, ?_⟩
    intro k hk hlt
    interval_cases k <;> norm_num at hk ⊢
    all_goals exact ⟨EAtom.ring 0, by native_decide⟩
  · unfold PreservesStructure
    native_decide

private theorem rotateF_axis : HasRotationalAxisOrder structureF rotateF 6 := by
  refine ⟨by native_decide, ?_, ?_⟩
  · refine ⟨by norm_num, by native_decide, ?_⟩
    intro k hk hlt
    interval_cases k <;> norm_num at hk ⊢
    all_goals exact ⟨FAtom.ring 0, by native_decide⟩
  · unfold PreservesStructure
    native_decide

private theorem rotateG_axis : HasRotationalAxisOrder structureG rotateG 3 := by
  refine ⟨by native_decide, ?_, ?_⟩
  · refine ⟨by norm_num, by native_decide, ?_⟩
    intro k hk hlt
    interval_cases k <;> norm_num at hk ⊢
    all_goals exact ⟨GAtom.ring 0, by native_decide⟩
  · unfold PreservesStructure
    native_decide

/-! ## Requested-output specifications -/

/-- Every decisive source constraint and every atom-level drawing obligation
for output E. -/
def StructureEOutput : Prop :=
  formulaOf structureE = formulaE ∧
  CompleteNeutralClosedShell structureE ∧
  HasMethylAtEveryRingSite structureE ∧
  sourceData.eSymmetry = .exactAxisOrder 6 ∧
  HasRotationalAxisOrder structureE rotateE 6 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
    (elementMassPercent .hydrogen formulaE)
    sourceData.eHydrogenPercentShown
    sourceData.eHydrogenPercentQuantum

/-- Every decisive source constraint and every atom-level drawing obligation
for output F. -/
def StructureFOutput : Prop :=
  formulaOf structureF = formulaF ∧
  CompleteNeutralClosedShell structureF ∧
  HasCarboxylicAcidAtEveryRingSite structureF ∧
  HasRotationalAxisOrder structureF rotateF 6 ∧
  sourceData.fSymmetry = .highlySymmetricAcid

/-- Every decisive source constraint and every atom-level drawing obligation
for output G. -/
def StructureGOutput : Prop :=
  formulaOf structureG = formulaG ∧
  CompleteNeutralClosedShell structureG ∧
  HasThreeAnhydrideBridges structureG ∧
  sourceData.gComposition = .binaryCompound ∧
  IsBinaryFormula formulaG ∧
  sourceData.gSymmetry = .exactAxisOrder 3 ∧
  HasRotationalAxisOrder structureG rotateG 3 ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
    (elementMassPercent .oxygen formulaG)
    sourceData.gOxygenPercentShown
    sourceData.gOxygenPercentQuantum

/-- Non-structural shared context retained from the A5 paragraph. -/
def SourceContextAudit : Prop :=
  sourceData.stoneOrigin = .coalDeposit ∧
  sourceData.stoneAnionParent = .F

/-- Raw solve-phase proposition: the concrete graph triple satisfies the
measurements, symmetries, functional-group patterns, and both source-located
qualitative arrows. -/
def RawResult : Prop :=
  StructureEOutput ∧ StructureFOutput ∧ StructureGOutput ∧
  SourceContextAudit ∧ OxidationArrowAudit ∧ DehydrationArrowAudit

/-- Exact-symbolic reported proposition.  There is no numerical reporting
boundary in this multi-structure answer; the three complete graph carriers are
the reportable objects. -/
def ReportedResult : Prop :=
  RawResult ∧
  HasMethylAtEveryRingSite structureE ∧
  HasCarboxylicAcidAtEveryRingSite structureF ∧
  HasThreeAnhydrideBridges structureG

theorem structure_e_output : StructureEOutput := by
  refine ⟨by native_decide, ?_, ?_, rfl, rotateE_axis, ?_⟩
  · refine ⟨by native_decide, ?_, structureE_connected, by simp [structureE]⟩
    intro a b
    simpa [structureE] using eBondOrder_symmetric a b
  · simp [HasMethylAtEveryRingSite, structureE, eElement, eBondOrder]
  · norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
      elementMassPercent, formulaMass, MolecularFormula.count, formulaE,
      atomicWeight, sourceData]

theorem structure_f_output : StructureFOutput := by
  refine ⟨by native_decide, ?_, ?_, rotateF_axis, rfl⟩
  refine ⟨by native_decide, ?_, structureF_connected, by simp [structureF]⟩
  intro a b
  simpa [structureF] using fBondOrder_symmetric a b
  simp [HasCarboxylicAcidAtEveryRingSite, structureF, fElement, fBondOrder]

theorem structure_g_output : StructureGOutput := by
  refine ⟨by native_decide, ?_, ?_, rfl, ?_,
    rfl, rotateG_axis, ?_⟩
  · refine ⟨by native_decide, ?_, structureG_connected, by simp [structureG]⟩
    intro a b
    simpa [structureG] using gBondOrder_symmetric a b
  · simp [HasThreeAnhydrideBridges, structureG, gElement, gBondOrder,
      bridgeIncident]
  · norm_num [IsBinaryFormula, MolecularFormula.presentElementCount, formulaG]
  · norm_num [IChO2026Chem.Reporting.ConsistentMeasurement,
      elementMassPercent, formulaMass, MolecularFormula.count, formulaG,
      atomicWeight, sourceData]

theorem source_context_audit : SourceContextAudit := by
  unfold SourceContextAudit
  exact ⟨rfl, rfl⟩

theorem oxidation_arrow_audit : OxidationArrowAudit := by
  simp [OxidationArrowAudit, OxidationConnectivityCorrespondence, stageUse,
    sourceData, structureE, structureF, eElement, fElement, eBondOrder,
    fBondOrder]

theorem dehydration_arrow_audit : DehydrationArrowAudit := by
  simp [DehydrationArrowAudit, DehydrationConnectivityCorrespondence,
    TrianhydrideAtomAccounting, HasThreeAnhydrideBridges, stageUse, sourceData,
    formulaF, formulaG, MolecularFormula.add, MolecularFormula.nsmul,
    waterFormula, structureF, structureG, fElement, gElement, fBondOrder,
    gBondOrder, bridgeIncident]

theorem raw_result : RawResult := by
  exact ⟨structure_e_output, structure_f_output, structure_g_output,
    source_context_audit, oxidation_arrow_audit, dehydration_arrow_audit⟩

theorem reported_result : ReportedResult := by
  exact ⟨raw_result, structure_e_output.2.2.1,
    structure_f_output.2.2.1, structure_g_output.2.2.1⟩

/-- Hash-bound raw solve artifact.  The marker is generated from the exact
answer-blind candidate payload by the controller-supplied canonical helper. -/
theorem raw_result_contract :
    ("ffdfa3dd71e49d56cebda3af2afe3cbbf20ad7766a52e5fa1159ccf54a4d66cc" : String) =
      "ffdfa3dd71e49d56cebda3af2afe3cbbf20ad7766a52e5fa1159ccf54a4d66cc" ∧
    RawResult := by
  exact ⟨rfl, raw_result⟩

/-- Hash-bound exact-symbolic reporting artifact. -/
theorem reported_result_contract :
    ("83b8eed426c27af12d86291d9db576703aafb466c399ee7b8a4f6b8e94435f74" : String) =
      "83b8eed426c27af12d86291d9db576703aafb466c399ee7b8a4f6b8e94435f74" ∧
    ReportedResult := by
  exact ⟨rfl, reported_result⟩

end

end IChO2026Problems.T1A5
