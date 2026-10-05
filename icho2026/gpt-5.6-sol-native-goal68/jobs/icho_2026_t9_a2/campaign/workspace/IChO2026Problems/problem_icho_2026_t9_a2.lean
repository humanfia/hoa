import IChO2026Chem

/-!
# IChO 2026 T9-A2: per-3,6-anhydro-beta-cyclodextrin

The problem input, the two general reaction operations, and the derived answer
are kept in separate namespaces below.  The molecular graph for `K` records
every heavy-atom site of all seven repeats, every bond order, the number of
implicit hydrogens on every site, formal charges, radical electrons, and the
face-defining bond at every stereocentre.
-/

namespace IChO2026Problems.Icho2026T9A2

inductive Chair where
  | fourCOne
  | oneCFour
  deriving DecidableEq, Repr

inductive TemplateChoice where
  | left
  | right
  deriving DecidableEq, Repr

inductive Linkage where
  | alphaOneToFour
  deriving DecidableEq, Repr

/-- The oxygen-bearing state at one of the three initially hydroxylated
positions of a glucopyranosyl repeat. -/
inductive SiteState where
  | hydroxyO
  | tosylateO
  | etherOToC6
  | bondedFromO3
  deriving DecidableEq, Repr

structure RepeatPattern where
  c2 : SiteState
  c3 : SiteState
  c6 : SiteState
  deriving DecidableEq, Repr

structure CDState where
  repeatCount : Nat
  linkage : Linkage
  repeatPattern : RepeatPattern
  chair : Chair
  deriving DecidableEq, Repr

namespace ProblemInput

/-- The statement says that beta-CD has seven alpha-D-glucopyranosyl units. -/
def betaUnits : Nat := 7

/-- The reaction diagram prints seven equivalents of tosyl chloride. -/
def tosylChlorideEquivalents : Nat := 7

/-- The three free alcohol positions shown on each starting repeat are C2,
C3, and C6; the displayed starting chair is the usual `4C1` chair. -/
def betaCD : CDState where
  repeatCount := betaUnits
  linkage := .alphaOneToFour
  repeatPattern := {
    c2 := .hydroxyO
    c3 := .hydroxyO
    c6 := .hydroxyO
  }
  chair := .fourCOne

end ProblemInput

namespace TrustedChemistry

/-- Per-primary tosylation: when one equivalent is supplied for every
identical repeat of the triol, the accessible C6 alcohol on every repeat is
converted to the corresponding tosylate.  This operation leaves C2, C3, the
glycosidic linkage, and all carbon stereocentres unchanged. -/
def perPrimaryTosylation (equivalents : Nat) (cd : CDState) : CDState :=
  if equivalents = cd.repeatCount ∧
      cd.repeatPattern = {
        c2 := .hydroxyO
        c3 := .hydroxyO
        c6 := .hydroxyO
      }
  then
    { cd with repeatPattern := {
        c2 := .hydroxyO
        c3 := .hydroxyO
        c6 := .tosylateO
      }
    }
  else cd

/-- Warm aqueous hydroxide generates the C3 alkoxide, which displaces the
C6 tosylate intramolecularly.  The resulting O3--C6 ether bridge fixes the
repeat in the inverted `1C4` chair. -/
def warmAqueousBase36Closure (cd : CDState) : CDState :=
  if cd.repeatPattern.c3 = .hydroxyO ∧
      cd.repeatPattern.c6 = .tosylateO
  then
    { cd with
      repeatPattern := {
        c2 := cd.repeatPattern.c2
        c3 := .etherOToC6
        c6 := .bondedFromO3
      }
      chair := .oneCFour
    }
  else cd

end TrustedChemistry

namespace Derived

def per6TosylIntermediate : CDState :=
  TrustedChemistry.perPrimaryTosylation
    ProblemInput.tosylChlorideEquivalents ProblemInput.betaCD

def reactionProduct : CDState :=
  TrustedChemistry.warmAqueousBase36Closure per6TosylIntermediate

def per36AnhydroBetaCD : CDState where
  repeatCount := 7
  linkage := .alphaOneToFour
  repeatPattern := {
    c2 := .hydroxyO
    c3 := .etherOToC6
    c6 := .bondedFromO3
  }
  chair := .oneCFour

theorem tosylation_is_per6 :
    per6TosylIntermediate.repeatPattern = {
      c2 := .hydroxyO
      c3 := .hydroxyO
      c6 := .tosylateO
    } := by
  rfl

theorem base_closure_is_per36_anhydro :
    reactionProduct = per36AnhydroBetaCD := by
  rfl

end Derived

inductive Element where
  | C
  | O
  deriving DecidableEq, Repr

/-- Ten heavy-atom sites remain in one repeat of K.  `o36` is the oxygen
originally attached to C3; it is now bonded to both C3 and C6.  `glycosidicO`
belongs to the bond leaving C1 for C4 of the next repeat. -/
inductive ProductSite where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO | hydroxyO2 | o36 | glycosidicO
  deriving DecidableEq, Repr, Fintype

abbrev KAtom := Fin 7 × ProductSite

def atom (repeatIndex : Fin 7) (site : ProductSite) : KAtom :=
  (repeatIndex, site)

def nextRepeat (i : Fin 7) : Fin 7 :=
  ⟨(i.val + 1) % 7, Nat.mod_lt _ (by decide)⟩

def siteElement : ProductSite → Element
  | .c1 | .c2 | .c3 | .c4 | .c5 | .c6 => .C
  | .ringO | .hydroxyO2 | .o36 | .glycosidicO => .O

/-- Hydrogens suppressed in the skeletal drawing: C1--C5 each carry one,
C6 carries two, and the sole remaining alcohol oxygen carries one. -/
def siteImplicitHydrogens : ProductSite → Nat
  | .c1 | .c2 | .c3 | .c4 | .c5 => 1
  | .c6 => 2
  | .hydroxyO2 => 1
  | .ringO | .o36 | .glycosidicO => 0

def UnorderedEdge (a b x y : KAtom) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

/-- Exact heavy-atom connectivity of heptakis(3,6-anhydro)-beta-CD.
The last disjunct closes the seven-member macrocycle through alpha-(1->4)
glycosidic oxygen atoms. -/
def DirectedProductEdge (i : Fin 7) (x y : KAtom) : Prop :=
  (x = atom i .c1 ∧ y = atom i .c2) ∨
  (x = atom i .c2 ∧ y = atom i .c3) ∨
  (x = atom i .c3 ∧ y = atom i .c4) ∨
  (x = atom i .c4 ∧ y = atom i .c5) ∨
  (x = atom i .c5 ∧ y = atom i .ringO) ∨
  (x = atom i .ringO ∧ y = atom i .c1) ∨
  (x = atom i .c5 ∧ y = atom i .c6) ∨
  (x = atom i .c2 ∧ y = atom i .hydroxyO2) ∨
  (x = atom i .c3 ∧ y = atom i .o36) ∨
  (x = atom i .o36 ∧ y = atom i .c6) ∨
  (x = atom i .c1 ∧ y = atom i .glycosidicO) ∨
  (x = atom i .glycosidicO ∧ y = atom (nextRepeat i) .c4)

def ProductAdjacent (a b : KAtom) : Prop :=
  ∃ i : Fin 7, ∃ x y : KAtom,
    DirectedProductEdge i x y ∧ UnorderedEdge a b x y

inductive Face where
  | up
  | down
  deriving DecidableEq, Repr

/-- The face-defining ligand at every carbon stereocentre.  These are the
unchanged alpha-D-gluco configurations, expressed as up/down bonds in the
standard Haworth orientation. -/
def ProductStereo (centre ligand : KAtom) (face : Face) : Prop :=
  ∃ i : Fin 7,
    (centre = atom i .c1 ∧ ligand = atom i .glycosidicO ∧ face = .down) ∨
    (centre = atom i .c2 ∧ ligand = atom i .hydroxyO2 ∧ face = .down) ∨
    (centre = atom i .c3 ∧ ligand = atom i .o36 ∧ face = .up) ∨
    (centre = atom (nextRepeat i) .c4 ∧
      ligand = atom i .glycosidicO ∧ face = .down) ∨
    (centre = atom i .c5 ∧ ligand = atom i .c6 ∧ face = .up)

structure MolecularGraph (Atom : Type) where
  element : Atom → Element
  implicitHydrogens : Atom → Nat
  formalCharge : Atom → Int
  radicalElectrons : Atom → Nat
  bondOrder : Atom → Atom → Nat
  stereo : Atom → Atom → Face → Prop
  chair : Chair

noncomputable def productBondOrder (a b : KAtom) : Nat :=
  @ite Nat (ProductAdjacent a b) (Classical.propDecidable _) 1 0

noncomputable def kGraph : MolecularGraph KAtom where
  element := fun a => siteElement a.2
  implicitHydrogens := fun a => siteImplicitHydrogens a.2
  formalCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  bondOrder := productBondOrder
  stereo := ProductStereo
  chair := .oneCFour

structure Formula where
  carbon : Nat
  hydrogen : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

def elementCount (g : MolecularGraph KAtom) (e : Element) : Nat :=
  ((Finset.univ : Finset KAtom).filter fun a => g.element a = e).card

def hydrogenCount (g : MolecularGraph KAtom) : Nat :=
  ∑ a : KAtom, g.implicitHydrogens a

def graphFormula (g : MolecularGraph KAtom) : Formula where
  carbon := elementCount g .C
  hydrogen := hydrogenCount g
  oxygen := elementCount g .O

theorem productAdjacent_symmetric (a b : KAtom) :
    ProductAdjacent a b ↔ ProductAdjacent b a := by
  constructor
  · rintro ⟨i, x, y, hxy, hab⟩
    refine ⟨i, x, y, hxy, ?_⟩
    rcases hab with hab | hab
    · exact Or.inr ⟨hab.2, hab.1⟩
    · exact Or.inl ⟨hab.2, hab.1⟩
  · rintro ⟨i, x, y, hxy, hba⟩
    refine ⟨i, x, y, hxy, ?_⟩
    rcases hba with hba | hba
    · exact Or.inr ⟨hba.2, hba.1⟩
    · exact Or.inl ⟨hba.2, hba.1⟩

theorem k_bondOrder_symmetric (a b : KAtom) :
    kGraph.bondOrder a b = kGraph.bondOrder b a := by
  by_cases h : ProductAdjacent a b
  · have h' : ProductAdjacent b a := (productAdjacent_symmetric a b).mp h
    simp [kGraph, productBondOrder, h, h']
  · have h' : ¬ ProductAdjacent b a := by
      intro hba
      exact h ((productAdjacent_symmetric a b).mpr hba)
    simp [kGraph, productBondOrder, h, h']

theorem k_has_only_single_bonds (a b : KAtom) :
    kGraph.bondOrder a b = 0 ∨ kGraph.bondOrder a b = 1 := by
  by_cases h : ProductAdjacent a b
  · exact Or.inr (by simp [kGraph, productBondOrder, h])
  · exact Or.inl (by simp [kGraph, productBondOrder, h])

theorem k_is_neutral_and_closed_shell (a : KAtom) :
    kGraph.formalCharge a = 0 ∧ kGraph.radicalElectrons a = 0 := by
  exact ⟨rfl, rfl⟩

theorem k_atom_labels_are_exact (a : KAtom) :
    kGraph.element a = siteElement a.2 ∧
    kGraph.implicitHydrogens a = siteImplicitHydrogens a.2 := by
  exact ⟨rfl, rfl⟩

theorem k_connectivity_is_exact (a b : KAtom) :
    kGraph.bondOrder a b = 1 ↔ ProductAdjacent a b := by
  by_cases h : ProductAdjacent a b
  · simp [kGraph, productBondOrder, h]
  · simp [kGraph, productBondOrder, h]

theorem k_stereo_predicate_is_exact (centre ligand : KAtom) (face : Face) :
    kGraph.stereo centre ligand face ↔ ProductStereo centre ligand face := by
  rfl

theorem k_only_free_hydroxyl_is_c2 (i : Fin 7) (site : ProductSite) :
    (kGraph.element (atom i site) = .O ∧
      kGraph.implicitHydrogens (atom i site) = 1) ↔
      site = .hydroxyO2 := by
  cases site <;> simp [kGraph, atom, siteElement, siteImplicitHydrogens]

theorem k_formula :
    graphFormula kGraph = { carbon := 42, hydrogen := 56, oxygen := 28 } := by
  decide

theorem k_heavy_atom_count : Fintype.card KAtom = 70 := by
  decide

def AlphaDGlucoStereoAt (g : MolecularGraph KAtom) (i : Fin 7) : Prop :=
  g.stereo (atom i .c1) (atom i .glycosidicO) .down ∧
  g.stereo (atom i .c2) (atom i .hydroxyO2) .down ∧
  g.stereo (atom i .c3) (atom i .o36) .up ∧
  g.stereo (atom (nextRepeat i) .c4) (atom i .glycosidicO) .down ∧
  g.stereo (atom i .c5) (atom i .c6) .up

/-- Every face-defining stereochemical bond required on one displayed repeat.
The C4 clause uses the glycosidic oxygen of the preceding repeat. -/
theorem k_stereochemistry_is_alpha_D_gluco (i : Fin 7) :
    AlphaDGlucoStereoAt kGraph i := by
  change ProductStereo (atom i .c1) (atom i .glycosidicO) .down ∧
    ProductStereo (atom i .c2) (atom i .hydroxyO2) .down ∧
    ProductStereo (atom i .c3) (atom i .o36) .up ∧
    ProductStereo (atom (nextRepeat i) .c4) (atom i .glycosidicO) .down ∧
    ProductStereo (atom i .c5) (atom i .c6) .up
  constructor
  · exact ⟨i, Or.inl ⟨rfl, rfl, rfl⟩⟩
  constructor
  · exact ⟨i, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  constructor
  · exact ⟨i, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  constructor
  · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
  · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))⟩

/-- The exact local bonds to add to the right-hand blank template. -/
theorem adjacent_c2_hydroxyl (i : Fin 7) :
    ProductAdjacent (atom i .c2) (atom i .hydroxyO2) := by
  refine ⟨i, atom i .c2, atom i .hydroxyO2, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  · exact Or.inl ⟨rfl, rfl⟩

theorem adjacent_c3_o36 (i : Fin 7) :
    ProductAdjacent (atom i .c3) (atom i .o36) := by
  refine ⟨i, atom i .c3, atom i .o36, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  · exact Or.inl ⟨rfl, rfl⟩

theorem adjacent_o36_c6 (i : Fin 7) :
    ProductAdjacent (atom i .o36) (atom i .c6) := by
  refine ⟨i, atom i .o36, atom i .c6, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))))
  · exact Or.inl ⟨rfl, rfl⟩

theorem adjacent_c5_c6 (i : Fin 7) :
    ProductAdjacent (atom i .c5) (atom i .c6) := by
  refine ⟨i, atom i .c5, atom i .c6, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, rfl⟩))))))
  · exact Or.inl ⟨rfl, rfl⟩

theorem k_template_completion_bonds (i : Fin 7) :
    kGraph.bondOrder (atom i .c2) (atom i .hydroxyO2) = 1 ∧
    kGraph.bondOrder (atom i .c3) (atom i .o36) = 1 ∧
    kGraph.bondOrder (atom i .o36) (atom i .c6) = 1 ∧
    kGraph.bondOrder (atom i .c5) (atom i .c6) = 1 := by
  simp [kGraph, productBondOrder, adjacent_c2_hydroxyl,
    adjacent_c3_o36, adjacent_o36_c6, adjacent_c5_c6]

def favourableTemplate : TemplateChoice :=
  if Derived.reactionProduct.chair = .oneCFour then .right else .left

/-- Requested output 1: tick the right-hand, inverted `1C4` chair. -/
theorem chair_conformation :
    favourableTemplate = .right ∧
    Derived.reactionProduct.chair = .oneCFour := by
  exact ⟨rfl, rfl⟩

/-- Requested output 2: the reaction gives the neutral, closed-shell,
heptakis(3,6-anhydro) graph with one C2 hydroxyl on each repeat and retained
alpha-D-gluco stereochemistry. -/
theorem structure_K :
    Derived.reactionProduct = Derived.per36AnhydroBetaCD ∧
    kGraph.chair = .oneCFour ∧
    graphFormula kGraph = { carbon := 42, hydrogen := 56, oxygen := 28 } ∧
    Fintype.card KAtom = 70 ∧
    (∀ a : KAtom,
      kGraph.element a = siteElement a.2 ∧
      kGraph.implicitHydrogens a = siteImplicitHydrogens a.2) ∧
    (∀ a b : KAtom, kGraph.bondOrder a b = 1 ↔ ProductAdjacent a b) ∧
    (∀ a : KAtom,
      kGraph.formalCharge a = 0 ∧ kGraph.radicalElectrons a = 0) ∧
    (∀ centre ligand : KAtom, ∀ face : Face,
      kGraph.stereo centre ligand face ↔ ProductStereo centre ligand face) ∧
    (∀ i : Fin 7, ∀ site : ProductSite,
      (kGraph.element (atom i site) = .O ∧
        kGraph.implicitHydrogens (atom i site) = 1) ↔
        site = .hydroxyO2) ∧
    (∀ i : Fin 7,
      kGraph.bondOrder (atom i .c3) (atom i .o36) = 1 ∧
      kGraph.bondOrder (atom i .o36) (atom i .c6) = 1) ∧
    (∀ i : Fin 7, AlphaDGlucoStereoAt kGraph i) := by
  refine ⟨Derived.base_closure_is_per36_anhydro, rfl, k_formula,
    k_heavy_atom_count, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact k_atom_labels_are_exact a
  · intro a b
    exact k_connectivity_is_exact a b
  · intro a
    exact k_is_neutral_and_closed_shell a
  · intro centre ligand face
    exact k_stereo_predicate_is_exact centre ligand face
  · intro i site
    exact k_only_free_hydroxyl_is_c2 i site
  · intro i
    exact ⟨(k_template_completion_bonds i).2.1,
      (k_template_completion_bonds i).2.2.1⟩
  · intro i
    exact k_stereochemistry_is_alpha_D_gluco i

#print axioms chair_conformation
#print axioms structure_K
#print axioms k_formula
#print axioms k_bondOrder_symmetric
#print axioms k_connectivity_is_exact

end IChO2026Problems.Icho2026T9A2
