import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T7-A5

This is an answer-blind formalization of the structure-drawing task.  It keeps
three logically different kinds of evidence separate:

* the precursor and ligand skeleton read from the bound problem image;
* the exact gas-uptake calculation used as a primitive-stoichiometry check;
* a typed observation of Figure 1a of Arashiba--Miyake--Nishibayashi,
  DOI `10.1038/nchem.906`, which nominates the complete coordination topology.

The public figure is used only to nominate and check a concrete witness.  It
does not establish a yield, a complete material balance, sole-product status,
or open-world uniqueness.  Conditions omitted by the problem (solvent, time,
temperature and byproducts) remain unknown.  Accordingly the source arrow is
classified as `qualitativeNamedTransformOnly`.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T7A5

/-! ## Typed provenance and molecular structures -/

inductive EvidenceOrigin where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | publicLiterature
  | derivedTheorem
deriving DecidableEq, Repr

structure EvidenceCitation where
  origin : EvidenceOrigin
  title : String
  doi : String
  stableURL : String
  locator : String
  exactScopedClaim : String
  applicabilityConditions : List String
  exclusions : List String
  contentSha256 : String
deriving Repr

inductive Element where
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  | phosphorus
  | chlorine
  | sodium
  | molybdenum
deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | none
  | single
  | double
  | triple
  | coordination
deriving DecidableEq, Fintype, Repr

/-- `formalCharge` is distinct from oxidation state.  Every isotope, charge,
radical and implicit hydrogen suppressed by a skeletal drawing is explicit. -/
structure AtomLabel where
  element : Element
  isotope : Option ℕ := none
  formalCharge : ℤ := 0
  radicalElectrons : ℕ := 0
  implicitHydrogens : ℕ := 0
deriving DecidableEq, Repr

inductive TetrahedralConfiguration where
  | clockwise
  | anticlockwise
deriving DecidableEq, Repr

structure MolecularGraph (V : Type) where
  atom : V → AtomLabel
  bondOrder : V → V → BondOrder
  bondOrder_symm : ∀ a b, bondOrder a b = bondOrder b a
  no_self_bond : ∀ a, bondOrder a a = .none

/-- A structure drawing consists of a labelled graph plus the spatial data
which a plain graph cannot express.  `transAt m a b` says that donors `a` and
`b` are mutually trans at centre `m`. -/
structure MolecularStructure (V : Type) extends MolecularGraph V where
  tetrahedralConfiguration : V → Option TetrahedralConfiguration
  transAt : V → V → V → Prop
  transAt_symm : ∀ m a b, transAt m a b ↔ transAt m b a
  transAt_irrefl : ∀ m a, ¬ transAt m a a

def atomCount (a : AtomLabel) (e : Element) : ℕ :=
  (if a.element = e then 1 else 0) +
    (if e = .hydrogen then a.implicitHydrogens else 0)

def graphElementCount {V : Type} [Fintype V] (g : MolecularGraph V)
    (e : Element) : ℕ :=
  ∑ v : V, atomCount (g.atom v) e

def graphFormalCharge {V : Type} [Fintype V] (g : MolecularGraph V) : ℤ :=
  ∑ v : V, (g.atom v).formalCharge

def graphRadicalElectrons {V : Type} [Fintype V]
    (g : MolecularGraph V) : ℕ :=
  ∑ v : V, (g.atom v).radicalElectrons

def IsPair {α : Type} (a b x y : α) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

theorem isPair_comm {α : Type} (a b x y : α) :
    IsPair a b x y ↔ IsPair b a x y := by
  simp only [IsPair]
  aesop

theorem not_isPair_self_of_ne {α : Type} (a x y : α) (hxy : x ≠ y) :
    ¬ IsPair a a x y := by
  rintro (h | h)
  · exact hxy (h.1.symm.trans h.2)
  · exact hxy (h.2.symm.trans h.1)

/-! ## Full PNP ligand read from the problem inset -/

inductive PincerArm where
  | upper
  | lower
deriving DecidableEq, Fintype, Repr

inductive PhosphineSubstituent where
  | first
  | second
deriving DecidableEq, Fintype, Repr

inductive MethylBranch where
  | first
  | second
  | third
deriving DecidableEq, Fintype, Repr

inductive PyridineCarbon where
  | upperSubstituted
  | upperMeta
  | para
  | lowerMeta
  | lowerSubstituted
deriving DecidableEq, Fintype, Repr

/-- All 26 non-hydrogen atoms in one
2,6-bis((di-tert-butylphosphino)methyl)pyridine ligand. -/
inductive PincerHeavyAtom where
  | pyridineN
  | pyridineC (position : PyridineCarbon)
  | methylene (arm : PincerArm)
  | phosphorus (arm : PincerArm)
  | tertButylCentral (arm : PincerArm) (substituent : PhosphineSubstituent)
  | tertButylMethyl (arm : PincerArm) (substituent : PhosphineSubstituent)
      (branch : MethylBranch)
deriving DecidableEq, Fintype, Repr

def pincerAtomLabel : PincerHeavyAtom → AtomLabel
  | .pyridineN => { element := .nitrogen }
  | .pyridineC .upperSubstituted => { element := .carbon }
  | .pyridineC .lowerSubstituted => { element := .carbon }
  | .pyridineC _ => { element := .carbon, implicitHydrogens := 1 }
  | .methylene _ => { element := .carbon, implicitHydrogens := 2 }
  | .phosphorus _ => { element := .phosphorus }
  | .tertButylCentral _ _ => { element := .carbon }
  | .tertButylMethyl _ _ _ => { element := .carbon, implicitHydrogens := 3 }

def PincerDoubleBond (a b : PincerHeavyAtom) : Prop :=
  IsPair a b .pyridineN (.pyridineC .upperSubstituted) ∨
  IsPair a b (.pyridineC .upperMeta) (.pyridineC .para) ∨
  IsPair a b (.pyridineC .lowerMeta) (.pyridineC .lowerSubstituted)

def PincerSingleBond (a b : PincerHeavyAtom) : Prop :=
  IsPair a b (.pyridineC .upperSubstituted) (.pyridineC .upperMeta) ∨
  IsPair a b (.pyridineC .para) (.pyridineC .lowerMeta) ∨
  IsPair a b (.pyridineC .lowerSubstituted) .pyridineN ∨
  (∃ arm : PincerArm,
    IsPair a b
      (.pyridineC (match arm with
        | .upper => .upperSubstituted
        | .lower => .lowerSubstituted))
      (.methylene arm)) ∨
  (∃ arm : PincerArm,
    IsPair a b (.methylene arm) (.phosphorus arm)) ∨
  (∃ (arm : PincerArm) (substituent : PhosphineSubstituent),
    IsPair a b (.phosphorus arm) (.tertButylCentral arm substituent)) ∨
  (∃ (arm : PincerArm) (substituent : PhosphineSubstituent)
      (branch : MethylBranch),
    IsPair a b (.tertButylCentral arm substituent)
      (.tertButylMethyl arm substituent branch))

noncomputable def pincerBondOrder (a b : PincerHeavyAtom) : BondOrder := by
  classical
  exact if PincerDoubleBond a b then .double
    else if PincerSingleBond a b then .single else .none

theorem pincerBondOrder_symm (a b : PincerHeavyAtom) :
    pincerBondOrder a b = pincerBondOrder b a := by
  classical
  have swapPair {x y u v : PincerHeavyAtom} :
      IsPair x y u v → IsPair y x u v :=
    (isPair_comm x y u v).mp
  have swapDouble {x y : PincerHeavyAtom} :
      PincerDoubleBond x y → PincerDoubleBond y x := by
    intro h
    rcases h with h | h | h
    · exact Or.inl (swapPair h)
    · exact Or.inr (Or.inl (swapPair h))
    · exact Or.inr (Or.inr (swapPair h))
  have swapSingle {x y : PincerHeavyAtom} :
      PincerSingleBond x y → PincerSingleBond y x := by
    intro h
    rcases h with h | h | h | ⟨arm, h⟩ | ⟨arm, h⟩ |
      ⟨arm, substituent, h⟩ | ⟨arm, substituent, branch, h⟩
    · exact Or.inl (swapPair h)
    · exact Or.inr (Or.inl (swapPair h))
    · exact Or.inr (Or.inr (Or.inl (swapPair h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨arm, swapPair h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨arm, swapPair h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨arm, substituent, swapPair h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨arm, substituent, branch, swapPair h⟩)))))
  have hd : PincerDoubleBond a b ↔ PincerDoubleBond b a :=
    ⟨swapDouble, swapDouble⟩
  have hs : PincerSingleBond a b ↔ PincerSingleBond b a :=
    ⟨swapSingle, swapSingle⟩
  simp only [pincerBondOrder]
  rw [hd, hs]

theorem pincerBondOrder_self (a : PincerHeavyAtom) :
    pincerBondOrder a a = .none := by
  classical
  have hd : ¬ PincerDoubleBond a a := by
    intro h
    rcases h with h | h | h
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
  have hs : ¬ PincerSingleBond a a := by
    intro h
    rcases h with h | h | h | ⟨arm, h⟩ | ⟨arm, h⟩ |
      ⟨arm, substituent, h⟩ | ⟨arm, substituent, branch, h⟩
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
    · exact (not_isPair_self_of_ne a _ _ (by decide)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
  simp [pincerBondOrder, hd, hs]

noncomputable def pincerGraph : MolecularGraph PincerHeavyAtom where
  atom := pincerAtomLabel
  bondOrder := pincerBondOrder
  bondOrder_symm := pincerBondOrder_symm
  no_self_bond := pincerBondOrder_self

def ligandInsetCitation : EvidenceCitation where
  origin := .problemImage
  title := "IChO 2026 T7 problem page 2"
  doi := ""
  stableURL := ""
  locator := "T7_page-2.png, dashed PNP-ligand inset"
  exactScopedClaim :=
    "The inset expands PNP as 2,6-bis((di-tert-butylphosphino)methyl)pyridine."
  applicabilityConditions := ["the shorthand PNP in precursor 4 is this inset"]
  exclusions := ["no product topology is printed in the inset"]
  contentSha256 :=
    "010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba"

def PincerTemplateFromProblem (g : MolecularGraph PincerHeavyAtom) : Prop :=
  ligandInsetCitation.origin = .problemImage ∧
  (∀ a, g.atom a = pincerAtomLabel a) ∧
  (∀ a b,
    (g.bondOrder a b = .double ↔ PincerDoubleBond a b) ∧
    (g.bondOrder a b = .single ↔ PincerSingleBond a b) ∧
    (g.bondOrder a b = .none ↔
      ¬ PincerDoubleBond a b ∧ ¬ PincerSingleBond a b)) ∧
  graphElementCount g .carbon = 23 ∧
  graphElementCount g .hydrogen = 43 ∧
  graphElementCount g .nitrogen = 1 ∧
  graphElementCount g .phosphorus = 2 ∧
  graphFormalCharge g = 0 ∧
  graphRadicalElectrons g = 0 ∧
  (∀ a, (g.atom a).isotope = none)

theorem pincer_template_from_problem :
    PincerTemplateFromProblem pincerGraph := by
  classical
  have hdisjoint (a b : PincerHeavyAtom) :
      ¬ (PincerDoubleBond a b ∧ PincerSingleBond a b) := by
    rintro ⟨hd, hs⟩
    rcases hd with hd | hd | hd <;>
      rcases hs with hs | hs | hs | ⟨arm, hs⟩ | ⟨arm, hs⟩ |
        ⟨arm, substituent, hs⟩ | ⟨arm, substituent, branch, hs⟩ <;>
      simp [IsPair] at hd hs <;> aesop
  refine ⟨rfl, (fun _ => rfl), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    by_cases hd : PincerDoubleBond a b
    · have hs : ¬ PincerSingleBond a b := fun hs => hdisjoint a b ⟨hd, hs⟩
      simp [pincerGraph, pincerBondOrder, hd, hs]
    · by_cases hs : PincerSingleBond a b
      · simp [pincerGraph, pincerBondOrder, hd, hs]
      · simp [pincerGraph, pincerBondOrder, hd, hs]
  · change (∑ v : PincerHeavyAtom, atomCount (pincerAtomLabel v) .carbon) = 23
    native_decide
  · change (∑ v : PincerHeavyAtom, atomCount (pincerAtomLabel v) .hydrogen) = 43
    native_decide
  · change (∑ v : PincerHeavyAtom, atomCount (pincerAtomLabel v) .nitrogen) = 1
    native_decide
  · change (∑ v : PincerHeavyAtom, atomCount (pincerAtomLabel v) .phosphorus) = 2
    native_decide
  · change (∑ v : PincerHeavyAtom, (pincerAtomLabel v).formalCharge) = 0
    native_decide
  · change (∑ v : PincerHeavyAtom, (pincerAtomLabel v).radicalElectrons) = 0
    native_decide
  · intro a
    cases a with
    | pyridineN => rfl
    | pyridineC position => cases position <;> rfl
    | methylene arm => rfl
    | phosphorus arm => rfl
    | tertButylCentral arm substituent => rfl
    | tertButylMethyl arm substituent branch => rfl

/-! ## Precursor 4 read before any product candidate is introduced -/

inductive ChlorideSite where
  | first
  | second
  | third
deriving DecidableEq, Fintype, Repr

inductive PincerDonor where
  | upperP
  | pyridineN
  | lowerP
deriving DecidableEq, Fintype, Repr

def pincerDonorAtom : PincerDonor → PincerHeavyAtom
  | .upperP => .phosphorus .upper
  | .pyridineN => .pyridineN
  | .lowerP => .phosphorus .lower

inductive PrecursorHeavyAtom where
  | molybdenum
  | ligand (atom : PincerHeavyAtom)
  | chloride (site : ChlorideSite)
deriving DecidableEq, Fintype, Repr

def precursorAtomLabel : PrecursorHeavyAtom → AtomLabel
  | .molybdenum => { element := .molybdenum, formalCharge := 3 }
  | .ligand atom => pincerAtomLabel atom
  | .chloride _ => { element := .chlorine, formalCharge := -1 }

def PrecursorLigandBond (a b : PrecursorHeavyAtom) (order : BondOrder) : Prop :=
  ∃ x y : PincerHeavyAtom,
    IsPair a b (.ligand x) (.ligand y) ∧
    pincerBondOrder x y = order ∧ order ≠ .none

def PrecursorCoordinationBond (a b : PrecursorHeavyAtom) : Prop :=
  (∃ site : ChlorideSite, IsPair a b .molybdenum (.chloride site)) ∨
  (∃ donor : PincerDonor,
    IsPair a b .molybdenum (.ligand (pincerDonorAtom donor)))

noncomputable def precursorBondOrder
    (a b : PrecursorHeavyAtom) : BondOrder := by
  classical
  exact if PrecursorCoordinationBond a b then .coordination
    else if PrecursorLigandBond a b .double then .double
    else if PrecursorLigandBond a b .single then .single else .none

theorem precursorBondOrder_symm (a b : PrecursorHeavyAtom) :
    precursorBondOrder a b = precursorBondOrder b a := by
  classical
  have swapPair {x y u v : PrecursorHeavyAtom} :
      IsPair x y u v → IsPair y x u v :=
    (isPair_comm x y u v).mp
  have hc :
      PrecursorCoordinationBond a b ↔ PrecursorCoordinationBond b a := by
    constructor
    · rintro (⟨site, h⟩ | ⟨donor, h⟩)
      · exact Or.inl ⟨site, swapPair h⟩
      · exact Or.inr ⟨donor, swapPair h⟩
    · rintro (⟨site, h⟩ | ⟨donor, h⟩)
      · exact Or.inl ⟨site, swapPair h⟩
      · exact Or.inr ⟨donor, swapPair h⟩
  have hl (order : BondOrder) :
      PrecursorLigandBond a b order ↔ PrecursorLigandBond b a order := by
    constructor
    · rintro ⟨x, y, hpair, horder, hn⟩
      exact ⟨x, y, swapPair hpair, horder, hn⟩
    · rintro ⟨x, y, hpair, horder, hn⟩
      exact ⟨x, y, swapPair hpair, horder, hn⟩
  simp only [precursorBondOrder]
  rw [hc, hl .double, hl .single]

theorem precursorBondOrder_self (a : PrecursorHeavyAtom) :
    precursorBondOrder a a = .none := by
  classical
  have hc : ¬ PrecursorCoordinationBond a a := by
    rintro (⟨site, h⟩ | ⟨donor, h⟩)
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
  have hl (order : BondOrder) : ¬ PrecursorLigandBond a a order := by
    rintro ⟨x, y, hpair, horder, hnonzero⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      apply hnonzero
      exact horder.symm.trans (pincerBondOrder_self x)
    exact (not_isPair_self_of_ne a (.ligand x) (.ligand y)
      (by simpa using hxy)) hpair
  simp [precursorBondOrder, hc, hl]

noncomputable def precursor4 : MolecularGraph PrecursorHeavyAtom where
  atom := precursorAtomLabel
  bondOrder := precursorBondOrder
  bondOrder_symm := precursorBondOrder_symm
  no_self_bond := precursorBondOrder_self

def precursorFigureCitation : EvidenceCitation where
  origin := .problemImage
  title := "IChO 2026 T7 problem page 2"
  doi := ""
  stableURL := ""
  locator := "T7_page-2.png, lower fixation scheme, structure 4"
  exactScopedClaim :=
    "Precursor 4 is neutral MoCl3(PNP), with P,N,P and three chloride contacts; M_W is 597.824 g mol-1."
  applicabilityConditions := ["the displayed complex is labelled 4"]
  exclusions := ["the product at the arrow tip is not drawn"]
  contentSha256 :=
    "010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba"

def Precursor4FromProblem (g : MolecularGraph PrecursorHeavyAtom) : Prop :=
  precursorFigureCitation.origin = .problemImage ∧
  (∀ a, g.atom a = precursorAtomLabel a) ∧
  (∀ donor,
    g.bondOrder .molybdenum (.ligand (pincerDonorAtom donor)) =
      .coordination) ∧
  (∀ site,
    g.bondOrder .molybdenum (.chloride site) = .coordination) ∧
  Fintype.card ChlorideSite = 3 ∧
  graphElementCount g .carbon = 23 ∧
  graphElementCount g .hydrogen = 43 ∧
  graphElementCount g .nitrogen = 1 ∧
  graphElementCount g .phosphorus = 2 ∧
  graphElementCount g .chlorine = 3 ∧
  graphElementCount g .molybdenum = 1 ∧
  graphFormalCharge g = 0 ∧
  graphRadicalElectrons g = 0 ∧
  (∀ a, (g.atom a).isotope = none)

theorem precursor4_from_problem : Precursor4FromProblem precursor4 := by
  classical
  refine ⟨rfl, (fun _ => rfl), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro donor
    have hc : PrecursorCoordinationBond .molybdenum
        (.ligand (pincerDonorAtom donor)) :=
      Or.inr ⟨donor, Or.inl ⟨rfl, rfl⟩⟩
    simp [precursor4, precursorBondOrder, hc]
  · intro site
    have hc : PrecursorCoordinationBond .molybdenum (.chloride site) :=
      Or.inl ⟨site, Or.inl ⟨rfl, rfl⟩⟩
    simp [precursor4, precursorBondOrder, hc]
  · native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .carbon) = 23
    native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .hydrogen) = 43
    native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .nitrogen) = 1
    native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .phosphorus) = 2
    native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .chlorine) = 3
    native_decide
  · change (∑ v : PrecursorHeavyAtom, atomCount (precursorAtomLabel v) .molybdenum) = 1
    native_decide
  · change (∑ v : PrecursorHeavyAtom, (precursorAtomLabel v).formalCharge) = 0
    native_decide
  · change (∑ v : PrecursorHeavyAtom, (precursorAtomLabel v).radicalElectrons) = 0
    native_decide
  · intro a
    cases a with
    | molybdenum => rfl
    | chloride site => rfl
    | ligand atom =>
      cases atom with
      | pyridineN => rfl
      | pyridineC position => cases position <;> rfl
      | methylene arm => rfl
      | phosphorus arm => rfl
      | tertButylCentral arm substituent => rfl
      | tertButylMethyl arm substituent branch => rfl

/-! ## Inline, answer-blind derivation of the A4 prerequisite -/

inductive Phase where
  | gas
  | aqueous
  | liquid
  | sourceUnspecified
deriving DecidableEq, Fintype, Repr

inductive ArrowDirection where
  | forward
  | reversible
deriving DecidableEq, Repr

inductive A4Species where
  | mdea
  | carbonDioxide
  | water
  | protonatedMdea
  | bicarbonate
deriving DecidableEq, Fintype, Repr

def a4Source : CRNT.Complex A4Species
  | .mdea => 1
  | .carbonDioxide => 1
  | .water => 1
  | _ => 0

def a4Target : CRNT.Complex A4Species
  | .protonatedMdea => 1
  | .bicarbonate => 1
  | _ => 0

def a4CarbonDioxideCapture : CRNT.Reaction A4Species where
  source := a4Source
  target := a4Target

def a4Formula : A4Species → Element → ℕ
  | .mdea, .carbon => 5
  | .mdea, .hydrogen => 13
  | .mdea, .nitrogen => 1
  | .mdea, .oxygen => 2
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .protonatedMdea, .carbon => 5
  | .protonatedMdea, .hydrogen => 14
  | .protonatedMdea, .nitrogen => 1
  | .protonatedMdea, .oxygen => 2
  | .bicarbonate, .carbon => 1
  | .bicarbonate, .hydrogen => 1
  | .bicarbonate, .oxygen => 3
  | _, _ => 0

def a4Charge : A4Species → ℤ
  | .protonatedMdea => 1
  | .bicarbonate => -1
  | _ => 0

def a4Phase : A4Species → Phase
  | .mdea => .aqueous
  | .carbonDioxide => .gas
  | .water => .liquid
  | .protonatedMdea => .aqueous
  | .bicarbonate => .aqueous

def complexElementTotal {S : Type} [Fintype S]
    (c : CRNT.Complex S) (formula : S → Element → ℕ) (e : Element) : ℕ :=
  ∑ s : S, c s * formula s e

def complexChargeTotal {S : Type} [Fintype S]
    (c : CRNT.Complex S) (charge : S → ℤ) : ℤ :=
  ∑ s : S, (c s : ℤ) * charge s

/-- The image gives aqueous N-methyldiethanolamine and CO2; ordinary aqueous
acid/base chemistry supplies the protonated amine/bicarbonate pair. -/
def A4EquationDerived : Prop :=
  (∀ e : Element,
    complexElementTotal a4CarbonDioxideCapture.source a4Formula e =
      complexElementTotal a4CarbonDioxideCapture.target a4Formula e) ∧
  complexChargeTotal a4CarbonDioxideCapture.source a4Charge =
    complexChargeTotal a4CarbonDioxideCapture.target a4Charge ∧
  a4Phase .mdea = .aqueous ∧
  a4Phase .carbonDioxide = .gas ∧
  a4Phase .protonatedMdea = .aqueous ∧
  a4Phase .bicarbonate = .aqueous ∧
  (ArrowDirection.reversible = .reversible)

theorem a4_equation_derived_inline : A4EquationDerived := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro e
    cases e <;>
      native_decide
  · native_decide

/-! ## Problem arrow and its deliberately limited stage semantics -/

inductive NamedArrowInput where
  | dinitrogen
  | sodiumAmalgam
deriving DecidableEq, Fintype, Repr

inductive TransformClaimScope where
  | compatibilityOnly
  | completeMaterialBalance
deriving DecidableEq, Repr

inductive StageUseClassification where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
deriving DecidableEq, Repr

structure QualitativeArrowEvidence where
  reactantLabel : ℕ
  productLabel : ℕ
  direction : ArrowDirection
  namedInputs : Finset NamedArrowInput
  dinitrogenPressureBar : ℝ
  sodiumAmalgamEquivalentsPerPrecursor : ℕ
  solvent : Option String
  temperature : Option String
  duration : Option String
  byproducts : Option (List String)
  yield : Option ℝ
  claimScope : TransformClaimScope
  locator : String

noncomputable def problemArrow : QualitativeArrowEvidence where
  reactantLabel := 4
  productLabel := 5
  direction := .forward
  namedInputs := { .dinitrogen, .sodiumAmalgam }
  dinitrogenPressureBar := 1
  sodiumAmalgamEquivalentsPerPrecursor := 3
  solvent := none
  temperature := none
  duration := none
  byproducts := none
  yield := none
  claimScope := .compatibilityOnly
  locator := "T7_page-2.png, lower fixation arrow"

def selectedStageUse : StageUseClassification :=
  .qualitativeNamedTransformOnly

def ProblemArrowFromFigure : Prop :=
  problemArrow.reactantLabel = 4 ∧
  problemArrow.productLabel = 5 ∧
  problemArrow.direction = .forward ∧
  problemArrow.namedInputs = { .dinitrogen, .sodiumAmalgam } ∧
  problemArrow.dinitrogenPressureBar = 1 ∧
  problemArrow.sodiumAmalgamEquivalentsPerPrecursor = 3

def QualitativeNamedTransformScope : Prop :=
  selectedStageUse = .qualitativeNamedTransformOnly ∧
  problemArrow.claimScope = .compatibilityOnly ∧
  problemArrow.solvent = none ∧
  problemArrow.temperature = none ∧
  problemArrow.duration = none ∧
  problemArrow.byproducts = none ∧
  problemArrow.yield = none

theorem problem_arrow_from_figure : ProblemArrowFromFigure := by
  simp [ProblemArrowFromFigure, problemArrow]

theorem qualitative_named_transform_scope :
    QualitativeNamedTransformScope := by
  simp [QualitativeNamedTransformScope, selectedStageUse, problemArrow]

/-! ## Exact gas-uptake expression and source-derived interval -/

structure DisplayedMeasurement where
  shown : ℝ
  lastDisplayedQuantum : ℝ

structure A5SourceData where
  sampleMassG : DisplayedMeasurement
  precursorMolarMassGPerMol : ℝ
  dinitrogenVolumeCm3 : DisplayedMeasurement
  temperatureK : ℝ
  pressureBar : ℝ
  sodiumEquivalentsPerPrecursor : ℕ

noncomputable def sourceData : A5SourceData where
  sampleMassG := { shown := 1, lastDisplayedQuantum := 1 / 100 }
  precursorMolarMassGPerMol := 597824 / 1000
  dinitrogenVolumeCm3 :=
    { shown := 9497 / 100, lastDisplayedQuantum := 1 / 100 }
  temperatureK := 27315 / 100
  pressureBar := 1
  sodiumEquivalentsPerPrecursor := 3

def uptakeCitation : EvidenceCitation where
  origin := .problemText
  title := "IChO 2026 T7-A5"
  doi := ""
  stableURL := ""
  locator := "T7_page-3.png, box 7.5; molar mass on T7_page-2.png"
  exactScopedClaim :=
    "1.00 g of 4 consumes 94.97 cm3 N2 stoichiometrically at 273.15 K and 1.0 bar; M_W(4)=597.824 g mol-1."
  applicabilityConditions := ["precursor is the displayed complex 4"]
  exclusions := ["no product yield or complete reaction ledger is stated"]
  contentSha256 :=
    "9bc386ab33010a7f8e999035212268ecbeb2ff73ca3a8a108dca96b364e5d47c"

def gasConstantCitation : EvidenceCitation where
  origin := .publicLiterature
  title := "NIST CODATA complete listing of the 2022 constants"
  doi := ""
  stableURL := "https://physics.nist.gov/cuu/Constants/Table/allascii.txt"
  locator := "molar gas constant row"
  exactScopedClaim :=
    "R = 8.314462618... J mol-1 K-1 and its standard uncertainty is exact."
  applicabilityConditions := [
    "ideal-gas amount calculation",
    "the exact SI defining-constant product is converted using 1 L bar = 100 J"
  ]
  exclusions := ["no empirical claim about the coordination product"]
  contentSha256 :=
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"

def avogadroConstantCitation : EvidenceCitation where
  origin := .publicLiterature
  title := "NIST CODATA complete listing of the 2022 constants"
  doi := ""
  stableURL := "https://physics.nist.gov/cuu/Constants/Table/allascii.txt"
  locator := "Avogadro constant row"
  exactScopedClaim := "N_A = 6.02214076 x 10^23 mol-1, exactly."
  applicabilityConditions := ["SI defining constant"]
  exclusions := ["no chemistry-product claim"]
  contentSha256 :=
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"

def boltzmannConstantCitation : EvidenceCitation where
  origin := .publicLiterature
  title := "NIST CODATA complete listing of the 2022 constants"
  doi := ""
  stableURL := "https://physics.nist.gov/cuu/Constants/Table/allascii.txt"
  locator := "Boltzmann constant row"
  exactScopedClaim := "k = 1.380649 x 10^-23 J K-1, exactly."
  applicabilityConditions := ["SI defining constant"]
  exclusions := ["no chemistry-product claim"]
  contentSha256 :=
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"

noncomputable def avogadroConstantPerMol : ℝ :=
  602214076000000000000000

noncomputable def boltzmannConstantJPerK : ℝ :=
  1380649 / 100000000000000000000000000000

noncomputable def molarGasConstantJPerMolK : ℝ :=
  avogadroConstantPerMol * boltzmannConstantJPerK

noncomputable def molarGasConstantLBarPerMolK : ℝ :=
  molarGasConstantJPerMolK / 100

def GasConstantReferenceAudit : Prop :=
  gasConstantCitation.origin = .publicLiterature ∧
  gasConstantCitation.stableURL =
    "https://physics.nist.gov/cuu/Constants/Table/allascii.txt" ∧
  avogadroConstantCitation.contentSha256 =
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67" ∧
  boltzmannConstantCitation.contentSha256 =
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67" ∧
  molarGasConstantJPerMolK =
    avogadroConstantPerMol * boltzmannConstantJPerK ∧
  molarGasConstantJPerMolK =
    207861565453831 / 25000000000000 ∧
  molarGasConstantLBarPerMolK = molarGasConstantJPerMolK / 100

theorem gas_constant_reference_audit : GasConstantReferenceAudit := by
  norm_num [GasConstantReferenceAudit, gasConstantCitation,
    avogadroConstantCitation, boltzmannConstantCitation,
    molarGasConstantJPerMolK, molarGasConstantLBarPerMolK,
    avogadroConstantPerMol, boltzmannConstantJPerK]

structure MeasurementRealization where
  sampleMassG : ℝ
  dinitrogenVolumeCm3 : ℝ

def SourceMeasurementCompatible (r : MeasurementRealization) : Prop :=
  IChO2026Chem.Reporting.ConsistentMeasurement
      r.sampleMassG sourceData.sampleMassG.shown
        sourceData.sampleMassG.lastDisplayedQuantum ∧
  IChO2026Chem.Reporting.ConsistentMeasurement
      r.dinitrogenVolumeCm3 sourceData.dinitrogenVolumeCm3.shown
        sourceData.dinitrogenVolumeCm3.lastDisplayedQuantum

noncomputable def precursorAmountMol (r : MeasurementRealization) : ℝ :=
  r.sampleMassG / sourceData.precursorMolarMassGPerMol

noncomputable def dinitrogenAmountMol (r : MeasurementRealization) : ℝ :=
  sourceData.pressureBar * (r.dinitrogenVolumeCm3 / 1000) /
    (molarGasConstantLBarPerMolK * sourceData.temperatureK)

noncomputable def uptakePerPrecursor (r : MeasurementRealization) : ℝ :=
  dinitrogenAmountMol r / precursorAmountMol r

noncomputable def lowerEndpointRealization : MeasurementRealization where
  sampleMassG := sourceData.sampleMassG.shown +
    sourceData.sampleMassG.lastDisplayedQuantum / 2
  dinitrogenVolumeCm3 := sourceData.dinitrogenVolumeCm3.shown -
    sourceData.dinitrogenVolumeCm3.lastDisplayedQuantum / 2

noncomputable def upperEndpointRealization : MeasurementRealization where
  sampleMassG := sourceData.sampleMassG.shown -
    sourceData.sampleMassG.lastDisplayedQuantum / 2
  dinitrogenVolumeCm3 := sourceData.dinitrogenVolumeCm3.shown +
    sourceData.dinitrogenVolumeCm3.lastDisplayedQuantum / 2

noncomputable def sourceUptakeLower : ℝ :=
  uptakePerPrecursor lowerEndpointRealization

noncomputable def sourceUptakeUpper : ℝ :=
  uptakePerPrecursor upperEndpointRealization

/-- The interval is constructed from the displayed half-quantum endpoints
before any topology is introduced. -/
def SourceUptakeIntervalDerived : Prop :=
  sourceUptakeLower < sourceUptakeUpper ∧
  ∀ r, SourceMeasurementCompatible r →
    sourceUptakeLower ≤ uptakePerPrecursor r ∧
    uptakePerPrecursor r ≤ sourceUptakeUpper

theorem source_uptake_interval_derived : SourceUptakeIntervalDerived := by
  refine ⟨?_, ?_⟩
  · norm_num [sourceUptakeLower, sourceUptakeUpper, uptakePerPrecursor,
      lowerEndpointRealization, upperEndpointRealization,
      dinitrogenAmountMol, precursorAmountMol, sourceData,
      molarGasConstantLBarPerMolK, molarGasConstantJPerMolK,
      avogadroConstantPerMol, boltzmannConstantJPerK]
  · intro r hr
    rcases hr with ⟨⟨_, hm⟩, ⟨_, hv⟩⟩
    rw [abs_le] at hm hv
    norm_num [sourceData] at hm hv
    have hmLower : (199 : ℝ) / 200 ≤ r.sampleMassG := by linarith
    have hmUpper : r.sampleMassG ≤ (201 : ℝ) / 200 := by linarith
    have hvLower : (18993 : ℝ) / 200 ≤ r.dinitrogenVolumeCm3 := by linarith
    have hvUpper : r.dinitrogenVolumeCm3 ≤ (18995 : ℝ) / 200 := by linarith
    have hmpos : 0 < r.sampleMassG := by
      nlinarith [hmLower]
    have huptake : uptakePerPrecursor r =
        ((29891200000000000 : ℝ) / 1135547732074278753) *
          r.dinitrogenVolumeCm3 / r.sampleMassG := by
      simp only [uptakePerPrecursor, dinitrogenAmountMol,
        precursorAmountMol]
      norm_num [sourceData, molarGasConstantLBarPerMolK,
        molarGasConstantJPerMolK, avogadroConstantPerMol,
        boltzmannConstantJPerK]
      field_simp [ne_of_gt hmpos]
      all_goals ring
    have hlower : sourceUptakeLower =
        (189241187200000000000 : ℝ) / 76081698048976676451 := by
      norm_num [sourceUptakeLower, uptakePerPrecursor,
        lowerEndpointRealization, dinitrogenAmountMol, precursorAmountMol,
        sourceData, molarGasConstantLBarPerMolK,
        molarGasConstantJPerMolK, avogadroConstantPerMol,
        boltzmannConstantJPerK]
    have hupper : sourceUptakeUpper =
        (567783344000000000000 : ℝ) / 225973998682781471847 := by
      norm_num [sourceUptakeUpper, uptakePerPrecursor,
        upperEndpointRealization, dinitrogenAmountMol, precursorAmountMol,
        sourceData, molarGasConstantLBarPerMolK,
        molarGasConstantJPerMolK, avogadroConstantPerMol,
        boltzmannConstantJPerK]
    constructor
    · rw [hlower, huptake, le_div_iff₀ hmpos]
      linarith
    · rw [hupper, huptake, div_le_iff₀ hmpos]
      linarith

def precursorMoOxidationState : ℤ := 3

def productMoOxidationState : ℤ := 0

/-- A local oxidation-state check, not a claim that a complete reaction or a
particular byproduct stream has been specified. -/
def ReductantElectronCompatibility : Prop :=
  precursorMoOxidationState = 3 ∧
  productMoOxidationState = 0 ∧
  sourceData.sodiumEquivalentsPerPrecursor = 3 ∧
  (sourceData.sodiumEquivalentsPerPrecursor : ℤ) =
    precursorMoOxidationState - productMoOxidationState

theorem reductant_electron_compatibility :
    ReductantElectronCompatibility := by
  norm_num [ReductantElectronCompatibility, precursorMoOxidationState,
    productMoOxidationState, sourceData]

/-! ## Typed observation of the external candidate-nominating figure -/

inductive MetalCentre where
  | left
  | right
deriving DecidableEq, Fintype, Repr

inductive AxialSite where
  | upper
  | lower
deriving DecidableEq, Fintype, Repr

inductive DinitrogenSite where
  | terminal (metal : MetalCentre) (site : AxialSite)
  | bridge
deriving DecidableEq, Fintype, Repr

inductive DinitrogenEnd where
  | first
  | second
deriving DecidableEq, Fintype, Repr

inductive CoordinationPosition where
  | upperP
  | pyridineN
  | lowerP
  | terminalUpper
  | terminalLower
  | bridge
deriving DecidableEq, Fintype, Repr

inductive FigureSkeletonAtom where
  | molybdenum (metal : MetalCentre)
  | pincerDonor (metal : MetalCentre) (donor : PincerDonor)
  | dinitrogen (site : DinitrogenSite) (atom : DinitrogenEnd)
deriving DecidableEq, Fintype, Repr

def terminalDonorSkeleton (metal : MetalCentre) (site : AxialSite) :
    FigureSkeletonAtom :=
  .dinitrogen (.terminal metal site) .first

def bridgeDonorSkeleton : MetalCentre → FigureSkeletonAtom
  | .left => .dinitrogen .bridge .first
  | .right => .dinitrogen .bridge .second

def FigureDinitrogenBond (a b : FigureSkeletonAtom) : Prop :=
  ∃ site : DinitrogenSite,
    IsPair a b (.dinitrogen site .first) (.dinitrogen site .second)

def FigureCoordinationBond (a b : FigureSkeletonAtom) : Prop :=
  (∃ (metal : MetalCentre) (donor : PincerDonor),
    IsPair a b (.molybdenum metal) (.pincerDonor metal donor)) ∨
  (∃ (metal : MetalCentre) (site : AxialSite),
    IsPair a b (.molybdenum metal) (terminalDonorSkeleton metal site)) ∨
  (∃ metal : MetalCentre,
    IsPair a b (.molybdenum metal) (bridgeDonorSkeleton metal))

noncomputable def figureSkeletonBondOrder
    (a b : FigureSkeletonAtom) : BondOrder := by
  classical
  exact if FigureDinitrogenBond a b then .triple
    else if FigureCoordinationBond a b then .coordination else .none

def figureSkeletonFormalCharge (_ : FigureSkeletonAtom) : ℤ := 0

def figureSkeletonRadicalElectrons (_ : FigureSkeletonAtom) : ℕ := 0

def figureSkeletonIsotope (_ : FigureSkeletonAtom) : Option ℕ := none

def FigureTransPair : CoordinationPosition → CoordinationPosition → Prop
  | .upperP, .lowerP => True
  | .lowerP, .upperP => True
  | .pyridineN, .bridge => True
  | .bridge, .pyridineN => True
  | .terminalUpper, .terminalLower => True
  | .terminalLower, .terminalUpper => True
  | _, _ => False

def primaryFigureCitation : EvidenceCitation where
  origin := .publicLiterature
  title :=
    "A molybdenum complex bearing PNP-type pincer ligands leads to the catalytic reduction of dinitrogen into ammonia"
  doi := "10.1038/nchem.906"
  stableURL :=
    "https://media.springernature.com/full/springer-static/image/art%3A10.1038%2Fnchem.906/MediaObjects/41557_2011_Article_BFnchem906_Fig1_HTML.jpg"
  locator :=
    "Figure 1a, Preparation and molecular structure of dinitrogen-bridged dimolybdenum complex 2a"
  exactScopedClaim :=
    "For the depicted MoCl3(PNP)/N2/Na-Hg reaction, Figure 1a draws a neutral dinitrogen-bridged dimolybdenum complex with two terminal end-on N2 ligands at each Mo, one end-on/end-on N2 bridge, retained PNP ligands, and no Mo-Mo bond."
  applicabilityConditions := [
    "the precursor skeleton is MoCl3 with the same PNP ligand",
    "the named inputs are N2 and sodium amalgam",
    "the figure is used only to nominate/check a candidate topology"
  ]
  exclusions := [
    "no transfer of the reported 63 percent yield",
    "no transfer of THF, room temperature, or 12 hour protocol",
    "no sole-product or open-world uniqueness conclusion"
  ]
  contentSha256 :=
    "8ac353a229cb217214ca9f8a5c79f3da939a3d59033a0ed20a6eed8d7ce9c908"

structure LiteratureReactionFingerprint where
  metal : Element
  namedGas : NamedArrowInput
  namedReductant : NamedArrowInput
  chlorideSitesPerPrecursor : ℕ
  ligandCarbon : ℕ
  ligandHydrogen : ℕ
  ligandNitrogen : ℕ
  ligandPhosphorus : ℕ
  precursorMultiplicity : ℕ
  sodiumAmalgamEquivalentsShown : ℕ
  dinitrogenPressureAtmospheres : ℝ
  solvent : String
  temperature : String
  durationHours : ℕ
  reportedYieldPercent : ℕ

noncomputable def literatureFingerprint : LiteratureReactionFingerprint where
  metal := .molybdenum
  namedGas := .dinitrogen
  namedReductant := .sodiumAmalgam
  chlorideSitesPerPrecursor := 3
  ligandCarbon := 23
  ligandHydrogen := 43
  ligandNitrogen := 1
  ligandPhosphorus := 2
  precursorMultiplicity := 2
  sodiumAmalgamEquivalentsShown := 6
  dinitrogenPressureAtmospheres := 1
  solvent := "THF"
  temperature := "room temperature"
  durationHours := 12
  reportedYieldPercent := 63

/-- This proposition is a typed transcription of the cited figure, not a
locally invented inverse-classification rule. -/
def PrimaryFigureObservation : Prop :=
  primaryFigureCitation.origin = .publicLiterature ∧
  primaryFigureCitation.doi = "10.1038/nchem.906" ∧
  primaryFigureCitation.contentSha256 =
    "8ac353a229cb217214ca9f8a5c79f3da939a3d59033a0ed20a6eed8d7ce9c908" ∧
  Fintype.card MetalCentre = 2 ∧
  Fintype.card DinitrogenSite = 5 ∧
  Fintype.card
      {site : DinitrogenSite //
        ∃ metal axial, site = .terminal metal axial} = 4 ∧
  Fintype.card {site : DinitrogenSite // site = .bridge} = 1 ∧
  literatureFingerprint.precursorMultiplicity = 2 ∧
  literatureFingerprint.sodiumAmalgamEquivalentsShown = 6 ∧
  (∀ site,
    figureSkeletonBondOrder (.dinitrogen site .first)
      (.dinitrogen site .second) = .triple) ∧
  (∀ metal donor,
    figureSkeletonBondOrder (.molybdenum metal)
      (.pincerDonor metal donor) = .coordination) ∧
  (∀ metal axial,
    figureSkeletonBondOrder (.molybdenum metal)
      (terminalDonorSkeleton metal axial) = .coordination) ∧
  (∀ metal,
    figureSkeletonBondOrder (.molybdenum metal)
      (bridgeDonorSkeleton metal) = .coordination) ∧
  figureSkeletonBondOrder (.molybdenum .left) (.molybdenum .right) = .none ∧
  (∀ a b,
    (figureSkeletonBondOrder a b = .triple ↔ FigureDinitrogenBond a b) ∧
    (figureSkeletonBondOrder a b = .coordination ↔
      FigureCoordinationBond a b) ∧
    (figureSkeletonBondOrder a b = .none ↔
      ¬ FigureDinitrogenBond a b ∧ ¬ FigureCoordinationBond a b)) ∧
  (∀ a, figureSkeletonFormalCharge a = 0) ∧
  (∀ a, figureSkeletonRadicalElectrons a = 0) ∧
  (∀ a, figureSkeletonIsotope a = none) ∧
  (∀ p q,
    FigureTransPair p q ↔
      IsPair p q .upperP .lowerP ∨
      IsPair p q .pyridineN .bridge ∨
      IsPair p q .terminalUpper .terminalLower)

theorem primary_figure_observation : PrimaryFigureObservation := by
  classical
  have hdisjoint (a b : FigureSkeletonAtom) :
      ¬ (FigureDinitrogenBond a b ∧ FigureCoordinationBond a b) := by
    rintro ⟨⟨site, hd⟩, hc⟩
    rcases hc with ⟨metal, donor, hc⟩ | ⟨metal, axial, hc⟩ |
      ⟨metal, hc⟩ <;>
      simp [IsPair, terminalDonorSkeleton, bridgeDonorSkeleton] at hd hc <;>
      aesop
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro site
    have hd : FigureDinitrogenBond (.dinitrogen site .first)
        (.dinitrogen site .second) :=
      ⟨site, Or.inl ⟨rfl, rfl⟩⟩
    simp [figureSkeletonBondOrder, hd]
  · intro metal donor
    have hc : FigureCoordinationBond (.molybdenum metal)
        (.pincerDonor metal donor) :=
      Or.inl ⟨metal, donor, Or.inl ⟨rfl, rfl⟩⟩
    have hd : ¬ FigureDinitrogenBond (.molybdenum metal)
        (.pincerDonor metal donor) := by
      rintro ⟨site, h⟩
      simp [IsPair] at h
    simp [figureSkeletonBondOrder, hd, hc]
  · intro metal axial
    have hc : FigureCoordinationBond (.molybdenum metal)
        (terminalDonorSkeleton metal axial) :=
      Or.inr (Or.inl ⟨metal, axial, Or.inl ⟨rfl, rfl⟩⟩)
    have hd : ¬ FigureDinitrogenBond (.molybdenum metal)
        (terminalDonorSkeleton metal axial) := by
      rintro ⟨site, h⟩
      simp [IsPair, terminalDonorSkeleton] at h
    simp [figureSkeletonBondOrder, hd, hc]
  · intro metal
    have hc : FigureCoordinationBond (.molybdenum metal)
        (bridgeDonorSkeleton metal) :=
      Or.inr (Or.inr ⟨metal, Or.inl ⟨rfl, rfl⟩⟩)
    have hd : ¬ FigureDinitrogenBond (.molybdenum metal)
        (bridgeDonorSkeleton metal) := by
      rintro ⟨site, h⟩
      cases metal <;> simp [IsPair, bridgeDonorSkeleton] at h
    simp [figureSkeletonBondOrder, hd, hc]
  · simp [figureSkeletonBondOrder, FigureDinitrogenBond,
      FigureCoordinationBond, IsPair, terminalDonorSkeleton,
      bridgeDonorSkeleton]
    intro metal
    cases metal <;> simp
  · intro a b
    by_cases hd : FigureDinitrogenBond a b
    · have hc : ¬ FigureCoordinationBond a b :=
        fun hc => hdisjoint a b ⟨hd, hc⟩
      simp [figureSkeletonBondOrder, hd, hc]
    · by_cases hc : FigureCoordinationBond a b
      · simp [figureSkeletonBondOrder, hd, hc]
      · simp [figureSkeletonBondOrder, hd, hc]
  · intro p q
    cases p <;> cases q <;> simp [FigureTransPair, IsPair]

/-- Only cues actually common to the problem and the paper are matched.  The
paper's solvent, temperature, time and yield are recorded but deliberately not
copied into `problemArrow`. -/
def CandidateNominationApplicability : Prop :=
  Precursor4FromProblem precursor4 ∧
  ProblemArrowFromFigure ∧
  QualitativeNamedTransformScope ∧
  literatureFingerprint.metal = .molybdenum ∧
  literatureFingerprint.namedGas = .dinitrogen ∧
  literatureFingerprint.namedReductant = .sodiumAmalgam ∧
  literatureFingerprint.chlorideSitesPerPrecursor =
    Fintype.card ChlorideSite ∧
  literatureFingerprint.ligandCarbon =
    graphElementCount pincerGraph .carbon ∧
  literatureFingerprint.ligandHydrogen =
    graphElementCount pincerGraph .hydrogen ∧
  literatureFingerprint.ligandNitrogen =
    graphElementCount pincerGraph .nitrogen ∧
  literatureFingerprint.ligandPhosphorus =
    graphElementCount pincerGraph .phosphorus ∧
  literatureFingerprint.sodiumAmalgamEquivalentsShown = 6 ∧
  problemArrow.sodiumAmalgamEquivalentsPerPrecursor = 3 ∧
  problemArrow.dinitrogenPressureBar = 1 ∧
  literatureFingerprint.dinitrogenPressureAtmospheres = 1 ∧
  problemArrow.solvent = none ∧
  problemArrow.temperature = none ∧
  problemArrow.duration = none ∧
  problemArrow.yield = none

theorem candidate_nomination_applicability :
    CandidateNominationApplicability := by
  rcases pincer_template_from_problem with
    ⟨_, _, _, hcarbon, hhydrogen, hnitrogen, hphosphorus, _, _, _⟩
  refine ⟨precursor4_from_problem, problem_arrow_from_figure,
    qualitative_named_transform_scope, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change 3 = Fintype.card ChlorideSite
    native_decide
  · simpa [literatureFingerprint] using hcarbon.symm
  · simpa [literatureFingerprint] using hhydrogen.symm
  · simpa [literatureFingerprint] using hnitrogen.symm
  · simpa [literatureFingerprint] using hphosphorus.symm

/-! ## Complete product graph assembled from the two audited sources -/

inductive ProductHeavyAtom where
  | molybdenum (metal : MetalCentre)
  | ligand (metal : MetalCentre) (atom : PincerHeavyAtom)
  | dinitrogen (site : DinitrogenSite) (atom : DinitrogenEnd)
deriving DecidableEq, Fintype, Repr

def productAtomLabel : ProductHeavyAtom → AtomLabel
  | .molybdenum _ => { element := .molybdenum }
  | .ligand _ atom => pincerAtomLabel atom
  | .dinitrogen _ _ => { element := .nitrogen }

def embedFigureSkeleton : FigureSkeletonAtom → ProductHeavyAtom
  | .molybdenum metal => .molybdenum metal
  | .pincerDonor metal donor => .ligand metal (pincerDonorAtom donor)
  | .dinitrogen site atom => .dinitrogen site atom

def terminalDonor (metal : MetalCentre) (site : AxialSite) : ProductHeavyAtom :=
  .dinitrogen (.terminal metal site) .first

def bridgeDonor : MetalCentre → ProductHeavyAtom
  | .left => .dinitrogen .bridge .first
  | .right => .dinitrogen .bridge .second

def ProductPincerBond (a b : ProductHeavyAtom) (order : BondOrder) : Prop :=
  ∃ (metal : MetalCentre) (x y : PincerHeavyAtom),
    IsPair a b (.ligand metal x) (.ligand metal y) ∧
    pincerBondOrder x y = order ∧ order ≠ .none

def ProductDinitrogenBond (a b : ProductHeavyAtom) : Prop :=
  ∃ site : DinitrogenSite,
    IsPair a b (.dinitrogen site .first) (.dinitrogen site .second)

def ProductCoordinationBond (a b : ProductHeavyAtom) : Prop :=
  (∃ (metal : MetalCentre) (donor : PincerDonor),
    IsPair a b (.molybdenum metal)
      (.ligand metal (pincerDonorAtom donor))) ∨
  (∃ (metal : MetalCentre) (site : AxialSite),
    IsPair a b (.molybdenum metal) (terminalDonor metal site)) ∨
  (∃ metal : MetalCentre,
    IsPair a b (.molybdenum metal) (bridgeDonor metal))

noncomputable def productBondOrder
    (a b : ProductHeavyAtom) : BondOrder := by
  classical
  exact if ProductDinitrogenBond a b then .triple
    else if ProductCoordinationBond a b then .coordination
    else if ProductPincerBond a b .double then .double
    else if ProductPincerBond a b .single then .single else .none

theorem productBondOrder_symm (a b : ProductHeavyAtom) :
    productBondOrder a b = productBondOrder b a := by
  classical
  have swapPair {x y u v : ProductHeavyAtom} :
      IsPair x y u v → IsPair y x u v :=
    (isPair_comm x y u v).mp
  have hd : ProductDinitrogenBond a b ↔ ProductDinitrogenBond b a := by
    constructor
    · rintro ⟨site, h⟩
      exact ⟨site, swapPair h⟩
    · rintro ⟨site, h⟩
      exact ⟨site, swapPair h⟩
  have hc : ProductCoordinationBond a b ↔ ProductCoordinationBond b a := by
    constructor
    · rintro (⟨metal, donor, h⟩ | ⟨metal, site, h⟩ | ⟨metal, h⟩)
      · exact Or.inl ⟨metal, donor, swapPair h⟩
      · exact Or.inr (Or.inl ⟨metal, site, swapPair h⟩)
      · exact Or.inr (Or.inr ⟨metal, swapPair h⟩)
    · rintro (⟨metal, donor, h⟩ | ⟨metal, site, h⟩ | ⟨metal, h⟩)
      · exact Or.inl ⟨metal, donor, swapPair h⟩
      · exact Or.inr (Or.inl ⟨metal, site, swapPair h⟩)
      · exact Or.inr (Or.inr ⟨metal, swapPair h⟩)
  have hp (order : BondOrder) :
      ProductPincerBond a b order ↔ ProductPincerBond b a order := by
    constructor
    · rintro ⟨metal, x, y, hpair, horder, hn⟩
      exact ⟨metal, x, y, swapPair hpair, horder, hn⟩
    · rintro ⟨metal, x, y, hpair, horder, hn⟩
      exact ⟨metal, x, y, swapPair hpair, horder, hn⟩
  simp only [productBondOrder]
  rw [hd, hc, hp .double, hp .single]

theorem productBondOrder_self (a : ProductHeavyAtom) :
    productBondOrder a a = .none := by
  classical
  have hd : ¬ ProductDinitrogenBond a a := by
    rintro ⟨site, h⟩
    exact (not_isPair_self_of_ne a _ _ (by simp)) h
  have hc : ¬ ProductCoordinationBond a a := by
    rintro (⟨metal, donor, h⟩ | ⟨metal, site, h⟩ | ⟨metal, h⟩)
    · exact (not_isPair_self_of_ne a _ _ (by simp)) h
    · exact (not_isPair_self_of_ne a _ _ (by simp [terminalDonor])) h
    · exact (not_isPair_self_of_ne a _ _ (by
        cases metal <;> simp [bridgeDonor])) h
  have hp (order : BondOrder) : ¬ ProductPincerBond a a order := by
    rintro ⟨metal, x, y, hpair, horder, hnonzero⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      apply hnonzero
      exact horder.symm.trans (pincerBondOrder_self x)
    exact (not_isPair_self_of_ne a (.ligand metal x) (.ligand metal y)
      (by simpa using hxy)) hpair
  simp [productBondOrder, hd, hc, hp]

def coordinationAtom (metal : MetalCentre) :
    CoordinationPosition → ProductHeavyAtom
  | .upperP => .ligand metal (.phosphorus .upper)
  | .pyridineN => .ligand metal .pyridineN
  | .lowerP => .ligand metal (.phosphorus .lower)
  | .terminalUpper => terminalDonor metal .upper
  | .terminalLower => terminalDonor metal .lower
  | .bridge => bridgeDonor metal

theorem coordinationAtom_injective (metal : MetalCentre) :
    Function.Injective (coordinationAtom metal) := by
  intro p q h
  cases metal <;> cases p <;> cases q <;>
    simp [coordinationAtom, terminalDonor, bridgeDonor] at h ⊢

def ProductTransRelation
    (centre first second : ProductHeavyAtom) : Prop :=
  ∃ (metal : MetalCentre) (p q : CoordinationPosition),
    centre = .molybdenum metal ∧
    first = coordinationAtom metal p ∧
    second = coordinationAtom metal q ∧
    FigureTransPair p q

theorem productTransRelation_symm (m a b : ProductHeavyAtom) :
    ProductTransRelation m a b ↔ ProductTransRelation m b a := by
  have swapTrans {p q : CoordinationPosition} :
      FigureTransPair p q → FigureTransPair q p := by
    cases p <;> cases q <;> simp [FigureTransPair] at *
  constructor
  · rintro ⟨metal, p, q, hm, ha, hb, hpq⟩
    exact ⟨metal, q, p, hm, hb, ha, swapTrans hpq⟩
  · rintro ⟨metal, p, q, hm, hb, ha, hqp⟩
    exact ⟨metal, q, p, hm, ha, hb, swapTrans hqp⟩

theorem productTransRelation_irrefl (m a : ProductHeavyAtom) :
    ¬ ProductTransRelation m a a := by
  rintro ⟨metal, p, q, hm, hp, hq, hpq⟩
  have hcoord : coordinationAtom metal p = coordinationAtom metal q :=
    hp.symm.trans hq
  have : p = q := coordinationAtom_injective metal hcoord
  subst q
  cases p <;> simp [FigureTransPair] at hpq

noncomputable def structure5 : MolecularStructure ProductHeavyAtom where
  atom := productAtomLabel
  bondOrder := productBondOrder
  bondOrder_symm := productBondOrder_symm
  no_self_bond := productBondOrder_self
  tetrahedralConfiguration := fun _ => none
  transAt := ProductTransRelation
  transAt_symm := productTransRelation_symm
  transAt_irrefl := productTransRelation_irrefl

def ProductBondSpecification
    (g : MolecularGraph ProductHeavyAtom) : Prop :=
  ∀ a b,
    (g.bondOrder a b = .triple ↔ ProductDinitrogenBond a b) ∧
    (g.bondOrder a b = .coordination ↔ ProductCoordinationBond a b) ∧
    (g.bondOrder a b = .double ↔ ProductPincerBond a b .double) ∧
    (g.bondOrder a b = .single ↔ ProductPincerBond a b .single) ∧
    (g.bondOrder a b = .none ↔
      ¬ ProductDinitrogenBond a b ∧
      ¬ ProductCoordinationBond a b ∧
      ¬ ProductPincerBond a b .double ∧
      ¬ ProductPincerBond a b .single)

def RealizesPrimaryFigureSkeleton
    (s : MolecularStructure ProductHeavyAtom) : Prop :=
  (∀ x y : FigureSkeletonAtom,
    s.bondOrder (embedFigureSkeleton x) (embedFigureSkeleton y) =
      figureSkeletonBondOrder x y) ∧
  (∀ metal p q,
    s.transAt (.molybdenum metal)
        (coordinationAtom metal p) (coordinationAtom metal q) ↔
      FigureTransPair p q) ∧
  s.bondOrder (.molybdenum .left) (.molybdenum .right) = .none ∧
  (∀ a : FigureSkeletonAtom,
    (s.atom (embedFigureSkeleton a)).formalCharge =
      figureSkeletonFormalCharge a ∧
    (s.atom (embedFigureSkeleton a)).radicalElectrons =
      figureSkeletonRadicalElectrons a ∧
    (s.atom (embedFigureSkeleton a)).isotope = figureSkeletonIsotope a)

def CandidateCoordinationAudit : Prop :=
  Fintype.card MetalCentre = 2 ∧
  Fintype.card DinitrogenSite = 5 ∧
  Fintype.card
      {site : DinitrogenSite //
        ∃ metal axial, site = .terminal metal axial} = 4 ∧
  Fintype.card {site : DinitrogenSite // site = .bridge} = 1 ∧
  4 + 2 * 1 = Fintype.card MetalCentre * Fintype.card ChlorideSite ∧
  (∀ metal : MetalCentre,
    Fintype.card
        {site : DinitrogenSite //
          ∃ axial, site = .terminal metal axial} = 2) ∧
  Nat.Coprime (Fintype.card MetalCentre) (Fintype.card DinitrogenSite)

theorem candidate_coordination_audit : CandidateCoordinationAudit := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro metal
    cases metal <;> native_decide
  · native_decide

def PrimitiveUptakeCompatibility
    (precursorUnits dinitrogenUnits : ℕ) : Prop :=
  0 < precursorUnits ∧
  Nat.Coprime precursorUnits dinitrogenUnits ∧
  sourceUptakeLower ≤
      (dinitrogenUnits : ℝ) / (precursorUnits : ℝ) ∧
  (dinitrogenUnits : ℝ) / (precursorUnits : ℝ) ≤ sourceUptakeUpper

theorem product_primitive_uptake_compatibility :
    PrimitiveUptakeCompatibility
      (Fintype.card MetalCentre) (Fintype.card DinitrogenSite) := by
  have hmetal : Fintype.card MetalCentre = 2 := by native_decide
  have hsites : Fintype.card DinitrogenSite = 5 := by native_decide
  rw [hmetal, hsites]
  norm_num [PrimitiveUptakeCompatibility, sourceUptakeLower,
    sourceUptakeUpper, uptakePerPrecursor, lowerEndpointRealization,
    upperEndpointRealization, dinitrogenAmountMol, precursorAmountMol,
    sourceData, molarGasConstantLBarPerMolK, molarGasConstantJPerMolK,
    avogadroConstantPerMol, boltzmannConstantJPerK]

/-- Every atom and every possible bond order is constrained independently of
the implementation of `structure5`; the finite graph therefore cannot hide an
extra ligand, chloride, metal--metal edge, charge, radical or stereocentre. -/
def Structure5Specification
    (s : MolecularStructure ProductHeavyAtom) : Prop :=
  CandidateCoordinationAudit ∧
  PrimitiveUptakeCompatibility
    (Fintype.card MetalCentre) (Fintype.card DinitrogenSite) ∧
  (∀ a, s.atom a = productAtomLabel a) ∧
  ProductBondSpecification s.toMolecularGraph ∧
  RealizesPrimaryFigureSkeleton s ∧
  graphElementCount s.toMolecularGraph .carbon = 46 ∧
  graphElementCount s.toMolecularGraph .hydrogen = 86 ∧
  graphElementCount s.toMolecularGraph .nitrogen = 12 ∧
  graphElementCount s.toMolecularGraph .phosphorus = 4 ∧
  graphElementCount s.toMolecularGraph .molybdenum = 2 ∧
  graphElementCount s.toMolecularGraph .chlorine = 0 ∧
  graphFormalCharge s.toMolecularGraph = 0 ∧
  graphRadicalElectrons s.toMolecularGraph = 0 ∧
  (∀ a, (s.atom a).isotope = none) ∧
  (∀ a, s.tetrahedralConfiguration a = none) ∧
  (∀ m a b, s.transAt m a b ↔ ProductTransRelation m a b) ∧
  (∀ metal position,
    s.bondOrder (.molybdenum metal) (coordinationAtom metal position) =
      .coordination) ∧
  (∀ metal, Function.Injective (coordinationAtom metal))

theorem structure5_product_bond_specification :
    ProductBondSpecification structure5.toMolecularGraph := by
  classical
  have hdc (a b : ProductHeavyAtom) :
      ProductDinitrogenBond a b → ¬ ProductCoordinationBond a b := by
    rintro ⟨site, hd⟩ hc
    rcases hc with ⟨metal, donor, hc⟩ | ⟨metal, axial, hc⟩ |
      ⟨metal, hc⟩ <;>
      simp [IsPair, terminalDonor, bridgeDonor] at hd hc <;>
      aesop
  have hdp (a b : ProductHeavyAtom) (order : BondOrder) :
      ProductDinitrogenBond a b → ¬ ProductPincerBond a b order := by
    rintro ⟨site, hd⟩ ⟨metal, x, y, hp, horder, hn⟩
    simp [IsPair] at hd hp
    aesop
  have hcp (a b : ProductHeavyAtom) (order : BondOrder) :
      ProductCoordinationBond a b → ¬ ProductPincerBond a b order := by
    intro hc
    rintro ⟨metal', x, y, hp, horder, hn⟩
    rcases hc with ⟨metal, donor, hc⟩ | ⟨metal, axial, hc⟩ |
      ⟨metal, hc⟩ <;>
      simp [IsPair, terminalDonor, bridgeDonor] at hc hp <;>
      aesop
  have pairUnique {a b : ProductHeavyAtom}
      {metal metal' : MetalCentre} {x y u v : PincerHeavyAtom}
      (hxy : IsPair a b (.ligand metal x) (.ligand metal y))
      (huv : IsPair a b (.ligand metal' u) (.ligand metal' v)) :
      (metal = metal' ∧ x = u ∧ y = v) ∨
        (metal = metal' ∧ x = v ∧ y = u) := by
    simp only [IsPair] at hxy huv ⊢
    aesop
  have hps (a b : ProductHeavyAtom) :
      ProductPincerBond a b .double →
        ¬ ProductPincerBond a b .single := by
    rintro ⟨metal, x, y, hxy, hdouble, _⟩
      ⟨metal', u, v, huv, hsingle, _⟩
    rcases pairUnique hxy huv with hsame | hreverse
    · rcases hsame with ⟨rfl, rfl, rfl⟩
      have : (BondOrder.double : BondOrder) = .single :=
        hdouble.symm.trans hsingle
      cases this
    · rcases hreverse with ⟨rfl, rfl, rfl⟩
      have : (BondOrder.double : BondOrder) = .single := by
        calc
          BondOrder.double = pincerBondOrder x y := hdouble.symm
          _ = pincerBondOrder y x := pincerBondOrder_symm x y
          _ = BondOrder.single := hsingle
      cases this
  intro a b
  by_cases hd : ProductDinitrogenBond a b
  · have hc := hdc a b hd
    have hpd := hdp a b .double hd
    have hpsingle := hdp a b .single hd
    simp [structure5, productBondOrder, hd, hc, hpd, hpsingle]
  · by_cases hc : ProductCoordinationBond a b
    · have hpd := hcp a b .double hc
      have hpsingle := hcp a b .single hc
      simp [structure5, productBondOrder, hd, hc, hpd, hpsingle]
    · by_cases hpd : ProductPincerBond a b .double
      · have hpsingle := hps a b hpd
        simp [structure5, productBondOrder, hd, hc, hpd, hpsingle]
      · by_cases hpsingle : ProductPincerBond a b .single
        · simp [structure5, productBondOrder, hd, hc, hpd, hpsingle]
        · simp [structure5, productBondOrder, hd, hc, hpd, hpsingle]

theorem pincerDonorAtom_injective : Function.Injective pincerDonorAtom := by
  intro a b h
  cases a <;> cases b <;> simp [pincerDonorAtom] at h ⊢

theorem embedFigureSkeleton_injective :
    Function.Injective embedFigureSkeleton := by
  intro x y h
  cases x with
  | molybdenum metal =>
      cases y <;> simp [embedFigureSkeleton] at h ⊢
      all_goals assumption
  | pincerDonor metal donor =>
      cases y with
      | molybdenum metal' => simp [embedFigureSkeleton] at h
      | dinitrogen site atom => simp [embedFigureSkeleton] at h
      | pincerDonor metal' donor' =>
          simp only [embedFigureSkeleton, ProductHeavyAtom.ligand.injEq] at h
          rcases h with ⟨hmetal, hdonor⟩
          have := pincerDonorAtom_injective hdonor
          subst metal'
          subst donor'
          rfl
  | dinitrogen site atom =>
      cases y <;> simp [embedFigureSkeleton] at h ⊢
      all_goals assumption

theorem structure5_realizes_primary_figure :
    RealizesPrimaryFigureSkeleton structure5 := by
  classical
  have hpair (a b x y : FigureSkeletonAtom) :
      IsPair (embedFigureSkeleton a) (embedFigureSkeleton b)
          (embedFigureSkeleton x) (embedFigureSkeleton y) ↔
        IsPair a b x y := by
    constructor
    · rintro (⟨hax, hby⟩ | ⟨hay, hbx⟩)
      · exact Or.inl ⟨embedFigureSkeleton_injective hax,
          embedFigureSkeleton_injective hby⟩
      · exact Or.inr ⟨embedFigureSkeleton_injective hay,
          embedFigureSkeleton_injective hbx⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have hd_iff (a b : FigureSkeletonAtom) :
      ProductDinitrogenBond (embedFigureSkeleton a) (embedFigureSkeleton b) ↔
        FigureDinitrogenBond a b := by
    constructor
    · rintro ⟨site, h⟩
      exact ⟨site, (hpair a b (.dinitrogen site .first)
        (.dinitrogen site .second)).mp h⟩
    · rintro ⟨site, h⟩
      exact ⟨site, (hpair a b (.dinitrogen site .first)
        (.dinitrogen site .second)).mpr h⟩
  have hc_iff (a b : FigureSkeletonAtom) :
      ProductCoordinationBond (embedFigureSkeleton a) (embedFigureSkeleton b) ↔
        FigureCoordinationBond a b := by
    have bridge_embed (metal : MetalCentre) :
        embedFigureSkeleton (bridgeDonorSkeleton metal) = bridgeDonor metal := by
      cases metal <;> rfl
    have metal_embed (metal : MetalCentre) :
        embedFigureSkeleton (.molybdenum metal) = .molybdenum metal := rfl
    constructor
    · rintro (⟨metal, donor, h⟩ | ⟨metal, axial, h⟩ | ⟨metal, h⟩)
      · exact Or.inl ⟨metal, donor,
          (hpair a b (.molybdenum metal) (.pincerDonor metal donor)).mp h⟩
      · exact Or.inr (Or.inl ⟨metal, axial,
          (hpair a b (.molybdenum metal)
            (terminalDonorSkeleton metal axial)).mp h⟩)
      · exact Or.inr (Or.inr ⟨metal,
          (hpair a b (.molybdenum metal)
            (bridgeDonorSkeleton metal)).mp (by
              simpa only [metal_embed, bridge_embed] using h)⟩)
    · rintro (⟨metal, donor, h⟩ | ⟨metal, axial, h⟩ | ⟨metal, h⟩)
      · exact Or.inl ⟨metal, donor,
          (hpair a b (.molybdenum metal) (.pincerDonor metal donor)).mpr h⟩
      · exact Or.inr (Or.inl ⟨metal, axial,
          (hpair a b (.molybdenum metal)
            (terminalDonorSkeleton metal axial)).mpr h⟩)
      · apply Or.inr
        apply Or.inr
        refine ⟨metal, ?_⟩
        have h' := (hpair a b (.molybdenum metal)
          (bridgeDonorSkeleton metal)).mpr h
        simpa only [metal_embed, bridge_embed] using h'
  have hdonor_none (a b : PincerDonor) :
      pincerBondOrder (pincerDonorAtom a) (pincerDonorAtom b) = .none := by
    cases a <;> cases b <;>
      simp [pincerDonorAtom, pincerBondOrder, PincerDoubleBond,
        PincerSingleBond, IsPair]
  have ligandImage {z : FigureSkeletonAtom} {metal : MetalCentre}
      {x : PincerHeavyAtom}
      (h : embedFigureSkeleton z = .ligand metal x) :
      ∃ donor, x = pincerDonorAtom donor := by
    cases z with
    | molybdenum metal' => simp [embedFigureSkeleton] at h
    | dinitrogen site atom => simp [embedFigureSkeleton] at h
    | pincerDonor metal' donor =>
        simp only [embedFigureSkeleton, ProductHeavyAtom.ligand.injEq] at h
        exact ⟨donor, h.2.symm⟩
  have hpfalse (a b : FigureSkeletonAtom) (order : BondOrder) :
      ¬ ProductPincerBond (embedFigureSkeleton a) (embedFigureSkeleton b)
        order := by
    rintro ⟨metal, x, y, hxy, horder, hnonzero⟩
    rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · rcases ligandImage hx with ⟨donorX, hX⟩
      rcases ligandImage hy with ⟨donorY, hY⟩
      subst x
      subst y
      apply hnonzero
      exact horder.symm.trans (hdonor_none donorX donorY)
    · rcases ligandImage hx with ⟨donorX, hX⟩
      rcases ligandImage hy with ⟨donorY, hY⟩
      subst x
      subst y
      apply hnonzero
      exact horder.symm.trans (hdonor_none donorX donorY)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    change productBondOrder (embedFigureSkeleton a) (embedFigureSkeleton b) =
      figureSkeletonBondOrder a b
    by_cases hd : FigureDinitrogenBond a b
    · have hpd := (hd_iff a b).mpr hd
      simp [productBondOrder, figureSkeletonBondOrder, hd, hpd]
    · have hpd : ¬ ProductDinitrogenBond (embedFigureSkeleton a)
          (embedFigureSkeleton b) := fun h => hd ((hd_iff a b).mp h)
      by_cases hc : FigureCoordinationBond a b
      · have hpc := (hc_iff a b).mpr hc
        simp [productBondOrder, figureSkeletonBondOrder, hd, hpd, hc, hpc]
      · have hpc : ¬ ProductCoordinationBond (embedFigureSkeleton a)
            (embedFigureSkeleton b) := fun h => hc ((hc_iff a b).mp h)
        simp [productBondOrder, figureSkeletonBondOrder, hd, hpd, hc, hpc,
          hpfalse]
  · intro metal p q
    change ProductTransRelation (.molybdenum metal)
        (coordinationAtom metal p) (coordinationAtom metal q) ↔
      FigureTransPair p q
    constructor
    · rintro ⟨metal', p', q', hmetal, hp, hq, hpq⟩
      have hmetal' : metal = metal' := by
        simpa using hmetal
      subst metal'
      have hp' : p = p' := coordinationAtom_injective metal hp
      have hq' : q = q' := coordinationAtom_injective metal hq
      subst p'
      subst q'
      exact hpq
    · intro hpq
      exact ⟨metal, p, q, rfl, rfl, rfl, hpq⟩
  · simp [structure5, productBondOrder, ProductDinitrogenBond,
      ProductCoordinationBond, ProductPincerBond, IsPair, terminalDonor,
      bridgeDonor]
    intro metal
    cases metal <;> simp
  · intro a
    cases a with
    | molybdenum metal =>
        simp [structure5, embedFigureSkeleton, productAtomLabel,
          figureSkeletonFormalCharge, figureSkeletonRadicalElectrons,
          figureSkeletonIsotope]
    | pincerDonor metal donor =>
        cases donor <;>
          simp [structure5, embedFigureSkeleton, productAtomLabel,
            pincerDonorAtom, pincerAtomLabel, figureSkeletonFormalCharge,
            figureSkeletonRadicalElectrons, figureSkeletonIsotope]
    | dinitrogen site atom =>
        simp [structure5, embedFigureSkeleton, productAtomLabel,
          figureSkeletonFormalCharge, figureSkeletonRadicalElectrons,
          figureSkeletonIsotope]

theorem structure5_satisfies_specification :
    Structure5Specification structure5 := by
  refine ⟨candidate_coordination_audit,
    product_primitive_uptake_compatibility, (fun _ => rfl),
    structure5_product_bond_specification,
    structure5_realizes_primary_figure, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, (fun _ => rfl), (fun _ _ _ => Iff.rfl), ?_,
    coordinationAtom_injective⟩
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .carbon) = 46
    native_decide
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .hydrogen) = 86
    native_decide
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .nitrogen) = 12
    native_decide
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .phosphorus) = 4
    native_decide
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .molybdenum) = 2
    native_decide
  · change (∑ v : ProductHeavyAtom, atomCount (productAtomLabel v) .chlorine) = 0
    native_decide
  · change (∑ v : ProductHeavyAtom, (productAtomLabel v).formalCharge) = 0
    native_decide
  · change (∑ v : ProductHeavyAtom, (productAtomLabel v).radicalElectrons) = 0
    native_decide
  · intro a
    cases a with
    | molybdenum metal => rfl
    | dinitrogen site atom => rfl
    | ligand metal atom =>
      cases atom with
      | pyridineN => rfl
      | pyridineC position => cases position <;> rfl
      | methylene arm => rfl
      | phosphorus arm => rfl
      | tertButylCentral arm substituent => rfl
      | tertButylMethyl arm substituent branch => rfl
  · intro metal position
    cases position with
    | upperP =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .upperP) := by
          rintro ⟨site, h⟩
          simp [coordinationAtom, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .upperP) :=
          Or.inl ⟨metal, .upperP, Or.inl ⟨rfl, rfl⟩⟩
        simp [structure5, productBondOrder, hd, hc]
    | pyridineN =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .pyridineN) := by
          rintro ⟨site, h⟩
          simp [coordinationAtom, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .pyridineN) :=
          Or.inl ⟨metal, .pyridineN, Or.inl ⟨rfl, rfl⟩⟩
        simp [structure5, productBondOrder, hd, hc]
    | lowerP =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .lowerP) := by
          rintro ⟨site, h⟩
          simp [coordinationAtom, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .lowerP) :=
          Or.inl ⟨metal, .lowerP, Or.inl ⟨rfl, rfl⟩⟩
        simp [structure5, productBondOrder, hd, hc]
    | terminalUpper =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .terminalUpper) := by
          rintro ⟨site, h⟩
          simp [coordinationAtom, terminalDonor, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .terminalUpper) :=
          Or.inr (Or.inl ⟨metal, .upper, Or.inl ⟨rfl, rfl⟩⟩)
        simp [structure5, productBondOrder, hd, hc]
    | terminalLower =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .terminalLower) := by
          rintro ⟨site, h⟩
          simp [coordinationAtom, terminalDonor, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .terminalLower) :=
          Or.inr (Or.inl ⟨metal, .lower, Or.inl ⟨rfl, rfl⟩⟩)
        simp [structure5, productBondOrder, hd, hc]
    | bridge =>
        have hd : ¬ ProductDinitrogenBond (.molybdenum metal)
            (coordinationAtom metal .bridge) := by
          rintro ⟨site, h⟩
          cases metal <;> simp [coordinationAtom, bridgeDonor, IsPair] at h
        have hc : ProductCoordinationBond (.molybdenum metal)
            (coordinationAtom metal .bridge) :=
          Or.inr (Or.inr ⟨metal, Or.inl ⟨rfl, rfl⟩⟩)
        simp [structure5, productBondOrder, hd, hc]

/-! ## Payload-bound raw and exact-symbolic result carriers -/

/-- No finite candidate universe is used.  A concrete literature-nominated
witness is checked against every source constraint relevant to this drawing. -/
noncomputable def Structure5RawResult : Prop :=
  A4EquationDerived ∧
  PincerTemplateFromProblem pincerGraph ∧
  Precursor4FromProblem precursor4 ∧
  ProblemArrowFromFigure ∧
  QualitativeNamedTransformScope ∧
  GasConstantReferenceAudit ∧
  SourceUptakeIntervalDerived ∧
  ReductantElectronCompatibility ∧
  PrimaryFigureObservation ∧
  CandidateNominationApplicability ∧
  Structure5Specification structure5

noncomputable def Structure5ReportedResult : Prop :=
  Structure5RawResult ∧
  Fintype.card MetalCentre = 2 ∧
  Fintype.card DinitrogenSite = 5 ∧
  Fintype.card
      {site : DinitrogenSite //
        ∃ metal axial, site = .terminal metal axial} = 4 ∧
  Fintype.card {site : DinitrogenSite // site = .bridge} = 1 ∧
  structure5.bondOrder (.molybdenum .left) (.molybdenum .right) = .none ∧
  (∀ metal : MetalCentre,
    structure5.bondOrder (.molybdenum metal) (bridgeDonor metal) =
      .coordination) ∧
  graphFormalCharge structure5.toMolecularGraph = 0 ∧
  graphRadicalElectrons structure5.toMolecularGraph = 0 ∧
  (∀ a, structure5.tetrahedralConfiguration a = none)

/-- Payload-bound raw solve-phase result carrier. -/
theorem structure5_raw_result :
    ("155cec46215fe7e100ebda50a4a132078b2876bf5764d09c0c7394ae2ad05780" :
      String) =
      "155cec46215fe7e100ebda50a4a132078b2876bf5764d09c0c7394ae2ad05780" ∧
    Structure5RawResult := by
  refine ⟨rfl, ?_⟩
  exact ⟨a4_equation_derived_inline, pincer_template_from_problem,
    precursor4_from_problem, problem_arrow_from_figure,
    qualitative_named_transform_scope, gas_constant_reference_audit,
    source_uptake_interval_derived, reductant_electron_compatibility,
    primary_figure_observation, candidate_nomination_applicability,
    structure5_satisfies_specification⟩

/-- Payload-bound exact-symbolic reported result carrier. -/
theorem structure5_reported_result :
    ("f8ea8d848a6c7ebc593cba21d0145de6750a9b1884dfd80ce239bbe7f51b4dfd" :
      String) =
      "f8ea8d848a6c7ebc593cba21d0145de6750a9b1884dfd80ce239bbe7f51b4dfd" ∧
    Structure5ReportedResult := by
  refine ⟨rfl, ?_⟩
  rcases candidate_coordination_audit with
    ⟨hmetal, hsites, hterminal, hbridge, _, _, _⟩
  rcases structure5_satisfies_specification with
    ⟨_, _, _, _, hfigure, _, _, _, _, _, _, hcharge, hradical, _,
      htetrahedral, _, hcoordination, _⟩
  rcases hfigure with ⟨_, _, hnoMetalBond, _⟩
  refine ⟨structure5_raw_result.2, hmetal, hsites, hterminal, hbridge,
    hnoMetalBond, ?_, hcharge, hradical, htetrahedral⟩
  intro metal
  simpa only [coordinationAtom] using hcoordination metal .bridge

end ProblemIChO2026T7A5
end IChO2026Problems
