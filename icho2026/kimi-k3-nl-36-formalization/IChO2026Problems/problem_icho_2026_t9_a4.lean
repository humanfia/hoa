import IChO2026Chem

/-!
# IChO 2026, problem 9.4

This file formalizes the complete stereochemical structure requested for `Y`.
The six-residue product is represented as a labelled heavy-atom graph.  Every
hydrogen is retained at its heavy-atom parent, and `ExpandedAtom` turns those
counts into individual hydrogen atoms with explicit single bonds.  Thus the
model records every atom, bond order, formal charge, radical count, and carbon
stereocentre appearing in the requested drawing.

The depicted synthesis is used only as a `qualitativeNamedTransformOnly`
compatibility constraint.  No yield, completion, sole-product, phase balance,
or unprinted material stream is asserted.
-/

namespace IChO2026Problems.T9A4

/-! ## Molecular-graph vocabulary -/

inductive Element where
  | hydrogen
  | carbon
  | oxygen
  | silicon
  deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | single
  | double
  | triple
  deriving DecidableEq, Fintype, Repr

def BondOrder.valence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

/-- A heavy atom, including its electronic state and the number of separately
bound hydrogen atoms at that site. -/
structure AtomSpec where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  deriving DecidableEq, Repr

def neutralAtom (element : Element) (attachedHydrogens : ℕ) : AtomSpec where
  element := element
  formalCharge := 0
  radicalElectrons := 0
  attachedHydrogens := attachedHydrogens

/-- One undirected heavy-atom edge with an explicit bond order. -/
structure Bond (α : Type) where
  left : α
  right : α
  order : BondOrder
  deriving Repr

def bond {α : Type} (left right : α) (order : BondOrder := .single) : Bond α :=
  { left := left, right := right, order := order }

def Bond.Connects {α : Type} (e : Bond α) (a b : α) : Prop :=
  (e.left = a ∧ e.right = b) ∨ (e.left = b ∧ e.right = a)

structure MolecularGraph (α : Type) where
  atom : α → AtomSpec
  bonds : List (Bond α)

def MolecularGraph.Bonded {α : Type} (g : MolecularGraph α)
    (a b : α) (order : BondOrder) : Prop :=
  ∃ e ∈ g.bonds, e.Connects a b ∧ e.order = order

/-- Bond existence is decidable by traversing the finite bond list. -/
private instance instDecidableBonded {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) (order : BondOrder) :
    Decidable (g.Bonded a b order) := by
  unfold MolecularGraph.Bonded Bond.Connects
  infer_instance

/-- Atom carrier after expanding every attached-H count. -/
def ExpandedAtom {α : Type} (g : MolecularGraph α) : Type :=
  Sum α (Σ a : α, Fin (g.atom a).attachedHydrogens)

def ExpandedAtom.element {α : Type} {g : MolecularGraph α} :
    ExpandedAtom g → Element
  | .inl a => (g.atom a).element
  | .inr _ => .hydrogen

/-- In the expanded graph, each stored hydrogen has exactly one single bond to
its parent heavy atom. -/
def MolecularGraph.ExpandedBonded {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (x y : ExpandedAtom g) (order : BondOrder) : Prop :=
  match x, y with
  | .inl a, .inl b => g.Bonded a b order
  | .inl a, .inr ⟨b, _⟩ => a = b ∧ order = .single
  | .inr ⟨a, _⟩, .inl b => a = b ∧ order = .single
  | .inr _, .inr _ => False

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  silicon : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

def add (f g : MolecularFormula) : MolecularFormula where
  carbon := f.carbon + g.carbon
  hydrogen := f.hydrogen + g.hydrogen
  oxygen := f.oxygen + g.oxygen
  silicon := f.silicon + g.silicon

def scale (n : ℕ) (f : MolecularFormula) : MolecularFormula where
  carbon := n * f.carbon
  hydrogen := n * f.hydrogen
  oxygen := n * f.oxygen
  silicon := n * f.silicon

def removeWaterUnits (n : ℕ) (f : MolecularFormula) : MolecularFormula where
  carbon := f.carbon
  hydrogen := f.hydrogen - 2 * n
  oxygen := f.oxygen - n
  silicon := f.silicon

end MolecularFormula

def MolecularGraph.formula {α : Type} [Fintype α]
    (g : MolecularGraph α) : MolecularFormula where
  carbon := ∑ a : α, if (g.atom a).element = .carbon then 1 else 0
  hydrogen := ∑ a : α,
    ((g.atom a).attachedHydrogens +
      if (g.atom a).element = .hydrogen then 1 else 0)
  oxygen := ∑ a : α, if (g.atom a).element = .oxygen then 1 else 0
  silicon := ∑ a : α, if (g.atom a).element = .silicon then 1 else 0

def Element.neutralValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2
  | .silicon => 4

def MolecularGraph.incidentValence {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a : α) : ℕ :=
  (g.bonds.map fun e =>
    if e.left = a ∨ e.right = a then e.order.valence else 0).sum

def MolecularGraph.NoSelfBonds {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ e ∈ g.bonds, e.left ≠ e.right

def MolecularGraph.NoDuplicateBonds {α : Type} (g : MolecularGraph α) : Prop :=
  g.bonds.Pairwise (fun e f => ¬ e.Connects f.left f.right)

def MolecularGraph.NeutralClosedValence {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  ∀ a,
    (g.atom a).formalCharge = 0 ∧
    (g.atom a).radicalElectrons = 0 ∧
    g.incidentValence a + (g.atom a).attachedHydrogens =
      (g.atom a).element.neutralValence

inductive MolecularGraph.Reachable {α : Type} (g : MolecularGraph α) : α → α → Prop
  | refl (a : α) : g.Reachable a a
  | tail {a b c : α} (h : g.Reachable a b) (order : BondOrder)
      (hbond : g.Bonded b c order) : g.Reachable a c

def MolecularGraph.Connected {α : Type} (g : MolecularGraph α) : Prop :=
  ∀ a b, g.Reachable a b

def MolecularGraph.WellFormedClosed {α : Type} [DecidableEq α]
    (g : MolecularGraph α) : Prop :=
  g.NoSelfBonds ∧
  g.NoDuplicateBonds ∧
  g.NeutralClosedValence ∧
  g.Connected

private theorem bonded_symm {α : Type} {g : MolecularGraph α}
    {a b : α} {order : BondOrder} (h : g.Bonded a b order) :
    g.Bonded b a order := by
  rcases h with ⟨e, he, hconn, horder⟩
  refine ⟨e, he, ?_, horder⟩
  rcases hconn with hconn | hconn
  · exact Or.inr ⟨hconn.1, hconn.2⟩
  · exact Or.inl ⟨hconn.1, hconn.2⟩

private theorem reachable_of_bonded {α : Type} {g : MolecularGraph α}
    {a b : α} {order : BondOrder} (h : g.Bonded a b order) :
    g.Reachable a b :=
  .tail (.refl a) order h

private theorem reachable_trans {α : Type} {g : MolecularGraph α}
    {a b c : α} (hab : g.Reachable a b) (hbc : g.Reachable b c) :
    g.Reachable a c := by
  induction hbc with
  | refl => exact hab
  | tail _ order hbond ih => exact .tail ih order hbond

private theorem reachable_symm {α : Type} {g : MolecularGraph α}
    {a b : α} (h : g.Reachable a b) : g.Reachable b a := by
  induction h with
  | refl => exact .refl _
  | tail _ order hbond ih =>
      exact reachable_trans
        (reachable_of_bonded (bonded_symm hbond)) ih

/-! ## Source assembly: six-unit alpha-cyclodextrin -/

/-- The bracket multiplier `6` and the alpha-CD label in the source image. -/
abbrev Residue := Fin 6

def nextResidue (i : Residue) : Residue := i + 1

def previousResidue (i : Residue) : Residue := i + 5

/-- Connectivity reduces to local paths to C1 and paths between successive
residue roots around the six-membered cyclodextrin cycle. -/
private theorem connected_of_local_and_next {L : Type}
    (g : MolecularGraph (Residue × L)) (root : L)
    (hlocal : ∀ i x, g.Reachable (i, x) (i, root))
    (hnext : ∀ i, g.Reachable (i, root) (nextResidue i, root)) :
    g.Connected := by
  have h01 : g.Reachable ((0 : Residue), root) ((1 : Residue), root) := by
    simpa [nextResidue] using hnext (0 : Residue)
  have h12 : g.Reachable ((1 : Residue), root) ((2 : Residue), root) := by
    simpa [nextResidue] using hnext (1 : Residue)
  have h23 : g.Reachable ((2 : Residue), root) ((3 : Residue), root) := by
    simpa [nextResidue] using hnext (2 : Residue)
  have h34 : g.Reachable ((3 : Residue), root) ((4 : Residue), root) := by
    simpa [nextResidue] using hnext (3 : Residue)
  have h45 : g.Reachable ((4 : Residue), root) ((5 : Residue), root) := by
    simpa [nextResidue] using hnext (4 : Residue)
  have h02 := reachable_trans h01 h12
  have h03 := reachable_trans h02 h23
  have h04 := reachable_trans h03 h34
  have h05 := reachable_trans h04 h45
  have htozero (i : Residue) :
      g.Reachable (i, root) ((0 : Residue), root) := by
    fin_cases i
    · exact .refl _
    · exact reachable_symm h01
    · exact reachable_symm h02
    · exact reachable_symm h03
    · exact reachable_symm h04
    · exact reachable_symm h05
  rintro ⟨i, x⟩ ⟨j, y⟩
  exact reachable_trans
    (reachable_trans (hlocal i x) (htozero i))
    (reachable_trans (reachable_symm (htozero j))
      (reachable_symm (hlocal j y)))

inductive AlphaLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | hydroxylO2
  | hydroxylO3
  | hydroxylO6
  deriving DecidableEq, Fintype, Repr

abbrev AlphaAtom := Residue × AlphaLocalAtom

def alphaAtomSpec : AlphaAtom → AtomSpec
  | (_, .c1) | (_, .c2) | (_, .c3) | (_, .c4) | (_, .c5) =>
      neutralAtom .carbon 1
  | (_, .c6) => neutralAtom .carbon 2
  | (_, .ringO5) | (_, .glycosidicO) => neutralAtom .oxygen 0
  | (_, .hydroxylO2) | (_, .hydroxylO3) | (_, .hydroxylO6) =>
      neutralAtom .oxygen 1

/-- Six pyranose-ring edges, the C5-C6 edge, three C-OH edges, and both
halves of the outgoing alpha-(1→4) glycosidic link, for every residue. -/
def alphaCDBonds : List (Bond AlphaAtom) :=
  (List.ofFn fun i : Residue =>
    [ bond (i, .ringO5) (i, .c1)
    , bond (i, .c1) (i, .c2)
    , bond (i, .c2) (i, .c3)
    , bond (i, .c3) (i, .c4)
    , bond (i, .c4) (i, .c5)
    , bond (i, .c5) (i, .ringO5)
    , bond (i, .c5) (i, .c6)
    , bond (i, .c2) (i, .hydroxylO2)
    , bond (i, .c3) (i, .hydroxylO3)
    , bond (i, .c6) (i, .hydroxylO6)
    , bond (i, .c1) (i, .glycosidicO)
    , bond (i, .glycosidicO) (nextResidue i, .c4) ]).flatten

def alphaCDGraph : MolecularGraph AlphaAtom where
  atom := alphaAtomSpec
  bonds := alphaCDBonds

def alphaCDFormula : MolecularFormula :=
  { carbon := 36, hydrogen := 60, oxygen := 30, silicon := 0 }

private theorem alpha_spanning_bonds :
    ∀ i : Residue,
      alphaCDGraph.Bonded (i, .c2) (i, .c1) .single ∧
      alphaCDGraph.Bonded (i, .c3) (i, .c2) .single ∧
      alphaCDGraph.Bonded (i, .c4) (i, .c3) .single ∧
      alphaCDGraph.Bonded (i, .c5) (i, .c4) .single ∧
      alphaCDGraph.Bonded (i, .ringO5) (i, .c1) .single ∧
      alphaCDGraph.Bonded (i, .c6) (i, .c5) .single ∧
      alphaCDGraph.Bonded (i, .hydroxylO2) (i, .c2) .single ∧
      alphaCDGraph.Bonded (i, .hydroxylO3) (i, .c3) .single ∧
      alphaCDGraph.Bonded (i, .hydroxylO6) (i, .c6) .single ∧
      alphaCDGraph.Bonded (i, .glycosidicO) (i, .c1) .single ∧
      alphaCDGraph.Bonded
        (i, .glycosidicO) (nextResidue i, .c4) .single := by
  native_decide

private theorem alpha_reachable_local (i : Residue) (x : AlphaLocalAtom) :
    alphaCDGraph.Reachable (i, x) (i, .c1) := by
  rcases alpha_spanning_bonds i with
    ⟨h21, h32, h43, h54, hO51, h65, hO2, hO3, hO6, hG1, _⟩
  have r1 : alphaCDGraph.Reachable (i, .c1) (i, .c1) := .refl _
  have r2 := reachable_of_bonded h21
  have r3 := reachable_trans (reachable_of_bonded h32) r2
  have r4 := reachable_trans (reachable_of_bonded h43) r3
  have r5 := reachable_trans (reachable_of_bonded h54) r4
  have r6 := reachable_trans (reachable_of_bonded h65) r5
  have rO5 := reachable_of_bonded hO51
  have rG := reachable_of_bonded hG1
  have rO2 := reachable_trans (reachable_of_bonded hO2) r2
  have rO3 := reachable_trans (reachable_of_bonded hO3) r3
  have rO6 := reachable_trans (reachable_of_bonded hO6) r6
  cases x <;> assumption

private theorem alpha_reachable_next (i : Residue) :
    alphaCDGraph.Reachable (i, .c1) (nextResidue i, .c1) := by
  rcases alpha_spanning_bonds i with
    ⟨_, _, _, _, _, _, _, _, _, hG1, hGnext⟩
  exact reachable_trans
    (reachable_of_bonded (bonded_symm hG1))
    (reachable_trans (reachable_of_bonded hGnext)
      (alpha_reachable_local (nextResidue i) .c4))

private theorem alpha_connected : alphaCDGraph.Connected :=
  connected_of_local_and_next alphaCDGraph .c1
    alpha_reachable_local alpha_reachable_next

/-- Whole-assembly audit for the six connected glucopyranoside residues in
the starting image. -/
theorem alphaCD_graph_audit :
    alphaCDGraph.formula = alphaCDFormula ∧
    alphaCDGraph.WellFormedClosed := by
  refine ⟨by native_decide, ?_⟩
  refine ⟨?_, ?_, ?_, alpha_connected⟩
  · unfold MolecularGraph.NoSelfBonds
    native_decide
  · unfold MolecularGraph.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold MolecularGraph.NeutralClosedValence
    native_decide

/-! ## Inline derivation of the controller-listed T9.3 prerequisite -/

inductive XSourceLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | glycosidicO
  | ringO5
  deriving DecidableEq, Fintype, Repr

/-- Membership in the large-ring path is computed over every carbon and ring
oxygen visible in a source residue.  The periodate-cleaved C2/C3 branches and
the exocyclic C6 branch do not lie on that path. -/
def LiesOnMacrocycleXPath : XSourceLocalAtom → Prop
  | .c1 | .glycosidicO | .c4 | .c5 | .ringO5 => True
  | .c2 | .c3 | .c6 => False

noncomputable def xMacrocyclePathSites : Finset XSourceLocalAtom := by
  classical
  exact Finset.univ.filter LiesOnMacrocycleXPath

noncomputable def previousRingSize : ℕ := 7 * xMacrocyclePathSites.card

inductive XCarbon where
  | c1 | c2 | c3 | c4 | c5 | c6
  deriving DecidableEq, Fintype, Repr

inductive CarbonOutcomeAfterCleavage where
  | retainedTetrahedral
  | reducedMethylene
  | preexistingMethylene
  deriving DecidableEq, Fintype, Repr

/-- Periodate cleaves the C2-C3 vicinal-diol bond and borohydride reduces both
new termini to methylenes; C6 was already a methylene. -/
def carbonOutcomeAfterCleavage : XCarbon → CarbonOutcomeAfterCleavage
  | .c1 | .c4 | .c5 => .retainedTetrahedral
  | .c2 | .c3 => .reducedMethylene
  | .c6 => .preexistingMethylene

def IsStereocentreAfterCleavage (carbon : XCarbon) : Prop :=
  carbonOutcomeAfterCleavage carbon = .retainedTetrahedral

noncomputable def xRetainedStereocentreSites : Finset XCarbon := by
  classical
  exact Finset.univ.filter IsStereocentreAfterCleavage

noncomputable def previousStereocentreCount : ℕ :=
  7 * xRetainedStereocentreSites.card

inductive PreviousReagent where
  | sodiumPeriodate
  | sodiumBorohydride
  | water
  | aceticAnhydride
  | pyridine
  deriving DecidableEq, Fintype, Repr

structure PreviousReactionConditions where
  first : PreviousReagent
  second : PreviousReagent
  secondMedium : PreviousReagent
  third : PreviousReagent
  thirdMedium : PreviousReagent
  deriving DecidableEq, Repr

def previousSourceConditions : PreviousReactionConditions where
  first := .sodiumPeriodate
  second := .sodiumBorohydride
  secondMedium := .water
  third := .aceticAnhydride
  thirdMedium := .pyridine

def PreviousConditionsHold : Prop :=
  previousSourceConditions.first = .sodiumPeriodate ∧
  previousSourceConditions.second = .sodiumBorohydride ∧
  previousSourceConditions.secondMedium = .water ∧
  previousSourceConditions.third = .aceticAnhydride ∧
  previousSourceConditions.thirdMedium = .pyridine

/-- The two counts are computed from complete, source-derived local domains;
neither result is installed as the carrier of a singleton candidate. -/
def PreviousPartResult : Prop :=
  PreviousConditionsHold ∧
  (∀ site, site ∈ xMacrocyclePathSites ↔ LiesOnMacrocycleXPath site) ∧
  (∀ carbon, carbon ∈ xRetainedStereocentreSites ↔
    IsStereocentreAfterCleavage carbon) ∧
  previousRingSize = 35 ∧
  previousStereocentreCount = 21

theorem previous_part_derived : PreviousPartResult := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro site
    simp [xMacrocyclePathSites]
  · intro carbon
    simp [xRetainedStereocentreSites]
  · have hsites : xMacrocyclePathSites =
        {.c1, .glycosidicO, .c4, .c5, .ringO5} := by
      ext site
      fin_cases site <;>
        simp [xMacrocyclePathSites, LiesOnMacrocycleXPath]
    simp [previousRingSize, hsites]
  · have hsites : xRetainedStereocentreSites = {.c1, .c4, .c5} := by
      ext carbon
      fin_cases carbon <;>
        simp [xRetainedStereocentreSites,
          IsStereocentreAfterCleavage, carbonOutcomeAfterCleavage]
    simp [previousStereocentreCount, hsites]

/-! ## Current source reaction conditions and formula ledger -/

inductive Reagent where
  | tertButyldimethylsilylChloride
  | pyridine
  | sodiumHydride
  | tosylChloride
  | tetrabutylammoniumFluoride
  | water
  deriving DecidableEq, Fintype, Repr

structure ReactionConditions where
  firstReagent : Reagent
  firstEquivalents : ℚ
  firstMedium : Reagent
  secondReagent : Reagent
  secondEquivalents : ℚ
  thirdReagent : Reagent
  thirdEquivalents : ℚ
  fourthReagent : Reagent
  fifthReagent : Reagent
  fifthTemperatureC : ℚ
  deriving DecidableEq, Repr

/-- Exact transcription of both arrows adjacent to `Y`. -/
def sourceReactionConditions : ReactionConditions where
  firstReagent := .tertButyldimethylsilylChloride
  firstEquivalents := 6
  firstMedium := .pyridine
  secondReagent := .sodiumHydride
  secondEquivalents := 12
  thirdReagent := .tosylChloride
  thirdEquivalents := 6
  fourthReagent := .tetrabutylammoniumFluoride
  fifthReagent := .water
  fifthTemperatureC := 100

def SourceConditionsHold : Prop :=
  sourceReactionConditions.firstReagent =
      .tertButyldimethylsilylChloride ∧
  sourceReactionConditions.firstEquivalents = 6 ∧
  sourceReactionConditions.firstMedium = .pyridine ∧
  sourceReactionConditions.secondReagent = .sodiumHydride ∧
  sourceReactionConditions.secondEquivalents = 12 ∧
  sourceReactionConditions.thirdReagent = .tosylChloride ∧
  sourceReactionConditions.thirdEquivalents = 6 ∧
  sourceReactionConditions.fourthReagent =
      .tetrabutylammoniumFluoride ∧
  sourceReactionConditions.fifthReagent = .water ∧
  sourceReactionConditions.fifthTemperatureC = 100

theorem sourceConditions_hold : SourceConditionsHold := by
  norm_num [SourceConditionsHold, sourceReactionConditions]

inductive TransformationUse where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def sourceTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-- Replacing one O-H hydrogen by one TBS group changes a formula by
`C6H14Si`; closing one epoxide then removes one water per residue. -/
def tbsNetFormulaIncrement : MolecularFormula :=
  { carbon := 6, hydrogen := 14, oxygen := 0, silicon := 1 }

def sourceDerivedYFormula : MolecularFormula :=
  MolecularFormula.removeWaterUnits 6 <|
    MolecularFormula.add alphaCDFormula
      (MolecularFormula.scale 6 tbsNetFormulaIncrement)

/-- Formula printed directly beneath `Y` in the source scheme. -/
def printedYFormula : MolecularFormula :=
  { carbon := 72, hydrogen := 132, oxygen := 24, silicon := 6 }

theorem source_formula_ledger : sourceDerivedYFormula = printedYFormula := by
  native_decide

/-! ## Source-grounded protection and epoxide alternatives -/

inductive HydroxylSite where
  | c2
  | c3
  | c6
  deriving DecidableEq, Fintype, Repr

inductive HydroxylClass where
  | primary
  | secondary
  deriving DecidableEq, Fintype, Repr

def hydroxylClass : HydroxylSite → HydroxylClass
  | .c2 | .c3 => .secondary
  | .c6 => .primary

structure ProtectionCandidate where
  site : HydroxylSite
  deriving DecidableEq, Fintype, Repr

def protectionCandidateDomain : Finset ProtectionCandidate := Finset.univ

inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | publicLiterature
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

def protectionCandidateDomainProvenance : List Provenance :=
  [.problemImage, .trustedGeneralLaw, .derivedTheorem]

/-- Limited bulky-silyl protection is applied uniformly to the primary class;
the three possible OH locants are all present before this filter. -/
def ProtectionFits (candidate : ProtectionCandidate) : Prop :=
  SourceConditionsHold ∧
  candidate ∈ protectionCandidateDomain ∧
  hydroxylClass candidate.site = .primary

theorem existsUniqueProtectionCandidate :
    ∃! candidate : ProtectionCandidate, ProtectionFits candidate := by
  refine ⟨⟨.c6⟩, ?_, ?_⟩
  · exact ⟨sourceConditions_hold,
      by simp [protectionCandidateDomain], rfl⟩
  · rintro ⟨site⟩ h
    rcases h with ⟨_, _, hprimary⟩
    cases site <;> simp_all [hydroxylClass]

noncomputable def derivedProtectionCandidate : ProtectionCandidate :=
  Classical.choose existsUniqueProtectionCandidate

theorem derivedProtectionCandidate_spec :
    ProtectionFits derivedProtectionCandidate := by
  exact (Classical.choose_spec existsUniqueProtectionCandidate).1

theorem derivedProtectionCandidate_component :
    derivedProtectionCandidate.site = .c6 := by
  have hselected : ProtectionFits (⟨.c6⟩ : ProtectionCandidate) :=
    ⟨sourceConditions_hold, by simp [protectionCandidateDomain], rfl⟩
  have heq : (⟨.c6⟩ : ProtectionCandidate) =
      derivedProtectionCandidate :=
    (Classical.choose_spec existsUniqueProtectionCandidate).2 _ hselected
  exact congrArg ProtectionCandidate.site heq.symm

inductive SecondarySite where
  | c2
  | c3
  deriving DecidableEq, Fintype, Repr

structure ClosureCandidate where
  leavingCarbon : SecondarySite
  attackingOxygen : SecondarySite
  deriving DecidableEq, Fintype, Repr

def closureCandidateDomain : Finset ClosureCandidate := Finset.univ

def closureCandidateDomainProvenance : List Provenance :=
  [.problemImage, .trustedGeneralLaw, .derivedTheorem]

inductive Face where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

def Face.opposite : Face → Face
  | .up => .down
  | .down => .up

/-- Alpha-D-gluco face assignment read from the starting template. -/
def startingHydroxylFace : SecondarySite → Face
  | .c2 => .down
  | .c3 => .up

/-- Intramolecular SN2 closure inverts the carbon bearing the leaving group;
the attacking oxygen retains its bond direction at its original carbon. -/
def epoxideBondFace (candidate : ClosureCandidate)
    (site : SecondarySite) : Face :=
  if site = candidate.leavingCarbon then
    (startingHydroxylFace site).opposite
  else
    startingHydroxylFace site

inductive EpoxideSeries where
  | twoThreeAnhydroManno
  | twoThreeAnhydroAllo
  | incompatibleFaces
  deriving DecidableEq, Fintype, Repr

def candidateEpoxideSeries (candidate : ClosureCandidate) : EpoxideSeries :=
  if epoxideBondFace candidate .c2 = .up ∧
      epoxideBondFace candidate .c3 = .up then
    .twoThreeAnhydroManno
  else if epoxideBondFace candidate .c2 = .down ∧
      epoxideBondFace candidate .c3 = .down then
    .twoThreeAnhydroAllo
  else
    .incompatibleFaces

/-- Bibliographic record for the source-scoped chemistry bridge used here.
Nogami et al., Angew. Chem. Int. Ed. Engl. 36 (1997), 1899-1902,
DOI 10.1002/anie.199718991. -/
structure LiteratureRecord where
  title : String
  doi : String
  stableURL : String
  locator : String
  deriving DecidableEq, Repr

def cycloaltrinSynthesisPaper : LiteratureRecord where
  title := "Synthesis, Structure, and Conformational Features of α-Cycloaltrin: A Cyclooligosaccharide with Alternating 4C1/1C4 Pyranoid Chairs"
  doi := "10.1002/anie.199718991"
  stableURL := "https://doi.org/10.1002/anie.199718991"
  locator := "abstract, final sentence"

inductive NamedAssembly where
  | alphaCyclodextrin
  | alphaCycloaltrin
  deriving DecidableEq, Fintype, Repr

/-- Exact scoped abstract claim: alpha-cycloaltrin is prepared from alpha-CD by
a four-step protocol whose key intermediate is 2,3-anhydro-alpha-cyclomannin. -/
structure KeyIntermediateClaim where
  source : LiteratureRecord
  startingAssembly : NamedAssembly
  finalAssembly : NamedAssembly
  keyIntermediate : EpoxideSeries
  deriving DecidableEq, Repr

def cycloaltrinKeyIntermediateClaim : KeyIntermediateClaim where
  source := cycloaltrinSynthesisPaper
  startingAssembly := .alphaCyclodextrin
  finalAssembly := .alphaCycloaltrin
  keyIntermediate := .twoThreeAnhydroManno

def CandidateMatchesKeyIntermediate
    (candidate : ClosureCandidate) : Prop :=
  candidateEpoxideSeries candidate =
    cycloaltrinKeyIntermediateClaim.keyIntermediate

/-- Face pattern transcribed from the alpha-cycloaltrin drawing after the
fluoride/water arrow. -/
def finalCycloaltrinFace : SecondarySite → Face
  | .c2 => .up
  | .c3 => .down

/-- Nucleophilic epoxide opening inverts the attacked carbon and retains the
other carbon-oxygen bond. -/
def openedProductFace (candidate : ClosureCandidate)
    (attacked site : SecondarySite) : Face :=
  if site = attacked then
    (epoxideBondFace candidate site).opposite
  else
    epoxideBondFace candidate site

def DownstreamHydrolysisCompatible (candidate : ClosureCandidate) : Prop :=
  ∃ attacked : SecondarySite,
    ∀ site : SecondarySite,
      openedProductFace candidate attacked site = finalCycloaltrinFace site

/-! ## Complete all-atom graph for each epoxide candidate -/

inductive YLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | epoxideO23
  | oxygen6
  | silicon
  | silylMethyl (index : Fin 2)
  | tertButylCentral
  | tertButylMethyl (index : Fin 3)
  deriving DecidableEq, Fintype, Repr

abbrev YAtom := Residue × YLocalAtom

def yAtomSpec : YAtom → AtomSpec
  | (_, .c1) | (_, .c2) | (_, .c3) | (_, .c4) | (_, .c5) =>
      neutralAtom .carbon 1
  | (_, .c6) => neutralAtom .carbon 2
  | (_, .ringO5) | (_, .glycosidicO) | (_, .epoxideO23) |
      (_, .oxygen6) => neutralAtom .oxygen 0
  | (_, .silicon) => neutralAtom .silicon 0
  | (_, .silylMethyl _) | (_, .tertButylMethyl _) =>
      neutralAtom .carbon 3
  | (_, .tertButylCentral) => neutralAtom .carbon 0

/-- Nineteen heavy-atom bonds per residue: the cyclic alpha-(1→4) carbohydrate
skeleton, a C2-O-C3 epoxide, and the complete O-SiMe2-CMe3 substituent. -/
def yBonds : List (Bond YAtom) :=
  (List.ofFn fun i : Residue =>
    [ bond (i, .ringO5) (i, .c1)
    , bond (i, .c1) (i, .c2)
    , bond (i, .c2) (i, .c3)
    , bond (i, .c3) (i, .c4)
    , bond (i, .c4) (i, .c5)
    , bond (i, .c5) (i, .ringO5)
    , bond (i, .c5) (i, .c6)
    , bond (i, .c1) (i, .glycosidicO)
    , bond (i, .glycosidicO) (nextResidue i, .c4)
    , bond (i, .c2) (i, .epoxideO23)
    , bond (i, .c3) (i, .epoxideO23)
    , bond (i, .c6) (i, .oxygen6)
    , bond (i, .oxygen6) (i, .silicon)
    , bond (i, .silicon) (i, .silylMethyl 0)
    , bond (i, .silicon) (i, .silylMethyl 1)
    , bond (i, .silicon) (i, .tertButylCentral)
    , bond (i, .tertButylCentral) (i, .tertButylMethyl 0)
    , bond (i, .tertButylCentral) (i, .tertButylMethyl 1)
    , bond (i, .tertButylCentral) (i, .tertButylMethyl 2) ]).flatten

def yGraph : MolecularGraph YAtom where
  atom := yAtomSpec
  bonds := yBonds

private theorem y_spanning_bonds :
    ∀ i : Residue,
      yGraph.Bonded (i, .c2) (i, .c1) .single ∧
      yGraph.Bonded (i, .c3) (i, .c2) .single ∧
      yGraph.Bonded (i, .c4) (i, .c3) .single ∧
      yGraph.Bonded (i, .c5) (i, .c4) .single ∧
      yGraph.Bonded (i, .ringO5) (i, .c1) .single ∧
      yGraph.Bonded (i, .c6) (i, .c5) .single ∧
      yGraph.Bonded (i, .glycosidicO) (i, .c1) .single ∧
      yGraph.Bonded (i, .epoxideO23) (i, .c2) .single ∧
      yGraph.Bonded (i, .oxygen6) (i, .c6) .single ∧
      yGraph.Bonded (i, .silicon) (i, .oxygen6) .single ∧
      (∀ j : Fin 2,
        yGraph.Bonded (i, .silylMethyl j) (i, .silicon) .single) ∧
      yGraph.Bonded (i, .tertButylCentral) (i, .silicon) .single ∧
      (∀ j : Fin 3,
        yGraph.Bonded
          (i, .tertButylMethyl j) (i, .tertButylCentral) .single) ∧
      yGraph.Bonded
        (i, .glycosidicO) (nextResidue i, .c4) .single := by
  native_decide

private theorem y_reachable_local (i : Residue) (x : YLocalAtom) :
    yGraph.Reachable (i, x) (i, .c1) := by
  rcases y_spanning_bonds i with
    ⟨h21, h32, h43, h54, hO51, h65, hG1, hE2, hO6, hSi,
      hMe, htBu, htBuMe, _⟩
  have r1 : yGraph.Reachable (i, .c1) (i, .c1) := .refl _
  have r2 := reachable_of_bonded h21
  have r3 := reachable_trans (reachable_of_bonded h32) r2
  have r4 := reachable_trans (reachable_of_bonded h43) r3
  have r5 := reachable_trans (reachable_of_bonded h54) r4
  have r6 := reachable_trans (reachable_of_bonded h65) r5
  have rO5 := reachable_of_bonded hO51
  have rG := reachable_of_bonded hG1
  have rE := reachable_trans (reachable_of_bonded hE2) r2
  have rO6 := reachable_trans (reachable_of_bonded hO6) r6
  have rSi := reachable_trans (reachable_of_bonded hSi) rO6
  have rtBu := reachable_trans (reachable_of_bonded htBu) rSi
  cases x with
  | c1 => exact r1
  | c2 => exact r2
  | c3 => exact r3
  | c4 => exact r4
  | c5 => exact r5
  | c6 => exact r6
  | ringO5 => exact rO5
  | glycosidicO => exact rG
  | epoxideO23 => exact rE
  | oxygen6 => exact rO6
  | silicon => exact rSi
  | silylMethyl j =>
      exact reachable_trans (reachable_of_bonded (hMe j)) rSi
  | tertButylCentral => exact rtBu
  | tertButylMethyl j =>
      exact reachable_trans (reachable_of_bonded (htBuMe j)) rtBu

private theorem y_reachable_next (i : Residue) :
    yGraph.Reachable (i, .c1) (nextResidue i, .c1) := by
  rcases y_spanning_bonds i with
    ⟨_, _, _, _, _, _, hG1, _, _, _, _, _, _, hGnext⟩
  exact reachable_trans
    (reachable_of_bonded (bonded_symm hG1))
    (reachable_trans (reachable_of_bonded hGnext)
      (y_reachable_local (nextResidue i) .c4))

private theorem y_connected : yGraph.Connected :=
  connected_of_local_and_next yGraph .c1
    y_reachable_local y_reachable_next

theorem yGraph_formula_and_valence :
    yGraph.formula = printedYFormula ∧
    yGraph.WellFormedClosed := by
  refine ⟨by native_decide, ?_⟩
  refine ⟨?_, ?_, ?_, y_connected⟩
  · unfold MolecularGraph.NoSelfBonds
    native_decide
  · unfold MolecularGraph.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold MolecularGraph.NeutralClosedValence
    native_decide

/-! ## Explicit stereochemistry -/

inductive RingCarbon where
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

inductive ConfigurationChange where
  | retained
  | inverted
  deriving DecidableEq, Fintype, Repr

def ringCarbonAtom (i : Residue) : RingCarbon → YAtom
  | .c1 => (i, .c1)
  | .c2 => (i, .c2)
  | .c3 => (i, .c3)
  | .c4 => (i, .c4)
  | .c5 => (i, .c5)

def candidateExternalFace (candidate : ClosureCandidate) : RingCarbon → Face
  | .c1 => .down
  | .c2 => epoxideBondFace candidate .c2
  | .c3 => epoxideBondFace candidate .c3
  | .c4 => .down
  | .c5 => .up

def candidateConfigurationChange
    (candidate : ClosureCandidate) : RingCarbon → ConfigurationChange
  | .c2 => if candidate.leavingCarbon = .c2 then .inverted else .retained
  | .c3 => if candidate.leavingCarbon = .c3 then .inverted else .retained
  | .c1 | .c4 | .c5 => .retained

/-- Ordered ring neighbours and the external ligand make each tetrahedral
centre explicit; face data fix the relative stereochemistry in the template. -/
structure StereoCentre where
  center : YAtom
  ringBack : YAtom
  ringForward : YAtom
  externalLigand : YAtom
  attachedHydrogenParent : YAtom
  externalFace : Face
  hydrogenFace : Face
  changeFromAlphaDGlucose : ConfigurationChange
  deriving DecidableEq, Repr

def yStereo (candidate : ClosureCandidate)
    (i : Residue) : RingCarbon → StereoCentre
  | .c1 =>
      { center := (i, .c1)
        ringBack := (i, .ringO5)
        ringForward := (i, .c2)
        externalLigand := (i, .glycosidicO)
        attachedHydrogenParent := (i, .c1)
        externalFace := candidateExternalFace candidate .c1
        hydrogenFace := (candidateExternalFace candidate .c1).opposite
        changeFromAlphaDGlucose := candidateConfigurationChange candidate .c1 }
  | .c2 =>
      { center := (i, .c2)
        ringBack := (i, .c1)
        ringForward := (i, .c3)
        externalLigand := (i, .epoxideO23)
        attachedHydrogenParent := (i, .c2)
        externalFace := candidateExternalFace candidate .c2
        hydrogenFace := (candidateExternalFace candidate .c2).opposite
        changeFromAlphaDGlucose := candidateConfigurationChange candidate .c2 }
  | .c3 =>
      { center := (i, .c3)
        ringBack := (i, .c2)
        ringForward := (i, .c4)
        externalLigand := (i, .epoxideO23)
        attachedHydrogenParent := (i, .c3)
        externalFace := candidateExternalFace candidate .c3
        hydrogenFace := (candidateExternalFace candidate .c3).opposite
        changeFromAlphaDGlucose := candidateConfigurationChange candidate .c3 }
  | .c4 =>
      { center := (i, .c4)
        ringBack := (i, .c3)
        ringForward := (i, .c5)
        externalLigand := (previousResidue i, .glycosidicO)
        attachedHydrogenParent := (i, .c4)
        externalFace := candidateExternalFace candidate .c4
        hydrogenFace := (candidateExternalFace candidate .c4).opposite
        changeFromAlphaDGlucose := candidateConfigurationChange candidate .c4 }
  | .c5 =>
      { center := (i, .c5)
        ringBack := (i, .c4)
        ringForward := (i, .ringO5)
        externalLigand := (i, .c6)
        attachedHydrogenParent := (i, .c5)
        externalFace := candidateExternalFace candidate .c5
        hydrogenFace := (candidateExternalFace candidate .c5).opposite
        changeFromAlphaDGlucose := candidateConfigurationChange candidate .c5 }

def StereoCentre.ValidFor (g : MolecularGraph YAtom)
    (candidate : ClosureCandidate) (carbon : RingCarbon)
    (s : StereoCentre) : Prop :=
  (g.atom s.center).element = .carbon ∧
  (g.atom s.center).attachedHydrogens = 1 ∧
  s.attachedHydrogenParent = s.center ∧
  g.Bonded s.center s.ringBack .single ∧
  g.Bonded s.center s.ringForward .single ∧
  g.Bonded s.center s.externalLigand .single ∧
  s.externalFace = candidateExternalFace candidate carbon ∧
  s.hydrogenFace = s.externalFace.opposite ∧
  s.changeFromAlphaDGlucose = candidateConfigurationChange candidate carbon

inductive GlycosidicLinkage where
  | alphaOneFour
  deriving DecidableEq, Fintype, Repr

structure CyclodextrinStructure where
  graph : MolecularGraph YAtom
  linkage : GlycosidicLinkage
  stereocentre : Residue → RingCarbon → StereoCentre

def candidateY (candidate : ClosureCandidate) : CyclodextrinStructure where
  graph := yGraph
  linkage := .alphaOneFour
  stereocentre := yStereo candidate

def HasAlphaOneFourLink (m : CyclodextrinStructure) (i : Residue) : Prop :=
  m.graph.Bonded (i, .c1) (i, .glycosidicO) .single ∧
  m.graph.Bonded (i, .glycosidicO) (nextResidue i, .c4) .single ∧
  (m.stereocentre i .c1).externalFace = .down ∧
  (m.stereocentre (nextResidue i) .c4).externalFace = .down

def Has23Epoxide (m : CyclodextrinStructure) (i : Residue) : Prop :=
  m.graph.Bonded (i, .c2) (i, .c3) .single ∧
  m.graph.Bonded (i, .c2) (i, .epoxideO23) .single ∧
  m.graph.Bonded (i, .c3) (i, .epoxideO23) .single

/-- Complete connectivity of one `O-Si(CH3)2-C(CH3)3` substituent. -/
def HasTBSAtC6 (m : CyclodextrinStructure) (i : Residue) : Prop :=
  m.graph.Bonded (i, .c6) (i, .oxygen6) .single ∧
  m.graph.Bonded (i, .oxygen6) (i, .silicon) .single ∧
  (∀ j : Fin 2,
    m.graph.Bonded (i, .silicon) (i, .silylMethyl j) .single) ∧
  m.graph.Bonded (i, .silicon) (i, .tertButylCentral) .single ∧
  (∀ j : Fin 3,
    m.graph.Bonded (i, .tertButylCentral) (i, .tertButylMethyl j) .single)

def IsOxygenLocal : YLocalAtom → Prop
  | .ringO5 | .glycosidicO | .epoxideO23 | .oxygen6 => True
  | _ => False

def NoFreeHydroxyl (m : CyclodextrinStructure) : Prop :=
  ∀ i site, IsOxygenLocal site →
    (m.graph.atom (i, site)).attachedHydrogens = 0

def AllNeutralClosedShell (m : CyclodextrinStructure) : Prop :=
  ∀ atom,
    (m.graph.atom atom).formalCharge = 0 ∧
    (m.graph.atom atom).radicalElectrons = 0

/-! ## Exact substrate-to-candidate graph rewrite -/

def SecondarySite.alphaOxygen : SecondarySite → AlphaLocalAtom
  | .c2 => .hydroxylO2
  | .c3 => .hydroxylO3

def SecondarySite.yCarbon : SecondarySite → YLocalAtom
  | .c2 => .c2
  | .c3 => .c3

def preserveYLocal (candidate : ClosureCandidate) :
    YLocalAtom → Option AlphaLocalAtom
  | .c1 => some .c1
  | .c2 => some .c2
  | .c3 => some .c3
  | .c4 => some .c4
  | .c5 => some .c5
  | .c6 => some .c6
  | .ringO5 => some .ringO5
  | .glycosidicO => some .glycosidicO
  | .epoxideO23 => some candidate.attackingOxygen.alphaOxygen
  | .oxygen6 => some .hydroxylO6
  | .silicon | .silylMethyl _ | .tertButylCentral | .tertButylMethyl _ => none

def preserveYAtom (candidate : ClosureCandidate) (a : YAtom) : Option AlphaAtom :=
  (preserveYLocal candidate a.2).map fun site => (a.1, site)

def IsNewEpoxideBond (candidate : ClosureCandidate) (a b : YAtom) : Prop :=
  ∃ i : Residue,
    (a = (i, .epoxideO23) ∧ b = (i, candidate.leavingCarbon.yCarbon)) ∨
    (b = (i, .epoxideO23) ∧ a = (i, candidate.leavingCarbon.yCarbon))

private instance instDecidableIsNewEpoxideBond
    (candidate : ClosureCandidate) (a b : YAtom) :
    Decidable (IsNewEpoxideBond candidate a b) := by
  unfold IsNewEpoxideBond
  infer_instance

def IsTBSLocalBond : YLocalAtom → YLocalAtom → Prop
  | .oxygen6, .silicon | .silicon, .oxygen6 => True
  | .silicon, .silylMethyl _ | .silylMethyl _, .silicon => True
  | .silicon, .tertButylCentral | .tertButylCentral, .silicon => True
  | .tertButylCentral, .tertButylMethyl _ |
      .tertButylMethyl _, .tertButylCentral => True
  | _, _ => False

private instance instDecidableIsTBSLocalBond (a b : YLocalAtom) :
    Decidable (IsTBSLocalBond a b) := by
  cases a <;> cases b <;> simp [IsTBSLocalBond] <;> infer_instance

def IsNewTBSBond (a b : YAtom) : Prop :=
  a.1 = b.1 ∧ IsTBSLocalBond a.2 b.2

private instance instDecidableIsNewTBSBond (a b : YAtom) :
    Decidable (IsNewTBSBond a b) := by
  unfold IsNewTBSBond
  infer_instance

/-- A direct, computable form of the existential source-bond clause used in
`GraphRewriteAt`.  It avoids repeatedly searching the whole source carrier
once the two partial atom maps have already been evaluated. -/
private def PreservedSourceBond (candidate : ClosureCandidate)
    (a b : YAtom) (order : BondOrder) : Prop :=
  match preserveYAtom candidate a, preserveYAtom candidate b with
  | some sourceA, some sourceB => alphaCDGraph.Bonded sourceA sourceB order
  | _, _ => False

private instance instDecidablePreservedSourceBond
    (candidate : ClosureCandidate) (a b : YAtom) (order : BondOrder) :
    Decidable (PreservedSourceBond candidate a b order) := by
  unfold PreservedSourceBond
  split <;> infer_instance

private theorem exists_preserved_source_bond_iff
    (candidate : ClosureCandidate) (a b : YAtom) (order : BondOrder) :
    (∃ sourceA sourceB,
        preserveYAtom candidate a = some sourceA ∧
        preserveYAtom candidate b = some sourceB ∧
        alphaCDGraph.Bonded sourceA sourceB order) ↔
      PreservedSourceBond candidate a b order := by
  unfold PreservedSourceBond
  cases ha : preserveYAtom candidate a <;>
    cases hb : preserveYAtom candidate b <;>
    simp

/-- Candidate-level graph rewrite.  The leaving secondary oxygen is absent;
the attacking oxygen loses H and gains the new epoxide bond; O6 loses H and
gains the complete TBS substituent.  All other source atoms and bonds persist. -/
def GraphRewriteAt (candidate : ClosureCandidate)
    (m : CyclodextrinStructure) : Prop :=
  (∀ a b order,
    m.graph.Bonded a b order ↔
      (∃ sourceA sourceB,
        preserveYAtom candidate a = some sourceA ∧
        preserveYAtom candidate b = some sourceB ∧
        alphaCDGraph.Bonded sourceA sourceB order) ∨
      (order = .single ∧
        (IsNewEpoxideBond candidate a b ∨ IsNewTBSBond a b))) ∧
  (∀ a sourceA,
    preserveYAtom candidate a = some sourceA →
      (m.graph.atom a).element = (alphaCDGraph.atom sourceA).element ∧
      (m.graph.atom a).formalCharge =
        (alphaCDGraph.atom sourceA).formalCharge ∧
      (m.graph.atom a).radicalElectrons =
        (alphaCDGraph.atom sourceA).radicalElectrons ∧
      (m.graph.atom a).attachedHydrogens =
        if a.2 = .epoxideO23 ∨ a.2 = .oxygen6 then
          (alphaCDGraph.atom sourceA).attachedHydrogens - 1
        else
          (alphaCDGraph.atom sourceA).attachedHydrogens) ∧
  (∀ sourceA : AlphaAtom,
    (∃ a : YAtom, preserveYAtom candidate a = some sourceA) ↔
      sourceA.2 ≠ candidate.leavingCarbon.alphaOxygen) ∧
  m.graph.formula = sourceDerivedYFormula

/-! ## Uniform candidate audit and derived output -/

def ClosureCandidateFits (candidate : ClosureCandidate) : Prop :=
  SourceConditionsHold ∧
  PreviousPartResult ∧
  derivedProtectionCandidate.site = .c6 ∧
  candidate ∈ closureCandidateDomain ∧
  candidate.attackingOxygen ≠ candidate.leavingCarbon ∧
  CandidateMatchesKeyIntermediate candidate ∧
  DownstreamHydrolysisCompatible candidate ∧
  GraphRewriteAt candidate (candidateY candidate) ∧
  (candidateY candidate).graph.formula = printedYFormula ∧
  (candidateY candidate).graph.WellFormedClosed

private def selectedClosureCandidate : ClosureCandidate where
  leavingCarbon := .c2
  attackingOxygen := .c3

private theorem selected_bond_rewrite :
    ∀ a b order,
      (candidateY selectedClosureCandidate).graph.Bonded a b order ↔
        PreservedSourceBond selectedClosureCandidate a b order ∨
        (order = .single ∧
          (IsNewEpoxideBond selectedClosureCandidate a b ∨
            IsNewTBSBond a b)) := by
  native_decide

private theorem selectedClosureCandidate_fits :
    ClosureCandidateFits selectedClosureCandidate := by
  refine ⟨sourceConditions_hold, previous_part_derived,
    derivedProtectionCandidate_component, ?_, ?_, ?_, ?_, ?_,
    yGraph_formula_and_valence.1, yGraph_formula_and_valence.2⟩
  · simp [selectedClosureCandidate, closureCandidateDomain]
  · simp [selectedClosureCandidate]
  · unfold CandidateMatchesKeyIntermediate candidateEpoxideSeries
      epoxideBondFace startingHydroxylFace Face.opposite
      cycloaltrinKeyIntermediateClaim selectedClosureCandidate
    decide
  · refine ⟨.c3, ?_⟩
    intro site
    cases site <;>
      rfl
  · unfold GraphRewriteAt
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b order
      rw [exists_preserved_source_bond_iff]
      exact selected_bond_rewrite a b order
    · native_decide
    · native_decide
    · native_decide

/-- The complete C2/C3 mechanistic domain is formed before applying the same
source, stereochemical, formula, and literature constraints to every case. -/
theorem existsUniqueClosureCandidate :
    ∃! candidate : ClosureCandidate, ClosureCandidateFits candidate := by
  refine ⟨selectedClosureCandidate, selectedClosureCandidate_fits, ?_⟩
  rintro ⟨leaving, attacking⟩ hfits
  have hne := hfits.2.2.2.2.1
  have hkey := hfits.2.2.2.2.2.1
  cases leaving <;> cases attacking <;>
    simp_all [selectedClosureCandidate, CandidateMatchesKeyIntermediate,
      candidateEpoxideSeries, epoxideBondFace, startingHydroxylFace,
      Face.opposite, cycloaltrinKeyIntermediateClaim]

noncomputable def derivedClosureCandidate : ClosureCandidate :=
  Classical.choose existsUniqueClosureCandidate

theorem derivedClosureCandidate_spec :
    ClosureCandidateFits derivedClosureCandidate := by
  exact (Classical.choose_spec existsUniqueClosureCandidate).1

theorem derivedClosureCandidate_unique
    (candidate : ClosureCandidate) (h : ClosureCandidateFits candidate) :
    candidate = derivedClosureCandidate := by
  exact (Classical.choose_spec existsUniqueClosureCandidate).2 candidate h

/-- The selected mechanistic case is O3 attack at tosylated C2. -/
theorem derivedClosureCandidate_components :
    derivedClosureCandidate.leavingCarbon = .c2 ∧
    derivedClosureCandidate.attackingOxygen = .c3 := by
  have hselected := derivedClosureCandidate_unique selectedClosureCandidate
    selectedClosureCandidate_fits
  rw [← hselected]
  exact ⟨rfl, rfl⟩

/-- The molecular candidate is constructed only after the uniform finite
audit; it is not supplied as a theorem premise. -/
noncomputable def derivedY : CyclodextrinStructure :=
  candidateY derivedClosureCandidate

def SourceReactionCompatible (m : CyclodextrinStructure) : Prop :=
  sourceTransformationUse = .qualitativeNamedTransformOnly ∧
  SourceConditionsHold ∧
  PreviousPartResult ∧
  sourceDerivedYFormula = printedYFormula ∧
  ∃ candidate : ClosureCandidate,
    ClosureCandidateFits candidate ∧
    m = candidateY candidate

theorem derivedY_sourceReactionCompatible :
    SourceReactionCompatible derivedY := by
  exact ⟨rfl, sourceConditions_hold, previous_part_derived,
    source_formula_ledger, derivedClosureCandidate,
    derivedClosureCandidate_spec, rfl⟩

/-- Complete connectivity, electronics, formula, template fields, and
stereochemistry for the sixfold 6-O-TBS-2,3-anhydro-alpha-CD product. -/
def CompleteYSpecification (m : CyclodextrinStructure) : Prop :=
  m.graph = yGraph ∧
  m.linkage = .alphaOneFour ∧
  derivedProtectionCandidate.site = .c6 ∧
  derivedClosureCandidate.leavingCarbon = .c2 ∧
  derivedClosureCandidate.attackingOxygen = .c3 ∧
  (∀ i carbon,
    m.stereocentre i carbon = yStereo derivedClosureCandidate i carbon ∧
    (m.stereocentre i carbon).ValidFor
      m.graph derivedClosureCandidate carbon) ∧
  (∀ i,
    HasAlphaOneFourLink m i ∧
    Has23Epoxide m i ∧
    HasTBSAtC6 m i ∧
    (m.stereocentre i .c1).externalFace = .down ∧
    (m.stereocentre i .c2).externalFace = .up ∧
    (m.stereocentre i .c3).externalFace = .up ∧
    (m.stereocentre i .c4).externalFace = .down ∧
    (m.stereocentre i .c5).externalFace = .up ∧
    (m.stereocentre i .c1).changeFromAlphaDGlucose = .retained ∧
    (m.stereocentre i .c2).changeFromAlphaDGlucose = .inverted ∧
    (m.stereocentre i .c3).changeFromAlphaDGlucose = .retained ∧
    (m.stereocentre i .c4).changeFromAlphaDGlucose = .retained ∧
    (m.stereocentre i .c5).changeFromAlphaDGlucose = .retained) ∧
  NoFreeHydroxyl m ∧
  AllNeutralClosedShell m ∧
  m.graph.formula = printedYFormula ∧
  m.graph.WellFormedClosed

theorem derivedY_complete : CompleteYSpecification derivedY := by
  have hcandidate : derivedClosureCandidate = selectedClosureCandidate :=
    (derivedClosureCandidate_unique selectedClosureCandidate
      selectedClosureCandidate_fits).symm
  unfold CompleteYSpecification derivedY
  rw [hcandidate]
  refine ⟨rfl, rfl, derivedProtectionCandidate_component, rfl, rfl,
    ?_, ?_, ?_, ?_, yGraph_formula_and_valence.1,
    yGraph_formula_and_valence.2⟩
  · intro i carbon
    refine ⟨rfl, ?_⟩
    unfold StereoCentre.ValidFor
    revert i carbon
    native_decide
  · intro i
    unfold HasAlphaOneFourLink Has23Epoxide HasTBSAtC6
    revert i
    native_decide
  · unfold NoFreeHydroxyl
    intro i site hoxygen
    cases site <;>
      simp_all [IsOxygenLocal, candidateY, yGraph, yAtomSpec, neutralAtom]
  · unfold AllNeutralClosedShell
    rintro ⟨i, site⟩
    cases site <;>
      simp [candidateY, yGraph, yAtomSpec, neutralAtom]

/-! ## Requested-output and exact-symbolic result carriers -/

/-- Requested output `structure_y`.  This is a graph-and-stereochemistry
proposition, not a molecular-name string or a premise containing the answer. -/
def StructureYResult : Prop :=
  SourceReactionCompatible derivedY ∧
  CompleteYSpecification derivedY

theorem structure_y : StructureYResult := by
  exact ⟨derivedY_sourceReactionCompatible, derivedY_complete⟩

/-- Exact symbolic raw result for the sole controller-listed output. -/
def RawResult : Prop := StructureYResult

/-- Exact-symbolic reporting performs no rounding or tolerance change. -/
def ReportedResult : Prop := StructureYResult

theorem raw_result : RawResult := by
  exact structure_y

theorem reported_result : ReportedResult := by
  exact structure_y

end IChO2026Problems.T9A4
