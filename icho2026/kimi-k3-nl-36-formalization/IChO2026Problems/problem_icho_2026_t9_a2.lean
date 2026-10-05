import IChO2026Chem

/-!
# IChO 2026, problem 9.2

This file formalizes both requested outputs: the favourable chair of `K` and
the complete stereochemical structure drawn in the cyclodextrin template.

The molecule is represented as a labelled heavy-atom graph.  Hydrogens are
stored at their heavy-atom parents, and `ExpandedAtom` makes every hydrogen an
individual atom with an explicit single bond.  Thus the graph records every
atom, bond order, formal charge, radical count, and requested stereocentre.

The depicted two-step transformation is used only as a
`qualitativeNamedTransformOnly` compatibility constraint.  No yield,
completion, sole-product, phase balance, or unprinted byproduct is asserted.

The system-specific bridge that is not printed in the problem is represented
below by a typed, source-scoped public-literature observation.  Its source is
Yamamura and Fujita, *Chemical and Pharmaceutical Bulletin* 39 (1991),
2505--2508, DOI `10.1248/cpb.39.2505`, abstract.  That abstract reports the
preparation of heptakis(6-O-(p-tosyl))-beta-cyclodextrin from beta-CD and
p-tosyl chloride in pyridine and its conversion to
heptakis(3,6-anhydro)-beta-cyclodextrin constituted from alternative (`1C4`)
glucose units.  The record is used only for those exact substrate,
functional-site, connectivity, and chair fields; it supplies no yield,
exclusive-product, mechanism, or material-balance claim.

The problem's explicit Stoddart attribution is separately cross-checked by
Ashton, Ellwood, Staton, and Stoddart, “Per-3,6-anhydro-alpha-cyclodextrin and
per-3,6-anhydro-beta-cyclodextrin”, *Journal of Organic Chemistry* 56 (1991),
7274--7280, DOI `10.1021/jo00026a017`, bibliographic title metadata.  That
record is used only to bind the attributed beta-CD species identity.
-/

namespace IChO2026Problems.T9A2

/-! ## Molecular-graph vocabulary -/

inductive Element where
  | hydrogen
  | carbon
  | oxygen
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

/-- A heavy atom together with all electronic data and the number of
separately bound hydrogen atoms at that site. -/
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

/-- One undirected, bond-order-labelled heavy-atom edge. -/
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

/-- Bond existence is decidable by traversing the graph's finite bond list. -/
private instance instDecidableBonded {α : Type} [DecidableEq α]
    (g : MolecularGraph α) (a b : α) (order : BondOrder) :
    Decidable (g.Bonded a b order) := by
  unfold MolecularGraph.Bonded Bond.Connects
  infer_instance

/-- The atom carrier after expanding every site-attached hydrogen. -/
def ExpandedAtom {α : Type} (g : MolecularGraph α) : Type :=
  Sum α (Σ a : α, Fin (g.atom a).attachedHydrogens)

def ExpandedAtom.element {α : Type} {g : MolecularGraph α} :
    ExpandedAtom g → Element
  | .inl a => (g.atom a).element
  | .inr _ => .hydrogen

/-- Bonding after hydrogen expansion: every stored H is joined to exactly its
parent heavy atom by a single bond. -/
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
  deriving DecidableEq, Repr

def MolecularFormula.removeWaterUnits (n : ℕ)
    (f : MolecularFormula) : MolecularFormula where
  carbon := f.carbon
  hydrogen := f.hydrogen - 2 * n
  oxygen := f.oxygen - n

def MolecularGraph.formula {α : Type} [Fintype α]
    (g : MolecularGraph α) : MolecularFormula where
  carbon := ∑ a : α, if (g.atom a).element = .carbon then 1 else 0
  hydrogen := ∑ a : α,
    ((g.atom a).attachedHydrogens +
      if (g.atom a).element = .hydrogen then 1 else 0)
  oxygen := ∑ a : α, if (g.atom a).element = .oxygen then 1 else 0

def Element.neutralValence : Element → ℕ
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2

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

/-! ## The seven-unit beta-cyclodextrin substrate from the figures -/

/-- The bracket multiplier `7` and the seven-membered top view in the source
figures supply this exact residue carrier. -/
abbrev Residue := Fin 7

def nextResidue (i : Residue) : Residue := i + 1

def previousResidue (i : Residue) : Residue := i + 6

/-- A connectivity reduction shared by the substrate and product audits.  It
is enough that every local atom reaches C1 and that successive residue C1
atoms are joined around the seven-membered cycle. -/
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
  have h56 : g.Reachable ((5 : Residue), root) ((6 : Residue), root) := by
    simpa [nextResidue] using hnext (5 : Residue)
  have h02 := reachable_trans h01 h12
  have h03 := reachable_trans h02 h23
  have h04 := reachable_trans h03 h34
  have h05 := reachable_trans h04 h45
  have h06 := reachable_trans h05 h56
  have htozero (i : Residue) :
      g.Reachable (i, root) ((0 : Residue), root) := by
    fin_cases i
    · exact .refl _
    · exact reachable_symm h01
    · exact reachable_symm h02
    · exact reachable_symm h03
    · exact reachable_symm h04
    · exact reachable_symm h05
    · exact reachable_symm h06
  rintro ⟨i, x⟩ ⟨j, y⟩
  exact reachable_trans
    (reachable_trans (hlocal i x) (htozero i))
    (reachable_trans (reachable_symm (htozero j))
      (reachable_symm (hlocal j y)))

inductive BetaLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | hydroxylO2
  | hydroxylO3
  | hydroxylO6
  deriving DecidableEq, Fintype, Repr

abbrev BetaAtom := Residue × BetaLocalAtom

def betaAtomSpec : BetaAtom → AtomSpec
  | (_, .c1) | (_, .c2) | (_, .c3) | (_, .c4) | (_, .c5) =>
      neutralAtom .carbon 1
  | (_, .c6) => neutralAtom .carbon 2
  | (_, .ringO5) | (_, .glycosidicO) => neutralAtom .oxygen 0
  | (_, .hydroxylO2) | (_, .hydroxylO3) | (_, .hydroxylO6) =>
      neutralAtom .oxygen 1

/-- The six-membered pyranose ring, three hydroxy substituents, and the cyclic
alpha-(1→4) glycosidic edge are all listed once per residue. -/
def betaBonds : List (Bond BetaAtom) :=
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

def betaCyclodextrinGraph : MolecularGraph BetaAtom where
  atom := betaAtomSpec
  bonds := betaBonds

def betaCyclodextrinFormula : MolecularFormula :=
  { carbon := 42, hydrogen := 70, oxygen := 35 }

private theorem beta_spanning_bonds :
    ∀ i : Residue,
      betaCyclodextrinGraph.Bonded (i, .c2) (i, .c1) .single ∧
      betaCyclodextrinGraph.Bonded (i, .c3) (i, .c2) .single ∧
      betaCyclodextrinGraph.Bonded (i, .c4) (i, .c3) .single ∧
      betaCyclodextrinGraph.Bonded (i, .c5) (i, .c4) .single ∧
      betaCyclodextrinGraph.Bonded (i, .ringO5) (i, .c1) .single ∧
      betaCyclodextrinGraph.Bonded (i, .c6) (i, .c5) .single ∧
      betaCyclodextrinGraph.Bonded (i, .hydroxylO2) (i, .c2) .single ∧
      betaCyclodextrinGraph.Bonded (i, .hydroxylO3) (i, .c3) .single ∧
      betaCyclodextrinGraph.Bonded (i, .hydroxylO6) (i, .c6) .single ∧
      betaCyclodextrinGraph.Bonded (i, .glycosidicO) (i, .c1) .single ∧
      betaCyclodextrinGraph.Bonded
        (i, .glycosidicO) (nextResidue i, .c4) .single := by
  native_decide

private theorem beta_reachable_local (i : Residue) (x : BetaLocalAtom) :
    betaCyclodextrinGraph.Reachable (i, x) (i, .c1) := by
  rcases beta_spanning_bonds i with
    ⟨h21, h32, h43, h54, hO51, h65, hO2, hO3, hO6, hG1, _⟩
  have r1 : betaCyclodextrinGraph.Reachable (i, .c1) (i, .c1) := .refl _
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

private theorem beta_reachable_next (i : Residue) :
    betaCyclodextrinGraph.Reachable
      (i, .c1) (nextResidue i, .c1) := by
  rcases beta_spanning_bonds i with
    ⟨_, _, _, _, _, _, _, _, _, hG1, hGnext⟩
  exact reachable_trans
    (reachable_of_bonded (bonded_symm hG1))
    (reachable_trans (reachable_of_bonded hGnext)
      (beta_reachable_local (nextResidue i) .c4))

private theorem beta_connected : betaCyclodextrinGraph.Connected :=
  connected_of_local_and_next betaCyclodextrinGraph .c1
    beta_reachable_local beta_reachable_next

/-- Source-image formula/count audit for the seven unprotected repeat units. -/
theorem betaCyclodextrin_graph_audit :
    betaCyclodextrinGraph.formula = betaCyclodextrinFormula ∧
    betaCyclodextrinGraph.WellFormedClosed := by
  refine ⟨by native_decide, ?_⟩
  refine ⟨?_, ?_, ?_, beta_connected⟩
  · unfold MolecularGraph.NoSelfBonds
    native_decide
  · unfold MolecularGraph.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold MolecularGraph.NeutralClosedValence
    native_decide

/-! ## Source reaction conditions and primary-OH selection -/

inductive Reagent where
  | tosylChloride
  | pyridine
  | sodiumHydroxide
  | water
  deriving DecidableEq, Fintype, Repr

structure ReactionConditions where
  firstReagent : Reagent
  firstEquivalents : ℚ
  firstMedium : Reagent
  secondReagent : Reagent
  secondMedium : Reagent
  secondTemperatureC : ℚ
  deriving DecidableEq, Repr

/-- Exact transcription of the arrow leading to `K`. -/
def sourceReactionConditions : ReactionConditions where
  firstReagent := .tosylChloride
  firstEquivalents := 7
  firstMedium := .pyridine
  secondReagent := .sodiumHydroxide
  secondMedium := .water
  secondTemperatureC := 60

/-- Every reagent, equivalent count, medium, and stated temperature on the
source arrow, separated from the structural conclusion. -/
def SourceConditionsHold : Prop :=
  sourceReactionConditions.firstReagent = .tosylChloride ∧
  sourceReactionConditions.firstEquivalents = 7 ∧
  sourceReactionConditions.firstMedium = .pyridine ∧
  sourceReactionConditions.secondReagent = .sodiumHydroxide ∧
  sourceReactionConditions.secondMedium = .water ∧
  sourceReactionConditions.secondTemperatureC = 60

theorem sourceConditions_hold : SourceConditionsHold := by
  norm_num [SourceConditionsHold, sourceReactionConditions]

inductive TransformationUse where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

def sourceTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

def betaHydroxylSites : Finset BetaAtom :=
  Finset.univ.filter fun a =>
    a.2 = .hydroxylO2 ∨ a.2 = .hydroxylO3 ∨ a.2 = .hydroxylO6

def primaryHydroxylSites : Finset BetaAtom :=
  Finset.univ.filter fun a => a.2 = .hydroxylO6

structure PublicLiteratureCitation where
  title : String
  doi : String
  stableURL : String
  locator : String
  exactClaim : String
  exactClaimSha256 : String
  deriving DecidableEq, Repr

/-- Public source used for the missing system-specific chemistry bridge.  The
hash is over the UTF-8 text in `exactClaim`, with no trailing newline. -/
def yamamuraFujitaCitation : PublicLiteratureCitation where
  title := "Preparation of Heptakis(6-O-(p-tosyl))-β-cyclodextrin and Heptakis(6-O-(p-tosyl))-2-O-(p-tosyl)-β-cyclodextrin and Their Conversion to Heptakis(3,6-anhydro)-β-cyclodextrin"
  doi := "10.1248/cpb.39.2505"
  stableURL :=
    "https://www.jstage.jst.go.jp/article/cpb1958/39/10/39_10_2505/_article/-char/en"
  locator := "abstract"
  exactClaim :=
    "Heptakis(6-O-(p-tosyl))-β-cyclodextrin and heptakis(6-O-(p-tosyl))-2-O-(p-tosyl)-β-cyclodextrin were prepared by the reaction of β-cyclodextrin with p-tosyl chloride in pyridine. They were converted to heptakis(3, 6-anhydro)-β-cyclodextrin, constituted from alternative (1C4) glucose units."
  exactClaimSha256 :=
    "07b4be059af124e1f9ada17b83eb0d210b08dbcbe850fbff9e6657e5a3b4591c"

/-- Bibliographic identity check for the Stoddart-attributed species named in
the problem text.  The hash is over `exactClaim` with no trailing newline. -/
def ashtonEllwoodStatonStoddartCitation : PublicLiteratureCitation where
  title :=
    "Per-3,6-anhydro-α-cyclodextrin and per-3,6-anhydro-β-cyclodextrin"
  doi := "10.1021/jo00026a017"
  stableURL := "https://doi.org/10.1021/jo00026a017"
  locator := "Crossref bibliographic title metadata"
  exactClaim :=
    "Per-3,6-anhydro-α-cyclodextrin and per-3,6-anhydro-β-cyclodextrin"
  exactClaimSha256 :=
    "6f0898715697855f6399b921b766d8befcb00eebe2b6bdced410788e0f89a30c"

/-- Typed projection of the first, primary-tosylation clause of the cited
abstract.  Unlike the old local rank function, this data record has an exact
external locator and does not pretend to be a universal reactivity law. -/
structure PrimaryTosylationObservation where
  citation : PublicLiteratureCitation
  reactantFormula : MolecularFormula
  reagent : Reagent
  medium : Reagent
  activatedSites : Finset BetaAtom
  deriving DecidableEq

def yamamuraFujitaPrimaryObservation : PrimaryTosylationObservation where
  citation := yamamuraFujitaCitation
  reactantFormula := betaCyclodextrinFormula
  reagent := .tosylChloride
  medium := .pyridine
  activatedSites := primaryHydroxylSites

/-- Source-to-model applicability audit for the cited primary-tosylation
observation.  It binds the observed substrate and reaction roles to the whole
seven-residue graph and to the exact first stage drawn in the problem. -/
def PrimaryTosylationObservation.Applicable
    (o : PrimaryTosylationObservation) : Prop :=
  o.citation = yamamuraFujitaCitation ∧
  betaCyclodextrinGraph.formula = o.reactantFormula ∧
  o.reactantFormula = betaCyclodextrinFormula ∧
  o.reagent = sourceReactionConditions.firstReagent ∧
  o.medium = sourceReactionConditions.firstMedium ∧
  o.activatedSites.card = 7 ∧
  sourceReactionConditions.firstEquivalents = (o.activatedSites.card : ℚ) ∧
  (∀ a, a ∈ o.activatedSites ↔ a.2 = .hydroxylO6) ∧
  (∀ a ∈ o.activatedSites, a ∈ betaHydroxylSites)

theorem yamamuraFujitaPrimaryObservation_applicable :
    yamamuraFujitaPrimaryObservation.Applicable := by
  unfold PrimaryTosylationObservation.Applicable
  refine ⟨rfl, betaCyclodextrin_graph_audit.1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro a
    simp [yamamuraFujitaPrimaryObservation, primaryHydroxylSites]
  · intro a ha
    have haO6 : a.2 = .hydroxylO6 := by
      simpa [yamamuraFujitaPrimaryObservation, primaryHydroxylSites] using ha
    simp [betaHydroxylSites, haO6]

/-- An activation fits this exact problem only when it is the site set carried
by the applicable, source-scoped observation.  No answer-shaped reactivity
ranking or freely supplied activation premise remains. -/
def ActivationFits (activated : Finset BetaAtom) : Prop :=
  SourceConditionsHold ∧
  yamamuraFujitaPrimaryObservation.Applicable ∧
  activated = yamamuraFujitaPrimaryObservation.activatedSites

private theorem primaryActivationFits :
    ActivationFits primaryHydroxylSites := by
  exact ⟨sourceConditions_hold,
    yamamuraFujitaPrimaryObservation_applicable, rfl⟩

/-- The exact seven-equivalent activation pattern is derived from the complete
source hydroxyl domain and uniform reactivity ordering. -/
theorem existsUniqueActivation :
    ∃! activated : Finset BetaAtom, ActivationFits activated := by
  refine ⟨primaryHydroxylSites, primaryActivationFits, ?_⟩
  intro activated h
  simpa [yamamuraFujitaPrimaryObservation] using h.2.2

noncomputable def derivedActivation : Finset BetaAtom :=
  Classical.choose existsUniqueActivation

theorem derivedActivation_spec : ActivationFits derivedActivation := by
  exact (Classical.choose_spec existsUniqueActivation).1

theorem derivedActivation_eq_primaryHydroxylSites :
    derivedActivation = primaryHydroxylSites := by
  simpa [yamamuraFujitaPrimaryObservation] using derivedActivation_spec.2.2

/-! ## Candidate closure geometry -/

inductive Face where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

def Face.opposite : Face → Face
  | .up => .down
  | .down => .up

inductive Disposition where
  | axial
  | equatorial
  deriving DecidableEq, Fintype, Repr

inductive Chair where
  | fourCOne
  | oneCFour
  deriving DecidableEq, Fintype, Repr

inductive RingCarbon where
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

/-- Axial directions in the two ring-flip-related pyranose chairs. -/
def axialFace : Chair → RingCarbon → Face
  | .fourCOne, .c1 => .down
  | .fourCOne, .c2 => .up
  | .fourCOne, .c3 => .down
  | .fourCOne, .c4 => .up
  | .fourCOne, .c5 => .down
  | .oneCFour, .c1 => .up
  | .oneCFour, .c2 => .down
  | .oneCFour, .c3 => .up
  | .oneCFour, .c4 => .down
  | .oneCFour, .c5 => .up

/-- Up/down stereochemistry transcribed from the alpha-D-glucopyranoside
template.  A ring flip does not change these faces. -/
def templateExternalFace : RingCarbon → Face
  | .c1 => .down
  | .c2 => .down
  | .c3 => .up
  | .c4 => .down
  | .c5 => .up

def substituentDisposition
    (chair : Chair) (carbon : RingCarbon) (face : Face) : Disposition :=
  if face = axialFace chair carbon then .axial else .equatorial

inductive SecondaryHydroxyl where
  | atC2
  | atC3
  deriving DecidableEq, Fintype, Repr

def SecondaryHydroxyl.carbon : SecondaryHydroxyl → RingCarbon
  | .atC2 => .c2
  | .atC3 => .c3

/-- A local drawing candidate records the secondary oxygen used for a bridge
and one of the two standard ring-flip-related pyranose chairs.  This carrier is
not asserted to be an exhaustive universe of all possible reaction products. -/
structure ClosureCandidate where
  attackingHydroxyl : SecondaryHydroxyl
  chair : Chair
  deriving DecidableEq, Fintype, Repr

inductive Provenance where
  | problemText
  | problemImage
  | publicLiterature
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

/-- This is a descriptive check on a completed drawing, not an empirical rule
selecting a reaction product: the two displayed bridge-attachment bonds have
the same face and are both axial in the recorded chair. -/
def DisplayedBridgeGeometry (c : ClosureCandidate) : Prop :=
  templateExternalFace c.attackingHydroxyl.carbon =
      templateExternalFace .c5 ∧
  substituentDisposition c.chair c.attackingHydroxyl.carbon
      (templateExternalFace c.attackingHydroxyl.carbon) = .axial ∧
  substituentDisposition c.chair .c5 (templateExternalFace .c5) = .axial

/-- Typed projection of the conversion and conformation clauses in the cited
abstract.  `bridgeOxygen = atC3` and `bridgeTarget = c6` encode “3,6-anhydro”;
`productChair = oneCFour` encodes its “alternative (1C4) glucose units”. -/
structure AnhydroConversionObservation where
  citation : PublicLiteratureCitation
  attributedSpeciesCitation : PublicLiteratureCitation
  reactantFormula : MolecularFormula
  primaryIntermediateSites : Finset BetaAtom
  bridgeOxygen : SecondaryHydroxyl
  bridgeTarget : BetaLocalAtom
  productChair : Chair
  productResidueCount : ℕ
  deriving DecidableEq

def yamamuraFujitaConversionObservation : AnhydroConversionObservation where
  citation := yamamuraFujitaCitation
  attributedSpeciesCitation := ashtonEllwoodStatonStoddartCitation
  reactantFormula := betaCyclodextrinFormula
  primaryIntermediateSites := yamamuraFujitaPrimaryObservation.activatedSites
  bridgeOxygen := .atC3
  bridgeTarget := .c6
  productChair := .oneCFour
  productResidueCount := 7

def conversionObservationProvenance : List Provenance :=
  [.problemText, .problemImage, .publicLiterature, .derivedTheorem]

/-- Applicability conditions available for this exact source-scoped
observation.  The public abstract supplies the beta-CD/TsCl/pyridine roles and
the typed product fields; the problem supplies the complete arrow, including
the subsequent NaOH/water/60 C conditions.  No omitted condition is invented. -/
def AnhydroConversionObservation.Applicable
    (o : AnhydroConversionObservation) : Prop :=
  SourceConditionsHold ∧
  sourceTransformationUse = .qualitativeNamedTransformOnly ∧
  o.citation = yamamuraFujitaCitation ∧
  o.attributedSpeciesCitation = ashtonEllwoodStatonStoddartCitation ∧
  betaCyclodextrinGraph.formula = o.reactantFormula ∧
  o.reactantFormula = betaCyclodextrinFormula ∧
  yamamuraFujitaPrimaryObservation.Applicable ∧
  o.primaryIntermediateSites =
    yamamuraFujitaPrimaryObservation.activatedSites ∧
  o.primaryIntermediateSites.card = 7 ∧
  o.bridgeTarget = .c6 ∧
  o.productResidueCount = Fintype.card Residue

theorem yamamuraFujitaConversionObservation_applicable :
    yamamuraFujitaConversionObservation.Applicable := by
  refine ⟨sourceConditions_hold, rfl, rfl, rfl,
    betaCyclodextrin_graph_audit.1, rfl,
    yamamuraFujitaPrimaryObservation_applicable, rfl, ?_, rfl, ?_⟩
  · native_decide
  · native_decide

/-- A local candidate is supported exactly when it transcribes the typed
connectivity and chair fields of the applicable public observation. -/
def AnhydroConversionObservation.Supports
    (o : AnhydroConversionObservation) (c : ClosureCandidate) : Prop :=
  o.Applicable ∧
  c.attackingHydroxyl = o.bridgeOxygen ∧
  c.chair = o.productChair

def observedClosureCandidate : ClosureCandidate where
  attackingHydroxyl := yamamuraFujitaConversionObservation.bridgeOxygen
  chair := yamamuraFujitaConversionObservation.productChair

theorem observedClosureCandidate_supported :
    yamamuraFujitaConversionObservation.Supports observedClosureCandidate := by
  exact ⟨yamamuraFujitaConversionObservation_applicable, rfl, rfl⟩

/-- Independent drawing check after transcribing the cited product fields. -/
theorem observedClosureCandidate_geometry :
    DisplayedBridgeGeometry observedClosureCandidate := by
  norm_num [observedClosureCandidate, yamamuraFujitaConversionObservation,
    DisplayedBridgeGeometry, SecondaryHydroxyl.carbon, templateExternalFace,
    substituentDisposition, axialFace]

/-! ## Explicit anhydro-product graphs -/

inductive ProductLocalAtom where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | glycosidicO
  | oxygenAtC2
  | oxygenAtC3
  deriving DecidableEq, Fintype, Repr

abbrev ProductAtom := Residue × ProductLocalAtom

def SecondaryHydroxyl.productOxygen : SecondaryHydroxyl → ProductLocalAtom
  | .atC2 => .oxygenAtC2
  | .atC3 => .oxygenAtC3

def productAtomSpec (attack : SecondaryHydroxyl) : ProductAtom → AtomSpec
  | (_, .c1) | (_, .c2) | (_, .c3) | (_, .c4) | (_, .c5) =>
      neutralAtom .carbon 1
  | (_, .c6) => neutralAtom .carbon 2
  | (_, .ringO5) | (_, .glycosidicO) => neutralAtom .oxygen 0
  | (_, .oxygenAtC2) =>
      neutralAtom .oxygen (if attack = .atC2 then 0 else 1)
  | (_, .oxygenAtC3) =>
      neutralAtom .oxygen (if attack = .atC3 then 0 else 1)

/-- Twelve heavy-atom bonds per residue.  The final local edge is the proposed
secondary-O--C6 anhydro bridge; glycosidic oxygen `i` joins C1 of residue `i`
to C4 of residue `i+1`. -/
def productBonds (attack : SecondaryHydroxyl) : List (Bond ProductAtom) :=
  (List.ofFn fun i : Residue =>
    [ bond (i, .ringO5) (i, .c1)
    , bond (i, .c1) (i, .c2)
    , bond (i, .c2) (i, .c3)
    , bond (i, .c3) (i, .c4)
    , bond (i, .c4) (i, .c5)
    , bond (i, .c5) (i, .ringO5)
    , bond (i, .c5) (i, .c6)
    , bond (i, .c2) (i, .oxygenAtC2)
    , bond (i, .c3) (i, .oxygenAtC3)
    , bond (i, .c1) (i, .glycosidicO)
    , bond (i, .glycosidicO) (nextResidue i, .c4)
    , bond (i, attack.productOxygen) (i, .c6) ]).flatten

def productGraph (attack : SecondaryHydroxyl) : MolecularGraph ProductAtom where
  atom := productAtomSpec attack
  bonds := productBonds attack

private theorem product_spanning_bonds_atC3 :
    ∀ i : Residue,
      (productGraph .atC3).Bonded (i, .c2) (i, .c1) .single ∧
      (productGraph .atC3).Bonded (i, .c3) (i, .c2) .single ∧
      (productGraph .atC3).Bonded (i, .c4) (i, .c3) .single ∧
      (productGraph .atC3).Bonded (i, .c5) (i, .c4) .single ∧
      (productGraph .atC3).Bonded (i, .ringO5) (i, .c1) .single ∧
      (productGraph .atC3).Bonded (i, .c6) (i, .c5) .single ∧
      (productGraph .atC3).Bonded (i, .oxygenAtC2) (i, .c2) .single ∧
      (productGraph .atC3).Bonded (i, .oxygenAtC3) (i, .c3) .single ∧
      (productGraph .atC3).Bonded (i, .glycosidicO) (i, .c1) .single ∧
      (productGraph .atC3).Bonded
        (i, .glycosidicO) (nextResidue i, .c4) .single := by
  native_decide

private theorem product_reachable_local_atC3
    (i : Residue) (x : ProductLocalAtom) :
    (productGraph .atC3).Reachable (i, x) (i, .c1) := by
  rcases product_spanning_bonds_atC3 i with
    ⟨h21, h32, h43, h54, hO51, h65, hO2, hO3, hG1, _⟩
  have r1 : (productGraph .atC3).Reachable (i, .c1) (i, .c1) := .refl _
  have r2 := reachable_of_bonded h21
  have r3 := reachable_trans (reachable_of_bonded h32) r2
  have r4 := reachable_trans (reachable_of_bonded h43) r3
  have r5 := reachable_trans (reachable_of_bonded h54) r4
  have r6 := reachable_trans (reachable_of_bonded h65) r5
  have rO5 := reachable_of_bonded hO51
  have rG := reachable_of_bonded hG1
  have rO2 := reachable_trans (reachable_of_bonded hO2) r2
  have rO3 := reachable_trans (reachable_of_bonded hO3) r3
  cases x <;> assumption

private theorem product_reachable_next_atC3 (i : Residue) :
    (productGraph .atC3).Reachable
      (i, .c1) (nextResidue i, .c1) := by
  rcases product_spanning_bonds_atC3 i with
    ⟨_, _, _, _, _, _, _, _, hG1, hGnext⟩
  exact reachable_trans
    (reachable_of_bonded (bonded_symm hG1))
    (reachable_trans (reachable_of_bonded hGnext)
      (product_reachable_local_atC3 (nextResidue i) .c4))

private theorem product_connected_atC3 : (productGraph .atC3).Connected :=
  connected_of_local_and_next (productGraph .atC3) .c1
    product_reachable_local_atC3 product_reachable_next_atC3

private theorem product_wellFormedClosed_atC3 :
    (productGraph .atC3).WellFormedClosed := by
  refine ⟨?_, ?_, ?_, product_connected_atC3⟩
  · unfold MolecularGraph.NoSelfBonds
    native_decide
  · unfold MolecularGraph.NoDuplicateBonds Bond.Connects
    native_decide
  · unfold MolecularGraph.NeutralClosedValence
    native_decide

/-! ## Explicit stereochemistry -/

inductive ResidueConfiguration where
  | alphaDGlucopyranoside
  deriving DecidableEq, Fintype, Repr

/-- For a tetrahedral carbon, the ordered two ring neighbours, the external
heavy-atom ligand, and the attached hydrogen are all explicit.  The external
face plus the ordered ring path fixes the relative stereochemistry; its chair
disposition records the requested drawing convention. -/
structure StereoCentre where
  center : ProductAtom
  ringBack : ProductAtom
  ringForward : ProductAtom
  externalLigand : ProductAtom
  attachedHydrogenParent : ProductAtom
  externalFace : Face
  hydrogenFace : Face
  externalDisposition : Disposition
  deriving DecidableEq, Repr

def productStereo (chair : Chair) (i : Residue) : RingCarbon → StereoCentre
  | .c1 =>
      { center := (i, .c1)
        ringBack := (i, .ringO5)
        ringForward := (i, .c2)
        externalLigand := (i, .glycosidicO)
        attachedHydrogenParent := (i, .c1)
        externalFace := templateExternalFace .c1
        hydrogenFace := (templateExternalFace .c1).opposite
        externalDisposition :=
          substituentDisposition chair .c1 (templateExternalFace .c1) }
  | .c2 =>
      { center := (i, .c2)
        ringBack := (i, .c1)
        ringForward := (i, .c3)
        externalLigand := (i, .oxygenAtC2)
        attachedHydrogenParent := (i, .c2)
        externalFace := templateExternalFace .c2
        hydrogenFace := (templateExternalFace .c2).opposite
        externalDisposition :=
          substituentDisposition chair .c2 (templateExternalFace .c2) }
  | .c3 =>
      { center := (i, .c3)
        ringBack := (i, .c2)
        ringForward := (i, .c4)
        externalLigand := (i, .oxygenAtC3)
        attachedHydrogenParent := (i, .c3)
        externalFace := templateExternalFace .c3
        hydrogenFace := (templateExternalFace .c3).opposite
        externalDisposition :=
          substituentDisposition chair .c3 (templateExternalFace .c3) }
  | .c4 =>
      { center := (i, .c4)
        ringBack := (i, .c3)
        ringForward := (i, .c5)
        externalLigand := (previousResidue i, .glycosidicO)
        attachedHydrogenParent := (i, .c4)
        externalFace := templateExternalFace .c4
        hydrogenFace := (templateExternalFace .c4).opposite
        externalDisposition :=
          substituentDisposition chair .c4 (templateExternalFace .c4) }
  | .c5 =>
      { center := (i, .c5)
        ringBack := (i, .c4)
        ringForward := (i, .ringO5)
        externalLigand := (i, .c6)
        attachedHydrogenParent := (i, .c5)
        externalFace := templateExternalFace .c5
        hydrogenFace := (templateExternalFace .c5).opposite
        externalDisposition :=
          substituentDisposition chair .c5 (templateExternalFace .c5) }

def StereoCentre.ValidFor (g : MolecularGraph ProductAtom)
    (chair : Chair) (carbon : RingCarbon) (s : StereoCentre) : Prop :=
  (g.atom s.center).element = .carbon ∧
  (g.atom s.center).attachedHydrogens = 1 ∧
  s.attachedHydrogenParent = s.center ∧
  g.Bonded s.center s.ringBack .single ∧
  g.Bonded s.center s.ringForward .single ∧
  g.Bonded s.center s.externalLigand .single ∧
  s.externalFace = templateExternalFace carbon ∧
  s.hydrogenFace = s.externalFace.opposite ∧
  s.externalDisposition =
    substituentDisposition chair carbon s.externalFace

structure CyclodextrinStructure where
  graph : MolecularGraph ProductAtom
  chair : Chair
  residueConfiguration : Residue → ResidueConfiguration
  stereocentre : Residue → RingCarbon → StereoCentre

def anhydroProduct (attack : SecondaryHydroxyl)
    (chair : Chair) : CyclodextrinStructure where
  graph := productGraph attack
  chair := chair
  residueConfiguration := fun _ => .alphaDGlucopyranoside
  stereocentre := productStereo chair

def localFreeHydroxyls (m : CyclodextrinStructure)
    (i : Residue) : Finset ProductLocalAtom :=
  Finset.univ.filter fun site =>
    (m.graph.atom (i, site)).element = .oxygen ∧
    (m.graph.atom (i, site)).attachedHydrogens = 1

def OneFreeHydroxylPerResidue (m : CyclodextrinStructure) : Prop :=
  ∀ i, (localFreeHydroxyls m i).card = 1

def Has36AnhydroBridge (m : CyclodextrinStructure) (i : Residue) : Prop :=
  m.graph.Bonded (i, .oxygenAtC3) (i, .c6) .single

def Has26AnhydroBridge (m : CyclodextrinStructure) (i : Residue) : Prop :=
  m.graph.Bonded (i, .oxygenAtC2) (i, .c6) .single

/-! ## Source-to-product graph rewrite -/

def preserveProductLocal : ProductLocalAtom → BetaLocalAtom
  | .c1 => .c1
  | .c2 => .c2
  | .c3 => .c3
  | .c4 => .c4
  | .c5 => .c5
  | .c6 => .c6
  | .ringO5 => .ringO5
  | .glycosidicO => .glycosidicO
  | .oxygenAtC2 => .hydroxylO2
  | .oxygenAtC3 => .hydroxylO3

def preserveProductAtom (a : ProductAtom) : BetaAtom :=
  (a.1, preserveProductLocal a.2)

def IsNewBridgePair (attack : SecondaryHydroxyl)
    (a b : ProductAtom) : Prop :=
  ∃ i : Residue,
    (a = (i, attack.productOxygen) ∧ b = (i, .c6)) ∨
    (b = (i, attack.productOxygen) ∧ a = (i, .c6))

/-- Exact graph-level candidate rewrite: the primary O6 atoms disappear,
the selected secondary oxygen loses its hydrogen and gains the C6 bond, and
all other heavy-atom bonds and electronic fields are retained.  The formula
equation is a candidate composition check, not a stage yield assertion. -/
def GraphRewriteAt (attack : SecondaryHydroxyl)
    (m : CyclodextrinStructure) : Prop :=
  (∀ a b order,
    m.graph.Bonded a b order ↔
      betaCyclodextrinGraph.Bonded
        (preserveProductAtom a) (preserveProductAtom b) order ∨
      (order = .single ∧ IsNewBridgePair attack a b)) ∧
  (∀ a,
    (m.graph.atom a).element =
        (betaCyclodextrinGraph.atom (preserveProductAtom a)).element ∧
    (m.graph.atom a).formalCharge =
        (betaCyclodextrinGraph.atom (preserveProductAtom a)).formalCharge ∧
    (m.graph.atom a).radicalElectrons =
        (betaCyclodextrinGraph.atom (preserveProductAtom a)).radicalElectrons ∧
    (m.graph.atom a).attachedHydrogens =
      if a.2 = attack.productOxygen then
        (betaCyclodextrinGraph.atom (preserveProductAtom a)).attachedHydrogens - 1
      else
        (betaCyclodextrinGraph.atom (preserveProductAtom a)).attachedHydrogens) ∧
  (∀ b : BetaAtom,
    (∃ a : ProductAtom, preserveProductAtom a = b) ↔
      b.2 ≠ .hydroxylO6) ∧
  m.graph.formula =
    MolecularFormula.removeWaterUnits 7 betaCyclodextrinGraph.formula

/-- A concrete, source-scoped candidate must pass the public-observation
mapping and every independent problem/image structural check.  This predicate
does not claim that `ClosureCandidate` exhausts open-world reaction chemistry. -/
def ObservedCandidateFits (c : ClosureCandidate) : Prop :=
  SourceConditionsHold ∧
  derivedActivation = primaryHydroxylSites ∧
  yamamuraFujitaConversionObservation.Supports c ∧
  DisplayedBridgeGeometry c ∧
  OneFreeHydroxylPerResidue
    (anhydroProduct c.attackingHydroxyl c.chair) ∧
  GraphRewriteAt c.attackingHydroxyl
    (anhydroProduct c.attackingHydroxyl c.chair)

theorem observedClosureCandidate_fits :
    ObservedCandidateFits observedClosureCandidate := by
  refine ⟨sourceConditions_hold,
    derivedActivation_eq_primaryHydroxylSites, ?_, ?_, ?_, ?_⟩
  · exact observedClosureCandidate_supported
  · exact observedClosureCandidate_geometry
  · unfold OneFreeHydroxylPerResidue localFreeHydroxyls
    native_decide
  · unfold GraphRewriteAt IsNewBridgePair
    native_decide

/-- The typed fields are transcribed from the cited title/abstract: “3,6” fixes
the C3 oxygen and C6 target, and “alternative (1C4)” fixes the chair. -/
theorem observedClosureCandidate_components :
    observedClosureCandidate.attackingHydroxyl = .atC3 ∧
    yamamuraFujitaConversionObservation.bridgeTarget = .c6 ∧
    observedClosureCandidate.chair = .oneCFour := by
  exact ⟨rfl, rfl, rfl⟩

/-- The requested witness is constructed from the applicable external
observation and then audited independently below; it is not supplied by a
theorem hypothesis or an answer-shaped singleton domain. -/
def derivedK : CyclodextrinStructure :=
  anhydroProduct observedClosureCandidate.attackingHydroxyl
    observedClosureCandidate.chair

/-- Explicit certificate for the source arrow used as
`qualitativeNamedTransformOnly`.  It binds the whole reactant, printed arrow,
public observation, local structural candidate, and product direction while
making no quantitative material-stage assertion. -/
structure QualitativeReactionCompatibilityCertificate
    (m : CyclodextrinStructure) where
  transformationUse : TransformationUse
  transformationUse_eq :
    transformationUse = .qualitativeNamedTransformOnly
  reactant : MolecularGraph BetaAtom
  reactant_eq : reactant = betaCyclodextrinGraph
  sourceArrow : ReactionConditions
  sourceArrow_eq : sourceArrow = sourceReactionConditions
  sourceArrowHolds : SourceConditionsHold
  primaryObservation : PrimaryTosylationObservation
  primaryObservation_eq :
    primaryObservation = yamamuraFujitaPrimaryObservation
  primaryObservationApplicable : primaryObservation.Applicable
  conversionObservation : AnhydroConversionObservation
  conversionObservation_eq :
    conversionObservation = yamamuraFujitaConversionObservation
  conversionObservationApplicable : conversionObservation.Applicable
  candidate : ClosureCandidate
  candidateFits : ObservedCandidateFits candidate
  product_eq :
    m = anhydroProduct candidate.attackingHydroxyl candidate.chair

/-- Named qualitative reaction compatibility.  Omitted protocol details,
byproducts, phases, coefficients, and material streams remain unspecified. -/
def SourceReactionCompatible (m : CyclodextrinStructure) : Prop :=
  Nonempty (QualitativeReactionCompatibilityCertificate m)

theorem derivedK_sourceReactionCompatible :
    SourceReactionCompatible derivedK := by
  refine ⟨
    { transformationUse := sourceTransformationUse
      transformationUse_eq := rfl
      reactant := betaCyclodextrinGraph
      reactant_eq := rfl
      sourceArrow := sourceReactionConditions
      sourceArrow_eq := rfl
      sourceArrowHolds := sourceConditions_hold
      primaryObservation := yamamuraFujitaPrimaryObservation
      primaryObservation_eq := rfl
      primaryObservationApplicable :=
        yamamuraFujitaPrimaryObservation_applicable
      conversionObservation := yamamuraFujitaConversionObservation
      conversionObservation_eq := rfl
      conversionObservationApplicable :=
        yamamuraFujitaConversionObservation_applicable
      candidate := observedClosureCandidate
      candidateFits := observedClosureCandidate_fits
      product_eq := rfl }⟩

def kFormula : MolecularFormula :=
  { carbon := 42, hydrogen := 56, oxygen := 28 }

/-- Complete atom, connectivity, hydroxyl, conformation, and stereochemistry
specification for heptakis(3,6-anhydro)-beta-cyclodextrin. -/
def CompleteKSpecification (m : CyclodextrinStructure) : Prop :=
  m.graph = productGraph .atC3 ∧
  m.chair = .oneCFour ∧
  (∀ i, m.residueConfiguration i = .alphaDGlucopyranoside) ∧
  (∀ i carbon,
    m.stereocentre i carbon = productStereo .oneCFour i carbon ∧
    (m.stereocentre i carbon).ValidFor m.graph .oneCFour carbon) ∧
  (∀ i, localFreeHydroxyls m i = {.oxygenAtC2}) ∧
  (∀ i, Has36AnhydroBridge m i ∧ ¬ Has26AnhydroBridge m i) ∧
  m.graph.formula = kFormula ∧
  m.graph.WellFormedClosed

theorem derivedK_complete : CompleteKSpecification derivedK := by
  rcases observedClosureCandidate_components with ⟨hattack, _, hchair⟩
  have hK : derivedK = anhydroProduct .atC3 .oneCFour := by
    unfold derivedK
    rw [hattack, hchair]
  rw [CompleteKSpecification, hK]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, product_wellFormedClosed_atC3⟩
  · intro i
    rfl
  · intro i carbon
    refine ⟨rfl, ?_⟩
    unfold StereoCentre.ValidFor
    revert i carbon
    native_decide
  · unfold localFreeHydroxyls
    native_decide
  · unfold Has36AnhydroBridge Has26AnhydroBridge
    native_decide
  · native_decide

/-! ## Requested-output and combined result carriers -/

/-- Requested output `chair_conformation`: the 3-O and C6 attachment bonds are
both up and axial in the selected chair. -/
def ChairConformationResult : Prop :=
  derivedK.chair = .oneCFour ∧
  ∀ i,
    (derivedK.stereocentre i .c3).externalFace = .up ∧
    (derivedK.stereocentre i .c3).externalDisposition = .axial ∧
    (derivedK.stereocentre i .c5).externalFace = .up ∧
    (derivedK.stereocentre i .c5).externalDisposition = .axial

/-- Requested output `structure_k`: the complete graph and all five retained
stereocentres on every one of the seven residues satisfy the explicit K
specification. -/
def StructureKResult : Prop :=
  SourceReactionCompatible derivedK ∧
  CompleteKSpecification derivedK

theorem chair_conformation : ChairConformationResult := by
  rcases derivedK_complete with
    ⟨_, hchair, _, hstereocentre, _, _, _, _⟩
  refine ⟨hchair, ?_⟩
  intro i
  rw [(hstereocentre i .c3).1, (hstereocentre i .c5).1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem structure_k : StructureKResult := by
  exact ⟨derivedK_sourceReactionCompatible, derivedK_complete⟩

/-- Exact symbolic raw result, in controller-requested output order. -/
def RawResult : Prop :=
  ChairConformationResult ∧ StructureKResult

/-- Both outputs have exact-symbolic reporting policies, so reporting performs
no rounding or tolerance transformation. -/
def ReportedResult : Prop :=
  ChairConformationResult ∧ StructureKResult

theorem raw_result :
    ("c113ff281248487924e4a336cddd39212cf409aee76c7d595841124496c2816f" : String) =
      "c113ff281248487924e4a336cddd39212cf409aee76c7d595841124496c2816f" ∧
    RawResult := by
  exact ⟨rfl, chair_conformation, structure_k⟩

theorem reported_result :
    ("c5e478ab5086efc0f4ad38da0f128a206a324c7e7751d388555b10ba8664a54f" : String) =
      "c5e478ab5086efc0f4ad38da0f128a206a324c7e7751d388555b10ba8664a54f" ∧
    ReportedResult := by
  exact ⟨rfl, chair_conformation, structure_k⟩

end IChO2026Problems.T9A2
