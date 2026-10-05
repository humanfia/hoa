import Mathlib
import IChO2026Chem

/-!
# IChO 2026, theory problem 6, part 6

The source asks for the structures `M`--`R` in the page-4 synthesis of a
butadiyne-linked zinc-porphyrin nanoring.  The label skipped by the linear
sequence is present in the figure as `P6`: it is the cyclic hexamer obtained
after template removal.  Accordingly, `structureP` below is the complete
six-porphyrin product, rather than an invented monomer.

The configured libraries have simple graphs and reaction-network structures,
but no molecular graph whose vertices carry element, formal charge, radical,
hydrogen and stereochemical data and whose edges carry chemical bond order.
The small target-local model below therefore expands every attached hydrogen
to a vertex.  It also distinguishes covalent, triple, and zinc coordination
bonds.  No official answer or prior-result certificate is used.
-/

namespace IChO2026Problems.Icho2026T6A6

/-! ## Source provenance and atom-level molecular graphs -/

inductive Provenance
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

inductive Element
  | hydrogen
  | carbon
  | nitrogen
  | oxygen
  | silicon
  | bromine
  | zinc
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  | triple
  | coordination
  deriving DecidableEq, Repr

/-- Coordination bonds are recorded but do not enter the ordinary covalent
valence sum. -/
def BondOrder.covalentValence : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .coordination => 0

inductive LocalStereo
  | notStereogenic
  | sourceUnspecified
  | r
  | s
  deriving DecidableEq, Repr

structure HeavyAtom where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  attachedHydrogens : ℕ
  stereochemistry : LocalStereo
  deriving DecidableEq, Repr

structure Atom where
  element : Element
  formalCharge : ℤ
  radicalElectrons : ℕ
  stereochemistry : LocalStereo
  deriving DecidableEq, Repr

/-- Constructors name every heavy atom in the six requested products. -/
inductive HeavyAtomId
  | areneRingCarbon (position : ℕ)
  | areneMethylCarbon (ringPosition : ℕ)
  | areneFormylCarbon (ringPosition : ℕ)
  | areneFormylOxygen (ringPosition : ℕ)
  | areneTertButylCenter (ringPosition : ℕ)
  | areneTertButylMethyl (ringPosition branch : ℕ)
  | porphyrinPyrroleCarbon (unit pyrrole position : ℕ)
  | porphyrinMesoCarbon (unit site : ℕ)
  | porphyrinNitrogen (unit pyrrole : ℕ)
  | porphyrinZinc (unit : ℕ)
  | arylRingCarbon (unit aryl position : ℕ)
  | arylTertButylCenter (unit aryl ringPosition : ℕ)
  | arylTertButylMethyl (unit aryl ringPosition branch : ℕ)
  | mesoBromine (unit site : ℕ)
  | ethynylCarbon (unit site position : ℕ)
  deriving DecidableEq, Repr

inductive AtomId
  | heavy (id : HeavyAtomId)
  | hydrogen (parent : HeavyAtomId) (position : ℕ)
  deriving DecidableEq, Repr

structure HeavyBond where
  left : HeavyAtomId
  right : HeavyAtomId
  order : BondOrder
  deriving DecidableEq, Repr

structure Bond where
  left : AtomId
  right : AtomId
  order : BondOrder
  deriving DecidableEq, Repr

structure HeavyGraph where
  atoms : List (HeavyAtomId × HeavyAtom)
  bonds : List HeavyBond
  deriving DecidableEq, Repr

structure MolecularStructure where
  atoms : List (AtomId × Atom)
  bonds : List Bond
  deriving DecidableEq, Repr

structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  silicon : ℕ
  bromine : ℕ
  zinc : ℕ
  deriving DecidableEq, Repr

def MolecularFormula.zero : MolecularFormula :=
  { carbon := 0, hydrogen := 0, nitrogen := 0, oxygen := 0
    silicon := 0, bromine := 0, zinc := 0 }

def MolecularFormula.add (a b : MolecularFormula) : MolecularFormula :=
  { carbon := a.carbon + b.carbon
    hydrogen := a.hydrogen + b.hydrogen
    nitrogen := a.nitrogen + b.nitrogen
    oxygen := a.oxygen + b.oxygen
    silicon := a.silicon + b.silicon
    bromine := a.bromine + b.bromine
    zinc := a.zinc + b.zinc }

def MolecularFormula.scale (n : ℕ) (a : MolecularFormula) : MolecularFormula :=
  { carbon := n * a.carbon
    hydrogen := n * a.hydrogen
    nitrogen := n * a.nitrogen
    oxygen := n * a.oxygen
    silicon := n * a.silicon
    bromine := n * a.bromine
    zinc := n * a.zinc }

def Atom.formulaContribution (a : Atom) : MolecularFormula :=
  match a.element with
  | .hydrogen => { MolecularFormula.zero with hydrogen := 1 }
  | .carbon => { MolecularFormula.zero with carbon := 1 }
  | .nitrogen => { MolecularFormula.zero with nitrogen := 1 }
  | .oxygen => { MolecularFormula.zero with oxygen := 1 }
  | .silicon => { MolecularFormula.zero with silicon := 1 }
  | .bromine => { MolecularFormula.zero with bromine := 1 }
  | .zinc => { MolecularFormula.zero with zinc := 1 }

def MolecularStructure.formula (s : MolecularStructure) : MolecularFormula :=
  s.atoms.foldl
    (fun total entry => MolecularFormula.add total entry.2.formulaContribution)
    MolecularFormula.zero

def MolecularStructure.atomIds (s : MolecularStructure) : List AtomId :=
  s.atoms.map Prod.fst

def MolecularStructure.totalFormalCharge (s : MolecularStructure) : ℤ :=
  (s.atoms.map fun entry => entry.2.formalCharge).sum

def MolecularStructure.totalRadicalElectrons (s : MolecularStructure) : ℕ :=
  (s.atoms.map fun entry => entry.2.radicalElectrons).sum

def MolecularStructure.incidentCovalentValence
    (s : MolecularStructure) (id : AtomId) : ℕ :=
  (s.bonds.map fun b =>
    if b.left = id ∨ b.right = id then b.order.covalentValence else 0).sum

def Element.expectedCovalentValence (e : Element) (charge : ℤ) : ℕ :=
  match e with
  | .hydrogen => 1
  | .carbon => 4
  | .nitrogen => if charge = -1 then 2 else 3
  | .oxygen => 2
  | .silicon => 4
  | .bromine => 1
  | .zinc => 0

def MolecularStructure.BondEndpointsPresent (s : MolecularStructure) : Prop :=
  ∀ b ∈ s.bonds, b.left ∈ s.atomIds ∧ b.right ∈ s.atomIds

def MolecularStructure.NoSelfBonds (s : MolecularStructure) : Prop :=
  ∀ b ∈ s.bonds, b.left ≠ b.right

def MolecularStructure.ValenceCorrect (s : MolecularStructure) : Prop :=
  ∀ id atom, (id, atom) ∈ s.atoms →
    s.incidentCovalentValence id =
      atom.element.expectedCovalentValence atom.formalCharge

def MolecularStructure.Adjacent (s : MolecularStructure) (a b : AtomId) : Prop :=
  ∃ bond ∈ s.bonds,
    (bond.left = a ∧ bond.right = b) ∨
      (bond.left = b ∧ bond.right = a)

def MolecularStructure.Connected (s : MolecularStructure) : Prop :=
  ∀ a ∈ s.atomIds, ∀ b ∈ s.atomIds,
    Relation.ReflTransGen s.Adjacent a b

def MolecularStructure.StereochemistryComplete (s : MolecularStructure) : Prop :=
  ∀ id atom, (id, atom) ∈ s.atoms →
    atom.stereochemistry = .notStereogenic

def MolecularStructure.FullySpecifiedNeutralClosedShell
    (s : MolecularStructure) : Prop :=
  s.atomIds.Nodup ∧
    s.bonds.Nodup ∧
    s.BondEndpointsPresent ∧
    s.NoSelfBonds ∧
    s.ValenceCorrect ∧
    s.Connected ∧
    s.StereochemistryComplete ∧
    s.totalFormalCharge = 0 ∧
    s.totalRadicalElectrons = 0

def mkHeavyAtom (element : Element) (charge : ℤ) (hydrogens : ℕ) : HeavyAtom :=
  { element := element
    formalCharge := charge
    radicalElectrons := 0
    attachedHydrogens := hydrogens
    stereochemistry := .notStereogenic }

def mkHeavyBond (left right : HeavyAtomId) (order : BondOrder) : HeavyBond :=
  { left := left, right := right, order := order }

def expandHeavyAtom (entry : HeavyAtomId × HeavyAtom) : List (AtomId × Atom) :=
  let heavy : Atom :=
    { element := entry.2.element
      formalCharge := entry.2.formalCharge
      radicalElectrons := entry.2.radicalElectrons
      stereochemistry := entry.2.stereochemistry }
  let hydrogens := (List.range entry.2.attachedHydrogens).map fun h =>
    (AtomId.hydrogen entry.1 h,
      { element := Element.hydrogen
        formalCharge := 0
        radicalElectrons := 0
        stereochemistry := LocalStereo.notStereogenic })
  (AtomId.heavy entry.1, heavy) :: hydrogens

def hydrogenBonds (entry : HeavyAtomId × HeavyAtom) : List Bond :=
  (List.range entry.2.attachedHydrogens).map fun h =>
    { left := .heavy entry.1
      right := .hydrogen entry.1 h
      order := .single }

def HeavyGraph.expand (g : HeavyGraph) : MolecularStructure :=
  { atoms := g.atoms.flatMap expandHeavyAtom
    bonds :=
      g.bonds.map (fun b =>
        { left := .heavy b.left, right := .heavy b.right, order := b.order }) ++
      g.atoms.flatMap hydrogenBonds }

def CandidateChecks (g : HeavyGraph) (formula : MolecularFormula) : Prop :=
  g.expand.formula = formula ∧
    g.expand.FullySpecifiedNeutralClosedShell

/-! ### Finite certificates for the explicit molecular graphs

`Connected` is intentionally stated over the (infinite) type of all syntactic
atom identifiers, restricted by membership in the concrete atom list.  Thus
the proposition itself has no global `Decidable` instance.  A rooted parent
scheme gives every non-root listed atom one adjacent parent of smaller rank.
The well-founded proof below turns that finite certificate into genuine
`ReflTransGen` reachability.  Consequently `native_decide` below checks only
concrete atom, bond, and rank data; it is not an axiom for connectivity. -/

structure RootedParentScheme where
  root : AtomId
  parent : AtomId → Option AtomId
  rank : AtomId → ℕ

/-- Decidable bond lookup used only inside a finite certificate. -/
def MolecularStructure.hasBondBetween
    (s : MolecularStructure) (a b : AtomId) : Bool :=
  s.bonds.any fun bond => decide
    ((bond.left = a ∧ bond.right = b) ∨
      (bond.left = b ∧ bond.right = a))

/-- Every listed atom is either the root or has a listed, bonded parent of
strictly smaller rank. -/
def MolecularStructure.ValidParentScheme
    (s : MolecularStructure) (scheme : RootedParentScheme) : Bool :=
  decide (scheme.root ∈ s.atomIds) &&
    s.atomIds.all fun id =>
      if id = scheme.root then true
      else
        match scheme.parent id with
        | none => false
        | some parent => decide
            (parent ∈ s.atomIds ∧
              scheme.rank parent < scheme.rank id ∧
              s.hasBondBetween parent id = true)

/-- All non-connectivity fields of `FullySpecifiedNeutralClosedShell`, written
with `List.Forall` so that the concrete audit is decidable. -/
def MolecularStructure.FiniteAudit
    (s : MolecularStructure) (formula : MolecularFormula) : Prop :=
  s.formula = formula ∧
    s.atomIds.Nodup ∧
    s.bonds.Nodup ∧
    s.bonds.Forall (fun bond =>
      bond.left ∈ s.atomIds ∧ bond.right ∈ s.atomIds) ∧
    s.bonds.Forall (fun bond => bond.left ≠ bond.right) ∧
    s.atoms.Forall (fun entry =>
      s.incidentCovalentValence entry.1 =
        entry.2.element.expectedCovalentValence entry.2.formalCharge) ∧
    s.atoms.Forall (fun entry =>
      entry.2.stereochemistry = .notStereogenic) ∧
    s.totalFormalCharge = 0 ∧
    s.totalRadicalElectrons = 0

theorem MolecularStructure.adjacent_symm
    {s : MolecularStructure} {a b : AtomId} (h : s.Adjacent a b) :
    s.Adjacent b a := by
  rcases h with ⟨bond, hbond, hab | hab⟩
  · exact ⟨bond, hbond, Or.inr ⟨hab.1, hab.2⟩⟩
  · exact ⟨bond, hbond, Or.inl ⟨hab.1, hab.2⟩⟩

theorem MolecularStructure.reflTransGen_adjacent_symm
    {s : MolecularStructure} {a b : AtomId}
    (h : Relation.ReflTransGen s.Adjacent a b) :
    Relation.ReflTransGen s.Adjacent b a := by
  induction h with
  | refl => rfl
  | tail _ hyz ih =>
      exact (Relation.ReflTransGen.single (s.adjacent_symm hyz)).trans ih

theorem MolecularStructure.adjacent_of_hasBondBetween
    (s : MolecularStructure) {a b : AtomId}
    (h : s.hasBondBetween a b = true) : s.Adjacent a b := by
  simp only [MolecularStructure.hasBondBetween, List.any_eq_true,
    decide_eq_true_eq] at h
  exact h

theorem MolecularStructure.connected_of_parent_scheme
    (s : MolecularStructure) (scheme : RootedParentScheme)
    (h : s.ValidParentScheme scheme = true) :
    s.Connected := by
  have hparts := Bool.and_eq_true_iff.mp h
  have hroot_mem : scheme.root ∈ s.atomIds := of_decide_eq_true hparts.1
  have hall := List.all_eq_true.mp hparts.2
  have hreached : ∀ n, ∀ id ∈ s.atomIds, scheme.rank id = n →
      Relation.ReflTransGen s.Adjacent scheme.root id := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro id hid hrank
        have hcertificate := hall id hid
        by_cases hroot : id = scheme.root
        · subst id
          rfl
        · simp only [hroot, ↓reduceIte] at hcertificate
          cases hp : scheme.parent id with
          | none => simp [hp] at hcertificate
          | some parent =>
              simp only [hp, decide_eq_true_eq] at hcertificate
              rcases hcertificate with ⟨hparent_mem, hrank_lt, hbond⟩
              exact (ih (scheme.rank parent) (hrank ▸ hrank_lt) parent
                hparent_mem rfl).tail (s.adjacent_of_hasBondBetween hbond)
  have hrootReach : ∀ id ∈ s.atomIds,
      Relation.ReflTransGen s.Adjacent scheme.root id := by
    intro id hid
    exact hreached (scheme.rank id) id hid rfl
  intro a ha b hb
  exact (s.reflTransGen_adjacent_symm (hrootReach a ha)).trans
    (hrootReach b hb)

theorem candidateChecks_of_finite_certificates
    (g : HeavyGraph) (formula : MolecularFormula)
    (haudit : g.expand.FiniteAudit formula)
    (scheme : RootedParentScheme)
    (hconnected : g.expand.ValidParentScheme scheme = true) :
    CandidateChecks g formula := by
  rcases haudit with
    ⟨hformula, hatoms, hbonds, hendpoints, hself, hvalence, hstereo,
      hcharge, hradicals⟩
  refine ⟨hformula, hatoms, hbonds, ?_, ?_, ?_, ?_, ?_, hcharge, hradicals⟩
  · exact List.forall_iff_forall_mem.mp hendpoints
  · exact List.forall_iff_forall_mem.mp hself
  · intro id atom hmem
    exact List.forall_iff_forall_mem.mp hvalence (id, atom) hmem
  · exact g.expand.connected_of_parent_scheme scheme hconnected
  · intro id atom hmem
    exact List.forall_iff_forall_mem.mp hstereo (id, atom) hmem

/-! ## M and N: the substituted arene domain -/

inductive AreneSubstituent
  | hydrogen
  | methyl
  | tertButyl
  | formyl
  deriving DecidableEq, Repr

structure AreneDescriptor where
  /-- Positions `0`--`5` run around the benzene ring. -/
  substituents : List AreneSubstituent
  deriving DecidableEq, Repr

def AreneDescriptor.substituentAt
    (d : AreneDescriptor) (position : ℕ) : AreneSubstituent :=
  d.substituents.getD position .hydrogen

def benzeneBondOrder (position : ℕ) : BondOrder :=
  if position % 2 = 0 then .double else .single

def AreneDescriptor.heavyAtoms
    (d : AreneDescriptor) : List (HeavyAtomId × HeavyAtom) :=
  let ringAtoms := (List.range 6).map fun p =>
    (.areneRingCarbon p,
      mkHeavyAtom .carbon 0 (if d.substituentAt p = .hydrogen then 1 else 0))
  let substituentAtoms := (List.range 6).flatMap fun p =>
    match d.substituentAt p with
    | .hydrogen => []
    | .methyl =>
        [(.areneMethylCarbon p, mkHeavyAtom .carbon 0 3)]
    | .formyl =>
        [ (.areneFormylCarbon p, mkHeavyAtom .carbon 0 1)
        , (.areneFormylOxygen p, mkHeavyAtom .oxygen 0 0) ]
    | .tertButyl =>
        (.areneTertButylCenter p, mkHeavyAtom .carbon 0 0) ::
          (List.range 3).map fun branch =>
            (.areneTertButylMethyl p branch, mkHeavyAtom .carbon 0 3)
  ringAtoms ++ substituentAtoms

def AreneDescriptor.heavyBonds (d : AreneDescriptor) : List HeavyBond :=
  let ringBonds := (List.range 6).map fun p =>
    mkHeavyBond (.areneRingCarbon p) (.areneRingCarbon ((p + 1) % 6))
      (benzeneBondOrder p)
  let substituentBonds := (List.range 6).flatMap fun p =>
    match d.substituentAt p with
    | .hydrogen => []
    | .methyl =>
        [mkHeavyBond (.areneRingCarbon p) (.areneMethylCarbon p) .single]
    | .formyl =>
        [ mkHeavyBond (.areneRingCarbon p) (.areneFormylCarbon p) .single
        , mkHeavyBond (.areneFormylCarbon p) (.areneFormylOxygen p) .double ]
    | .tertButyl =>
        mkHeavyBond (.areneRingCarbon p) (.areneTertButylCenter p) .single ::
          (List.range 3).map fun branch =>
            mkHeavyBond (.areneTertButylCenter p)
              (.areneTertButylMethyl p branch) .single
  ringBonds ++ substituentBonds

def AreneDescriptor.toHeavyGraph (d : AreneDescriptor) : HeavyGraph :=
  { atoms := d.heavyAtoms, bonds := d.heavyBonds }

structure PositionPair where
  first : ℕ
  second : ℕ
  deriving DecidableEq, Repr

structure CandidateDomain (α : Type) where
  candidates : List α
  provenance : Provenance
  sourceLocator : String

def nonMethylRingPositions : List ℕ := [1, 2, 3, 4, 5]

/-- All ten ways to place two identical tert-butyl groups on the five sites
remaining after retaining the source methyl group at position zero. -/
def mRegioisomerDomain : CandidateDomain PositionPair :=
  { candidates := nonMethylRingPositions.flatMap fun p =>
      (nonMethylRingPositions.filter fun q => decide (p < q)).map fun q =>
        { first := p, second := q }
    provenance := .problemImage
    sourceLocator := "T6_page-4.png: toluene + 2 equiv. t-BuCl/AlCl3" }

def areneForPair (pair : PositionPair) : AreneDescriptor :=
  { substituents := (List.range 6).map fun p =>
      if p = 0 then .methyl
      else if p = pair.first ∨ p = pair.second then .tertButyl
      else .hydrogen }

def reflectedPosition (p : ℕ) : ℕ := (6 - p) % 6

def reflectionPreservesPair (pair : PositionPair) : Bool :=
  decide
    ((reflectedPosition pair.first = pair.first ∧
        reflectedPosition pair.second = pair.second) ∨
      (reflectedPosition pair.first = pair.second ∧
        reflectedPosition pair.second = pair.first))

def canonicalPositionForPair (pair : PositionPair) (p : ℕ) : ℕ :=
  if reflectionPreservesPair pair then min p (reflectedPosition p) else p

def ringHydrogenPositions (pair : PositionPair) : List ℕ :=
  nonMethylRingPositions.filter fun p =>
    decide (p ≠ pair.first ∧ p ≠ pair.second)

/-- One methyl environment, plus symmetry orbits of the two tert-butyl proton
sets and of the three aryl proton sites.  Rapid rotation within each methyl or
tert-butyl group is incorporated before the ring-reflection quotient. -/
def protonEnvironmentCount (pair : PositionPair) : ℕ :=
  1 +
    (([pair.first, pair.second].map (canonicalPositionForPair pair)).eraseDups.length) +
    (((ringHydrogenPositions pair).map (canonicalPositionForPair pair)).eraseDups.length)

/-! ### Source-scoped constitution bridge for M

The problem itself says that `M` is the thermodynamic product, but it does not
print relative free energies.  We therefore do **not** replace free energy by
an invented graph score.  The constitution datum below is scoped to the exact
published claim that the hydrocarbon obtained by di-tert-butylation of toluene
is the 3,5 isomer.  The source observation separately checks that the page-4
arrow is a di-tert-butylation of toluene and supplies the thermodynamic and
four-proton cues.  No yield, mechanism, quantitative energy, or sole-product
claim is imported from the paper.
-/

inductive MStartingArene
  | benzene
  | toluene
  deriving DecidableEq, Repr

inductive MAlkylatingReagent
  | tertButylChloride
  | tertButylBromide
  | isobutene
  deriving DecidableEq, Repr

inductive MLewisAcidCatalyst
  | aluminumChloride
  | ironChloride
  | solidAcid
  deriving DecidableEq, Repr

inductive ProductControl
  | kinetic
  | thermodynamic
  deriving DecidableEq, Repr

structure MSourceObservation where
  ringCarbonCount : ℕ
  startingArene : MStartingArene
  retainedMethylPosition : ℕ
  alkylatingReagent : MAlkylatingReagent
  alkylatingEquivalents : ℕ
  catalyst : MLewisAcidCatalyst
  productControl : ProductControl
  protonTypes : ℕ
  provenance : Provenance
  sourceLocator : String
  deriving DecidableEq, Repr

def page4MObservation : MSourceObservation :=
  { ringCarbonCount := 6
    startingArene := .toluene
    retainedMethylPosition := 0
    alkylatingReagent := .tertButylChloride
    alkylatingEquivalents := 2
    catalyst := .aluminumChloride
    productControl := .thermodynamic
    protonTypes := 4
    provenance := .problemImage
    sourceLocator :=
      "T6_page-4.png: toluene + 2 equiv. t-BuCl/AlCl3; hint: thermodynamic product and four proton types" }

inductive LiteratureClaimKind
  | productConstitutionOnly
  | quantitativeThermodynamics
  | completeReactionOutcome
  deriving DecidableEq, Repr

inductive UnsupportedLiteratureClaim
  | relativeFreeEnergy
  | reactionYield
  | soleProduct
  | completeMechanism
  deriving DecidableEq, Repr

/-- A public primary-literature record.  The `claimedProductPair` is the
atom-position reading of the exact constitution asserted in the deposited
abstract, with the methyl-bearing carbon numbered zero. -/
structure ConstitutionLiteratureRecord where
  title : String
  doi : String
  stableUrl : String
  locator : String
  scopedClaim : String
  substrate : MStartingArene
  substitutionCount : ℕ
  claimedProductPair : PositionPair
  claimKind : LiteratureClaimKind
  unsupportedClaims : List UnsupportedLiteratureClaim
  deriving DecidableEq, Repr

def geuze1956DiTertButylation : ConstitutionLiteratureRecord :=
  { title :=
      "Preparation and proof of the constitution of 3,5-di-tert. butyltoluene"
    doi := "10.1002/recl.19560750309"
    stableUrl := "https://doi.org/10.1002/recl.19560750309"
    locator := "Crossref-deposited abstract; article pages 301-310"
    scopedClaim :=
      "It is proved that the hydrocarbon of m.p. 31-32 degrees obtained by di-tert-butylation of toluene is 3,5-di-tert-butyltoluene."
    substrate := .toluene
    substitutionCount := 2
    claimedProductPair := { first := 2, second := 4 }
    claimKind := .productConstitutionOnly
    unsupportedClaims :=
      [.relativeFreeEnergy, .reactionYield, .soleProduct, .completeMechanism] }

/-- Every field used to apply the literature constitution is checked against
typed page-4 data.  The literature record is not generalized to another
substrate, substitution count, or claim kind. -/
def MConstitutionScopeAudit : Prop :=
  geuze1956DiTertButylation.title =
      "Preparation and proof of the constitution of 3,5-di-tert. butyltoluene" ∧
    geuze1956DiTertButylation.doi = "10.1002/recl.19560750309" ∧
    geuze1956DiTertButylation.stableUrl =
      "https://doi.org/10.1002/recl.19560750309" ∧
    geuze1956DiTertButylation.locator =
      "Crossref-deposited abstract; article pages 301-310" ∧
    geuze1956DiTertButylation.scopedClaim =
      "It is proved that the hydrocarbon of m.p. 31-32 degrees obtained by di-tert-butylation of toluene is 3,5-di-tert-butyltoluene." ∧
    geuze1956DiTertButylation.substrate = page4MObservation.startingArene ∧
    geuze1956DiTertButylation.substitutionCount =
      page4MObservation.alkylatingEquivalents ∧
    page4MObservation.ringCarbonCount = 6 ∧
    page4MObservation.retainedMethylPosition = 0 ∧
    page4MObservation.alkylatingReagent = .tertButylChloride ∧
    page4MObservation.catalyst = .aluminumChloride ∧
    page4MObservation.productControl = .thermodynamic ∧
    page4MObservation.protonTypes = 4 ∧
    page4MObservation.provenance = .problemImage ∧
    geuze1956DiTertButylation.claimKind = .productConstitutionOnly ∧
    geuze1956DiTertButylation.unsupportedClaims =
      [.relativeFreeEnergy, .reactionYield, .soleProduct, .completeMechanism]

/-- The only outcome-changing datum supplied by the paper is its reported
constitution.  Thermodynamic control and the proton count remain problem
observations, and membership is checked in the independently formed domain. -/
def MConstitutionBridge (pair : PositionPair) : Prop :=
  MConstitutionScopeAudit ∧
    pair ∈ mRegioisomerDomain.candidates ∧
    pair = geuze1956DiTertButylation.claimedProductPair

def MSourceConstraints (d : AreneDescriptor) : Prop :=
  ∃ pair ∈ mRegioisomerDomain.candidates,
    d = areneForPair pair ∧
      protonEnvironmentCount pair = page4MObservation.protonTypes ∧
      MConstitutionBridge pair

/-- Independently stated candidate: 1-methyl-3,5-di-tert-butylbenzene. -/
def candidateMDescriptor : AreneDescriptor :=
  { substituents :=
      [.methyl, .hydrogen, .tertButyl, .hydrogen, .tertButyl, .hydrogen] }

/-- NBS/benzoyl peroxide, then HMTA and aqueous acid, replaces the sole
benzylic methyl substituent by formyl without changing the ring pattern. -/
def benzylicBrominationSommelet (d : AreneDescriptor) : AreneDescriptor :=
  { substituents := d.substituents.map fun group =>
      if group = .methyl then .formyl else group }

/-- Independently stated candidate: 3,5-di-tert-butylbenzaldehyde. -/
def candidateNDescriptor : AreneDescriptor :=
  { substituents :=
      [.formyl, .hydrogen, .tertButyl, .hydrogen, .tertButyl, .hydrogen] }

def AreneDescriptor.tertButylPositions (d : AreneDescriptor) : List ℕ :=
  (List.range 6).filter fun p => decide (d.substituentAt p = .tertButyl)

/-! A rooted spanning scheme shared by the explicit arene products. -/

def areneHeavyRank : HeavyAtomId → ℕ
  | .areneRingCarbon position => position
  | .areneMethylCarbon position => 100 + 10 * position
  | .areneFormylCarbon position => 100 + 10 * position
  | .areneFormylOxygen position => 101 + 10 * position
  | .areneTertButylCenter position => 200 + 10 * position
  | .areneTertButylMethyl position branch => 201 + 10 * position + branch
  | _ => 0

def areneAtomRank : AtomId → ℕ
  | .heavy id => areneHeavyRank id
  | .hydrogen parent position => 1000 + 10 * areneHeavyRank parent + position

def areneParent : AtomId → Option AtomId
  | .hydrogen parent _ => some (.heavy parent)
  | .heavy (.areneRingCarbon 0) => none
  | .heavy (.areneRingCarbon (position + 1)) =>
      some (.heavy (.areneRingCarbon position))
  | .heavy (.areneMethylCarbon position) =>
      some (.heavy (.areneRingCarbon position))
  | .heavy (.areneFormylCarbon position) =>
      some (.heavy (.areneRingCarbon position))
  | .heavy (.areneFormylOxygen position) =>
      some (.heavy (.areneFormylCarbon position))
  | .heavy (.areneTertButylCenter position) =>
      some (.heavy (.areneRingCarbon position))
  | .heavy (.areneTertButylMethyl position _) =>
      some (.heavy (.areneTertButylCenter position))
  | _ => none

def areneParentScheme : RootedParentScheme :=
  { root := .heavy (.areneRingCarbon 0)
    parent := areneParent
    rank := areneAtomRank }

/-! ## O, Q, R and P6: zinc porphyrin structures -/

inductive TerminalGroup
  | mesoHydrogen
  | bromine
  | ethynyl
  deriving DecidableEq, Repr

structure PorphyrinDescriptor where
  unitCount : ℕ
  /-- Meso sites occupied by the two aryl groups within every unit. -/
  mesoArylSites : List ℕ
  /-- Ring positions occupied by tert-butyl within every aryl group. -/
  arylTertButylSites : List ℕ
  terminalGroup : TerminalGroup
  /-- `true` adds one terminal-carbon single bond between each neighboring
  pair of units, giving butadiyne links and removing terminal C-H bonds. -/
  cyclicCoupled : Bool
  deriving DecidableEq, Repr

def PorphyrinDescriptor.terminalSites (d : PorphyrinDescriptor) : List ℕ :=
  (List.range 4).filter fun site => decide (site ∉ d.mesoArylSites)

def pyrroleBonds (unit pyrrole : ℕ) : List HeavyBond :=
  let n := HeavyAtomId.porphyrinNitrogen unit pyrrole
  let c0 := HeavyAtomId.porphyrinPyrroleCarbon unit pyrrole 0
  let c1 := HeavyAtomId.porphyrinPyrroleCarbon unit pyrrole 1
  let c2 := HeavyAtomId.porphyrinPyrroleCarbon unit pyrrole 2
  let c3 := HeavyAtomId.porphyrinPyrroleCarbon unit pyrrole 3
  match pyrrole with
  | 0 =>
      [ mkHeavyBond n c0 .single, mkHeavyBond c0 c1 .single
      , mkHeavyBond c1 c2 .double, mkHeavyBond c2 c3 .single
      , mkHeavyBond c3 n .single ]
  | 1 =>
      [ mkHeavyBond n c0 .double, mkHeavyBond c0 c1 .single
      , mkHeavyBond c1 c2 .double, mkHeavyBond c2 c3 .single
      , mkHeavyBond c3 n .single ]
  | 2 =>
      [ mkHeavyBond n c0 .single, mkHeavyBond c0 c1 .double
      , mkHeavyBond c1 c2 .single, mkHeavyBond c2 c3 .double
      , mkHeavyBond c3 n .single ]
  | _ =>
      [ mkHeavyBond n c0 .single, mkHeavyBond c0 c1 .single
      , mkHeavyBond c1 c2 .double, mkHeavyBond c2 c3 .single
      , mkHeavyBond c3 n .double ]

/-- A fixed Kekule representative of the delocalized porphyrin core. -/
def porphyrinMesoBonds (unit : ℕ) : List HeavyBond :=
  [ mkHeavyBond (.porphyrinPyrroleCarbon unit 0 3)
      (.porphyrinMesoCarbon unit 0) .double
  , mkHeavyBond (.porphyrinMesoCarbon unit 0)
      (.porphyrinPyrroleCarbon unit 1 0) .single
  , mkHeavyBond (.porphyrinPyrroleCarbon unit 1 3)
      (.porphyrinMesoCarbon unit 1) .double
  , mkHeavyBond (.porphyrinMesoCarbon unit 1)
      (.porphyrinPyrroleCarbon unit 2 0) .single
  , mkHeavyBond (.porphyrinPyrroleCarbon unit 2 3)
      (.porphyrinMesoCarbon unit 2) .single
  , mkHeavyBond (.porphyrinMesoCarbon unit 2)
      (.porphyrinPyrroleCarbon unit 3 0) .double
  , mkHeavyBond (.porphyrinPyrroleCarbon unit 3 3)
      (.porphyrinMesoCarbon unit 3) .single
  , mkHeavyBond (.porphyrinMesoCarbon unit 3)
      (.porphyrinPyrroleCarbon unit 0 0) .double ]

def PorphyrinDescriptor.unitHeavyAtoms
    (d : PorphyrinDescriptor) (unit : ℕ) : List (HeavyAtomId × HeavyAtom) :=
  let pyrroleCarbons := (List.range 4).flatMap fun pyrrole =>
    (List.range 4).map fun position =>
      (.porphyrinPyrroleCarbon unit pyrrole position,
        mkHeavyAtom .carbon 0 (if position = 1 ∨ position = 2 then 1 else 0))
  let mesoCarbons := (List.range 4).map fun site =>
    let hasHydrogen :=
      site ∉ d.mesoArylSites ∧ d.terminalGroup = .mesoHydrogen
    (.porphyrinMesoCarbon unit site,
      mkHeavyAtom .carbon 0 (if hasHydrogen then 1 else 0))
  let nitrogens := (List.range 4).map fun pyrrole =>
    (.porphyrinNitrogen unit pyrrole,
      mkHeavyAtom .nitrogen (if pyrrole = 0 ∨ pyrrole = 2 then -1 else 0) 0)
  let zinc := [(.porphyrinZinc unit, mkHeavyAtom .zinc 2 0)]
  let arylCarbons := (List.range d.mesoArylSites.length).flatMap fun aryl =>
    (List.range 6).map fun position =>
      let hasHydrogen :=
        position ≠ 0 ∧ position ∉ d.arylTertButylSites
      (.arylRingCarbon unit aryl position,
        mkHeavyAtom .carbon 0 (if hasHydrogen then 1 else 0))
  let arylTertButyls := (List.range d.mesoArylSites.length).flatMap fun aryl =>
    d.arylTertButylSites.flatMap fun position =>
      (.arylTertButylCenter unit aryl position, mkHeavyAtom .carbon 0 0) ::
        (List.range 3).map fun branch =>
          (.arylTertButylMethyl unit aryl position branch,
            mkHeavyAtom .carbon 0 3)
  let terminals := d.terminalSites.flatMap fun site =>
    match d.terminalGroup with
    | .mesoHydrogen => []
    | .bromine => [(.mesoBromine unit site, mkHeavyAtom .bromine 0 0)]
    | .ethynyl =>
        [ (.ethynylCarbon unit site 0, mkHeavyAtom .carbon 0 0)
        , (.ethynylCarbon unit site 1,
            mkHeavyAtom .carbon 0 (if d.cyclicCoupled then 0 else 1)) ]
  pyrroleCarbons ++ mesoCarbons ++ nitrogens ++ zinc ++
    arylCarbons ++ arylTertButyls ++ terminals

def PorphyrinDescriptor.unitHeavyBonds
    (d : PorphyrinDescriptor) (unit : ℕ) : List HeavyBond :=
  let pyrroles := (List.range 4).flatMap (pyrroleBonds unit)
  let zincCoordination := (List.range 4).map fun pyrrole =>
    mkHeavyBond (.porphyrinNitrogen unit pyrrole) (.porphyrinZinc unit)
      .coordination
  let arylRingBonds := (List.range d.mesoArylSites.length).flatMap fun aryl =>
    (List.range 6).map fun p =>
      mkHeavyBond (.arylRingCarbon unit aryl p)
        (.arylRingCarbon unit aryl ((p + 1) % 6)) (benzeneBondOrder p)
  let mesoArylBonds := (List.range d.mesoArylSites.length).map fun aryl =>
    mkHeavyBond
      (.porphyrinMesoCarbon unit (d.mesoArylSites.getD aryl 0))
      (.arylRingCarbon unit aryl 0) .single
  let tertButylBonds := (List.range d.mesoArylSites.length).flatMap fun aryl =>
    d.arylTertButylSites.flatMap fun position =>
      mkHeavyBond (.arylRingCarbon unit aryl position)
          (.arylTertButylCenter unit aryl position) .single ::
        (List.range 3).map fun branch =>
          mkHeavyBond (.arylTertButylCenter unit aryl position)
            (.arylTertButylMethyl unit aryl position branch) .single
  let terminalBonds := d.terminalSites.flatMap fun site =>
    match d.terminalGroup with
    | .mesoHydrogen => []
    | .bromine =>
        [mkHeavyBond (.porphyrinMesoCarbon unit site)
          (.mesoBromine unit site) .single]
    | .ethynyl =>
        [ mkHeavyBond (.porphyrinMesoCarbon unit site)
            (.ethynylCarbon unit site 0) .single
        , mkHeavyBond (.ethynylCarbon unit site 0)
            (.ethynylCarbon unit site 1) .triple ]
  pyrroles ++ porphyrinMesoBonds unit ++ zincCoordination ++
    arylRingBonds ++ mesoArylBonds ++ tertButylBonds ++ terminalBonds

def PorphyrinDescriptor.couplingBonds
    (d : PorphyrinDescriptor) : List HeavyBond :=
  if d.cyclicCoupled then
    (List.range d.unitCount).map fun unit =>
      mkHeavyBond (.ethynylCarbon unit 3 1)
        (.ethynylCarbon ((unit + 1) % d.unitCount) 1 1) .single
  else
    []

def PorphyrinDescriptor.toHeavyGraph (d : PorphyrinDescriptor) : HeavyGraph :=
  { atoms := (List.range d.unitCount).flatMap d.unitHeavyAtoms
    bonds :=
      (List.range d.unitCount).flatMap d.unitHeavyBonds ++ d.couplingBonds }

/-- Two aldehydes and two dipyrromethanes give the alternating 5,15-diaryl
porphyrin; DDQ oxidation and zinc acetate give its neutral zinc complex. -/
def porphyrinFromAldehyde (d : AreneDescriptor) : PorphyrinDescriptor :=
  { unitCount := 1
    mesoArylSites := [0, 2]
    arylTertButylSites := d.tertButylPositions
    terminalGroup := .mesoHydrogen
    cyclicCoupled := false }

def brominateFreeMesoSites (d : PorphyrinDescriptor) : PorphyrinDescriptor :=
  { d with terminalGroup := .bromine }

def sonogashiraThenDesilylate (d : PorphyrinDescriptor) : PorphyrinDescriptor :=
  { d with terminalGroup := .ethynyl }

def macrocyclizeWithTemplate
    (bindingSiteCount : ℕ) (d : PorphyrinDescriptor) : PorphyrinDescriptor :=
  { d with unitCount := bindingSiteCount, cyclicCoupled := true }

/-- Zinc 5,15-bis(3,5-di-tert-butylphenyl)porphyrin. -/
def candidateODescriptor : PorphyrinDescriptor :=
  { unitCount := 1, mesoArylSites := [0, 2]
    arylTertButylSites := [2, 4], terminalGroup := .mesoHydrogen
    cyclicCoupled := false }

/-- The 10,20-dibromo derivative of `candidateODescriptor`. -/
def candidateQDescriptor : PorphyrinDescriptor :=
  { unitCount := 1, mesoArylSites := [0, 2]
    arylTertButylSites := [2, 4], terminalGroup := .bromine
    cyclicCoupled := false }

/-- The 10,20-diethynyl derivative obtained after coupling and fluoride
deprotection. -/
def candidateRDescriptor : PorphyrinDescriptor :=
  { unitCount := 1, mesoArylSites := [0, 2]
    arylTertButylSites := [2, 4], terminalGroup := .ethynyl
    cyclicCoupled := false }

/-- `P6`: six `R`-derived zinc porphyrins joined head-to-tail through six
butadiyne links. -/
def candidatePDescriptor : PorphyrinDescriptor :=
  { unitCount := 6, mesoArylSites := [0, 2]
    arylTertButylSites := [2, 4], terminalGroup := .ethynyl
    cyclicCoupled := true }

def sourceTemplateBindingSiteCount : ℕ := 6

/-! A source-order rooted spanning scheme for the porphyrin products.  Within
each porphyrin it follows the meso/pyrrole perimeter from meso site 1, then
branches to zinc, aryl, tert-butyl, terminal, and hydrogen atoms.  In `P6`,
unit `u + 1` is entered through the depicted butadiyne bond from unit `u`. -/

def porphyrinHeavyUnit : HeavyAtomId → ℕ
  | .porphyrinPyrroleCarbon unit _ _ => unit
  | .porphyrinMesoCarbon unit _ => unit
  | .porphyrinNitrogen unit _ => unit
  | .porphyrinZinc unit => unit
  | .arylRingCarbon unit _ _ => unit
  | .arylTertButylCenter unit _ _ => unit
  | .arylTertButylMethyl unit _ _ _ => unit
  | .mesoBromine unit _ => unit
  | .ethynylCarbon unit _ _ => unit
  | _ => 0

def porphyrinPyrroleBase : ℕ → ℕ
  | 2 => 10
  | 3 => 20
  | 0 => 30
  | 1 => 40
  | pyrrole => 60 + 10 * pyrrole

def porphyrinHeavyLocalRank
    (d : PorphyrinDescriptor) : HeavyAtomId → ℕ
  | .porphyrinMesoCarbon _ 1 => 3
  | .porphyrinMesoCarbon _ 2 => 14
  | .porphyrinMesoCarbon _ 3 => 24
  | .porphyrinMesoCarbon _ 0 => 34
  | .porphyrinMesoCarbon _ site => 50 + site
  | .porphyrinPyrroleCarbon _ pyrrole position =>
      porphyrinPyrroleBase pyrrole + position
  | .porphyrinNitrogen _ pyrrole => 100 + pyrrole
  | .porphyrinZinc _ => 110
  | .arylRingCarbon _ aryl position => 200 + 20 * aryl + position
  | .arylTertButylCenter _ aryl ringPosition =>
      400 + 100 * aryl + 10 * ringPosition
  | .arylTertButylMethyl _ aryl ringPosition branch =>
      700 + 100 * aryl + 10 * ringPosition + branch
  | .mesoBromine _ site => 850 + 10 * site
  | .ethynylCarbon unit site position =>
      if d.cyclicCoupled && unit ≠ 0 && site = 1 then
        if position = 1 then 1 else 2
      else 850 + 10 * site + position
  | _ => 0

def porphyrinAtomRank (d : PorphyrinDescriptor) : AtomId → ℕ
  | .heavy id =>
      10000 * porphyrinHeavyUnit id + porphyrinHeavyLocalRank d id
  | .hydrogen parent position =>
      10000 * porphyrinHeavyUnit parent + 2000 +
        10 * porphyrinHeavyLocalRank d parent + position

def porphyrinParent (d : PorphyrinDescriptor) : AtomId → Option AtomId
  | .hydrogen parent _ => some (.heavy parent)
  | .heavy (.porphyrinMesoCarbon unit 1) =>
      if unit = 0 then none
      else if d.cyclicCoupled then
        some (.heavy (.ethynylCarbon unit 1 0))
      else none
  | .heavy (.porphyrinMesoCarbon unit 2) =>
      some (.heavy (.porphyrinPyrroleCarbon unit 2 3))
  | .heavy (.porphyrinMesoCarbon unit 3) =>
      some (.heavy (.porphyrinPyrroleCarbon unit 3 3))
  | .heavy (.porphyrinMesoCarbon unit 0) =>
      some (.heavy (.porphyrinPyrroleCarbon unit 0 3))
  | .heavy (.porphyrinMesoCarbon _ _) => none
  | .heavy (.porphyrinPyrroleCarbon unit pyrrole 0) =>
      match pyrrole with
      | 2 => some (.heavy (.porphyrinMesoCarbon unit 1))
      | 3 => some (.heavy (.porphyrinMesoCarbon unit 2))
      | 0 => some (.heavy (.porphyrinMesoCarbon unit 3))
      | 1 => some (.heavy (.porphyrinMesoCarbon unit 0))
      | _ => none
  | .heavy (.porphyrinPyrroleCarbon unit pyrrole (position + 1)) =>
      some (.heavy (.porphyrinPyrroleCarbon unit pyrrole position))
  | .heavy (.porphyrinNitrogen unit pyrrole) =>
      some (.heavy (.porphyrinPyrroleCarbon unit pyrrole 0))
  | .heavy (.porphyrinZinc unit) =>
      some (.heavy (.porphyrinNitrogen unit 0))
  | .heavy (.arylRingCarbon unit aryl 0) =>
      some (.heavy (.porphyrinMesoCarbon unit
        (d.mesoArylSites.getD aryl 0)))
  | .heavy (.arylRingCarbon unit aryl (position + 1)) =>
      some (.heavy (.arylRingCarbon unit aryl position))
  | .heavy (.arylTertButylCenter unit aryl ringPosition) =>
      some (.heavy (.arylRingCarbon unit aryl ringPosition))
  | .heavy (.arylTertButylMethyl unit aryl ringPosition _) =>
      some (.heavy (.arylTertButylCenter unit aryl ringPosition))
  | .heavy (.mesoBromine unit site) =>
      some (.heavy (.porphyrinMesoCarbon unit site))
  | .heavy (.ethynylCarbon unit site position) =>
      if d.cyclicCoupled && unit ≠ 0 && site = 1 then
        if position = 0 then
          some (.heavy (.ethynylCarbon unit site 1))
        else if position = 1 then
          some (.heavy (.ethynylCarbon (unit - 1) 3 1))
        else none
      else if position = 0 then
        some (.heavy (.porphyrinMesoCarbon unit site))
      else
        some (.heavy (.ethynylCarbon unit site (position - 1)))
  | _ => none

def porphyrinParentScheme (d : PorphyrinDescriptor) : RootedParentScheme :=
  { root := .heavy (.porphyrinMesoCarbon 0 1)
    parent := porphyrinParent d
    rank := porphyrinAtomRank d }

/-! ## Requested atom-and-bond carriers and formula cross-checks -/

def structureM : MolecularStructure := candidateMDescriptor.toHeavyGraph.expand
def structureN : MolecularStructure := candidateNDescriptor.toHeavyGraph.expand
def structureO : MolecularStructure := candidateODescriptor.toHeavyGraph.expand
def structureP : MolecularStructure := candidatePDescriptor.toHeavyGraph.expand
def structureQ : MolecularStructure := candidateQDescriptor.toHeavyGraph.expand
def structureR : MolecularStructure := candidateRDescriptor.toHeavyGraph.expand

def formulaM : MolecularFormula :=
  { carbon := 15, hydrogen := 24, nitrogen := 0, oxygen := 0
    silicon := 0, bromine := 0, zinc := 0 }

def formulaN : MolecularFormula :=
  { carbon := 15, hydrogen := 22, nitrogen := 0, oxygen := 1
    silicon := 0, bromine := 0, zinc := 0 }

def formulaO : MolecularFormula :=
  { carbon := 48, hydrogen := 52, nitrogen := 4, oxygen := 0
    silicon := 0, bromine := 0, zinc := 1 }

def formulaQ : MolecularFormula :=
  { carbon := 48, hydrogen := 50, nitrogen := 4, oxygen := 0
    silicon := 0, bromine := 2, zinc := 1 }

def formulaR : MolecularFormula :=
  { carbon := 52, hydrogen := 52, nitrogen := 4, oxygen := 0
    silicon := 0, bromine := 0, zinc := 1 }

def formulaP : MolecularFormula :=
  { carbon := 312, hydrogen := 300, nitrogen := 24, oxygen := 0
    silicon := 0, bromine := 0, zinc := 6 }

inductive ComponentRole
  | core
  | repeatUnit
  | linker
  | substituent
  | terminalGroup
  | guest
  | leavingGroup
  deriving DecidableEq, Repr

structure ComponentLedgerEntry where
  sourceLocalLabel : String
  formula : MolecularFormula
  multiplicity : ℕ
  role : ComponentRole
  deriving DecidableEq, Repr

def coupledPorphyrinCoreFormula : MolecularFormula :=
  { carbon := 20, hydrogen := 8, nitrogen := 4, oxygen := 0
    silicon := 0, bromine := 0, zinc := 1 }

def arylSubstituentFormula : MolecularFormula :=
  { carbon := 14, hydrogen := 21, nitrogen := 0, oxygen := 0
    silicon := 0, bromine := 0, zinc := 0 }

def butadiyneLinkFormula : MolecularFormula :=
  { carbon := 4, hydrogen := 0, nitrogen := 0, oxygen := 0
    silicon := 0, bromine := 0, zinc := 0 }

/-- Visual component recount of the de-threaded page-4 product.  The central
hexapyridyl template in the boxed precursor is a guest and is absent from the
left-hand `P6` drawing after DABCO treatment. -/
def p6ComponentLedger : List ComponentLedgerEntry :=
  [ { sourceLocalLabel := "Zn porphyrin core", formula := coupledPorphyrinCoreFormula
      multiplicity := 6, role := .repeatUnit }
  , { sourceLocalLabel := "3,5-di-tert-butylphenyl (Ar)"
      formula := arylSubstituentFormula, multiplicity := 12, role := .substituent }
  , { sourceLocalLabel := "butadiyne link", formula := butadiyneLinkFormula
      multiplicity := 6, role := .linker } ]

def p6RecombinedFormula : MolecularFormula :=
  MolecularFormula.add
    (MolecularFormula.scale 6 coupledPorphyrinCoreFormula)
    (MolecularFormula.add
      (MolecularFormula.scale 12 arylSubstituentFormula)
      (MolecularFormula.scale 6 butadiyneLinkFormula))

def P6AssemblyAccounting : Prop :=
  p6ComponentLedger.length = 3 ∧
    (∀ entry ∈ p6ComponentLedger, 0 < entry.multiplicity) ∧
    p6RecombinedFormula = formulaP ∧
    candidatePDescriptor.couplingBonds.length = 6 ∧
    candidatePDescriptor.unitCount = sourceTemplateBindingSiteCount

/-! ## Exact page-4 source arrows -/

inductive SpeciesLabel
  | toluene
  | m
  | n
  | o
  | q
  | r
  | sixSiteTemplate
  | templatedP6
  | p6
  deriving DecidableEq, Repr

inductive Reagent
  | tertButylChloride (equivalents : ℕ)
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
  | dabco
  deriving DecidableEq, Repr

inductive TransformationUse
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

inductive SourceLocator
  | page4SynthesisScheme
  | page4P6RepeatDrawing
  | page3PreviousPartScheme
  deriving DecidableEq, Repr

structure SourceArrow where
  reactants : List SpeciesLabel
  products : List SpeciesLabel
  reagents : List Reagent
  transformationUse : TransformationUse
  locator : SourceLocator
  deriving DecidableEq, Repr

def sourceArrows : List SourceArrow :=
  [ { reactants := [.toluene], products := [.m]
      reagents := [.tertButylChloride 2, .aluminumChloride]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.m], products := [.n]
      reagents := [.nbs, .benzoylPeroxide, .hmta, .hydrochloricAcid, .water]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.n], products := [.o]
      reagents := [.dipyrromethane, .trifluoroaceticAcid, .ddq, .zincAcetate]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.o], products := [.q]
      reagents := [.nbs]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.q], products := [.r]
      reagents := [.palladiumZero, .triphenylphosphine, .copperIodide,
        .trihexylsilylacetylene, .tetrabutylammoniumFluoride]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.r, .sixSiteTemplate], products := [.templatedP6]
      reagents := [.paraBenzoquinone, .palladiumDichloride,
        .triphenylphosphine, .copperIodide]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4SynthesisScheme }
  , { reactants := [.templatedP6], products := [.p6]
      reagents := [.dabco]
      transformationUse := .qualitativeNamedTransformOnly
      locator := .page4P6RepeatDrawing } ]

def SourceSchemeBound : Prop :=
  sourceArrows.length = 7 ∧
    ∀ arrow ∈ sourceArrows,
      arrow.transformationUse = .qualitativeNamedTransformOnly

/-! ## Inline, problem-only handling of the declared A5 prerequisite

Part A5 is not chemically consumed by any A6 transformation.  Nevertheless,
the dependency policy is made explicit by independently transcribing its
page-3 chain descriptors here; no theorem or answer file from A5 is imported.
-/

inductive A5RingKind
  | benzene
  | cyclohexa25Diene
  deriving DecidableEq, Repr

inductive A5OxygenKind
  | hydroxyl
  | carbonyl
  | tbsEther
  | tesEther
  deriving DecidableEq, Repr

structure A5OxygenSite where
  slot : ℕ
  ring : ℕ
  position : ℕ
  kind : A5OxygenKind
  deriving DecidableEq, Repr

structure A5BromineSite where
  slot : ℕ
  ring : ℕ
  position : ℕ
  deriving DecidableEq, Repr

/-- Consecutive rings are joined para-to-para; `closed` adds the last-to-first
bond.  Oxygen and bromine attachment sites are explicit. -/
structure A5Descriptor where
  rings : List A5RingKind
  closed : Bool
  bromines : List A5BromineSite
  oxygens : List A5OxygenSite
  deriving DecidableEq, Repr

def a5O (slot ring position : ℕ) (kind : A5OxygenKind) : A5OxygenSite :=
  { slot := slot, ring := ring, position := position, kind := kind }

def a5Br (slot ring position : ℕ) : A5BromineSite :=
  { slot := slot, ring := ring, position := position }

def a5StartingMaterial : A5Descriptor :=
  { rings := [.benzene, .cyclohexa25Diene], closed := false
    bromines := [a5Br 0 0 0]
    oxygens := [a5O 0 1 0 .hydroxyl, a5O 1 1 3 .carbonyl] }

def a5BiphenylOTBSFragment : A5Descriptor :=
  { rings := [.benzene, .benzene], closed := false, bromines := []
    oxygens := [a5O 0 1 3 .tbsEther] }

def a5ParaBromophenylFragment : A5Descriptor :=
  { rings := [.benzene], closed := false
    bromines := [a5Br 0 0 3], oxygens := [] }

def shiftA5O (ringOffset slotOffset : ℕ) (site : A5OxygenSite) : A5OxygenSite :=
  { site with ring := site.ring + ringOffset, slot := site.slot + slotOffset }

def shiftA5Br (ringOffset slotOffset : ℕ) (site : A5BromineSite) : A5BromineSite :=
  { site with ring := site.ring + ringOffset, slot := site.slot + slotOffset }

def a5CarbonylAddition (substrate fragment : A5Descriptor) : A5Descriptor :=
  let terminalRing := substrate.rings.length - 1
  let changed := substrate.oxygens.map fun site =>
    if site.ring = terminalRing ∧ site.position = 3 ∧ site.kind = .carbonyl then
      { site with kind := .hydroxyl }
    else site
  { rings := substrate.rings ++ fragment.rings
    closed := false
    bromines := substrate.bromines ++
      fragment.bromines.map
        (shiftA5Br substrate.rings.length substrate.bromines.length)
    oxygens := changed ++
      fragment.oxygens.map
        (shiftA5O substrate.rings.length substrate.oxygens.length) }

def a5ProtectTES (d : A5Descriptor) : A5Descriptor :=
  { d with oxygens := d.oxygens.map fun site =>
      if site.kind = .hydroxyl then { site with kind := .tesEther } else site }

def a5CleaveTBS (d : A5Descriptor) : A5Descriptor :=
  { d with oxygens := d.oxygens.map fun site =>
      if site.kind = .tbsEther then { site with kind := .hydroxyl } else site }

def a5DearomatizeLast : List A5RingKind → List A5RingKind
  | [] => []
  | [_] => [.cyclohexa25Diene]
  | kind :: rest => kind :: a5DearomatizeLast rest

def a5OxidativeDearomatization (d : A5Descriptor) : A5Descriptor :=
  let terminalRing := d.rings.length - 1
  let changed := d.oxygens.map fun site =>
    if site.ring = terminalRing ∧ site.position = 3 ∧ site.kind = .hydroxyl then
      { site with kind := .carbonyl }
    else site
  { d with
    rings := a5DearomatizeLast d.rings
    oxygens := changed ++ [a5O d.oxygens.length terminalRing 0 .hydroxyl] }

def a5CloseRing (d : A5Descriptor) : A5Descriptor :=
  { d with closed := true, bromines := [] }

def a5F : A5Descriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .benzene]
    closed := false, bromines := [a5Br 0 0 0]
    oxygens := [a5O 0 1 0 .hydroxyl, a5O 1 1 3 .hydroxyl,
      a5O 2 3 3 .tbsEther] }

def a5G : A5Descriptor :=
  { rings := a5F.rings, closed := false, bromines := a5F.bromines
    oxygens := [a5O 0 1 0 .tesEther, a5O 1 1 3 .tesEther,
      a5O 2 3 3 .tbsEther] }

def a5H : A5Descriptor :=
  { rings := a5G.rings, closed := false, bromines := a5G.bromines
    oxygens := [a5O 0 1 0 .tesEther, a5O 1 1 3 .tesEther,
      a5O 2 3 3 .hydroxyl] }

def a5I : A5Descriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene, .cyclohexa25Diene]
    closed := false, bromines := [a5Br 0 0 0]
    oxygens := [a5O 0 1 0 .tesEther, a5O 1 1 3 .tesEther,
      a5O 2 3 3 .carbonyl, a5O 3 3 0 .hydroxyl] }

def a5J : A5Descriptor :=
  { rings := [.benzene, .cyclohexa25Diene, .benzene,
      .cyclohexa25Diene, .benzene]
    closed := false, bromines := [a5Br 0 0 0, a5Br 1 4 3]
    oxygens := [a5O 0 1 0 .tesEther, a5O 1 1 3 .tesEther,
      a5O 2 3 3 .hydroxyl, a5O 3 3 0 .hydroxyl] }

def a5K : A5Descriptor :=
  { rings := a5J.rings, closed := false, bromines := a5J.bromines
    oxygens := [a5O 0 1 0 .tesEther, a5O 1 1 3 .tesEther,
      a5O 2 3 3 .tesEther, a5O 3 3 0 .tesEther] }

def a5L : A5Descriptor :=
  { rings := a5K.rings, closed := true, bromines := []
    oxygens := a5K.oxygens }

def PreviousPartA5Result : Prop :=
  a5CarbonylAddition a5StartingMaterial a5BiphenylOTBSFragment = a5F ∧
    a5ProtectTES a5F = a5G ∧
    a5CleaveTBS a5G = a5H ∧
    a5OxidativeDearomatization a5H = a5I ∧
    a5CarbonylAddition a5I a5ParaBromophenylFragment = a5J ∧
    a5ProtectTES a5J = a5K ∧
    a5CloseRing a5K = a5L

/-! ## Assumption/target split and requested specifications

There are no theorem hypotheses containing an answer.  `SourceSchemeBound`,
the finite M regioisomer domain, `page4MObservation`, the source-scoped
`geuze1956DiTertButylation` constitution record, the six-site template count,
and the inline A5 transcription are the problem-side data.  The following
propositions are the six output targets.  Every transformation is used only as
a qualitative forward compatibility constraint; no yield, completion, or
omitted-stream claim is made.
-/

def StructureMResult : Prop :=
  MConstitutionScopeAudit ∧
    MSourceConstraints candidateMDescriptor ∧
    CandidateChecks candidateMDescriptor.toHeavyGraph formulaM

def StructureNResult : Prop :=
  benzylicBrominationSommelet candidateMDescriptor = candidateNDescriptor ∧
    CandidateChecks candidateNDescriptor.toHeavyGraph formulaN

def StructureOResult : Prop :=
  porphyrinFromAldehyde candidateNDescriptor = candidateODescriptor ∧
    CandidateChecks candidateODescriptor.toHeavyGraph formulaO

def StructureQResult : Prop :=
  brominateFreeMesoSites candidateODescriptor = candidateQDescriptor ∧
    CandidateChecks candidateQDescriptor.toHeavyGraph formulaQ

def StructureRResult : Prop :=
  sonogashiraThenDesilylate candidateQDescriptor = candidateRDescriptor ∧
    CandidateChecks candidateRDescriptor.toHeavyGraph formulaR

def StructurePResult : Prop :=
  macrocyclizeWithTemplate sourceTemplateBindingSiteCount candidateRDescriptor =
      candidatePDescriptor ∧
    CandidateChecks candidatePDescriptor.toHeavyGraph formulaP ∧
    P6AssemblyAccounting

/-- One theorem carrier for each requested output. -/
theorem structure_m : StructureMResult := by
  refine ⟨?_, ?_, ?_⟩
  · unfold MConstitutionScopeAudit
    native_decide
  · refine ⟨{ first := 2, second := 4 }, ?_, ?_, ?_, ?_⟩
    · native_decide
    · native_decide
    · native_decide
    · unfold MConstitutionBridge MConstitutionScopeAudit
      native_decide
  · apply candidateChecks_of_finite_certificates
      (scheme := areneParentScheme)
    · unfold MolecularStructure.FiniteAudit
      native_decide
    · unfold MolecularStructure.ValidParentScheme
      native_decide

theorem structure_n : StructureNResult := by
  refine ⟨by native_decide, ?_⟩
  apply candidateChecks_of_finite_certificates
    (scheme := areneParentScheme)
  · unfold MolecularStructure.FiniteAudit
    native_decide
  · unfold MolecularStructure.ValidParentScheme
    native_decide

theorem structure_o : StructureOResult := by
  refine ⟨by native_decide, ?_⟩
  apply candidateChecks_of_finite_certificates
    (scheme := porphyrinParentScheme candidateODescriptor)
  · unfold MolecularStructure.FiniteAudit
    native_decide
  · unfold MolecularStructure.ValidParentScheme
    native_decide

theorem structure_p : StructurePResult := by
  refine ⟨by native_decide, ?_, ?_⟩
  apply candidateChecks_of_finite_certificates
    (scheme := porphyrinParentScheme candidatePDescriptor)
  · unfold MolecularStructure.FiniteAudit
    native_decide
  · unfold MolecularStructure.ValidParentScheme
    native_decide
  · unfold P6AssemblyAccounting
    native_decide

theorem structure_q : StructureQResult := by
  refine ⟨by native_decide, ?_⟩
  apply candidateChecks_of_finite_certificates
    (scheme := porphyrinParentScheme candidateQDescriptor)
  · unfold MolecularStructure.FiniteAudit
    native_decide
  · unfold MolecularStructure.ValidParentScheme
    native_decide

theorem structure_r : StructureRResult := by
  refine ⟨by native_decide, ?_⟩
  apply candidateChecks_of_finite_certificates
    (scheme := porphyrinParentScheme candidateRDescriptor)
  · unfold MolecularStructure.FiniteAudit
    native_decide
  · unfold MolecularStructure.ValidParentScheme
    native_decide

theorem previous_part_a5_result : PreviousPartA5Result := by
  unfold PreviousPartA5Result
  native_decide

theorem source_scheme_bound : SourceSchemeBound := by
  unfold SourceSchemeBound
  constructor
  · native_decide
  · intro arrow harrow
    simp only [sourceArrows, List.mem_cons, List.not_mem_nil, or_false] at harrow
    rcases harrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Raw solve-phase symbolic contract, in requested output order. -/
def RawResult : Prop :=
  PreviousPartA5Result ∧
    SourceSchemeBound ∧
    StructureMResult ∧
    StructureNResult ∧
    StructureOResult ∧
    StructurePResult ∧
    StructureQResult ∧
    StructureRResult

/-- Exact-symbolic reporting preserves every atom-and-bond carrier. -/
def ReportedResult : Prop :=
  StructureMResult ∧
    StructureNResult ∧
    StructureOResult ∧
    StructurePResult ∧
    StructureQResult ∧
    StructureRResult ∧
    SourceSchemeBound ∧
    PreviousPartA5Result

/- The two literal payload digests are filled from the solve artifact by the
trusted pipeline helper; their equalities prevent detaching these theorems from
that exact symbolic submission. -/
theorem raw_result :
    ("0dea269e03ada0397d55734fea67b863dd4a6f3b1e39710a024ae2a38f8e4d3f" : String) =
      "0dea269e03ada0397d55734fea67b863dd4a6f3b1e39710a024ae2a38f8e4d3f" ∧
      RawResult := by
  refine ⟨rfl, ?_⟩
  exact ⟨previous_part_a5_result, source_scheme_bound, structure_m,
    structure_n, structure_o, structure_p, structure_q, structure_r⟩

theorem reported_result :
    ("3edc61bd2514e4debfbd1c2de4521ad3f8a3960ef5e6bb529dd1f84e11933f23" : String) =
      "3edc61bd2514e4debfbd1c2de4521ad3f8a3960ef5e6bb529dd1f84e11933f23" ∧
      ReportedResult := by
  refine ⟨rfl, ?_⟩
  exact ⟨structure_m, structure_n, structure_o, structure_p, structure_q,
    structure_r, source_scheme_bound, previous_part_a5_result⟩

end IChO2026Problems.Icho2026T6A6
