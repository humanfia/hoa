import IChO2026Chem

/-!
# IChO 2026, problem 1.2

This file formalizes the identification of compound `Z` and the requested
structures of `A` and `B`.  The molecular structures below are all-atom
labelled graphs: hydrogens, bond labels, formal charges, radical counts, and
tetrahedral-stereochemistry fields are explicit.  The source drawing of `Z`
retains its displayed Kekule form.  The aromatic structures `A` and `B` use a
resonance-invariant aromatic bond label together with an explicit obligation
that a closed-shell Kekule localization exists.  Molecular symmetries therefore
act on the delocalized structure, rather than on an arbitrary localized drawing.

The chlorination statement is used quantitatively only through the finite
molecular ledger

`Z + k Cl₂ ⟶ chlorinated Z + k HCl`.

It does not assert a bulk yield, a sole product, a phase, or a mechanism.  The
thermal conversion is represented separately as a qualitative named transform.
-/

namespace IChO2026Problems.IChO2026T1A2

/-! ## Formulae and the source table -/

/-- Elements needed for the source table and the chlorine isotope audit. -/
inductive ChemicalElement
  | carbon
  | hydrogen
  | oxygen
  | chlorine
  deriving DecidableEq, Fintype, Repr

/-- A neutral molecular formula over the elements used in this subproblem. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  chlorine : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

/-- Addition of molecular-formula atom ledgers. -/
def add (f g : MolecularFormula) : MolecularFormula where
  carbon := f.carbon + g.carbon
  hydrogen := f.hydrogen + g.hydrogen
  oxygen := f.oxygen + g.oxygen
  chlorine := f.chlorine + g.chlorine

/-- Multiplication of a molecular-formula ledger by a stoichiometric coefficient. -/
def scale (n : ℕ) (f : MolecularFormula) : MolecularFormula where
  carbon := n * f.carbon
  hydrogen := n * f.hydrogen
  oxygen := n * f.oxygen
  chlorine := n * f.chlorine

/-- Nominal mass using the light isotopes relevant to the `m/z = 218` peak. -/
def nominalMass35 (f : MolecularFormula) : ℕ :=
  12 * f.carbon + f.hydrogen + 16 * f.oxygen + 35 * f.chlorine

end MolecularFormula

/-- The ten distinct numbered compounds visible in the table on source page 2. -/
inductive TableCompound
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | ten
  deriving DecidableEq, Fintype, Repr

/-- Formula labels transcribed from all ten distinct panels of the source table. -/
def tableFormula : TableCompound → MolecularFormula
  | .one => ⟨11, 14, 3, 0⟩
  | .two => ⟨10, 18, 1, 0⟩
  | .three => ⟨10, 18, 1, 0⟩
  | .four => ⟨6, 12, 1, 0⟩
  | .five => ⟨10, 12, 2, 0⟩
  | .six => ⟨10, 18, 1, 0⟩
  | .seven => ⟨14, 16, 0, 0⟩
  | .eight => ⟨15, 24, 0, 0⟩
  | .nine => ⟨10, 16, 1, 0⟩
  | .ten => ⟨10, 18, 1, 0⟩

/-- The finite identification domain comes from the complete numbered table,
not from a candidate-named singleton. -/
def tableCandidateDomain : Finset TableCompound := Finset.univ

/-! ## Explicit molecular graphs -/

inductive TetrahedralStereo
  | notStereogenic
  | clockwise
  | anticlockwise
  | unspecified
  deriving DecidableEq, Repr

inductive BondOrder
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr

/-- A stable natural-number code for comparing exact bond labels.  This is not
an arithmetic valence for an aromatic bond. -/
def BondOrder.code : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 4

/-- Integral bond orders available in one localized Kekule representative. -/
inductive LocalizedBondOrder
  | single
  | double
  | triple
  deriving DecidableEq, Repr

def LocalizedBondOrder.valence : LocalizedBondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

/-- Which localized bond orders are represented by a graph bond label. -/
def BondOrder.AllowsLocalization : BondOrder → LocalizedBondOrder → Prop
  | .single, localized => localized = .single
  | .double, localized => localized = .double
  | .triple, localized => localized = .triple
  | .aromatic, localized => localized = .single ∨ localized = .double

/-- Every atom carries the electronic and stereochemical fields requested by
the structure-drawing contract. -/
structure AtomSpec where
  element : ChemicalElement
  formalCharge : ℤ
  radicalElectrons : ℕ
  tetrahedralStereo : TetrahedralStereo
  deriving DecidableEq, Repr

def neutralClosedShellAtom (e : ChemicalElement) : AtomSpec where
  element := e
  formalCharge := 0
  radicalElectrons := 0
  tetrahedralStereo := .notStereogenic

structure Bond (n : ℕ) where
  first : Fin n
  second : Fin n
  order : BondOrder
  deriving DecidableEq, Repr

/-- A finite labelled molecular graph.  Bonds are listed once, rather than as
both orientations. -/
structure MolecularGraph where
  atomCount : ℕ
  atom : Fin atomCount → AtomSpec
  bonds : List (Bond atomCount)

private def mkBond {n : ℕ} (i j : Fin n) (order : BondOrder) : Bond n :=
  ⟨i, j, order⟩

def Bond.sameUndirected {n : ℕ} (b c : Bond n) : Prop :=
  (b.first = c.first ∧ b.second = c.second) ∨
    (b.first = c.second ∧ b.second = c.first)

def MolecularGraph.bondLabelCodeBetween
    (m : MolecularGraph) (i j : Fin m.atomCount) : ℕ :=
  m.bonds.foldl
    (fun total b =>
      if (b.first = i ∧ b.second = j) ∨ (b.first = j ∧ b.second = i) then
        total + b.order.code
      else total)
    0

def MolecularGraph.adjacent
    (m : MolecularGraph) (i j : Fin m.atomCount) : Prop :=
  0 < m.bondLabelCodeBetween i j

/-! A localization assigns an integral order to every listed bond.  Fixed
single/double/triple labels must remain fixed; an aromatic label may be either
single or double in the chosen resonance representative. -/
structure KekuleLocalization (m : MolecularGraph) where
  localizedOrder : Bond m.atomCount → LocalizedBondOrder
  compatible : ∀ b ∈ m.bonds, b.order.AllowsLocalization (localizedOrder b)

def MolecularGraph.bondValenceAtUnder
    (m : MolecularGraph) (localization : KekuleLocalization m)
    (i : Fin m.atomCount) : ℕ :=
  m.bonds.foldl
    (fun total b =>
      if b.first = i ∨ b.second = i then
        total + (localization.localizedOrder b).valence
      else total)
    0

def ChemicalElement.closedShellValence : ChemicalElement → ℕ
  | .carbon => 4
  | .hydrogen => 1
  | .oxygen => 2
  | .chlorine => 1

def MolecularGraph.countElement (m : MolecularGraph) (e : ChemicalElement) : ℕ :=
  (Finset.univ.filter (fun i => (m.atom i).element = e)).card

def MolecularGraph.formula (m : MolecularGraph) : MolecularFormula where
  carbon := m.countElement .carbon
  hydrogen := m.countElement .hydrogen
  oxygen := m.countElement .oxygen
  chlorine := m.countElement .chlorine

def MolecularGraph.connected (m : MolecularGraph) : Prop :=
  ∀ i j, Relation.ReflTransGen m.adjacent i j

/-- The delocalized bond labels admit at least one ordinary closed-shell
single/double/triple localization. -/
def MolecularGraph.AdmitsClosedShellKekuleLocalization
    (m : MolecularGraph) : Prop :=
  ∃ localization : KekuleLocalization m,
    ∀ i, m.bondValenceAtUnder localization i =
      (m.atom i).element.closedShellValence

/-- Structural well-formedness checks neutrality, closed shells, non-looping
bonds, absence of duplicate undirected bonds, a chemically admissible Kekule
localization with ordinary valence, and connectedness. -/
def MolecularGraph.WellFormed (m : MolecularGraph) : Prop :=
  (∀ i, (m.atom i).formalCharge = 0 ∧ (m.atom i).radicalElectrons = 0) ∧
  (∀ b ∈ m.bonds, b.first ≠ b.second) ∧
  m.bonds.Pairwise (fun b c => ¬ b.sameUndirected c) ∧
  m.AdmitsClosedShellKekuleLocalization ∧
  m.connected

/-- Azulene with resonance-invariant aromatic carbon-carbon bonds.  Carbon
vertices are `0`--`9`, and hydrogen vertices are `10`--`17`.  The rings are
`0-1-2-3-4-0` and `3-5-6-7-8-9-4-3`. -/
def azulene : MolecularGraph where
  atomCount := 18
  atom := fun i =>
    if i.val < 10 then neutralClosedShellAtom .carbon
    else neutralClosedShellAtom .hydrogen
  bonds :=
    [ mkBond 0 1 .aromatic, mkBond 1 2 .aromatic, mkBond 2 3 .aromatic,
      mkBond 3 4 .aromatic, mkBond 4 0 .aromatic,
      mkBond 3 5 .aromatic, mkBond 5 6 .aromatic, mkBond 6 7 .aromatic,
      mkBond 7 8 .aromatic, mkBond 8 9 .aromatic, mkBond 9 4 .aromatic,
      mkBond 0 10 .single, mkBond 1 11 .single, mkBond 2 12 .single,
      mkBond 5 13 .single, mkBond 6 14 .single, mkBond 7 15 .single,
      mkBond 8 16 .single, mkBond 9 17 .single ]

/-- Naphthalene with resonance-invariant aromatic carbon-carbon bonds.  Carbon
vertices are `0`--`9`, and hydrogen vertices are `10`--`17`.  The rings are
`0-1-2-3-4-5-0` and `4-6-7-8-9-5-4`. -/
def naphthalene : MolecularGraph where
  atomCount := 18
  atom := fun i =>
    if i.val < 10 then neutralClosedShellAtom .carbon
    else neutralClosedShellAtom .hydrogen
  bonds :=
    [ mkBond 0 1 .aromatic, mkBond 1 2 .aromatic, mkBond 2 3 .aromatic,
      mkBond 3 4 .aromatic, mkBond 4 5 .aromatic, mkBond 5 0 .aromatic,
      mkBond 4 6 .aromatic, mkBond 6 7 .aromatic, mkBond 7 8 .aromatic,
      mkBond 8 9 .aromatic, mkBond 9 5 .aromatic,
      mkBond 0 10 .single, mkBond 1 11 .single, mkBond 2 12 .single,
      mkBond 3 13 .single, mkBond 6 14 .single, mkBond 7 15 .single,
      mkBond 8 16 .single, mkBond 9 17 .single ]

/-- Compound 7 from the source image: the azulene core has methyl groups at
locants 1 and 4 and an ethyl group at locant 7.  Carbon vertices are `0`--`13`;
all sixteen hydrogen vertices `14`--`29` are explicit. -/
def chamazulene : MolecularGraph where
  atomCount := 30
  atom := fun i =>
    if i.val < 14 then neutralClosedShellAtom .carbon
    else neutralClosedShellAtom .hydrogen
  bonds :=
    [ mkBond 0 1 .double, mkBond 1 2 .single, mkBond 2 3 .double,
      mkBond 3 4 .single, mkBond 4 0 .single,
      mkBond 3 5 .single, mkBond 5 6 .double, mkBond 6 7 .single,
      mkBond 7 8 .double, mkBond 8 9 .single, mkBond 9 4 .double,
      mkBond 0 10 .single, mkBond 5 11 .single,
      mkBond 8 12 .single, mkBond 12 13 .single,
      mkBond 1 14 .single, mkBond 2 15 .single, mkBond 6 16 .single,
      mkBond 7 17 .single, mkBond 9 18 .single,
      mkBond 10 19 .single, mkBond 10 20 .single, mkBond 10 21 .single,
      mkBond 11 22 .single, mkBond 11 23 .single, mkBond 11 24 .single,
      mkBond 12 25 .single, mkBond 12 26 .single,
      mkBond 13 27 .single, mkBond 13 28 .single, mkBond 13 29 .single ]

/-! ## Nontrivial topology, substituent, and symmetry carriers -/

def cyclicSucc {k : ℕ} (positive : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ positive⟩

structure RingCycle (m : MolecularGraph) (k : ℕ) where
  positive : 0 < k
  atomAt : Fin k → Fin m.atomCount
  injective : Function.Injective atomAt
  adjacentNext : ∀ i, m.adjacent (atomAt i) (atomAt (cyclicSucc positive i))

def RingCycle.vertexSet {m : MolecularGraph} {k : ℕ} (c : RingCycle m k) :
    Finset (Fin m.atomCount) :=
  Finset.univ.image c.atomAt

/-- Two cycles fused along exactly one edge (two common adjacent atoms). -/
def HasFusedRings (m : MolecularGraph) (k l : ℕ) : Prop :=
  ∃ c₁ : RingCycle m k, ∃ c₂ : RingCycle m l,
    (c₁.vertexSet ∩ c₂.vertexSet).card = 2 ∧
    ∃ i, i ∈ c₁.vertexSet ∩ c₂.vertexSet ∧
      ∃ j, j ∈ c₁.vertexSet ∩ c₂.vertexSet ∧ i ≠ j ∧ m.adjacent i j

/-- A graph-level 10-π Kekulé carrier: a simple perimeter cycle with strictly
alternating double and single bonds. -/
def HasAlternatingCycle (m : MolecularGraph) (k : ℕ) : Prop :=
  ∃ c : RingCycle m k, ∀ i,
    m.bondLabelCodeBetween (c.atomAt i) (c.atomAt (cyclicSucc c.positive i)) =
      if i.val % 2 = 0 then 2 else 1

/-- A simple cycle whose carbon-carbon edges all carry the
resonance-invariant aromatic label.  Closed-shell feasibility is supplied
separately by `MolecularGraph.AdmitsClosedShellKekuleLocalization`. -/
def HasAromaticCycle (m : MolecularGraph) (k : ℕ) : Prop :=
  ∃ c : RingCycle m k, ∀ i,
    m.bondLabelCodeBetween (c.atomAt i) (c.atomAt (cyclicSucc c.positive i)) =
      BondOrder.aromatic.code

inductive CoordinateAxis
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Exact coordinates used only to certify spatial symmetry. -/
structure Point3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

def Point3.reflect : CoordinateAxis → Point3 → Point3
  | .x, p => ⟨-p.x, p.y, p.z⟩
  | .y, p => ⟨p.x, -p.y, p.z⟩
  | .z, p => ⟨p.x, p.y, -p.z⟩

/-- Vanishing cross product for the displacement vectors from `p`. -/
def Point3.collinear (p q r : Point3) : Prop :=
  (q.y - p.y) * (r.z - p.z) = (q.z - p.z) * (r.y - p.y) ∧
  (q.z - p.z) * (r.x - p.x) = (q.x - p.x) * (r.z - p.z) ∧
  (q.x - p.x) * (r.y - p.y) = (q.y - p.y) * (r.x - p.x)

/-- A nondegenerate placement of all nuclei.  Noncollinearity prevents several
coordinate planes from being manufactured by placing every atom on their
common line. -/
structure SpatialRealization (m : MolecularGraph) where
  position : Fin m.atomCount → Point3
  injective : Function.Injective position
  noncollinear : ∃ i j k,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ¬ Point3.collinear (position i) (position j) (position k)

/-- An idealized molecular mirror plane.  Its normal is one of an orthogonal
coordinate basis, its atom action is an involutive labelled-graph
automorphism, and that action is tied to actual coordinate reflection.  An
identity atom action is permitted for the molecular plane because all nuclei
of these planar hydrocarbons lie in it. -/
structure MirrorPlane (m : MolecularGraph) (r : SpatialRealization m) where
  normalAxis : CoordinateAxis
  action : Equiv.Perm (Fin m.atomCount)
  involutive : ∀ i, action (action i) = i
  preservesAtom : ∀ i, m.atom (action i) = m.atom i
  preservesBondLabel : ∀ i j,
    m.bondLabelCodeBetween (action i) (action j) =
      m.bondLabelCodeBetween i j
  realizesReflection : ∀ i,
    r.position (action i) = Point3.reflect normalAxis (r.position i)

/-- Distinct coordinate-axis normals are pairwise perpendicular; the induced
atom actions must also be distinct, so a single trivial automorphism cannot be
counted repeatedly. -/
def HasMutuallyPerpendicularMirrorPlanes (m : MolecularGraph) (k : ℕ) : Prop :=
  ∃ realization : SpatialRealization m,
    ∃ planes : Fin k → MirrorPlane m realization,
      Function.Injective (fun i => (planes i).normalAxis) ∧
      Function.Injective (fun i => (planes i).action)

/-- A planar molecular realization is witnessed by a mirror plane whose
reflection fixes every atomic nucleus. -/
def HasPlanarRealization (m : MolecularGraph) : Prop :=
  ∃ realization : SpatialRealization m,
    ∃ plane : MirrorPlane m realization,
      plane.action = Equiv.refl (Fin m.atomCount)

def CarbonSite (m : MolecularGraph) :=
  {i : Fin m.atomCount // (m.atom i).element = .carbon}

/-- The graph-theoretic content of “is a derivative of”: an injective copy of
the complete carbon adjacency framework.  This intentionally compares
connectivity rather than one Kekule bond placement, because the base is stored
with aromatic labels while the source panel displays one localized form. -/
structure CarbonFrameworkEmbedding (base derivative : MolecularGraph) where
  toSite : CarbonSite base → CarbonSite derivative
  injective : Function.Injective toSite
  preservesCarbonAdjacency : ∀ i j,
    derivative.adjacent (toSite i).val (toSite j).val ↔
      base.adjacent i.val j.val

noncomputable def MolecularGraph.neighborsOfElement
    (m : MolecularGraph) (i : Fin m.atomCount) (e : ChemicalElement) :
    Finset (Fin m.atomCount) := by
  classical
  exact Finset.univ.filter (fun j => (m.atom j).element = e ∧ m.adjacent i j)

def IsMethylSubstituent
    (m : MolecularGraph) (core methyl : Fin m.atomCount) : Prop :=
  (m.atom core).element = .carbon ∧
  (m.atom methyl).element = .carbon ∧
  m.bondLabelCodeBetween core methyl = BondOrder.single.code ∧
  (m.neighborsOfElement methyl .hydrogen).card = 3 ∧
  m.neighborsOfElement methyl .carbon = {core}

def IsEthylSubstituent
    (m : MolecularGraph) (core alpha beta : Fin m.atomCount) : Prop :=
  (m.atom core).element = .carbon ∧
  (m.atom alpha).element = .carbon ∧
  (m.atom beta).element = .carbon ∧
  m.bondLabelCodeBetween core alpha = BondOrder.single.code ∧
  m.bondLabelCodeBetween alpha beta = BondOrder.single.code ∧
  (m.neighborsOfElement alpha .hydrogen).card = 2 ∧
  (m.neighborsOfElement beta .hydrogen).card = 3 ∧
  m.neighborsOfElement alpha .carbon = {core, beta} ∧
  m.neighborsOfElement beta .carbon = {alpha}

/-- The reducible atom-count projection is made explicit so that locant
indices below retain their checked `Fin 30` bounds. -/
def chamazuleneAtomIndex (i : Fin 30) : Fin chamazulene.atomCount := by
  simpa [chamazulene] using i

/-- Complete structure audit for the image's compound 7.  With the conventional
azulene numbering fixed in the graph comments, core vertices `0`, `5`, and `8`
are locants 1, 4, and 7 respectively. -/
def IsOneFourDimethylSevenEthylAzulene : Prop :=
  chamazulene.WellFormed ∧
  chamazulene.formula = ⟨14, 16, 0, 0⟩ ∧
  HasFusedRings chamazulene 5 7 ∧
  HasAlternatingCycle chamazulene 10 ∧
  Nonempty (CarbonFrameworkEmbedding azulene chamazulene) ∧
  IsMethylSubstituent chamazulene (chamazuleneAtomIndex 0) (chamazuleneAtomIndex 10) ∧
  IsMethylSubstituent chamazulene (chamazuleneAtomIndex 5) (chamazuleneAtomIndex 11) ∧
  IsEthylSubstituent chamazulene (chamazuleneAtomIndex 8)
    (chamazuleneAtomIndex 12) (chamazuleneAtomIndex 13)

inductive ProblemSourceLocator
  | pageTwoCompoundTable
  | pageThreeChlorinationSentence
  | pageThreeThermalSentence
  deriving DecidableEq, Repr

/-! ## Chlorination and isotope-pattern ledger -/

def chlorineGas : MolecularFormula := ⟨0, 0, 0, 2⟩
def hydrogenChloride : MolecularFormula := ⟨0, 1, 0, 1⟩

/-- Formula after `k` hydrogens have been substituted by chlorine. -/
def substitutionChlorinationProduct
    (precursor : MolecularFormula) (k : ℕ) : MolecularFormula :=
  ⟨precursor.carbon, precursor.hydrogen - k, precursor.oxygen,
    precursor.chlorine + k⟩

/-- Relative binomial coefficient for exactly `j` heavy chlorine isotopes when
the contest-level light:heavy abundance ratio is `3:1`. -/
def chlorineEnvelopeCoefficient (chlorineAtoms heavyAtoms : ℕ) : ℕ :=
  Nat.choose chlorineAtoms heavyAtoms * 3 ^ (chlorineAtoms - heavyAtoms)

/-- Source observation at `m/z = 218, 220`, together with the complete
outcome-decisive atom ledger.  The lower peak is the all-`Cl-35` isotopologue;
the peak two units higher replaces exactly one `Cl-35` by `Cl-37`.  The
coefficient equation encodes their observed `3:1` intensity ratio, so it does
not incorrectly treat the upper peak as the all-heavy isotopologue. -/
structure ChlorinationObservation (precursor : MolecularFormula) where
  locator : ProblemSourceLocator
  isChlorinationSentence : locator = .pageThreeChlorinationSentence
  substitutionCount : ℕ
  positiveSubstitutionCount : 0 < substitutionCount
  enoughHydrogen : substitutionCount ≤ precursor.hydrogen
  precursorInitiallyChlorineFree : precursor.chlorine = 0
  atomLedger :
    MolecularFormula.add precursor
        (MolecularFormula.scale substitutionCount chlorineGas) =
      MolecularFormula.add
        (substitutionChlorinationProduct precursor substitutionCount)
        (MolecularFormula.scale substitutionCount hydrogenChloride)
  lightPeak :
    (substitutionChlorinationProduct precursor substitutionCount).nominalMass35 = 218
  heavyPeak :
    (substitutionChlorinationProduct precursor substitutionCount).nominalMass35 +
        2 = 220
  intensityRatio :
    chlorineEnvelopeCoefficient
        (substitutionChlorinationProduct precursor substitutionCount).chlorine 0 =
      3 * chlorineEnvelopeCoefficient
        (substitutionChlorinationProduct precursor substitutionCount).chlorine
        1

/-- The 3:1 ratio of the all-light and exactly-one-heavy chlorine isotopologues
forces one chlorine substitution. -/
theorem chlorine_pair_forces_one_substitution
    {precursor : MolecularFormula} (h : ChlorinationObservation precursor) :
    h.substitutionCount = 1 := by
  have hpos := h.positiveSubstitutionCount
  have hratio := h.intensityRatio
  simp only [substitutionChlorinationProduct,
    h.precursorInitiallyChlorineFree, Nat.zero_add,
    chlorineEnvelopeCoefficient, Nat.choose_zero_right,
    Nat.sub_zero, Nat.choose_one_right] at hratio
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hk] at hratio ⊢
  simp only [Nat.succ_sub_one, Nat.pow_succ] at hratio
  have hpow : 0 < 3 ^ k := pow_pos (by omega : 0 < (3 : ℕ)) k
  nlinarith

/-- The lower nominal-mass peak is therefore 34 units above the precursor. -/
theorem chlorine_pair_forces_parent_nominal_mass
    {precursor : MolecularFormula} (h : ChlorinationObservation precursor) :
    precursor.nominalMass35 = 184 := by
  have hk := chlorine_pair_forces_one_substitution h
  have hH := h.enoughHydrogen
  have hCl := h.precursorInitiallyChlorineFree
  have hm := h.lightPeak
  simp only [hk, substitutionChlorinationProduct,
    MolecularFormula.nominalMass35] at hm ⊢
  omega

/-- Exhaustive calculation over the ten source-table entries. -/
theorem table_nominal_mass_184_unique
    (entry : TableCompound) (h : (tableFormula entry).nominalMass35 = 184) :
    entry = .seven := by
  cases entry <;>
    norm_num [tableFormula, MolecularFormula.nominalMass35] at h
  rfl

/-- The isotope/mass calculation identifies `Z` as table compound 7 without
assuming a candidate-shaped source premise. -/
theorem chlorination_observation_identifies_compound_seven
    (entry : TableCompound) (h : ChlorinationObservation (tableFormula entry)) :
    entry = .seven := by
  exact table_nominal_mass_184_unique entry
    (chlorine_pair_forces_parent_nominal_mass h)

/-! ## Finite structural certificates used by the requested outputs -/

/-- Select an ordinary integral order for every possible bond.  The selector
is relevant only for aromatic bonds; fixed bond labels localize to themselves. -/
private def selectedLocalizationOrder {n : ℕ}
    (aromaticDouble : Bond n → Bool) (b : Bond n) : LocalizedBondOrder :=
  match b.order with
  | .single => .single
  | .double => .double
  | .triple => .triple
  | .aromatic => if aromaticDouble b then .double else .single

private theorem selectedLocalizationOrder_compatible {n : ℕ}
    (aromaticDouble : Bond n → Bool) (b : Bond n) :
    b.order.AllowsLocalization (selectedLocalizationOrder aromaticDouble b) := by
  cases horder : b.order <;>
    simp only [selectedLocalizationOrder, horder, BondOrder.AllowsLocalization]
  split <;> simp_all

private def azuleneAtomIndex (i : Fin 18) : Fin azulene.atomCount := by
  simpa [azulene] using i

private def naphthaleneAtomIndex (i : Fin 18) : Fin naphthalene.atomCount := by
  simpa [naphthalene] using i

private def azuleneAromaticDouble
    (b : Bond azulene.atomCount) : Bool := by
  change Bond 18 at b
  exact decide (b = mkBond 0 1 .aromatic ∨
    b = mkBond 2 3 .aromatic ∨
    b = mkBond 5 6 .aromatic ∨
    b = mkBond 7 8 .aromatic ∨
    b = mkBond 9 4 .aromatic)

private def naphthaleneAromaticDouble
    (b : Bond naphthalene.atomCount) : Bool := by
  change Bond 18 at b
  exact decide (b = mkBond 0 1 .aromatic ∨
    b = mkBond 2 3 .aromatic ∨
    b = mkBond 4 6 .aromatic ∨
    b = mkBond 7 8 .aromatic ∨
    b = mkBond 9 5 .aromatic)

private def azuleneLocalization : KekuleLocalization azulene where
  localizedOrder := selectedLocalizationOrder azuleneAromaticDouble
  compatible := fun b _ => selectedLocalizationOrder_compatible _ b

private def naphthaleneLocalization : KekuleLocalization naphthalene where
  localizedOrder := selectedLocalizationOrder naphthaleneAromaticDouble
  compatible := fun b _ => selectedLocalizationOrder_compatible _ b

private def chamazuleneLocalization : KekuleLocalization chamazulene where
  localizedOrder := selectedLocalizationOrder (fun _ => false)
  compatible := fun b _ => selectedLocalizationOrder_compatible _ b

private theorem azulene_localized_valence :
    ∀ i, azulene.bondValenceAtUnder azuleneLocalization i =
      (azulene.atom i).element.closedShellValence := by
  decide

private theorem naphthalene_localized_valence :
    ∀ i, naphthalene.bondValenceAtUnder naphthaleneLocalization i =
      (naphthalene.atom i).element.closedShellValence := by
  decide

private theorem chamazulene_localized_valence :
    ∀ i, chamazulene.bondValenceAtUnder chamazuleneLocalization i =
      (chamazulene.atom i).element.closedShellValence := by
  decide

private def azuleneFiveCycle : RingCycle azulene 5 where
  positive := by norm_num
  atomAt := ![azuleneAtomIndex 0, azuleneAtomIndex 1, azuleneAtomIndex 2,
    azuleneAtomIndex 3, azuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def azuleneSevenCycle : RingCycle azulene 7 where
  positive := by norm_num
  atomAt := ![azuleneAtomIndex 3, azuleneAtomIndex 5, azuleneAtomIndex 6,
    azuleneAtomIndex 7, azuleneAtomIndex 8, azuleneAtomIndex 9,
    azuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def azulenePerimeterCycle : RingCycle azulene 10 where
  positive := by norm_num
  atomAt := ![azuleneAtomIndex 0, azuleneAtomIndex 1, azuleneAtomIndex 2,
    azuleneAtomIndex 3, azuleneAtomIndex 5, azuleneAtomIndex 6,
    azuleneAtomIndex 7, azuleneAtomIndex 8, azuleneAtomIndex 9,
    azuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def chamazuleneFiveCycle : RingCycle chamazulene 5 where
  positive := by norm_num
  atomAt := ![chamazuleneAtomIndex 0, chamazuleneAtomIndex 1,
    chamazuleneAtomIndex 2, chamazuleneAtomIndex 3, chamazuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def chamazuleneSevenCycle : RingCycle chamazulene 7 where
  positive := by norm_num
  atomAt := ![chamazuleneAtomIndex 3, chamazuleneAtomIndex 5,
    chamazuleneAtomIndex 6, chamazuleneAtomIndex 7, chamazuleneAtomIndex 8,
    chamazuleneAtomIndex 9, chamazuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def chamazulenePerimeterCycle : RingCycle chamazulene 10 where
  positive := by norm_num
  atomAt := ![chamazuleneAtomIndex 0, chamazuleneAtomIndex 1,
    chamazuleneAtomIndex 2, chamazuleneAtomIndex 3, chamazuleneAtomIndex 5,
    chamazuleneAtomIndex 6, chamazuleneAtomIndex 7, chamazuleneAtomIndex 8,
    chamazuleneAtomIndex 9, chamazuleneAtomIndex 4]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def naphthaleneLeftCycle : RingCycle naphthalene 6 where
  positive := by norm_num
  atomAt := ![naphthaleneAtomIndex 0, naphthaleneAtomIndex 1,
    naphthaleneAtomIndex 2, naphthaleneAtomIndex 3, naphthaleneAtomIndex 4,
    naphthaleneAtomIndex 5]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def naphthaleneRightCycle : RingCycle naphthalene 6 where
  positive := by norm_num
  atomAt := ![naphthaleneAtomIndex 4, naphthaleneAtomIndex 6,
    naphthaleneAtomIndex 7, naphthaleneAtomIndex 8, naphthaleneAtomIndex 9,
    naphthaleneAtomIndex 5]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private def naphthalenePerimeterCycle : RingCycle naphthalene 10 where
  positive := by norm_num
  atomAt := ![naphthaleneAtomIndex 0, naphthaleneAtomIndex 1,
    naphthaleneAtomIndex 2, naphthaleneAtomIndex 3, naphthaleneAtomIndex 4,
    naphthaleneAtomIndex 6, naphthaleneAtomIndex 7, naphthaleneAtomIndex 8,
    naphthaleneAtomIndex 9, naphthaleneAtomIndex 5]
  injective := by decide
  adjacentNext := by
    simp only [MolecularGraph.adjacent]
    decide

private theorem azulene_has_fused_rings : HasFusedRings azulene 5 7 := by
  refine ⟨azuleneFiveCycle, azuleneSevenCycle, ?_, azuleneAtomIndex 3, ?_,
    azuleneAtomIndex 4, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · simp only [MolecularGraph.adjacent]
    decide

private theorem chamazulene_has_fused_rings : HasFusedRings chamazulene 5 7 := by
  refine ⟨chamazuleneFiveCycle, chamazuleneSevenCycle, ?_, chamazuleneAtomIndex 3,
    ?_, chamazuleneAtomIndex 4, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · simp only [MolecularGraph.adjacent]
    decide

private theorem naphthalene_has_fused_rings : HasFusedRings naphthalene 6 6 := by
  refine ⟨naphthaleneLeftCycle, naphthaleneRightCycle, ?_, naphthaleneAtomIndex 4,
    ?_, naphthaleneAtomIndex 5, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · simp only [MolecularGraph.adjacent]
    decide

private theorem azulene_has_aromatic_perimeter : HasAromaticCycle azulene 10 := by
  exact ⟨azulenePerimeterCycle, by decide⟩

private theorem naphthalene_has_aromatic_perimeter :
    HasAromaticCycle naphthalene 10 := by
  exact ⟨naphthalenePerimeterCycle, by decide⟩

private theorem chamazulene_has_alternating_perimeter :
    HasAlternatingCycle chamazulene 10 := by
  exact ⟨chamazulenePerimeterCycle, by decide⟩

private theorem adjacent_reverse (m : MolecularGraph) {i j : Fin m.atomCount}
    (h : m.adjacent i j) : m.adjacent j i := by
  simpa only [MolecularGraph.adjacent, MolecularGraph.bondLabelCodeBetween,
    or_comm] using h

private theorem reflTransGen_reverse {α : Type} {r : α → α → Prop}
    (symmetric : ∀ {a b}, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | @tail b c hab hbc ih =>
      exact (Relation.ReflTransGen.single (symmetric hbc)).trans ih

private theorem connected_of_decreasing_parent (m : MolecularGraph)
    (root : Fin m.atomCount) (parent : Fin m.atomCount → Fin m.atomCount)
    (parentAdjacent : ∀ i, i ≠ root → m.adjacent (parent i) i)
    (parentDecreases : ∀ i, i ≠ root → (parent i).val < i.val) :
    m.connected := by
  have reaches : ∀ k : ℕ, ∀ i : Fin m.atomCount, i.val = k →
      Relation.ReflTransGen m.adjacent root i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hi
        by_cases hir : i = root
        · subst i
          exact .refl
        · have hparent : Relation.ReflTransGen m.adjacent root (parent i) :=
            ih (parent i).val (by simpa [hi] using parentDecreases i hir)
              (parent i) rfl
          exact hparent.tail (parentAdjacent i hir)
  intro i j
  exact (reflTransGen_reverse (fun {_ _} => adjacent_reverse m)
      (reaches i.val i rfl)).trans (reaches j.val j rfl)

private def azuleneParent
    (i : Fin azulene.atomCount) : Fin azulene.atomCount := by
  change Fin 18 at i ⊢
  exact ![0, 0, 1, 2, 0, 3, 5, 6, 7, 8, 0, 1, 2, 5, 6, 7, 8, 9] i

private def naphthaleneParent
    (i : Fin naphthalene.atomCount) : Fin naphthalene.atomCount := by
  change Fin 18 at i ⊢
  exact ![0, 0, 1, 2, 3, 0, 4, 6, 7, 8, 0, 1, 2, 3, 6, 7, 8, 9] i

private def chamazuleneParent
    (i : Fin chamazulene.atomCount) : Fin chamazulene.atomCount := by
  change Fin 30 at i ⊢
  exact ![0, 0, 1, 2, 0, 3, 5, 6, 7, 8, 0, 5, 8, 12, 1,
    2, 6, 7, 9, 10, 10, 10, 11, 11, 11, 12, 12, 13, 13, 13] i

private theorem azulene_parent_adjacent : ∀ i, i ≠ azuleneAtomIndex 0 →
    azulene.adjacent (azuleneParent i) i := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    simp only [MolecularGraph.adjacent]
    decide

private theorem naphthalene_parent_adjacent : ∀ i, i ≠ naphthaleneAtomIndex 0 →
    naphthalene.adjacent (naphthaleneParent i) i := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    simp only [MolecularGraph.adjacent]
    decide

private theorem chamazulene_parent_adjacent : ∀ i, i ≠ chamazuleneAtomIndex 0 →
    chamazulene.adjacent (chamazuleneParent i) i := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    simp only [MolecularGraph.adjacent]
    decide

private theorem azulene_parent_decreases : ∀ i, i ≠ azuleneAtomIndex 0 →
    (azuleneParent i).val < i.val := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals decide

private theorem naphthalene_parent_decreases : ∀ i, i ≠ naphthaleneAtomIndex 0 →
    (naphthaleneParent i).val < i.val := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals decide

private theorem chamazulene_parent_decreases : ∀ i, i ≠ chamazuleneAtomIndex 0 →
    (chamazuleneParent i).val < i.val := by
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals decide

private theorem azulene_connected : azulene.connected :=
  connected_of_decreasing_parent azulene (azuleneAtomIndex 0) azuleneParent
    azulene_parent_adjacent azulene_parent_decreases

private theorem naphthalene_connected : naphthalene.connected :=
  connected_of_decreasing_parent naphthalene (naphthaleneAtomIndex 0)
    naphthaleneParent naphthalene_parent_adjacent naphthalene_parent_decreases

private theorem chamazulene_connected : chamazulene.connected :=
  connected_of_decreasing_parent chamazulene (chamazuleneAtomIndex 0)
    chamazuleneParent chamazulene_parent_adjacent chamazulene_parent_decreases

private theorem azulene_bonds_nonlooping :
    ∀ b ∈ azulene.bonds, b.first ≠ b.second := by
  have h : azulene.bonds.Forall (fun b => b.first ≠ b.second) := by
    decide
  exact List.forall_iff_forall_mem.mp h

private theorem naphthalene_bonds_nonlooping :
    ∀ b ∈ naphthalene.bonds, b.first ≠ b.second := by
  have h : naphthalene.bonds.Forall (fun b => b.first ≠ b.second) := by
    decide
  exact List.forall_iff_forall_mem.mp h

private theorem chamazulene_bonds_nonlooping :
    ∀ b ∈ chamazulene.bonds, b.first ≠ b.second := by
  have h : chamazulene.bonds.Forall (fun b => b.first ≠ b.second) := by
    decide
  exact List.forall_iff_forall_mem.mp h

private theorem azulene_well_formed : azulene.WellFormed := by
  refine ⟨by decide, azulene_bonds_nonlooping, ?_,
    ⟨azuleneLocalization, azulene_localized_valence⟩, azulene_connected⟩
  simp only [Bond.sameUndirected]
  decide

private theorem naphthalene_well_formed : naphthalene.WellFormed := by
  refine ⟨by decide, naphthalene_bonds_nonlooping, ?_,
    ⟨naphthaleneLocalization, naphthalene_localized_valence⟩,
    naphthalene_connected⟩
  simp only [Bond.sameUndirected]
  decide

private theorem chamazulene_well_formed : chamazulene.WellFormed := by
  refine ⟨by decide, chamazulene_bonds_nonlooping, ?_,
    ⟨chamazuleneLocalization, chamazulene_localized_valence⟩,
    chamazulene_connected⟩
  simp only [Bond.sameUndirected]
  decide

/-- A computable presentation of the already-defined element-filtered
neighbour set, used only to discharge the finite substituent audits. -/
private def computableNeighborsOfElement
    (m : MolecularGraph) (i : Fin m.atomCount) (e : ChemicalElement) :
    Finset (Fin m.atomCount) :=
  Finset.univ.filter (fun j =>
    (m.atom j).element = e ∧ 0 < m.bondLabelCodeBetween i j)

private theorem neighborsOfElement_eq_computable
    (m : MolecularGraph) (i : Fin m.atomCount) (e : ChemicalElement) :
    m.neighborsOfElement i e = computableNeighborsOfElement m i e := by
  classical
  ext j
  simp only [MolecularGraph.neighborsOfElement, computableNeighborsOfElement,
    Finset.mem_filter, Finset.mem_univ, true_and, MolecularGraph.adjacent]

private theorem chamazulene_methyl_at_zero :
    IsMethylSubstituent chamazulene (chamazuleneAtomIndex 0)
      (chamazuleneAtomIndex 10) := by
  simp only [IsMethylSubstituent, neighborsOfElement_eq_computable]
  decide

private theorem chamazulene_methyl_at_five :
    IsMethylSubstituent chamazulene (chamazuleneAtomIndex 5)
      (chamazuleneAtomIndex 11) := by
  simp only [IsMethylSubstituent, neighborsOfElement_eq_computable]
  decide

private theorem chamazulene_ethyl_at_eight :
    IsEthylSubstituent chamazulene (chamazuleneAtomIndex 8)
      (chamazuleneAtomIndex 12) (chamazuleneAtomIndex 13) := by
  simp only [IsEthylSubstituent, neighborsOfElement_eq_computable]
  decide

private theorem azulene_carbon_index_lt_ten (i : CarbonSite azulene) :
    i.val.val < 10 := by
  by_contra h
  have hnot : ¬ i.val.val < 10 := h
  have hi := i.property
  simp [azulene, hnot, neutralClosedShellAtom] at hi

private def azuleneCarbonToCham
    (i : CarbonSite azulene) : CarbonSite chamazulene := by
  refine ⟨⟨i.val.val, ?_⟩, ?_⟩
  · have hi := i.val.isLt
    change i.val.val < 18 at hi
    change i.val.val < 30
    omega
  · have hi : i.val.val < 14 := by
      exact lt_trans (azulene_carbon_index_lt_ten i) (by norm_num)
    simp [chamazulene, hi, neutralClosedShellAtom]

private def azuleneCarbonFin (i : CarbonSite azulene) : Fin 10 :=
  ⟨i.val.val, azulene_carbon_index_lt_ten i⟩

private def finTenToAzuleneAtom (i : Fin 10) : Fin azulene.atomCount :=
  azuleneAtomIndex ⟨i.val, by omega⟩

private def finTenToChamazuleneAtom (i : Fin 10) : Fin chamazulene.atomCount :=
  chamazuleneAtomIndex ⟨i.val, by omega⟩

private theorem azulene_chamazulene_core_adjacency (i j : Fin 10) :
    chamazulene.adjacent (finTenToChamazuleneAtom i)
        (finTenToChamazuleneAtom j) ↔
      azulene.adjacent (finTenToAzuleneAtom i) (finTenToAzuleneAtom j) := by
  simp only [MolecularGraph.adjacent]
  fin_cases i <;> fin_cases j <;> decide

private def azuleneChamFrameworkEmbedding :
    CarbonFrameworkEmbedding azulene chamazulene where
  toSite := azuleneCarbonToCham
  injective := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun x : CarbonSite chamazulene => x.val.val) h
  preservesCarbonAdjacency := by
    intro i j
    change chamazulene.adjacent
        (finTenToChamazuleneAtom (azuleneCarbonFin i))
        (finTenToChamazuleneAtom (azuleneCarbonFin j)) ↔
      azulene.adjacent
        (finTenToAzuleneAtom (azuleneCarbonFin i))
        (finTenToAzuleneAtom (azuleneCarbonFin j))
    exact azulene_chamazulene_core_adjacency (azuleneCarbonFin i)
      (azuleneCarbonFin j)

/-! Exact planar realizations and the requested independent mirror actions. -/

private def azulenePosition (i : Fin azulene.atomCount) : Point3 := by
  change Fin 18 at i
  exact ![
    ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨-1, 0, 0⟩, ⟨1, 2, 0⟩,
    ⟨-1, 2, 0⟩, ⟨2, 3, 0⟩, ⟨3, 4, 0⟩, ⟨0, 5, 0⟩,
    ⟨-3, 4, 0⟩, ⟨-2, 3, 0⟩, ⟨1, 10, 0⟩, ⟨0, 11, 0⟩,
    ⟨-1, 10, 0⟩, ⟨2, 13, 0⟩, ⟨3, 14, 0⟩, ⟨0, 15, 0⟩,
    ⟨-3, 14, 0⟩, ⟨-2, 13, 0⟩] i

private def naphthalenePosition (i : Fin naphthalene.atomCount) : Point3 := by
  change Fin 18 at i
  exact ![
    ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨-2, 2, 0⟩, ⟨-1, 1, 0⟩,
    ⟨3, 0, 0⟩, ⟨-3, 0, 0⟩, ⟨-1, -1, 0⟩, ⟨-2, -2, 0⟩,
    ⟨2, -2, 0⟩, ⟨1, -1, 0⟩, ⟨4, 4, 0⟩, ⟨5, 5, 0⟩,
    ⟨-5, 5, 0⟩, ⟨-4, 4, 0⟩, ⟨-4, -4, 0⟩, ⟨-5, -5, 0⟩,
    ⟨5, -5, 0⟩, ⟨4, -4, 0⟩] i

private def azuleneRealization : SpatialRealization azulene where
  position := azulenePosition
  injective := by decide
  noncollinear := by
    refine ⟨azuleneAtomIndex 0, azuleneAtomIndex 1, azuleneAtomIndex 3,
      by decide, by decide, by decide, ?_⟩
    change ¬ Point3.collinear ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨1, 2, 0⟩
    norm_num [Point3.collinear]

private def naphthaleneRealization : SpatialRealization naphthalene where
  position := naphthalenePosition
  injective := by decide
  noncollinear := by
    refine ⟨naphthaleneAtomIndex 0, naphthaleneAtomIndex 1,
      naphthaleneAtomIndex 4, by decide, by decide,
      by decide, ?_⟩
    change ¬ Point3.collinear ⟨1, 1, 0⟩ ⟨2, 2, 0⟩ ⟨3, 0, 0⟩
    norm_num [Point3.collinear]

private def azuleneInPlaneReflection : Equiv.Perm (Fin azulene.atomCount) := by
  change Equiv.Perm (Fin 18)
  exact ⟨![2, 1, 0, 4, 3, 9, 8, 7, 6, 5, 12, 11, 10, 17, 16, 15, 14, 13],
    ![2, 1, 0, 4, 3, 9, 8, 7, 6, 5, 12, 11, 10, 17, 16, 15, 14, 13],
    by decide, by decide⟩

private def naphthaleneXReflection : Equiv.Perm (Fin naphthalene.atomCount) := by
  change Equiv.Perm (Fin 18)
  exact ⟨![3, 2, 1, 0, 5, 4, 9, 8, 7, 6, 13, 12, 11, 10, 17, 16, 15, 14],
    ![3, 2, 1, 0, 5, 4, 9, 8, 7, 6, 13, 12, 11, 10, 17, 16, 15, 14],
    by decide, by decide⟩

private def naphthaleneYReflection : Equiv.Perm (Fin naphthalene.atomCount) := by
  change Equiv.Perm (Fin 18)
  exact ⟨![9, 8, 7, 6, 4, 5, 3, 2, 1, 0, 17, 16, 15, 14, 13, 12, 11, 10],
    ![9, 8, 7, 6, 4, 5, 3, 2, 1, 0, 17, 16, 15, 14, 13, 12, 11, 10],
    by decide, by decide⟩

private def azuleneMolecularPlane : MirrorPlane azulene azuleneRealization where
  normalAxis := .z
  action := Equiv.refl _
  involutive := by simp
  preservesAtom := by simp
  preservesBondLabel := by simp
  realizesReflection := by decide

private def azuleneInPlaneMirror : MirrorPlane azulene azuleneRealization where
  normalAxis := .x
  action := azuleneInPlaneReflection
  involutive := by decide
  preservesAtom := by decide
  preservesBondLabel := by decide
  realizesReflection := by decide

private def naphthaleneMolecularPlane :
    MirrorPlane naphthalene naphthaleneRealization where
  normalAxis := .z
  action := Equiv.refl _
  involutive := by simp
  preservesAtom := by simp
  preservesBondLabel := by simp
  realizesReflection := by decide

private def naphthaleneXMirror :
    MirrorPlane naphthalene naphthaleneRealization where
  normalAxis := .x
  action := naphthaleneXReflection
  involutive := by decide
  preservesAtom := by decide
  preservesBondLabel := by decide
  realizesReflection := by decide

private def naphthaleneYMirror :
    MirrorPlane naphthalene naphthaleneRealization where
  normalAxis := .y
  action := naphthaleneYReflection
  involutive := by decide
  preservesAtom := by decide
  preservesBondLabel := by decide
  realizesReflection := by decide

private theorem azulene_planar : HasPlanarRealization azulene :=
  ⟨azuleneRealization, azuleneMolecularPlane, rfl⟩

private theorem naphthalene_planar : HasPlanarRealization naphthalene :=
  ⟨naphthaleneRealization, naphthaleneMolecularPlane, rfl⟩

private def azuleneMirrorPlanes :
    Fin 2 → MirrorPlane azulene azuleneRealization :=
  ![azuleneMolecularPlane, azuleneInPlaneMirror]

private def azuleneActionMarker : Fin 2 → ℕ := ![0, 2]

private theorem azulene_action_marker_spec (i : Fin 2) :
    ((azuleneMirrorPlanes i).action (azuleneAtomIndex 0)).val =
      azuleneActionMarker i := by
  fin_cases i <;> decide

private theorem azulene_action_marker_injective :
    Function.Injective azuleneActionMarker := by decide

private def naphthaleneMirrorPlanes :
    Fin 3 → MirrorPlane naphthalene naphthaleneRealization :=
  ![naphthaleneMolecularPlane, naphthaleneXMirror, naphthaleneYMirror]

private def naphthaleneActionMarker : Fin 3 → ℕ := ![0, 3, 9]

private theorem naphthalene_action_marker_spec (i : Fin 3) :
    ((naphthaleneMirrorPlanes i).action (naphthaleneAtomIndex 0)).val =
      naphthaleneActionMarker i := by
  fin_cases i <;> decide

private theorem naphthalene_action_marker_injective :
    Function.Injective naphthaleneActionMarker := by decide

private theorem azulene_two_mirror_planes :
    HasMutuallyPerpendicularMirrorPlanes azulene 2 := by
  refine ⟨azuleneRealization, azuleneMirrorPlanes, by decide, ?_⟩
  intro i j h
  apply azulene_action_marker_injective
  calc
    azuleneActionMarker i =
        ((azuleneMirrorPlanes i).action (azuleneAtomIndex 0)).val :=
      (azulene_action_marker_spec i).symm
    _ = ((azuleneMirrorPlanes j).action (azuleneAtomIndex 0)).val :=
      congrArg
        (fun e : Equiv.Perm (Fin azulene.atomCount) =>
          (e (azuleneAtomIndex 0)).val) h
    _ = azuleneActionMarker j := azulene_action_marker_spec j

private theorem naphthalene_three_mirror_planes :
    HasMutuallyPerpendicularMirrorPlanes naphthalene 3 := by
  refine ⟨naphthaleneRealization, naphthaleneMirrorPlanes,
    by decide, ?_⟩
  intro i j h
  apply naphthalene_action_marker_injective
  calc
    naphthaleneActionMarker i =
        ((naphthaleneMirrorPlanes i).action (naphthaleneAtomIndex 0)).val :=
      (naphthalene_action_marker_spec i).symm
    _ = ((naphthaleneMirrorPlanes j).action (naphthaleneAtomIndex 0)).val :=
      congrArg
        (fun e : Equiv.Perm (Fin naphthalene.atomCount) =>
          (e (naphthaleneAtomIndex 0)).val) h
    _ = naphthaleneActionMarker j := naphthalene_action_marker_spec j

/-! ## Requested-output contracts -/

/-- Requested output `identity_z`: compound 7, whose explicit graph is
1,4-dimethyl-7-ethylazulene (chamazulene), `C14H16`. -/
def IdentityZResult : Prop :=
  (∀ entry : TableCompound,
      ChlorinationObservation (tableFormula entry) → entry = .seven) ∧
  Nonempty (ChlorinationObservation (tableFormula .seven)) ∧
  chamazulene.formula = tableFormula .seven ∧
  IsOneFourDimethylSevenEthylAzulene

/-- Requested output `structure_a`: the all-atom azulene graph, a neutral
`C10H8` fused 5/7 hydrocarbon with a delocalized aromatic perimeter, an
admissible closed-shell Kekule localization, two perpendicular mirror planes,
and the carbon framework found in compound 7. -/
def StructureAResult : Prop :=
  azulene.WellFormed ∧
  azulene.formula = ⟨10, 8, 0, 0⟩ ∧
  HasFusedRings azulene 5 7 ∧
  HasAromaticCycle azulene 10 ∧
  HasPlanarRealization azulene ∧
  HasMutuallyPerpendicularMirrorPlanes azulene 2 ∧
  Nonempty (CarbonFrameworkEmbedding azulene chamazulene)

/-- A constructive graph-level isomerization witness: every atom and its
electronic state is retained bijectively, while at least one adjacency changes. -/
structure IsomerizationWitness (reactant product : MolecularGraph) where
  atomMap : Fin reactant.atomCount ≃ Fin product.atomCount
  preservesAtom : ∀ i, product.atom (atomMap i) = reactant.atom i
  changedAdjacency : ∃ i j,
    (product.adjacent (atomMap i) (atomMap j) ∧
        ¬ reactant.adjacent i j) ∨
      (reactant.adjacent i j ∧
        ¬ product.adjacent (atomMap i) (atomMap j))

/-- A source-located certificate for the directed heating sentence. -/
structure NamedThermalTransformCertificate
    (reactant product : MolecularGraph) where
  locator : ProblemSourceLocator
  isThermalSentence : locator = .pageThreeThermalSentence
  isomerization : IsomerizationWitness reactant product

/-- The source arrow is used only as a directed, non-exclusive compatibility
constraint.  The atom bijection checks formula conservation and rearrangement,
but claims no protocol, yield, phase, sole-product status, or bulk balance. -/
def QualitativeNamedThermalTransform
    (reactant product : MolecularGraph) : Prop :=
  Nonempty (NamedThermalTransformCertificate reactant product)

private def azuleneNaphthaleneAtomMap :
    Fin azulene.atomCount ≃ Fin naphthalene.atomCount := by
  change Fin 18 ≃ Fin 18
  exact Equiv.refl _

private def azuleneNaphthaleneIsomerization :
    IsomerizationWitness azulene naphthalene where
  atomMap := azuleneNaphthaleneAtomMap
  preservesAtom := by decide
  changedAdjacency := by
    refine ⟨azuleneAtomIndex 0, azuleneAtomIndex 4, Or.inr ⟨?_, ?_⟩⟩
    · simp only [MolecularGraph.adjacent]
      decide
    · simp only [MolecularGraph.adjacent]
      decide

private def azuleneNaphthaleneThermalCertificate :
    NamedThermalTransformCertificate azulene naphthalene where
  locator := .pageThreeThermalSentence
  isThermalSentence := rfl
  isomerization := azuleneNaphthaleneIsomerization

private theorem azulene_thermally_transforms_to_naphthalene :
    QualitativeNamedThermalTransform azulene naphthalene :=
  ⟨azuleneNaphthaleneThermalCertificate⟩

/-- Requested output `structure_b`: the all-atom naphthalene graph, a neutral
`C10H8` fused 6/6 delocalized aromatic system with an admissible closed-shell
Kekule localization and three mutually perpendicular mirror planes, compatible
with the stated heating direction from azulene. -/
def StructureBResult : Prop :=
  naphthalene.WellFormed ∧
  naphthalene.formula = ⟨10, 8, 0, 0⟩ ∧
  HasFusedRings naphthalene 6 6 ∧
  HasAromaticCycle naphthalene 10 ∧
  HasPlanarRealization naphthalene ∧
  HasMutuallyPerpendicularMirrorPlanes naphthalene 3 ∧
  QualitativeNamedThermalTransform azulene naphthalene

/-- Raw exact-symbolic result covering all requested outputs in source order. -/
def RawResult : Prop :=
  IdentityZResult ∧ StructureAResult ∧ StructureBResult

/-- Exact-symbolic reporting does not round or otherwise alter the molecular
graphs; this proposition still exposes each requested output separately. -/
def ReportedResult : Prop :=
  IdentityZResult ∧ StructureAResult ∧ StructureBResult

theorem identity_z_result : IdentityZResult := by
  refine ⟨chlorination_observation_identifies_compound_seven, ?_,
    by decide, ?_⟩
  · exact ⟨{
      locator := .pageThreeChlorinationSentence
      isChlorinationSentence := rfl
      substitutionCount := 1
      positiveSubstitutionCount := by decide
      enoughHydrogen := by decide
      precursorInitiallyChlorineFree := by decide
      atomLedger := by decide
      lightPeak := by decide
      heavyPeak := by decide
      intensityRatio := by decide }⟩
  · exact ⟨chamazulene_well_formed, by decide,
      chamazulene_has_fused_rings, chamazulene_has_alternating_perimeter,
      ⟨azuleneChamFrameworkEmbedding⟩, chamazulene_methyl_at_zero,
      chamazulene_methyl_at_five, chamazulene_ethyl_at_eight⟩

theorem structure_a_result : StructureAResult := by
  exact ⟨azulene_well_formed, by decide, azulene_has_fused_rings,
    azulene_has_aromatic_perimeter, azulene_planar, azulene_two_mirror_planes,
    ⟨azuleneChamFrameworkEmbedding⟩⟩

/-!
The empirical direction cue used by the next theorem is source-scoped.  A
generic literature check supporting this direction is Brouwer and Troe, “Thermal
isomerization of azulene to naphthalene in shock waves”, *International Journal
of Chemical Kinetics* 20 (1988), 379--386, DOI 10.1002/kin.550200504, abstract.
The problem itself supplies the directed heating observation.  Neither source
is encoded as a universal inverse-classification rule.
-/
theorem structure_b_result : StructureBResult := by
  exact ⟨naphthalene_well_formed, by decide,
    naphthalene_has_fused_rings, naphthalene_has_aromatic_perimeter,
    naphthalene_planar, naphthalene_three_mirror_planes,
    azulene_thermally_transforms_to_naphthalene⟩

theorem raw_result :
    ("5a3138305792d5cb423621d87fbf9da7b6d5c0b4725083a75fa257c36c261eb4" : String) =
      "5a3138305792d5cb423621d87fbf9da7b6d5c0b4725083a75fa257c36c261eb4" ∧
    RawResult := by
  exact ⟨rfl, identity_z_result, structure_a_result, structure_b_result⟩

theorem reported_result :
    ("245b4efaaf0472a02f8ac47a54c3643b362452fe6207e1bcc19bdf2143033692" : String) =
      "245b4efaaf0472a02f8ac47a54c3643b362452fe6207e1bcc19bdf2143033692" ∧
    ReportedResult := by
  exact ⟨rfl, identity_z_result, structure_a_result, structure_b_result⟩

end IChO2026Problems.IChO2026T1A2
