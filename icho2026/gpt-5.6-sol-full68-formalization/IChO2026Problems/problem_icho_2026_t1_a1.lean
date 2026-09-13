import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T1-A1

This file formalizes the answer-blind identification of the two elixir
components called `X` and `Y`.  The ten numbered molecular drawings and their
plant rows are represented as finite data.  The acidic transformation is used
only as a qualitative, atom-conserving structural compatibility test: an
acyclic diene tertiary alcohol closes to a saturated bicyclic ether.  No yield,
completion, or exclusive-product assertion is made.
-/

namespace IChO2026Problems.Icho2026T1A1

/-! ## Source inventory -/

/-- The four plant rows printed in the table on problem page T1-2. -/
inductive Plant where
  | zingiber
  | hypericum
  | chamomilla
  | artemisia
  deriving DecidableEq, Fintype, Repr

/-- The ten distinct numbered structures printed in the source table. -/
inductive CompoundId where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype, Repr

/-- Molecular formula restricted to the elements occurring in this table. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Formula labels transcribed from problem page T1-2.  In particular, this is
the printed source data rather than a value imported from a chemical table. -/
def printedFormula : CompoundId → MolecularFormula
  | .c1 => ⟨11, 14, 3⟩
  | .c2 => ⟨10, 18, 1⟩
  | .c3 => ⟨10, 18, 1⟩
  | .c4 => ⟨6, 12, 1⟩
  | .c5 => ⟨10, 12, 2⟩
  | .c6 => ⟨10, 18, 1⟩
  | .c7 => ⟨14, 16, 0⟩
  | .c8 => ⟨15, 24, 0⟩
  | .c9 => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- Exact transcription of which numbered structures occur in each plant row.
Compound 3 intentionally occurs in three different rows. -/
def ExtractableFrom : Plant → CompoundId → Prop
  | .zingiber, c => c = .c1 ∨ c = .c2 ∨ c = .c3
  | .hypericum, c => c = .c4 ∨ c = .c5 ∨ c = .c6
  | .chamomilla, c => c = .c7 ∨ c = .c8 ∨ c = .c3
  | .artemisia, c => c = .c9 ∨ c = .c10 ∨ c = .c3

/-- A compound belongs to the problem's finite candidate domain precisely when
it is displayed in at least one plant row. -/
def DisplayedCandidate (c : CompoundId) : Prop :=
  ∃ p : Plant, ExtractableFrom p c

/-! ## Heavy-atom molecular drawings -/

/-- Elements explicitly present in the skeletal drawings.  Hydrogens are
implicit and are accounted for separately by `derivedFormula`. -/
inductive Element where
  | carbon
  | oxygen
  deriving DecidableEq, Inhabited, Repr

/-- An undirected heavy-atom bond.  `order = 1` is a single bond and
`order = 2` is a double bond. -/
structure Bond where
  left : ℕ
  right : ℕ
  order : ℕ
  deriving DecidableEq, Repr

/-- Finite atom-and-bond data read from one numbered skeletal diagram. -/
structure MolecularDiagram where
  atoms : List Element
  bonds : List Bond
  deriving DecidableEq, Repr

private def single (a b : ℕ) : Bond := ⟨a, b, 1⟩
private def double (a b : ℕ) : Bond := ⟨a, b, 2⟩

private def carbonAtoms (n : ℕ) : List Element :=
  List.replicate n .carbon

/-- Structure 1: the substituted phenolic ketone drawn in the Zingiber row. -/
def compound1Diagram : MolecularDiagram where
  atoms := [.oxygen, .oxygen, .oxygen] ++ carbonAtoms 11
  bonds :=
    [single 0 8, single 0 13, single 1 11, double 2 9,
     single 3 4, single 3 5, double 4 6, single 4 7,
     single 5 9, single 6 8, double 7 10, double 8 11,
     single 9 12, single 10 11]

/-- Structure 2: the bridged secondary alcohol drawn in the Zingiber row. -/
def compound2Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 10
  bonds :=
    [single 0 4, single 1 2, single 1 4, single 1 5,
     single 1 8, single 2 3, single 2 9, single 2 10,
     single 3 6, single 3 7, single 4 6, single 5 7]

/-- Structure 3: the saturated bridged ether (1,8-cineole/eucalyptol) repeated
in the Zingiber, Chamomilla, and Artemisia rows. -/
def compound3Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 10
  bonds :=
    [single 0 2, single 0 3, single 1 3, single 1 4,
     single 1 5, single 2 6, single 2 7, single 2 8,
     single 3 9, single 3 10, single 4 6, single 5 7]

/-- Structure 4: the six-carbon alkenol drawn in the Hypericum row. -/
def compound4Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 6
  bonds :=
    [single 0 5, single 1 3, single 1 5, single 2 4,
     single 2 6, double 3 4]

/-- Structure 5: the methoxyphenol with an allyl substituent drawn in the
Hypericum row. -/
def compound5Diagram : MolecularDiagram where
  atoms := [.oxygen, .oxygen] ++ carbonAtoms 10
  bonds :=
    [single 0 5, single 0 10, single 1 7, single 2 3,
     double 2 4, single 2 6, single 3 9, single 4 5,
     double 5 7, double 6 8, single 7 8, double 9 11]

/-- Structure 6: the acyclic diene tertiary alcohol linalool drawn in the
Hypericum row. -/
def compound6Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 10
  bonds :=
    [single 0 1, single 1 2, single 1 4, single 1 5,
     single 2 3, single 3 6, double 5 10, double 6 7,
     single 7 8, single 7 9]

/-- Structure 7: the substituted fused five/seven-membered hydrocarbon drawn
in the Chamomilla row. -/
def compound7Diagram : MolecularDiagram where
  atoms := carbonAtoms 14
  bonds :=
    [single 0 1, double 0 2, single 0 5, double 1 3,
     single 1 6, single 2 7, single 2 11, single 3 9,
     single 3 12, double 4 5, single 4 8, single 4 10,
     double 6 7, single 8 13, double 9 10]

/-- Structure 8: the branched acyclic tetraene hydrocarbon drawn in the
Chamomilla row. -/
def compound8Diagram : MolecularDiagram where
  atoms := carbonAtoms 15
  bonds :=
    [single 0 1, single 0 2, double 1 4, single 1 7,
     single 2 6, single 3 4, single 3 5, single 5 9,
     double 6 8, single 8 10, single 8 11, single 9 12,
     double 9 13, double 12 14]

/-- Structure 9: the bridged ketone drawn in the Artemisia row. -/
def compound9Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 10
  bonds :=
    [double 0 7, single 1 2, single 1 3, single 1 8,
     single 1 9, single 2 4, single 2 7, single 2 10,
     single 3 5, single 3 6, single 4 5, single 6 7]

/-- Structure 10: the fused-ring ketone drawn in the Artemisia row.  Its graph
is transcribed independently of the formula text printed beneath it. -/
def compound10Diagram : MolecularDiagram where
  atoms := [.oxygen] ++ carbonAtoms 10
  bonds :=
    [double 0 7, single 1 2, single 1 3, single 1 5,
     single 1 6, single 2 3, single 2 4, single 4 7,
     single 4 8, single 5 7, single 6 9, single 6 10]

/-- The complete source-first assignment of numbered entries to graphs. -/
def compoundDiagram : CompoundId → MolecularDiagram
  | .c1 => compound1Diagram
  | .c2 => compound2Diagram
  | .c3 => compound3Diagram
  | .c4 => compound4Diagram
  | .c5 => compound5Diagram
  | .c6 => compound6Diagram
  | .c7 => compound7Diagram
  | .c8 => compound8Diagram
  | .c9 => compound9Diagram
  | .c10 => compound10Diagram

/-- Ordinary neutral valences used only to recount implicit hydrogen atoms. -/
def standardValence : Element → ℕ
  | .carbon => 4
  | .oxygen => 2

/-- A bond list is well formed when every endpoint is an atom, there are no
self-bonds or duplicate unordered pairs, and every order is one or two. -/
def MolecularDiagram.WellFormed (d : MolecularDiagram) : Prop :=
  (∀ b ∈ d.bonds,
      b.left < d.atoms.length ∧ b.right < d.atoms.length ∧
      b.left ≠ b.right ∧ (b.order = 1 ∨ b.order = 2)) ∧
  ∀ b₁ ∈ d.bonds, ∀ b₂ ∈ d.bonds,
    ({b₁.left, b₁.right} : Finset ℕ) = {b₂.left, b₂.right} → b₁ = b₂

/-- The total order of all heavy-atom bonds. -/
def MolecularDiagram.totalBondOrder (d : MolecularDiagram) : ℕ :=
  (d.bonds.map Bond.order).sum

/-- Formula recomputed from the heavy-atom graph and ordinary C/O valences.
This is a cross-check carrier, not the source of the printed formula labels. -/
def MolecularDiagram.derivedFormula (d : MolecularDiagram) : MolecularFormula :=
  { carbon := d.atoms.count .carbon
    hydrogen := (d.atoms.map standardValence).sum - 2 * d.totalBondOrder
    oxygen := d.atoms.count .oxygen }

/-- Number of edges incident to atom index `i`. -/
def MolecularDiagram.incidentEdgeCount (d : MolecularDiagram) (i : ℕ) : ℕ :=
  (d.bonds.filter fun b => b.left = i ∨ b.right = i).length

/-- Sum of bond orders incident to atom index `i`. -/
def MolecularDiagram.incidentBondOrder (d : MolecularDiagram) (i : ℕ) : ℕ :=
  ((d.bonds.filter fun b => b.left = i ∨ b.right = i).map Bond.order).sum

/-- Bond order between two heavy-atom indices, or zero when they are not
joined. -/
def MolecularDiagram.bondOrder (d : MolecularDiagram) (i j : ℕ) : ℕ :=
  ((d.bonds.filter fun b =>
      (b.left = i ∧ b.right = j) ∨ (b.left = j ∧ b.right = i)).map Bond.order).sum

/-- Number of heavy-atom double bonds in a diagram. -/
def MolecularDiagram.doubleBondCount (d : MolecularDiagram) : ℕ :=
  (d.bonds.filter fun b => b.order = 2).length

/-- The cyclomatic count for a connected molecular graph. -/
def MolecularDiagram.cycleRank (d : MolecularDiagram) : ℕ :=
  d.bonds.length + 1 - d.atoms.length

/-- Atom inventory used to state atom conservation without relying on a name
or an opaque chemical predicate. -/
def MolecularDiagram.atomInventory (d : MolecularDiagram) : ℕ × ℕ :=
  (d.atoms.count .carbon, d.atoms.count .oxygen)

/-- Undirected adjacency in the heavy-atom graph. -/
def MolecularDiagram.Adjacent (d : MolecularDiagram) (i j : ℕ) : Prop :=
  ∃ b ∈ d.bonds,
    (b.left = i ∧ b.right = j) ∨ (b.left = j ∧ b.right = i)

/-- Connectedness of all in-range heavy atoms. -/
def MolecularDiagram.Connected (d : MolecularDiagram) : Prop :=
  ∀ i, i < d.atoms.length → ∀ j, j < d.atoms.length →
    Relation.ReflTransGen d.Adjacent i j

/-- Index `o` is a hydroxy oxygen attached by one single bond. -/
def MolecularDiagram.IsHydroxyOxygen (d : MolecularDiagram) (o : ℕ) : Prop :=
  d.atoms[o]? = some .oxygen ∧
  d.incidentEdgeCount o = 1 ∧ d.incidentBondOrder o = 1

instance isHydroxyOxygenDecidable (d : MolecularDiagram) (o : ℕ) :
    Decidable (d.IsHydroxyOxygen o) := by
  unfold MolecularDiagram.IsHydroxyOxygen
  infer_instance

/-- Index `o` is an ether oxygen attached by two single bonds. -/
def MolecularDiagram.IsEtherOxygen (d : MolecularDiagram) (o : ℕ) : Prop :=
  d.atoms[o]? = some .oxygen ∧
  d.incidentEdgeCount o = 2 ∧ d.incidentBondOrder o = 2

instance isEtherOxygenDecidable (d : MolecularDiagram) (o : ℕ) :
    Decidable (d.IsEtherOxygen o) := by
  unfold MolecularDiagram.IsEtherOxygen
  infer_instance

/-- A hydroxy oxygen is bonded to a carbon with three carbon neighbours. -/
def MolecularDiagram.HasTertiaryAlcohol (d : MolecularDiagram) : Prop :=
  ∃ o c,
    d.IsHydroxyOxygen o ∧ d.atoms[c]? = some .carbon ∧
    d.bondOrder o c = 1 ∧
    ((d.bonds.filter fun b =>
      ((b.left = c ∧ d.atoms[b.right]? = some .carbon) ∨
       (b.right = c ∧ d.atoms[b.left]? = some .carbon))).length = 3)

/-! ## Located source facts -/

/-- A precise human-readable locator into one of the two bound source images. -/
structure SourceLocator where
  imagePath : String
  region : String
  cue : String
  deriving DecidableEq, Repr

/-- A proposition paired with the exact source location that states it. -/
structure LocatedFact (locator : SourceLocator) (P : Prop) : Prop where
  proof : P

def tableLocator : SourceLocator :=
  ⟨"icho_2026_source/image/T1_page-2.png", "compound table",
    "the ten numbered extractable structures and their formula labels"⟩

def chromatographyLocator : SourceLocator :=
  ⟨"icho_2026_source/image/T1_page-2.png", "text below the table",
    "the elixir consists of four different substances (X, Y, Z and W)"⟩

def acidicIsomerizationLocator : SourceLocator :=
  ⟨"icho_2026_source/image/T1_page-2.png", "last sentence above item 1.1",
    "X can isomerise into Y in an acidic medium"⟩

def symmetryLocator : SourceLocator :=
  ⟨"icho_2026_source/image/T1_page-2.png", "last sentence above item 1.1",
    "Y has a plane of symmetry"⟩

/-! ## A non-answer-shaped acidic-isomerization carrier -/

/-- Equality of two unordered pairs of atom indices. -/
def SameUnorderedPair {n : ℕ} (i j k l : Fin n) : Prop :=
  (i = k ∧ j = l) ∨ (i = l ∧ j = k)

instance sameUnorderedPairDecidable {n : ℕ} (i j k l : Fin n) :
    Decidable (SameUnorderedPair i j k l) := by
  unfold SameUnorderedPair
  infer_instance

/-- A structural witness for the qualitative acid-promoted double cyclization
of a hydroxy diene.  The definition is uniform in the two molecular diagrams:
it contains an atom relabelling and the complete bond-order matrix update.

All source bonds remain, each of the two alkene bonds becomes single, and two
new intramolecular single bonds are made: one O-C bond and one C-C bond.  No
condition mentions a numbered compound.  The carrier deliberately says
nothing about acid identity, solvent, rate, yield, completion, byproducts, or
product exclusivity. -/
structure AcidicIsomerizationWitness
    (start finish : MolecularDiagram) where
  relabel : Fin start.atoms.length ≃ Fin finish.atoms.length
  startWellFormed : start.WellFormed
  finishWellFormed : finish.WellFormed
  startConnected : start.Connected
  finishConnected : finish.Connected
  atomPreserving : ∀ i,
    start.atoms.get i = finish.atoms.get (relabel i)
  hydroxyOxygen : Fin start.atoms.length
  firstAlkeneNearO : Fin start.atoms.length
  firstAlkeneOther : Fin start.atoms.length
  secondAlkeneAnchor : Fin start.atoms.length
  secondAlkeneOther : Fin start.atoms.length
  sourceHydroxy : start.IsHydroxyOxygen hydroxyOxygen.1
  firstNearCarbon : start.atoms.get firstAlkeneNearO = .carbon
  firstOtherCarbon : start.atoms.get firstAlkeneOther = .carbon
  secondAnchorCarbon : start.atoms.get secondAlkeneAnchor = .carbon
  secondOtherCarbon : start.atoms.get secondAlkeneOther = .carbon
  sourceHasTwoDoubleBonds : start.doubleBondCount = 2
  targetHasNoDoubleBonds : finish.doubleBondCount = 0
  firstAlkene :
    start.bondOrder firstAlkeneNearO.1 firstAlkeneOther.1 = 2
  secondAlkene :
    start.bondOrder secondAlkeneAnchor.1 secondAlkeneOther.1 = 2
  alkenePairsDistinct :
    ¬ SameUnorderedPair firstAlkeneNearO firstAlkeneOther
      secondAlkeneAnchor secondAlkeneOther
  addedOxygenBondAbsent :
    start.bondOrder hydroxyOxygen.1 firstAlkeneNearO.1 = 0
  addedCarbonBondAbsent :
    start.bondOrder firstAlkeneOther.1 secondAlkeneOther.1 = 0
  productEther : finish.IsEtherOxygen (relabel hydroxyOxygen).1
  netBondRewrite : ∀ i j,
    finish.bondOrder (relabel i).1 (relabel j).1 =
      if SameUnorderedPair i j hydroxyOxygen firstAlkeneNearO ∨
          SameUnorderedPair i j firstAlkeneOther secondAlkeneOther
      then 1
      else Nat.min (start.bondOrder i.1 j.1) 1

/-- The source phrase is used as a non-exclusive qualitative compatibility
constraint.  Molecular formula equality is explicit, while the nontrivial
witness above exposes the atom map and every changed heavy-atom bond. -/
def AcidicIsomerizationCompatible (x y : CompoundId) : Prop :=
  printedFormula x = printedFormula y ∧
  Nonempty (AcidicIsomerizationWitness (compoundDiagram x) (compoundDiagram y))

/-- This target uses the stated transformation only in the
`qualitative_named_transform_only` sense. -/
inductive TransformationUse where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Repr

def acidicTransformationUse : TransformationUse :=
  .qualitativeNamedTransformOnly

/-! ## Plane-symmetry carrier -/

/-- Exact rational coordinates for an idealized finite spatial realization. -/
structure Point3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

/-- Reflection in the coordinate plane `z = 0`. -/
def Point3.reflect (p : Point3) : Point3 :=
  ⟨p.x, p.y, -p.z⟩

/-- Twice the oriented area of three points projected to the `xy` plane. -/
def Point3.xyArea2 (a b c : Point3) : ℚ :=
  (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

/-- A genuine reflection-plane witness for an idealized spatial molecular
model.  Besides atom and bond preservation, three fixed non-collinear atoms
anchor the plane and at least one atom occurs off the plane. -/
structure PlaneSymmetryWitness (d : MolecularDiagram) where
  reflection : Equiv.Perm (Fin d.atoms.length)
  position : Fin d.atoms.length → Point3
  involutive : Function.Involutive reflection
  nontrivial : ∃ i, reflection i ≠ i
  positionInjective : Function.Injective position
  reflectionGeometry : ∀ i, position (reflection i) = (position i).reflect
  fixedNoncollinear : ∃ i j k,
    reflection i = i ∧ reflection j = j ∧ reflection k = k ∧
    Point3.xyArea2 (position i) (position j) (position k) ≠ 0
  offPlane : ∃ i, (position i).z ≠ 0
  atomPreserving : ∀ i,
    d.atoms.get i = d.atoms.get (reflection i)
  bondPreserving : ∀ i j,
    d.bondOrder i.1 j.1 = d.bondOrder (reflection i).1 (reflection j).1

def HasPlaneOfSymmetry (d : MolecularDiagram) : Prop :=
  Nonempty (PlaneSymmetryWitness d)

/-- The visible framework reflection of structure 3. -/
def compound3Reflection : Equiv.Perm (Fin compound3Diagram.atoms.length) := by
  change Equiv.Perm (Fin 11)
  exact ((Equiv.swap (4 : Fin 11) 5).trans (Equiv.swap (6 : Fin 11) 7)).trans
    (Equiv.swap (9 : Fin 11) 10)

/-! The following executable checkers prove that the complete transcribed
graphs are legitimate connected molecular diagrams. -/

private def MolecularDiagram.wellFormedCheck (d : MolecularDiagram) : Bool :=
  d.bonds.all fun b =>
    decide (b.left < d.atoms.length ∧ b.right < d.atoms.length ∧
      b.left ≠ b.right ∧ (b.order = 1 ∨ b.order = 2)) &&
    d.bonds.all fun b₂ =>
      decide (({b.left, b.right} : Finset ℕ) = {b₂.left, b₂.right} → b = b₂)

private theorem MolecularDiagram.wellFormed_of_check (d : MolecularDiagram)
    (h : d.wellFormedCheck = true) : d.WellFormed := by
  rw [wellFormedCheck, List.all_eq_true] at h
  constructor
  · intro b hb
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (h b hb)).1
  · intro b₁ hb₁ b₂ hb₂ hpairs
    have hall := (Bool.and_eq_true_iff.mp (h b₁ hb₁)).2
    rw [List.all_eq_true] at hall
    exact (of_decide_eq_true (hall b₂ hb₂)) hpairs

private def MolecularDiagram.adjacentCheck
    (d : MolecularDiagram) (i j : ℕ) : Bool :=
  d.bonds.any fun b =>
    (b.left == i && b.right == j) || (b.left == j && b.right == i)

private theorem MolecularDiagram.adjacent_of_check
    (d : MolecularDiagram) {i j : ℕ} (h : d.adjacentCheck i j = true) :
    d.Adjacent i j := by
  rw [adjacentCheck, List.any_eq_true] at h
  rcases h with ⟨b, hb, hends⟩
  refine ⟨b, hb, ?_⟩
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hends

private def MolecularDiagram.expandReachable
    (d : MolecularDiagram) (seen : List ℕ) : List ℕ :=
  (List.range d.atoms.length).filter fun j =>
    seen.any fun i => d.adjacentCheck i j

private def MolecularDiagram.reachableVertices
    (d : MolecularDiagram) : ℕ → List ℕ → List ℕ
  | 0, seen => seen
  | n + 1, seen =>
      d.reachableVertices n (seen ++ d.expandReachable seen)

private theorem MolecularDiagram.expandReachable_sound
    (d : MolecularDiagram) {source : ℕ} {seen : List ℕ}
    (hseen : ∀ k ∈ seen, Relation.ReflTransGen d.Adjacent source k) :
    ∀ k ∈ d.expandReachable seen,
      Relation.ReflTransGen d.Adjacent source k := by
  intro k hk
  rw [expandReachable, List.mem_filter] at hk
  rcases hk with ⟨_, hk⟩
  rw [List.any_eq_true] at hk
  rcases hk with ⟨i, hi, hik⟩
  exact (hseen i hi).tail (d.adjacent_of_check hik)

private theorem MolecularDiagram.reachableVertices_sound
    (d : MolecularDiagram) {source : ℕ} {seen : List ℕ} {n : ℕ}
    (hseen : ∀ k ∈ seen, Relation.ReflTransGen d.Adjacent source k) :
    ∀ k ∈ d.reachableVertices n seen,
      Relation.ReflTransGen d.Adjacent source k := by
  induction n generalizing seen with
  | zero => simpa [reachableVertices] using hseen
  | succ n ih =>
      rw [reachableVertices]
      apply ih
      intro k hk
      rw [List.mem_append] at hk
      rcases hk with hk | hk
      · exact hseen k hk
      · exact d.expandReachable_sound hseen k hk

private def MolecularDiagram.connectedCheck (d : MolecularDiagram) : Bool :=
  (List.range d.atoms.length).all fun i =>
    (List.range d.atoms.length).all fun j =>
      (d.reachableVertices d.atoms.length [i]).contains j

private theorem MolecularDiagram.connected_of_check (d : MolecularDiagram)
    (h : d.connectedCheck = true) : d.Connected := by
  intro i hi j hj
  rw [connectedCheck, List.all_eq_true] at h
  have hiRow := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at hiRow
  have hij := hiRow j (List.mem_range.mpr hj)
  have hjmem : j ∈ d.reachableVertices d.atoms.length [i] :=
    List.contains_iff_mem.mp hij
  apply d.reachableVertices_sound (source := i) (seen := [i]) (n := d.atoms.length)
  · intro k hk
    simp only [List.mem_singleton] at hk
    subst k
    exact Relation.ReflTransGen.refl
  · exact hjmem

/-! ## Source-to-Lean bridge checks -/

theorem every_numbered_compound_is_displayed :
    ∀ c : CompoundId, DisplayedCandidate c := by
  intro c
  cases c with
  | c1 => exact ⟨.zingiber, Or.inl rfl⟩
  | c2 => exact ⟨.zingiber, Or.inr (Or.inl rfl)⟩
  | c3 => exact ⟨.zingiber, Or.inr (Or.inr rfl)⟩
  | c4 => exact ⟨.hypericum, Or.inl rfl⟩
  | c5 => exact ⟨.hypericum, Or.inr (Or.inl rfl)⟩
  | c6 => exact ⟨.hypericum, Or.inr (Or.inr rfl)⟩
  | c7 => exact ⟨.chamomilla, Or.inl rfl⟩
  | c8 => exact ⟨.chamomilla, Or.inr (Or.inl rfl)⟩
  | c9 => exact ⟨.artemisia, Or.inl rfl⟩
  | c10 => exact ⟨.artemisia, Or.inr (Or.inl rfl)⟩

theorem all_numbered_diagrams_wellFormed :
    ∀ c : CompoundId, (compoundDiagram c).WellFormed := by
  intro c
  apply MolecularDiagram.wellFormed_of_check
  cases c <;> native_decide

theorem all_numbered_diagrams_connected :
    ∀ c : CompoundId, (compoundDiagram c).Connected := by
  intro c
  apply MolecularDiagram.connected_of_check
  cases c <;> native_decide

/-- Independent valence recount for the nine entries whose printed formula
agrees with the visible heavy-atom graph. -/
theorem printed_formula_recounted_except_10 :
    ∀ c : CompoundId, c ≠ .c10 →
      (compoundDiagram c).derivedFormula = printedFormula c := by
  intro c hc
  cases c <;> simp_all <;> native_decide

/-- The drawing of entry 10 has two rings and one carbonyl, hence the ordinary
valence recount is C10H16O, whereas the text beneath it prints C10H18O.  The
formalization preserves both source reads and does not use this discrepancy to
select either requested output. -/
theorem compound10_formula_source_discrepancy :
    compound10Diagram.derivedFormula = ⟨10, 16, 1⟩ ∧
      printedFormula .c10 = ⟨10, 18, 1⟩ := by
  native_decide

/-- Source-to-target atom relabelling found by comparing the two complete
heavy-atom graphs, before selecting an answer. -/
def compound6To3IndexMap : Fin 11 → Fin 11 :=
  ![0, 2, 6, 4, 8, 7, 1, 3, 9, 10, 5]

def compound3To6IndexMap : Fin 11 → Fin 11 :=
  ![0, 6, 1, 7, 3, 10, 2, 5, 4, 8, 9]

def compound6To3Relabel : Equiv.Perm (Fin 11) where
  toFun := compound6To3IndexMap
  invFun := compound3To6IndexMap
  left_inv := by
    intro i
    fin_cases i <;> native_decide
  right_inv := by
    intro i
    fin_cases i <;> native_decide

/-- The explicit bond-matrix witness for the qualitative transformation. -/
def compound6_to_compound3_witness :
    AcidicIsomerizationWitness compound6Diagram compound3Diagram := by
  refine
    { relabel := compound6To3Relabel
      startWellFormed := all_numbered_diagrams_wellFormed .c6
      finishWellFormed := all_numbered_diagrams_wellFormed .c3
      startConnected := all_numbered_diagrams_connected .c6
      finishConnected := all_numbered_diagrams_connected .c3
      atomPreserving := ?_
      hydroxyOxygen := ⟨0, by native_decide⟩
      firstAlkeneNearO := ⟨7, by native_decide⟩
      firstAlkeneOther := ⟨6, by native_decide⟩
      secondAlkeneAnchor := ⟨5, by native_decide⟩
      secondAlkeneOther := ⟨10, by native_decide⟩
      sourceHydroxy := by native_decide
      firstNearCarbon := by native_decide
      firstOtherCarbon := by native_decide
      secondAnchorCarbon := by native_decide
      secondOtherCarbon := by native_decide
      sourceHasTwoDoubleBonds := by native_decide
      targetHasNoDoubleBonds := by native_decide
      firstAlkene := by native_decide
      secondAlkene := by native_decide
      alkenePairsDistinct := by native_decide
      addedOxygenBondAbsent := by native_decide
      addedCarbonBondAbsent := by native_decide
      productEther := by native_decide
      netBondRewrite := ?_ }
  · intro i
    fin_cases i <;> native_decide
  · intro i j
    fin_cases i <;> fin_cases j <;> native_decide

theorem compound6_to_compound3_compatible :
    AcidicIsomerizationCompatible .c6 .c3 := by
  exact ⟨by native_decide, ⟨compound6_to_compound3_witness⟩⟩

/-- The explicit framework reflection preserves the atom labels, every bond,
and a non-degenerate spatial plane. -/
theorem compound3Reflection_is_plane_symmetry :
    ∃ w : PlaneSymmetryWitness compound3Diagram,
      w.reflection = compound3Reflection := by
  let position : Fin 11 → Point3 := fun i =>
    match i.1 with
    | 0 => ⟨0, 0, 0⟩
    | 1 => ⟨1, 0, 0⟩
    | 2 => ⟨0, 1, 0⟩
    | 3 => ⟨1, 1, 0⟩
    | 4 => ⟨2, 0, 1⟩
    | 5 => ⟨2, 0, -1⟩
    | 6 => ⟨2, 1, 1⟩
    | 7 => ⟨2, 1, -1⟩
    | 8 => ⟨0, 2, 0⟩
    | 9 => ⟨3, 0, 1⟩
    | 10 => ⟨3, 0, -1⟩
    | _ => ⟨0, 0, 0⟩
  let witness : PlaneSymmetryWitness compound3Diagram :=
    { reflection := compound3Reflection
      position := position
      involutive := by
        intro i
        fin_cases i <;> native_decide
      nontrivial := ⟨⟨4, by native_decide⟩, by native_decide⟩
      positionInjective := by
        intro i j hij
        have hcheck :
            (List.finRange 11).all (fun i =>
              (List.finRange 11).all fun j =>
                decide (position i = position j → i = j)) = true := by
          native_decide
        rw [List.all_eq_true] at hcheck
        have hiRow := hcheck i (List.mem_finRange i)
        rw [List.all_eq_true] at hiRow
        exact (of_decide_eq_true (hiRow j (List.mem_finRange j))) hij
      reflectionGeometry := by
        intro i
        fin_cases i <;> native_decide
      fixedNoncollinear := by
        refine ⟨⟨0, by native_decide⟩, ⟨1, by native_decide⟩,
          ⟨2, by native_decide⟩, ?_, ?_, ?_, ?_⟩
        · native_decide
        · native_decide
        · native_decide
        · norm_num [position, Point3.xyArea2]
      offPlane := ⟨⟨4, by native_decide⟩, by norm_num [position]⟩
      atomPreserving := by
        intro i
        fin_cases i <;> native_decide
      bondPreserving := by
        intro i j
        fin_cases i <;> fin_cases j <;> native_decide }
  exact ⟨witness, rfl⟩

theorem compound3_has_plane_of_symmetry :
    HasPlaneOfSymmetry compound3Diagram := by
  rcases compound3Reflection_is_plane_symmetry with ⟨w, _⟩
  exact ⟨w⟩

private theorem compound2_has_no_ether_oxygen :
    ¬ ∃ o, compound2Diagram.IsEtherOxygen o := by
  rintro ⟨o, hoatom, hedge, _⟩
  obtain ⟨holt, _⟩ := List.getElem?_eq_some_iff.mp hoatom
  change o < 11 at holt
  interval_cases o <;>
    norm_num [compound2Diagram, carbonAtoms,
      MolecularDiagram.incidentEdgeCount, single] at hoatom hedge
  all_goals cases hoatom

/-- Uniform elimination over the ten-by-ten source domain.  The input side is
selected by the two explicit alkene bonds in the witness.  Formula equality,
target saturation, and the product ether oxygen then eliminate every target
except structure 3. -/
theorem acidic_isomerization_pair_identified
    {x y : CompoundId} (h : AcidicIsomerizationCompatible x y) :
    x = .c6 ∧ y = .c3 := by
  rcases h with ⟨hformula, ⟨w⟩⟩
  have hx : x = .c6 := by
    have hd := w.sourceHasTwoDoubleBonds
    cases x with
    | c1 => exact False.elim ((by native_decide :
        (compoundDiagram .c1).doubleBondCount ≠ 2) hd)
    | c2 => exact False.elim ((by native_decide :
        (compoundDiagram .c2).doubleBondCount ≠ 2) hd)
    | c3 => exact False.elim ((by native_decide :
        (compoundDiagram .c3).doubleBondCount ≠ 2) hd)
    | c4 => exact False.elim ((by native_decide :
        (compoundDiagram .c4).doubleBondCount ≠ 2) hd)
    | c5 => exact False.elim ((by native_decide :
        (compoundDiagram .c5).doubleBondCount ≠ 2) hd)
    | c6 => rfl
    | c7 => exact False.elim ((by native_decide :
        (compoundDiagram .c7).doubleBondCount ≠ 2) hd)
    | c8 => exact False.elim ((by native_decide :
        (compoundDiagram .c8).doubleBondCount ≠ 2) hd)
    | c9 => exact False.elim ((by native_decide :
        (compoundDiagram .c9).doubleBondCount ≠ 2) hd)
    | c10 => exact False.elim ((by native_decide :
        (compoundDiagram .c10).doubleBondCount ≠ 2) hd)
  subst x
  refine ⟨rfl, ?_⟩
  cases y with
  | c1 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c1) hformula)
  | c2 => exact False.elim (compound2_has_no_ether_oxygen
      ⟨(w.relabel w.hydroxyOxygen).1, w.productEther⟩)
  | c3 => rfl
  | c4 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c4) hformula)
  | c5 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c5) hformula)
  | c6 => exact False.elim ((by native_decide :
      (compoundDiagram .c6).doubleBondCount ≠ 0) w.targetHasNoDoubleBonds)
  | c7 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c7) hformula)
  | c8 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c8) hformula)
  | c9 => exact False.elim ((by native_decide :
      printedFormula .c6 ≠ printedFormula .c9) hformula)
  | c10 => exact False.elim ((by native_decide :
      (compoundDiagram .c10).doubleBondCount ≠ 0) w.targetHasNoDoubleBonds)

/-! ## Complete source observation and requested outputs -/

/-- Pairwise distinctness of the four chromatographic substances X, Y, Z, W. -/
def PairwiseDistinctFour (x y z w : CompoundId) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w

/-- One complete assignment of the four observed chromatographic components.
Every component is a member of the ten-element image-derived type; the two
decisive qualitative facts retain their exact source locators. -/
structure SourceAssignment where
  x : CompoundId
  y : CompoundId
  z : CompoundId
  w : CompoundId
  xDisplayed : LocatedFact tableLocator (DisplayedCandidate x)
  yDisplayed : LocatedFact tableLocator (DisplayedCandidate y)
  zDisplayed : LocatedFact tableLocator (DisplayedCandidate z)
  wDisplayed : LocatedFact tableLocator (DisplayedCandidate w)
  different : LocatedFact chromatographyLocator (PairwiseDistinctFour x y z w)
  acidic : LocatedFact acidicIsomerizationLocator
    (AcidicIsomerizationCompatible x y)
  symmetric : LocatedFact symmetryLocator
    (HasPlaneOfSymmetry (compoundDiagram y))

def SatisfiesSourceObservations (x y : CompoundId) : Prop :=
  ∃ obs : SourceAssignment, obs.x = x ∧ obs.y = y

def selectedSourceAssignment : SourceAssignment where
  x := .c6
  y := .c3
  z := .c1
  w := .c2
  xDisplayed := ⟨every_numbered_compound_is_displayed .c6⟩
  yDisplayed := ⟨every_numbered_compound_is_displayed .c3⟩
  zDisplayed := ⟨every_numbered_compound_is_displayed .c1⟩
  wDisplayed := ⟨every_numbered_compound_is_displayed .c2⟩
  different := ⟨by simp [PairwiseDistinctFour]⟩
  acidic := ⟨compound6_to_compound3_compatible⟩
  symmetric := ⟨compound3_has_plane_of_symmetry⟩

theorem identify_X_and_Y (obs : SourceAssignment) :
    obs.x = .c6 ∧ obs.y = .c3 := by
  exact acidic_isomerization_pair_identified obs.acidic.proof

/-- Finite uniform audit of every ordered pair from the ten displayed
structures. -/
theorem acidic_symmetric_pair_unique :
    ∃! p : CompoundId × CompoundId,
      SatisfiesSourceObservations p.1 p.2 := by
  refine ⟨(.c6, .c3), ⟨selectedSourceAssignment, rfl, rfl⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨obs, hx, hy⟩
  rcases identify_X_and_Y obs with ⟨hox, hoy⟩
  simp only [Prod.mk.injEq]
  exact ⟨hx.symm.trans hox, hy.symm.trans hoy⟩

/-- A candidate pair is realized and every complete source assignment gives
that same ordered pair.  The candidate occurs only in this conclusion. -/
def IsIdentification (answerX answerY : CompoundId) : Prop :=
  (∃ obs : SourceAssignment, obs.x = answerX ∧ obs.y = answerY) ∧
  ∀ obs : SourceAssignment, obs.x = answerX ∧ obs.y = answerY

/-- Combined raw exact-symbolic result for the two requested outputs. -/
def RawIdentificationResult : Prop :=
  IsIdentification .c6 .c3

/-- Requested output carrier for the identity of X. -/
def IdentityXResult : Prop :=
  (∃ obs : SourceAssignment, obs.x = .c6) ∧
  ∀ obs : SourceAssignment, obs.x = .c6

/-- Requested output carrier for the identity of Y. -/
def IdentityYResult : Prop :=
  (∃ obs : SourceAssignment, obs.y = .c3) ∧
  ∀ obs : SourceAssignment, obs.y = .c3

/-- Exact-symbolic reporting preserves both classifications unchanged. -/
def ReportedIdentificationResult : Prop :=
  IdentityXResult ∧ IdentityYResult

theorem raw_identification_result : RawIdentificationResult := by
  refine ⟨⟨selectedSourceAssignment, rfl, rfl⟩, ?_⟩
  intro obs
  exact identify_X_and_Y obs

theorem identity_x_result : IdentityXResult := by
  refine ⟨⟨selectedSourceAssignment, rfl⟩, ?_⟩
  intro obs
  exact (identify_X_and_Y obs).1

theorem identity_y_result : IdentityYResult := by
  refine ⟨⟨selectedSourceAssignment, rfl⟩, ?_⟩
  intro obs
  exact (identify_X_and_Y obs).2

theorem reported_identification_result : ReportedIdentificationResult := by
  exact ⟨identity_x_result, identity_y_result⟩

/- The two payload strings below are regenerated with Archon's trusted helper
after the synchronized answer-blind candidate is written. -/
theorem raw_result_contract :
    ("8dfd2b7a55f30b42a0640f2d1a2f5b6343b8d245898e240ec255fcc786f05175" : String) =
      "8dfd2b7a55f30b42a0640f2d1a2f5b6343b8d245898e240ec255fcc786f05175" ∧
      RawIdentificationResult := by
  exact ⟨rfl, raw_identification_result⟩

theorem reported_result_contract :
    ("e2bc1b7ccc1e3489e1800734d8f8a7c3f545387d787c27565e8c78850cd11537" : String) =
      "e2bc1b7ccc1e3489e1800734d8f8a7c3f545387d787c27565e8c78850cd11537" ∧
      ReportedIdentificationResult := by
  exact ⟨rfl, reported_identification_result⟩

end IChO2026Problems.Icho2026T1A1
