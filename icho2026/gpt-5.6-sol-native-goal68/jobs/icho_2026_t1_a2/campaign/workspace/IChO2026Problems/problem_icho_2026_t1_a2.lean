import Mathlib

/-!
# IChO 2026 T1-A2: chamazulene, azulene, and naphthalene

This file keeps the printed problem data separate from the derived answer.
The mass-spectrum elimination is performed over all ten printed candidates.
The three requested structures are finite molecular graphs: every atom has an
element, formal charge, radical count, and stereochemical annotation, and every
bond has an order and stereochemical annotation.  Aromatic bonds are represented
as aromatic in the molecular graph; an explicit valid Kekule form is supplied
for each graph so that the alternating single/double-bond drawing and ordinary
valences are also checked.

The geometry used for the symmetry clues is an exact integral planar embedding.
The listed reflections preserve atoms and aromatic bond types, not merely an
unlabelled graph.
-/

namespace IChO2026T1A2

/-! ## Chemical structures -/

inductive Element
  | hydrogen
  | carbon
  | oxygen
  | chlorine
  deriving DecidableEq, Repr

inductive AtomStereo
  | none
  | clockwise
  | anticlockwise
  deriving DecidableEq, Repr

structure Atom where
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  stereo : AtomStereo
  deriving DecidableEq, Repr

def neutralAtom (e : Element) : Atom :=
  ⟨e, 0, 0, .none⟩

inductive BondOrder
  | single
  | double
  | aromatic
  deriving DecidableEq, Repr

inductive BondStereo
  | none
  | up
  | down
  | together
  | opposite
  deriving DecidableEq, Repr

structure Bond where
  order : BondOrder
  stereo : BondStereo
  deriving DecidableEq, Repr

def singleBond : Bond := ⟨.single, .none⟩
def aromaticBond : Bond := ⟨.aromatic, .none⟩

structure Molecule where
  atomCount : Nat
  atom : Fin atomCount → Atom
  bond : Fin atomCount → Fin atomCount → Option Bond

abbrev EdgeList := List (Nat × Nat)

/-- Membership in an undirected list of edges. -/
def containsUndirected (edges : EdgeList) (i j : Nat) : Bool :=
  edges.any fun e =>
    (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)

def bondMap {n : Nat} (aromaticEdges singleEdges : EdgeList)
    (i j : Fin n) : Option Bond :=
  if containsUndirected aromaticEdges i.val j.val then
    some aromaticBond
  else if containsUndirected singleEdges i.val j.val then
    some singleBond
  else
    none

def neutralHydrocarbonAtom {n : Nat} (carbonCount : Nat) (i : Fin n) : Atom :=
  if i.val < carbonCount then neutralAtom .carbon else neutralAtom .hydrogen

structure MolecularFormula where
  C : Nat
  H : Nat
  O : Nat
  Cl : Nat
  deriving DecidableEq, Repr

def countElement (m : Molecule) (e : Element) : Nat :=
  (Finset.univ.filter fun i => (m.atom i).element = e).card

def HasFormula (m : Molecule) (f : MolecularFormula) : Prop :=
  countElement m .carbon = f.C ∧
  countElement m .hydrogen = f.H ∧
  countElement m .oxygen = f.O ∧
  countElement m .chlorine = f.Cl

def NeutralClosedShell (m : Molecule) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    decide ((m.atom i).formalCharge = 0) &&
    decide ((m.atom i).radicalElectrons = 0)) = true

def NoAtomStereocentres (m : Molecule) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    decide ((m.atom i).stereo = .none)) = true

def NoBondStereochemistry (m : Molecule) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    (List.finRange m.atomCount).all fun j =>
    match m.bond i j with
    | none => true
    | some b => decide (b.stereo = .none)) = true

def SymmetricBonds (m : Molecule) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    (List.finRange m.atomCount).all fun j =>
    decide (m.bond i j = m.bond j i)) = true

def NoSelfBonds (m : Molecule) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    decide (m.bond i i = none)) = true

/-- A Kekule form selects which aromatic edges are drawn double. -/
def kekuleMultiplicity (m : Molecule) (doubleEdges : EdgeList)
    (i j : Fin m.atomCount) : Nat :=
  match m.bond i j with
  | none => 0
  | some b =>
      match b.order with
      | .single => 1
      | .double => 2
      | .aromatic =>
          if containsUndirected doubleEdges i.val j.val then 2 else 1

def normalValence (a : Atom) : Nat :=
  match a.element with
  | .hydrogen => 1
  | .carbon => 4
  | .oxygen => 2
  | .chlorine => 1

def ValidKekuleForm (m : Molecule) (doubleEdges : EdgeList) : Prop :=
  ((List.finRange m.atomCount).all fun i =>
    (List.finRange m.atomCount).all fun j =>
    !containsUndirected doubleEdges i.val j.val ||
      decide ((m.bond i j).map Bond.order = some .aromatic)) = true ∧
  ((List.finRange m.atomCount).all fun i => decide
    ((Finset.univ.sum fun j => kekuleMultiplicity m doubleEdges i j) =
      normalValence (m.atom i))) = true

def CompleteStructure (m : Molecule) (f : MolecularFormula)
    (doubleEdges : EdgeList) : Prop :=
  HasFormula m f ∧
  NeutralClosedShell m ∧
  NoAtomStereocentres m ∧
  NoBondStereochemistry m ∧
  SymmetricBonds m ∧
  NoSelfBonds m ∧
  ValidKekuleForm m doubleEdges

/-! ### The three explicit molecular graphs

Carbon atoms are numbered first, followed by explicit hydrogen atoms.
For azulene and chamazulene, carbon indices `0,...,9` run around the
ten-member perimeter and `(2,6)` is the shared edge of the five- and
seven-membered rings.  The azulene positions bearing substituents in
chamazulene are `3` (position 1), `7` (position 4), and `0` (position 7).
-/

def azulenePerimeter : EdgeList :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
   (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)]

def azuleneAromaticEdges : EdgeList :=
  azulenePerimeter ++ [(2, 6)]

def azuleneHydrogenEdges : EdgeList :=
  [(0, 10), (1, 11), (3, 12), (4, 13),
   (5, 14), (7, 15), (8, 16), (9, 17)]

def azulene : Molecule where
  atomCount := 18
  atom := neutralHydrocarbonAtom 10
  bond := bondMap azuleneAromaticEdges azuleneHydrogenEdges

def azuleneKekuleDoubles : EdgeList :=
  [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]

def naphthalenePerimeter : EdgeList := azulenePerimeter

def naphthaleneAromaticEdges : EdgeList :=
  naphthalenePerimeter ++ [(2, 7)]

def naphthaleneHydrogenEdges : EdgeList :=
  [(0, 10), (1, 11), (3, 12), (4, 13),
   (5, 14), (6, 15), (8, 16), (9, 17)]

def naphthalene : Molecule where
  atomCount := 18
  atom := neutralHydrocarbonAtom 10
  bond := bondMap naphthaleneAromaticEdges naphthaleneHydrogenEdges

def naphthaleneKekuleDoubles : EdgeList :=
  [(0, 1), (2, 7), (3, 4), (5, 6), (8, 9)]

/-- Chamazulene: 7-ethyl-1,4-dimethylazulene.

Carbons `0,...,9` are the azulene core.  `0-10-11` is the ethyl group;
`3-12` and `7-13` are the two methyl groups. -/
def chamazuleneSingleEdges : EdgeList :=
  [(0, 10), (10, 11), (3, 12), (7, 13),
   (1, 14), (4, 15), (5, 16), (8, 17), (9, 18),
   (10, 19), (10, 20),
   (11, 21), (11, 22), (11, 23),
   (12, 24), (12, 25), (12, 26),
   (13, 27), (13, 28), (13, 29)]

def chamazulene : Molecule where
  atomCount := 30
  atom := neutralHydrocarbonAtom 14
  bond := bondMap azuleneAromaticEdges chamazuleneSingleEdges

def chamazuleneKekuleDoubles : EdgeList := azuleneKekuleDoubles

def c10h8 : MolecularFormula := ⟨10, 8, 0, 0⟩
def c14h16 : MolecularFormula := ⟨14, 16, 0, 0⟩

theorem azulene_complete :
    CompleteStructure azulene c10h8 azuleneKekuleDoubles := by
  unfold CompleteStructure NeutralClosedShell NoAtomStereocentres
    NoBondStereochemistry SymmetricBonds NoSelfBonds ValidKekuleForm HasFormula
  decide

theorem naphthalene_complete :
    CompleteStructure naphthalene c10h8 naphthaleneKekuleDoubles := by
  unfold CompleteStructure NeutralClosedShell NoAtomStereocentres
    NoBondStereochemistry SymmetricBonds NoSelfBonds ValidKekuleForm HasFormula
  decide

theorem chamazulene_complete :
    CompleteStructure chamazulene c14h16 chamazuleneKekuleDoubles := by
  unfold CompleteStructure NeutralClosedShell NoAtomStereocentres
    NoBondStereochemistry SymmetricBonds NoSelfBonds ValidKekuleForm HasFormula
  decide

/-! ## Problem data: the ten printed molecular formulae and the mass spectrum -/

inductive Candidate
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Repr

def Candidate.formula : Candidate → MolecularFormula
  | .c1 => ⟨11, 14, 3, 0⟩
  | .c2 => ⟨10, 18, 1, 0⟩
  | .c3 => ⟨10, 18, 1, 0⟩
  | .c4 => ⟨6, 12, 1, 0⟩
  | .c5 => ⟨10, 12, 2, 0⟩
  | .c6 => ⟨10, 18, 1, 0⟩
  | .c7 => ⟨14, 16, 0, 0⟩
  | .c8 => ⟨15, 24, 0, 0⟩
  | .c9 => ⟨10, 16, 1, 0⟩
  | .c10 => ⟨10, 18, 1, 0⟩

/-- Nominal masses used by the printed integer-m/z isotope clue. -/
def nominalMass (f : MolecularFormula) : Nat :=
  12 * f.C + f.H + 16 * f.O + 35 * f.Cl

/-- Mass after monochlorination by replacement of one hydrogen, using the
specified chlorine isotope mass. -/
def monochloroNominalMass (f : MolecularFormula) (chlorineMass : Nat) : Nat :=
  12 * f.C + (f.H - 1) + 16 * f.O + chlorineMass

/-- With natural chlorine abundance approximately 3:1, a molecule containing
one chlorine gives these two molecular-ion peak weights. -/
def monochloroPattern (f : MolecularFormula) : List (Nat × Nat) :=
  [(monochloroNominalMass f 35, 3),
   (monochloroNominalMass f 37, 1)]

def printedPattern : List (Nat × Nat) := [(218, 3), (220, 1)]

def FitsPrintedMassSpectrum (c : Candidate) : Prop :=
  monochloroPattern c.formula = printedPattern

theorem one_chlorine_has_two_peaks_and_ratio_three_to_one :
    monochloroPattern c14h16 = [(218, 3), (220, 1)] := by
  decide

theorem identify_Z_from_mass_spectrum (z : Candidate)
    (hobs : FitsPrintedMassSpectrum z) : z = .c7 := by
  cases z <;>
    simp_all [FitsPrintedMassSpectrum, monochloroPattern,
      monochloroNominalMass, Candidate.formula, printedPattern]

theorem candidate7_is_unique_mass_match (z : Candidate) :
    FitsPrintedMassSpectrum z ↔ z = .c7 := by
  cases z <;>
    simp [FitsPrintedMassSpectrum, monochloroPattern,
      monochloroNominalMass, Candidate.formula, printedPattern]

theorem candidate7_formula_is_chamazulene_formula :
    Candidate.formula .c7 = c14h16 ∧ HasFormula chamazulene c14h16 := by
  exact ⟨rfl, chamazulene_complete.1⟩

/-! ## The derivative relation identifies A's azulene core -/

def embedAzuleneCoreInChamazulene (i : Fin 10) : Fin chamazulene.atomCount :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

def embedAzuleneCoreInAzulene (i : Fin 10) : Fin azulene.atomCount :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

def HasSameTenCarbonAromaticCore (large small : Molecule)
    (embedLarge : Fin 10 → Fin large.atomCount)
    (embedSmall : Fin 10 → Fin small.atomCount) : Prop :=
  ((List.finRange 10).all fun i => decide
    (large.atom (embedLarge i) = small.atom (embedSmall i))) = true ∧
  ((List.finRange 10).all fun i => (List.finRange 10).all fun j => decide
    (large.bond (embedLarge i) (embedLarge j) =
      small.bond (embedSmall i) (embedSmall j))) = true

theorem chamazulene_has_azulene_core :
    HasSameTenCarbonAromaticCore chamazulene azulene
      embedAzuleneCoreInChamazulene embedAzuleneCoreInAzulene := by
  unfold HasSameTenCarbonAromaticCore
  decide

theorem chamazulene_substitution_bonds :
    chamazulene.bond ⟨0, by decide⟩ ⟨10, by decide⟩ = some singleBond ∧
    chamazulene.bond ⟨10, by decide⟩ ⟨11, by decide⟩ = some singleBond ∧
    chamazulene.bond ⟨3, by decide⟩ ⟨12, by decide⟩ = some singleBond ∧
    chamazulene.bond ⟨7, by decide⟩ ⟨13, by decide⟩ = some singleBond := by
  decide

/-! ## Exact reflection symmetries -/

structure Coord3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

inductive AxisNormal
  | x | y | z
  deriving DecidableEq, Repr

def reflect : AxisNormal → Coord3 → Coord3
  | .x, p => ⟨-p.x, p.y, p.z⟩
  | .y, p => ⟨p.x, -p.y, p.z⟩
  | .z, p => ⟨p.x, p.y, -p.z⟩

structure EmbeddedMolecule where
  molecule : Molecule
  coord : Fin molecule.atomCount → Coord3

def IsMirrorPlane (em : EmbeddedMolecule) (normal : AxisNormal)
    (perm : Fin em.molecule.atomCount → Fin em.molecule.atomCount) : Prop :=
  ((List.finRange em.molecule.atomCount).all fun i =>
    decide (perm (perm i) = i)) = true ∧
  ((List.finRange em.molecule.atomCount).all fun i => decide
    (em.coord (perm i) = reflect normal (em.coord i))) = true ∧
  ((List.finRange em.molecule.atomCount).all fun i => decide
    (em.molecule.atom (perm i) = em.molecule.atom i)) = true ∧
  ((List.finRange em.molecule.atomCount).all fun i =>
    (List.finRange em.molecule.atomCount).all fun j => decide
    (em.molecule.bond (perm i) (perm j) = em.molecule.bond i j)) = true

/-- The coordinate axes are stipulated orthogonal, so distinct coordinate
plane normals specify perpendicular planes. -/
def PerpendicularPlanes (a b : AxisNormal) : Prop := a ≠ b

def azuleneCoord (i : Fin azulene.atomCount) : Coord3 :=
  ![⟨-3, 0, 0⟩, ⟨-2, 2, 0⟩, ⟨-1, 4, 0⟩,
    ⟨-1, 5, 0⟩, ⟨0, 6, 0⟩, ⟨1, 5, 0⟩,
    ⟨1, 4, 0⟩, ⟨2, 2, 0⟩, ⟨3, 0, 0⟩, ⟨0, -2, 0⟩,
    ⟨-4, 0, 0⟩, ⟨-3, 3, 0⟩, ⟨-2, 6, 0⟩, ⟨0, 7, 0⟩,
    ⟨2, 6, 0⟩, ⟨3, 3, 0⟩, ⟨4, 0, 0⟩, ⟨0, -3, 0⟩] i

def azuleneEmbedded : EmbeddedMolecule := ⟨azulene, azuleneCoord⟩

def azuleneMirrorX (i : Fin 18) : Fin 18 :=
  ![8, 7, 6, 5, 4, 3, 2, 1, 0, 9, 16, 15, 14, 13, 12, 11, 10, 17] i

def identity18 (i : Fin 18) : Fin 18 := i

theorem azulene_two_perpendicular_planes :
    IsMirrorPlane azuleneEmbedded .x azuleneMirrorX ∧
    IsMirrorPlane azuleneEmbedded .z identity18 ∧
    PerpendicularPlanes .x .z := by
  unfold IsMirrorPlane PerpendicularPlanes
  decide

def naphthaleneCoord (i : Fin naphthalene.atomCount) : Coord3 :=
  ![⟨-4, 1, 0⟩, ⟨-2, 2, 0⟩, ⟨0, 1, 0⟩, ⟨2, 2, 0⟩,
    ⟨4, 1, 0⟩, ⟨4, -1, 0⟩, ⟨2, -2, 0⟩, ⟨0, -1, 0⟩,
    ⟨-2, -2, 0⟩, ⟨-4, -1, 0⟩,
    ⟨-5, 1, 0⟩, ⟨-3, 3, 0⟩, ⟨3, 3, 0⟩, ⟨5, 1, 0⟩,
    ⟨5, -1, 0⟩, ⟨3, -3, 0⟩, ⟨-3, -3, 0⟩, ⟨-5, -1, 0⟩] i

def naphthaleneEmbedded : EmbeddedMolecule := ⟨naphthalene, naphthaleneCoord⟩

def naphthaleneMirrorX (i : Fin 18) : Fin 18 :=
  ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5, 13, 12, 11, 10, 17, 16, 15, 14] i

def naphthaleneMirrorY (i : Fin 18) : Fin 18 :=
  ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 17, 16, 15, 14, 13, 12, 11, 10] i

theorem naphthalene_three_mutually_perpendicular_planes :
    IsMirrorPlane naphthaleneEmbedded .x naphthaleneMirrorX ∧
    IsMirrorPlane naphthaleneEmbedded .y naphthaleneMirrorY ∧
    IsMirrorPlane naphthaleneEmbedded .z identity18 ∧
    PerpendicularPlanes .x .y ∧
    PerpendicularPlanes .x .z ∧
    PerpendicularPlanes .y .z := by
  unfold IsMirrorPlane PerpendicularPlanes
  decide

/-! ## The azulene-to-naphthalene structural isomerization -/

def bondAt (m : Molecule) (i j : Nat) : Option Bond :=
  if hi : i < m.atomCount then
    if hj : j < m.atomCount then m.bond ⟨i, hi⟩ ⟨j, hj⟩ else none
  else
    none

def atomAt (m : Molecule) (i : Nat) : Option Atom :=
  if hi : i < m.atomCount then some (m.atom ⟨i, hi⟩) else none

def fusionShiftChangedEdges : EdgeList :=
  [(2, 6), (2, 7), (7, 15), (6, 15)]

def IsAzuleneNaphthaleneFusionShift (a b : Molecule) : Prop :=
  a.atomCount = 18 ∧ b.atomCount = 18 ∧
  HasFormula a c10h8 ∧ HasFormula b c10h8 ∧
  bondAt a 2 6 = some aromaticBond ∧
  bondAt b 2 6 = none ∧
  bondAt a 2 7 = none ∧
  bondAt b 2 7 = some aromaticBond ∧
  bondAt a 7 15 = some singleBond ∧
  bondAt b 7 15 = none ∧
  bondAt a 6 15 = none ∧
  bondAt b 6 15 = some singleBond ∧
  ((List.finRange 18).all fun i => decide (atomAt a i = atomAt b i)) = true ∧
  ((List.finRange 18).all fun i => (List.finRange 18).all fun j =>
    containsUndirected fusionShiftChangedEdges i.val j.val ||
      decide (bondAt a i j = bondAt b i j)) = true

theorem azulene_isomerizes_structurally_to_naphthalene :
    IsAzuleneNaphthaleneFusionShift azulene naphthalene := by
  unfold IsAzuleneNaphthaleneFusionShift HasFormula
  decide

theorem azulene_and_naphthalene_are_distinct_isomers :
    HasFormula azulene c10h8 ∧
    HasFormula naphthalene c10h8 ∧
    azulene.bond ⟨2, by decide⟩ ⟨6, by decide⟩ ≠
      naphthalene.bond ⟨2, by decide⟩ ⟨6, by decide⟩ := by
  unfold HasFormula
  decide

/-! ## Final bundled result -/

theorem icho_2026_t1_a2 (z : Candidate)
    (hobs : FitsPrintedMassSpectrum z) :
    z = .c7 ∧
    Candidate.formula z = c14h16 ∧
    CompleteStructure chamazulene c14h16 chamazuleneKekuleDoubles ∧
    HasSameTenCarbonAromaticCore chamazulene azulene
      embedAzuleneCoreInChamazulene embedAzuleneCoreInAzulene ∧
    CompleteStructure azulene c10h8 azuleneKekuleDoubles ∧
    IsAzuleneNaphthaleneFusionShift azulene naphthalene ∧
    CompleteStructure naphthalene c10h8 naphthaleneKekuleDoubles ∧
    (IsMirrorPlane azuleneEmbedded .x azuleneMirrorX ∧
      IsMirrorPlane azuleneEmbedded .z identity18 ∧
      PerpendicularPlanes .x .z) ∧
    (IsMirrorPlane naphthaleneEmbedded .x naphthaleneMirrorX ∧
      IsMirrorPlane naphthaleneEmbedded .y naphthaleneMirrorY ∧
      IsMirrorPlane naphthaleneEmbedded .z identity18 ∧
      PerpendicularPlanes .x .y ∧
      PerpendicularPlanes .x .z ∧
      PerpendicularPlanes .y .z) := by
  have hz : z = .c7 := identify_Z_from_mass_spectrum z hobs
  subst z
  exact ⟨rfl,
    rfl,
    chamazulene_complete,
    chamazulene_has_azulene_core,
    azulene_complete,
    azulene_isomerizes_structurally_to_naphthalene,
    naphthalene_complete,
    azulene_two_perpendicular_planes,
    naphthalene_three_mutually_perpendicular_planes⟩

#print axioms identify_Z_from_mass_spectrum
#print axioms chamazulene_complete
#print axioms azulene_complete
#print axioms naphthalene_complete
#print axioms azulene_two_perpendicular_planes
#print axioms naphthalene_three_mutually_perpendicular_planes
#print axioms azulene_isomerizes_structurally_to_naphthalene
#print axioms icho_2026_t1_a2

end IChO2026T1A2
