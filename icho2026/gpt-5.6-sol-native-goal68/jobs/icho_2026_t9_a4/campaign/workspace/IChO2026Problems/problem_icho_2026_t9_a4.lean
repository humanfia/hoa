import Mathlib

/-!
# IChO 2026 T9-A4: structure of Y

The problem gives α-cyclodextrin (six α-(1→4)-linked D-glucopyranosyl
units), six equivalents of TBSCl, twelve equivalents of NaH, six
equivalents of TsCl, and the formula `C72H132O24Si6` for `Y`.  The displayed
next step hydrolyses `Y` to α-cycloaltrin.

This file models the resulting sixfold 6-O-TBS-protected 2,3-anhydro
α-cyclomannin.  It records every atom (including hydrogen), every bond, the
absence of charge and radicals, and the stereochemical face of every
stereocentre on the chair template.  The reaction-level description and the
atom graph are kept separate and are checked against one another through the
formula and connectivity theorems below.
-/

namespace IChO2026Problems.Icho2026T9A4

/-! ## Atom-level representation of the proposed structure -/

inductive Element
  | C | H | O | Si
  deriving DecidableEq, Fintype, Repr

inductive BondOrder
  | single | double | triple
  deriving DecidableEq, Fintype, Repr

/-- The seventeen heavy-atom sites in one repeat.  `linkO` is the
α-(1→4)-glycosidic oxygen whose anomeric carbon belongs to this repeat.
The six carbon sites after `si` are the tert-butyldimethylsilyl carbons. -/
inductive HeavySite
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO | linkO | epoxideO | o6
  | si | siMe1 | siMe2 | tertC | tertMe1 | tertMe2 | tertMe3
  deriving DecidableEq, Fintype, Repr

abbrev UnitId := Fin 6
abbrev HydrogenId := Fin 22

/-- All atoms of Y.  There are six copies of seventeen heavy sites and
twenty-two explicitly indexed hydrogen sites. -/
abbrev Atom := UnitId × (HeavySite ⊕ HydrogenId)

def heavy (i : UnitId) (s : HeavySite) : Atom := (i, Sum.inl s)
def hydrogen (i : UnitId) (h : HydrogenId) : Atom := (i, Sum.inr h)

def heavyElement : HeavySite → Element
  | .c1 | .c2 | .c3 | .c4 | .c5 | .c6
  | .siMe1 | .siMe2 | .tertC | .tertMe1 | .tertMe2 | .tertMe3 => .C
  | .ringO | .linkO | .epoxideO | .o6 => .O
  | .si => .Si

def atomElement (a : Atom) : Element :=
  match a.2 with
  | Sum.inl s => heavyElement s
  | Sum.inr _ => .H

/-- The owner of each explicitly represented hydrogen in a repeat:
H0--H4 are on C1--C5; H5--H6 are on C6; the remaining fifteen hydrogens
are on the five methyl groups of TBS. -/
def hydrogenOwner (h : HydrogenId) : HeavySite :=
  match h.1 with
  | 0 => .c1
  | 1 => .c2
  | 2 => .c3
  | 3 => .c4
  | 4 => .c5
  | 5 | 6 => .c6
  | 7 | 8 | 9 => .siMe1
  | 10 | 11 | 12 => .siMe2
  | 13 | 14 | 15 => .tertMe1
  | 16 | 17 | 18 => .tertMe2
  | _ => .tertMe3

def eqb {α : Type} [DecidableEq α] (a b : α) : Bool := decide (a = b)

def UnorderedPair {α : Type} [DecidableEq α] (a b x y : α) : Bool :=
  (eqb a x && eqb b y) || (eqb a y && eqb b x)

/-- Exact within-repeat heavy-atom edges.  In particular, C2--O(epoxide)
and C3--O(epoxide) are the two sides of the fused oxirane, and O6--Si plus
the six-carbon silicon substituent is a complete TBS group. -/
def InternalHeavyPair (a b : HeavySite) : Bool :=
  UnorderedPair a b .c1 .c2 ||
  UnorderedPair a b .c2 .c3 ||
  UnorderedPair a b .c3 .c4 ||
  UnorderedPair a b .c4 .c5 ||
  UnorderedPair a b .c5 .ringO ||
  UnorderedPair a b .ringO .c1 ||
  UnorderedPair a b .c5 .c6 ||
  UnorderedPair a b .c6 .o6 ||
  UnorderedPair a b .o6 .si ||
  UnorderedPair a b .si .siMe1 ||
  UnorderedPair a b .si .siMe2 ||
  UnorderedPair a b .si .tertC ||
  UnorderedPair a b .tertC .tertMe1 ||
  UnorderedPair a b .tertC .tertMe2 ||
  UnorderedPair a b .tertC .tertMe3 ||
  UnorderedPair a b .c2 .epoxideO ||
  UnorderedPair a b .c3 .epoxideO ||
  UnorderedPair a b .c1 .linkO

def nextUnit (i : UnitId) : UnitId :=
  ⟨(i.1 + 1) % 6, Nat.mod_lt _ (by decide)⟩

/-- `Bonded a b order` is the complete bond relation of Y.  The last two
heavy-heavy cases close the macrocycle: `linkO i` joins `C1 i` to
`C4 (i+1 mod 6)`.  The mixed cases add every C--H bond explicitly. -/
def Bonded (a b : Atom) (order : BondOrder) : Bool :=
  eqb order .single &&
  match a.2, b.2 with
  | Sum.inl sa, Sum.inl sb =>
      (eqb a.1 b.1 && InternalHeavyPair sa sb) ||
      (eqb sa .linkO && eqb sb .c4 && eqb b.1 (nextUnit a.1)) ||
      (eqb sb .linkO && eqb sa .c4 && eqb a.1 (nextUnit b.1))
  | Sum.inl sa, Sum.inr hb =>
      eqb a.1 b.1 && eqb (hydrogenOwner hb) sa
  | Sum.inr ha, Sum.inl sb =>
      eqb a.1 b.1 && eqb (hydrogenOwner ha) sb
  | Sum.inr _, Sum.inr _ => false

def formalCharge (_ : Atom) : Int := 0
def radicalElectrons (_ : Atom) : Nat := 0

/-- Coordination number, counting the exact neighbor relation above. -/
def degree (a : Atom) : Nat :=
  (Finset.univ.filter fun b : Atom => Bonded a b .single = true).card

def normalValence : Element → Nat
  | .C => 4
  | .H => 1
  | .O => 2
  | .Si => 4

def atomCount (e : Element) : Nat :=
  (Finset.univ.filter fun a : Atom => atomElement a = e).card

structure Formula where
  carbon : Nat
  hydrogen : Nat
  oxygen : Nat
  silicon : Nat
  deriving DecidableEq, Repr

def graphFormula : Formula :=
  { carbon := atomCount .C
    hydrogen := atomCount .H
    oxygen := atomCount .O
    silicon := atomCount .Si }

def printedFormulaY : Formula :=
  { carbon := 72, hydrogen := 132, oxygen := 24, silicon := 6 }

/-! ## Stereochemistry on the supplied chair template -/

inductive Face
  | up | down
  deriving DecidableEq, Fintype, Repr

inductive Center
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

def opposite : Face → Face
  | .up => .down
  | .down => .up

/-- Faces in the α-D-glucopyranosyl starting material.  At C1 this is the
face of the α-glycosidic oxygen; at C2/C3 it is the face of the hydroxyl
oxygen; at C4 it is the incoming glycosidic oxygen; at C5 it is CH2OH. -/
def alphaCDStereo (_ : UnitId) : Center → Face
  | .c1 => .down
  | .c2 => .down
  | .c3 => .up
  | .c4 => .down
  | .c5 => .up

/-- Intramolecular displacement at C2 inverts only C2.  The oxygen that was
on C3 remains on its original upper face and bridges to the now upper-face
C2, giving the cis 2,3-anhydro-D-manno epoxide. -/
def mannoEpoxideStereo (i : UnitId) : Center → Face
  | .c2 => opposite (alphaCDStereo i .c2)
  | c => alphaCDStereo i c

inductive PrimarySix
  | hydroxyl | tbsEther
  deriving DecidableEq, Repr

inductive VicinalTwoThree
  | diol (c2Face c3Face : Face)
  | epoxide (oxygenFaceAtC2 oxygenFaceAtC3 : Face)
  deriving DecidableEq, Repr

structure RepeatDescriptor where
  primarySix : PrimarySix
  vicinalTwoThree : VicinalTwoThree
  stereo : Center → Face

/-- Problem input: one α-D-glucopyranosyl repeat of α-CD in the shown
`4C1` template. -/
def alphaCDRepeat (i : UnitId) : RepeatDescriptor :=
  { primarySix := .hydroxyl
    vicinalTwoThree := .diol (alphaCDStereo i .c2) (alphaCDStereo i .c3)
    stereo := alphaCDStereo i }

/-- Trusted general reaction rule used for the first operation: under the
shown TBSCl/pyridine conditions the primary O6 alcohol is replaced by O6-TBS;
the secondary stereocentres are untouched. -/
def protectPrimaryO6 (r : RepeatDescriptor) : RepeatDescriptor :=
  { r with primarySix := .tbsEther }

/-- Trusted general reaction rule used for NaH/TsCl: activation at O2 and
intramolecular SN2 attack by O3 closes a 2,3-epoxide, inverting C2 and
retaining C3. -/
def closeMannoEpoxide (i : UnitId) (r : RepeatDescriptor) : RepeatDescriptor :=
  { r with
    vicinalTwoThree := .epoxide (mannoEpoxideStereo i .c2)
      (mannoEpoxideStereo i .c3)
    stereo := mannoEpoxideStereo i }

def reactionRepeat (i : UnitId) : RepeatDescriptor :=
  closeMannoEpoxide i (protectPrimaryO6 (alphaCDRepeat i))

/-! ## Independent formula bookkeeping for the reaction sequence -/

def glucoseFormula : Formula :=
  { carbon := 6, hydrogen := 12, oxygen := 6, silicon := 0 }

/-- Six glucoses form a cyclic hexamer through six glycosidic condensations,
so the construction subtracts six water molecules. -/
def cyclicHexamerFormula (monomer : Formula) : Formula :=
  { carbon := 6 * monomer.carbon
    hydrogen := 6 * monomer.hydrogen - 12
    oxygen := 6 * monomer.oxygen - 6
    silicon := 6 * monomer.silicon }

def alphaCDFormula : Formula := cyclicHexamerFormula glucoseFormula

/-- Replacing six O--H hydrogens by six `Si(CH3)2C(CH3)3` groups adds
`C36 H84 Si6`. -/
def sixfoldTBSProtection (f : Formula) : Formula :=
  { carbon := f.carbon + 36
    hydrogen := f.hydrogen + 84
    oxygen := f.oxygen
    silicon := f.silicon + 6 }

/-- Six 2,3-epoxide closures remove six water molecules. -/
def sixfoldEpoxideClosure (f : Formula) : Formula :=
  { carbon := f.carbon
    hydrogen := f.hydrogen - 12
    oxygen := f.oxygen - 6
    silicon := f.silicon }

def reactionFormula : Formula :=
  sixfoldEpoxideClosure (sixfoldTBSProtection alphaCDFormula)

/-! ## Verified output -/

theorem reaction_repeat_is_protected_manno_epoxide (i : UnitId) :
    (reactionRepeat i).primarySix = .tbsEther ∧
    (reactionRepeat i).vicinalTwoThree = .epoxide .up .up ∧
    (reactionRepeat i).stereo .c1 = .down ∧
    (reactionRepeat i).stereo .c2 = .up ∧
    (reactionRepeat i).stereo .c3 = .up ∧
    (reactionRepeat i).stereo .c4 = .down ∧
    (reactionRepeat i).stereo .c5 = .up := by
  simp [reactionRepeat, closeMannoEpoxide, protectPrimaryO6,
    alphaCDRepeat, mannoEpoxideStereo, alphaCDStereo, opposite]

theorem alpha_anomer_retained (i : UnitId) :
    (reactionRepeat i).stereo .c1 =
      opposite ((reactionRepeat i).stereo .c5) := by
  simp [reactionRepeat, closeMannoEpoxide, protectPrimaryO6,
    alphaCDRepeat, mannoEpoxideStereo, alphaCDStereo, opposite]

theorem c2_inverted_c3_retained (i : UnitId) :
    (reactionRepeat i).stereo .c2 = opposite (alphaCDStereo i .c2) ∧
    (reactionRepeat i).stereo .c3 = alphaCDStereo i .c3 := by
  simp [reactionRepeat, closeMannoEpoxide, mannoEpoxideStereo]

theorem alpha_cd_formula_from_six_glucoses :
    alphaCDFormula =
      { carbon := 36, hydrogen := 60, oxygen := 30, silicon := 0 } := by
  decide

theorem epoxide_connectivity (i : UnitId) :
    Bonded (heavy i .c2) (heavy i .c3) .single = true ∧
    Bonded (heavy i .c2) (heavy i .epoxideO) .single = true ∧
    Bonded (heavy i .c3) (heavy i .epoxideO) .single = true := by
  simp [Bonded, heavy, InternalHeavyPair, UnorderedPair, eqb]

theorem tbs_connectivity (i : UnitId) :
    Bonded (heavy i .c6) (heavy i .o6) .single = true ∧
    Bonded (heavy i .o6) (heavy i .si) .single = true ∧
    Bonded (heavy i .si) (heavy i .siMe1) .single = true ∧
    Bonded (heavy i .si) (heavy i .siMe2) .single = true ∧
    Bonded (heavy i .si) (heavy i .tertC) .single = true ∧
    Bonded (heavy i .tertC) (heavy i .tertMe1) .single = true ∧
    Bonded (heavy i .tertC) (heavy i .tertMe2) .single = true ∧
    Bonded (heavy i .tertC) (heavy i .tertMe3) .single = true := by
  simp [Bonded, heavy, InternalHeavyPair, UnorderedPair, eqb]

theorem alpha_one_four_connectivity (i : UnitId) :
    Bonded (heavy i .c1) (heavy i .linkO) .single = true ∧
    Bonded (heavy i .linkO) (heavy (nextUnit i) .c4) .single = true := by
  simp [Bonded, heavy, InternalHeavyPair, UnorderedPair, eqb]

theorem all_bonds_are_single {a b : Atom} {order : BondOrder}
    (h : Bonded a b order = true) : order = .single := by
  cases order <;> simp_all [Bonded, eqb]

theorem neutral_and_closed_shell :
    (∀ a : Atom, formalCharge a = 0) ∧
    (∀ a : Atom, radicalElectrons a = 0) := by
  constructor <;> intro a <;> rfl

/-- This computation checks every one of the 234 atoms against the exact
bond relation; hence it also checks that every explicit hydrogen is attached
and that there are no missing or surplus heavy-atom neighbors. -/
theorem every_atom_has_normal_valence :
    ∀ a : Atom, degree a = normalValence (atomElement a) := by
  set_option maxRecDepth 100000 in
    decide

theorem graph_formula_is_printed_formula :
    graphFormula = printedFormulaY := by
  set_option maxRecDepth 100000 in
    decide

theorem reaction_formula_is_printed_formula :
    reactionFormula = printedFormulaY := by
  decide

/-- Final formal answer to T9-A4.  It simultaneously establishes the
six identical stereochemical repeat descriptors, their characteristic
epoxide/TBS/interunit bonds, the formula printed on the blank answer sheet,
normal valences, and absence of charge or radicals. -/
theorem structure_y :
    (∀ i : UnitId,
      (reactionRepeat i).primarySix = .tbsEther ∧
      (reactionRepeat i).vicinalTwoThree = .epoxide .up .up ∧
      (reactionRepeat i).stereo .c1 = .down ∧
      (reactionRepeat i).stereo .c2 = .up ∧
      (reactionRepeat i).stereo .c3 = .up ∧
      (reactionRepeat i).stereo .c4 = .down ∧
      (reactionRepeat i).stereo .c5 = .up ∧
      Bonded (heavy i .c2) (heavy i .c3) .single = true ∧
      Bonded (heavy i .c2) (heavy i .epoxideO) .single = true ∧
      Bonded (heavy i .c3) (heavy i .epoxideO) .single = true ∧
      Bonded (heavy i .c6) (heavy i .o6) .single = true ∧
      Bonded (heavy i .o6) (heavy i .si) .single = true ∧
      Bonded (heavy i .c1) (heavy i .linkO) .single = true ∧
      Bonded (heavy i .linkO) (heavy (nextUnit i) .c4) .single = true) ∧
    graphFormula = printedFormulaY ∧
    reactionFormula = printedFormulaY ∧
    (∀ a : Atom, degree a = normalValence (atomElement a)) ∧
    (∀ a : Atom, formalCharge a = 0 ∧ radicalElectrons a = 0) := by
  refine ⟨?_, graph_formula_is_printed_formula,
    reaction_formula_is_printed_formula, every_atom_has_normal_valence, ?_⟩
  · intro i
    have hr := reaction_repeat_is_protected_manno_epoxide i
    have he := epoxide_connectivity i
    have ht := tbs_connectivity i
    have hg := alpha_one_four_connectivity i
    rcases hr with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    rcases he with ⟨h9, h10, h11⟩
    rcases ht with ⟨h12, h13, -, -, -, -, -, -⟩
    rcases hg with ⟨h14, h15⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7,
      h9, h10, h11, h12, h13, h14, h15⟩
  · intro a
    exact ⟨rfl, rfl⟩

#print axioms structure_y
#print axioms graph_formula_is_printed_formula
#print axioms every_atom_has_normal_valence

end IChO2026Problems.Icho2026T9A4
