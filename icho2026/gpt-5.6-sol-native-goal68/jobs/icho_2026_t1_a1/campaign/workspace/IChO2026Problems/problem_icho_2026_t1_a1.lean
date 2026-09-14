import Mathlib

/-!
# IChO 2026 T1-A1: identification of X and Y

The problem page displays ten numbered structures.  The student answer sheet
confirms that both `X` and `Y` are to be selected from those ten structures.
This file separates three layers:

* `Candidate`, `printedFormula`, and `descriptor` transcribe finite data visible
  in the problem's structure table;
* `AcidCineoleCyclization` encodes the standard protonation / intramolecular
  ether-closure test used on those structural descriptors;
* the final theorems eliminate the finite candidates and return the two answer
  numbers.  An explicit embedded heavy-atom graph supplies a checkable mirror
  plane certificate for structure 3 rather than merely naming its symmetry.

No declaration in this file is an axiom, and no answer identity is an
assumption of a final theorem.
-/

namespace IChO2026Problems.T1A1

/-! ## Problem-page data -/

/-- The ten check-box choices printed on answer sheet A1-1. -/
inductive Candidate where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype, Repr

/-- Element counts in the molecular formulae printed below the structures. -/
structure MolecularFormula where
  carbon : Nat
  hydrogen : Nat
  oxygen : Nat
  deriving DecidableEq, Repr

/-- Molecular formulae transcribed from problem page Q1-2. -/
def printedFormula : Candidate → MolecularFormula
  | .c1  => ⟨11, 14, 3⟩
  | .c2  => ⟨10, 18, 1⟩
  | .c3  => ⟨10, 18, 1⟩
  | .c4  => ⟨6, 12, 1⟩
  | .c5  => ⟨10, 12, 2⟩
  | .c6  => ⟨10, 18, 1⟩
  | .c7  => ⟨14, 16, 0⟩
  | .c8  => ⟨15, 24, 0⟩
  | .c9  => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- Carbon frameworks needed to distinguish the four `C10H18O` drawings. -/
inductive CarbonFramework where
  | other
  | bornaneLike
  | pMenthane
  | cyclopropylKetone
  deriving DecidableEq, Repr

/-- The oxygen environment read from a displayed structural formula. -/
inductive OxygenEnvironment where
  | other
  | secondaryAlcohol
  | tertiaryAlcohol
  | bridgedEther
  | ketone
  deriving DecidableEq, Repr

/-- Geometry of an alkene/alcohol tether relevant to cineole closure. -/
inductive ClosureGeometry where
  | none
  | protonatableAlkeneToInternalOxygen
  deriving DecidableEq, Repr

/-- A compact transcription of the structural, rather than merely molecular-
formula, information needed in this subquestion. -/
structure DiagramDescriptor where
  framework : CarbonFramework
  oxygenEnvironment : OxygenEnvironment
  hasCarbonCarbonDoubleBond : Bool
  closureGeometry : ClosureGeometry
  hasMirrorPlane : Bool
  deriving DecidableEq, Repr

/-- Structural features read from the ten drawings on Q1-2.  The four entries
with formula `C10H18O` are recorded in detail.  The other entries cannot be one
member of a distinct isomeric pair from the answer choices, so their unused
features are conservatively recorded as `other`/`none`. -/
def descriptor : Candidate → DiagramDescriptor
  | .c2 => ⟨.bornaneLike, .secondaryAlcohol, false, .none, false⟩
  | .c3 => ⟨.pMenthane, .bridgedEther, false, .none, true⟩
  | .c6 =>
      ⟨.pMenthane, .tertiaryAlcohol, true,
        .protonatableAlkeneToInternalOxygen, false⟩
  | .c10 => ⟨.cyclopropylKetone, .ketone, false, .none, false⟩
  | _ => ⟨.other, .other, false, .none, false⟩

/-- A diagram has the α-terpineol motif used by the standard acid-catalysed
cineole closure exactly when it is a p-menthane tertiary alkenol with the shown
intramolecular O/alkene tether. -/
def IsAlphaTerpineolMotif (c : Candidate) : Prop :=
  (descriptor c).framework = .pMenthane ∧
  (descriptor c).oxygenEnvironment = .tertiaryAlcohol ∧
  (descriptor c).hasCarbonCarbonDoubleBond = true ∧
  (descriptor c).closureGeometry = .protonatableAlkeneToInternalOxygen

/-- A diagram is the corresponding 1,8-cineole ether product exactly when it
has the same p-menthane framework represented as the displayed bridged ether. -/
def IsCineoleEtherMotif (c : Candidate) : Prop :=
  (descriptor c).framework = .pMenthane ∧
  (descriptor c).oxygenEnvironment = .bridgedEther

/-- The mirror-plane assessment made by inspecting the displayed
stereostructure.  Its positive case is independently certified below using an
embedded molecular graph. -/
def DiagramHasMirrorPlane (c : Candidate) : Prop :=
  (descriptor c).hasMirrorPlane = true

/-! ## Trusted general chemical rule, specialized to the displayed motifs -/

/-- Applicability relation for the reaction invoked by the clue.  It encodes
the standard rule: protonation of the suitably tethered α-terpineol alkene,
followed by intramolecular attack by its oxygen, produces the cineole ether.
Formula equality makes explicit the mass-balance requirement for an
isomerisation. -/
def AcidCineoleCyclization (x y : Candidate) : Prop :=
  IsAlphaTerpineolMotif x ∧
  IsCineoleEtherMotif y ∧
  printedFormula x = printedFormula y

/-- The two consequences of the phrase "X can isomerise into Y in an acidic
medium" used before the product structure is identified: X has the displayed
α-terpineol cyclization motif, and an isomerisation preserves its molecular
formula. -/
def AcidIsomerisationClue (x y : Candidate) : Prop :=
  IsAlphaTerpineolMotif x ∧ printedFormula x = printedFormula y

theorem acidCineoleCyclization_preserves_formula {x y : Candidate}
    (h : AcidCineoleCyclization x y) :
    printedFormula x = printedFormula y := by
  exact h.2.2

theorem alphaTerpineol_motif_unique {x : Candidate}
    (h : IsAlphaTerpineolMotif x) : x = .c6 := by
  cases x <;> simp [IsAlphaTerpineolMotif, descriptor] at h ⊢

theorem cineole_ether_motif_unique {y : Candidate}
    (h : IsCineoleEtherMotif y) : y = .c3 := by
  cases y <;> simp [IsCineoleEtherMotif, descriptor] at h ⊢

theorem acid_cyclization_pair_unique {x y : Candidate}
    (h : AcidCineoleCyclization x y) : x = .c6 ∧ y = .c3 := by
  exact ⟨alphaTerpineol_motif_unique h.1,
    cineole_ether_motif_unique h.2.1⟩

theorem mirror_plane_C10H18O_choice_unique {y : Candidate}
    (hformula : printedFormula .c6 = printedFormula y)
    (hplane : DiagramHasMirrorPlane y) : y = .c3 := by
  cases y <;>
    simp [printedFormula, DiagramHasMirrorPlane, descriptor] at hformula hplane ⊢

/-! ## Explicit symmetry and formula certificate for candidate 3 -/

inductive Element where
  | carbon | oxygen
  deriving DecidableEq, Repr

/-- Heavy atoms of 1,8-cineole.  There are two equivalent carbon paths
`a-p-q-b` and `a-r-s-b`, an ether path `a-o-t-b`, one methyl at `a`, and two
methyls at `t`. -/
inductive CineoleAtom where
  | a | b | p | q | r | s | o | t | methylA | methylTPlus | methylTMinus
  deriving DecidableEq, Fintype, Repr

structure Point3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

def reflectInZPlane (v : Point3) : Point3 := ⟨v.x, v.y, -v.z⟩

structure EmbeddedMolecule (Atom : Type) where
  element : Atom → Element
  bonded : Atom → Atom → Bool
  position : Atom → Point3
  implicitHydrogens : Atom → Nat

def cineoleElement : CineoleAtom → Element
  | .o => .oxygen
  | _ => .carbon

/-- The undirected heavy-atom bonds of the 1,8-cineole skeleton. -/
def cineoleBonded : CineoleAtom → CineoleAtom → Bool
  | .a, .p | .p, .a
  | .p, .q | .q, .p
  | .q, .b | .b, .q
  | .a, .r | .r, .a
  | .r, .s | .s, .r
  | .s, .b | .b, .s
  | .a, .o | .o, .a
  | .o, .t | .t, .o
  | .t, .b | .b, .t
  | .a, .methylA | .methylA, .a
  | .t, .methylTPlus | .methylTPlus, .t
  | .t, .methylTMinus | .methylTMinus, .t => true
  | _, _ => false

/-- One symmetric three-dimensional embedding.  The `z = 0` plane contains
the bridgeheads and ether path; it exchanges the two carbon paths and the two
methyl groups at `t`. -/
def cineolePosition : CineoleAtom → Point3
  | .a => ⟨0, 0, 0⟩
  | .b => ⟨4, 0, 0⟩
  | .p => ⟨1, 1, 1⟩
  | .q => ⟨3, 1, 1⟩
  | .r => ⟨1, 1, -1⟩
  | .s => ⟨3, 1, -1⟩
  | .o => ⟨1, -1, 0⟩
  | .t => ⟨3, -1, 0⟩
  | .methylA => ⟨-1, 0, 0⟩
  | .methylTPlus => ⟨4, -1, 1⟩
  | .methylTMinus => ⟨4, -1, -1⟩

/-- Hydrogens required at each heavy atom by ordinary valence after the
displayed single bonds are accounted for. -/
def cineoleHydrogens : CineoleAtom → Nat
  | .a => 0
  | .b => 1
  | .p | .q | .r | .s => 2
  | .o => 0
  | .t => 0
  | .methylA | .methylTPlus | .methylTMinus => 3

def cineoleMolecule : EmbeddedMolecule CineoleAtom :=
  ⟨cineoleElement, cineoleBonded, cineolePosition, cineoleHydrogens⟩

def cineoleMirror : CineoleAtom → CineoleAtom
  | .p => .r
  | .r => .p
  | .q => .s
  | .s => .q
  | .methylTPlus => .methylTMinus
  | .methylTMinus => .methylTPlus
  | atom => atom

/-- A fully checkable certificate that an embedded molecular graph is
preserved by reflection. -/
structure MirrorPlaneCertificate {Atom : Type}
    (m : EmbeddedMolecule Atom) where
  mirror : Atom → Atom
  involutive : Function.Involutive mirror
  nontrivial : ∃ atom, mirror atom ≠ atom
  element_preserved : ∀ atom, m.element (mirror atom) = m.element atom
  position_reflected : ∀ atom,
    m.position (mirror atom) = reflectInZPlane (m.position atom)
  bond_preserved : ∀ atom₁ atom₂,
    m.bonded (mirror atom₁) (mirror atom₂) = m.bonded atom₁ atom₂
  implicitHydrogens_preserved : ∀ atom,
    m.implicitHydrogens (mirror atom) = m.implicitHydrogens atom

def cineoleMirrorPlaneCertificate :
    MirrorPlaneCertificate cineoleMolecule where
  mirror := cineoleMirror
  involutive := by
    intro atom
    cases atom <;> rfl
  nontrivial := ⟨.p, by decide⟩
  element_preserved := by
    intro atom
    cases atom <;> rfl
  position_reflected := by
    intro atom
    cases atom <;> rfl
  bond_preserved := by
    intro atom₁ atom₂
    cases atom₁ <;> cases atom₂ <;> rfl
  implicitHydrogens_preserved := by
    intro atom
    cases atom <;> rfl

theorem candidate3_has_plane_of_symmetry :
    Nonempty (MirrorPlaneCertificate cineoleMolecule) := by
  exact ⟨cineoleMirrorPlaneCertificate⟩

theorem candidate3_plane_assessment_is_certified :
    DiagramHasMirrorPlane .c3 ∧
      Nonempty (MirrorPlaneCertificate cineoleMolecule) := by
  exact ⟨rfl, candidate3_has_plane_of_symmetry⟩

def cineoleCarbonCount : Nat :=
  (Finset.univ.filter
    (fun atom : CineoleAtom => cineoleElement atom = .carbon)).card

def cineoleOxygenCount : Nat :=
  (Finset.univ.filter
    (fun atom : CineoleAtom => cineoleElement atom = .oxygen)).card

def cineoleHydrogenCount : Nat :=
  ∑ atom : CineoleAtom, cineoleHydrogens atom

theorem candidate3_formula_from_graph :
    MolecularFormula.mk cineoleCarbonCount cineoleHydrogenCount
      cineoleOxygenCount = printedFormula .c3 := by
  decide

/-! ## Requested outputs -/

/-- The prompt's observations, interpreted through the explicitly defined
acid-isomerisation and mirror-plane predicates.  Neither premise contains a
candidate identity. -/
structure ProblemObservation where
  x : Candidate
  y : Candidate
  differentSubstances : x ≠ y
  acidIsomerisation : AcidIsomerisationClue x y
  yHasPlaneOfSymmetry : DiagramHasMirrorPlane y

/-- The derived pair really satisfies the formalized problem clues; hence the
universal identification theorems below are not vacuous. -/
def solutionObservation : ProblemObservation where
  x := .c6
  y := .c3
  differentSubstances := by decide
  acidIsomerisation := by
    simp [AcidIsomerisationClue, IsAlphaTerpineolMotif, descriptor,
      printedFormula]
  yHasPlaneOfSymmetry := rfl

theorem problem_observation_is_consistent : Nonempty ProblemObservation := by
  exact ⟨solutionObservation⟩

theorem candidate6_to_candidate3_acid_cyclization :
    AcidCineoleCyclization .c6 .c3 := by
  simp [AcidCineoleCyclization, IsAlphaTerpineolMotif,
    IsCineoleEtherMotif, descriptor, printedFormula]

/-- Requested output `identity_x`: X is choice 6, α-terpineol. -/
theorem identity_x (o : ProblemObservation) : o.x = .c6 := by
  exact alphaTerpineol_motif_unique o.acidIsomerisation.1

/-- Requested output `identity_y`: Y is choice 3, 1,8-cineole. -/
theorem identity_y (o : ProblemObservation) : o.y = .c3 := by
  have hx : o.x = .c6 := identity_x o
  have hformula : printedFormula .c6 = printedFormula o.y := by
    simpa [hx] using o.acidIsomerisation.2
  exact mirror_plane_C10H18O_choice_unique hformula o.yHasPlaneOfSymmetry

/-- Combined answer, together with the formal certificate for the symmetry
clue attached to Y. -/
theorem identify_X_and_Y (o : ProblemObservation) :
    o.x = .c6 ∧ o.y = .c3 ∧
      Nonempty (MirrorPlaneCertificate cineoleMolecule) := by
  exact ⟨identity_x o, identity_y o, candidate3_has_plane_of_symmetry⟩

#print axioms identity_x
#print axioms identity_y
#print axioms identify_X_and_Y
#print axioms candidate3_has_plane_of_symmetry
#print axioms candidate3_formula_from_graph
#print axioms problem_observation_is_consistent
#print axioms candidate6_to_candidate3_acid_cyclization

end IChO2026Problems.T1A1
