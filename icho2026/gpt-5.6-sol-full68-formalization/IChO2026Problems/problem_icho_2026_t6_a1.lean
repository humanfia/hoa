import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T6-A1: aromatic and antiaromatic systems in cyclocarbons

The problem asks for eight exact integer counts.  The two cyclic π systems are
distinguished by their in-plane and out-of-plane orientations.  Their electron
inventories are kept separate from Hückel classification, so the requested
counts are conclusions rather than fields of the chemical input model.

For C₁₃, the model deliberately retains the electron-allocation freedom that
is irrelevant to the requested counts.  A triplet allocation is any odd/odd
positive split of the 26 π electrons.  A closed-shell singlet allocation is any
positive even/even split of the same total.  Thus the assumptions contain no
selected 12/14 singlet assignment: modular arithmetic, rather than an
answer-shaped electron configuration, determines its Hückel counts.
-/

namespace IChO2026Problems.T6A1

/-- The two geometrically distinct cyclic π systems of an sp-carbon ring. -/
inductive PiOrientation where
  | inPlane
  | outOfPlane
  deriving DecidableEq, Fintype, Repr

/-- The four molecular/electronic cases named in subquestion T6-A1. -/
inductive CyclocarbonCase where
  | c18
  | c16
  | tripletC13
  | singletC13
  deriving DecidableEq, Fintype, Repr

/-- The three outcomes relevant to applying the ground-state Hückel rule to a
cyclic π-electron count.  An odd count is neither of the two closed-shell
Hückel classes. -/
inductive HuckelCharacter where
  | aromatic
  | antiaromatic
  | neither
  deriving DecidableEq, Repr

/-- Hückel's `4k+2`/`4k` classification, expressed by residues modulo four.
Zero electrons are excluded from the antiaromatic class. -/
def huckelCharacter (electrons : ℕ) : HuckelCharacter :=
  if electrons % 4 = 2 then
    .aromatic
  else if 0 < electrons ∧ electrons % 4 = 0 then
    .antiaromatic
  else
    .neither

/-- An electron inventory does not contain any aromaticity labels or requested
counts; it records only electron numbers for each named case and orientation. -/
structure PiElectronModel where
  electrons : CyclocarbonCase → PiOrientation → ℕ

/-- The source spin label `S = 1`, interpreted in the elementary two-subsystem
electron ledger: each subsystem contains an odd number of electrons and their
combined inventory is the `2 × 13` π electrons of neutral C₁₃. -/
def TripletAllocationAdmissible (inPlane outOfPlane : ℕ) : Prop :=
  inPlane % 2 = 1 ∧
  outOfPlane % 2 = 1 ∧
  inPlane + outOfPlane = 26

/-- The source spin label `S = 0`, interpreted in the elementary closed-shell
two-subsystem ledger.  Both subsystem populations are positive and even, and
only their total is fixed.  In particular, this predicate does not choose an
orientation or an exact electron split. -/
def SingletAllocationAdmissible (inPlane outOfPlane : ℕ) : Prop :=
  0 < inPlane ∧
  0 < outOfPlane ∧
  inPlane % 2 = 0 ∧
  outOfPlane % 2 = 0 ∧
  inPlane + outOfPlane = 26

/-- Problem-side chemical input for the Hückel calculation.

Even cyclocarbons have one `n`-electron system in each orientation.  For the
odd ring, only the total population and the parity implied by the stated spin
form are retained.  The exact singlet and triplet allocations remain free.
-/
def FitsProblemModel (model : PiElectronModel) : Prop :=
  model.electrons .c18 .inPlane = 18 ∧
  model.electrons .c18 .outOfPlane = 18 ∧
  model.electrons .c16 .inPlane = 16 ∧
  model.electrons .c16 .outOfPlane = 16 ∧
  TripletAllocationAdmissible
    (model.electrons .tripletC13 .inPlane)
    (model.electrons .tripletC13 .outOfPlane) ∧
  SingletAllocationAdmissible
    (model.electrons .singletC13 .inPlane)
    (model.electrons .singletC13 .outOfPlane)

/-- The singlet assumptions genuinely leave the allocation unresolved: two
different positive even splits satisfy the same source-side ledger.  These are
mathematical witnesses to freedom in the abstraction, not asserted molecular
structures. -/
theorem singletAllocation_not_unique :
    SingletAllocationAdmissible 12 14 ∧
    SingletAllocationAdmissible 10 16 ∧
    (12, 14) ≠ (10, 16) := by
  norm_num [SingletAllocationAdmissible]

/-- Count the distinct orientations having a specified Hückel character. -/
def countCharacter (model : PiElectronModel) (species : CyclocarbonCase)
    (character : HuckelCharacter) : ℕ :=
  ((Finset.univ : Finset PiOrientation).filter fun orientation =>
    huckelCharacter (model.electrons species orientation) = character).card

/- Each source-requested table cell has its own named raw carrier. -/

def c18Aromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .c18 .aromatic

def c18Antiaromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .c18 .antiaromatic

def c16Aromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .c16 .aromatic

def c16Antiaromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .c16 .antiaromatic

def tripletC13Aromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .tripletC13 .aromatic

def tripletC13Antiaromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .tripletC13 .antiaromatic

def singletC13Aromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .singletC13 .aromatic

def singletC13Antiaromatic (model : PiElectronModel) : ℕ :=
  countCharacter model .singletC13 .antiaromatic

/- The eight conclusions are stated separately before being assembled in the
raw-result contract, preserving the order fixed by the source report. -/

def C18AromaticSpec (model : PiElectronModel) : Prop :=
  c18Aromatic model = 2

def C18AntiaromaticSpec (model : PiElectronModel) : Prop :=
  c18Antiaromatic model = 0

def C16AromaticSpec (model : PiElectronModel) : Prop :=
  c16Aromatic model = 0

def C16AntiaromaticSpec (model : PiElectronModel) : Prop :=
  c16Antiaromatic model = 2

def TripletC13AromaticSpec (model : PiElectronModel) : Prop :=
  tripletC13Aromatic model = 0

def TripletC13AntiaromaticSpec (model : PiElectronModel) : Prop :=
  tripletC13Antiaromatic model = 0

def SingletC13AromaticSpec (model : PiElectronModel) : Prop :=
  singletC13Aromatic model = 1

def SingletC13AntiaromaticSpec (model : PiElectronModel) : Prop :=
  singletC13Antiaromatic model = 1

/-- Raw end-to-end result: every electron inventory satisfying the problem-side
chemical model yields all eight Hückel counts, and the model constraints are
jointly satisfiable. -/
def RawResult : Prop :=
  (∃ model : PiElectronModel, FitsProblemModel model) ∧
    ∀ model : PiElectronModel, FitsProblemModel model →
      C18AromaticSpec model ∧
      C18AntiaromaticSpec model ∧
      C16AromaticSpec model ∧
      C16AntiaromaticSpec model ∧
      TripletC13AromaticSpec model ∧
      TripletC13AntiaromaticSpec model ∧
      SingletC13AromaticSpec model ∧
      SingletC13AntiaromaticSpec model

/-- Exact-integer reporting does not round: the displayed natural number must
equal the computed raw count. -/
def ExactIntegerReport (raw displayed : ℕ) : Prop :=
  displayed = raw

/-- Reported result for the eight table cells under their source-declared
`exact_integer` policies. -/
def ReportedResult : Prop :=
  (∃ model : PiElectronModel, FitsProblemModel model) ∧
    ∀ model : PiElectronModel, FitsProblemModel model →
      ExactIntegerReport (c18Aromatic model) 2 ∧
      ExactIntegerReport (c18Antiaromatic model) 0 ∧
      ExactIntegerReport (c16Aromatic model) 0 ∧
      ExactIntegerReport (c16Antiaromatic model) 2 ∧
      ExactIntegerReport (tripletC13Aromatic model) 0 ∧
      ExactIntegerReport (tripletC13Antiaromatic model) 0 ∧
      ExactIntegerReport (singletC13Aromatic model) 1 ∧
      ExactIntegerReport (singletC13Antiaromatic model) 1

/-- An odd electron count belongs to neither closed-shell Hückel residue
class.  This is the only arithmetic fact needed for every admissible triplet
electron split. -/
private lemma huckelCharacter_of_mod_two_eq_one (electrons : ℕ)
    (hOdd : electrons % 2 = 1) :
    huckelCharacter electrons = .neither := by
  unfold huckelCharacter
  split
  · omega
  split
  · omega
  · rfl

/-- The generated finite enumeration contains exactly the two named geometric
orientations. -/
private lemma piOrientation_univ :
    (Finset.univ : Finset PiOrientation) = {.inPlane, .outOfPlane} := by
  ext orientation
  cases orientation <;> simp

/-- Machine-bound raw solve-phase contract. -/
theorem rawResultContract :
    ("c211466608bbdf9e2466bdb0f840bfe7afb32219a3860ff8ef63bf913360b9b7" : String) =
        "c211466608bbdf9e2466bdb0f840bfe7afb32219a3860ff8ef63bf913360b9b7" ∧
      RawResult := by
  constructor
  · rfl
  · constructor
    · refine ⟨{ electrons := fun species orientation =>
          match species, orientation with
          | .c18, _ => 18
          | .c16, _ => 16
          | .tripletC13, _ => 13
          | .singletC13, .inPlane => 10
          | .singletC13, .outOfPlane => 16 }, ?_⟩
      norm_num [FitsProblemModel, TripletAllocationAdmissible,
        SingletAllocationAdmissible]
    · intro model hModel
      rcases hModel with
        ⟨h18In, h18Out, h16In, h16Out, hTriplet, hSinglet⟩
      rcases hTriplet with
        ⟨hTripletIn, hTripletOut, _hTripletTotal⟩
      rcases hSinglet with
        ⟨hSingletInPositive, hSingletOutPositive, hSingletInEven,
          hSingletOutEven, hSingletTotal⟩
      have h18InCharacter :
          huckelCharacter (model.electrons .c18 .inPlane) = .aromatic := by
        simp [h18In, huckelCharacter]
      have h18OutCharacter :
          huckelCharacter (model.electrons .c18 .outOfPlane) = .aromatic := by
        simp [h18Out, huckelCharacter]
      have h16InCharacter :
          huckelCharacter (model.electrons .c16 .inPlane) = .antiaromatic := by
        simp [h16In, huckelCharacter]
      have h16OutCharacter :
          huckelCharacter (model.electrons .c16 .outOfPlane) = .antiaromatic := by
        simp [h16Out, huckelCharacter]
      have hTripletInCharacter :=
        huckelCharacter_of_mod_two_eq_one
          (model.electrons .tripletC13 .inPlane) hTripletIn
      have hTripletOutCharacter :=
        huckelCharacter_of_mod_two_eq_one
          (model.electrons .tripletC13 .outOfPlane) hTripletOut
      have hSingletResidues :
          ((model.electrons .singletC13 .inPlane % 4 = 0 ∧
              model.electrons .singletC13 .outOfPlane % 4 = 2) ∨
            (model.electrons .singletC13 .inPlane % 4 = 2 ∧
              model.electrons .singletC13 .outOfPlane % 4 = 0)) := by
        omega
      rcases hSingletResidues with hSingletResidues | hSingletResidues
      · rcases hSingletResidues with ⟨hSingletInMod, hSingletOutMod⟩
        have hSingletInCharacter :
            huckelCharacter (model.electrons .singletC13 .inPlane) =
              .antiaromatic := by
          simp [huckelCharacter, hSingletInMod, hSingletInPositive]
        have hSingletOutCharacter :
            huckelCharacter (model.electrons .singletC13 .outOfPlane) =
              .aromatic := by
          simp [huckelCharacter, hSingletOutMod]
        simp [C18AromaticSpec, C18AntiaromaticSpec, C16AromaticSpec,
          C16AntiaromaticSpec, TripletC13AromaticSpec,
          TripletC13AntiaromaticSpec, SingletC13AromaticSpec,
          SingletC13AntiaromaticSpec, c18Aromatic, c18Antiaromatic,
          c16Aromatic, c16Antiaromatic, tripletC13Aromatic,
          tripletC13Antiaromatic, singletC13Aromatic,
          singletC13Antiaromatic, countCharacter, piOrientation_univ,
          Finset.filter_insert, Finset.filter_singleton, h18InCharacter,
          h18OutCharacter, h16InCharacter, h16OutCharacter,
          hTripletInCharacter, hTripletOutCharacter, hSingletInCharacter,
          hSingletOutCharacter]
      · rcases hSingletResidues with ⟨hSingletInMod, hSingletOutMod⟩
        have hSingletInCharacter :
            huckelCharacter (model.electrons .singletC13 .inPlane) =
              .aromatic := by
          simp [huckelCharacter, hSingletInMod]
        have hSingletOutCharacter :
            huckelCharacter (model.electrons .singletC13 .outOfPlane) =
              .antiaromatic := by
          simp [huckelCharacter, hSingletOutMod, hSingletOutPositive]
        simp [C18AromaticSpec, C18AntiaromaticSpec, C16AromaticSpec,
          C16AntiaromaticSpec, TripletC13AromaticSpec,
          TripletC13AntiaromaticSpec, SingletC13AromaticSpec,
          SingletC13AntiaromaticSpec, c18Aromatic, c18Antiaromatic,
          c16Aromatic, c16Antiaromatic, tripletC13Aromatic,
          tripletC13Antiaromatic, singletC13Aromatic,
          singletC13Antiaromatic, countCharacter, piOrientation_univ,
          Finset.filter_insert, Finset.filter_singleton, h18InCharacter,
          h18OutCharacter, h16InCharacter, h16OutCharacter,
          hTripletInCharacter, hTripletOutCharacter, hSingletInCharacter,
          hSingletOutCharacter]

/-- Machine-bound exact-integer reporting contract. -/
theorem reportedResultContract :
    ("8ba4b25c0443f85d12d63fab88f91ba98b28e1f1640b8b718240af1d05b2d37c" : String) =
        "8ba4b25c0443f85d12d63fab88f91ba98b28e1f1640b8b718240af1d05b2d37c" ∧
      ReportedResult := by
  constructor
  · rfl
  · rcases rawResultContract.2 with ⟨hExists, hCounts⟩
    refine ⟨hExists, ?_⟩
    intro model hModel
    rcases hCounts model hModel with
      ⟨h18A, h18AA, h16A, h16AA, hTripletA, hTripletAA, hSingletA,
        hSingletAA⟩
    exact ⟨h18A.symm, h18AA.symm, h16A.symm, h16AA.symm,
      hTripletA.symm, hTripletAA.symm, hSingletA.symm, hSingletAA.symm⟩

end IChO2026Problems.T6A1
