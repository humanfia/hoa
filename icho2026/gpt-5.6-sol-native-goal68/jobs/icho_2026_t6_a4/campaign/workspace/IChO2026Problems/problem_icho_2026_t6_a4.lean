import Mathlib

/-!
# IChO 2026 T6-A4: nominal masses of cyclo[48]carbon catenane ions

The problem page supplies the formula `C₄₀H₃₄N₂O₃` for macrocycle E and
identifies the carbon ring as `C₄₈`.  The blank answer sheet supplies the
worked assignment `m/z = 591` as `[E + H]⁺`.  Thus the positive ions below
are represented by an intact carbon ring, intact copies of E, added protons,
and the indicated positive charge.

Only integer atomic masses requested by the question are used:
`C = 12`, `H = 1`, `N = 14`, and `O = 16`.
-/

namespace IChO2026Problems.T6A4

/-- Element counts needed for the two problem-supplied molecular formulas. -/
structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace Formula

/-- Sum formulas add their element counts. -/
def add (a b : Formula) : Formula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  nitrogen := a.nitrogen + b.nitrogen
  oxygen := a.oxygen + b.oxygen

/-- `scale n f` is the formula of `n` intact copies of `f`. -/
def scale (n : ℕ) (f : Formula) : Formula where
  carbon := n * f.carbon
  hydrogen := n * f.hydrogen
  nitrogen := n * f.nitrogen
  oxygen := n * f.oxygen

/-- Integer nominal mass using C/H/N/O masses 12/1/14/16. -/
def integerMass (f : Formula) : ℕ :=
  12 * f.carbon + f.hydrogen + 14 * f.nitrogen + 16 * f.oxygen

end Formula

/-- Formula of macrocycle E, printed on the problem page. -/
def macrocycleE : Formula :=
  { carbon := 40, hydrogen := 34, nitrogen := 2, oxygen := 3 }

/-- Formula of the cyclo[48]carbon ring printed on the problem page. -/
def cyclo48Carbon : Formula :=
  { carbon := 48, hydrogen := 0, nitrogen := 0, oxygen := 0 }

/-- Formula contribution of added protons in the nominal-mass model. -/
def addedProtons (n : ℕ) : Formula :=
  { carbon := 0, hydrogen := n, nitrogen := 0, oxygen := 0 }

theorem macrocycleE_integerMass : Formula.integerMass macrocycleE = 590 := by
  norm_num [Formula.integerMass, macrocycleE]

theorem cyclo48Carbon_integerMass : Formula.integerMass cyclo48Carbon = 576 := by
  norm_num [Formula.integerMass, cyclo48Carbon]

/-- An ion assembled without fragmentation from cyclo[48]carbon, E, and
protons.  `charge` is the magnitude of its positive charge. -/
structure IonIdentity where
  cyclo48Count : ℕ
  macrocycleECount : ℕ
  protonCount : ℕ
  charge : ℕ
  deriving DecidableEq, Repr

namespace IonIdentity

/-- Molecular formula after adding all intact components and protons. -/
def formula (i : IonIdentity) : Formula :=
  Formula.add
    (Formula.add
      (Formula.scale i.cyclo48Count cyclo48Carbon)
      (Formula.scale i.macrocycleECount macrocycleE))
    (addedProtons i.protonCount)

/-- The integer nominal mass of the charged composition. -/
def nominalMass (i : IonIdentity) : ℕ := i.formula.integerMass

/-- Exact integral `m/z`: using the cross-multiplied equation also proves
that no remainder was discarded by natural-number division. -/
def HasMZ (i : IonIdentity) (mz : ℕ) : Prop :=
  0 < i.charge ∧ i.nominalMass = mz * i.charge

end IonIdentity

/-- The worked example from the answer sheet: `[E + H]⁺`. -/
def ion591 : IonIdentity where
  cyclo48Count := 0
  macrocycleECount := 1
  protonCount := 1
  charge := 1

/-- Suggested `m/z = 783` identity: `[C₄₈ + 3E + 3H]³⁺`. -/
def ion783 : IonIdentity where
  cyclo48Count := 1
  macrocycleECount := 3
  protonCount := 3
  charge := 3

/-- Suggested `m/z = 879` identity: `[C₄₈ + 2E + 2H]²⁺`. -/
def ion879 : IonIdentity where
  cyclo48Count := 1
  macrocycleECount := 2
  protonCount := 2
  charge := 2

/-- Suggested `m/z = 1174` identity: `[C₄₈ + 3E + 2H]²⁺`. -/
def ion1174 : IonIdentity where
  cyclo48Count := 1
  macrocycleECount := 3
  protonCount := 2
  charge := 2

theorem worked_example_591 :
    ion591.formula =
      { carbon := 40, hydrogen := 35, nitrogen := 2, oxygen := 3 } ∧
    ion591.HasMZ 591 := by
  constructor <;>
    norm_num [ion591, IonIdentity.formula, Formula.add, Formula.scale,
      addedProtons, cyclo48Carbon, macrocycleE, IonIdentity.HasMZ,
      IonIdentity.nominalMass, Formula.integerMass]

/-- Full formula, charge, and exact mass-to-charge proof for the 783 ion. -/
theorem ion_783_identity :
    ion783.cyclo48Count = 1 ∧
    ion783.macrocycleECount = 3 ∧
    ion783.protonCount = 3 ∧
    ion783.charge = 3 ∧
    ion783.formula =
      { carbon := 168, hydrogen := 105, nitrogen := 6, oxygen := 9 } ∧
    ion783.HasMZ 783 := by
  norm_num [ion783, IonIdentity.HasMZ, IonIdentity.nominalMass,
    IonIdentity.formula, Formula.integerMass, Formula.add, Formula.scale,
    addedProtons, cyclo48Carbon, macrocycleE]

/-- Full formula, charge, and exact mass-to-charge proof for the 879 ion. -/
theorem ion_879_identity :
    ion879.cyclo48Count = 1 ∧
    ion879.macrocycleECount = 2 ∧
    ion879.protonCount = 2 ∧
    ion879.charge = 2 ∧
    ion879.formula =
      { carbon := 128, hydrogen := 70, nitrogen := 4, oxygen := 6 } ∧
    ion879.HasMZ 879 := by
  norm_num [ion879, IonIdentity.HasMZ, IonIdentity.nominalMass,
    IonIdentity.formula, Formula.integerMass, Formula.add, Formula.scale,
    addedProtons, cyclo48Carbon, macrocycleE]

/-- Full formula, charge, and exact mass-to-charge proof for the 1174 ion. -/
theorem ion_1174_identity :
    ion1174.cyclo48Count = 1 ∧
    ion1174.macrocycleECount = 3 ∧
    ion1174.protonCount = 2 ∧
    ion1174.charge = 2 ∧
    ion1174.formula =
      { carbon := 168, hydrogen := 104, nitrogen := 6, oxygen := 9 } ∧
    ion1174.HasMZ 1174 := by
  norm_num [ion1174, IonIdentity.HasMZ, IonIdentity.nominalMass,
    IonIdentity.formula, Formula.integerMass, Formula.add, Formula.scale,
    addedProtons, cyclo48Carbon, macrocycleE]

/-- All three requested outputs in the order used by `TASK.json`. -/
theorem requested_ion_identities :
    ion783.HasMZ 783 ∧ ion879.HasMZ 879 ∧ ion1174.HasMZ 1174 := by
  norm_num [ion783, ion879, ion1174, IonIdentity.HasMZ,
    IonIdentity.nominalMass, IonIdentity.formula, Formula.integerMass,
    Formula.add, Formula.scale, addedProtons, cyclo48Carbon, macrocycleE]

#print axioms ion_783_identity
#print axioms ion_879_identity
#print axioms ion_1174_identity
#print axioms requested_ion_identities

end IChO2026Problems.T6A4
