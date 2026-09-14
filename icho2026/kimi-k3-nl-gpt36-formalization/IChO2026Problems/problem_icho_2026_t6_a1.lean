import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T6.1: Hückel systems of cyclocarbons

## Assumptions represented by the model

The problem supplies four neutral cyclocarbons, identifies the two spin states
of `C₁₃`, and asks that Hückel's rule be applied to their distinct π systems.
The standard cyclocarbon electron model used here has two perpendicular,
fully-conjugated cyclic π systems.  An even closed-shell `Cₙ` puts `n`
electrons in each system.  Triplet `C₁₃` has one unpaired electron and thirteen
π electrons in each system.  Its closed-shell singlet transfers the pair into
one system, giving the conserving split `14 + 12 = 2 * 13`.

The Hückel classifier below is not an answer table: it uniformly classifies an
eligible closed-shell cyclic conjugated system from its electron count modulo
four.  The requested entries are obtained by filtering the two orientations.

## Targets

The eight final theorems expose, in the source order, the requested exact
integer counts of aromatic and anti-aromatic π systems.
-/

namespace IChO2026Problems.T6A1

/-- The two geometrically distinct π systems of an sp-hybridized cyclocarbon. -/
inductive PiOrientation where
  | inPlane
  | outOfPlane
  deriving DecidableEq, Fintype, Repr

/-- The four species/electronic states named by T6.1. -/
inductive CyclocarbonForm where
  | c18
  | c16
  | tripletC13
  | singletC13
  deriving DecidableEq, Fintype, Repr

/-- Occupancy patterns needed to instantiate the standard two-loop model. -/
inductive OccupancyPattern where
  | evenClosedShell
  | oddTriplet
  | oddClosedShellSinglet
  deriving DecidableEq, Repr

/-- Number of carbon atoms in each source-named cyclocarbon. -/
def carbonCount : CyclocarbonForm → ℕ
  | .c18 => 18
  | .c16 => 16
  | .tripletC13 => 13
  | .singletC13 => 13

/-- Spin `S` explicitly printed for the two `C₁₃` forms; it is not printed for
`C₁₈` or `C₁₆`. -/
def statedSpin : CyclocarbonForm → Option ℕ
  | .c18 => none
  | .c16 => none
  | .tripletC13 => some 1
  | .singletC13 => some 0

/-- Source-directed electronic configuration used before applying Hückel's
rule.  The even species are ordinary closed-shell cyclocarbons, while the two
`C₁₃` constructors retain the spin distinction printed in the question. -/
def occupancyPattern : CyclocarbonForm → OccupancyPattern
  | .c18 => .evenClosedShell
  | .c16 => .evenClosedShell
  | .tripletC13 => .oddTriplet
  | .singletC13 => .oddClosedShellSinglet

/-- Data relevant to Hückel classification for one distinct π system. -/
structure PiSystem where
  orientation : PiOrientation
  electronCount : ℕ
  unpairedElectronCount : ℕ
  cyclic : Bool
  fullyConjugated : Bool
  deriving DecidableEq, Repr

/-- Electron count in either perpendicular π system.  This construction is
uniform in the ring size and occupancy pattern; the `C₁₃` singlet's two
orientations differ only by which loop receives the paired electrons. -/
def piElectronCount (form : CyclocarbonForm)
    (orientation : PiOrientation) : ℕ :=
  match occupancyPattern form with
  | .evenClosedShell => carbonCount form
  | .oddTriplet => carbonCount form
  | .oddClosedShellSinglet =>
      match orientation with
      | .inPlane => carbonCount form + 1
      | .outOfPlane => carbonCount form - 1

/-- Number of unpaired electrons carried by one π loop in the standard model. -/
def piUnpairedElectronCount (form : CyclocarbonForm) : ℕ :=
  match occupancyPattern form with
  | .evenClosedShell => 0
  | .oddTriplet => 1
  | .oddClosedShellSinglet => 0

/-- The concrete π system supplied to the Hückel classifier. -/
def standardPiSystem (form : CyclocarbonForm)
    (orientation : PiOrientation) : PiSystem :=
  { orientation := orientation
    electronCount := piElectronCount form orientation
    unpairedElectronCount := piUnpairedElectronCount form
    cyclic := true
    fullyConjugated := true }

/-- A loop is eligible for the ground-state Hückel classification only when it
is cyclic, fully conjugated, and closed-shell. -/
abbrev HuckelEligible (system : PiSystem) : Prop :=
  system.cyclic = true ∧
    system.fullyConjugated = true ∧
    system.unpairedElectronCount = 0

/-- The three possible outcomes when the ordinary Hückel rule is applied.
Open-shell loops remain `unclassified`, rather than being counted in either
requested column. -/
inductive HuckelClass where
  | aromatic
  | antiaromatic
  | unclassified
  deriving DecidableEq, Repr

/-- Uniform arithmetic statement of Hückel's rule: eligible `4k + 2` systems
are aromatic and eligible `4k` systems are anti-aromatic. -/
def huckelClass (system : PiSystem) : HuckelClass :=
  if HuckelEligible system then
    if system.electronCount % 4 = 2 then
      .aromatic
    else if system.electronCount % 4 = 0 then
      .antiaromatic
    else
      .unclassified
  else
    .unclassified

/-- Number of the two distinct orientations assigned a selected Hückel class. -/
def countHuckelClass (form : CyclocarbonForm)
    (classification : HuckelClass) : ℕ :=
  (Finset.univ.filter fun orientation : PiOrientation =>
    huckelClass (standardPiSystem form orientation) = classification).card

/-- Raw source-derived number for the aromatic column. -/
def aromaticCount (form : CyclocarbonForm) : ℕ :=
  countHuckelClass form .aromatic

/-- Raw source-derived number for the anti-aromatic column. -/
def antiaromaticCount (form : CyclocarbonForm) : ℕ :=
  countHuckelClass form .antiaromatic

/-- Auxiliary count showing that an open-shell system was retained rather than
silently deleted from the two-loop inventory. -/
def unclassifiedCount (form : CyclocarbonForm) : ℕ :=
  countHuckelClass form .unclassified

/-- Every species is audited over exactly the two perpendicular π systems. -/
theorem two_distinct_pi_systems : Fintype.card PiOrientation = 2 := by
  native_decide

/-- The two π-system electron ledgers conserve the `2n` π electrons of `Cₙ`. -/
theorem pi_electron_conservation (form : CyclocarbonForm) :
    (∑ orientation : PiOrientation, piElectronCount form orientation) =
      2 * carbonCount form := by
  cases form <;> native_decide

/-- The source-stated `C₁₃` spin distinction agrees with the modeled unpaired
electron inventory. -/
theorem c13_spin_inventory :
    statedSpin .tripletC13 = some 1 ∧
      (∑ orientation : PiOrientation,
          (standardPiSystem .tripletC13 orientation).unpairedElectronCount) = 2 ∧
      statedSpin .singletC13 = some 0 ∧
      (∑ orientation : PiOrientation,
      (standardPiSystem .singletC13 orientation).unpairedElectronCount) = 0 := by
  native_decide

/-- Both triplet loops remain present but are outside the closed-shell Hückel
classes. -/
theorem triplet_c13_unclassified :
    unclassifiedCount .tripletC13 = 2 := by
  native_decide

/-! ### Requested exact-integer outputs -/

/-- Requested output `c18_aromatic`. -/
theorem c18_aromatic : aromaticCount .c18 = 2 := by
  native_decide

/-- Requested output `c18_antiaromatic`. -/
theorem c18_antiaromatic : antiaromaticCount .c18 = 0 := by
  native_decide

/-- Requested output `c16_aromatic`. -/
theorem c16_aromatic : aromaticCount .c16 = 0 := by
  native_decide

/-- Requested output `c16_antiaromatic`. -/
theorem c16_antiaromatic : antiaromaticCount .c16 = 2 := by
  native_decide

/-- Requested output `triplet_c13_aromatic`. -/
theorem triplet_c13_aromatic : aromaticCount .tripletC13 = 0 := by
  native_decide

/-- Requested output `triplet_c13_antiaromatic`. -/
theorem triplet_c13_antiaromatic : antiaromaticCount .tripletC13 = 0 := by
  native_decide

/-- Requested output `singlet_c13_aromatic`. -/
theorem singlet_c13_aromatic : aromaticCount .singletC13 = 1 := by
  native_decide

/-- Requested output `singlet_c13_antiaromatic`. -/
theorem singlet_c13_antiaromatic : antiaromaticCount .singletC13 = 1 := by
  native_decide

/-- One conjunction covering every blank of the source table in source order. -/
theorem completed_table :
    aromaticCount .c18 = 2 ∧
      antiaromaticCount .c18 = 0 ∧
      aromaticCount .c16 = 0 ∧
      antiaromaticCount .c16 = 2 ∧
      aromaticCount .tripletC13 = 0 ∧
      antiaromaticCount .tripletC13 = 0 ∧
      aromaticCount .singletC13 = 1 ∧
      antiaromaticCount .singletC13 = 1 := by
  exact ⟨c18_aromatic, c18_antiaromatic, c16_aromatic, c16_antiaromatic,
    triplet_c13_aromatic, triplet_c13_antiaromatic,
    singlet_c13_aromatic, singlet_c13_antiaromatic⟩

end IChO2026Problems.T6A1
