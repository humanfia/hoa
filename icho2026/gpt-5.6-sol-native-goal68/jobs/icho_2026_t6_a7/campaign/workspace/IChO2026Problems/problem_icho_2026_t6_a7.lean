import Mathlib

/-!
# IChO 2026, theory problem 6.7

This file formalizes the electron count for the global conjugated circuit of
the six-porphyrin nanoring `P6` and the application of Hückel's `4k + 2`
rule requested in part 6.7.

The source-image interpretation is isolated in `ProblemInput`.  Everything
after that namespace is a derived definition or theorem.
-/

namespace IChO2026Problems.ProblemIcho2026T6A7

namespace ProblemInput

/-- The label and repeat-unit bracket in the supplied structure show that
`P6` contains six porphyrin units. -/
def porphyrinUnits : ℕ := 6

/-- Along one continuous global route through a porphyrin, the displayed
conjugated path contains five occupied pi-electron pairs, hence ten
pi electrons. -/
def porphyrinPathElectronPairsPerUnit : ℕ := 5

/-- The butadiyne connection supplies one pair from each of its two triple
bonds to the continuous conjugated channel, hence two pairs per repeat. -/
def linkerPathElectronPairsPerUnit : ℕ := 2

end ProblemInput

/-- The number of pi electrons contributed by one porphyrin--butadiyne
repeat to the global circuit. -/
def piElectronsPerUnit : ℕ :=
  2 * (ProblemInput.porphyrinPathElectronPairsPerUnit +
    ProblemInput.linkerPathElectronPairsPerUnit)

/-- The neutral global circuit electron count of `P6`. -/
def neutralGlobalPiElectrons : ℕ :=
  ProblemInput.porphyrinUnits * piElectronsPerUnit

/-- The electron count after oxidative removal of `removed` electrons. -/
def oxidizedGlobalPiElectrons (removed : ℕ) : ℕ :=
  neutralGlobalPiElectrons - removed

/-- A physically meaningful oxidation removes a positive number of electrons
and no more electrons than are present in the neutral global circuit. -/
def ValidOxidativeRemoval (removed : ℕ) : Prop :=
  0 < removed ∧ removed ≤ neutralGlobalPiElectrons

/-- Hückel's ground-state aromatic electron-count rule. -/
def HuckelAromatic (electrons : ℕ) : Prop :=
  ∃ k : ℕ, electrons = 4 * k + 2

/-- An oxidation amount is aromatic when it is valid and leaves a Hückel
`4k + 2` global circuit. -/
def AromaticRemoval (removed : ℕ) : Prop :=
  ValidOxidativeRemoval removed ∧
    HuckelAromatic (oxidizedGlobalPiElectrons removed)

/-- `removed` is the least positive oxidative removal that makes the global
circuit Hückel-aromatic. -/
def IsMinimumAromaticRemoval (removed : ℕ) : Prop :=
  AromaticRemoval removed ∧
    ∀ candidate : ℕ, AromaticRemoval candidate → removed ≤ candidate

theorem pi_electrons_per_unit_eq_fourteen : piElectronsPerUnit = 14 := by
  norm_num [piElectronsPerUnit, ProblemInput.porphyrinPathElectronPairsPerUnit,
    ProblemInput.linkerPathElectronPairsPerUnit]

theorem neutral_global_pi_electrons_eq_eighty_four :
    neutralGlobalPiElectrons = 84 := by
  norm_num [neutralGlobalPiElectrons, ProblemInput.porphyrinUnits,
    piElectronsPerUnit, ProblemInput.porphyrinPathElectronPairsPerUnit,
    ProblemInput.linkerPathElectronPairsPerUnit]

theorem removal_two_leaves_eighty_two :
    oxidizedGlobalPiElectrons 2 = 82 := by
  norm_num [oxidizedGlobalPiElectrons, neutralGlobalPiElectrons,
    ProblemInput.porphyrinUnits, piElectronsPerUnit,
    ProblemInput.porphyrinPathElectronPairsPerUnit,
    ProblemInput.linkerPathElectronPairsPerUnit]

theorem eighty_two_is_huckel_aromatic : HuckelAromatic 82 := by
  refine ⟨20, ?_⟩
  norm_num

theorem removal_two_is_aromatic : AromaticRemoval 2 := by
  constructor
  · norm_num [ValidOxidativeRemoval, neutralGlobalPiElectrons,
      ProblemInput.porphyrinUnits, piElectronsPerUnit,
      ProblemInput.porphyrinPathElectronPairsPerUnit,
      ProblemInput.linkerPathElectronPairsPerUnit]
  · simpa [removal_two_leaves_eighty_two] using eighty_two_is_huckel_aromatic

/-- Any positive valid removal that satisfies Hückel's rule is at least two.
In particular, removing just one electron leaves 83, which cannot be `4k+2`. -/
theorem any_aromatic_removal_at_least_two
    {removed : ℕ} (h : AromaticRemoval removed) : 2 ≤ removed := by
  rcases h with ⟨⟨hpositive, hbounded⟩, k, hcount⟩
  simp only [oxidizedGlobalPiElectrons] at hcount
  rw [neutral_global_pi_electrons_eq_eighty_four] at hcount hbounded
  omega

/-- Requested output `n(e)`: two is the minimum number of electrons that
must be removed. -/
theorem minimum_electrons_removed : IsMinimumAromaticRemoval 2 := by
  exact ⟨removal_two_is_aromatic, fun _ h => any_aromatic_removal_at_least_two h⟩

/-- Requested output `n(t)`: after that minimum removal, the global circuit
contains 82 pi electrons. -/
theorem global_pi_electron_count : oxidizedGlobalPiElectrons 2 = 82 := by
  exact removal_two_leaves_eighty_two

/-- The two requested outputs as one checked result. -/
theorem requested_outputs :
    IsMinimumAromaticRemoval 2 ∧ oxidizedGlobalPiElectrons 2 = 82 := by
  exact ⟨minimum_electrons_removed, global_pi_electron_count⟩

/-- Completeness/uniqueness check: any pair satisfying the formal problem
specification is exactly `(n(e), n(t)) = (2, 82)`. -/
theorem requested_outputs_unique
    {removed total : ℕ}
    (hminimum : IsMinimumAromaticRemoval removed)
    (htotal : total = oxidizedGlobalPiElectrons removed) :
    removed = 2 ∧ total = 82 := by
  have hle : removed ≤ 2 := hminimum.2 2 removal_two_is_aromatic
  have hge : 2 ≤ removed := any_aromatic_removal_at_least_two hminimum.1
  have hremoved : removed = 2 := Nat.le_antisymm hle hge
  subst removed
  exact ⟨rfl, htotal.trans removal_two_leaves_eighty_two⟩

#print axioms minimum_electrons_removed
#print axioms global_pi_electron_count
#print axioms requested_outputs
#print axioms requested_outputs_unique

end IChO2026Problems.ProblemIcho2026T6A7
