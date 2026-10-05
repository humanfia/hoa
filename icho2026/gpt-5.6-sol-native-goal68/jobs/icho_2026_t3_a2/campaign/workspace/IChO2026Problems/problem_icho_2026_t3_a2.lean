import IChO2026Chem.Reporting
import Mathlib

/-!
# IChO 2026 T3-A2: internal diameter of the COF-2 honeycomb

The official problem figure shows one idealized side of the COF-2 honeycomb as
the straight path between two neighbouring three-connected B3 centres.  With
linker width neglected, that path contains, in order, three arene increments,
one B--O increment, one C--B increment, the two arene increments across the
para-phenylene linker, and the reverse sequence at the other end.  Thus it has
eight arene C--C increments, two C--B increments, and two B--O increments.

The decimal bond lengths below are stipulated constants in the question, so
they are represented exactly.  Rounding is performed only after the exact raw
diameter has been obtained.
-/

namespace IChO2026Problems.problem_icho_2026_t3_a2

open IChO2026Chem.Reporting

/-! ## Problem inputs -/

/-- The three kinds of length increment supplied in T3-A2. -/
inductive BondKind where
  | areneCC
  | carbonBoron
  | boronOxygen
  deriving DecidableEq, Repr

/-- Exact bond lengths in angstroms, as printed in the problem. -/
noncomputable def bondLengthAngstrom : BondKind → ℝ
  | .areneCC => 139 / 100
  | .carbonBoron => 39 / 25
  | .boronOxygen => 69 / 50

/--
The centre-to-centre bond-length walk for one side of the idealized COF-2
honeycomb, read from the displayed molecular structure.  The two halves are
related by reversing the walk about the para-phenylene linker.
-/
def cof2SideWalk : List BondKind :=
  [ .areneCC, .areneCC, .areneCC,
    .boronOxygen, .carbonBoron,
    .areneCC, .areneCC,
    .carbonBoron, .boronOxygen,
    .areneCC, .areneCC, .areneCC ]

/-- The idealized side length `a`, before applying the supplied hexagon rule. -/
noncomputable def cof2SideLengthAngstrom : ℝ :=
  (cof2SideWalk.map bondLengthAngstrom).sum

/-- The unrounded answer obtained from the supplied rule `d = sqrt 3 * a`. -/
noncomputable def cof2RawDiameterAngstrom : ℝ :=
  Real.sqrt 3 * cof2SideLengthAngstrom

/-! ## Derived exact calculation -/

/-- The source figure's side walk contains exactly the claimed bond counts. -/
theorem cof2_side_bond_counts :
    cof2SideWalk.count .areneCC = 8 ∧
    cof2SideWalk.count .carbonBoron = 2 ∧
    cof2SideWalk.count .boronOxygen = 2 := by
  decide

/-- Summing the stipulated bond lengths gives `a = 17.00 Å` exactly. -/
theorem cof2_side_length_exact : cof2SideLengthAngstrom = 17 := by
  norm_num [cof2SideLengthAngstrom, cof2SideWalk, bondLengthAngstrom]

/-- Hence the unrounded internal diameter is exactly `17 * sqrt 3 Å`. -/
theorem cof2_internal_diameter_exact :
    cof2RawDiameterAngstrom = 17 * Real.sqrt 3 := by
  rw [cof2RawDiameterAngstrom, cof2_side_length_exact]
  ring

/-! ## Final answer-blind reporting boundary -/

/-- Rational bounds sufficient to determine the nearest 0.1 Å. -/
theorem sqrt_three_reporting_bounds :
    (587 : ℝ) / 340 ≤ Real.sqrt 3 ∧
    Real.sqrt 3 < (589 : ℝ) / 340 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    norm_num
  have hlower_sq : ((587 : ℝ) / 340) ^ 2 < 3 := by
    norm_num
  have hupper_sq : 3 < ((589 : ℝ) / 340) ^ 2 := by
    norm_num
  constructor <;> nlinarith

/-- The raw result lies in the half-open interval that rounds to `29.4 Å`. -/
theorem cof2_internal_diameter_rounding_interval :
    (147 : ℝ) / 5 - ((1 : ℝ) / 10) / 2 ≤ cof2RawDiameterAngstrom ∧
    cof2RawDiameterAngstrom < (147 : ℝ) / 5 + ((1 : ℝ) / 10) / 2 := by
  rw [cof2_internal_diameter_exact]
  rcases sqrt_three_reporting_bounds with ⟨hlower, hupper⟩
  constructor <;> nlinarith

/-- The solver-owned exact/raw and three-significant-figure submission. -/
noncomputable def cof2DiameterSubmission : NumericSubmission where
  rawValue := cof2RawDiameterAngstrom
  reportedValue := 147 / 5
  reportingQuantum := 1 / 10

/--
The requested output: the exact raw diameter is retained and its valid nearest
0.1 Å (three-significant-figure) report is `29.4 Å`.
-/
theorem cof2_internal_diameter_submission_valid :
    ValidNumericSubmission cof2RawDiameterAngstrom cof2DiameterSubmission := by
  refine ⟨rfl, ?_⟩
  refine ⟨by norm_num [cof2DiameterSubmission], ?_, ?_⟩
  · refine ⟨294, ?_⟩
    norm_num [cof2DiameterSubmission]
  · rw [if_pos]
    · simpa [cof2DiameterSubmission] using
        cof2_internal_diameter_rounding_interval
    · change 0 ≤ cof2RawDiameterAngstrom
      rw [cof2_internal_diameter_exact]
      positivity

/-- The numeric value placed in the answer-sheet blank is `29.4`. -/
theorem cof2_internal_diameter_reported :
    cof2DiameterSubmission.reportedValue = (147 : ℝ) / 5 := by
  rfl

#print axioms cof2_side_bond_counts
#print axioms cof2_side_length_exact
#print axioms cof2_internal_diameter_exact
#print axioms sqrt_three_reporting_bounds
#print axioms cof2_internal_diameter_rounding_interval
#print axioms cof2_internal_diameter_submission_valid
#print axioms cof2_internal_diameter_reported

end IChO2026Problems.problem_icho_2026_t3_a2
