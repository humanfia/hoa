import Mathlib
import IChO2026Chem.Core
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory Problem 3, Part 3.2 (T3-A2)

Source: `theory_problem.pdf`, page Q3-2 (printed page 26).

> **3.2** *Calculate the internal diameter, d, in Å, of the honeycomb for COF-2,
> with the following assumptions:
> • C–C/C=C (arenes) = 1.39 Å
> • C–B = 1.56 Å
> • B–O = 1.38 Å
> • Note, the diameter of a circle, d, inscribed inside a hexagon, is given by
>   d = √3a, where a is the side length of the hexagon.
> • Neglect the width of the linkers.*

## Structure of COF-2 (from page Q3-1)

COF-2 is built from benzene-1,3,5-triboronic acid (monomer A2) by dehydration
into planar boroxine rings (B₃O₃, regular six-membered rings with side
B–O = 1.38 Å).  In the honeycomb, the vertices of each pore hexagon are the
boroxine ring centres and each side passes through one benzene ring bridging
two boroxine rings.  Hence one side `a` spans the collinear chain

  boroxine centre → B (1.38) — C–B (1.56) — benzene para crossing,
  C(ipso)…C(para) = 2 × C–C (2 × 1.39) — C–B (1.56) — B → next boroxine
  centre (1.38).

The boroxine ring is modelled as a regular hexagon of side B–O; its
circumradius (centre to a B vertex) therefore equals 1.38 Å.  The benzene ring
is modelled as a regular hexagon of side C–C = 1.39 Å, whose para diameter is
2 × 1.39 Å.  The C–B bonds are collinear with the side because both rings are
trigonal (120° interior angles for boroxine, and the arene C–C bonds on the
side axis are perpendicular to it).  With the linker width neglected, no part
of the boroxine ring protrudes inside the pore hexagon, so `d = √3 a`.

  a = 2·(B–O) + 2·(C–B) + 2·(C–C) = 2.76 + 3.12 + 2.78 = 8.66 Å
  d = √3 · 8.66 Å ≈ 14.9996 Å ≈ 15.0 Å   (three significant figures)
-/

namespace IChO2026T3A2

open IChO2026Chem.Reporting

/-! ## Problem inputs (exact as printed) -/

/-- Stipulated C–C/C=C arene bond length, 1.39 Å. -/
def cC : ℝ := 1.39

/-- Stipulated C–B bond length, 1.56 Å. -/
def cB : ℝ := 1.56

/-- Stipulated B–O bond length, 1.38 Å. -/
def bO : ℝ := 1.38

/-- Side length `a` of the COF-2 pore hexagon: two boroxine circumradii
(B–O), two aryl C–B bonds and one benzene para crossing (2·C–C). -/
def cof2HexagonSide : ℝ := 2 * bO + 2 * cB + 2 * cC

/-- Internal diameter `d = √3 · a`, the formula stipulated in the problem. -/
noncomputable def cof2InternalDiameter : ℝ := Real.sqrt 3 * cof2HexagonSide

/-! ## Raw evaluation -/

theorem cof2HexagonSide_eq : cof2HexagonSide = 8.66 := by
  norm_num [cof2HexagonSide, bO, cB, cC]

/-- Squared value of the diameter: d² = 3a² = 2249868/10000 = 224.9868. -/
theorem cof2InternalDiameter_sq :
    cof2InternalDiameter ^ 2 = 2249868 / 10000 := by
  have h : cof2InternalDiameter ^ 2 = 3 * cof2HexagonSide ^ 2 := by
    unfold cof2InternalDiameter
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [h, cof2HexagonSide_eq]
  norm_num

theorem cof2InternalDiameter_nonneg : 0 ≤ cof2InternalDiameter := by
  unfold cof2InternalDiameter
  exact mul_nonneg (Real.sqrt_nonneg _) (by rw [cof2HexagonSide_eq]; norm_num)

/-- Strict lower bound via square-root monotonicity: 14.95 < d. -/
theorem cof2InternalDiameter_lower :
    (1495 / 100 : ℝ) < cof2InternalDiameter := by
  have hnn := cof2InternalDiameter_nonneg
  have h1495pos : (0 : ℝ) ≤ 1495 / 100 := by norm_num
  calc (1495 / 100 : ℝ)
      = Real.sqrt (((1495 / 100 : ℝ)) ^ 2) := (Real.sqrt_sq h1495pos).symm
    _ < Real.sqrt (cof2InternalDiameter ^ 2) := by
        apply Real.sqrt_lt_sqrt (by positivity)
        rw [cof2InternalDiameter_sq]; norm_num
    _ = cof2InternalDiameter := Real.sqrt_sq hnn

/-- Strict upper bound via square-root monotonicity: d < 15.05. -/
theorem cof2InternalDiameter_upper :
    cof2InternalDiameter < (1505 / 100 : ℝ) := by
  have hnn := cof2InternalDiameter_nonneg
  have h1505pos : (0 : ℝ) ≤ 1505 / 100 := by norm_num
  calc cof2InternalDiameter
      = Real.sqrt (cof2InternalDiameter ^ 2) := (Real.sqrt_sq hnn).symm
    _ < Real.sqrt ((1505 / 100 : ℝ) ^ 2) := by
        apply Real.sqrt_lt_sqrt (by rw [cof2InternalDiameter_sq]; positivity)
        rw [cof2InternalDiameter_sq]; norm_num
    _ = 1505 / 100 := Real.sqrt_sq h1505pos

/-- Exact raw bounds locating `d` strictly inside the 15.0 Å reporting window. -/
theorem cof2InternalDiameter_bounds :
    1495 / 100 < cof2InternalDiameter ∧ cof2InternalDiameter < 1505 / 100 :=
  ⟨cof2InternalDiameter_lower, cof2InternalDiameter_upper⟩

/-- Three-significant-figure reported value: 15.0 Å. -/
theorem cof2InternalDiameter_three_sf :
    |cof2InternalDiameter - 15.0| < 0.05 := by
  have hb := cof2InternalDiameter_bounds
  have h : |cof2InternalDiameter - (150 / 10 : ℝ)| < 1 / 20 := by
    rw [abs_lt]
    constructor
    · have s : -(1 / 20 : ℝ) < cof2InternalDiameter - 150 / 10 := by
        linear_combination hb.1
      exact s
    · have s : cof2InternalDiameter - 150 / 10 < 1 / 20 := by
        linear_combination hb.2
      exact s
  convert h using 3 <;> norm_num1

/-! ## Reporting contract

The uniform blind-evaluation default requests three significant figures.
For a value near 15 the corresponding decimal quantum is 0.1; the raw value
lies in `[15.0 − 0.05, 15.0 + 0.05)`, so the reported value is 15.0 Å with
exact ties rounded away from zero (none occurs here, since d > 14.95). -/

/-- The unique multiple of 0.1 within half a quantum of `d` is 15.0. -/
theorem cof2InternalDiameter_rounding_uniqueness {k : ℤ}
    (h : |(0.1 : ℝ) * k - cof2InternalDiameter| ≤ 0.05) : (15 : ℝ) = 0.1 * k := by
  have hb := cof2InternalDiameter_bounds
  have h' : |(1 / 10 : ℝ) * k - cof2InternalDiameter| ≤ 1 / 20 := by
    have e1 : (1 / 10 : ℝ) = 0.1 := by norm_num1
    have e2 : (1 / 20 : ℝ) = 0.05 := by norm_num1
    rw [e1, e2]
    exact h
  obtain ⟨hle, heq⟩ := abs_le.mp h'
  -- hle : −(1/20) ≤ (1/10) k − d,  heq : (1/10) k − d ≤ 1/20
  have hupper : (1 / 10 : ℝ) * k < 151 / 10 := by
    have step1 : (1/10 : ℝ) * k ≤ cof2InternalDiameter + 1/20 := by
      linear_combination heq
    have step2 : cof2InternalDiameter + 1/20 < 1505/100 + 1/20 := by
      linear_combination hb.2
    have step3 : (1505:ℝ)/100 + 1/20 = 151/10 := by norm_num
    exact lt_of_le_of_lt step1 (lt_of_lt_of_eq step2 step3)
  have hlower : (149 / 10 : ℝ) < 1/10 * k := by
    have step1 : cof2InternalDiameter - 1/20 ≤ (1/10 : ℝ) * k := by
      linear_combination hle
    have step2 : 1495/100 - 1/20 < cof2InternalDiameter - 1/20 := by
      linear_combination hb.1
    have step3 : (149/10:ℝ) = 1495/100 - 1/20 := by norm_num
    exact lt_of_eq_of_lt step3 (lt_of_lt_of_le step2 step1)
  have hk : k = 150 := by
    have h1 : k < 151 := by
      by_contra hc
      have hc' : (151 : ℤ) ≤ k := by omega
      have hkr : (151 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hc'
      have hmul : (1/10 : ℝ) * 151 ≤ 1/10 * k := by
        linear_combination (1/10:ℝ) * hkr
      have hmul' : (151/10 : ℝ) ≤ 1/10 * k := by
        calc (151/10 : ℝ) = 1/10 * 151 := by norm_num
        _ ≤ 1/10 * k := hmul
      exact absurd (lt_of_le_of_lt hmul' hupper) (lt_irrefl _)
    have h2 : 149 < k := by
      by_contra hc
      have hc' : k ≤ (149 : ℤ) := by omega
      have hkr : (k : ℝ) ≤ (149 : ℝ) := by exact_mod_cast hc'
      have hmul : (1/10 : ℝ) * k ≤ 1/10 * 149 := by
        linear_combination (1/10:ℝ) * hkr
      have hmul' : (1/10 : ℝ) * k ≤ 149/10 := by
        calc (1/10 : ℝ) * k ≤ 1/10 * 149 := hmul
        _ = 149/10 := by norm_num
      exact absurd (lt_of_lt_of_le hlower hmul') (lt_irrefl _)
    omega
  rw [hk]; norm_num

theorem cof2InternalDiameter_reported :
    ReportsAtQuantum cof2InternalDiameter 15 0.1 := by
  have hb := cof2InternalDiameter_bounds
  obtain ⟨hq, hmult, hwin⟩ :
      ReportsAtQuantum cof2InternalDiameter (150/10 : ℝ) (1/10 : ℝ) := by
    refine ⟨by norm_num, ⟨150, by norm_num⟩, ?_⟩
    simp only [show (0 : ℝ) ≤ cof2InternalDiameter from cof2InternalDiameter_nonneg,
      ↓reduceIte]
    constructor
    · -- (150/10) − (1/10)/2 = 1495/100 ≤ d
      have step : (150/10 : ℝ) - (1/10)/2 ≤ cof2InternalDiameter := by
        linear_combination hb.1
      exact step
    · -- d < (150/10) + (1/10)/2 = 1505/100
      have step : cof2InternalDiameter < (150/10 : ℝ) + (1/10)/2 := by
        linear_combination hb.2
      exact step
  exact ⟨by norm_num, by
    obtain ⟨kk, hkk⟩ := hmult
    refine ⟨kk, by convert hkk <;> norm_num⟩,
    by
      rw [if_pos cof2InternalDiameter_nonneg] at hwin
      rw [if_pos cof2InternalDiameter_nonneg]
      convert hwin using 3 <;> norm_num⟩

/-- The full numeric submission for the requested output
`cof2_internal_diameter`. -/
noncomputable def cof2Submission : NumericSubmission where
  rawValue := cof2InternalDiameter
  reportedValue := 15
  reportingQuantum := 0.1

theorem cof2Submission_valid :
    ValidNumericSubmission cof2InternalDiameter cof2Submission :=
  ⟨rfl, cof2InternalDiameter_reported⟩

#print axioms cof2HexagonSide_eq
#print axioms cof2InternalDiameter_sq
#print axioms cof2InternalDiameter_bounds
#print axioms cof2InternalDiameter_rounding_uniqueness
#print axioms cof2InternalDiameter_three_sf
#print axioms cof2InternalDiameter_reported
#print axioms cof2Submission_valid

end IChO2026T3A2
