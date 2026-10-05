import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 2, subquestion 3

The problem compares elementary steps (1) and (4).  Their mass-action rates
have the common factors `[HBrO₂]` and `[H⁺]`.  This file first proves the
general cancellation result (with the chemically relevant nonzero conditions),
then instantiates the printed data and verifies the requested numerical report.

All concentrations are represented by their numerical values in `mol dm⁻³`,
and the printed rate constants are represented in the coherent units displayed
in the problem.  No assertion from an answer key is used.
-/

namespace IChO2026Problems.T2A3

open IChO2026Chem.Reporting

noncomputable section

/-- Mass-action rate of elementary step (1),
`HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`. -/
def step1Rate
    (k1 hbrO2 bromate proton : ℝ) : ℝ :=
  k1 * hbrO2 * bromate * proton

/-- Mass-action rate of elementary step (4),
`HBrO₂ + Br⁻ + H⁺ → 2 HBrO`. -/
def step4Rate
    (k4 hbrO2 bromide proton : ℝ) : ℝ :=
  k4 * hbrO2 * bromide * proton

/-- At equal rates, cancellation of the two common, nonzero concentration
factors gives the general critical-bromide formula. -/
theorem switchBoundary_formula
    {k1 k4 hbrO2 bromate proton bromide : ℝ}
    (hk4 : k4 ≠ 0)
    (hhbrO2 : hbrO2 ≠ 0)
    (hproton : proton ≠ 0)
    (hboundary :
      step4Rate k4 hbrO2 bromide proton =
        step1Rate k1 hbrO2 bromate proton) :
    bromide = (k1 / k4) * bromate := by
  have hcommon : hbrO2 * proton ≠ 0 := mul_ne_zero hhbrO2 hproton
  have hcancelled : k4 * bromide = k1 * bromate := by
    apply mul_left_cancel₀ hcommon
    simpa [step1Rate, step4Rate, mul_assoc, mul_left_comm, mul_comm] using
      hboundary
  field_simp [hk4]
  nlinarith [hcancelled]

namespace ProblemInput

/-- Printed `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`. -/
def k1 : ℝ := 1.0 * 10 ^ 4

/-- Printed `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`. -/
def k4 : ℝ := 2.0 * 10 ^ 9

/-- Printed maintained bromate concentration, `[BrO₃⁻] = 0.06 M`. -/
def bromate : ℝ := 0.06

/-- Printed maintained proton concentration, `[H⁺] = 0.8 M`. -/
def proton : ℝ := 0.8

/-- Problem-stated fallback for `[HBrO₂]A`; only its positivity matters here. -/
def fallbackHBrO2A : ℝ := 1 / 10 ^ 5

/-- Problem-stated fallback for `[HBrO₂]B`; only its positivity matters here. -/
def fallbackHBrO2B : ℝ := 1 / 10 ^ 10

end ProblemInput

open ProblemInput

/-- The exact raw expression obtained from the equal-rate condition. -/
def bromideCriticalRaw : ℝ := (k1 / k4) * bromate

/-- The rate equality for the printed data occurs exactly at the raw critical
concentration.  The positivity hypothesis makes explicit the condition needed
to cancel `[HBrO₂]`; the printed `[H⁺] = 0.8 M` is proved positive internally. -/
theorem printedRates_equal_iff
    {hbrO2 bromide : ℝ}
    (hhbrO2 : 0 < hbrO2) :
    step4Rate k4 hbrO2 bromide proton =
        step1Rate k1 hbrO2 bromate proton ↔
      bromide = bromideCriticalRaw := by
  constructor
  · intro hboundary
    exact switchBoundary_formula
      (by norm_num [k4]) (ne_of_gt hhbrO2) (by norm_num [proton]) hboundary
  · intro hbromide
    rw [hbromide]
    norm_num [bromideCriticalRaw, step1Rate, step4Rate,
      k1, k4, bromate, proton]
    ring

/-- Above the critical bromide concentration, elementary step (4) is faster
than elementary step (1), as required for the switch from process A to B. -/
theorem step4_exceeds_step1_iff
    {hbrO2 bromide : ℝ}
    (hhbrO2 : 0 < hbrO2) :
    step1Rate k1 hbrO2 bromate proton <
        step4Rate k4 hbrO2 bromide proton ↔
      bromideCriticalRaw < bromide := by
  have hcommon : 0 < hbrO2 * proton :=
    mul_pos hhbrO2 (by norm_num [proton])
  constructor
  · intro hrate
    have hfactored :
        (hbrO2 * proton) * (k1 * bromate) <
          (hbrO2 * proton) * (k4 * bromide) := by
      calc
        (hbrO2 * proton) * (k1 * bromate) =
            step1Rate k1 hbrO2 bromate proton := by
          unfold step1Rate
          ring
        _ < step4Rate k4 hbrO2 bromide proton := hrate
        _ = (hbrO2 * proton) * (k4 * bromide) := by
          unfold step4Rate
          ring
    have hcoeff : k1 * bromate < k4 * bromide :=
      lt_of_mul_lt_mul_left hfactored (le_of_lt hcommon)
    norm_num [bromideCriticalRaw, k1, k4, bromate] at hcoeff ⊢
    linarith
  · intro hbromide
    have hcoeff : k1 * bromate < k4 * bromide := by
      norm_num [bromideCriticalRaw, k1, k4, bromate] at hbromide ⊢
      linarith
    calc
      step1Rate k1 hbrO2 bromate proton =
          (hbrO2 * proton) * (k1 * bromate) := by
        unfold step1Rate
        ring
      _ < (hbrO2 * proton) * (k4 * bromide) :=
        mul_lt_mul_of_pos_left hcoeff hcommon
      _ = step4Rate k4 hbrO2 bromide proton := by
        unfold step4Rate
        ring

/-- Below the critical bromide concentration, elementary step (1) is faster
than elementary step (4), the reverse rate ordering required for process A. -/
theorem step1_exceeds_step4_iff
    {hbrO2 bromide : ℝ}
    (hhbrO2 : 0 < hbrO2) :
    step4Rate k4 hbrO2 bromide proton <
        step1Rate k1 hbrO2 bromate proton ↔
      bromide < bromideCriticalRaw := by
  have hcommon : 0 < hbrO2 * proton :=
    mul_pos hhbrO2 (by norm_num [proton])
  constructor
  · intro hrate
    have hfactored :
        (hbrO2 * proton) * (k4 * bromide) <
          (hbrO2 * proton) * (k1 * bromate) := by
      calc
        (hbrO2 * proton) * (k4 * bromide) =
            step4Rate k4 hbrO2 bromide proton := by
          unfold step4Rate
          ring
        _ < step1Rate k1 hbrO2 bromate proton := hrate
        _ = (hbrO2 * proton) * (k1 * bromate) := by
          unfold step1Rate
          ring
    have hcoeff : k4 * bromide < k1 * bromate :=
      lt_of_mul_lt_mul_left hfactored (le_of_lt hcommon)
    norm_num [bromideCriticalRaw, k1, k4, bromate] at hcoeff ⊢
    linarith
  · intro hbromide
    have hcoeff : k4 * bromide < k1 * bromate := by
      norm_num [bromideCriticalRaw, k1, k4, bromate] at hbromide ⊢
      linarith
    calc
      step4Rate k4 hbrO2 bromide proton =
          (hbrO2 * proton) * (k4 * bromide) := by
        unfold step4Rate
        ring
      _ < (hbrO2 * proton) * (k1 * bromate) :=
        mul_lt_mul_of_pos_left hcoeff hcommon
      _ = step1Rate k1 hbrO2 bromate proton := by
        unfold step1Rate
        ring

/-- The problem-supplied fallback stationary concentrations are positive, so
the equal-rate and rate-order theorems apply in both processes without using
any result from subquestion 2.2. -/
theorem fallbackHBrO2_levels_positive :
    0 < fallbackHBrO2A ∧ 0 < fallbackHBrO2B := by
  norm_num [fallbackHBrO2A, fallbackHBrO2B]

/-- Requested exact output:
`[Br⁻]critical = 3 / 10⁷ mol dm⁻³`. -/
theorem bromide_critical :
    bromideCriticalRaw = (3 / 10 ^ 7 : ℝ) := by
  norm_num [bromideCriticalRaw, k1, k4, bromate]

/-- The answer-blind three-significant-figure submission.  Its numerical value
is `3.00 × 10⁻⁷`; the `10⁻⁹` quantum records the two trailing significant
decimal places without changing the exact raw value. -/
def bromideCriticalSubmission : NumericSubmission where
  rawValue := bromideCriticalRaw
  reportedValue := 3 / 10 ^ 7
  reportingQuantum := 1 / 10 ^ 9

/-- The reported `3.00 × 10⁻⁷ mol dm⁻³` is a valid nearest-quantum report of
the unrounded raw expression. -/
theorem bromide_critical_reported :
    ValidNumericSubmission bromideCriticalRaw bromideCriticalSubmission := by
  refine ⟨rfl, ?_⟩
  change ReportsAtQuantum bromideCriticalRaw (3 / 10 ^ 7) (1 / 10 ^ 9)
  rw [bromide_critical]
  refine ⟨by norm_num, ?_, ?_⟩
  · refine ⟨(300 : ℤ), ?_⟩
    norm_num
  · norm_num

#print axioms switchBoundary_formula
#print axioms printedRates_equal_iff
#print axioms step4_exceeds_step1_iff
#print axioms step1_exceeds_step4_iff
#print axioms fallbackHBrO2_levels_positive
#print axioms bromide_critical
#print axioms bromide_critical_reported

end

end IChO2026Problems.T2A3
