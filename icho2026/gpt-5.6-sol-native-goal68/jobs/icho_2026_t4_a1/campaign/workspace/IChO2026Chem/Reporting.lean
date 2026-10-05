import Mathlib

/-!
# Answer-blind numerical reporting

This module fixes the reporting convention before any IChO target is solved.
All intermediate quantities remain exact real expressions.  A target may
choose a final display quantum from the problem statement (or the project-wide
default recorded in its source contract), but it may not change the interval
after seeing a desired decimal.
-/

namespace IChO2026Chem.Reporting

/-- A displayed measurement with last-place quantum `q` represents the closed
half-quantum interval around the printed value. -/
def ConsistentMeasurement (actual shown quantum : ℝ) : Prop :=
  0 < quantum ∧ |actual - shown| ≤ quantum / 2

/-- `reported` is the nearest multiple of `quantum` to `raw`, with exact ties
rounded away from zero.  This relation is used only at the final reporting
boundary; it must not be inserted between stages of a raw calculation. -/
def ReportsAtQuantum (raw reported quantum : ℝ) : Prop :=
  0 < quantum ∧
  (∃ k : ℤ, reported = quantum * k) ∧
  if 0 ≤ raw then
    reported - quantum / 2 ≤ raw ∧ raw < reported + quantum / 2
  else
    reported - quantum / 2 < raw ∧ raw ≤ reported + quantum / 2

/-- A solver-owned candidate keeps the exact raw value separate from its final
printed value and explicitly records the chosen final quantum. -/
structure NumericSubmission where
  rawValue : ℝ
  reportedValue : ℝ
  reportingQuantum : ℝ

/-- The target-independent contract for a numerical answer-blind submission. -/
def ValidNumericSubmission (rawExpression : ℝ) (s : NumericSubmission) : Prop :=
  s.rawValue = rawExpression ∧
  ReportsAtQuantum s.rawValue s.reportedValue s.reportingQuantum

theorem consistentMeasurement_nonnegativeQuantum
    {actual shown quantum : ℝ}
    (h : ConsistentMeasurement actual shown quantum) : 0 ≤ quantum := by
  exact le_of_lt h.1

theorem validNumericSubmission_raw
    {rawExpression : ℝ} {s : NumericSubmission}
    (h : ValidNumericSubmission rawExpression s) :
    s.rawValue = rawExpression := by
  exact h.1

end IChO2026Chem.Reporting
