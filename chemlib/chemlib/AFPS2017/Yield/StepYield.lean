import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.Real.Basic

/-!
# Multiplicative step-yield model

This module treats each step yield as a supplied model input in the closed
interval `[0, 1]`.  Cumulative yield is the finite product of those inputs; no
yield is inferred from protocol timing or analytical observations.

Source reference:

* Sanitized yield contract (`afps2017.yield.contract:question`).
-/

namespace AFPS2017.Yield

/-- A supplied step-yield value certified to lie in the closed unit interval. -/
structure StepYield : Type where
  /-- The supplied model value. -/
  value : ℝ
  /-- A step-yield value is nonnegative. -/
  nonnegative : 0 ≤ value
  /-- A step-yield value is at most one. -/
  atMostOne : value ≤ 1

/-- The cumulative yield of finitely many steps is their product. -/
def cumulativeStepYield (steps : List StepYield) : ℝ :=
  (steps.map StepYield.value).prod

/-- Cumulative step yield unfolds to the product of the supplied values. -/
theorem cumulativeStepYield_eq_product (steps : List StepYield) :
    cumulativeStepYield steps = (steps.map StepYield.value).prod :=
  rfl

/-- A common lower bound on every step gives the corresponding power lower
bound on cumulative yield. -/
theorem cumulativeStepYield_lower_bound (floor : ℝ) (floor_nonnegative : 0 ≤ floor)
    (_floor_atMostOne : floor ≤ 1) (steps : List StepYield)
    (each_atLeastFloor : ∀ step ∈ steps, floor ≤ step.value) :
    floor ^ steps.length ≤ cumulativeStepYield steps := by
  induction steps with
  | nil => simp [cumulativeStepYield]
  | cons step steps inductionHypothesis =>
      have step_atLeastFloor : floor ≤ step.value :=
        each_atLeastFloor step (by simp)
      have remaining_atLeastFloor :
          ∀ remaining ∈ steps, floor ≤ remaining.value := by
        intro remaining remaining_mem
        exact each_atLeastFloor remaining (List.mem_cons_of_mem step remaining_mem)
      calc
        floor ^ (step :: steps).length = floor * floor ^ steps.length := by
          simp [pow_succ, mul_comm]
        _ ≤ step.value * cumulativeStepYield steps :=
          mul_le_mul step_atLeastFloor
            (inductionHypothesis remaining_atLeastFloor)
            (pow_nonneg floor_nonnegative _) step.nonnegative
        _ = cumulativeStepYield (step :: steps) := by
          simp [cumulativeStepYield]

/-- Every cumulative step yield lies in the closed unit interval. -/
theorem cumulativeStepYield_mem_unit_interval (steps : List StepYield) :
    0 ≤ cumulativeStepYield steps ∧ cumulativeStepYield steps ≤ 1 := by
  induction steps with
  | nil => simp [cumulativeStepYield]
  | cons step steps inductionHypothesis =>
      constructor
      · simpa [cumulativeStepYield] using
          mul_nonneg step.nonnegative inductionHypothesis.1
      · have product_atMostOne :
            step.value * cumulativeStepYield steps ≤ (1 : ℝ) * 1 :=
          mul_le_mul step.atMostOne inductionHypothesis.2
            inductionHypothesis.1 zero_le_one
        simpa [cumulativeStepYield] using product_atMostOne

/-- Cumulative step yield is nonnegative. -/
theorem cumulativeStepYield_nonnegative (steps : List StepYield) :
    0 ≤ cumulativeStepYield steps :=
  (cumulativeStepYield_mem_unit_interval steps).1

/-- Repeating one step gives a natural power of its value. -/
theorem cumulativeStepYield_replicate (step : StepYield) (count : Nat) :
    cumulativeStepYield (List.replicate count step) = step.value ^ count := by
  simp [cumulativeStepYield]

end AFPS2017.Yield
