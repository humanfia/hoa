import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))

theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  sorry
