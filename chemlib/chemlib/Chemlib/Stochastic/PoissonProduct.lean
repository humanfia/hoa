import Chemlib.Stochastic.CountState
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Poisson product weights

This module defines the raw finite product of Poisson factors used in
ACK-2010, Section 4, equation (4.2) and Theorem 4.1.  It records only the
weight and its elementary positivity property, before any restriction or
normalization.
-/

open scoped BigOperators

namespace Chemlib.Stochastic

noncomputable section

/-- The Poisson factor with parameter `c` at count `n`. -/
def poissonFactor : ℝ → ℕ → ℝ :=
  fun c n ↦ c ^ n * Real.exp (-c) / (n.factorial : ℝ)

/-- The raw product of the Poisson factors over a finite species type. -/
def poissonProductWeight {Species : Type} [Fintype Species]
    (c : Species → ℝ) (x : CountState Species) : ℝ :=
  ∏ i, poissonFactor (c i) (x i)

/-- Positive parameters give a strictly positive Poisson product weight. -/
theorem poissonProductWeight_pos {Species : Type} [Fintype Species]
    (c : Species → ℝ) (hc : ∀ i, 0 < c i) (x : CountState Species) :
    0 < poissonProductWeight c x := by
  unfold poissonProductWeight
  apply Finset.prod_pos
  intro i _hi
  unfold poissonFactor
  exact div_pos (mul_pos (pow_pos (hc i) _) (Real.exp_pos _))
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

end

end Chemlib.Stochastic
