import Chemlib.Stochastic.CountState
import Mathlib.Data.Real.Basic

/-!
# Stochastic mass-action propensities

This module defines the falling-factorial reaction intensity from ACK-2010,
Section 3.1, equations (3.3)--(3.4), as recorded by source artifact
`222b8bed89ef875d89943a8634560dc29758ab803d5ad7054cb639fe21280c3c` and the
sanitized research contract `research:ack_2010:ctmc_generator`.
-/

open scoped BigOperators

namespace Chemlib.Stochastic

/-- The number of ordered selections of `k` objects from `n` objects. -/
def fallingFactorial (n k : ℕ) : ℕ :=
  n.descFactorial k

/-- The propensity helper is Mathlib's descending factorial. -/
theorem fallingFactorial_eq_descFactorial (n k : ℕ) :
    fallingFactorial n k = n.descFactorial k := by
  rfl

/-- A falling factorial vanishes when more objects are requested than available. -/
theorem fallingFactorial_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    fallingFactorial n k = 0 := by
  exact Nat.descFactorial_of_lt h

/-- The stochastic mass-action intensity of reaction `r` at count state `x`. -/
def massActionPropensity {Species Complex Reaction : Type} [Fintype Species]
    (N : Chemlib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (r : Reaction) (x : CountState Species) : ℝ :=
  κ r * ∏ i, (fallingFactorial (x i) (N.reactant r i) : ℝ)

/-- A reaction with an unavailable reactant has zero propensity. -/
theorem massActionPropensity_eq_zero_of_not_canFire
    {Species Complex Reaction : Type} [Fintype Species]
    (N : Chemlib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (r : Reaction) (x : CountState Species)
    (h : ¬ CanFire N r x) :
    massActionPropensity N κ r x = 0 := by
  simp only [CanFire, not_forall] at h
  obtain ⟨i, hi⟩ := h
  have hlt : x i < N.reactant r i := Nat.lt_of_not_ge hi
  unfold massActionPropensity
  rw [Finset.prod_eq_zero (i := i) (by simp)
    (by simp [fallingFactorial_eq_zero_of_lt hlt])]
  simp

/-- Nonnegative stochastic rate constants give nonnegative propensities. -/
theorem massActionPropensity_nonneg
    {Species Complex Reaction : Type} [Fintype Species]
    (N : Chemlib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (r : Reaction) (x : CountState Species) :
    0 ≤ massActionPropensity N κ r x := by
  classical
  unfold massActionPropensity
  apply mul_nonneg (hκ r)
  induction (Finset.univ : Finset Species) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact mul_nonneg (Nat.cast_nonneg _) ih

end Chemlib.Stochastic
