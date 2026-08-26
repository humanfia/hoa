import ChemistryLib.Stochastic.PoissonProduct
import ChemistryLib.Stochastic.ReactionGenerator
import ChemistryLib.Stochastic.Stationary

/-!
# Poisson product forms on finite count classes

This module defines the finite-class normalizer and normalized Poisson product
form from ACK-2010, Section 4, equations (4.2)--(4.4) and Theorem 4.1,
specialized to finite count-state classes.  It records only the elementary
normalization facts: the normalizer is the finite sum of the raw Poisson
weights, and the class form divides each raw weight by that sum.
-/

open scoped BigOperators

namespace ChemistryLib.Stochastic

noncomputable section

/-- The finite sum of the Poisson product weights over a count-state class. -/
def classNormalization {Species : Type} [Fintype Species]
    (c : Species → ℝ) (Ω : Finset (CountState Species)) : ℝ :=
  ∑ x ∈ Ω, poissonProductWeight c x

/-- Positive parameters give a positive normalizer on a nonempty finite class. -/
theorem classNormalization_pos {Species : Type} [Fintype Species]
    (c : Species → ℝ) (Ω : Finset (CountState Species))
    (hc : ∀ i, 0 < c i) (hΩ : Ω.Nonempty) :
    0 < classNormalization c Ω := by
  classical
  unfold classNormalization
  exact Finset.sum_pos (fun x _hx ↦ poissonProductWeight_pos c hc x) hΩ

/-- The Poisson product weight restricted to a finite class and normalized. -/
def classProductForm {Species : Type} [Fintype Species]
    (c : Species → ℝ) (Ω : Finset (CountState Species)) (x : ↥Ω) : ℝ :=
  poissonProductWeight c x.1 / classNormalization c Ω

/-- Positive parameters and a positive normalizer give nonnegative class weights. -/
theorem classProductForm_nonneg {Species : Type} [Fintype Species]
    (c : Species → ℝ) (Ω : Finset (CountState Species))
    (hc : ∀ i, 0 < c i) (hZ : 0 < classNormalization c Ω) :
    ∀ x, 0 ≤ classProductForm c Ω x := by
  intro x
  exact (div_pos (poissonProductWeight_pos c hc x.1) hZ).le

/-- The normalized Poisson product weights on a finite class have unit mass. -/
theorem classProductForm_sum_eq_one {Species : Type} [Fintype Species]
    (c : Species → ℝ) (Ω : Finset (CountState Species))
    (hZ : 0 < classNormalization c Ω) :
    ∑ x, classProductForm c Ω x = 1 := by
  classical
  unfold classProductForm
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show ∑ x : ↥Ω, poissonProductWeight c x.1 = classNormalization c Ω by
    exact (Finset.sum_subtype Ω (fun _ ↦ Iff.rfl) (poissonProductWeight c)).symm]
  exact mul_inv_cancel₀ (ne_of_gt hZ)

end

end ChemistryLib.Stochastic
