import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Chemlib.Foundations.Stoichiometry

/-!
# Stoichiometric production yield

This module expresses the amount ratio between a consumed feed and a produced
species, then combines that ratio with molar masses and an overall fractional
yield to compute the required feed mass. Plant capacity, molar masses,
stoichiometric numbers, and empirical yield remain explicit inputs.

Source: `icho_2026_t7_a2:T7-A2`, IChO 2026 Theory Task, source page 63.
-/

namespace Chemlib.Process

/-- Product amount obtained per unit feed amount from signed stoichiometric numbers. -/
noncomputable def productPerFeedRatio {Species : Type}
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) : ℝ :=
  -(nu product : ℝ) / (nu feed : ℝ)

/-- The product-per-feed ratio unfolds to the signed stoichiometric quotient. -/
theorem productPerFeedRatio_eq {Species : Type}
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) :
    productPerFeedRatio nu feed product = -(nu product : ℝ) / (nu feed : ℝ) := by
  rfl

/-- A consumed feed and produced product give a positive product-per-feed ratio. -/
theorem productPerFeedRatio_pos {Species : Type}
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (hfeed : nu feed < 0) (hproduct : 0 < nu product) :
    0 < productPerFeedRatio nu feed product := by
  rw [productPerFeedRatio_eq]
  apply div_pos_of_neg_of_neg
  · exact neg_neg_of_pos (by exact_mod_cast hproduct)
  · exact_mod_cast hfeed

/-- Feed mass needed for a desired product mass at a specified overall fractional yield. -/
noncomputable def requiredFeedMass {Species : Type}
    (productMass feedMolarMass productMolarMass : ℝ)
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (yield : ℝ) : ℝ :=
  productMass * feedMolarMass /
    (productMolarMass * productPerFeedRatio nu feed product * yield)

/-- The required feed mass unfolds to the mass, molar-mass, ratio, and yield formula. -/
theorem requiredFeedMass_eq {Species : Type}
    (productMass feedMolarMass productMolarMass : ℝ)
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (yield : ℝ) :
    requiredFeedMass productMass feedMolarMass productMolarMass nu feed product yield =
      productMass * feedMolarMass /
        (productMolarMass * productPerFeedRatio nu feed product * yield) := by
  rfl

/-- Positive physical inputs and physical stoichiometric signs require positive feed mass. -/
theorem requiredFeedMass_pos {Species : Type}
    (productMass feedMolarMass productMolarMass : ℝ)
    (nu : Chemlib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (yield : ℝ)
    (hproductMass : 0 < productMass) (hfeedMolarMass : 0 < feedMolarMass)
    (hproductMolarMass : 0 < productMolarMass) (hfeed : nu feed < 0)
    (hproduct : 0 < nu product) (hyield : 0 < yield) :
    0 < requiredFeedMass productMass feedMolarMass productMolarMass nu feed product yield := by
  rw [requiredFeedMass_eq]
  exact div_pos (mul_pos hproductMass hfeedMolarMass)
    (mul_pos (mul_pos hproductMolarMass
      (productPerFeedRatio_pos nu feed product hfeed hproduct)) hyield)

/-- Clearing the nonzero denominator recovers desired product mass times feed molar mass. -/
theorem requiredFeedMass_spec {Species : Type}
    {productMass feedMolarMass productMolarMass yield : ℝ}
    {nu : Chemlib.Foundations.StoichiometricNumber Species}
    {feed product : Species} (hproductMolarMass : productMolarMass ≠ 0)
    (hratio : productPerFeedRatio nu feed product ≠ 0) (hyield : yield ≠ 0) :
    requiredFeedMass productMass feedMolarMass productMolarMass nu feed product yield *
        (productMolarMass * productPerFeedRatio nu feed product * yield) =
      productMass * feedMolarMass := by
  rw [requiredFeedMass_eq]
  exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hproductMolarMass hratio) hyield)

end Chemlib.Process
