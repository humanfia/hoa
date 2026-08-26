import ChemistryLib.ReactionNetwork.Deficiency
import ChemistryLib.ReactionNetwork.DeficiencyZeroComplexBalance
import ChemistryLib.ReactionNetwork.Graph
import ChemistryLib.Stochastic.ComplexBalanceProductForm

/-!
# Deficiency-zero product forms on finite count classes

This module records the finite-class deficiency-zero product-form corollary
from Anderson--Craciun--Kurtz (2010), Section 2, Definitions 2.1--2.4, and
Section 4, Theorem 4.2.  Weak reversibility and zero deficiency provide a
positive complex-balanced state; on an explicitly finite closed irreducible
count class, its normalized Poisson product form is stationary.

No infinite-class normalization, count-state process construction,
nonexplosion, uniqueness, convergence, or fluctuation theorem is asserted.
-/

namespace ChemistryLib.Stochastic

noncomputable section

/-- A weakly reversible deficiency-zero network with positive rate constants
has a normalized Poisson product-form stationary distribution on every finite
closed irreducible count class.  This is the finite-class specialization of
ACK-2010, Theorem 4.2. -/
theorem deficiencyZero_finiteClosedIrreducibleClass_productForm_stationary
    {Species Complex Reaction : Type}
    [Fintype Species] [Fintype Complex] [Fintype Reaction]
    [DecidableEq Species] [DecidableEq Complex]
    (N : ChemistryLib.ReactionNetwork Species Complex Reaction)
    (κ : Reaction → ℝ) (Ω : Finset (CountState Species))
    (hwr : N.WeaklyReversible) (hdef : N.deficiency = 0)
    (hκ : ∀ r, 0 < κ r)
    (hclosed : IsClosedCountClass N Ω)
    (hirreducible : IsIrreducibleCountClass N Ω) :
    ∃ c : Species → ℝ, N.IsComplexBalanced κ c ∧
      0 < classNormalization c Ω ∧
      IsStationaryDistribution (restrictedRateKernel N κ Ω)
        (classProductForm c Ω) := by
  obtain ⟨c, hcb⟩ :=
    ChemistryLib.ReactionNetwork.deficiencyZero_complexBalanced
      N hwr hdef κ hκ
  have hΩ : Ω.Nonempty :=
    irreducibleCountClass_nonempty N Ω hirreducible
  have hZ : 0 < classNormalization c Ω :=
    classNormalization_pos c Ω hcb.2.1 hΩ
  refine ⟨c, hcb, hZ, ?_⟩
  exact complexBalanced_finiteClosedIrreducibleClass_productForm_stationary
    N κ c Ω hcb hclosed hirreducible

end

end ChemistryLib.Stochastic
