import ChemistryLib.ReactionNetwork.Balance
import ChemistryLib.ReactionNetwork.DeficiencyZeroBridge
import ChemistryLib.ReactionNetwork.MassAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The deficiency-zero complex-balance theorem

This module packages the deficiency-zero theorem for finite mass-action
reaction networks: weak reversibility and zero deficiency imply existence of a
positive complex-balanced state for every positive rate assignment.  The
argument follows YU-CRACIUN-2018, Section 2.2, Theorem 2.8 (source corpus
SHA-256
`087c3303f891486c8056bd60bd540dc85bf1b862999249906199e8b57a6dc671`,
<https://arxiv.org/pdf/1805.10371v1>).  It asserts existence of complex
balance only and makes no global-attraction claim.
-/

namespace ChemistryLib.ReactionNetwork

noncomputable section

/-! ## Project-local Mathlib supplement — Deficiency-zero complex balance -/

/-- A weakly reversible finite reaction network of deficiency zero is
complex-balanced for every positive assignment of reaction-rate constants. -/
theorem deficiencyZero_complexBalanced
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (hwr : N.WeaklyReversible) (hdef : N.deficiency = 0)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    ∃ x : Species → ℝ, N.IsComplexBalanced k x := by
  obtain ⟨b, hb, hbpos⟩ :=
    N.weaklyReversible_exists_positive_weightedLaplacianKernel hwr k hk
  obtain ⟨u, q, hdecomp, hq⟩ :=
    N.deficiencyZero_logDecomposition hdef (fun c ↦ Real.log (b c))
  have hrescaled :
      (fun c ↦ b c * Real.exp (-q c)) ∈ N.weightedLaplacianKernel k :=
    N.weightedLaplacianKernel_rescale_exp_neg k b q hb hq
  have hmonomial :
      (fun c ↦ Real.exp
        (Matrix.mulVec N.compositionMatrix.transpose u c)) =
        fun c ↦ b c * Real.exp (-q c) := by
    funext c
    have hc := congr_fun hdecomp c
    have hu : Matrix.mulVec N.compositionMatrix.transpose u c =
        Real.log (b c) - q c := by
      exact eq_sub_of_add_eq hc.symm
    rw [hu, sub_eq_add_neg, Real.exp_add, Real.exp_log (hbpos c)]
  refine ⟨fun s ↦ Real.exp (u s), ?_⟩
  apply (N.complexBalanced_iff_weightedLaplacian k _).2
  refine ⟨hk, fun s ↦ Real.exp_pos (u s), ?_⟩
  rw [N.complexMonomialVector_exp u, hmonomial]
  exact hrescaled

end

end ChemistryLib.ReactionNetwork
