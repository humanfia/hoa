import Chemlib.ReactionNetwork.TerminalKernelBasis
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimensions of the weighted-Laplacian kernel and image

The terminal-component basis identifies the dimension of the weighted
complex-graph Laplacian's kernel.  Finite-dimensional rank-nullity then gives
the complementary image dimension.  This is the dimension statement from
GUNAWARDENA-2003, Section 4, Theorem 4.2 (sanitized contract
`research:gunawardena_2003:laplacian_kernel`).  Positive reaction-rate labels
remain explicit hypotheses.
-/

namespace Chemlib.ReactionNetwork

/-! ## Project-local Mathlib supplement — Weighted-Laplacian dimensions -/

/-- The image of the weighted Laplacian acting on complex-indexed vectors. -/
def weightedLaplacianImage
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) : Submodule ℝ (ComplexId → ℝ) :=
  LinearMap.range (N.weightedLaplacian k).mulVecLin

/-- The weighted-Laplacian kernel has one basis vector per terminal strong
component. -/
theorem finrank_weightedLaplacianKernel
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Module.finrank ℝ (weightedLaplacianKernel N k) =
      Fintype.card (TerminalStrongComponent N) := by
  exact Module.finrank_eq_card_basis (terminalKernelBasis N k hk)

/-- Rank-nullity expresses the weighted-Laplacian image dimension as the
number of complexes minus the number of terminal strong components. -/
theorem finrank_weightedLaplacianImage
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (hk : ∀ r, 0 < k r) :
    Module.finrank ℝ (weightedLaplacianImage N k) =
      Fintype.card ComplexId - Fintype.card (TerminalStrongComponent N) := by
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker (N.weightedLaplacian k).mulVecLin
  rw [show Module.finrank ℝ (ComplexId → ℝ) = Fintype.card ComplexId by
      exact Module.finrank_fintype_fun_eq_card ℝ] at hrankNullity
  rw [← finrank_weightedLaplacianKernel N k hk]
  unfold weightedLaplacianImage weightedLaplacianKernel
  omega

end Chemlib.ReactionNetwork
