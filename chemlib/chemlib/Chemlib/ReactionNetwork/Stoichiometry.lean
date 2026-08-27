import Chemlib.ReactionNetwork.Incidence

/-!
# Stoichiometry and conservation

The stoichiometric subspace is represented as the range of the matrix linear
map.  This agrees with Mathlib's span-of-columns characterization.
-/

namespace Chemlib.ReactionNetwork

/-- The real reaction vector `product - reactant`. -/
def reactionVector
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) : Species → ℝ :=
  fun s ↦ (N.product r s : ℝ) - (N.reactant r s : ℝ)

/-- The stoichiometric matrix, with one reaction vector in each column. -/
def stoichiometricMatrix
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Matrix Species ReactionId ℝ :=
  fun s r ↦ N.reactionVector r s

/-- Stoichiometry factors as complex composition followed by reaction
incidence. -/
theorem stoichiometricMatrix_eq_composition_mul_incidence
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricMatrix = N.compositionMatrix * N.incidenceMatrix := by
  symm
  ext s r
  simp only [Matrix.mul_apply, compositionMatrix, incidenceMatrix,
    stoichiometricMatrix, reactionVector, product, reactant]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

/-- The stoichiometric subspace is the range of the stoichiometric linear
map. -/
def stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Submodule ℝ (Species → ℝ) :=
  LinearMap.range N.stoichiometricMatrix.mulVecLin

/-- Coordinate expansion of stoichiometric matrix-vector multiplication. -/
theorem stoichiometricMatrix_mulVec_apply
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (v : ReactionId → ℝ) (s : Species) :
    Matrix.mulVec N.stoichiometricMatrix v s =
      Finset.univ.sum (fun r ↦ N.reactionVector r s * v r) := by
  rfl

/-- Every linear combination of reaction columns lies in the stoichiometric
subspace. -/
theorem mulVec_mem_stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (v : ReactionId → ℝ) :
    Matrix.mulVec N.stoichiometricMatrix v ∈ N.stoichiometricSubspace := by
  exact ⟨v, rfl⟩

/-- The range definition equals the span of the reaction columns. -/
theorem stoichiometricSubspace_eq_span
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricSubspace =
      Submodule.span ℝ (Set.range N.stoichiometricMatrix.col) := by
  exact Matrix.range_mulVecLin N.stoichiometricMatrix

/-- A linear conservation law annihilates every reaction vector. -/
def IsConservationLaw
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (w : Species → ℝ) : Prop :=
  ∀ r, Finset.univ.sum (fun s ↦ w s * N.reactionVector r s) = 0

/-- A conservation law annihilates every flux-induced vector field. -/
theorem conservation_annihilates_mulVec
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (w : Species → ℝ) (hw : N.IsConservationLaw w)
    (v : ReactionId → ℝ) :
    Finset.univ.sum
      (fun s ↦ w s * Matrix.mulVec N.stoichiometricMatrix v s) = 0 := by
  simp only [stoichiometricMatrix_mulVec_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro r _
  rw [hw r, zero_mul]

end Chemlib.ReactionNetwork
