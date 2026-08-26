import ChemistryLib.ReactionNetwork.Basic
import ChemistryLib.ReactionNetwork.Graph
import ChemistryLib.ReactionNetwork.Incidence
import ChemistryLib.ReactionNetwork.MassAction
import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Weighted complex-graph Laplacian

This module records the reaction-network-native weighted Laplacian and its
factorization through the directed incidence matrix and source-rate matrix.
The development follows GUNAWARDENA-2003, Sections 3--4, equations (10) and
(16), and Theorem 4.2.  Rate assignments remain explicit parameters of the
definitions, so no empirical kinetic data is built into the library.
-/

namespace ChemistryLib.ReactionNetwork

/-- The vector of complex monomials evaluated at a concentration state. -/
def complexMonomialVector
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (x : Species → ℝ) : ComplexId → ℝ :=
  fun c ↦ Complex.monomial (N.complex c) x

/-- The source-rate matrix, retaining one column entry for every reaction. -/
def sourceRateMatrix
    {Species ComplexId ReactionId : Type} [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) : Matrix ReactionId ComplexId ℝ :=
  fun r c ↦ if c = N.source r then k r else 0

/-- The weighted Laplacian in the existing complex-row, complex-column
convention. -/
def weightedLaplacian
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) : Matrix ComplexId ComplexId ℝ :=
  N.incidenceMatrix * N.sourceRateMatrix k

/-- Source-rate multiplication recovers the mass-action flux vector. -/
theorem sourceRateMatrix_mulVec_complexMonomial
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) :
    Matrix.mulVec (N.sourceRateMatrix k) (N.complexMonomialVector x) =
      N.massActionFlux k x := by
  funext r
  simp [Matrix.mulVec, dotProduct, sourceRateMatrix, complexMonomialVector,
    massActionFlux, reactant]

/-- Every weighted-Laplacian column has total weight zero. -/
theorem weightedLaplacian_column_sum
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (d : ComplexId) :
    Finset.univ.sum (fun c ↦ N.weightedLaplacian k c d) = 0 := by
  simp only [weightedLaplacian, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [incidence_column_sum]

/-- The weighted Laplacian factors as incidence times source rate. -/
theorem weightedLaplacian_eq_incidence_mul_sourceRate
    {Species ComplexId ReactionId : Type}
    [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) :
    N.weightedLaplacian k = N.incidenceMatrix * N.sourceRateMatrix k := by
  rfl

/-- Laplacian multiplication sends complex monomials to the incidence image
of the mass-action flux vector. -/
theorem weightedLaplacian_mulVec_complexMonomial
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) :
    Matrix.mulVec (N.weightedLaplacian k) (N.complexMonomialVector x) =
      Matrix.mulVec N.incidenceMatrix (N.massActionFlux k x) := by
  rw [weightedLaplacian_eq_incidence_mul_sourceRate, ← Matrix.mulVec_mulVec,
    sourceRateMatrix_mulVec_complexMonomial]

/-- The mass-action vector field factors through the weighted Laplacian. -/
theorem massActionVectorField_eq_composition_mulVec_weightedLaplacian
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ) :
    N.massActionVectorField k x =
      Matrix.mulVec N.compositionMatrix
        (Matrix.mulVec (N.weightedLaplacian k)
          (N.complexMonomialVector x)) := by
  rw [massActionVectorField, stoichiometricMatrix_eq_composition_mul_incidence,
    weightedLaplacian_mulVec_complexMonomial, ← Matrix.mulVec_mulVec]

end ChemistryLib.ReactionNetwork
