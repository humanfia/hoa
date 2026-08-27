import Chemlib.ReactionNetwork.DeficiencyKernel
import Chemlib.ReactionNetwork.Incidence
import Chemlib.ReactionNetwork.IncidenceRank
import Chemlib.ReactionNetwork.IntegerHyperflow

/-!
# Stoichiometric adapters for integer hyperflows

These results connect integer hyperflows to the reaction-network incidence,
stoichiometric-subspace, rank, and restricted-kernel APIs.

Source references:
* ANDERSEN-ETAL-2021, equation (2) and Lemmas 3--4.
* `corpus.research_contracts`, authenticated autocatalysis rank/kernel reuse.
-/

namespace Chemlib.Autocatalysis

namespace IntegerHyperflow

/-- The real reaction change factors through incidence and complex composition. -/
theorem real_change_eq_composition_mul_incidence
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    Matrix.mulVec (Chemlib.ReactionNetwork.stoichiometricMatrix N)
        (fun r ↦ (f.reaction r : ℝ)) =
      Matrix.mulVec (Chemlib.ReactionNetwork.compositionMatrix N)
        (Matrix.mulVec (Chemlib.ReactionNetwork.incidenceMatrix N)
          (fun r ↦ (f.reaction r : ℝ))) := by
  rw [N.stoichiometricMatrix_eq_composition_mul_incidence,
    Matrix.mulVec_mulVec]

/-- The real reaction change of an integer hyperflow is stoichiometric. -/
theorem real_change_mem_stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    Matrix.mulVec (Chemlib.ReactionNetwork.stoichiometricMatrix N)
        (fun r ↦ (f.reaction r : ℝ)) ∈
      Chemlib.ReactionNetwork.stoichiometricSubspace N := by
  exact N.mulVec_mem_stoichiometricSubspace
    (fun r ↦ (f.reaction r : ℝ))

end IntegerHyperflow

/-- Stoichiometric rank is bounded by incidence rank. -/
theorem hyperflow_rank_bound
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Chemlib.ReactionNetwork.stoichiometricRank N ≤
      Chemlib.ReactionNetwork.incidenceRank N := by
  exact N.stoichiometricRank_le_incidenceRank

/-- Deficiency is the dimension of the restricted complex-composition kernel. -/
theorem restrictedKernel_finrank
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Chemlib.ReactionNetwork.deficiency N =
      Module.finrank ℝ
        (LinearMap.ker
          (Chemlib.ReactionNetwork.complexCompositionOnIncidenceImage N)) := by
  exact N.deficiency_eq_finrank_ker_complexCompositionOnIncidenceImage

end Chemlib.Autocatalysis
