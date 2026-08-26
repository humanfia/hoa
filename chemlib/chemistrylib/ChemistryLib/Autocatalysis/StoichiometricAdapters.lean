import ChemistryLib.ReactionNetwork.DeficiencyKernel
import ChemistryLib.ReactionNetwork.Incidence
import ChemistryLib.ReactionNetwork.IncidenceRank
import ChemistryLib.ReactionNetwork.IntegerHyperflow

/-!
# Stoichiometric adapters for integer hyperflows

These results connect integer hyperflows to the reaction-network incidence,
stoichiometric-subspace, rank, and restricted-kernel APIs.

Source references:
* ANDERSEN-ETAL-2021, equation (2) and Lemmas 3--4.
* `corpus.research_contracts`, authenticated autocatalysis rank/kernel reuse.
-/

namespace ChemistryLib.Autocatalysis

namespace IntegerHyperflow

/-- The real reaction change factors through incidence and complex composition. -/
theorem real_change_eq_composition_mul_incidence
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    Matrix.mulVec (ChemistryLib.ReactionNetwork.stoichiometricMatrix N)
        (fun r ↦ (f.reaction r : ℝ)) =
      Matrix.mulVec (ChemistryLib.ReactionNetwork.compositionMatrix N)
        (Matrix.mulVec (ChemistryLib.ReactionNetwork.incidenceMatrix N)
          (fun r ↦ (f.reaction r : ℝ))) := by
  rw [N.stoichiometricMatrix_eq_composition_mul_incidence,
    Matrix.mulVec_mulVec]

/-- The real reaction change of an integer hyperflow is stoichiometric. -/
theorem real_change_mem_stoichiometricSubspace
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (f : IntegerHyperflow N) :
    Matrix.mulVec (ChemistryLib.ReactionNetwork.stoichiometricMatrix N)
        (fun r ↦ (f.reaction r : ℝ)) ∈
      ChemistryLib.ReactionNetwork.stoichiometricSubspace N := by
  exact N.mulVec_mem_stoichiometricSubspace
    (fun r ↦ (f.reaction r : ℝ))

end IntegerHyperflow

/-- Stoichiometric rank is bounded by incidence rank. -/
theorem hyperflow_rank_bound
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    ChemistryLib.ReactionNetwork.stoichiometricRank N ≤
      ChemistryLib.ReactionNetwork.incidenceRank N := by
  exact N.stoichiometricRank_le_incidenceRank

/-- Deficiency is the dimension of the restricted complex-composition kernel. -/
theorem restrictedKernel_finrank
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    ChemistryLib.ReactionNetwork.deficiency N =
      Module.finrank ℝ
        (LinearMap.ker
          (ChemistryLib.ReactionNetwork.complexCompositionOnIncidenceImage N)) := by
  exact N.deficiency_eq_finrank_ker_complexCompositionOnIncidenceImage

end ChemistryLib.Autocatalysis
