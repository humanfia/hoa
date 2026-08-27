import Chemlib.ReactionNetwork.Stoichiometry
import Chemlib.ReactionNetwork.UnconditionalDeficiency

/-!
# Deficiency as a restricted-composition kernel

The complex-composition map is restricted to the image of the reaction
incidence map.  Its image is the stoichiometric subspace, and rank--nullity
identifies its kernel dimension with the network deficiency.

Source references:
* `corpus.research_contracts:reaction_network.incidence_rank` and
  `corpus.scope:reaction_network.incidence_rank`.
* YU-CRACIUN-2018, Section 1, equation (5), and Section 2.2, Definition 2.7.
-/

namespace Chemlib.ReactionNetwork

noncomputable section

/-- Complex composition restricted to the image of the incidence map. -/
def complexCompositionOnIncidenceImage
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    (LinearMap.range N.incidenceMatrix.mulVecLin) →ₗ[ℝ] (Species → ℝ) :=
  N.compositionMatrix.mulVecLin.domRestrict
    (LinearMap.range N.incidenceMatrix.mulVecLin)

/-- The restricted map evaluates by ordinary complex-composition matrix
multiplication. -/
theorem complexCompositionOnIncidenceImage_apply
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (z : LinearMap.range N.incidenceMatrix.mulVecLin) :
    complexCompositionOnIncidenceImage N z =
      Matrix.mulVec N.compositionMatrix z.1 :=
  rfl

/-- The range of restricted complex composition is the stoichiometric
subspace. -/
theorem range_complexCompositionOnIncidenceImage
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    LinearMap.range (complexCompositionOnIncidenceImage N) =
      N.stoichiometricSubspace := by
  unfold complexCompositionOnIncidenceImage stoichiometricSubspace
  rw [LinearMap.range_domRestrict, ← LinearMap.range_comp,
    ← Matrix.mulVecLin_mul,
    ← N.stoichiometricMatrix_eq_composition_mul_incidence]

/-- Deficiency is the dimension of the kernel of complex composition on the
incidence image. -/
theorem deficiency_eq_finrank_ker_complexCompositionOnIncidenceImage
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.deficiency =
      Module.finrank ℝ (LinearMap.ker (complexCompositionOnIncidenceImage N)) := by
  rw [N.deficiency_eq_incidenceRank_sub_stoichiometricRank_of_incidenceRankCertificate
    N.incidenceRankCertificate]
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (complexCompositionOnIncidenceImage N)
  rw [range_complexCompositionOnIncidenceImage N] at hrank
  unfold incidenceRank stoichiometricRank stoichiometricSubspace at *
  omega

end

end Chemlib.ReactionNetwork
