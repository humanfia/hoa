import Chemlib.ReactionNetwork.Deficiency
import Chemlib.ReactionNetwork.IncidenceRank

/-!
# Unconditional deficiency identities

Every finite reaction network satisfies the incidence-rank certificate.  It
follows that stoichiometric rank is bounded by the number of complexes minus
the number of linkage classes, and that deficiency, linkage-class count, and
stoichiometric rank reconstruct the number of complexes.

Source references:
* `corpus.research_contracts:reaction_network.incidence_rank` and
  `corpus.scope:reaction_network.incidence_rank`.
* ACK-2010, Section 2, Definitions 2.1--2.4.
* YU-CRACIUN-2018, Section 2.2, Definition 2.7.
-/

namespace Chemlib.ReactionNetwork

/-- Deficiency, linkage-class count, and stoichiometric rank reconstruct the
number of complexes for every finite reaction network. -/
theorem deficiency_add_linkageClassCount_add_stoichiometricRank_eq_complexCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.deficiency + N.linkageClassCount + N.stoichiometricRank =
      Fintype.card ComplexId := by
  have hlink : N.linkageClassCount ≤ Fintype.card ComplexId :=
    N.linkageClassCount_le_complexCount
  have hstoich : N.stoichiometricRank ≤ N.incidenceRank :=
    N.stoichiometricRank_le_incidenceRank
  have hincidence :
      N.incidenceRank = Fintype.card ComplexId - N.linkageClassCount :=
    N.incidenceRank_eq_complexCount_sub_linkageClassCount
  unfold deficiency
  omega

/-- Every finite reaction network satisfies the incidence-rank certificate. -/
theorem incidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.IncidenceRankCertificate := by
  unfold IncidenceRankCertificate
  rw [N.incidenceRank_eq_complexCount_sub_linkageClassCount]
  exact Nat.sub_add_cancel N.linkageClassCount_le_complexCount

/-- Stoichiometric rank is at most the number of complexes minus the number of
linkage classes. -/
theorem stoichiometricRank_le_complexCount_sub_linkageClassCount
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.stoichiometricRank ≤
      Fintype.card ComplexId - N.linkageClassCount := by
  rw [← N.incidenceRank_eq_complexCount_sub_linkageClassCount]
  exact N.stoichiometricRank_le_incidenceRank

end Chemlib.ReactionNetwork
