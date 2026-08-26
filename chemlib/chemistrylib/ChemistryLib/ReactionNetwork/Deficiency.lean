import ChemistryLib.ReactionNetwork.DeficiencyRank
import ChemistryLib.ReactionNetwork.LinkageClass

/-!
# Deficiency of a reaction network

The deficiency is the number of complexes minus the number of linkage classes
and the stoichiometric rank.  An `IncidenceRankCertificate` records the
conditional incidence-rank identity needed to express deficiency in terms of
the incidence rank and to reconstruct the complex count.

Source references:
* YU-CRACIUN-2018, Section 2.2, Definition 2.7.
* ACK-2010, Section 2, Definition 2.4.
-/

namespace ChemistryLib.ReactionNetwork

noncomputable section

/-- A certificate that incidence rank plus linkage-class count is the complex count. -/
def IncidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : Prop :=
  N.incidenceRank + N.linkageClassCount = Fintype.card ComplexId

/-- The deficiency of a reaction network. -/
def deficiency
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : ℕ :=
  Fintype.card ComplexId - N.linkageClassCount - N.stoichiometricRank

/-- A certified network's deficiency, linkage classes, and stoichiometric rank
reconstruct its number of complexes. -/
theorem
deficiency_add_linkageClassCount_add_stoichiometricRank_eq_complexCount_of_incidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (h : N.IncidenceRankCertificate) :
    N.deficiency + N.linkageClassCount + N.stoichiometricRank =
      Fintype.card ComplexId := by
  have hrank : N.stoichiometricRank ≤ N.incidenceRank :=
    N.stoichiometricRank_le_incidenceRank
  unfold deficiency IncidenceRankCertificate at *
  omega

/-- Deficiency is complex count minus linkage-class count and stoichiometric rank. -/
theorem deficiency_eq_complexCount_sub
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    N.deficiency =
      Fintype.card ComplexId - N.linkageClassCount - N.stoichiometricRank :=
  rfl

/-- Under an incidence-rank certificate, deficiency is incidence rank minus
stoichiometric rank. -/
theorem deficiency_eq_incidenceRank_sub_stoichiometricRank_of_incidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (h : N.IncidenceRankCertificate) :
    N.deficiency = N.incidenceRank - N.stoichiometricRank := by
  unfold deficiency IncidenceRankCertificate at *
  omega

/-- The incidence-rank certificate is exactly its defining rank identity. -/
theorem incidenceRankCertificate_iff
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    N.IncidenceRankCertificate ↔
      N.incidenceRank + N.linkageClassCount = Fintype.card ComplexId :=
  Iff.rfl

/-- A certificate determines incidence rank as complex count minus
linkage-class count. -/
theorem incidenceRank_eq_complexCount_sub_linkageClassCount_of_incidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (h : N.IncidenceRankCertificate) :
    N.incidenceRank = Fintype.card ComplexId - N.linkageClassCount := by
  unfold IncidenceRankCertificate at h
  omega

/-- Under an incidence-rank certificate, linkage-class count plus
stoichiometric rank does not exceed complex count. -/
theorem linkageClassCount_add_stoichiometricRank_le_of_incidenceRankCertificate
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (h : N.IncidenceRankCertificate) :
    N.linkageClassCount + N.stoichiometricRank ≤ Fintype.card ComplexId := by
  have hrank : N.stoichiometricRank ≤ N.incidenceRank :=
    N.stoichiometricRank_le_incidenceRank
  unfold IncidenceRankCertificate at h
  omega

end

end ChemistryLib.ReactionNetwork
