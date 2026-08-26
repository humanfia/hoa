import ChemistryLib.ReactionNetwork.Graph
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Linkage classes of a reaction network

Linkage classes are the weakly connected components of the reaction quiver.

Source references:
* YU-CRACIUN-2018, Section 1, weak-reversibility and connected-component paragraph.
* ACK-2010, Section 2, linkage-class paragraph between Definitions 2.2 and 2.3.
-/

namespace ChemistryLib.ReactionNetwork

/-- The weakly connected components of a network's reaction quiver. -/
abbrev LinkageClass
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : Type :=
  letI := N.reactionQuiver
  Quiver.WeaklyConnectedComponent ComplexId

/-- The number of linkage classes of a finite-complex reaction network. -/
noncomputable def linkageClassCount
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : ℕ :=
  Nat.card (LinkageClass N)

/-- The linkage-class count is the cardinality of the weak-component type. -/
theorem linkageClassCount_eq_natCard
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    linkageClassCount N = Nat.card (LinkageClass N) := by
  rfl

/-- The number of linkage classes cannot exceed the number of complexes. -/
theorem linkageClassCount_le_complexCount
    {Species ComplexId ReactionId : Type} [Fintype ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    linkageClassCount N ≤ Fintype.card ComplexId := by
  rw [linkageClassCount_eq_natCard, ← Nat.card_eq_fintype_card]
  letI := N.reactionQuiver
  apply Nat.card_le_card_of_surjective Quiver.WeaklyConnectedComponent.mk
  intro c
  refine Quotient.inductionOn c ?_
  intro a
  exact ⟨a, rfl⟩

/-- The canonical linkage class containing a complex. -/
def linkageClassOf
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    ComplexId → LinkageClass N := by
  letI := N.reactionQuiver
  exact Quiver.WeaklyConnectedComponent.mk

/-- Two complexes represent the same linkage class exactly when they are weakly connected. -/
theorem sameLinkageClass_iff_linkageClass_eq
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (a b : ComplexId) :
    SameLinkageClass N a b ↔ linkageClassOf N a = linkageClassOf N b := by
  rfl

end ChemistryLib.ReactionNetwork
