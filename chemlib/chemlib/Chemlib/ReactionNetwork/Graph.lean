import Chemlib.ReactionNetwork.Basic
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Reaction graphs

Reaction identifiers are retained as the inhabitants of the corresponding
quiver hom-types.  This preserves parallel reactions while allowing Mathlib's
path and connected-component infrastructure to be used directly.
-/

namespace Chemlib.ReactionNetwork

/-- The reaction-indexed quiver of a network. -/
@[reducible] def reactionQuiver
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    Quiver ComplexId where
  Hom a b := {r : ReactionId // N.source r = a ∧ N.target r = b}

/-- Two complexes lie in the same (weakly connected) linkage class. -/
def SameLinkageClass
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (a b : ComplexId) : Prop :=
  letI := N.reactionQuiver
  Quiver.WeaklyConnectedComponent.mk a =
    Quiver.WeaklyConnectedComponent.mk b

/-- Two complexes lie in the same strongly connected linkage class. -/
def SameStrongLinkageClass
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (a b : ComplexId) : Prop :=
  letI := N.reactionQuiver
  Quiver.StronglyConnectedComponent.mk a =
    Quiver.StronglyConnectedComponent.mk b

/-- Every reaction has a reaction with the opposite endpoints. -/
def Reversible
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) : Prop :=
  ∀ r, ∃ r', N.source r' = N.target r ∧ N.target r' = N.source r

/-- Every reaction edge admits a directed path back to its source. -/
def WeaklyReversible
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) : Prop :=
  letI := N.reactionQuiver
  ∀ r, Nonempty (Quiver.Path (N.target r) (N.source r))

private theorem reaction_path
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (r : ReactionId) :
    letI := N.reactionQuiver
    Nonempty (Quiver.Path (N.source r) (N.target r)) := by
  letI := N.reactionQuiver
  exact ⟨Quiver.Hom.toPath
    (⟨r, rfl, rfl⟩ : Quiver.Hom (N.source r) (N.target r))⟩

/-- Weak reversibility is exactly strong-component equality at every reaction
edge. -/
theorem weaklyReversible_iff_sameStrongLinkageClass
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId) :
    N.WeaklyReversible ↔
      ∀ r, N.SameStrongLinkageClass (N.source r) (N.target r) := by
  letI := N.reactionQuiver
  constructor
  · intro h r
    exact Quiver.stronglyConnectedComponent_eq_of_path
      (reaction_path N r) (h r)
  · intro h r
    exact (Quiver.exists_path_of_stronglyConnectedComponent_eq (h r)).2

/-- A reversible reaction network is weakly reversible. -/
theorem reversible_weaklyReversible
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (h : N.Reversible) : N.WeaklyReversible := by
  letI := N.reactionQuiver
  intro r
  obtain ⟨r', hs, ht⟩ := h r
  exact ⟨Quiver.Hom.toPath
    (⟨r', hs, ht⟩ : Quiver.Hom (N.target r) (N.source r))⟩

end Chemlib.ReactionNetwork
