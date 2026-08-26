import Mathlib.Data.NNReal.Defs
import ChemistryLib.ReactionNetwork.MassAction

/-!
# Approximate steady states

This module formalizes a species-scaled steady-state approximation for the
mass-action vector field.  The tolerance and scale are nonnegative by their
`NNReal` types.

Sources: `icho_2026_t2_a2:T2-A2` and
`research:iupac_goldbook_2025:steady_state_approximation:term S05962`.
-/

namespace ChemistryLib

namespace ReactionNetwork

/-- The selected derivatives are bounded by a nonnegative relative tolerance
times their species-specific nonnegative scales. -/
def IsApproxSteadyState
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (selected : Set Species) (epsilon : NNReal) (scale : Species → NNReal)
    (k : ReactionId → ℝ) (x : Species → ℝ) : Prop :=
  ∀ s, s ∈ selected →
    |N.massActionVectorField k x s| ≤ (epsilon : ℝ) * (scale s : ℝ)

/-- The approximate steady-state predicate is its coordinatewise derivative
bound. -/
theorem isApproxSteadyState_iff
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {selected : Set Species} {epsilon : NNReal} {scale : Species → NNReal}
    {k : ReactionId → ℝ} {x : Species → ℝ} :
    N.IsApproxSteadyState selected epsilon scale k x ↔
      ∀ s, s ∈ selected →
        |N.massActionVectorField k x s| ≤ (epsilon : ℝ) * (scale s : ℝ) := by
  rfl

/-- With every species selected and zero tolerance, approximate and exact
steady state agree. -/
theorem isApproxSteadyState_univ_zero_iff
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {scale : Species → NNReal} {k : ReactionId → ℝ} {x : Species → ℝ} :
    N.IsApproxSteadyState Set.univ 0 scale k x ↔ N.IsSteadyState k x := by
  constructor
  · intro h
    change ∀ s, s ∈ Set.univ →
      |N.massActionVectorField k x s| ≤ ((0 : NNReal) : ℝ) * (scale s : ℝ) at h
    change N.massActionVectorField k x = 0
    funext s
    have hs : |N.massActionVectorField k x s| ≤ 0 := by
      simpa using h s (Set.mem_univ s)
    exact abs_eq_zero.mp (le_antisymm hs (abs_nonneg _))
  · intro h
    change N.massActionVectorField k x = 0 at h
    change ∀ s, s ∈ Set.univ →
      |N.massActionVectorField k x s| ≤ ((0 : NNReal) : ℝ) * (scale s : ℝ)
    intro s _
    have hs : N.massActionVectorField k x s = 0 := by
      simpa using congrFun h s
    simp [hs]

/-- At zero tolerance, the selected derivatives vanish exactly. -/
theorem isApproxSteadyState_zero_iff
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {selected : Set Species} {scale : Species → NNReal}
    {k : ReactionId → ℝ} {x : Species → ℝ} :
    N.IsApproxSteadyState selected 0 scale k x ↔
      ∀ s, s ∈ selected → N.massActionVectorField k x s = 0 := by
  constructor
  · intro h
    change ∀ s, s ∈ selected →
      |N.massActionVectorField k x s| ≤ ((0 : NNReal) : ℝ) * (scale s : ℝ) at h
    intro s hs
    have hle : |N.massActionVectorField k x s| ≤ 0 := by
      simpa using h s hs
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro h
    change ∀ s, s ∈ selected →
      |N.massActionVectorField k x s| ≤ ((0 : NNReal) : ℝ) * (scale s : ℝ)
    intro s hs
    simp [h s hs]

/-- Every exact steady state is approximate for any selected species,
nonnegative tolerance, and nonnegative scale. -/
theorem isSteadyState_implies_approx
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    {N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId}
    {selected : Set Species} {epsilon : NNReal} {scale : Species → NNReal}
    {k : ReactionId → ℝ} {x : Species → ℝ} :
    N.IsSteadyState k x → N.IsApproxSteadyState selected epsilon scale k x := by
  intro h
  change N.massActionVectorField k x = 0 at h
  change ∀ s, s ∈ selected →
    |N.massActionVectorField k x s| ≤ (epsilon : ℝ) * (scale s : ℝ)
  intro s _
  have hs : N.massActionVectorField k x s = 0 := by
    simpa using congrFun h s
  rw [hs, abs_zero]
  positivity

end ReactionNetwork

end ChemistryLib
