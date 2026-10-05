import Chemlib.Dynamics.OscillationCertificate
import Chemlib.ReactionNetwork.IntegerHyperflow

/-!
# Sealed reaction-network frontiers

A sealed frontier records the two exact physical-isolation obligations from
`corpus.manifest:autocatalysis.oscillation` (the physically isolated sealed
frontier): retained reactions have no reactant or product outside the retained
species, and omitted reactions have zero stoichiometric effect on every
retained species.

Following the transfer contract in
`corpus.scope:autocatalysis.oscillation`, restriction reuses an already exact
periodic trajectory, its positive period, its ODE identity, and an explicit
nonconstancy witness on the retained coordinates.  No simulation, recurrence,
stationarity, or path-probability evidence is promoted to deterministic
oscillation.
-/

namespace Chemlib.Autocatalysis

/-- Exact physical-isolation data for retained species and reactions. -/
structure SealedFrontier
    {Species ComplexId ReactionId : Type} [Fintype Species]
    [Fintype ReactionId]
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (retainedSpecies : Finset Species)
    (retainedReactions : Finset ReactionId) : Type where
  private omittedReactionInert :
    ∀ {r : ReactionId}, r ∉ retainedReactions → ∀ {s : Species},
      s ∈ retainedSpecies →
        Chemlib.ReactionNetwork.reactionVector N r s = 0
  private retainedReactionClosed :
    ∀ {r : ReactionId}, r ∈ retainedReactions → ∀ {s : Species},
      s ∉ retainedSpecies →
        Chemlib.ReactionNetwork.reactant N r s = 0 ∧
          Chemlib.ReactionNetwork.product N r s = 0

namespace SealedFrontier

/-- An omitted reaction has no stoichiometric effect on a retained species. -/
theorem omitted_reaction_inert
    {Species ComplexId ReactionId : Type} [Fintype Species]
    [Fintype ReactionId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    {retainedSpecies : Finset Species}
    {retainedReactions : Finset ReactionId}
    (h : SealedFrontier N retainedSpecies retainedReactions)
    {r : ReactionId} (hr : r ∉ retainedReactions) :
    ∀ {s : Species}, s ∈ retainedSpecies →
      Chemlib.ReactionNetwork.reactionVector N r s = 0 := by
  exact h.omittedReactionInert hr

/-- Restrict an exact periodic orbit to a sealed collection of coordinates. -/
def periodicOrbit_restrict
    {Species ComplexId ReactionId : Type} [Fintype Species]
    [Fintype ReactionId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    {retainedSpecies : Finset Species}
    {retainedReactions : Finset ReactionId}
    (hsealed : SealedFrontier N retainedSpecies retainedReactions)
    {F : (Species → ℝ) → Species → ℝ}
    {G : (retainedSpecies → ℝ) → retainedSpecies → ℝ}
    (c : Chemlib.Dynamics.PeriodicOrbitCertificate F)
    (hG : ∀ (t : ℝ) (s : retainedSpecies),
      G (fun q : retainedSpecies ↦ c.trajectory t q) s =
        F (c.trajectory t) s)
    (hnonconstant : ∃ t : ℝ,
      (fun s : retainedSpecies ↦ c.trajectory t s) ≠
        fun s : retainedSpecies ↦ c.trajectory 0 s) :
    Chemlib.Dynamics.PeriodicOrbitCertificate G := by
  let _ := hsealed
  exact {
    trajectory := fun t s ↦ c.trajectory t s
    period := c.period
    satisfies_ode := by
      intro t
      apply hasDerivAt_pi.mpr
      intro s
      rw [hG t s]
      exact hasDerivAt_pi.mp (c.satisfies_ode t) s
    period_positive := c.period_positive
    trajectory_nonconstant := by
      obtain ⟨t, ht⟩ := hnonconstant
      exact ⟨t, 0, ht⟩
    periodicity := by
      intro t
      funext s
      exact congrFun (c.periodicity t) s
  }

/-- A retained reaction has neither reactant nor product outside the frontier. -/
theorem retained_reaction_closed
    {Species ComplexId ReactionId : Type} [Fintype Species]
    [Fintype ReactionId]
    {N : Chemlib.ReactionNetwork Species ComplexId ReactionId}
    {retainedSpecies : Finset Species}
    {retainedReactions : Finset ReactionId}
    (h : SealedFrontier N retainedSpecies retainedReactions)
    {r : ReactionId} (hr : r ∈ retainedReactions) :
    ∀ {s : Species}, s ∉ retainedSpecies →
      Chemlib.ReactionNetwork.reactant N r s = 0 ∧
        Chemlib.ReactionNetwork.product N r s = 0 := by
  exact h.retainedReactionClosed hr

end SealedFrontier

end Chemlib.Autocatalysis
