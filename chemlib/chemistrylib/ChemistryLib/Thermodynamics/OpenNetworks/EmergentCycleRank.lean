import ChemistryLib.Thermodynamics.OpenNetworks.Conservation

/-!
# Emergent-cycle rank accounting in open reaction networks

Removing the chemostatted rows from a stoichiometric matrix can expose reaction
cycles that were not cycles of the closed network.  Rank-nullity then accounts
for the chemostats as the sum of independent broken conservation laws and these
emergent cycles.

This follows Rao and Esposito (2016), Sections II.B–II.C, equations (7)–(16),
under the explicit finite-rank hypotheses recorded by `chemostat_rank_identity`.
The sanitized source contract is
`research:rao_esposito_2016:open_crn_conservation`.
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

/-- A reaction current is an emergent cycle when its net stoichiometric change
vanishes on every internal species but is nonzero on some chemostatted species. -/
def IsEmergentCycle : ∀ {Species Reaction : Type} [Fintype Reaction]
    [DecidableEq Species], Finset Species → (Reaction → Species → ℝ) →
      (Reaction → ℝ) → Prop :=
  fun chemostats stoichiometry cycle ↦
    (∀ species, species ∉ chemostats →
      ∑ reaction, stoichiometry reaction species * cycle reaction = 0) ∧
    ∃ species ∈ chemostats,
      ∑ reaction, stoichiometry reaction species * cycle reaction ≠ 0

/-- The rank-nullity count of closed conservation laws that are broken after
removing the chemostatted species from the internal dynamics. -/
def brokenLawCount : ℕ → ℕ → ℕ → ℕ → ℕ :=
  fun speciesCount chemostatCount fullRank internalRank ↦
    (speciesCount - fullRank) -
      ((speciesCount - chemostatCount) - internalRank)

/-- The number of independent cycles exposed by projecting the full
stoichiometric matrix onto the internal species. -/
def emergentCycleCount : ℕ → ℕ → ℕ :=
  fun fullRank internalRank ↦ fullRank - internalRank

/-- Under the stated rank bounds, every chemostat accounts for either an
independent broken conservation law or an independent emergent cycle. -/
theorem chemostat_rank_identity :
    ∀ {speciesCount chemostatCount fullRank internalRank : ℕ},
      chemostatCount ≤ speciesCount →
      internalRank ≤ fullRank →
      internalRank ≤ speciesCount - chemostatCount →
      fullRank ≤ speciesCount →
      fullRank ≤ internalRank + chemostatCount →
      chemostatCount =
        brokenLawCount speciesCount chemostatCount fullRank internalRank +
          emergentCycleCount fullRank internalRank := by
  intro speciesCount chemostatCount fullRank internalRank
    hchemostats hinternal hinternalSpecies hfull hrankIncrease
  simp only [brokenLawCount, emergentCycleCount]
  omega

end ChemistryLib.Thermodynamics.OpenNetworks
