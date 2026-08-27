import Chemlib.ReactionNetwork.Stoichiometry
import Chemlib.Thermodynamics.OpenNetworks.Partition

/-!
# Rate equations for open reaction networks

The rate of change of a species is split into a stoichiometric reaction
contribution and an externally supplied reservoir current.  The reaction
fluxes and reservoir currents remain explicit parameters: this module does not
prescribe a kinetic law or a model of the chemostats.

This follows Rao and Esposito (2016), Sections II.B–II.C, equations (7)–(16),
in particular the internal-species and chemostatted-species rate equations
(9) and (10).
-/

namespace Chemlib.Thermodynamics.OpenNetworks

/-- A reservoir current is a chemostat current when it vanishes on every
species outside the selected finite set of chemostats. -/
def IsChemostatCurrent : ∀ {Species : Type} [DecidableEq Species],
    Finset Species → (Species → ℝ) → Prop :=
  fun chemostats current ↦
    ∀ species, species ∉ chemostats → current species = 0

/-- The species-formation rate due to the reaction fluxes: the finite
stoichiometric sum over reaction pathways. -/
def reactionSpeciesRate : ∀ {Species Reaction : Type} [Fintype Reaction],
    (Reaction → Species → ℝ) → (Reaction → ℝ) → Species → ℝ :=
  fun stoichiometry flux species ↦
    Finset.univ.sum (fun reaction ↦ stoichiometry reaction species * flux reaction)

/-- The open-network species rate is the reaction contribution plus the
externally supplied reservoir current. -/
def openSpeciesRate : ∀ {Species Reaction : Type} [Fintype Reaction],
    (Reaction → Species → ℝ) → (Reaction → ℝ) →
      (Species → ℝ) → Species → ℝ :=
  fun stoichiometry flux current species ↦
    reactionSpeciesRate stoichiometry flux species + current species

/-- An internal species has no reservoir-current contribution, so its open
rate is exactly its reaction-induced rate. -/
theorem openSpeciesRate_eq_reactionSpeciesRate_of_internal :
    ∀ {Species Reaction : Type} [DecidableEq Species] [Fintype Reaction]
      (Y : Finset Species) (ν : Reaction → Species → ℝ)
      (j : Reaction → ℝ) (I : Species → ℝ) (s : Species),
      IsChemostatCurrent Y I → s ∉ Y →
        openSpeciesRate ν j I s = reactionSpeciesRate ν j s := by
  intro Species Reaction _ _ Y ν j I s hI hs
  simp only [openSpeciesRate, hI s hs, add_zero]

end Chemlib.Thermodynamics.OpenNetworks
