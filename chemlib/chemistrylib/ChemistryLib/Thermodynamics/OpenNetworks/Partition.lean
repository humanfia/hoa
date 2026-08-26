import ChemistryLib.ReactionNetwork.Basic
import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Internal and chemostatted species

An open reaction network distinguishes the species maintained by reservoirs
(the chemostats) from the internal species whose amounts evolve only through
the network reactions.  Given the empirical finite set of chemostatted
species, an internal species is exactly one outside that set.  Thus every
modeled species lies in exactly one side of the partition.

This follows the species partition in Rao and Esposito (2016), Sections
II.B–II.C, equations (7)–(16).
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

/-- A species is internal when it is not among the finitely many chemostatted
species selected for the open reaction network. -/
def IsInternal : ∀ {Species : Type} [DecidableEq Species],
    Finset Species → Species → Prop :=
  fun chemostats species ↦ species ∉ chemostats

end ChemistryLib.Thermodynamics.OpenNetworks
