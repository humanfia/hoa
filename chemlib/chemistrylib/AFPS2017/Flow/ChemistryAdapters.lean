import AFPS2017.Sequence.StoichiometryAdapter
import ChemistryLib.Process.ProductionYield
import ChemistryLib.Thermodynamics.OpenNetworks.RateEquation

/-!
# Flow chemistry adapters

This module specializes ChemistryLib's open-network rate equation to the
verified coarse coupling network and delegates stoichiometric production
ratios and required feed mass directly to ChemistryLib's process API.  The
reservoir-current contribution vanishes only for a species certified to be
internal by the model's explicit chemostat-current witness.

Source references:

* Sanitized flow-protocol contract (`afps2017.flow.protocol:question`).
* Sanitized sequence contract (`afps2017.sequence.contract:question`).
-/

namespace AFPS2017.Flow

noncomputable section

local instance : DecidableEq AFPS2017.Sequence.CouplingSpecies :=
  Classical.decEq _

local instance : DecidableEq AFPS2017.Sequence.CouplingReactionId :=
  Classical.decEq _

/- USER: Keep this instance exported, not local. The locked theorem below uses
`reactionSpeciesRate`; its exact signature must re-elaborate in a downstream
importer, where a local instance from this source is unavailable. The campaign's
locked-name scanner excludes this anonymous support instance from the 10 APIs. -/
instance : Fintype AFPS2017.Sequence.CouplingReactionId where
  elems := {.amideFormation}
  complete := by
    intro reaction
    cases reaction
    simp

/-- Fluxes and chemostat currents for the coarse coupling reaction network. -/
structure OpenCouplingModel : Type where
  /-- Species whose external currents may be nonzero. -/
  chemostats : Finset AFPS2017.Sequence.CouplingSpecies
  /-- Reaction flux through each coarse coupling reaction. -/
  reactionFlux : AFPS2017.Sequence.CouplingReactionId → ℝ
  /-- Externally supplied species current. -/
  reservoirCurrent : AFPS2017.Sequence.CouplingSpecies → ℝ
  /-- The reservoir current vanishes away from the selected chemostats. -/
  isChemostatCurrent :
    ChemistryLib.Thermodynamics.OpenNetworks.IsChemostatCurrent
      chemostats reservoirCurrent

/-- ChemistryLib's open species rate specialized to the coarse coupling network. -/
def couplingOpenSpeciesRate (model : OpenCouplingModel)
    (species : AFPS2017.Sequence.CouplingSpecies) : ℝ :=
  ChemistryLib.Thermodynamics.OpenNetworks.openSpeciesRate
    (fun reaction species ↦
      AFPS2017.Sequence.couplingNetwork.reactionVector reaction species)
    model.reactionFlux model.reservoirCurrent species

/-- An internal coupling species receives no reservoir-current contribution. -/
theorem couplingOpenSpeciesRate_eq_reaction_of_internal
    (model : OpenCouplingModel)
    (species : AFPS2017.Sequence.CouplingSpecies)
    (internal : species ∉ model.chemostats) :
    couplingOpenSpeciesRate model species =
      ChemistryLib.Thermodynamics.OpenNetworks.reactionSpeciesRate
        (fun reaction species ↦
          AFPS2017.Sequence.couplingNetwork.reactionVector reaction species)
        model.reactionFlux species := by
  exact
    ChemistryLib.Thermodynamics.OpenNetworks.openSpeciesRate_eq_reactionSpeciesRate_of_internal
        model.chemostats
        (fun reaction species ↦
          AFPS2017.Sequence.couplingNetwork.reactionVector reaction species)
        model.reactionFlux model.reservoirCurrent species
        model.isChemostatCurrent internal

/-- Product obtained per unit feed, with ChemistryLib's signed stoichiometry semantics. -/
def stoichiometricProductPerFeedRatio {Species : Type}
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (feed product : Species) : ℝ :=
  ChemistryLib.Process.productPerFeedRatio nu feed product

/-- Required feed mass delegated to ChemistryLib's production-yield calculation. -/
def stoichiometricRequiredFeedMass {Species : Type}
    (productMass feedMolarMass productMolarMass : ℝ)
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (yield : ℝ) : ℝ :=
  ChemistryLib.Process.requiredFeedMass
    productMass feedMolarMass productMolarMass nu feed product yield

/-- The feed-mass adapter is exactly ChemistryLib's required-feed-mass definition. -/
theorem stoichiometricRequiredFeedMass_eq {Species : Type}
    (productMass feedMolarMass productMolarMass : ℝ)
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (feed product : Species) (yield : ℝ) :
    stoichiometricRequiredFeedMass
        productMass feedMolarMass productMolarMass nu feed product yield =
      ChemistryLib.Process.requiredFeedMass
        productMass feedMolarMass productMolarMass nu feed product yield :=
  rfl

end

end AFPS2017.Flow
