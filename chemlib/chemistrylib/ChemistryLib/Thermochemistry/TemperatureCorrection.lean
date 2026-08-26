import ChemistryLib.Thermochemistry.ReactionEnthalpy

/-!
# Constant-heat-capacity temperature correction

For temperature-independent species heat capacities, the reaction heat-capacity
change is their signed stoichiometric sum.  Kirchhoff's law then corrects a
reference reaction enthalpy by `deltaCp * (targetTemperature - referenceTemperature)`.

Source:

* `icho_2026_t4_a7:T4-A7`, IChO 2026 Theory Task 4.7, p. 39:
  <https://scheikundeolympiade.science.ru.nl/internationaal/2026/IChO2026%20Theory%20task%20final%20English.pdf>
-/

namespace ChemistryLib.Thermochemistry

/-- The reaction heat-capacity change obtained from signed stoichiometric
numbers and constant species heat capacities. -/
def reactionHeatCapacityChange {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (heatCapacity : Species → ℝ) : ℝ :=
  Finset.univ.sum (fun species ↦ (nu species : ℝ) * heatCapacity species)

/-- The reaction heat-capacity change unfolds to its defining stoichiometric
sum. -/
theorem reactionHeatCapacityChange_eq_sum {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (heatCapacity : Species → ℝ) :
    reactionHeatCapacityChange nu heatCapacity =
      Finset.univ.sum (fun species ↦ (nu species : ℝ) * heatCapacity species) := by
  rfl

/-- Correct a reference reaction enthalpy to a target temperature under the
constant-heat-capacity approximation. -/
def reactionEnthalpyAt
    (referenceEnthalpy deltaCp referenceTemperature targetTemperature : ℝ) : ℝ :=
  referenceEnthalpy + deltaCp * (targetTemperature - referenceTemperature)

/-- Compute the target-temperature reaction enthalpy from reference-temperature
formation enthalpies and constant species heat capacities. -/
def reactionEnthalpyFromFormationAt {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (formationEnthalpy heatCapacity : Species → ℝ)
    (referenceTemperature targetTemperature : ℝ) : ℝ :=
  reactionEnthalpyAt (reactionEnthalpy nu formationEnthalpy)
    (reactionHeatCapacityChange nu heatCapacity) referenceTemperature targetTemperature

/-- The constant-heat-capacity correction has Kirchhoff's form and composes
with the formation-enthalpy stoichiometric sum. -/
theorem reactionEnthalpyCorrections {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (formationEnthalpy heatCapacity : Species → ℝ)
    (referenceEnthalpy deltaCp referenceTemperature targetTemperature : ℝ) :
    reactionEnthalpyAt referenceEnthalpy deltaCp referenceTemperature targetTemperature =
        referenceEnthalpy + deltaCp * (targetTemperature - referenceTemperature) ∧
      reactionEnthalpyFromFormationAt nu formationEnthalpy heatCapacity
          referenceTemperature targetTemperature =
        reactionEnthalpyAt (reactionEnthalpy nu formationEnthalpy)
          (reactionHeatCapacityChange nu heatCapacity)
          referenceTemperature targetTemperature := by
  constructor <;> rfl

end ChemistryLib.Thermochemistry
