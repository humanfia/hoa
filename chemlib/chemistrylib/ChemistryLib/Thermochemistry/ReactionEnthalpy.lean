import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import ChemistryLib.Foundations.Stoichiometry

/-!
# Reaction enthalpy

The reaction enthalpy is the stoichiometric sum of the species' formation
enthalpies, with the signed stoichiometric numbers distinguishing products from
reactants.

Source:

* `icho_2026_t4_a6:T4-A6`, IChO 2026 Theory Task 4.6, p. 38:
  <https://scheikundeolympiade.science.ru.nl/internationaal/2026/IChO2026%20Theory%20task%20final%20English.pdf>
-/

namespace ChemistryLib.Thermochemistry

/-- The reaction enthalpy obtained from signed stoichiometric numbers and
species formation enthalpies. -/
def reactionEnthalpy {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (formationEnthalpy : Species → ℝ) : ℝ :=
  Finset.univ.sum (fun species ↦ (nu species : ℝ) * formationEnthalpy species)

/-- Reaction enthalpy unfolds to its defining stoichiometric sum. -/
theorem reactionEnthalpy_eq_sum {Species : Type} [Fintype Species]
    (nu : ChemistryLib.Foundations.StoichiometricNumber Species)
    (formationEnthalpy : Species → ℝ) :
    reactionEnthalpy nu formationEnthalpy =
      Finset.univ.sum (fun species ↦ (nu species : ℝ) * formationEnthalpy species) := by
  rfl

end ChemistryLib.Thermochemistry
