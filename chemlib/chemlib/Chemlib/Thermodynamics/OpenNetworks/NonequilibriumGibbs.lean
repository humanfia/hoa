import Chemlib.Thermodynamics.OpenNetworks.RelativeEntropy
import Chemlib.Thermodynamics.TemperatureAdapters

/-!
# Nonequilibrium Gibbs free energy for ideal-dilute reaction networks

For an ideal-dilute concentration state, the state-dependent Gibbs free energy
is the sum of the standard-potential and mixing contributions.  A reference
equilibrium matches a state when their difference has zero pairing with the
equilibrium chemical potential.  This is the conserved-component condition
that removes the affine term and leaves generalized relative entropy.

The solvent-dependent additive constant in equation (70) is omitted because
it cancels in the decomposition.

Source reference: RAO-ESPOSITO-2016, Sections III.E.2–III.E.3, equations
(70)–(75), <https://arxiv.org/pdf/1602.07257v3> (artifact SHA-256
`ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`).
Sanitized contract: `research:rao_esposito_2016:nonequilibrium_free_energy`.
-/

namespace Chemlib.Thermodynamics.OpenNetworks

noncomputable section

/-- A reference equilibrium matches `z` when the concentration difference has
zero pairing with the equilibrium ideal-dilute chemical potential. -/
def IsMatchingEquilibriumReference {Species : Type} [Fintype Species]
    (gasConstant temperature : ℝ) (standardPotential z zEq : Species → ℝ) : Prop :=
  ∑ s, (z s - zEq s) *
    (standardPotential s + gasConstant * temperature * Real.log (zEq s)) = 0

/-- Gibbs free energy as enthalpy minus temperature times entropy. -/
def gibbsFreeEnergy (enthalpy temperature entropy : ℝ) : ℝ :=
  enthalpy - temperature * entropy

/-- The defining enthalpy–entropy identity for Gibbs free energy. -/
theorem gibbsFreeEnergy_eq_enthalpy_sub_temperature_mul_entropy
    (enthalpy temperature entropy : ℝ) :
    gibbsFreeEnergy enthalpy temperature entropy =
      enthalpy - temperature * entropy :=
  rfl

/-- The state-dependent Gibbs free energy of an ideal-dilute concentration
state, with the solvent-dependent additive constant omitted. -/
def idealDiluteGibbs {Species : Type} [Fintype Species]
    (gasConstant temperature : ℝ) (standardPotential z : Species → ℝ) : ℝ :=
  ∑ s, z s *
    (standardPotential s + gasConstant * temperature * Real.log (z s) -
      gasConstant * temperature)

/-- Relative to a matching equilibrium reference, ideal-dilute Gibbs free
energy differs from its equilibrium value by `R T` times generalized relative
entropy. -/
theorem idealDiluteGibbs_decomposition
    {Species : Type} [Fintype Species]
    (gasConstant temperature : ℝ) (standardPotential z zEq : Species → ℝ)
    (_hGasConstant : 0 < gasConstant) (_hTemperature : 0 < temperature)
    (_hz : ∀ s, 0 ≤ z s) (_hzEq : ∀ s, 0 < zEq s)
    (hmatch : IsMatchingEquilibriumReference gasConstant temperature
      standardPotential z zEq) :
    idealDiluteGibbs gasConstant temperature standardPotential z =
      idealDiluteGibbs gasConstant temperature standardPotential zEq +
        gasConstant * temperature * generalizedRelativeEntropy z zEq := by
  unfold idealDiluteGibbs
  unfold IsMatchingEquilibriumReference at hmatch
  unfold generalizedRelativeEntropy Chemlib.ReactionNetwork.pseudoHelmholtz
  calc
    ∑ s, z s *
        (standardPotential s + gasConstant * temperature * Real.log (z s) -
          gasConstant * temperature) =
      (∑ s, zEq s *
        (standardPotential s + gasConstant * temperature * Real.log (zEq s) -
          gasConstant * temperature)) +
        gasConstant * temperature *
          (∑ s, (z s * (Real.log (z s) - Real.log (zEq s) - 1) + zEq s)) +
        ∑ s, (z s - zEq s) *
          (standardPotential s +
            gasConstant * temperature * Real.log (zEq s)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ =
      (∑ s, zEq s *
        (standardPotential s + gasConstant * temperature * Real.log (zEq s) -
          gasConstant * temperature)) +
        gasConstant * temperature *
          (∑ s, (z s * (Real.log (z s) - Real.log (zEq s) - 1) + zEq s)) := by
      rw [hmatch, add_zero]

end

end Chemlib.Thermodynamics.OpenNetworks
