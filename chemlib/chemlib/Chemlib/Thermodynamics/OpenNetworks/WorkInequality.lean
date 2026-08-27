import Chemlib.ReactionNetwork.ComplexBalanceDissipation
import Chemlib.Thermodynamics.OpenNetworks.Balances
import Chemlib.Thermodynamics.OpenNetworks.EntropyProduction
import Chemlib.Thermodynamics.OpenNetworks.NonequilibriumGibbs

/-!
# Chemical-work and Gibbs-rate inequalities

For a closed reaction network at fixed temperature, the Gibbs free-energy
rate is minus temperature times the entropy-production rate.  Opening the
network adds the chemical work supplied by the chemostats.  Nonnegative
entropy production therefore makes the closed Gibbs rate nonpositive and
bounds the open Gibbs rate above by the supplied chemical-work rate.

Source reference: Rao and Esposito (2016), Sections III.E.2–III.E.3,
equations (76)–(79), <https://arxiv.org/pdf/1602.07257v3> (artifact SHA-256
`ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`).
Sanitized contract:
`research:rao_esposito_2016:dissipation_work_inequality`.
-/

namespace Chemlib.Thermodynamics.OpenNetworks

/-- The fixed-temperature closed-network Gibbs dissipation identity
`Ġ = -T Σ̇`. -/
def ClosedGibbsDissipation : ℝ → ℝ → ℝ → Prop :=
  fun temperature entropyProductionRate gibbsRate ↦
    gibbsRate = -temperature * entropyProductionRate

/-- The fixed-temperature open-network Gibbs balance
`Ġ = -T Σ̇ + Ẇchem`. -/
def OpenChemicalWorkBalance : ℝ → ℝ → ℝ → ℝ → Prop :=
  fun temperature entropyProductionRate chemicalWorkRate gibbsRate ↦
    gibbsRate = -temperature * entropyProductionRate + chemicalWorkRate

/-- In an open network, the Gibbs free-energy rate cannot exceed the chemical
work rate supplied by chemostats. -/
theorem chemical_work_rate_ge_gibbs_rate :
    ∀ (temperature entropyProductionRate chemicalWorkRate gibbsRate : ℝ),
      0 < temperature → 0 ≤ entropyProductionRate →
        OpenChemicalWorkBalance temperature entropyProductionRate
          chemicalWorkRate gibbsRate →
        gibbsRate ≤ chemicalWorkRate := by
  intro temperature entropyProductionRate chemicalWorkRate gibbsRate
    hTemperature hEntropyProduction hBalance
  unfold OpenChemicalWorkBalance at hBalance
  nlinarith

/-- In a closed network, the Gibbs free-energy rate is nonpositive. -/
theorem closed_gibbs_rate_nonpos :
    ∀ (temperature entropyProductionRate gibbsRate : ℝ),
      0 < temperature → 0 ≤ entropyProductionRate →
        ClosedGibbsDissipation temperature entropyProductionRate gibbsRate →
        gibbsRate ≤ 0 := by
  intro temperature entropyProductionRate gibbsRate hTemperature
    hEntropyProduction hDissipation
  unfold ClosedGibbsDissipation at hDissipation
  nlinarith

/-- The pseudo-Helmholtz orbital derivative is nonpositive at a
complex-balanced reference state. -/
theorem complexBalanced_pseudoHelmholtz_rate_nonpos :
    ∀ {Species ComplexId ReactionId : Type}
      [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
      [DecidableEq Species] [DecidableEq ComplexId]
      (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
      (k : ReactionId → ℝ) (xStar x : Species → ℝ),
      N.IsComplexBalanced k xStar → (∀ s, 0 < x s) →
        N.pseudoHelmholtzOrbitalDerivative k xStar x ≤ 0 := by
  intro Species ComplexId ReactionId _ _ _ _ _ N k xStar x hBalance hPositive
  exact N.pseudoHelmholtz_derivative_nonpos k xStar x hBalance hPositive

end Chemlib.Thermodynamics.OpenNetworks
