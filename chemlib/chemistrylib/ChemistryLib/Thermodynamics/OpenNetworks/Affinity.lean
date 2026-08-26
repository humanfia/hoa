import ChemistryLib.Thermodynamics.OpenNetworks.RateEquation
import ChemistryLib.Thermodynamics.TemperatureAdapters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reaction affinity in open reaction networks

The Gibbs free-energy change of a reaction is the finite stoichiometric sum of
the species chemical potentials, and the reaction affinity is its negative.
Local detailed balance is recorded as an explicit, hypothesis-indexed relation
between affinity and the logarithm of the forward-to-reverse flux ratio.

This follows Rao and Esposito (2016), Sections III.B--III.E.1, equations
(46)--(69), especially equation (48).  Source artifact:
`https://arxiv.org/pdf/1602.07257v3`, SHA-256
`ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`.
Sanitized contract: `research:rao_esposito_2016:entropy_energy_balance`.
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

/-- Local detailed balance identifies each reaction affinity with the
gas-constant/temperature-scaled logarithmic forward-to-reverse flux ratio. -/
def LocalDetailedBalance : ∀ {Reaction : Type} (T : Temperature),
    ChemistryLib.Thermodynamics.PositiveAbsoluteTemperature T → ℝ →
      (Reaction → ℝ) → (Reaction → ℝ) → (Reaction → ℝ) → Prop :=
  fun T _hT gasConstant forwardFlux reverseFlux affinity ↦
    ∀ r, affinity r = gasConstant * T.val * Real.log (forwardFlux r / reverseFlux r)

/-- The affinity formula supplied by a local-detailed-balance witness. -/
theorem localDetailedBalance_affinity : ∀ {Reaction : Type} (T : Temperature)
    (hT : ChemistryLib.Thermodynamics.PositiveAbsoluteTemperature T)
    (gasConstant : ℝ) (forwardFlux reverseFlux affinity : Reaction → ℝ),
    LocalDetailedBalance T hT gasConstant forwardFlux reverseFlux affinity →
      ∀ r, affinity r = gasConstant * T.val * Real.log (forwardFlux r / reverseFlux r) := by
  intro Reaction T hT gasConstant forwardFlux reverseFlux affinity hBalance
  exact hBalance

/-- The Gibbs free-energy change of a reaction, obtained by pairing its
stoichiometric coefficients with the species chemical potentials. -/
def reactionGibbsEnergy : ∀ {Species Reaction : Type} [Fintype Species],
    (Reaction → Species → ℝ) → (Species → ℝ) → Reaction → ℝ :=
  fun ν μ r ↦ ∑ s, ν r s * μ s

/-- Reaction affinity is the negative reaction Gibbs free-energy change. -/
def reactionAffinity : ∀ {Species Reaction : Type} [Fintype Species],
    (Reaction → Species → ℝ) → (Species → ℝ) → Reaction → ℝ :=
  fun ν μ r ↦ -reactionGibbsEnergy ν μ r

/-- Reaction affinity is exactly minus the corresponding Gibbs free-energy
change. -/
theorem reactionAffinity_eq_neg_reactionGibbsEnergy :
    ∀ {Species Reaction : Type} [Fintype Species]
      (ν : Reaction → Species → ℝ) (μ : Species → ℝ) (r : Reaction),
      reactionAffinity ν μ r = -reactionGibbsEnergy ν μ r := by
  intro Species Reaction _ ν μ r
  rfl

end ChemistryLib.Thermodynamics.OpenNetworks
