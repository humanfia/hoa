import Chemlib.Thermodynamics.OpenNetworks.Affinity

/-!
# Entropy production in open reaction networks

For a finite family of reactions, the entropy-production rate is the gas
constant times the sum of the net reaction flux multiplied by the logarithmic
forward-to-reverse flux ratio.  Each summand is nonnegative when both fluxes
are positive, so a nonnegative gas constant gives nonnegative total entropy
production.

This follows Rao and Esposito (2016), Sections III.B--III.E.1, equation (55).
Source artifact: `https://arxiv.org/pdf/1602.07257v3`, SHA-256
`ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`.
Sanitized contract: `research:rao_esposito_2016:entropy_energy_balance`.
-/

namespace Chemlib.Thermodynamics.OpenNetworks

/-- The ideal-dilute entropy-production rate formed from net reaction fluxes
and logarithmic forward-to-reverse flux ratios. -/
noncomputable def entropyProductionRate : ∀ {Reaction : Type} [Fintype Reaction],
    ℝ → (Reaction → ℝ) → (Reaction → ℝ) → ℝ :=
  fun gasConstant forwardFlux reverseFlux ↦
    gasConstant * ∑ r, (forwardFlux r - reverseFlux r) *
      Real.log (forwardFlux r / reverseFlux r)

/-- Entropy production is nonnegative for nonnegative gas constant and
strictly positive forward and reverse fluxes. -/
theorem entropyProductionRate_nonneg :
    ∀ {Reaction : Type} [Fintype Reaction] (gasConstant : ℝ)
      (forwardFlux reverseFlux : Reaction → ℝ),
      0 ≤ gasConstant → (∀ r, 0 < forwardFlux r) →
        (∀ r, 0 < reverseFlux r) →
          0 ≤ entropyProductionRate gasConstant forwardFlux reverseFlux := by
  intro Reaction _ gasConstant forwardFlux reverseFlux hGasConstant hForward hReverse
  rw [entropyProductionRate]
  exact mul_nonneg hGasConstant (Finset.sum_nonneg fun r _ ↦ by
    by_cases hOrder : reverseFlux r ≤ forwardFlux r
    · exact mul_nonneg (sub_nonneg.mpr hOrder)
        (Real.log_nonneg ((one_le_div (hReverse r)).2 hOrder))
    · have hOrder' : forwardFlux r ≤ reverseFlux r :=
        le_of_lt (lt_of_not_ge hOrder)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hOrder')
        (Real.log_nonpos (div_pos (hForward r) (hReverse r)).le
          ((div_le_one (hReverse r)).2 hOrder')))

/-- Multiplying the entropy-production rate by temperature exposes the
temperature-scaled finite flux/log-ratio sum. -/
theorem temperature_mul_entropyProductionRate :
    ∀ {Reaction : Type} [Fintype Reaction] (temperature gasConstant : ℝ)
      (forwardFlux reverseFlux : Reaction → ℝ),
      temperature * entropyProductionRate gasConstant forwardFlux reverseFlux =
        gasConstant * temperature * ∑ r,
          (forwardFlux r - reverseFlux r) * Real.log (forwardFlux r / reverseFlux r) := by
  intro Reaction _ temperature gasConstant forwardFlux reverseFlux
  simp only [entropyProductionRate]
  ring

end Chemlib.Thermodynamics.OpenNetworks
