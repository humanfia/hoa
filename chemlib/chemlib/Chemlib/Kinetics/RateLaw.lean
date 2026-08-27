import Chemlib.ReactionNetwork.MassAction

/-!
# Positive mass-action rate switching

For two mass-action fluxes with a common positive factor, this module gives the
competitor concentration at which the fast pathway overtakes the slow pathway.

The rate-law interpretation follows the IUPAC Gold Book entries for rate of
reaction and rate law (`research:iupac_goldbook_2025:mass_action_rate_law`,
terms R05141 and 08184).  The rate-switch formulation is motivated by
`icho_2026_t2_a3:T2-A3`.
-/

namespace Chemlib.Kinetics

/-- The competitor concentration at which the two factored rates are equal. -/
noncomputable def criticalCompetitorConcentration : ℝ → ℝ → ℝ → ℝ :=
  fun kFast kSlow substrate ↦ kSlow * substrate / kFast

/-- The critical competitor concentration has its defining quotient form. -/
theorem criticalCompetitorConcentration_eq :
    {kFast kSlow substrate : ℝ} →
      criticalCompetitorConcentration kFast kSlow substrate =
        kSlow * substrate / kFast := by
  intro kFast kSlow substrate
  rfl

/-- With positive fast rate constant and common factor, the fast flux exceeds
the slow flux exactly above the critical competitor concentration. -/
theorem massActionFlux_rateSwitch_iff_above_critical
    {Species ComplexId ReactionId : Type}
    (N : Chemlib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (x : Species → ℝ)
    (fastReaction slowReaction : ReactionId)
    {kFast kSlow substrate competitor common : ℝ}
    (hFast : N.massActionFlux k x fastReaction = kFast * competitor * common)
    (hSlow : N.massActionFlux k x slowReaction = kSlow * substrate * common)
    (hkFast : 0 < kFast) (hcommon : 0 < common) :
    (N.massActionFlux k x fastReaction > N.massActionFlux k x slowReaction ↔
      competitor > criticalCompetitorConcentration kFast kSlow substrate) := by
  rw [hFast, hSlow]
  constructor
  · intro hFlux
    have hWithoutCommon : kSlow * substrate < kFast * competitor := by
      by_contra h
      have hLe : kFast * competitor ≤ kSlow * substrate := le_of_not_gt h
      have hFluxLe : kFast * competitor * common ≤ kSlow * substrate * common :=
        mul_le_mul_of_nonneg_right hLe (le_of_lt hcommon)
      exact (not_lt_of_ge hFluxLe) hFlux
    apply (div_lt_iff₀ hkFast).2
    simpa [mul_comm] using hWithoutCommon
  · intro hCompetitor
    have hWithoutDivision : kSlow * substrate < competitor * kFast :=
      (div_lt_iff₀ hkFast).mp hCompetitor
    have hWithoutCommon : kSlow * substrate < kFast * competitor := by
      simpa [mul_comm] using hWithoutDivision
    exact mul_lt_mul_of_pos_right hWithoutCommon hcommon

end Chemlib.Kinetics
