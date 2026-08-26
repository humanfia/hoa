import ChemistryLib.Kinetics.RateLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Closed-form scalar kinetics

This module records the exponential trajectory and logarithmic threshold time
for first-order decay, together with the scalar roots of linear and quadratic
steady-state residuals.  The kinetics conventions follow
`research:iupac_goldbook_2025:mass_action_rate_law` (terms R05141 and 08184)
and the steady-state interpretation follows
`research:iupac_goldbook_2025:steady_state_approximation` (term S05962).
The closed forms are motivated by `icho_2026_t2_a2:T2-A2` and
`icho_2026_t2_a5:T2-A5`.
-/

namespace ChemistryLib.Kinetics

/-- The concentration along a first-order exponential trajectory. -/
noncomputable def firstOrderConcentration : ℝ → ℝ → ℝ → ℝ :=
  fun initial rate time ↦ initial * Real.exp (-rate * time)

/-- The logarithmic time at which a first-order trajectory reaches a threshold. -/
noncomputable def firstOrderThresholdTime : ℝ → ℝ → ℝ → ℝ :=
  fun initial threshold rate ↦ Real.log (initial / threshold) / rate

/-- At the logarithmic switching time, the trajectory reaches the positive
mass-action critical competitor concentration. -/
theorem firstOrderConcentration_at_critical :
    {initial rate kFast kSlow substrate : ℝ} →
      0 < initial → 0 < kFast → 0 < kSlow → 0 < substrate → rate ≠ 0 →
      firstOrderConcentration initial rate
          (firstOrderThresholdTime initial
            (criticalCompetitorConcentration kFast kSlow substrate) rate) =
        criticalCompetitorConcentration kFast kSlow substrate := by
  intro initial rate kFast kSlow substrate hinitial hkFast hkSlow hsubstrate hrate
  have hinitial_ne : initial ≠ 0 := ne_of_gt hinitial
  have hcritical : 0 < criticalCompetitorConcentration kFast kSlow substrate := by
    rw [criticalCompetitorConcentration_eq]
    exact div_pos (mul_pos hkSlow hsubstrate) hkFast
  have hcritical_ne : criticalCompetitorConcentration kFast kSlow substrate ≠ 0 :=
    ne_of_gt hcritical
  have hratio :
      0 < criticalCompetitorConcentration kFast kSlow substrate / initial :=
    div_pos hcritical hinitial
  unfold firstOrderConcentration firstOrderThresholdTime
  calc
    initial * Real.exp
        (-rate *
          (Real.log
            (initial / criticalCompetitorConcentration kFast kSlow substrate) /
            rate)) =
        initial * Real.exp
          (Real.log
            (criticalCompetitorConcentration kFast kSlow substrate / initial)) := by
      congr 2
      rw [Real.log_div hinitial_ne hcritical_ne,
        Real.log_div hcritical_ne hinitial_ne]
      field_simp [hrate]
      ring
    _ = initial *
        (criticalCompetitorConcentration kFast kSlow substrate / initial) := by
      rw [Real.exp_log hratio]
    _ = criticalCompetitorConcentration kFast kSlow substrate := by
      field_simp [hinitial_ne]

/-- A positive rate and a threshold no larger than the initial concentration
give a nonnegative threshold time. -/
theorem firstOrderThresholdTime_nonneg :
    {initial threshold rate : ℝ} →
      0 < threshold → threshold ≤ initial → 0 < rate →
      0 ≤ firstOrderThresholdTime initial threshold rate := by
  intro initial threshold rate hthreshold hle hrate
  unfold firstOrderThresholdTime
  apply div_nonneg
  · exact Real.log_nonneg ((one_le_div₀ hthreshold).2 hle)
  · exact le_of_lt hrate

/-- On the positive concentration domain and for nonzero rate, the logarithmic
threshold time is the unique time at which the trajectory reaches the
threshold. -/
theorem firstOrderThresholdTime_spec_unique :
    {initial threshold rate time : ℝ} →
      0 < initial → 0 < threshold → rate ≠ 0 →
      (firstOrderConcentration initial rate time = threshold ↔
        time = firstOrderThresholdTime initial threshold rate) := by
  intro initial threshold rate time hinitial hthreshold hrate
  have hinitial_ne : initial ≠ 0 := ne_of_gt hinitial
  have hthreshold_ne : threshold ≠ 0 := ne_of_gt hthreshold
  unfold firstOrderConcentration firstOrderThresholdTime
  constructor
  · intro h
    have hExp : Real.exp (-rate * time) = threshold / initial := by
      apply (eq_div_iff hinitial_ne).2
      simpa [mul_comm] using h
    have hLog := congrArg Real.log hExp
    rw [Real.log_exp, Real.log_div hthreshold_ne hinitial_ne] at hLog
    rw [Real.log_div hinitial_ne hthreshold_ne]
    apply (eq_div_iff hrate).2
    nlinarith
  · intro h
    rw [h]
    have hratio : 0 < threshold / initial := div_pos hthreshold hinitial
    calc
      initial * Real.exp
          (-rate * (Real.log (initial / threshold) / rate)) =
          initial * Real.exp (Real.log (threshold / initial)) := by
        congr 2
        rw [Real.log_div hinitial_ne hthreshold_ne,
          Real.log_div hthreshold_ne hinitial_ne]
        field_simp [hrate]
        ring
      _ = initial * (threshold / initial) := by rw [Real.exp_log hratio]
      _ = threshold := by field_simp [hinitial_ne]

/-- The two first-order constructions have their locked exponential and
logarithmic closed forms. -/
theorem firstOrder_closedForms :
    (initial threshold rate time : ℝ) →
      firstOrderConcentration initial rate time =
          initial * Real.exp (-rate * time) ∧
        firstOrderThresholdTime initial threshold rate =
          Real.log (initial / threshold) / rate := by
  intro initial threshold rate time
  exact ⟨rfl, rfl⟩

/-- The closed-form root of a linear production-loss residual. -/
noncomputable def linearSteadyConcentration : ℝ → ℝ → ℝ :=
  fun production loss ↦ production / loss

/-- The quotient is the unique root of the linear residual whenever loss is
nonzero. -/
theorem linearSteadyConcentration_spec :
    (production loss : ℝ) →
      linearSteadyConcentration production loss = production / loss ∧
        (loss ≠ 0 → ∀ x : ℝ,
          (production - loss * x = 0 ↔
            x = linearSteadyConcentration production loss)) := by
  intro production loss
  unfold linearSteadyConcentration
  constructor
  · rfl
  · intro hloss x
    constructor
    · intro h
      apply (eq_div_iff hloss).2
      nlinarith
    · intro h
      rw [h]
      field_simp [hloss]
      ring

/-- The nonzero closed-form root of an autocatalytic quadratic residual. -/
noncomputable def nonzeroAutocatalyticSteadyConcentration : ℝ → ℝ → ℝ :=
  fun growth quadraticLoss ↦ growth / quadraticLoss

/-- On the positive branch, the quotient characterizes the nonzero root of
the autocatalytic quadratic residual. -/
theorem nonzeroAutocatalyticSteadyConcentration_spec :
    (growth quadraticLoss : ℝ) →
      nonzeroAutocatalyticSteadyConcentration growth quadraticLoss =
          growth / quadraticLoss ∧
        (0 < quadraticLoss → ∀ x : ℝ, 0 < x →
          (growth * x - quadraticLoss * x ^ 2 = 0 ↔
            x = nonzeroAutocatalyticSteadyConcentration growth quadraticLoss)) := by
  intro growth quadraticLoss
  unfold nonzeroAutocatalyticSteadyConcentration
  constructor
  · rfl
  · intro hquadratic x hx
    have hquadratic_ne : quadraticLoss ≠ 0 := ne_of_gt hquadratic
    constructor
    · intro hroot
      have hfactor : x * (growth - quadraticLoss * x) = 0 := by
        calc
          x * (growth - quadraticLoss * x) =
              growth * x - quadraticLoss * x ^ 2 := by ring
          _ = 0 := hroot
      have hlinear : growth - quadraticLoss * x = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hx)
      apply (eq_div_iff hquadratic_ne).2
      nlinarith
    · intro h
      rw [h]
      field_simp [hquadratic_ne]
      ring

end ChemistryLib.Kinetics
