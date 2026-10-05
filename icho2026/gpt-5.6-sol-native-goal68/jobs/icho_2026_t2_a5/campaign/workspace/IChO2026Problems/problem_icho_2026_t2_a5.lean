import IChO2026Chem.Reporting

/-!
# IChO 2026 T2-A5: period of the BZ oscillation

The constants below are the decimal data printed in the problem and are kept
as exact real numbers.  The steady-state equations are mass-action balances
for the elementary steps printed in T2.  During the long, colourless Process B
part of a cycle, Ce(IV) is absent to the stated approximation, so Process C
does not contribute appreciably to the slow bromide balance.  The problem also
states that the return to the maximum bromide concentration is almost
immediate.  Thus the requested period is the time of the slow Process B decay.
-/

namespace IChO2026Problems.T2A5

open Finset Real
open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem data -/

def k1 : ℝ := 1.0 * 10 ^ 4
def k2 : ℝ := 6.2 * 10 ^ 4
def k3 : ℝ := 4.0 * 10 ^ 7
def k4 : ℝ := 2.0 * 10 ^ 9
def k5 : ℝ := 2.1

def bromate : ℝ := 0.06
def proton : ℝ := 0.8
def bromideMax : ℝ := 7.0 * 10 ^ (-4 : ℤ)

/-! ## Elementary rates and steady-state prerequisites -/

/-- Rate of elementary step (1). -/
def v1 (hbro2 : ℝ) : ℝ := k1 * hbro2 * bromate * proton

/-- Rate of elementary step (2). -/
def v2 (bro2 ce3 : ℝ) : ℝ := k2 * bro2 * ce3 * proton

/-- Rate of elementary step (3). -/
def v3 (hbro2 : ℝ) : ℝ := k3 * hbro2 ^ 2

/-- Rate of elementary step (4). -/
def v4 (hbro2 bromide : ℝ) : ℝ := k4 * hbro2 * bromide * proton

/-- Rate of elementary step (5). -/
def v5 (bromide : ℝ) : ℝ := k5 * bromate * bromide * proton ^ 2

/-- Full Process A steady-state balances.  Step (1) makes two BrO₂ radicals,
step (2) consumes one; HBrO₂ is consumed once in (1), made once in (2), and
consumed twice in (3). -/
def ProcessASteadyState (hbro2 bro2 ce3 : ℝ) : Prop :=
  0 < hbro2 ∧ 2 * v1 hbro2 = v2 bro2 ce3 ∧
    -v1 hbro2 + v2 bro2 ce3 - 2 * v3 hbro2 = 0

/-- In Process A, eliminating the stationary BrO₂ rate gives `v₁ = 2v₃`. -/
theorem processA_reduced_balance {hbro2 bro2 ce3 : ℝ}
    (hss : ProcessASteadyState hbro2 bro2 ce3) :
    v1 hbro2 = 2 * v3 hbro2 := by
  rcases hss with ⟨_, hbro2rad, hhbro2⟩
  linarith

/-- The Process A stationary HBrO₂ concentration, derived rather than taken
from the fallback value printed for later parts. -/
theorem hbro2_processA {hbro2 bro2 ce3 : ℝ}
    (hss : ProcessASteadyState hbro2 bro2 ce3) :
    hbro2 = 6 * 10 ^ (-6 : ℤ) := by
  have hbal := processA_reduced_balance hss
  have hh : hbro2 ≠ 0 := ne_of_gt hss.1
  have hfac : hbro2 * (k1 * bromate * proton) =
      hbro2 * (2 * k3 * hbro2) := by
    calc
      hbro2 * (k1 * bromate * proton) = v1 hbro2 := by rw [v1]; ring
      _ = 2 * v3 hbro2 := hbal
      _ = hbro2 * (2 * k3 * hbro2) := by rw [v3]; ring
  have := mul_left_cancel₀ hh hfac
  norm_num [k1, k3, bromate, proton] at this ⊢
  linarith

/-- Process B stationary balance for HBrO₂: step (5) produces it and step (4)
consumes it. -/
def ProcessBSteadyState (hbro2 bromide : ℝ) : Prop :=
  0 < hbro2 ∧ 0 < bromide ∧ v4 hbro2 bromide = v5 bromide

/-- The Process B stationary HBrO₂ concentration, again derived from the
printed elementary rates rather than using the fallback. -/
theorem hbro2_processB {hbro2 bromide : ℝ}
    (hss : ProcessBSteadyState hbro2 bromide) :
    hbro2 = 5.04 * 10 ^ (-11 : ℤ) := by
  have hfactor : bromide * proton * (k4 * hbro2) =
      bromide * proton * (k5 * bromate * proton) := by
    calc
      bromide * proton * (k4 * hbro2) = v4 hbro2 bromide := by rw [v4]; ring
      _ = v5 bromide := hss.2.2
      _ = bromide * proton * (k5 * bromate * proton) := by rw [v5]; ring
  have hne : bromide * proton ≠ 0 :=
    mul_ne_zero (ne_of_gt hss.2.1) (by norm_num [proton])
  have := mul_left_cancel₀ hne hfactor
  norm_num [k4, k5, bromate, proton] at this ⊢
  linarith

/-- Equality of the rates of steps (1) and (4) at a process switch. -/
def AtSwitch (hbro2 bromide : ℝ) : Prop :=
  0 < hbro2 ∧ v4 hbro2 bromide = v1 hbro2

/-- The critical bromide concentration is independently derived from the
printed switching rule, not taken from the problem's fallback. -/
theorem bromide_critical {hbro2 bromide : ℝ} (hs : AtSwitch hbro2 bromide) :
    bromide = 3.0 * 10 ^ (-7 : ℤ) := by
  have hfactor : hbro2 * proton * (k4 * bromide) =
      hbro2 * proton * (k1 * bromate) := by
    calc
      hbro2 * proton * (k4 * bromide) = v4 hbro2 bromide := by rw [v4]; ring
      _ = v1 hbro2 := hs.2
      _ = hbro2 * proton * (k1 * bromate) := by rw [v1]; ring
  have hne : hbro2 * proton ≠ 0 :=
    mul_ne_zero (ne_of_gt hs.1) (by norm_num [proton])
  have := mul_left_cancel₀ hne hfactor
  norm_num [k1, k4, bromate] at this ⊢
  linarith

def hbro2B : ℝ := 5.04 * 10 ^ (-11 : ℤ)
def bromideCritical : ℝ := 3.0 * 10 ^ (-7 : ℤ)

/-- The derived value is not only necessary: it satisfies the Process B
steady-state balance at every positive bromide concentration. -/
theorem hbro2B_is_stationary {bromide : ℝ} (hb : 0 < bromide) :
    ProcessBSteadyState hbro2B bromide := by
  refine ⟨by norm_num [hbro2B], hb, ?_⟩
  norm_num [v4, v5, k4, k5, hbro2B, bromate, proton]
  ring

/-- The independently calculated critical value realizes equality of the two
competing elementary rates for every positive HBrO₂ concentration. -/
theorem bromideCritical_is_switch {hbro2 : ℝ} (hh : 0 < hbro2) :
    AtSwitch hbro2 bromideCritical := by
  refine ⟨hh, ?_⟩
  norm_num [AtSwitch, v4, v1, k1, k4, bromideCritical, bromate, proton]
  ring

theorem bromideCritical_lt_max : bromideCritical < bromideMax := by
  norm_num [bromideCritical, bromideMax]

/-- Since `v₄ = v₅` in Process B and each consumes one bromide, the total
slow-phase bromide disappearance rate is
`2 k₄ [HBrO₂]B [H⁺] [Br⁻]`. -/
def bromideDecayConstant : ℝ := 2 * k4 * hbro2B * proton

theorem bromide_decay_constant_value :
    bromideDecayConstant = 504 / 3125 := by
  norm_num [bromideDecayConstant, k4, hbro2B, proton]

/-- The two elementary bromide-consuming rates give exactly the coefficient
used in the slow-phase balance. -/
theorem processB_bromide_loss_rate (bromide : ℝ) :
    v4 hbro2B bromide + v5 bromide = bromideDecayConstant * bromide := by
  norm_num [v4, v5, bromideDecayConstant, k4, k5, hbro2B, bromate, proton]
  ring

/-- The explicit solution of the first-order slow-phase bromide balance. -/
def bromideDuringSlowPhase (t : ℝ) : ℝ :=
  bromideMax * exp (-bromideDecayConstant * t)

theorem bromide_slow_phase_initial : bromideDuringSlowPhase 0 = bromideMax := by
  simp [bromideDuringSlowPhase]

/-- The trajectory really satisfies `d[Br⁻]/dt = -κ[Br⁻]`. -/
theorem bromide_slow_phase_rate (t : ℝ) :
    HasDerivAt bromideDuringSlowPhase
      (-bromideDecayConstant * bromideDuringSlowPhase t) t := by
  change HasDerivAt
    (fun x => bromideMax * exp (-bromideDecayConstant * x))
    (-bromideDecayConstant *
      (bromideMax * exp (-bromideDecayConstant * t))) t
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    ((hasDerivAt_const_mul (x := t) (-bromideDecayConstant)).exp.const_mul bromideMax)

/-- Raw (unrounded) duration of the slow part of one oscillation. -/
def periodRaw : ℝ :=
  log (bromideMax / bromideCritical) / bromideDecayConstant

theorem period_raw_exact :
    periodRaw = (3125 / 504 : ℝ) * log (7000 / 3) := by
  norm_num [periodRaw, bromideMax, bromideCritical,
    bromideDecayConstant, k4, hbro2B, proton]
  ring

/-- At the raw period the exponentially decaying bromide concentration reaches
the independently derived critical concentration. -/
theorem bromide_at_period :
    bromideDuringSlowPhase periodRaw = bromideCritical := by
  have hκ : bromideDecayConstant ≠ 0 := by
    rw [bromide_decay_constant_value]
    norm_num
  have hratio : 0 < bromideMax / bromideCritical := by
    norm_num [bromideMax, bromideCritical]
  have hcancel :
      -bromideDecayConstant *
        (log (bromideMax / bromideCritical) / bromideDecayConstant) =
        -log (bromideMax / bromideCritical) := by
    field_simp
  rw [bromideDuringSlowPhase, periodRaw, hcancel, exp_neg, exp_log hratio]
  norm_num [bromideMax, bromideCritical]

/-! ## Certified final rounding

To avoid trusting a floating-point calculation, split
`log (7000/3) = 11 log 2 + log (875/768)`.  For the second logarithm use the
atanh series with `x = 107/1643`; one term and its proved remainder already
give more accuracy than the requested 0.1 s reporting quantum.
-/

private theorem log_ratio_decomposition :
    log (7000 / 3 : ℝ) = 11 * log 2 + log (875 / 768) := by
  rw [show (7000 / 3 : ℝ) = 2 ^ 11 * (875 / 768) by norm_num,
    log_mul (by norm_num : (2 : ℝ) ^ 11 ≠ 0) (by norm_num : (875 / 768 : ℝ) ≠ 0),
    log_pow]
  norm_num

private theorem log_small_ratio_lower :
    (214 / 1643 : ℝ) ≤ log (875 / 768) := by
  have h := sum_range_le_log_div
    (x := (107 / 1643 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num at h ⊢
  linarith

private theorem log_small_ratio_upper :
    log (875 / 768) ≤
      2 * ((107 / 1643 : ℝ) +
        (107 / 1643 : ℝ) ^ 3 / (1 - (107 / 1643 : ℝ) ^ 2)) := by
  have h := log_div_le_sum_range_add
    (x := (107 / 1643 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num at h ⊢
  linarith

private theorem log_period_argument_lower :
    (121086 / 15625 : ℝ) ≤ log (7000 / 3) := by
  rw [log_ratio_decomposition]
  have htwo := Real.log_two_gt_d9
  have hsmall := log_small_ratio_lower
  norm_num at htwo hsmall ⊢
  linarith

private theorem log_period_argument_upper :
    log (7000 / 3) < (121338 / 15625 : ℝ) := by
  rw [log_ratio_decomposition]
  have htwo := Real.log_two_lt_d9
  have hsmall := log_small_ratio_upper
  norm_num at htwo hsmall ⊢
  linarith

theorem period_bounds :
    (4805 / 100 : ℝ) ≤ periodRaw ∧ periodRaw < (4815 / 100 : ℝ) := by
  rw [period_raw_exact]
  constructor
  · nlinarith [log_period_argument_lower]
  · nlinarith [log_period_argument_upper]

/-- The requested numeric output: raw value retained exactly and displayed as
48.1 s (three significant figures, quantum 0.1 s). -/
def periodSubmission : NumericSubmission where
  rawValue := periodRaw
  reportedValue := 48.1
  reportingQuantum := 0.1

theorem oscillation_period :
    ValidNumericSubmission periodRaw periodSubmission := by
  refine ⟨rfl, ?_⟩
  refine ⟨by norm_num [periodSubmission], ⟨481, by norm_num [periodSubmission]⟩, ?_⟩
  have hnonneg : 0 ≤ periodSubmission.rawValue := by
    dsimp [periodSubmission]
    exact le_trans (by norm_num) period_bounds.1
  rw [if_pos hnonneg]
  dsimp [periodSubmission]
  constructor <;> nlinarith [period_bounds.1, period_bounds.2]

#print axioms processA_reduced_balance
#print axioms hbro2_processA
#print axioms hbro2_processB
#print axioms bromide_critical
#print axioms hbro2B_is_stationary
#print axioms bromideCritical_is_switch
#print axioms bromideCritical_lt_max
#print axioms bromide_decay_constant_value
#print axioms processB_bromide_loss_rate
#print axioms bromide_slow_phase_initial
#print axioms bromide_slow_phase_rate
#print axioms period_raw_exact
#print axioms bromide_at_period
#print axioms period_bounds
#print axioms oscillation_period

end

end IChO2026Problems.T2A5
