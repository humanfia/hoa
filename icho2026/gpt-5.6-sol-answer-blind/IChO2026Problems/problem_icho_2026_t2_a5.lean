import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T2-A5: period of the Belousov--Zhabotinsky oscillation

All concentrations below are represented by real numbers in molar (`M`), time
by real numbers in seconds, and reaction rates by real numbers in `M s⁻¹`.
Consequently the printed numerical rate constants are inserted in the matching
displayed units.  This target uses the problem's approximation that the return
from the critical bromide concentration to the maximum concentration is
effectively instantaneous; the period is therefore the duration of the slow
Process-B leg.
-/

namespace IChO2026Problems.ProblemIcho2026T2A5

noncomputable section

abbrev Concentration := ℝ
abbrev MolarRate := ℝ
abbrev Seconds := ℝ

/-! ## Chemical mechanism printed in the problem -/

/-- Named chemical species occurring in the seven printed elementary steps. -/
inductive Species where
  | hBrO2
  | bromate
  | proton
  | brO2Radical
  | water
  | ceriumIII
  | ceriumIV
  | hBrO
  | bromide
  | malonicAcid
  | bromomalonicAcid
  deriving DecidableEq, Repr

/-- A species together with its positive integer stoichiometric coefficient. -/
structure StoichiometricTerm where
  species : Species
  coefficient : ℕ
  positive_coefficient : 0 < coefficient
  deriving Repr

/-- The named part of an elementary reaction from the problem statement.
`hasOtherProducts` is true only for step (7), whose source explicitly writes
"other products" without identifying or quantifying them. -/
structure ElementaryReaction where
  reactants : List StoichiometricTerm
  products : List StoichiometricTerm
  hasOtherProducts : Bool
  deriving Repr

private def stoich (species : Species) (coefficient : ℕ)
    (h : 0 < coefficient := by omega) : StoichiometricTerm :=
  { species, coefficient, positive_coefficient := h }

def reaction1 : ElementaryReaction :=
  { reactants := [stoich .hBrO2 1, stoich .bromate 1, stoich .proton 1]
    products := [stoich .brO2Radical 2, stoich .water 1]
    hasOtherProducts := false }

def reaction2 : ElementaryReaction :=
  { reactants := [stoich .brO2Radical 1, stoich .ceriumIII 1, stoich .proton 1]
    products := [stoich .hBrO2 1, stoich .ceriumIV 1]
    hasOtherProducts := false }

def reaction3 : ElementaryReaction :=
  { reactants := [stoich .hBrO2 2]
    products := [stoich .bromate 1, stoich .hBrO 1, stoich .proton 1]
    hasOtherProducts := false }

def reaction4 : ElementaryReaction :=
  { reactants := [stoich .hBrO2 1, stoich .bromide 1, stoich .proton 1]
    products := [stoich .hBrO 2]
    hasOtherProducts := false }

def reaction5 : ElementaryReaction :=
  { reactants := [stoich .bromate 1, stoich .bromide 1, stoich .proton 2]
    products := [stoich .hBrO 1, stoich .hBrO2 1]
    hasOtherProducts := false }

def reaction6 : ElementaryReaction :=
  { reactants := [stoich .hBrO 1, stoich .malonicAcid 1]
    products := [stoich .bromomalonicAcid 1, stoich .water 1]
    hasOtherProducts := false }

def reaction7 : ElementaryReaction :=
  { reactants := [stoich .ceriumIV 1, stoich .bromomalonicAcid 1]
    products := [stoich .ceriumIII 1, stoich .bromide 1]
    hasOtherProducts := true }

/-! ## Printed kinetic data and mass-action rates -/

/-- Rate constant for step (1), in `M⁻² s⁻¹`. -/
def k1 : ℝ := 10000

/-- Rate constant for step (2), in `M⁻² s⁻¹`. -/
def k2 : ℝ := 62000

/-- Rate constant for step (3), in `M⁻¹ s⁻¹`. -/
def k3 : ℝ := 40000000

/-- Rate constant for step (4), in `M⁻² s⁻¹`. -/
def k4 : ℝ := 2000000000

/-- Rate constant for step (5), in `M⁻³ s⁻¹`. -/
def k5 : ℝ := 21 / 10

/-- Rate constant for step (6), in `M⁻¹ s⁻¹`. -/
def k6 : ℝ := 82 / 10

/-- Rate constant for step (7), in `M⁻¹ s⁻¹`. -/
def k7 : ℝ := 100

/-- Maintained bromate concentration `[BrO₃⁻] = 0.06 M`. -/
def bromateConcentration : Concentration := 3 / 50

/-- Maintained malonic-acid concentration `[MA] = 0.1 M`. -/
def malonicAcidConcentration : Concentration := 1 / 10

/-- Maintained proton concentration `[H⁺] = 0.8 M`. -/
def protonConcentration : Concentration := 4 / 5

/-- Initially printed cerium(IV) concentration `[Ce⁴⁺]₀ = 0.001 M`. -/
def initialCeriumIVConcentration : Concentration := 1 / 1000

/-- Maximum bromide concentration from the phase-portrait text,
`[Br⁻]max = 7.0 × 10⁻⁴ M`. -/
def maximumBromideConcentration : Concentration := 7 / 10000

/-- Problem-stated fallback for `[HBrO₂]A`; it is recorded but not used in the
blind derivation below. -/
def fallbackStationaryHBrO2A : Concentration := 1 / 100000

/-- Problem-stated fallback for `[HBrO₂]B`; it is recorded but not used in the
blind derivation below. -/
def fallbackStationaryHBrO2B : Concentration := 1 / 10000000000

/-- Problem-stated fallback for `[Br⁻]critical`; it is recorded but not used in
the blind derivation below. -/
def fallbackCriticalBromide : Concentration := 1 / 10000000

/-- Mass-action rate of step (1). -/
def rate1 (hbrO2 : Concentration) : MolarRate :=
  k1 * hbrO2 * bromateConcentration * protonConcentration

/-- Mass-action rate of step (2). -/
def rate2 (brO2Radical ceriumIII : Concentration) : MolarRate :=
  k2 * brO2Radical * ceriumIII * protonConcentration

/-- Event rate of step (3); its HBrO₂ consumption rate is twice this value. -/
def rate3 (hbrO2 : Concentration) : MolarRate :=
  k3 * hbrO2 ^ 2

/-- Mass-action rate of step (4). -/
def rate4 (hbrO2 bromide : Concentration) : MolarRate :=
  k4 * hbrO2 * bromide * protonConcentration

/-- Mass-action rate of step (5). -/
def rate5 (bromide : Concentration) : MolarRate :=
  k5 * bromateConcentration * bromide * protonConcentration ^ 2

/-- Mass-action rate of step (6). -/
def rate6 (hbrO : Concentration) : MolarRate :=
  k6 * hbrO * malonicAcidConcentration

/-- Mass-action rate of step (7). -/
def rate7 (ceriumIV bromomalonicAcid : Concentration) : MolarRate :=
  k7 * ceriumIV * bromomalonicAcid

/-! ## Inline derivation of the two previous-part prerequisites -/

/-- Steady-state rate balances in Process A.  The first equation is the
BrO₂-radical balance and the second is the HBrO₂ balance. -/
def ProcessASteadyState
    (hbrO2 brO2Radical ceriumIII : Concentration) : Prop :=
  0 < hbrO2 ∧ 0 ≤ brO2Radical ∧ 0 ≤ ceriumIII ∧
  rate2 brO2Radical ceriumIII = 2 * rate1 hbrO2 ∧
  rate2 brO2Radical ceriumIII = rate1 hbrO2 + 2 * rate3 hbrO2

/-- Eliminating the radical turnover from the two Process-A balances gives
`r₁ = 2 r₃`. -/
def ProcessAEliminatedBalance (hbrO2 : Concentration) : Prop :=
  0 < hbrO2 ∧ rate1 hbrO2 = 2 * rate3 hbrO2

theorem processA_steadyState_eliminates
    {hbrO2 brO2Radical ceriumIII : Concentration}
    (h : ProcessASteadyState hbrO2 brO2Radical ceriumIII) :
    ProcessAEliminatedBalance hbrO2 := by
  rcases h with ⟨hh, _, _, hradical, hhbrO2⟩
  exact ⟨hh, by linarith⟩

/-- Source-derived positive stationary HBrO₂ concentration in Process A. -/
def stationaryHBrO2A : Concentration :=
  k1 * bromateConcentration * protonConcentration / (2 * k3)

theorem stationaryHBrO2A_spec :
    ProcessAEliminatedBalance stationaryHBrO2A ∧
    ∀ x : Concentration,
      ProcessAEliminatedBalance x → x = stationaryHBrO2A := by
  constructor
  · constructor
    · norm_num [stationaryHBrO2A, k1, bromateConcentration,
        protonConcentration, k3]
    · norm_num [stationaryHBrO2A, rate1, rate3, k1,
        bromateConcentration, protonConcentration, k3]
  · intro x hx
    rcases hx with ⟨hxpos, hxbal⟩
    norm_num [rate1, rate3, k1, bromateConcentration,
      protonConcentration, k3] at hxbal
    norm_num [stationaryHBrO2A, k1, bromateConcentration,
      protonConcentration, k3]
    nlinarith

theorem stationaryHBrO2A_exact :
    stationaryHBrO2A = 3 / 500000 := by
  norm_num [stationaryHBrO2A, k1, bromateConcentration,
    protonConcentration, k3]

/-- HBrO₂ steady-state balance in Process B: step (5) produces HBrO₂ and
step (4) consumes it. -/
def ProcessBSteadyState (hbrO2 bromide : Concentration) : Prop :=
  0 < hbrO2 ∧ 0 < bromide ∧ rate5 bromide = rate4 hbrO2 bromide

/-- Source-derived positive stationary HBrO₂ concentration in Process B. -/
def stationaryHBrO2B : Concentration :=
  k5 * bromateConcentration * protonConcentration / k4

theorem stationaryHBrO2B_spec :
    ProcessBSteadyState stationaryHBrO2B maximumBromideConcentration ∧
    ∀ x : Concentration,
      ProcessBSteadyState x maximumBromideConcentration →
      x = stationaryHBrO2B := by
  constructor
  · norm_num [ProcessBSteadyState, stationaryHBrO2B,
      maximumBromideConcentration, rate4, rate5, k4, k5,
      bromateConcentration, protonConcentration]
  · intro x hx
    rcases hx with ⟨_, _, hxbal⟩
    norm_num [rate4, rate5, maximumBromideConcentration, k4, k5,
      bromateConcentration, protonConcentration] at hxbal
    norm_num [stationaryHBrO2B, k5, bromateConcentration,
      protonConcentration, k4]
    linarith

theorem stationaryHBrO2B_exact :
    stationaryHBrO2B = 63 / 1250000000000 := by
  norm_num [stationaryHBrO2B, k5, bromateConcentration,
    protonConcentration, k4]

/-- Equality of the competing rates (1) and (4) at a switching boundary. -/
def SwitchBoundary (bromide : Concentration) : Prop :=
  0 < bromide ∧
  ∃ hbrO2 : Concentration,
    0 < hbrO2 ∧ rate1 hbrO2 = rate4 hbrO2 bromide

/-- Source-derived critical bromide concentration. -/
def criticalBromideConcentration : Concentration :=
  k1 * bromateConcentration / k4

theorem criticalBromideConcentration_spec :
    SwitchBoundary criticalBromideConcentration ∧
    ∀ b : Concentration,
      SwitchBoundary b → b = criticalBromideConcentration := by
  constructor
  · constructor
    · norm_num [criticalBromideConcentration, k1,
        bromateConcentration, k4]
    · refine ⟨1, by norm_num, ?_⟩
      norm_num [rate1, rate4, criticalBromideConcentration, k1,
        bromateConcentration, protonConcentration, k4]
  · intro b hb
    rcases hb with ⟨_, hbrO2, hhbrO2, hrate⟩
    norm_num [rate1, rate4, k1, bromateConcentration,
      protonConcentration, k4] at hrate
    norm_num [criticalBromideConcentration, k1,
      bromateConcentration, k4]
    nlinarith

theorem criticalBromideConcentration_exact :
    criticalBromideConcentration = 3 / 10000000 := by
  norm_num [criticalBromideConcentration, k1,
    bromateConcentration, k4]

/-- Bromide above the critical concentration selects Process B, while bromide
below it selects Process A, exactly as determined by the rate comparison in
the problem statement. -/
theorem process_selection_by_bromide
    {hbrO2 bromide : Concentration} (hh : 0 < hbrO2) :
    (criticalBromideConcentration < bromide ↔
      rate1 hbrO2 < rate4 hbrO2 bromide) ∧
    (bromide < criticalBromideConcentration ↔
      rate4 hbrO2 bromide < rate1 hbrO2) := by
  norm_num [criticalBromideConcentration, rate1, rate4, k1, k4,
    bromateConcentration, protonConcentration]
  constructor <;> constructor <;> intro h <;> nlinarith

/-! ## Slow Process-B leg and the oscillation period -/

/-- Total bromide consumption rate in Process B.  One bromide is consumed by
each occurrence of step (4) and each occurrence of step (5). -/
def bromideConsumptionRate (bromide : Concentration) : MolarRate :=
  rate4 stationaryHBrO2B bromide + rate5 bromide

/-- First-order decay coefficient for bromide during the slow Process-B leg. -/
def slowBromideDecayConstant : ℝ :=
  k4 * stationaryHBrO2B * protonConcentration +
    k5 * bromateConcentration * protonConcentration ^ 2

theorem processB_equal_bromide_consumption_rates
    (bromide : Concentration) :
    rate4 stationaryHBrO2B bromide = rate5 bromide := by
  norm_num [rate4, rate5, stationaryHBrO2B, k4, k5,
    bromateConcentration, protonConcentration]
  ring

theorem slowBromideDecayConstant_exact :
    slowBromideDecayConstant = 504 / 3125 := by
  norm_num [slowBromideDecayConstant, stationaryHBrO2B, k4, k5,
    bromateConcentration, protonConcentration]

theorem bromideConsumptionRate_linear (bromide : Concentration) :
    bromideConsumptionRate bromide = slowBromideDecayConstant * bromide := by
  norm_num [bromideConsumptionRate, slowBromideDecayConstant, rate4,
    rate5, stationaryHBrO2B, k4, k5, bromateConcentration,
    protonConcentration]
  ring

/-- Exact concentration trajectory under the source's slow-leg approximation. -/
def bromideSlowTrajectory (t : Seconds) : Concentration :=
  maximumBromideConcentration * Real.exp (-slowBromideDecayConstant * t)

theorem bromideSlowTrajectory_initial :
    bromideSlowTrajectory 0 = maximumBromideConcentration := by
  simp [bromideSlowTrajectory]

/-- The trajectory obeys the bromide material-rate balance from steps (4) and
(5); the omitted rapid reset is not part of this slow-leg differential law. -/
theorem bromideSlowTrajectory_rate_law (t : Seconds) :
    HasDerivAt bromideSlowTrajectory
      (-bromideConsumptionRate (bromideSlowTrajectory t)) t := by
  rw [bromideConsumptionRate_linear]
  unfold bromideSlowTrajectory
  have h : HasDerivAt
      (fun y : ℝ => maximumBromideConcentration *
        Real.exp (-slowBromideDecayConstant * y))
      (maximumBromideConcentration *
        (Real.exp (-slowBromideDecayConstant * t) *
          (-slowBromideDecayConstant))) t :=
    (hasDerivAt_const_mul (-slowBromideDecayConstant)).exp.const_mul
      maximumBromideConcentration
  exact h.congr_deriv (by ring)

/-- A positive time is the slow-leg period precisely when it is the first time
at which the exponentially decaying bromide trajectory reaches the critical
concentration.  The logarithmic equality exposes the unrounded governing
relation used to obtain that time. -/
def OscillationPeriodDerivation (tau : Seconds) : Prop :=
  0 < tau ∧
  slowBromideDecayConstant * tau =
    Real.log (maximumBromideConcentration / criticalBromideConcentration) ∧
  bromideSlowTrajectory tau = criticalBromideConcentration ∧
  ∀ t : Seconds,
    0 ≤ t → t < tau →
      criticalBromideConcentration < bromideSlowTrajectory t

/-- Unrounded period, in seconds, derived end-to-end from the printed kinetic
constants and concentration thresholds. -/
def oscillationPeriodRaw : Seconds :=
  Real.log (maximumBromideConcentration / criticalBromideConcentration) /
    slowBromideDecayConstant

theorem oscillationPeriodRaw_exact_expression :
    oscillationPeriodRaw =
      (3125 / 504 : ℝ) * Real.log (7000 / 3) := by
  rw [oscillationPeriodRaw, maximumBromideConcentration,
    criticalBromideConcentration_exact, slowBromideDecayConstant_exact]
  norm_num
  ring

/-- Rational bounds for the only transcendental quantity in the raw period.
They are certified from the positive-term series for
`log ((1 + x) / (1 - x))`, after splitting
`7000 / 3 = 2^11 * (875 / 768)`. -/
private theorem oscillationLog_bounds :
    (12021 / 250 : ℝ) * (504 / 3125) < Real.log (7000 / 3) ∧
    Real.log (7000 / 3) < (9617 / 200 : ℝ) * (504 / 3125) := by
  have h2Lower := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 6
  have h2Upper := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 6
  have hRatioLower := Real.sum_range_le_log_div
    (x := (107 / 1643 : ℝ)) (by norm_num) (by norm_num) 2
  have hRatioUpper := Real.log_div_le_sum_range_add
    (x := (107 / 1643 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2Lower h2Upper hRatioLower hRatioUpper
  have hdecomp :
      Real.log (7000 / 3) =
        11 * Real.log 2 + Real.log (875 / 768) := by
    calc
      Real.log (7000 / 3) =
          Real.log ((2 : ℝ) ^ 11 * (875 / 768)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 11) + Real.log (875 / 768) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 11 * Real.log 2 + Real.log (875 / 768) := by
        rw [Real.log_pow]
        norm_num
  rw [hdecomp]
  constructor <;> nlinarith

/-- Raw result contract: the exact expression is the first hitting time and is
certified in a non-degenerate rational interval without equating it to a finite
decimal. -/
theorem oscillationPeriodRaw_spec :
    OscillationPeriodDerivation oscillationPeriodRaw ∧
    (12021 / 250 : ℝ) < oscillationPeriodRaw ∧
    oscillationPeriodRaw < (9617 / 200 : ℝ) := by
  have hc : 0 < slowBromideDecayConstant := by
    rw [slowBromideDecayConstant_exact]
    norm_num
  have hmax : 0 < maximumBromideConcentration := by
    norm_num [maximumBromideConcentration]
  have hcritical : 0 < criticalBromideConcentration := by
    rw [criticalBromideConcentration_exact]
    norm_num
  have hratio :
      maximumBromideConcentration / criticalBromideConcentration =
        (7000 / 3 : ℝ) := by
    rw [maximumBromideConcentration, criticalBromideConcentration_exact]
    norm_num
  have hratioOne :
      1 < maximumBromideConcentration / criticalBromideConcentration := by
    rw [hratio]
    norm_num
  have hlog :
      0 < Real.log
        (maximumBromideConcentration / criticalBromideConcentration) :=
    Real.log_pos hratioOne
  have htau : 0 < oscillationPeriodRaw := by
    rw [oscillationPeriodRaw]
    exact div_pos hlog hc
  have hbalance :
      slowBromideDecayConstant * oscillationPeriodRaw =
        Real.log
          (maximumBromideConcentration / criticalBromideConcentration) := by
    rw [oscillationPeriodRaw]
    field_simp [hc.ne']
  have hend :
      bromideSlowTrajectory oscillationPeriodRaw =
        criticalBromideConcentration := by
    rw [bromideSlowTrajectory]
    have hexponent :
        -slowBromideDecayConstant * oscillationPeriodRaw =
          -Real.log
            (maximumBromideConcentration /
              criticalBromideConcentration) := by
      linarith
    rw [hexponent, Real.exp_neg,
      Real.exp_log (div_pos hmax hcritical)]
    field_simp [hmax.ne', hcritical.ne']
  constructor
  · refine ⟨htau, hbalance, hend, ?_⟩
    intro t _ ht
    calc
      criticalBromideConcentration =
          bromideSlowTrajectory oscillationPeriodRaw := hend.symm
      _ < bromideSlowTrajectory t := by
        unfold bromideSlowTrajectory
        apply mul_lt_mul_of_pos_left _ hmax
        apply Real.exp_lt_exp.mpr
        nlinarith
  · rw [oscillationPeriodRaw_exact_expression]
    rcases oscillationLog_bounds with ⟨hlower, hupper⟩
    constructor <;> nlinarith

/-- Three-significant-figure display selected by the source report's uniform
answer-blind reporting policy. -/
def oscillationPeriodReported : Seconds := 481 / 10

/-- At magnitude `48.1`, three significant figures have quantum `0.1 s`. -/
def oscillationPeriodReportingQuantum : Seconds := 1 / 10

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"oscillation_period","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"48.1","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.ProblemIcho2026T2A5.oscillationPeriodRaw","reporting_declaration":"IChO2026Problems.ProblemIcho2026T2A5.oscillationPeriod_reported"}
theorem oscillationPeriod_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      oscillationPeriodRaw oscillationPeriodReported
      oscillationPeriodReportingQuantum := by
  refine ⟨by norm_num [oscillationPeriodReportingQuantum], ?_, ?_⟩
  · refine ⟨481, ?_⟩
    norm_num [oscillationPeriodReported, oscillationPeriodReportingQuantum]
  · rw [if_pos (le_of_lt oscillationPeriodRaw_spec.1.1)]
    rcases oscillationPeriodRaw_spec.2 with ⟨hlower, hupper⟩
    constructor
    · norm_num [oscillationPeriodReported,
        oscillationPeriodReportingQuantum]
      linarith
    · norm_num [oscillationPeriodReported,
        oscillationPeriodReportingQuantum]
      linarith

end

end IChO2026Problems.ProblemIcho2026T2A5
