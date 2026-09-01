import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T2, part A5 (printed item 2.5): period of oscillations τ
of the Belousov–Zhabotinsky reaction

## Source contract (answer-blind; problem-only inputs)

* Source images inspected:
  * `icho_2026_source/image/T2_page-2.png` — the mechanism table: Process A,
    steps (1) `HBrO₂ + BrO₃⁻ + H⁺ → 2BrO₂• + H₂O`, `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`;
    (2) `BrO₂• + Ce³⁺ + H⁺ → HBrO₂ + Ce⁴⁺`, `k₂ = 6.2 × 10⁴ M⁻² s⁻¹`;
    (3) `2HBrO₂ → BrO₃⁻ + HBrO + H⁺`, `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹`;
    Process B, steps (4) `HBrO₂ + Br⁻ + H⁺ → 2HBrO`, `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`;
    (5) `BrO₃⁻ + Br⁻ + 2H⁺ → HBrO + HBrO₂`, `k₅ = 2.1 M⁻³ s⁻¹`;
    (6) `HBrO + MA → BMA + H₂O`, `k₆ = 8.2 M⁻¹ s⁻¹`;
    Process C, step (7) `Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products`,
    `k₇ = 1.0 × 10² M⁻¹ s⁻¹`; the alternating-process stipulation and the
    buffered concentrations `[BrO₃⁻]₀ = 0.06 M`, `[MA]₀ = 0.1 M`,
    `[H⁺]₀ = 0.8 M`, `[Ce⁴⁺]₀ = 0.001 M`; item 2.2 with its printed fallbacks
    `[HBrO₂]A = 1 × 10⁻⁵ M`, `[HBrO₂]B = 1 × 10⁻¹⁰ M`.
  * `icho_2026_source/image/T2_page-3.png` — the phase portrait of `[HBrO₂]`
    vs `[Br⁻]`; the switch-over rule ("to switch Process A to Process B, the
    reaction rate of the elementary step (4) must exceed that of the
    elementary step (1) and vice versa"); item 2.3 with its printed fallback
    `[Br⁻]critical = 1 × 10⁻⁷ M`; the slow-leg stipulation "the concentration
    of `[Br⁻]` slowly decreases from `[Br⁻]max = 7.0 × 10⁻⁴ M` to
    `[Br⁻]critical`, and then almost immediately reaches `[Br⁻]max` again";
    and item 2.5: "Calculate based on the data the period of oscillations, τ,
    of the BZ reaction, in seconds."

## Assumption / target split

**Assumptions (all problem-stipulated).** The mass-action rate laws of the
mechanism table, in particular `r₁ = k₁[HBrO₂][BrO₃⁻][H⁺]`,
`r₄ = k₄[HBrO₂][Br⁻][H⁺]`, `r₅ = k₅[BrO₃⁻][Br⁻][H⁺]²`; the buffered
concentrations `[BrO₃⁻] = 0.06 M` and `[H⁺] = 0.8 M`; the stipulation
`[Br⁻]max = 7.0 × 10⁻⁴ M`; the alternation of Processes A and B with the
switch-over at `[Br⁻]critical`; and the statement that the recovery leg is
almost immediate, so the period equals the duration of the slow leg.

**Previous parts, derived inline** (dependency policy
`derive_in_answer_blind_run_or_use_problem_stated_fallback`; no printed
fallback is used anywhere in this file):

* T2-A3 (switch-over balance `r₄ = r₁`): `[Br⁻]critical = k₁[BrO₃⁻]/k₄
  = 3/10⁷ mol dm⁻³` (`bromideCriticalRaw`, `critical_isCritical`).
* T2-A2 (Process-B steady state for HBrO₂, `−r₄ + r₅ = 0`): `r₄ = r₅`, i.e.
  `[HBrO₂]B = k₅[BrO₃⁻][H⁺]/k₄ = 504/10¹³ mol dm⁻³` (`stationaryHBrO2_B`,
  `stationaryB_isStationary`).

**Target.** The period of oscillations `τ` in seconds, raw and reported to
three significant figures (the `final_precision` of the source reporting
policy; ties half away from zero).

## Derivation carried by the Lean declarations

During the slow leg `[Br⁻] > [Br⁻]critical`, so `r₄ > r₁` and Process B runs
while Process A practically does not occur. Within Process B, bromide is
consumed by steps (4) and (5) only; the Process-B steady state `r₄ = r₅` then
gives the bromide ledger

`−d[Br⁻]/dt = r₄ + r₅ = 2 r₅ = (2 k₅ [BrO₃⁻][H⁺]²)·[Br⁻]`,

a first-order decay with coefficient `k' = 2 k₅ [BrO₃⁻][H⁺]² = 504/3125 s⁻¹
= 0.16128 s⁻¹` (`bromideConsumptionRate`, `bromideDecayCoefficient`,
`bromideSlowLeg_ode`). Hence `[Br⁻](t) = [Br⁻]max·exp(−k' t)`
(`bromideSlowLeg`), and the slow leg ends when `[Br⁻]` reaches
`[Br⁻]critical` (`slowLeg_hits_critical`, `slowLeg_time_unique`), i.e.

`τ = ln([Br⁻]max/[Br⁻]critical)/k' = ln(7000/3) / (504/3125) = 48.0844… s`.

Reported to three significant figures: **48.1 s** (quantum `0.1 s`; the raw
value lies in the half-quantum cell `[48.05, 48.15)`).
-/

namespace IChO2026Problems.ProblemIcho2026T2A5

/-! ## Problem-stipulated constants (exact as printed, mechanism table on
`T2_page-2.png`; `[Br⁻]max` from `T2_page-3.png`) -/

/-- Rate constant of elementary step (1), `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`. -/
def k1 : ℝ := 1.0e4

/-- Rate constant of elementary step (2), `k₂ = 6.2 × 10⁴ M⁻² s⁻¹`
(listed for completeness; not used in part 2.5). -/
def k2 : ℝ := 6.2e4

/-- Rate constant of elementary step (3), `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹`
(listed for completeness; not used in part 2.5). -/
def k3 : ℝ := 4.0e7

/-- Rate constant of elementary step (4), `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`. -/
def k4 : ℝ := 2.0e9

/-- Rate constant of elementary step (5), `k₅ = 2.1 M⁻³ s⁻¹`. -/
def k5 : ℝ := 2.1

/-- Rate constant of elementary step (6), `k₆ = 8.2 M⁻¹ s⁻¹`
(listed for completeness; not used in part 2.5). -/
def k6 : ℝ := 8.2

/-- Rate constant of elementary step (7), `k₇ = 1.0 × 10² M⁻¹ s⁻¹`
(listed for completeness; not used in part 2.5). -/
def k7 : ℝ := 1.0e2

/-- Buffered bromate concentration `[BrO₃⁻] = 0.06 mol dm⁻³`. -/
def bromateConc : ℝ := 0.06

/-- Buffered proton concentration `[H⁺] = 0.8 mol dm⁻³` (constant pH). -/
def protonConc : ℝ := 0.8

/-- Buffered malonic acid concentration `[MA] = 0.1 mol dm⁻³`
(not used in part 2.5). -/
def maConc : ℝ := 0.1

/-- Initial cerium(IV) concentration `[Ce⁴⁺]₀ = 0.001 mol dm⁻³`
(initial data only; not used in part 2.5). -/
def ce4InitConc : ℝ := 0.001

/-- Maximum bromide concentration of the oscillation cycle,
`[Br⁻]max = 7.0 × 10⁻⁴ mol dm⁻³` (problem-stipulated, `T2_page-3.png`). -/
def bromideMax : ℝ := 7.0e-4

/-! ## Mass-action rate laws of the elementary steps entering the derivation -/

/-- Rate of elementary step (1): `r₁ = k₁[HBrO₂][BrO₃⁻][H⁺]`. -/
def rateStep1 (hbrO2 brO3 h : ℝ) : ℝ :=
  k1 * hbrO2 * brO3 * h

/-- Rate of elementary step (4): `r₄ = k₄[HBrO₂][Br⁻][H⁺]`. -/
def rateStep4 (hbrO2 br h : ℝ) : ℝ :=
  k4 * hbrO2 * br * h

/-- Rate of elementary step (5): `r₅ = k₅[BrO₃⁻][Br⁻][H⁺]²`. -/
def rateStep5 (brO3 br h : ℝ) : ℝ :=
  k5 * brO3 * br * h ^ 2

/-! ## Previous parts derived inline (no printed fallback is used) -/

/-- T2-A3, derived inline: the critical bromide concentration is the balance
point `r₄ = r₁` of the switch-over rule, `[Br⁻]critical = k₁[BrO₃⁻]/k₄`. -/
noncomputable def bromideCriticalRaw : ℝ :=
  k1 * bromateConc / k4

/-- T2-A2, derived inline: the stationary HBrO₂ concentration of Process B
from the steady state `−r₄ + r₅ = 0`, `[HBrO₂]B = k₅[BrO₃⁻][H⁺]/k₄`. -/
noncomputable def stationaryHBrO2_B : ℝ :=
  k5 * bromateConc * protonConc / k4

/-- Switch-over predicate: at `[Br⁻]critical` the rates of steps (4) and (1)
coincide at every positive HBrO₂ level (both steps are first order in HBrO₂,
so the common factors cancel). -/
def IsCriticalBromide (br : ℝ) : Prop :=
  ∀ hbrO2 : ℝ, 0 < hbrO2 →
    rateStep4 hbrO2 br protonConc = rateStep1 hbrO2 bromateConc protonConc

/-- Process-B steady-state predicate: production of HBrO₂ by step (5) balances
its consumption by step (4) at every positive bromide level. -/
def IsProcessBStationary (hbrO2 : ℝ) : Prop :=
  ∀ br : ℝ, 0 < br →
    rateStep4 hbrO2 br protonConc = rateStep5 bromateConc br protonConc

/-- Exact raw value of `[Br⁻]critical`: `k₁[BrO₃⁻]/k₄ = 3/10⁷ mol dm⁻³`. -/
theorem bromideCriticalRaw_exact : bromideCriticalRaw = (3 : ℝ) / 10 ^ 7 := by
  norm_num [bromideCriticalRaw, k1, k4, bromateConc]

/-- Exact raw value of `[HBrO₂]B`: `k₅[BrO₃⁻][H⁺]/k₄ = 504/10¹³ mol dm⁻³`. -/
theorem stationaryHBrO2_B_exact : stationaryHBrO2_B = (504 : ℝ) / 10 ^ 13 := by
  norm_num [stationaryHBrO2_B, k4, k5, bromateConc, protonConc]

theorem bromideCriticalRaw_pos : 0 < bromideCriticalRaw := by
  norm_num [bromideCriticalRaw, k1, k4, bromateConc]

theorem bromideMax_pos : 0 < bromideMax := by
  norm_num [bromideMax]

theorem bromideCriticalRaw_lt_max : bromideCriticalRaw < bromideMax := by
  norm_num [bromideCriticalRaw, bromideMax, k1, k4, bromateConc]

/-- The balance identity behind `[Br⁻]critical`:
`k₄·[Br⁻]critical = k₁[BrO₃⁻]`. -/
theorem critical_balance : k4 * bromideCriticalRaw = k1 * bromateConc := by
  norm_num [bromideCriticalRaw, k1, k4, bromateConc]

theorem critical_isCritical : IsCriticalBromide bromideCriticalRaw := by
  intro x _
  change k4 * x * bromideCriticalRaw * protonConc
    = k1 * x * bromateConc * protonConc
  linear_combination x * protonConc * critical_balance

/-- The balance identity behind `[HBrO₂]B`: `k₄[HBrO₂]B = k₅[BrO₃⁻][H⁺]`. -/
theorem stationaryB_balance :
    k4 * stationaryHBrO2_B = k5 * bromateConc * protonConc := by
  norm_num [stationaryHBrO2_B, k4, k5, bromateConc, protonConc]

theorem stationaryB_isStationary : IsProcessBStationary stationaryHBrO2_B := by
  intro br _
  change k4 * stationaryHBrO2_B * br * protonConc
    = k5 * bromateConc * br * protonConc ^ 2
  linear_combination br * protonConc * stationaryB_balance

/-! ## Slow-leg bromide kinetics -/

/-- Net bromide consumption rate during the slow Process-B leg: bromide is
consumed by steps (4) and (5), and the Process-B steady state `r₄ = r₅`
forces the total to `r₄ + r₅ = 2 r₅`. -/
def bromideConsumptionRate (br : ℝ) : ℝ :=
  2 * rateStep5 bromateConc br protonConc

/-- Pseudo-first-order decay coefficient of the slow leg,
`k' = 2 k₅ [BrO₃⁻][H⁺]²`, in `s⁻¹`. -/
def bromideDecayCoefficient : ℝ :=
  2 * k5 * bromateConc * protonConc ^ 2

/-- The consumption rate is pseudo-first-order in `[Br⁻]`:
`r₄ + r₅ = k'·[Br⁻]`. -/
theorem consumptionRate_eq (br : ℝ) :
    bromideConsumptionRate br = bromideDecayCoefficient * br := by
  unfold bromideConsumptionRate bromideDecayCoefficient rateStep5
  ring

/-- Exact value of the decay coefficient:
`2 · 2.1 · 0.06 · 0.8² = 504/3125 = 0.16128 s⁻¹`. -/
theorem bromideDecayCoefficient_exact :
    bromideDecayCoefficient = (504 : ℝ) / 3125 := by
  norm_num [bromideDecayCoefficient, k5, bromateConc, protonConc]

theorem bromideDecayCoefficient_pos : 0 < bromideDecayCoefficient := by
  norm_num [bromideDecayCoefficient, k5, bromateConc, protonConc]

/-- First-order decay trajectory of `[Br⁻]` during the slow leg: the solution
of `d[Br⁻]/dt = −k'·[Br⁻]` with `[Br⁻](0) = [Br⁻]max`. -/
noncomputable def bromideSlowLeg (t : ℝ) : ℝ :=
  bromideMax * Real.exp (-bromideDecayCoefficient * t)

/-- The slow leg starts at `[Br⁻]max`. -/
theorem bromideSlowLeg_zero : bromideSlowLeg 0 = bromideMax := by
  simp [bromideSlowLeg]

/-- The trajectory indeed solves the slow-leg kinetic equation
`d[Br⁻]/dt = −(r₄ + r₅) = −k'·[Br⁻]`. -/
theorem bromideSlowLeg_ode (t : ℝ) :
    HasDerivAt bromideSlowLeg (-bromideConsumptionRate (bromideSlowLeg t)) t := by
  have h :=
    (((hasDerivAt_id t).const_mul (-bromideDecayCoefficient)).exp).const_mul bromideMax
  have e : -bromideConsumptionRate (bromideSlowLeg t)
      = bromideMax * (Real.exp (-bromideDecayCoefficient * t)
        * (-bromideDecayCoefficient * 1)) := by
    rw [consumptionRate_eq]
    unfold bromideSlowLeg
    ring
  rw [e]
  exact h

/-- Raw oscillation period: the duration of the slow leg, i.e. the time at
which the decay trajectory reaches `[Br⁻]critical`; the recovery leg back to
`[Br⁻]max` is stipulated to be almost immediate. -/
noncomputable def oscillationPeriodRaw : ℝ :=
  Real.log (bromideMax / bromideCriticalRaw) / bromideDecayCoefficient

/-- The ratio entering the period: `[Br⁻]max/[Br⁻]critical = 7000/3`. -/
theorem bromideRatio_exact :
    bromideMax / bromideCriticalRaw = (7000 : ℝ) / 3 := by
  norm_num [bromideMax, bromideCriticalRaw, k1, k4, bromateConc]

/-- Exact closed form of the raw period:
`τ = ln(7000/3) / (504/3125) s = 48.0844… s`. -/
theorem oscillationPeriodRaw_exact :
    oscillationPeriodRaw = Real.log ((7000 : ℝ) / 3) / ((504 : ℝ) / 3125) := by
  unfold oscillationPeriodRaw
  rw [bromideRatio_exact, bromideDecayCoefficient_exact]

/-- At `t = τ` the slow-leg trajectory has decayed exactly to
`[Br⁻]critical`. -/
theorem slowLeg_hits_critical :
    bromideSlowLeg oscillationPeriodRaw = bromideCriticalRaw := by
  have hc := bromideCriticalRaw_pos
  have hmne : bromideMax ≠ 0 := ne_of_gt bromideMax_pos
  have hkne : bromideDecayCoefficient ≠ 0 := ne_of_gt bromideDecayCoefficient_pos
  have hpos : (0 : ℝ) < bromideMax / bromideCriticalRaw := div_pos bromideMax_pos hc
  have e : -bromideDecayCoefficient * oscillationPeriodRaw
      = -Real.log (bromideMax / bromideCriticalRaw) := by
    unfold oscillationPeriodRaw
    rw [neg_mul, mul_div_assoc', mul_div_cancel_left₀ _ hkne]
  unfold bromideSlowLeg
  rw [e, Real.exp_neg, Real.exp_log hpos, inv_div, mul_div_assoc',
    mul_div_cancel_left₀ _ hmne]

/-- The slow-leg hitting time is unique (the decay is strictly monotone), so
`τ` is *the* time at which `[Br⁻]` reaches `[Br⁻]critical`. -/
theorem slowLeg_time_unique (t : ℝ) (h : bromideSlowLeg t = bromideCriticalRaw) :
    t = oscillationPeriodRaw := by
  have hmne : bromideMax ≠ 0 := ne_of_gt bromideMax_pos
  have hkne : bromideDecayCoefficient ≠ 0 := ne_of_gt bromideDecayCoefficient_pos
  have h2 := slowLeg_hits_critical
  rw [← h2] at h
  unfold bromideSlowLeg at h
  have h3 := mul_left_cancel₀ hmne h
  have h4 := Real.exp_injective h3
  exact mul_left_cancel₀ (neg_ne_zero.mpr hkne) h4

theorem oscillationPeriodRaw_pos : 0 < oscillationPeriodRaw := by
  have h1 : (1 : ℝ) < bromideMax / bromideCriticalRaw := by
    rw [lt_div_iff₀ bromideCriticalRaw_pos, one_mul]
    exact bromideCriticalRaw_lt_max
  exact div_pos (Real.log_pos h1) bromideDecayCoefficient_pos

/-! ### Transcendental bounds on `ln(7000/3)`

The two remaining estimates `7.749504 ≤ ln(7000/3) ≤ 7.765632` are reduced to
exact integer comparisons via monotonicity of `Real.log` and the certified
nine-digit bounds `0.6931471803 < ln 2 < 0.6931471808`:

* lower: `2^179 < (7000/3)^16` gives
  `ln(7000/3) > (179/16)·0.6931471803 = 7.7545840… > 7.749504`;
* upper: `(7000/3)^5 < 2^56` gives
  `ln(7000/3) < (56/5)·0.6931471808 = 7.7632484… < 7.765632`. -/

/-- Rational-power comparison behind the lower bound on `ln(7000/3)`:
`2^179 < (7000/3)^16`, i.e. `2^179 · 3^16 < 7000^16` (exact integer check). -/
theorem two_pow_179_lt_ratio_pow_16 :
    (2 : ℝ) ^ 179 < ((7000 : ℝ) / 3) ^ 16 := by
  rw [div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ 16)]
  norm_num

/-- Rational-power comparison behind the upper bound on `ln(7000/3)`:
`(7000/3)^5 < 2^56`, i.e. `7000^5 < 2^56 · 3^5` (exact integer check). -/
theorem ratio_pow_5_lt_two_pow_56 :
    ((7000 : ℝ) / 3) ^ 5 < (2 : ℝ) ^ 56 := by
  rw [div_pow, div_lt_iff₀ (by positivity : (0 : ℝ) < 3 ^ 5)]
  norm_num

/-- Lower bound on the log-ratio entering the period:
`961/20 · k' = 7.749504 < ln(7000/3)`. -/
theorem log_bromideRatio_lower :
    (961 : ℝ) / 20 * bromideDecayCoefficient
      < Real.log (bromideMax / bromideCriticalRaw) := by
  rw [bromideDecayCoefficient_exact, bromideRatio_exact]
  have hlog : Real.log ((2 : ℝ) ^ 179) < Real.log (((7000 : ℝ) / 3) ^ 16) :=
    Real.log_lt_log (by positivity) two_pow_179_lt_ratio_pow_16
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have h2 := Real.log_two_gt_d9
  -- `179 * ln 2 < 16 * ln(7000/3)` and `0.6931471803 < ln 2` give
  -- `16 * ln(7000/3) > 179 * 0.6931471803 = 124.0733…`, hence
  -- `ln(7000/3) > 7.7545840… > 7.749504 = 961/20 * (504/3125)`.
  linarith

/-- Upper bound on the log-ratio entering the period:
`ln(7000/3) < 963/20 · k' = 7.765632`. -/
theorem log_bromideRatio_upper :
    Real.log (bromideMax / bromideCriticalRaw)
      < (963 : ℝ) / 20 * bromideDecayCoefficient := by
  rw [bromideDecayCoefficient_exact, bromideRatio_exact]
  have hlog : Real.log (((7000 : ℝ) / 3) ^ 5) < Real.log ((2 : ℝ) ^ 56) :=
    Real.log_lt_log (by positivity) ratio_pow_5_lt_two_pow_56
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have h2 := Real.log_two_lt_d9
  -- `5 * ln(7000/3) < 56 * ln 2` and `ln 2 < 0.6931471808` give
  -- `5 * ln(7000/3) < 56 * 0.6931471808 = 38.81624…`, hence
  -- `ln(7000/3) < 7.7632484… < 7.765632 = 963/20 * (504/3125)`.
  linarith

/-! ## Derivation specification and answer-blind result contracts -/

/-- Raw derivation specification for the period of oscillations: the inline
previous-part derivations hold (`[Br⁻]critical` is the switch-over balance
point, `[HBrO₂]B` is the Process-B steady state), the slow-leg trajectory is
the first-order decay driven by the bromide consumption rate `r₄ + r₅ = 2 r₅`,
it starts at `[Br⁻]max`, reaches `[Br⁻]critical` exactly at `τ`, that hitting
time is unique, and the raw period has the exact closed form
`ln(7000/3) / (504/3125) s`. -/
def oscillationPeriodRawSpec : Prop :=
  0 < bromideCriticalRaw ∧ bromideCriticalRaw < bromideMax ∧
    IsCriticalBromide bromideCriticalRaw ∧
      IsProcessBStationary stationaryHBrO2_B ∧
        (∀ br : ℝ, bromideConsumptionRate br = bromideDecayCoefficient * br) ∧
          (∀ t : ℝ,
            HasDerivAt bromideSlowLeg (-bromideConsumptionRate (bromideSlowLeg t)) t) ∧
            bromideSlowLeg 0 = bromideMax ∧
              bromideSlowLeg oscillationPeriodRaw = bromideCriticalRaw ∧
                (∀ t : ℝ, bromideSlowLeg t = bromideCriticalRaw →
                  t = oscillationPeriodRaw) ∧
                  oscillationPeriodRaw
                    = Real.log ((7000 : ℝ) / 3) / ((504 : ℝ) / 3125) ∧
                    0 < oscillationPeriodRaw

/-- **Raw result contract** (answer-blind certificate): the end-to-end derived
period satisfies the derivation specification and lies in the certified
interval `[48.05, 48.15] s`, the reporting half-cell of the
three-significant-figure quantum `0.1 s` around the reported value `48.1 s`.
The only non-algebraic obligations are the certified transcendental bounds
`7.749504 ≤ ln(7000/3) ≤ 7.765632`, isolated after the division inequality is
cleared. -/
theorem oscillationPeriodRawResult :
    oscillationPeriodRawSpec ∧
      ((961 : ℝ) / 20) ≤ oscillationPeriodRaw ∧
        oscillationPeriodRaw ≤ ((963 : ℝ) / 20) := by
  refine ⟨⟨bromideCriticalRaw_pos, bromideCriticalRaw_lt_max, critical_isCritical,
      stationaryB_isStationary, consumptionRate_eq, bromideSlowLeg_ode,
      bromideSlowLeg_zero, slowLeg_hits_critical, slowLeg_time_unique,
      oscillationPeriodRaw_exact, oscillationPeriodRaw_pos⟩, ?_, ?_⟩
  · -- `(961/20) ≤ τ ⟺ (961/20)·k' ≤ ln(7000/3)`, i.e. `7.749504 ≤ ln(7000/3)`.
    unfold oscillationPeriodRaw
    rw [le_div_iff₀ bromideDecayCoefficient_pos]
    exact log_bromideRatio_lower.le
  · -- `τ ≤ (963/20) ⟺ ln(7000/3) ≤ (963/20)·k'`, i.e. `ln(7000/3) ≤ 7.765632`.
    unfold oscillationPeriodRaw
    rw [div_le_iff₀ bromideDecayCoefficient_pos]
    exact log_bromideRatio_upper.le

/-- **Reported result contract**: the raw period, reported at three
significant figures (quantum `0.1 s`, ties half away from zero), is
`48.1 s`; the raw value lies in the half-quantum cell `[48.05, 48.15)`. -/
theorem oscillationPeriodReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum oscillationPeriodRaw ((481 : ℝ) / 10)
      ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨481, by norm_num⟩, ?_⟩
  rw [if_pos (le_of_lt oscillationPeriodRaw_pos)]
  constructor
  · -- lower cell boundary: `48.1 − 0.05 = 48.05 ≤ τ`
    have h1 : ((481 : ℝ) / 10) - ((1 : ℝ) / 10) / 2 = (961 : ℝ) / 20 := by norm_num
    rw [h1]
    unfold oscillationPeriodRaw
    rw [le_div_iff₀ bromideDecayCoefficient_pos]
    exact log_bromideRatio_lower.le
  · -- upper cell boundary: `τ < 48.1 + 0.05 = 48.15`
    have h2 : ((481 : ℝ) / 10) + ((1 : ℝ) / 10) / 2 = (963 : ℝ) / 20 := by norm_num
    rw [h2]
    unfold oscillationPeriodRaw
    rw [div_lt_iff₀ bromideDecayCoefficient_pos]
    exact log_bromideRatio_upper

end IChO2026Problems.ProblemIcho2026T2A5
