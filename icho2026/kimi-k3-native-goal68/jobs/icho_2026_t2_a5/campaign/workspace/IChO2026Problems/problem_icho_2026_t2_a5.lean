import Mathlib
import IChO2026Chem
import IChO2026Chem.Reporting

/-!
# IChO 2026 — Problem T2, subquestion 2.5 (target `icho_2026_t2_a5`)

**Question.** "Calculate based on the data the period of oscillations, τ, of
the BZ reaction, in seconds." (9 pt, theory paper T2, page Q2-3.)

## Problem inputs used (all printed on pages Q2-1 … Q2-3)

Rate constants (page Q2-2):

* `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`    step (1): HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂· + H₂O
* `k₂ = 6.2 × 10⁴ M⁻² s⁻¹`    step (2): BrO₂· + Ce³⁺ + H⁺ → HBrO₂ + Ce⁴⁺
* `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹`    step (3): 2 HBrO₂ → BrO₃⁻ + HBrO + H⁺
* `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`    step (4): HBrO₂ + Br⁻ + H⁺ → 2 HBrO
* `k₅ = 2.1 M⁻³ s⁻¹`          step (5): BrO₃⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO₂
* `k₆ = 8.2 M⁻¹ s⁻¹`          step (6): HBrO + MA → BMA + H₂O
* `k₇ = 1.0 × 10² M⁻¹ s⁻¹`    step (7): Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products

Maintained/initial concentrations (page Q2-2):
`[BrO₃⁻]₀ = 0.06 M`, `[MA]₀ = 0.1 M`, `[H⁺]₀ = 0.8 M`, `[Ce⁴⁺]₀ = 0.001 M`;
"the concentrations of the reactants (except Ce⁴⁺) and pH are maintained
constant throughout the BZ reaction"; when Process A occurs the solution is
yellow and Process B practically does not occur; when Process B occurs the
solution is colourless and Process A practically does not occur.

Page Q2-3 additionally stipulates `[Br⁻]max = 7.0 × 10⁻⁴ M` and that the
system "does not traverse the phase portrait at a constant velocity, that is
the concentration of [Br⁻] slowly decreases from [Br⁻]max to [Br⁻]critical,
and then almost immediately reaches [Br⁻]max again".  The period therefore
equals the duration of the slow descent.

## Derivation formalized below (all steps independent)

1. **Switching condition (2.3).** The switch over occurs when the rate of
   step (4) equals that of step (1);
   `k₄·[HBrO₂]·[Br⁻]crit·[H⁺] = k₁·[HBrO₂]·[BrO₃⁻]·[H⁺]`, giving
   `[Br⁻]crit = k₁[BrO₃⁻]/k₄ = 3.0 × 10⁻⁷ M`.

2. **Steady states (2.2).**
   Process A: `k₁[BrO₃⁻][H⁺] = k₃·[HBrO₂]A` gives `[HBrO₂]A = 1.2×10⁻⁵ M`;
   Process B: production of HBrO₂ at the rate of step (5),
   `k₅[BrO₃⁻][Br⁻][H⁺]²`, balances consumption at the rate of step (4),
   `k₄[HBrO₂]B[Br⁻][H⁺]`, giving
   `[HBrO₂]B = (k₅/k₄)·[BrO₃⁻]·[H⁺] = 5.04×10⁻¹¹ M`.

3. **Slow phase = Process B.** While Process B runs, the solution is
   colourless, i.e. `[Ce⁴⁺] ≈ 0`, so step (7) — the only Br⁻ source — is
   off, while steps (4) and (5) both consume Br⁻.  Since `[HBrO₂]B` is
   stationary (and independent of `[Br⁻]`),
   `d[Br⁻]/dt = −k₄[HBrO₂]B[Br⁻][H⁺] − k₅[BrO₃⁻][Br⁻][H⁺]² = −λ·[Br⁻]`,
   with `λ = k₄[HBrO₂]B[H⁺] + k₅[BrO₃⁻][H⁺]² = 2·k₅[BrO₃⁻][H⁺]²
   = 0.16128 s⁻¹`
   (the two terms are equal exactly by the 2.2 stationary condition).
   Hence `[Br⁻](t) = [Br⁻]max·e^{−λt}` — precisely the non-constant
   traversal velocity the problem text announces.

4. **Period.** The slow descent lasts
   `τ = λ⁻¹·ln([Br⁻]max/[Br⁻]crit) = ln(7000/3)/0.16128 ≈ 48.08 s`;
   the return (Br⁻ regeneration by step (7) during the yellow Process-A
   burst) is "almost immediate" per the problem, so the descent duration
   is the requested period.

All values below are exact results of the printed decimals; final
reporting is to three significant figures (project-wide answer-blind
default): quantum `0.1 s`, reported value `48.1 s`.
-/

namespace IChO2026T2A5

open IChO2026Chem IChO2026Chem.Reporting Real Finset

/-! ## Stipulated problem data (printed values, kept as exact decimals) -/

noncomputable def k1 : ℝ := 1.0 * 10 ^ 4          -- M⁻² s⁻¹
noncomputable def k2 : ℝ := 6.2 * 10 ^ 4          -- M⁻² s⁻¹
noncomputable def k3 : ℝ := 4.0 * 10 ^ 7          -- M⁻¹ s⁻¹
noncomputable def k4 : ℝ := 2.0 * 10 ^ 9          -- M⁻² s⁻¹
noncomputable def k5 : ℝ := 2.1                   -- M⁻³ s⁻¹
noncomputable def k6 : ℝ := 8.2                   -- M⁻¹ s⁻¹
noncomputable def k7 : ℝ := 1.0 * 10 ^ 2          -- M⁻¹ s⁻¹
noncomputable def brO3 : ℝ := 0.06                -- M, maintained
noncomputable def ma : ℝ := 0.1                   -- M, maintained
noncomputable def hPlus : ℝ := 0.8                -- M, maintained
noncomputable def ce4 : ℝ := 0.001                -- M (initial)
/-- `[Br⁻]max = 7.0 × 10⁻⁴ M`, printed on page Q2-3. -/
noncomputable def brMax : ℝ := 7.0 * 10 ^ (-4 : ℤ)

/-! ## Derived quantities -/

/-- 2.3: critical bromide concentration, `[Br⁻]crit = k₁·[BrO₃⁻]/k₄`. -/
noncomputable def brCritical : ℝ := k1 * brO3 / k4

/-- 2.2: stationary `[HBrO₂]A` from `k₁·[BrO₃⁻]·[H⁺] = k₃·[HBrO₂]A`. -/
noncomputable def hbrO2_A : ℝ := k1 * brO3 * hPlus / k3

/-- 2.2: stationary `[HBrO₂]B` from
`k₅·[BrO₃⁻]·[Br⁻]·[H⁺]² = k₄·[HBrO₂]B·[Br⁻]·[H⁺]`. -/
noncomputable def hbrO2_B : ℝ := k5 * brO3 * hPlus / k4

/-- Decay constant of `[Br⁻]` during the slow (colourless, Process-B) phase:
`λ = k₄·[HBrO₂]B·[H⁺] + k₅·[BrO₃⁻]·[H⁺]²`. -/
noncomputable def lambda : ℝ := k4 * hbrO2_B * hPlus + k5 * brO3 * hPlus ^ 2

/-- 2.5: period of oscillations.  The slow exponential descent
`[Br⁻](t) = [Br⁻]max·exp(−λ·t)` reaches `[Br⁻]critical` after
`τ = ln([Br⁻]max/[Br⁻]crit)/λ`; the return is "almost immediate"
(problem text, page Q2-3), so this descent duration is the period. -/
noncomputable def tau : ℝ := Real.log (brMax / brCritical) / lambda

/-! ## Exact values of the derived quantities -/

theorem k1_value : k1 = 10000 := by norm_num [k1]
theorem k2_value : k2 = 62000 := by norm_num [k2]
theorem k3_value : k3 = 40000000 := by norm_num [k3]
theorem k4_value : k4 = 2000000000 := by norm_num [k4]
theorem k5_value : k5 = 2.1 := rfl
theorem k6_value : k6 = 8.2 := rfl
theorem k7_value : k7 = 100 := by norm_num [k7]
theorem brMax_value : brMax = 7 / 10000 := by norm_num [brMax]

/-- `[Br⁻]crit = 3 × 10⁻⁷ M` exactly. -/
theorem brCritical_value : brCritical = 3 * 10 ^ (-7 : ℤ) := by
  norm_num [brCritical, k1, k4, brO3]

/-- `[HBrO₂]A = 1.2 × 10⁻⁵ M` exactly. -/
theorem hbrO2_A_value : hbrO2_A = 1.2 * 10 ^ (-5 : ℤ) := by
  norm_num [hbrO2_A, k1, k3, brO3, hPlus]

/-- `[HBrO₂]B = 5.04 × 10⁻¹¹ M` exactly. -/
theorem hbrO2_B_value : hbrO2_B = 5.04 * 10 ^ (-11 : ℤ) := by
  norm_num [hbrO2_B, k5, k4, brO3, hPlus]

/-- The two Br⁻-consumption terms of the slow phase are equal — this is the
stationary condition `r₄ = r₅` of HBrO₂ in Process B — and
`λ = 2·k₅·[BrO₃⁻]·[H⁺]² = 0.16128 s⁻¹` exactly. -/
theorem lambda_value : lambda = 0.16128 := by
  norm_num [lambda, hbrO2_B, k4, k5, brO3, hPlus]

/-- Equivalent form of the rate law behind `d[Br⁻]/dt = −λ·[Br⁻]`. -/
theorem lambda_eq_twice_k5 : lambda = 2 * k5 * brO3 * hPlus ^ 2 := by
  norm_num [lambda, hbrO2_B, k4, k5, brO3, hPlus]

/-- The argument of the logarithm: `[Br⁻]max/[Br⁻]crit = 7000/3`. -/
theorem br_ratio : brMax / brCritical = 7000 / 3 := by
  rw [brCritical_value, brMax_value]; norm_num

/-- Definition-restating certificate of the period (semantic anchor). -/
theorem tau_eq : tau = Real.log (brMax / brCritical) / lambda := rfl

/-- Consistency with the phase portrait on page Q2-3:
`[HBrO₂]B < [HBrO₂]A`. -/
theorem hbrO2_A_gt_B : hbrO2_B < hbrO2_A := by
  rw [hbrO2_A_value, hbrO2_B_value]; norm_num

/-! ## Switching-condition statement (semantic anchor of 2.3) -/

/-- At any `[HBrO₂] = x ≠ 0` and any `[H⁺] = hp ≠ 0`, the rate of step (4)
equals the rate of step (1) exactly when `[Br⁻] = [Br⁻]critical`:
`k₄·x·b·hp = k₁·x·[BrO₃⁻]·hp ↔ b = [Br⁻]critical`. -/
theorem brCritical_characterisation (x b hp : ℝ) (hx : x ≠ 0) (hpH : hp ≠ 0) :
    k4 * x * b * hp = k1 * x * brO3 * hp ↔ b = brCritical := by
  have hk4 : (k4 : ℝ) ≠ 0 := by norm_num [k4]
  constructor
  · intro h
    have h2 : x * hp * (k4 * b) = x * hp * (k1 * brO3) := by
      calc x * hp * (k4 * b) = k4 * x * b * hp := by ring
        _ = k1 * x * brO3 * hp := h
        _ = x * hp * (k1 * brO3) := by ring
    have h3 : x * hp ≠ 0 := mul_ne_zero hx hpH
    have h4 : k4 * b = k1 * brO3 := mul_left_cancel₀ h3 h2
    rw [brCritical]
    field_simp
    linarith [h4]
  · intro h
    rw [h, brCritical]
    field_simp

/-! ## Certified rational bounds on `ln([Br⁻]max/[Br⁻]crit)`

We use the exact factorisation `7000/3 = 2⁷ · (875/768)` together with
Mathlib's alternating (artanh) series bounds on `log`:

* `Real.sum_range_le_log_div` — the truncated series
  `∑_{i<n} x^(2i+1)/(2i+1)` is a **lower** bound of
  `½·log((1+x)/(1−x))`, and
* `Real.log_div_le_sum_range_add` — the same truncation plus the
  geometric tail `x^(2n+1)/(1 − x²)` is an **upper** bound.

Instantiated with `x = 1/3` (for `(1+x)/(1−x) = 2`, i.e. `ln 2`,
24 terms) and `x = 107/1643` (for `(1+x)/(1−x) = 875/768`, 5 terms),
and cleared of the factor `1/2` by multiplication with `2`. -/

/-- `ln 2` to fourteen decimal places, certified from the artanh series
with `x = 1/3` and 24 terms. -/
theorem log_two_bounds :
    (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.6931471805599454 := by
  have hx0 : (0:ℝ) ≤ 1/3 := by norm_num
  have hx1 : (1/3 : ℝ) < 1 := by norm_num
  have hratio : (1 + (1/3 : ℝ)) / (1 - 1/3) = 2 := by norm_num
  have lo := Real.sum_range_le_log_div hx0 hx1 24
  have hi := Real.log_div_le_sum_range_add hx0 hx1 24
  rw [hratio] at lo hi
  have hlo : (0.693147180559945 : ℝ) / 2 ≤
      ∑ i ∈ range 24, (1/3 : ℝ) ^ (2*i+1) / (2*i+1) := by
    norm_num [Finset.sum_range_succ]
  have hhi : (∑ i ∈ range 24, (1/3 : ℝ) ^ (2*i+1) / (2*i+1)) +
      (1/3 : ℝ) ^ 49 / (1 - (1/3)^2) ≤ (0.6931471805599454 : ℝ) / 2 := by
    norm_num [Finset.sum_range_succ]
  constructor
  · calc (0.693147180559945 : ℝ) = (0.693147180559945 / 2) * 2 := by ring
      _ ≤ ((1/2) * Real.log 2) * 2 :=
          mul_le_mul_of_nonneg_right (le_trans hlo lo) (by norm_num)
      _ = Real.log 2 := by ring
  · calc Real.log 2 = ((1/2) * Real.log 2) * 2 := by ring
      _ ≤ ((0.6931471805599454 : ℝ) / 2) * 2 :=
          mul_le_mul_of_nonneg_right (le_trans hi hhi) (by norm_num)
      _ = 0.6931471805599454 := by ring

/-- `ln(875/768)` to nine decimal places, certified from the artanh series
with `x = 107/1643` and five terms. -/
theorem log_875_768_bounds :
    (0.130434153 : ℝ) ≤ Real.log (875 / 768) ∧
      Real.log (875 / 768) ≤ 0.130434154 := by
  have hx0 : (0:ℝ) ≤ 107/1643 := by norm_num
  have hx1 : (107/1643 : ℝ) < 1 := by norm_num
  have hratio : (1 + (107/1643 : ℝ)) / (1 - 107/1643) = 875/768 := by norm_num
  have lo := Real.sum_range_le_log_div hx0 hx1 5
  have hi := Real.log_div_le_sum_range_add hx0 hx1 5
  rw [hratio] at lo hi
  have hlo : (0.130434153 : ℝ) / 2 ≤
      ∑ i ∈ range 5, (107/1643 : ℝ) ^ (2*i+1) / (2*i+1) := by
    norm_num [Finset.sum_range_succ]
  have hhi : (∑ i ∈ range 5, (107/1643 : ℝ) ^ (2*i+1) / (2*i+1)) +
      (107/1643 : ℝ) ^ 11 / (1 - (107/1643)^2) ≤ (0.130434154 : ℝ) / 2 := by
    norm_num [Finset.sum_range_succ]
  constructor
  · calc (0.130434153 : ℝ) = (0.130434153 / 2) * 2 := by ring
      _ ≤ ((1/2) * Real.log (875/768)) * 2 :=
          mul_le_mul_of_nonneg_right (le_trans hlo lo) (by norm_num)
      _ = Real.log (875/768) := by ring
  · calc Real.log (875/768) = ((1/2) * Real.log (875/768)) * 2 := by ring
      _ ≤ ((0.130434154 : ℝ) / 2) * 2 :=
          mul_le_mul_of_nonneg_right (le_trans hi hhi) (by norm_num)
      _ = 0.130434154 := by ring

/-- The exact factorisation `7000/3 = 2¹¹ · (875/768)`. -/
theorem ratio_decompose : (7000 : ℝ) / 3 = 2 ^ 11 * (875 / 768) := by norm_num

/-- Bounds on `ln([Br⁻]max/[Br⁻]crit) = ln(7000/3)`:
`7.75504327 < ln(7000/3) < 7.75505986`. -/
theorem log_ratio_bounds :
    (7.75504327 : ℝ) ≤ Real.log (brMax / brCritical) ∧
      Real.log (brMax / brCritical) ≤ 7.75505986 := by
  rw [br_ratio, ratio_decompose]
  obtain ⟨h2lo, h2hi⟩ := log_two_bounds
  obtain ⟨hrlo, hrhi⟩ := log_875_768_bounds
  have hfac :
      Real.log ((2:ℝ) ^ 11 * (875 / 768)) =
        11 * Real.log 2 + Real.log (875 / 768) := by
    rw [log_mul (by norm_num) (by norm_num), log_pow]
    norm_num [Nat.cast_ofNat]
  rw [hfac]
  constructor
  · have h1 : (11:ℝ) * Real.log 2 ≥ 11 * 0.693147180559945 :=
      mul_le_mul_of_nonneg_left h2lo (by norm_num)
    have h2 : Real.log (875/768) ≥ (0.130434153:ℝ) := hrlo
    linarith
  · have h1 : (11:ℝ) * Real.log 2 ≤ 11 * 0.6931471805599454 :=
      mul_le_mul_of_nonneg_left h2hi (by norm_num)
    have h2 : Real.log (875/768) ≤ (0.130434154:ℝ) := hrhi
    linarith

/-- The period lies strictly inside the reporting half-quantum band around
`48.1 s` with quantum `0.1 s`: `48.05 < τ < 48.15`. -/
theorem tau_report_band : (48.05 : ℝ) < tau ∧ tau < 48.15 := by
  obtain ⟨hlo, hhi⟩ := log_ratio_bounds
  have hlam : lambda = 0.16128 := lambda_value
  have hlam_pos : (0:ℝ) < lambda := by rw [hlam]; norm_num
  rw [tau]
  constructor
  · rw [lt_div_iff₀ hlam_pos]
    have h1 : (48.05 : ℝ) * 0.16128 = 7.749504 := by norm_num
    rw [hlam, h1]
    linarith [hlo]
  · rw [div_lt_iff₀ hlam_pos]
    have h2 : (48.15 : ℝ) * 0.16128 = 7.765632 := by norm_num
    rw [hlam, h2]
    linarith [hhi]

/-- Positivity of the period. -/
theorem tau_pos : 0 < tau :=
  lt_of_lt_of_le (by norm_num : (0:ℝ) < 48.05) tau_report_band.1.le

/-! ## Final reporting (uniform answer-blind policy: 3 significant figures;
for a value between 10 and 100 the 3-s.f. quantum is `0.1 s`) -/

/-- The answer-blind numerical submission for τ: raw exact value and the
three-significant-figure display `τ = 48.1 s`. -/
noncomputable def tauSubmission : NumericSubmission where
  rawValue := tau
  reportedValue := 48.1
  reportingQuantum := 0.1

/-- The raw value is exactly the derived expression. -/
theorem tauSubmission_raw : tauSubmission.rawValue = tau := rfl

/-- `48.1` is a valid display of `τ` at quantum `0.1 s`:
`48.1 = 481 · 0.1`, `0 ≤ τ`, and `48.1 − 0.05 ≤ τ < 48.1 + 0.05`. -/
theorem tauSubmission_valid :
    ReportsAtQuantum tauSubmission.rawValue tauSubmission.reportedValue
      tauSubmission.reportingQuantum := by
  obtain ⟨hlo, hhi⟩ := tau_report_band
  have hq : (0:ℝ) < tauSubmission.reportingQuantum := by norm_num [tauSubmission]
  have hrep : ∃ k : ℤ, tauSubmission.reportedValue =
      tauSubmission.reportingQuantum * k := ⟨481, by norm_num [tauSubmission]⟩
  have hraw : tauSubmission.rawValue = tau := rfl
  rw [hraw]
  refine ⟨hq, hrep, ?_⟩
  have hnn : (0 : ℝ) ≤ tau := tau_pos.le
  rw [if_pos hnn]
  constructor
  · change tauSubmission.reportedValue - tauSubmission.reportingQuantum / 2 ≤ tau
    calc tauSubmission.reportedValue - tauSubmission.reportingQuantum / 2
          = 48.05 := by norm_num [tauSubmission]
        _ ≤ tau := hlo.le
  · change tau < tauSubmission.reportedValue + tauSubmission.reportingQuantum / 2
    calc tau < 48.15 := hhi
      _ = tauSubmission.reportedValue + tauSubmission.reportingQuantum / 2 := by
          norm_num [tauSubmission]

/-- The submission satisfies the target-independent validity contract. -/
theorem tauSubmission_contract :
    ValidNumericSubmission tau tauSubmission :=
  ⟨rfl, tauSubmission_valid⟩

end IChO2026T2A5
