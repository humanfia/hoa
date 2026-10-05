import Mathlib

/-!
# IChO 2026, Problem T2, Subquestion A3 (question 2.3): [Br⁻]critical

## Problem source (theory_problem.pdf, Q2-2/Q2-3, source pages 15–17)

The Belousov–Zhabotinsky mechanism gives the elementary steps

* Process A: (1) `HBrO2 + BrO3⁻ + H⁺ → 2 BrO2• + H2O` with `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`;
* Process B: (4) `HBrO2 + Br⁻ + H⁺ → 2 HBrO` with `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`,
  (5) `BrO3⁻ + Br⁻ + 2H⁺ → HBrO + HBrO2` with `k₅ = 2.1 M⁻³ s⁻¹`;

with buffered concentrations `[BrO3⁻]₀ = 0.06 M`, `[H⁺]₀ = 0.8 M` and cerium
loading `[Ce⁴⁺]₀ = 0.001 M`, all held constant.

Q2.3 states: *"[Br⁻]critical is the critical concentration of Br⁻ at which
there is a switchover in processes from A to B or from B to A.  To switch
Process A to Process B, the reaction rate of the elementary step (4) must
exceed that of the elementary step (1) and vice versa."*  Hence the critical
concentration is the threshold at which `r₁ = r₄`.  The switch *from B to A*
happens at `[HBrO2] = [HBrO2]B` (the level Process B itself produces); since
both `r₁` and `r₄` are proportional to `[HBrO2]`, that factor cancels and
`[Br⁻]critical = k₁ [BrO3⁻]₀ / k₄ = 3.0 × 10⁻⁷ M`.  This file also derives
the stationary levels `[HBrO2]A`, `[HBrO2]B` from the steady-state
approximation (the previous part T2-A2), establishing that they are strictly
positive so the cancellation is legitimate.

## What is proved

* `bromide_critical_switch`: at `[Br⁻] = [Br⁻]critical` the rates of steps (1)
  and (4) are equal; below it `r₄ < r₁` (Process A proceeds), above it
  `r₄ > r₁` (Process B proceeds).  This is the problem's defining criterion.
* `bromide_critical_value`: `[Br⁻]critical = 3.0 × 10⁻⁷ mol dm⁻³`
  (`0.30 µmol dm⁻³`), reported to three significant figures as `300 × 10⁻⁹`.
* `hbrO2_A_steadyState`, `hbrO2_B_steadyState`: the T2-A2 steady-state
  balances that fix `[HBrO2]A`, `[HBrO2]B` (both positive).

All numerical assertions are exact rational equalities/inequalities over `ℝ`
proved by `norm_num`/`nlinarith`; no `sorry` and no custom axioms are used.
-/

open Real

namespace IChO2026T2A3

/-- Bundle of the exact printed problem inputs for Q2.3.  Only the data that
enters Q2.3 (and its T2-A2 prerequisites) are recorded. -/
structure BZData where
  k₁ : ℝ  -- rate constant of step (1)
  k₃ : ℝ  -- rate constant of step (3)
  k₄ : ℝ  -- rate constant of step (4)
  k₅ : ℝ  -- rate constant of step (5)
  cBrO3 : ℝ -- buffered `[BrO3⁻]₀`
  cH : ℝ    -- buffered `[H⁺]₀`
  hk₁ : k₁ = 1.0e4
  hk₃ : k₃ = 4.0e7
  hk₄ : k₄ = 2.0e9
  hk₅ : k₅ = 2.1
  hcBrO3 : cBrO3 = 0.06
  hcH : cH = 0.8

namespace BZData

variable (d : BZData)

theorem k₁_pos : 0 < d.k₁ := d.hk₁ ▸ by norm_num
theorem k₃_pos : 0 < d.k₃ := d.hk₃ ▸ by norm_num
theorem k₄_pos : 0 < d.k₄ := d.hk₄ ▸ by norm_num
theorem k₅_pos : 0 < d.k₅ := d.hk₅ ▸ by norm_num
theorem cBrO3_pos : 0 < d.cBrO3 := d.hcBrO3 ▸ by norm_num
theorem cH_pos : 0 < d.cH := d.hcH ▸ by norm_num

/-- Rate law of step (1), `r₁ = k₁ [HBrO2] [BrO3⁻] [H⁺]`. -/
noncomputable def r₁ (X : ℝ) : ℝ := d.k₁ * X * d.cBrO3 * d.cH
/-- Rate law of step (4), `r₄ = k₄ [HBrO2] [Br⁻] [H⁺]`. -/
noncomputable def r₄ (X b : ℝ) : ℝ := d.k₄ * X * b * d.cH

/-- The critical bromide concentration of Q2.3, `[Br⁻]critical = k₁[BrO3⁻]₀/k₄`. -/
noncomputable def bromideCritical : ℝ := d.k₁ * d.cBrO3 / d.k₄

/-- The core rate identity: `(k₄ X [H⁺]) · [Br⁻]critical = (k₁ X [H⁺]) · [BrO3⁻]₀`,
i.e. the threshold at which `r₄ = r₁`. -/
theorem bromideCritical_rate_identity (X : ℝ) :
    (d.k₄ * X * d.cH) * d.bromideCritical = (d.k₁ * X * d.cH) * d.cBrO3 := by
  rw [bromideCritical]
  field_simp [ne_of_gt d.k₄_pos]

/-- **The defining switchover property** of Q2.3 at any nonzero HBrO2 level:
at `[Br⁻] = [Br⁻]critical` the rates of steps (1) and (4) are equal; below it
`r₄ < r₁` (Process A proceeds / B switches off), above it `r₄ > r₁` (Process B
proceeds / A switches off). -/
theorem bromide_critical_switch (X : ℝ) (hX : 0 < X) :
    d.r₄ X d.bromideCritical = d.r₁ X
    ∧ (∀ b, 0 ≤ b → (d.r₄ X b < d.r₁ X ↔ b < d.bromideCritical))
    ∧ (∀ b, 0 ≤ b → (d.r₁ X < d.r₄ X b ↔ d.bromideCritical < b)) := by
  have hα : 0 < d.k₄ * X * d.cH := mul_pos (mul_pos d.k₄_pos hX) d.cH_pos
  have hI := d.bromideCritical_rate_identity X
  -- rewrites of the rate laws into factored form
  have hr₄ : ∀ b, d.r₄ X b = (d.k₄ * X * d.cH) * b := fun b => by
    rw [r₄]; ring
  have hr₁ : d.r₁ X = (d.k₁ * X * d.cH) * d.cBrO3 := by rw [r₁]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hr₄, hr₁]; exact hI
  · intro b _
    rw [hr₄ b, hr₁, ← hI]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      exact absurd (mul_le_mul_of_nonneg_left hcon hα.le) (not_le.mpr h)
    · intro h
      exact mul_lt_mul_of_pos_left h hα
  · intro b _
    rw [hr₄ b, hr₁, ← hI]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      exact absurd (mul_le_mul_of_nonneg_left hcon hα.le) (not_le.mpr h)
    · intro h
      exact mul_lt_mul_of_pos_left h hα

/-- **Main answer.** The requested value, exactly:
`[Br⁻]critical = 3.0 × 10⁻⁷ mol dm⁻³`. -/
theorem bromide_critical_value : d.bromideCritical = 3.0e-7 := by
  rw [bromideCritical, d.hk₁, d.hcBrO3, d.hk₄]
  norm_num

/-- In micromolar: `[Br⁻]critical = 0.30 µmol dm⁻³`. -/
theorem bromide_critical_value_umol : d.bromideCritical * 1.0e6 = 0.3 := by
  rw [d.bromide_critical_value]; norm_num

/-- Three-significant-figure reporting at quantum `10⁻⁹`:
`[Br⁻]critical = 300 × 10⁻⁹ = 3.00 × 10⁻⁷`. -/
theorem bromide_critical_reported : d.bromideCritical = 300 * 1.0e-9 := by
  rw [d.bromide_critical_value]; norm_num

/-- `[Br⁻]critical` sits above the printed `1 × 10⁻⁷ M` fallback (same order
of magnitude; the fallback is only a stub for students who did not derive
the value). -/
theorem bromide_critical_above_fallback : (1.0e-7 : ℝ) < d.bromideCritical := by
  rw [d.bromide_critical_value]; norm_num

/-! ## T2-A2 stationary HBrO2 levels (prerequisites, from problem data) -/

/-- The stationary HBrO2 level in Process A,
`[HBrO2]A = k₁ [BrO3⁻]₀ [H⁺]₀ / k₃` (from `r₁ = r₃` at the radical steady
state, `2 r₂` for step (2) being balanced by the Ce³⁺ reservoir). -/
noncomputable def hbrO2A : ℝ := d.k₁ * d.cBrO3 * d.cH / d.k₃

theorem hbrO2A_pos : 0 < d.hbrO2A :=
  div_pos (mul_pos (mul_pos d.k₁_pos d.cBrO3_pos) d.cH_pos) d.k₃_pos

/-- Process-A steady-state balance `r₁ = r₃`, i.e.
`k₁ X [BrO3⁻]₀ [H⁺]₀ = k₃ X²` with `X = [HBrO2]A`. -/
theorem hbrO2_A_steadyState :
    d.k₁ * d.hbrO2A * d.cBrO3 * d.cH = d.k₃ * d.hbrO2A ^ 2 := by
  rw [hbrO2A]
  field_simp [ne_of_gt d.k₃_pos]

/-- Numeric: `[HBrO2]A = 1.2 × 10⁻⁵ M`. -/
theorem hbrO2A_value : d.hbrO2A = 1.2e-5 := by
  have h : d.hbrO2A = (1.0e4 : ℝ) * 0.06 * 0.8 / (4.0e7 : ℝ) := by
    rw [hbrO2A, d.hk₁, d.hcBrO3, d.hcH, d.hk₃]
  rw [h]; field_simp; norm_num

/-- Linear coefficient in the Process-B steady-state quadratic,
`β = k₅ [BrO3⁻]₀ [H⁺]₀² / 2 = 0.04032`. -/
noncomputable def βB : ℝ := d.k₅ * d.cBrO3 * d.cH ^ 2 / 2

theorem βB_eq : d.βB = 0.04032 := by
  have h : d.βB = (2.1 : ℝ) * 0.06 * 0.8 ^ 2 / 2 := by
    rw [βB, d.hk₅, d.hcBrO3, d.hcH]
  rw [h]
  ring_nf

/-- Positive source term `T = k₅ [BrO3⁻]₀² [H⁺]₀²`. -/
noncomputable def TB : ℝ := d.k₅ * d.cBrO3 ^ 2 * d.cH ^ 2

theorem TB_eq : d.TB = 0.0048384 := by
  have h : d.TB = (2.1 : ℝ) * 0.06 ^ 2 * 0.8 ^ 2 := by
    rw [TB, d.hk₅, d.hcBrO3, d.hcH]
  rw [h]; ring_nf

/-- The discriminant of the Process-B quadratic,
`D = β² + 16 k₄ [H⁺]₀ T = 1209600000015876 / 9765625 ≈ 1.23863 × 10⁸`. -/
theorem discriminant_eq :
    d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB = 1209600000015876 / 9765625 := by
  rw [d.βB_eq, d.TB_eq, d.hk₄, d.hcH]
  norm_num

/-- The stationary HBrO2 level in Process B, the unique positive root of
`4 k₄ [H⁺]₀ X² + β X − T = 0`:
`[HBrO2]B = (−β + √(β² + 16 k₄ [H⁺]₀ T)) / (8 k₄ [H⁺]₀)`. -/
noncomputable def hbrO2B : ℝ :=
  (-d.βB + √(d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB)) / (8 * d.k₄ * d.cH)

theorem hbrO2B_eq :
    d.hbrO2B = (√(1209600000015876 / 9765625) - 0.04032) / 1.28e10 := by
  show (-(d.βB) + √(d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB)) / (8 * d.k₄ * d.cH)
      = (√(1209600000015876 / 9765625) - 0.04032) / 1.28e10
  rw [d.βB_eq, d.TB_eq, d.hk₄, d.hcH]

  ring_nf

/-- `√D > 0.04032`, so the numerator of `[HBrO2]B` is positive. -/
theorem sqrtD_gt : (0.04032 : ℝ) < √(1209600000015876 / 9765625) := by
  rw [← Real.sqrt_sq (show (0:ℝ) ≤ 0.04032 by norm_num)]
  apply Real.sqrt_lt_sqrt (by norm_num)
  norm_num

theorem hbrO2B_pos : 0 < d.hbrO2B := by
  rw [d.hbrO2B_eq]
  exact div_pos (sub_pos.2 sqrtD_gt) (by norm_num)

/-- Numeric magnitude of the Process-B level:
`8.6 × 10⁻⁷ < [HBrO2]B < 8.7 × 10⁻⁷`. -/
theorem hbrO2B_value : (8.6e-7 : ℝ) < d.hbrO2B ∧ d.hbrO2B < 8.7e-7 := by
  rw [d.hbrO2B_eq]
  have hnn : (0:ℝ) ≤ 1209600000015876 / 9765625 := by norm_num
  have hlo : (11129 : ℝ) < √(1209600000015876 / 9765625) := by
    rw [← Real.sqrt_sq (show (0:ℝ) ≤ 11129 by norm_num)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by norm_num)
  have hhi : √(1209600000015876 / 9765625) < (11130 : ℝ) := by
    rw [← Real.sqrt_sq (show (0:ℝ) ≤ 11130 by norm_num)]
    apply Real.sqrt_lt_sqrt hnn
    norm_num
  have hd : (0:ℝ) < 1.28e10 := by norm_num
  -- `(√D − 0.04032)` lies between `11128.96` and `11129.96`,
  -- so `[HBrO2]B` lies between roughly `8.6945e-7` and `8.6953e-7`.
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith [hlo]
  · rw [div_lt_iff₀ hd]
    nlinarith [hhi]

/-- The Process-B steady-state equation:
`4 k₄ [H⁺]₀ [HBrO2]B² + β [HBrO2]B − k₅ [BrO3⁻]₀² [H⁺]₀² = 0`. -/
theorem hbrO2_B_steadyState :
    4 * d.k₄ * d.cH * d.hbrO2B ^ 2 + d.βB * d.hbrO2B - d.TB = 0 := by
  have hDnn : 0 ≤ d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB := by
    rw [discriminant_eq]; norm_num
  have hsq : (√(d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB)) ^ 2
      = d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB := Real.sq_sqrt hDnn
  have h8kc : (8:ℝ) * d.k₄ * d.cH ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) d.k₄_pos) d.cH_pos)
  have hX : d.hbrO2B * (8 * d.k₄ * d.cH)
      = -d.βB + √(d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB) := by
    rw [hbrO2B, div_mul_cancel₀ _ h8kc]
  -- `X·(8k₄cH) + β = √D`; square and expand.
  set S := √(d.βB ^ 2 + 16 * d.k₄ * d.cH * d.TB) with hS
  have key : 8 * d.k₄ * d.cH * d.hbrO2B + d.βB = S := by
    have hX2 : 8 * d.k₄ * d.cH * d.hbrO2B = -d.βB + S := by
      rw [mul_comm]; exact hX
    linarith [hX2]
  have hsq2 : (8 * d.k₄ * d.cH * d.hbrO2B + d.βB) ^ 2 = S ^ 2 := by rw [key]
  rw [hS, hsq] at hsq2
  have hexp : (8 * d.k₄ * d.cH * d.hbrO2B + d.βB) ^ 2
      = (8 * d.k₄ * d.cH) ^ 2 * d.hbrO2B ^ 2 + 16 * d.k₄ * d.cH * (d.βB * d.hbrO2B)
        + d.βB ^ 2 := by ring
  rw [hexp] at hsq2
  have hd2 : (16:ℝ) * d.k₄ * d.cH ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) d.k₄_pos) d.cH_pos)
  have hfactor : (8 * d.k₄ * d.cH) ^ 2 = (16 * d.k₄ * d.cH) * (4 * d.k₄ * d.cH) := by ring
  rw [hfactor] at hsq2
  have hmain : (16 * d.k₄ * d.cH) * (4 * d.k₄ * d.cH) * d.hbrO2B ^ 2
      + 16 * d.k₄ * d.cH * (d.βB * d.hbrO2B)
      = 16 * d.k₄ * d.cH * d.TB := by linarith [hsq2]
  have hfact2 : (16 * d.k₄ * d.cH) * (4 * d.k₄ * d.cH) * d.hbrO2B ^ 2
      + 16 * d.k₄ * d.cH * (d.βB * d.hbrO2B)
      = (16 * d.k₄ * d.cH) * (4 * d.k₄ * d.cH * d.hbrO2B ^ 2 + d.βB * d.hbrO2B) := by ring
  rw [hfact2] at hmain
  have hdone := (mul_right_inj' hd2).mp hmain
  linarith

end BZData

/-- Concrete instantiation on the exact printed data of the problem. -/
noncomputable def problemData : BZData :=
  { k₁ := 1.0e4, k₃ := 4.0e7, k₄ := 2.0e9, k₅ := 2.1,
    cBrO3 := 0.06, cH := 0.8,
    hk₁ := rfl, hk₃ := rfl, hk₄ := rfl, hk₅ := rfl,
    hcBrO3 := rfl, hcH := rfl }

/-- Final answer on the concrete problem data:
`[Br⁻]critical = 3.0 × 10⁻⁷ mol dm⁻³`. -/
theorem answer_bromideCritical : problemData.bromideCritical = 3.0e-7 :=
  problemData.bromide_critical_value

end IChO2026T2A3
