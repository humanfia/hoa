import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T2, Part A2 (subquestion 2.2)

Kinetics of the Belousov–Zhabotinsky reaction: stationary concentrations of
HBrO₂ in Processes A and B under the steady-state approximation (SSA).

## Problem data (official statement, pages Q2-1/Q2-2)

Rate constants
* `k₁ = 1.0 × 10⁴ M⁻² s⁻¹` — (1) HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O
* `k₂ = 6.2 × 10⁴ M⁻² s⁻¹` — (2) BrO₂• + Ce³⁺ + H⁺ → HBrO₂ + Ce⁴⁺
* `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹` — (3) 2 HBrO₂ → BrO₃⁻ + HBrO + H⁺
* `k₄ = 2.0 × 10⁹ M⁻² s⁻¹` — (4) HBrO₂ + Br⁻ + H⁺ → 2 HBrO
* `k₅ = 2.1 M⁻³ s⁻¹`       — (5) BrO₃⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO₂
* `k₆ = 8.2 M⁻¹ s⁻¹`       — (6) HBrO + MA → BMA + H₂O

Held-constant reactant concentrations
  `[BrO₃⁻]₀ = 0.06 M`, `[MA]₀ = 0.1 M`, `[H⁺]₀ = 0.8 M`, `[Ce⁴⁺]₀ = 0.001 M`;
  all reactants except Ce⁴⁺ and the pH are maintained constant.

## Steady-state balance equations (mass–action stoichiometry)

Process A (steps 1–3 only; Process B is off).  With rates
`r₁ = k₁ X B H`, `r₂ = k₂ Y C₃ H` (per Ce³⁺ consumed) and `r₃ = k₃ X²`:

* SSA for the radical BrO₂•: `2 r₁ - r₂ = 0`, i.e. `r₂ = 2 r₁`;
* SSA for HBrO₂: `dX/dt = r₂ - r₁ - 2 r₃ = 0` (Ce⁴⁺-caused term
  `-k₂ Y C₄ H` appears separately; in the radical steady state the total
  Ce consumption `k₂ Y (C₃ + C₄) H = 2 r₁` exactly cancels it).

Combining gives `r₁ = 2 r₃`, hence the positive root

  `X_A = k₁ [BrO₃⁻] [H⁺] / (2 k₃) = 6.0 × 10⁻⁶ M`.

Process B (steps 4–6 only; Process A is off).  Since step (6) does not
involve HBrO₂, the HBrO₂ balance is `r₅ - r₄ = 0` with `r₄ = k₄ X Br H`
and `r₅ = k₅ B Br H²` (Br⁻ is held constant, so both rates are pinned):

  `X_B = k₅ [BrO₃⁻] [H⁺] / k₄ = 5.04 × 10⁻¹¹ M`.

## Results (3 significant figures)

* `[HBrO₂]_A = 6.00 × 10⁻⁶ mol dm⁻³`
* `[HBrO₂]_B = 5.04 × 10⁻¹¹ mol dm⁻³`

Both are consistent with the problem's own printed fallback values for
later parts (`1 × 10⁻⁵ M` and `1 × 10⁻¹⁰ M` respectively).
-/

namespace IChO2026.T2.A2

open IChO2026Chem.Reporting

-- ## Problem inputs (stipulated constants, exact as printed)

/-- Rate constant of step (1). -/
noncomputable def k1 : ℝ := 1.0e4

/-- Rate constant of step (3). -/
noncomputable def k3 : ℝ := 4.0e7

/-- Rate constant of step (4). -/
noncomputable def k4 : ℝ := 2.0e9

/-- Rate constant of step (5). -/
noncomputable def k5 : ℝ := 2.1

/-- Held-constant bromate concentration `[BrO₃⁻]₀` in mol dm⁻³. -/
noncomputable def bromate : ℝ := 0.06

/-- Held-constant proton concentration `[H⁺]₀` in mol dm⁻³. -/
noncomputable def proton : ℝ := 0.8

theorem k1_pos : 0 < k1 := by norm_num [k1]
theorem k3_pos : 0 < k3 := by norm_num [k3]
theorem k4_pos : 0 < k4 := by norm_num [k4]
theorem k5_pos : 0 < k5 := by norm_num [k5]
theorem bromate_pos : 0 < bromate := by norm_num [bromate]
theorem proton_pos : 0 < proton := by norm_num [proton]

-- ## Closed-form stationary concentrations

/-- Stationary HBrO₂ concentration in Process A, from `r₁ = 2 r₃`. -/
noncomputable def hbro2A : ℝ := k1 * bromate * proton / (2 * k3)

/-- Stationary HBrO₂ concentration in Process B, from `r₅ = r₄`. -/
noncomputable def hbro2B : ℝ := k5 * bromate * proton / k4

-- ## Process A: steady-state uniqueness and value

/-- Any HBrO₂ concentration `Y` annihilated in step (2) at the rate `r₂`
(with cerium held nonzero) equals the radical steady-state level
`k₂ Y Ce H = 2 r₁ → Y = 2 r₁ / (k₂ Ce H)`. -/
theorem radical_ssa_value {k2 Y ce H r1 : ℝ}
    (hk2 : 0 < k2) (hce : 0 < ce) (hH : 0 < H)
    (h : k2 * Y * ce * H = 2 * r1) :
    Y = 2 * r1 / (k2 * ce * H) := by
  have hne : k2 * ce * H ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hk2) (ne_of_gt hce)) (ne_of_gt hH)
  field_simp
  linear_combination h

/-- **Process A stationary HBrO₂.**  Under the SSA,
`d[HBrO₂]/dt = (r₂ - k₂ Y C₄ H) - r₁ - 2 r₃ = 0`, where `r₂ = k₂ Y C₃ H`
is the fraction of HBrO₂ production that replaces HBrO₂ consumed by Ce³⁺,
`k₂ Y C₄ H` the HBrO₂ annihilation caused by Ce⁴⁺, `r₁ = k₁ X B H` and
`r₃ = k₃ X²`.  Together with the radical steady state
`k₂ Y (C₃ + C₄) H = 2 r₁`, the only root in `0 < X` of the HBrO₂ balance
`r₁ = 2 r₃` is `hbro2A`. -/
theorem hbro2_process_A {X Y u v ce4 k2 : ℝ}
    (_hY : 0 < Y) (_hu : 0 < u) (_hce4 : 0 < ce4) (_hk2 : 0 < k2)
    (hX : 0 < X)
    (_hrad : k2 * Y * (u + v) * proton = 2 * (k1 * X * bromate * proton))
    (_hYssa : k2 * Y * u * proton = 2 * (k1 * X * bromate * proton))
    (h1 : k1 * X * bromate * proton = 2 * (k3 * X ^ 2)) :
    X = hbro2A := by
  have hk1 : k1 ≠ 0 := ne_of_gt k1_pos
  have hb : bromate ≠ 0 := ne_of_gt bromate_pos
  have hp : proton ≠ 0 := ne_of_gt proton_pos
  have hk3 : k3 ≠ 0 := ne_of_gt k3_pos
  have hX' : X ≠ 0 := ne_of_gt hX
  -- Divide the balance `k₁ X B H = 2 k₃ X²` by the nonzero factor `X`.
  have hdiv : k1 * bromate * proton = 2 * k3 * X := by
    apply mul_left_cancel₀ hX'
    -- Multiplying the goal by `X` recovers the hypothesis `h1` exactly.
    linear_combination h1
  unfold hbro2A
  field_simp
  linear_combination -hdiv

/-- Numeric evaluation of the Process A stationary concentration:
`hbro2A = 1.0e4 * 0.06 * 0.8 / (2 * 4.0e7) = 6.0e-6 mol dm⁻³`. -/
theorem hbro2A_value : hbro2A = 6.0e-6 := by
  unfold hbro2A k1 bromate proton k3
  norm_num

theorem hbro2A_pos : 0 < hbro2A := by
  rw [hbro2A_value]; norm_num

-- ## Process B: steady-state uniqueness and value

/-- **Process B stationary HBrO₂.**  In Process B, only steps (4) and (5)
produce or consume HBrO₂ (step (6) involves HBrO and MA only).  Bromide is
held constant, so the SSA balance `k₅ B Br H² = k₄ X Br H` divides by the
nonzero factor `Br · H` and pins the unique root `X = hbro2B`. -/
theorem hbro2_process_B {X br : ℝ}
    (hbr : 0 < br) (_hX : 0 < X)
    (h2 : k5 * bromate * br * proton ^ 2 = k4 * X * br * proton) :
    X = hbro2B := by
  have hbr' : br ≠ 0 := ne_of_gt hbr
  have hp : proton ≠ 0 := ne_of_gt proton_pos
  have hk4 : k4 ≠ 0 := ne_of_gt k4_pos
  unfold hbro2B
  rw [eq_div_iff hk4]
  -- Divide the balance by the nonzero factor `br * proton`.
  have hf : br * proton ≠ 0 := mul_ne_zero hbr' hp
  apply mul_left_cancel₀ hf
  -- Multiplying the goal by `br * proton` recovers the hypothesis `h2`.
  linear_combination -h2

/-- Numeric evaluation of the Process B stationary concentration:
`hbro2B = 2.1 * 0.06 * 0.8 / 2.0e9 = 5.04e-11 mol dm⁻³`. -/
theorem hbro2B_value : hbro2B = 5.04e-11 := by
  unfold hbro2B k5 bromate proton k4
  norm_num

theorem hbro2B_pos : 0 < hbro2B := by
  rw [hbro2B_value]; norm_num

-- ## Final answer-blind reporting (3 significant figures, powers of ten)

/-- Final reported value for `[HBrO₂]_A`: `6.00 × 10⁻⁶ mol dm⁻³` at
quantum `1 × 10⁻⁸` (third significant figure of a `10⁻⁶`-scale value). -/
noncomputable def submissionA : NumericSubmission where
  rawValue := hbro2A
  reportedValue := 6.00e-6
  reportingQuantum := 1.0e-8

/-- Final reported value for `[HBrO₂]_B`: `5.04 × 10⁻¹¹ mol dm⁻³` at
quantum `1 × 10⁻¹³` (third significant figure of a `10⁻¹¹`-scale value). -/
noncomputable def submissionB : NumericSubmission where
  rawValue := hbro2B
  reportedValue := 5.04e-11
  reportingQuantum := 1.0e-13

/-- The Process A submission satisfies the fixed reporting contract: the
raw expression is the exact closed form and `6.00e-6` is the nearest
multiple of `1.0e-8`, with no tie. -/
theorem valid_submission_A : ValidNumericSubmission hbro2A submissionA := by
  refine ⟨rfl, ?_, ⟨600, ?_⟩, ?_⟩
  · show (0 : ℝ) < 1.0e-8; norm_num
  · show (6.00e-6 : ℝ) = 1.0e-8 * (600 : ℤ); norm_num
  · have hraw : submissionA.rawValue = 6.0e-6 := hbro2A_value
    rw [if_pos (by rw [hraw]; norm_num), hraw]
    show 6.00e-6 - 1.0e-8 / 2 ≤ (6.0e-6 : ℝ) ∧ 6.0e-6 < 6.00e-6 + 1.0e-8 / 2
    constructor <;> norm_num

/-- The Process B submission satisfies the fixed reporting contract: the
raw expression is the exact closed form and `5.04e-11` is the nearest
multiple of `1.0e-13`, with no tie. -/
theorem valid_submission_B : ValidNumericSubmission hbro2B submissionB := by
  refine ⟨rfl, ?_, ⟨504, ?_⟩, ?_⟩
  · show (0 : ℝ) < 1.0e-13; norm_num
  · show (5.04e-11 : ℝ) = 1.0e-13 * (504 : ℤ); norm_num
  · have hraw : submissionB.rawValue = 5.04e-11 := hbro2B_value
    rw [if_pos (by rw [hraw]; norm_num), hraw]
    show 5.04e-11 - 1.0e-13 / 2 ≤ (5.04e-11 : ℝ) ∧ 5.04e-11 < 5.04e-11 + 1.0e-13 / 2
    constructor <;> norm_num

/-- Combined answer: the two stationary concentrations and their
3-significant-figure reported values. -/
theorem icho_2026_t2_a2_answer :
    hbro2A = 6.0e-6 ∧ hbro2B = 5.04e-11 ∧
    ValidNumericSubmission hbro2A submissionA ∧
    ValidNumericSubmission hbro2B submissionB :=
  ⟨hbro2A_value, hbro2B_value, valid_submission_A, valid_submission_B⟩

#print axioms hbro2_process_A
#print axioms hbro2_process_B
#print axioms hbro2A_value
#print axioms hbro2B_value
#print axioms valid_submission_A
#print axioms valid_submission_B
#print axioms icho_2026_t2_a2_answer

end IChO2026.T2.A2
