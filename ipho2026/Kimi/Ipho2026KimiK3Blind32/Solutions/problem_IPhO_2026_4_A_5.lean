import Mathlib

/-!
# IPhO 2026, Problem 4 (E1), Part A.5 — Constant-volume thermal pressure coefficient

Answer-blind formalization of subquestion E1-A.5 (0.7 pts):

> The thermal pressure coefficient at constant volume is defined by the
> relationship `β₀ = (1 / P₀) * (ΔP / ΔT)`, where `P₀` is the pressure of the
> system at the reference temperature `T₀` as indicated in the reference
> constants and values.  **A5.** Determine the value of the coefficient `β₀`
> for air.

## Experimental context (Part A: isochoric process of an ideal gas)

* The sealed trapped air column **CA** in the inner cylinder **IC** obeys the
  ideal gas equation of state `P * V = n * R * T` (equation (1) of the
  statement), where `R` is the universal gas constant.
* Propylene glycol (**PG**) is introduced into **IC** to the height
  `h = 4.5 cm` and valves **D** and **E** are closed, so the volume `V` of
  the **CA** is fixed (isochoric / isovolumetric process).
* The time-averaged density of ambient air in Bucaramanga,
  `ρ = 1.12 kg/m³`, together with the cylinder dimensions of Figure 17, is
  used in part A.1 to determine the mass `m`, the number of moles `n`, and
  the number of molecules `N` of the **CA**; here `n` enters only as a fixed
  sealed amount.
* The outer cylinder (**OC**) water bath is heated while the pressure `P` of
  the **CA** is recorded as a function of its temperature `T` (part A.2), and
  the data are plotted linearly (part A.3).  The slope `ΔP / ΔT` of that
  isochoric `P`-versus-`T` plot is the quantity entering equation (2).

## Answer-free statement design

The official value of `β₀` is withheld.  Following the blind policy, the
theorem signature introduces a result variable `b` of inverse-temperature
role and an answer-free solution predicate `IsThermalPressureCoefficient`
built from the defining relation `β₀ = (1 / P₀) * (ΔP / ΔT)` and the
secant slope of the recorded data, then asserts existence and uniqueness.
Later proofs construct the witness (e.g. `1 / T₀` on the Kelvin scale, from
Charles's law) without it appearing here.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4A5

/-- Experimental constants of Part A of Problem E1: the sealed air column
(CA), the universal gas constant appearing in equation (1), and the
reference values used in equation (2). -/
structure IsochoricAirData where
  /-- Universal gas constant `R` in `PV = nRT`. -/
  R : ℝ
  /-- Number of moles `n` of air sealed in the CA (determined in part A.1
  from `ρ = 1.12 kg/m³`, the Figure 17 geometry, and `h = 4.5 cm`). -/
  n : ℝ
  /-- Fixed volume `V` of the CA during the isochoric process (PG at
  `h = 4.5 cm`, valves **D** and **E** closed). -/
  V : ℝ
  /-- Reference temperature `T₀` named in equation (2), on the absolute
  (Kelvin) scale. -/
  T₀ : ℝ
  /-- Sealed amount of gas is positive. -/
  n_pos : 0 < n
  /-- Fixed CA volume is positive. -/
  V_pos : 0 < V
  /-- Reference absolute temperature is positive. -/
  T₀_pos : 0 < T₀

namespace IsochoricAirData

variable (D : IsochoricAirData)

/-- The reference pressure `P₀`: the pressure of the system at the reference
temperature `T₀`, as fixed by the ideal gas equation of state (1), `P₀ *
V = n * R * T₀`. -/
noncomputable def referencePressure : ℝ :=
  D.n * D.R / D.V * D.T₀

/-- Predicate expressing that `P` is the pressure `P(T)` of the CA at
temperature `T` as recorded in part A.2: every recorded pair obeys the
ideal gas equation of state (1) at the fixed volume of the isochoric
process. -/
def ObeysIdealGasLaw (P : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, P T * D.V = D.n * D.R * T

/-- The constant-volume thermal pressure coefficient of equation (2): a real
number `b` of inverse-temperature role is the coefficient `β₀` when it
equals `(1 / P₀) * (ΔP / ΔT)`, where `ΔP / ΔT` is the secant slope between
any two distinct recorded points of the isochoric pressure–temperature data
(constant on the straight-line plot of part A.3), and `P₀` is the pressure
of the system at the reference temperature `T₀`. -/
def IsThermalPressureCoefficient (P : ℝ → ℝ) (b : ℝ) : Prop :=
  (∀ T₁ T₂ : ℝ, T₁ ≠ T₂ → b = (P T₂ - P T₁) / (T₂ - T₁) / D.referencePressure)

/-- The reference pressure is the recorded pressure at the reference
temperature, `P₀ = P T₀`. -/
theorem referencePressure_eq (hP : D.ObeysIdealGasLaw P) (hR : D.R ≠ 0) :
    D.referencePressure = P D.T₀ := by
  have h1 := hP D.T₀
  have hV : D.V ≠ 0 := ne_of_gt D.V_pos
  unfold referencePressure
  rw [div_mul_eq_mul_div, eq_comm, ← h1]
  exact (mul_div_cancel_right₀ _ hV).symm

/-- Under the ideal gas law at fixed volume the secant slope `ΔP / ΔT` is
the same between any two distinct recorded temperatures: the plot of part
A.3 is a straight line. -/
theorem secant_slope_const (hP : D.ObeysIdealGasLaw P) (hR : D.R ≠ 0)
    {T₁ T₂ : ℝ} (h₁₂ : T₁ ≠ T₂) :
    (P T₂ - P T₁) / (T₂ - T₁) = D.n * D.R / D.V := by
  have h1 := hP T₁
  have h2 := hP T₂
  have hV : D.V ≠ 0 := ne_of_gt D.V_pos
  have h21 : T₂ - T₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₂)
  field_simp
  linear_combination h2 - h1

/-- The coefficient of equation (2) re-expressed at the reference point:
`β₀ = (1 / P₀) * (ΔP / ΔT) = P₀⁻¹ * (n * R / V)`. -/
theorem coefficient_eq_slope_div_referencePressure (hP : D.ObeysIdealGasLaw P)
    (hR : D.R ≠ 0) {b : ℝ} (hb : D.IsThermalPressureCoefficient P b)
    {T₁ T₂ : ℝ} (h₁₂ : T₁ ≠ T₂) :
    b = (D.n * D.R / D.V) / D.referencePressure := by
  have key := hb T₁ T₂ h₁₂
  rw [key]
  exact congrArg (· / D.referencePressure) (D.secant_slope_const hP hR h₁₂)

/-- **E1-A5, answer-free characterization.** Assuming the sealed
constant-volume sample of air obeys the ideal gas equation of state with a
nonzero gas constant, there exists a unique real number `β₀` satisfying the
defining relation `β₀ = (1 / P₀) * (ΔP / ΔT)` of equation (2).  The
explicit value (e.g. `β₀ = 1 / T₀` on the absolute scale) is deliberately
kept out of this statement; the later proof constructs it as the witness. -/
theorem thermal_pressure_coefficient_exists_unique (hP : D.ObeysIdealGasLaw P)
    (hR : D.R ≠ 0) : ∃! b : ℝ, D.IsThermalPressureCoefficient P b := by
  refine ⟨D.n * D.R / D.V / D.referencePressure, ?_, ?_⟩
  · intro T₁ T₂ h₁₂
    rw [D.secant_slope_const hP hR h₁₂]
  · intro b hb
    exact D.coefficient_eq_slope_div_referencePressure hP hR hb
      D.T₀_pos.ne'

end IsochoricAirData

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4A5
