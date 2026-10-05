import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Problem 4, Part C.6 — Effective wall
# thermal resistance `R_Th` from the C.5 graph

Answer-blind formalization of subquestion E1-C.6 (1.6 pts):

> **C6.** Determine the value of `R_Th` from the graph constructed in C5.

## Experimental context (Part C: heat conduction)

* Water in the inner cylinder (**IC**, water level `h = 10 cm`) and water in
  the outer cylinder (**OC**, water level `h = 15 cm`, initially heated to
  `65 °C` and homogenized with the pump) exchange heat radially through the
  acrylic cylindrical wall separating them; `T_IC` and `T_OC` are recorded as
  functions of time (parts C.1–C.2, geometry of Figure 17).
* Heat conduction through the solid wall follows the statement's
  equation (4),

      ΔQ / Δt = (1 / R_Th) · (T_OC - T_IC),

  where `ΔQ` is the heat received by the water in the IC through the wall
  during the time interval `Δt`, and `R_Th` is the effective thermal
  resistance of the wall, which depends on the material and geometry of the
  wall separating IC and OC.
* With variables measured a finite number of times, equation (4) is expressed
  as the statement's equation (5),

      (T_{IC,j} - T_{IC,j-1}) / (t_j - t_{j-1})  ∝  T̄_OC - T̄_IC,

  where `j` is the measurement number and `T̄` are the average temperatures
  at each cylinder during the interval `t_{j-1}` to `t_j`.  The
  proportionality constant is `1 / (m_IC c_w R_Th)`: the heat received by the
  IC in the interval raises its temperature by `ΔQ = m_IC c_w ΔT_IC`
  (calorimetry; the apparatus heat capacity is ignored as instructed), which
  inserted into equation (4) gives the affine law

      rate_j = (T̄_OC,j - T̄_IC,j) / (m_IC c_w R_Th).
* Part C.5 plots the finite-difference rate on the left-hand side of
  equation (5) against the interval-mean temperature difference on the
  right-hand side — a straight line through the origin whose slope carries
  `R_Th` (natural-language prerequisite; the graph construction itself is not
  imported here).
* The plate's equation (6) — Fourier's law for radial heat conduction through
  a slim cylindrical wall, `dQ/dt = -λ A dT/dr` — underlies the effective
  resistance and is used in part C.7 together with the dimensions of
  Figure 17; it is recorded here as the governing conduction law of the
  setup.

## Answer-free statement design

The official value of `R_Th` is withheld.  Following the blind policy, the
theorem signature introduces a result variable `R` of thermal-resistance
role and an answer-free solution predicate `IsWallThermalResistance`, built
from the calorimetric law for the IC water and the conduction model of
equation (4) — equivalently, from the affine slope law

    ∀ j ≥ 1,  rate_j = (abscissa_j) / (m_IC · c_w · R)

obeyed by every measurement interval (the C.5 graph is one representative
extraction of this slope) — and asserts existence and uniqueness.  The
witness (`(m_IC c_w · slope)⁻¹` of the best-fit C.5 line) is deliberately
kept out of the statement.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4C6

variable {ι : Type*}

/-- The type class of time-monotone measurement regimes: the stopwatch
readings of temporally ordered measured points are increasing, so the
denominators `Δt` of the finite-difference rates of statement equation (5)
are nonzero.  This holds for naturals, integers, consecutive-number
enumerations, or any set of consecutive indices. -/
class TimeOrderMono [LinearOrder ι] (t : ι → ℝ) : Prop where
  /-- The time of the successor measurement exceeds that of the predecessor:
  index order and time order agree. -/
  lt {i j : ι} : i < j → t i < t j

/-- Experimental parameters of Part C of Problem E1: the calorimetric
content of the IC (neglecting the apparatus heat capacity, as instructed
for C.6) and the raw series recorded in C.1. -/
structure HeatConductionData (ι : Type*) where
  /-- Mass `m_IC` of the water in the inner cylinder (from the IC water
  level `h = 10 cm` and the Figure 17 geometry). -/
  m_IC : ℝ
  /-- Specific heat capacity `c_w` of water. -/
  c_w : ℝ
  /-- Recorded measurement times `t_i` (C.1). -/
  t : ι → ℝ
  /-- Recorded internal (IC) water temperatures `T_IC` (C.1). -/
  T_IC : ι → ℝ
  /-- Recorded external (OC) water temperatures `T_OC` (C.1). -/
  T_OC : ι → ℝ
  /-- IC water mass is positive. -/
  m_IC_pos : 0 < m_IC
  /-- Specific heat capacity of water is positive. -/
  c_w_pos : 0 < c_w

namespace HeatConductionData

variable (D : HeatConductionData ι)

/-- The calorimetric factor `m_IC · c_w` of the IC water: the heat `ΔQ`
received through the wall in an interval raises the IC temperature by
`ΔQ / (m_IC c_w)`, with the apparatus heat capacity ignored as instructed. -/
noncomputable def calorimetricFactor : ℝ := D.m_IC * D.c_w

/-- The rate-of-heating ordinate of the C.5 graph (statement's equation (5),
left-hand side): the finite difference of the recorded IC temperature over
the interval from `i₀` to `i₁`,
`(T_IC,i₁ - T_IC,i₀) / (t_i₁ - t_i₀)`. -/
noncomputable def rate (i₀ i₁ : ι) : ℝ :=
  (D.T_IC i₁ - D.T_IC i₀) / (D.t i₁ - D.t i₀)

/-- The interval-mean temperature difference `T̄_OC - T̄_IC` on the
interval from `i₀` to `i₁`: the abscissa of the C.5 graph (statement's
equation (5), right-hand side). -/
noncomputable def meanDiff (i₀ i₁ : ι) : ℝ :=
  (D.T_OC i₀ + D.T_OC i₁) / 2 - (D.T_IC i₀ + D.T_IC i₁) / 2

/-- Invertibility of the ordinate denominator `Δt = t_j - t_{j-1}` for every
consecutive measurement pair `i₀ < i₁`, valid in the physical regime (the
stopwatch records distinct, increasing times). -/
theorem time_diff_ne_zero [LinearOrder ι] [TimeOrderMono D.t] {i₀ i₁ : ι}
    (h : i₀ < i₁) : D.t i₁ - D.t i₀ ≠ 0 :=
  ne_of_gt (sub_pos.mpr (TimeOrderMono.lt h))

/-- The affine slope law extracted from the C.5 graph: the finite-difference
rates and interval-mean temperature differences of every consecutive
measurement pair `i₀ < i₁` fall on a straight line through the origin with
slope `s`, i.e. `rate i₀ i₁ = s * meanDiff i₀ i₁`.  This is the graphical
content of the statement's equation (5); physically `s = 1 / (m_IC c_w
R_Th)`. -/
def IsC5Slope [LinearOrder ι] (s : ℝ) : Prop :=
  ∀ {i₀ i₁ : ι}, i₀ < i₁ → D.rate i₀ i₁ = s * D.meanDiff i₀ i₁

/-- The thermal-resistance law of the statement's equation (4), finite
difference form: the heat that raises the IC water by `ΔT_IC` in the interval
`Δt` — `ΔQ = m_IC c_w ΔT_IC` (calorimetry, apparatus heat capacity ignored)
—— is conducted through the wall at mean rate
`ΔQ / Δt = (T̄_OC - T̄_IC) / R`.  Reduces on clearing denominators to the C.5
slope law with slope `1 / (m_IC c_w R)`. -/
def SatisfiesThermalResistanceLaw [LinearOrder ι] (R : ℝ) : Prop :=
  ∀ {i₀ i₁ : ι} (_ : i₀ < i₁),
    D.calorimetricFactor * (D.T_IC i₁ - D.T_IC i₀) * R
      = (D.meanDiff i₀ i₁) * (D.t i₁ - D.t i₀)

/-- **Answer-free solution predicate for C.6.** A real number `R` of
thermal-resistance role is the effective wall thermal resistance `R_Th`
determined from the C.5 graph iff it is positive and the recorded
finite-difference data satisfy the conduction law of equation (4) with that
resistance — equivalently, iff the C.5 plot is affine through the origin with
slope `1 / (m_IC c_w R)`. -/
def IsWallThermalResistance [LinearOrder ι] (R : ℝ) : Prop :=
  0 < R ∧ D.SatisfiesThermalResistanceLaw R

/-- Equation (4) with resistance `R` is exactly the C.5 slope law with slope
`1 / (m_IC c_w R)`: the resistance is the reciprocal of the C.5 slope
rescaled by the calorimetric factor `m_IC c_w`. -/
theorem satisfies_thermal_resistance_law_iff_slope [LinearOrder ι]
    [TimeOrderMono D.t] {R : ℝ} (hR : R ≠ 0) :
    D.SatisfiesThermalResistanceLaw R ↔
      D.IsC5Slope (D.calorimetricFactor * R)⁻¹ := by
  have hm : D.m_IC ≠ 0 := ne_of_gt D.m_IC_pos
  have hc : D.c_w ≠ 0 := ne_of_gt D.c_w_pos
  have hcf : D.calorimetricFactor ≠ 0 := mul_ne_zero hm hc
  have hcfR : D.calorimetricFactor * R ≠ 0 := mul_ne_zero hcf hR
  constructor
  · -- Equation (4) implies the affine C.5 slope law with slope `1/(m_IC c_w R)`.
    intro hlaw i₀ i₁ hij
    have hΔt : D.t i₁ - D.t i₀ ≠ 0 := D.time_diff_ne_zero hij
    have h := hlaw hij
    simp only [rate]
    rw [div_eq_iff hΔt]
    -- `(T_IC i₁ - T_IC i₀) = (m_IC c_w · R)⁻¹ · T̄diff · Δt` follows from
    -- `m_IC c_w · ΔT_IC · R = T̄diff · Δt` on cancelling `m_IC c_w · R ≠ 0`.
    apply mul_left_cancel₀ hcfR
    have rhs_eq : (D.calorimetricFactor * R)
        * ((D.calorimetricFactor * R)⁻¹ * D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀))
        = D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀) := by
      calc (D.calorimetricFactor * R)
          * ((D.calorimetricFactor * R)⁻¹ * D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀))
          = ((D.calorimetricFactor * R) * (D.calorimetricFactor * R)⁻¹)
              * (D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀)) := by ring
        _ = 1 * (D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀)) := by
            rw [mul_inv_cancel₀ hcfR]
        _ = D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀) := one_mul _
    rw [rhs_eq]
    linear_combination h
  · -- The affine C.5 slope law implies equation (4) at resistance `R`.
    intro hslope i₀ i₁ hij
    have hΔt : D.t i₁ - D.t i₀ ≠ 0 := D.time_diff_ne_zero hij
    have h := hslope hij
    simp only [rate] at h
    rw [div_eq_iff hΔt] at h
    -- Scale the slope law by `m_IC c_w · R` and clear the reciprocal.
    have hscaled := congrArg (fun x => (D.calorimetricFactor * R) * x) h
    -- `(m_IC c_w R)` factors out of both sides; cancelling reciprocals gives
    -- an equation only up to the ring identity, so clear the reciprocal first.
    have rhs_eq : (D.calorimetricFactor * R)
        * ((D.calorimetricFactor * R)⁻¹ * D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀))
        = D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀) := by
      calc (D.calorimetricFactor * R)
          * ((D.calorimetricFactor * R)⁻¹ * D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀))
          = ((D.calorimetricFactor * R) * (D.calorimetricFactor * R)⁻¹)
              * (D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀)) := by ring
        _ = 1 * (D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀)) := by
            rw [mul_inv_cancel₀ hcfR]
        _ = D.meanDiff i₀ i₁ * (D.t i₁ - D.t i₀) := one_mul _
    -- `hscaled : (m_IC c_w R)·ΔT_IC = (m_IC c_w R)·((m_IC c_w R)⁻¹ T̄diff)·Δt`.
    -- Rewrite its right side via `rhs_eq` and undo the common factor.
    rw [rhs_eq] at hscaled
    -- `hscaled : (m_IC c_w)·R·ΔT_IC = T̄diff·Δt`; rearrange to equation (4).
    linear_combination hscaled

/-- The slope of the C.5 line is unique: any two slopes making every plotted
point collinear with the origin agree, provided at least one plotted point
has a nonzero abscissa (a non-degenerate graph). -/
theorem c5_slope_unique [LinearOrder ι] {s₁ s₂ : ℝ}
    (h₁ : D.IsC5Slope s₁) (h₂ : D.IsC5Slope s₂)
    (h : ∃ i₀ i₁ : ι, i₀ < i₁ ∧ D.meanDiff i₀ i₁ ≠ 0) :
    s₁ = s₂ := by
  obtain ⟨i₀, i₁, hij, hmd⟩ := h
  -- Both slopes reproduce the same ordinate `rate i₀ i₁` over the same
  -- nonzero abscissa `meanDiff i₀ i₁`; cancel the abscissa.
  have e₁ := h₁ hij
  have e₂ := h₂ hij
  have : s₁ * D.meanDiff i₀ i₁ = s₂ * D.meanDiff i₀ i₁ := by rw [← e₁, ← e₂]
  exact mul_right_cancel₀ hmd this

/-- If the recorded data obey the statement's equation (4) with a positive
effective wall resistance, then the resistance extracted from the C.5 graph
is unique whenever the graph is non-degenerate (at least one plotted point
has a nonzero abscissa). -/
theorem wall_thermal_resistance_unique [LinearOrder ι] [TimeOrderMono D.t]
    {R₁ R₂ : ℝ} (h₁ : D.IsWallThermalResistance R₁)
    (h₂ : D.IsWallThermalResistance R₂)
    (h : ∃ i₀ i₁ : ι, i₀ < i₁ ∧ D.meanDiff i₀ i₁ ≠ 0) :
    R₁ = R₂ := by
  obtain ⟨h₁pos, h₁law⟩ := h₁
  obtain ⟨h₂pos, h₂law⟩ := h₂
  have hR₁ : R₁ ≠ 0 := ne_of_gt h₁pos
  have hR₂ : R₂ ≠ 0 := ne_of_gt h₂pos
  -- Both readings give the same C.5 slope, hence coincide.
  have h₁slope : D.IsC5Slope (D.calorimetricFactor * R₁)⁻¹ :=
    (D.satisfies_thermal_resistance_law_iff_slope hR₁).mp h₁law
  have h₂slope : D.IsC5Slope (D.calorimetricFactor * R₂)⁻¹ :=
    (D.satisfies_thermal_resistance_law_iff_slope hR₂).mp h₂law
  have hslope := D.c5_slope_unique h₁slope h₂slope h
  -- `(m_IC c_w R₁)⁻¹ = (m_IC c_w R₂)⁻¹` with `m_IC c_w R_i ≠ 0` gives `R₁ = R₂`.
  have hm : D.m_IC ≠ 0 := ne_of_gt D.m_IC_pos
  have hc : D.c_w ≠ 0 := ne_of_gt D.c_w_pos
  have hcf : D.calorimetricFactor ≠ 0 := mul_ne_zero hm hc
  have : D.calorimetricFactor * R₁ = D.calorimetricFactor * R₂ := by
    rwa [inv_inj] at hslope
  exact mul_left_cancel₀ hcf this

/-- Conduction of Fourier's law (equation (6)) through a cylindrical wall:
the effective wall resistance is the radial integral of the local resistance
`dr / (λ A(r))`, with `A(r) = 2π r L` the lateral area of the slim
cylindrical shell of height `L` traversed by the radial heat current.
Recorded as the geometric content of the plate's equation (6) for part C.7. -/
noncomputable def cylindricalWallResistance (lam L r_in r_out : ℝ) : ℝ :=
  ∫ r in Set.Ioo r_in r_out, (2 * Real.pi * r * L * lam)⁻¹

/-- **Fourier's law for radial conduction (statement's equation (6)).**
For a heat current `dQ/dt` crossing a slim cylindrical shell of height `L`
and conductivity `lam` at radius `r`, the radial temperature gradient
satisfies `dQ/dt = -2π r L λ dT/dr`, i.e.
`radialGradient P r = -P / (2π r L λ)`.  Integrated from `r_in` to `r_out`
this reproduces the effective wall resistance of equation (4) (part C.7). -/
def SatisfiesFourierLawRadial (dQdt lam L : ℝ) (radialGradient : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, radialGradient r = - dQdt / (2 * Real.pi * r * L * lam)

/-- **E1-C6, answer-free characterization.** Assuming the recorded IC/OC
temperature series obeys the conduction model of equation (4) — the heat
received by the IC water in each interval is `ΔQ = m_IC c_w ΔT_IC`
(apparatus heat capacity ignored) and is conducted through the wall at mean
rate `(T̄_OC - T̄_IC) / R_Th` — there exists a unique effective wall thermal
resistance `R_Th` determined by the C.5 graph, whenever the graph is
affine through the origin with positive slope `s` and is non-degenerate.
The explicit witness — `(m_IC c_w s)⁻¹`, the reciprocal of the C.5 slope
times the IC calorimetric factor — is deliberately kept out of this
statement; the later proof constructs it. -/
theorem wall_thermal_resistance_exists_unique [LinearOrder ι]
    [TimeOrderMono D.t] {s : ℝ} (hs : 0 < s) (hsl : D.IsC5Slope s)
    (hdeg : ∃ i₀ i₁ : ι, i₀ < i₁ ∧ D.meanDiff i₀ i₁ ≠ 0) :
    ∃! R : ℝ, D.IsWallThermalResistance R := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hm : D.m_IC ≠ 0 := ne_of_gt D.m_IC_pos
  have hc : D.c_w ≠ 0 := ne_of_gt D.c_w_pos
  have hcf : D.calorimetricFactor ≠ 0 := mul_ne_zero hm hc
  have hcfs : D.calorimetricFactor * s ≠ 0 := mul_ne_zero hcf hs'
  have hwitne : (D.calorimetricFactor * s)⁻¹ ≠ 0 := inv_ne_zero hcfs
  -- The graph's slope is the rescaled reciprocal of the witness
  -- `(m_IC c_w · s)⁻¹`, i.e. `s = (m_IC c_w · (m_IC c_w · s)⁻¹)⁻¹`.
  have hinv : D.calorimetricFactor * (D.calorimetricFactor * s)⁻¹ = s⁻¹ := by
    calc D.calorimetricFactor * (D.calorimetricFactor * s)⁻¹
        = s⁻¹ * (D.calorimetricFactor * D.calorimetricFactor⁻¹) := by
          rw [mul_inv_rev]; ring
      _ = s⁻¹ * 1 := by rw [mul_inv_cancel₀ hcf]
      _ = s⁻¹ := mul_one _
  -- The witness obeys the thermal-resistance law of equation (4):
  -- its rescaled reciprocal slope is exactly `s`.
  have hwitslope : D.IsC5Slope
      (D.calorimetricFactor * (D.calorimetricFactor * s)⁻¹)⁻¹ := by
    rw [hinv, inv_inv]
    exact hsl
  refine ⟨((D.calorimetricFactor * s)⁻¹), ?_, ?_⟩
  · constructor
    · -- The extracted resistance is positive.
      exact inv_pos.mpr (mul_pos (mul_pos D.m_IC_pos D.c_w_pos) hs)
    · -- It obeys the thermal-resistance law of equation (4).
      exact (D.satisfies_thermal_resistance_law_iff_slope hwitne).mpr hwitslope
  · -- Any other determination of the resistance from the graph coincides
    -- with the witness, by uniqueness of the C.5 slope.
    intro R' hR'
    obtain ⟨hR'pos, hR'law⟩ := hR'
    have hR' : R' ≠ 0 := ne_of_gt hR'pos
    have hR'slope : D.IsC5Slope (D.calorimetricFactor * R')⁻¹ :=
      (D.satisfies_thermal_resistance_law_iff_slope hR').mp hR'law
    have hslope_eq := D.c5_slope_unique hR'slope hwitslope hdeg
    -- `(m_IC c_w R')⁻¹ = (m_IC c_w (m_IC c_w s)⁻¹)⁻¹` gives `R' = (m_IC c_w s)⁻¹`.
    have : D.calorimetricFactor * R'
        = D.calorimetricFactor * (D.calorimetricFactor * s)⁻¹ := by
      rwa [inv_inj] at hslope_eq
    exact mul_left_cancel₀ hcf this

end HeatConductionData

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4C6
