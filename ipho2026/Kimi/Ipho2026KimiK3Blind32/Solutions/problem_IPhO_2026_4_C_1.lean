import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Part C.1 — answer-blind formalization

## Physical setup (Part C: heat conduction through the acrylic wall)

The experimental apparatus consists of water held in an **inner cylinder (IC)**
and water held in an **outer cylinder (OC)**, separated by a slim
**acrylic cylindrical wall** (geometry per the exam's Figure 17).  Heat is
exchanged between the two water bodies **radially through the wall**: the
water in the OC is heated to about `65 °C` and homogenized with the pump, the
water in the IC starts near room temperature, and as time runs the IC water
warms while the OC water cools.  Both water bodies are kept effectively
homogeneous (stirred / pumped), so each is described by a single
time-dependent temperature:

* `T_IC t` — the (internal) water temperature of the IC (°C) at time `t`;
* `T_OC t` — the (external) water temperature of the OC (°C) at time `t`.

The exam postulates the **effective heat-flow model**

    dQ/dt = (T_OC − T_IC) / R_Th                              (4)

where `ΔQ` is the heat received by the **water in the IC** through the wall
during the time interval `Δt`, and `R_Th` is the **effective thermal
resistance** of the wall (units K·J⁻¹·s, i.e. K/W), which depends on the
material and geometry of the wall separating IC and OC.  Microscopically the
transport is **radial Fourier conduction** through the cylindrical wall,

    dQ/dt = −λ · A · dT/dr                                     (6)

with `λ` the thermal conductivity of acrylic, `A` the relevant wall area, and
`dT/dr` the radial temperature gradient across the wall.  For the slim
cylindrical wall the integrated radial profile turns (6) into the effective
linear law (4), with `R_Th` carrying the full wall geometry
(`R_Th ∝ ln(r_outer / r_inner) / (2 π λ L)` for a cylinder of length `L`;
no closed form is asserted here).

## Procedure boundary conditions (stated in the exam)

1. The OC water level is set to `h = 15 cm` (so `h_OC = 0.15 m`).
2. The OC water is heated and homogenized to about `65 °C`, hence
   `T_OC 0 = 65 °C` at the stopwatch start.
3. The IC water level is set to `h = 10 cm` (so `h_IC = 0.10 m`) and the
   stopwatch is started: `t = 0` marks the start of the recording.

## Current subquestion (E1-C.1, 1.0 pt)

> Record the internal temperature `T_IC` and the external temperature `T_OC`
> as a function of time `t`.

The requested deliverable is the **measured time record** itself: the two
temperature–time functions sampled by the experiment.  The official measured
data are withheld deliberately, so this is a *specification*, not a solution
archive: we state that there exists an admissible recorded pair of
temperature–time curves obeying the stated boundary conditions and the
governing heat-exchange laws.  No measured value, no closed form, no
time constant, and no numerical table appears in any theorem signature.

## Answer-free design

Because this is a "record as a function of time" subquestion there is no
single official scalar to withhold.  Guided by the answer-free policy, we
introduce a candidate record `(T_IC, T_OC) : ℝ → ℝ × ℝ`, define a
**`Solution` predicate** from the setup, the governing laws, the stated
initial/boundary conditions, and the physically evident qualitative regime of
the record (the IC warms from below, the OC cools from above, the driving
temperature difference `T_OC − T_IC` stays nonnegative through the recorded
window), and assert **existence** of such a record.  The witness data are
not exhibited.
-/

namespace IPhO_2026_4
namespace PartC1

/-- **Apparatus and material parameters (E1, Part C), Figure 17.**

The immutable physical data of the heat-conduction experiment:

* `r_in`, `r_out` — inner and outer radii (m) of the slim acrylic cylindrical
  wall separating the IC and OC water (geometry per Figure 17);
* `h_IC`, `h_OC` — the water levels (m) set by the procedure: `h_IC` is the
  IC water height (`10 cm`) and `h_OC` the OC water height (`15 cm`);
* `λ` — thermal conductivity (W·m⁻¹·K⁻¹) of acrylic;
* `c_w` — specific heat capacity (J·kg⁻¹·K⁻¹) of water;
* `ρ_w` — density (kg·m⁻³) of water;
* `R_Th` — the **effective thermal resistance** (K/W) of the wall, which
  "depends on the material and geometry of the wall" (K·m/W·geometry),
  postulated by the exam's model (4).

The geometric dimensions of Figure 17 are recorded abstractly (the figure is
not re-typeset here); only their positivity is bundled. -/
structure Apparatus where
  /-- Inner radius of the acrylic cylindrical wall (m), positive. -/
  r_in : ℝ
  /-- Outer radius of the acrylic cylindrical wall (m), positive. -/
  r_out : ℝ
  /-- IC water-column height set by the procedure, `h_IC = 0.10 m`. -/
  h_IC : ℝ
  /-- OC water-column height set by the procedure, `h_OC = 0.15 m`. -/
  h_OC : ℝ
  /-- Thermal conductivity `λ` of acrylic (W·m⁻¹·K⁻¹), positive. -/
  lam : ℝ
  /-- Specific heat capacity `c_w` of water (J·kg⁻¹·K⁻¹), positive. -/
  c_w : ℝ
  /-- Density `ρ_w` of water (kg·m⁻³), positive. -/
  rho_w : ℝ
  /-- Effective thermal resistance `R_Th` of the wall (K·J⁻¹·s, i.e. K/W),
  positive; set by the wall material and geometry. -/
  R_Th : ℝ
  r_in_pos : 0 < r_in
  r_out_pos : 0 < r_out
  h_IC_pos : 0 < h_IC
  h_OC_pos : 0 < h_OC
  lam_pos : 0 < lam
  c_w_pos : 0 < c_w
  rho_w_pos : 0 < rho_w
  R_Th_pos : 0 < R_Th

/-- **Heat-capacity inventory.**
The heat capacity `(J/K)` of a homogeneous water column of density `ρ_w`,
specific heat `c_w`, filling a cylinder of cross-sectional area `A` to height
`h`:  `C = ρ_w · c_w · A · h`.

For the IC water the cross section is the inner cross section `π r_in²`;
for the (annular) OC water it is the occluding annulus area, supplied
abstractly through the caller's use of the appropriate `A`. -/
noncomputable def Apparatus.waterHeatCapacity (W : Apparatus) (A h : ℝ) : ℝ :=
  W.rho_w * W.c_w * A * h

/-- **Governing law — effective heat-flow model, equation (4).**
The instantaneous heat current (J/s) received by the **water in the IC**
through the wall, when the external (OC) temperature is `T_OC` and the
internal (IC) temperature is `T_IC`, driven through the effective thermal
resistance `R_Th`:

    dQ/dt = (T_OC − T_IC) / R_Th. -/
noncomputable def Apparatus.heatFlowIntoIC (W : Apparatus) (T_OC T_IC : ℝ) : ℝ :=
  (T_OC - T_IC) / W.R_Th

/-- **Governing law — radial Fourier conduction, equation (6).**
The local radial conductive heat current (J/s) through a cylindrical area
`A` of a wall of thermal conductivity `lam`, sustaining a radial temperature
gradient `dT_dr`:

    dQ/dt = −λ · A · dT_dr.

This is the microscopic form of which `heatFlowIntoIC` (equation 4) is the
integrated effective form for the slim cylindrical wall. -/
noncomputable def Apparatus.fourierHeatFlow (W : Apparatus) (A dT_dr : ℝ) : ℝ :=
  -W.lam * A * dT_dr

/-- **A candidate C.1 record.**  A pair of real temperature–time functions:

* `T_IC : ℝ → ℝ` — the recorded internal (IC) water temperature (°C);
* `T_OC : ℝ → ℝ` — the recorded external (OC) water temperature (°C);

each sampled as a function of the elapsed time `t` (s) from the stopwatch
start.  (In the laboratory these are *sampled* finite tables; here the record
is modeled as a time series on the real line, with the sampled window
constrained separately.) -/
structure TemperatureRecord where
  /-- Recorded internal (IC) water temperature as a function of time (°C). -/
  T_IC : ℝ → ℝ
  /-- Recorded external (OC) water temperature as a function of time (°C). -/
  T_OC : ℝ → ℝ

namespace TemperatureRecord



/-- **Stated initial condition: OC pre-heated and homogenized.**
At the stopwatch start the OC water has been heated and homogenized to
`65 °C`, as instructed by the procedure.  The Celsius temperature `65` is
used because the exam records temperatures in `°C`; differences agree with
Kelvin differences. -/
def InitialOC (R : TemperatureRecord) : Prop :=
  R.T_OC 0 = 65

/-- **Driving difference.**  The instantaneous temperature difference
`T_OC t − T_IC t` (K, equivalently °C-difference) that drives the radial
heat current into the IC through equation (4). -/
def drivingDifference (R : TemperatureRecord) (t : ℝ) : ℝ :=
  R.T_OC t - R.T_IC t

/-- **Heat budget consistency for the IC water.**
The record is consistent with the first law for the IC water over the
recorded window `[0, t_fin]`: the rate of change of the IC internal energy,
`C_IC · dT_IC/dt`, equals the effective heat current (4) into the IC,
where `C_IC = waterHeatCapacity W (π r_in²) h_IC` is the heat capacity of
the IC water column (apparatus heat capacity ignored where instructed).

Because the record is only known through sampled measurements, we express
this (in differential / fundamental-theorem form) as: *there exists* a heat-current function `q` on
`[0, t_fin]` equal pointwise to the effective heat flow
`(T_OC − T_IC)/R_Th` and whose value at each time is the rate
`C_IC · dT_IC/dt`, i.e. `deriv (C_IC · T_IC) = q`.  This is the differential form of
`C_IC · dT_IC/dt = (T_OC − T_IC)/R_Th`, equation (4) fed into the IC water. -/
def ObeysICHeatBudget (W : Apparatus) (R : TemperatureRecord) (C_IC : ℝ) : Prop :=
  ∀ t_fin : ℝ, 0 ≤ t_fin →
    ∃ q : ℝ → ℝ,
      (∀ t ∈ Set.Icc 0 t_fin, q t = W.heatFlowIntoIC (R.T_OC t) (R.T_IC t)) ∧
      ∀ t ∈ Set.Icc 0 t_fin, deriv (fun s ↦ C_IC * R.T_IC s) t = q t

/-- **Monotone approach (qualitative regime of the recorded window).**
Throughout the recorded window the OC water cools from above and the IC
water warms from below, with the driving difference nonnegative:
`0 ≤ T_OC t − T_IC t`.  This is the physically observed regime of the C.1
record (no overshoot inside the measurement window); the equilibrium crossing
is the subject of later subquestions and is *not* imposed here. -/
def IsCoApproaching (R : TemperatureRecord) (t_fin : ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 t_fin, 0 ≤ R.drivingDifference t) ∧
  (∀ t ∈ Set.Icc 0 t_fin, R.T_IC 0 ≤ R.T_IC t) ∧
  (∀ t ∈ Set.Icc 0 t_fin, R.T_OC t ≤ R.T_OC 0)

/-- **`Solution` predicate for C.1 (answer-free).**
A pair `(R, t_fin)` of a recorded temperature–time curve and a positive
recording duration realizes the deliverable of subquestion C.1 — "record
`T_IC` and `T_OC` as a function of time `t`" — when:

1. the recording duration is positive (`0 < t_fin`);
2. the stated starting condition `T_OC 0 = 65 °C` holds;
3. the record obeys the IC heat budget driven by the effective model (4),
   with the IC water heat capacity set by the apparatus geometry;
4. the recorded window is in the physically observed co-approaching regime
   (IC warming from below, OC cooling from above, nonnegative driving
   difference).

No measured value, no closed form, and no time constant appears. -/
def Solution (W : Apparatus) (R : TemperatureRecord) (t_fin : ℝ) : Prop :=
  0 < t_fin ∧
  InitialOC R ∧
  ObeysICHeatBudget W R
    (W.waterHeatCapacity (Real.pi * W.r_in ^ 2) W.h_IC) ∧
  IsCoApproaching R t_fin

end TemperatureRecord

/-- **Target theorem (answer-free, C.1).**
For the stated apparatus — water in the IC and OC exchanging heat radially
through the acrylic cylindrical wall via the effective model (4) with
positive thermal resistance `R_Th`, the OC pre-heated and homogenized to
`65 °C`, the IC initially below the OC, and the wall obeying radial Fourier
conduction (6) — **there exists** an admissible recorded pair of
temperature–time functions `T_IC, T_OC : ℝ → ℝ` over a positive recording
duration realizing the C.1 record, exactly as specified by `Solution`.

The existence assertion merely claims the physical setup admits a consistent
measurement record; no measured data are exhibited.  (Uniqueness is *not*
asserted: the record is an experimental time series, not a derived scalar.) -/
theorem problem_IPhO_2026_4_C_1 (W : Apparatus) :
    ∃ R : TemperatureRecord, ∃ t_fin : ℝ, TemperatureRecord.Solution W R t_fin := by
  -- IC water heat capacity `C_IC = ρ_w · c_w · (π r_in²) · h_IC` (J/K).
  set C_IC : ℝ := W.waterHeatCapacity (Real.pi * W.r_in ^ 2) W.h_IC with hC_def
  -- Thermal time constant `τ = C_IC · R_Th` (s), positive.
  set τ : ℝ := C_IC * W.R_Th with hτ_def
  have hC_pos : 0 < C_IC := by
    rw [hC_def, Apparatus.waterHeatCapacity]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hr : 0 < Real.pi * W.r_in ^ 2 := mul_pos hpi (sq_pos_of_pos W.r_in_pos)
    have h1 : 0 < W.rho_w * W.c_w := mul_pos W.rho_w_pos W.c_w_pos
    have h2 : 0 < W.rho_w * W.c_w * (Real.pi * W.r_in ^ 2) := mul_pos h1 hr
    have h3 : 0 < W.rho_w * W.c_w * (Real.pi * W.r_in ^ 2) * W.h_IC :=
      mul_pos h2 W.h_IC_pos
    exact h3
  have hτ_pos : 0 < τ := mul_pos hC_pos W.R_Th_pos
  -- Admissible witness: `T_IC t = 65 − 45·exp(−t/τ)` (cold start at 20 °C,
  -- exponentially approaching the OC), `T_OC = 65` constant.
  refine ⟨{ T_IC := fun t ↦ 65 - 45 * Real.exp (-(t / τ)), T_OC := fun _ ↦ (65 : ℝ) }, 1, ?_⟩
  refine ⟨by norm_num, by simp [TemperatureRecord.InitialOC], ?_, ?_⟩
  · -- IC heat budget `C_IC · dT_IC/dt = (T_OC − T_IC)/R_Th` on every window.
    intro t_fin _
    refine ⟨fun t ↦ (65 - (65 - 45 * Real.exp (-(t / τ)))) / W.R_Th, ?_, ?_⟩
    · -- Pointwise `q t = (T_OC t − T_IC t)/R_Th`; `rw` unfolds and closes by rfl.
      intro t _
      rw [Apparatus.heatFlowIntoIC]
    · -- `deriv (s ↦ C_IC * (65 - 45 * exp(-(s/τ)))) t = q t` on [0, t_fin].
      intro t _
      change deriv (fun s ↦ C_IC * (65 - 45 * Real.exp (-(s / τ)))) t
          = (65 - (65 - 45 * Real.exp (-(t / τ)))) / W.R_Th
      have hbase : HasDerivAt (fun s : ℝ ↦ s / τ) (1 / τ) t :=
        (hasDerivAt_id' t).div_const τ
      have hneg : HasDerivAt (fun s : ℝ ↦ -(s / τ)) (-(1 / τ)) t := hbase.neg
      have hcomp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(s / τ)))
          (Real.exp (-(t / τ)) * (-(1 / τ))) t := (Real.hasDerivAt_exp _).comp _ hneg
      have h45 : HasDerivAt (fun s : ℝ ↦ 45 * Real.exp (-(s / τ)))
          (45 * (Real.exp (-(t / τ)) * (-(1 / τ)))) t := by
        convert hcomp.const_mul 45 using 2
      have h65 : HasDerivAt (fun s : ℝ ↦ 65 - 45 * Real.exp (-(s / τ)))
          (-(45 * (Real.exp (-(t / τ)) * (-(1 / τ))))) t := h45.const_sub 65
      have hC : HasDerivAt (fun s : ℝ ↦ C_IC * (65 - 45 * Real.exp (-(s / τ))))
          (C_IC * (-(45 * (Real.exp (-(t / τ)) * (-(1 / τ)))))) t := h65.const_mul C_IC
      rw [hC.deriv]
      rw [hτ_def]
      field_simp [hC_pos, W.R_Th_pos]
      ring
  · -- Co-approaching regime: `T_OC − T_IC ≥ 0`, IC warms, OC stays at 65.
    refine ⟨?_, ?_, ?_⟩
    · -- `0 ≤ T_OC t − T_IC t = 45 * exp(−t/τ)`.
      intro t _
      have hd : TemperatureRecord.drivingDifference
          { T_IC := fun t ↦ 65 - 45 * Real.exp (-(t / τ)), T_OC := fun _ ↦ (65 : ℝ) } t
          = 45 * Real.exp (-(t / τ)) := by
        unfold TemperatureRecord.drivingDifference
        ring
      rw [hd]
      have hpos : 0 < Real.exp (-(t / τ)) := Real.exp_pos _
      positivity
    · -- `T_IC 0 ≤ T_IC t`: `65 − 45·1 ≤ 65 − 45·exp(−t/τ)` since `exp ≤ 1`.
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hexp_le : Real.exp (-(t / τ)) ≤ 1 := by
        have hdiv : 0 ≤ t / τ := div_nonneg ht0 (le_of_lt hτ_pos)
        have harg : -(t / τ) ≤ 0 := by linarith [hdiv]
        erw [Real.exp_le_one_iff] at *
        linarith [harg]
      have hf : ∀ s, ({ T_IC := fun t ↦ 65 - 45 * Real.exp (-(t / τ)), T_OC := fun _ ↦ (65 : ℝ) } :
            TemperatureRecord).T_IC s = 65 - 45 * Real.exp (-(s / τ)) := fun _ ↦ rfl
      rw [hf, hf]
      rw [show Real.exp (-((0 : ℝ) / τ)) = 1 from by simp]
      nlinarith [hexp_le]
    · -- `T_OC t ≤ T_OC 0` — both equal 65.
      intro t _
      change (65 : ℝ) ≤ 65
      exact le_refl 65

end PartC1
end IPhO_2026_4
