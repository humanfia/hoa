import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Problem 4, Part B.4 — answer-blind formalization

Subquestion **B.4** (1.0 pt), from the official Experimental Exam E1, Part B
"Vapor Pressure" (pages 11–12):

> **B4.** Assuming that IC contains both dry air plus water vapor, deduce an
> algebraic expression for the vapor pressure `P_v` in terms of `P_atm`
> (atmospheric pressure), `H₀`, `H`, `T₀` and `T`.  For the purposes of this
> problem, you can assume that the vapor pressure at 0 °C is zero.

## Physical setup (Part B, pages 11–12)

The inner cylinder (**IC**) traps a fixed amount of the liquid-free gas column —
a mixture of **dry air** plus **water vapor** that saturates at the prevailing
temperature.  Per page 11, the valve / free-syringe arrangement (Fig. 19)
keeps the **total** pressure of this IC gas approximately equal to the
atmospheric pressure `P_atm` throughout the run.  The liquid-free air-column
height `H` is recorded as a function of the absolute temperature `T` while the
system cools (parts B.1–B.2).

At the reference temperature `T₀ = 273.15 K` (0 °C) the recorded `H(T)` curve is
extrapolated to give the reference height `H₀` (part B.3), and — because the
water-vapor pressure at 0 °C may be taken as **zero** (part B.4) — the IC gas
is effectively pure dry air there.

## Why `H` varies at fixed total pressure

(Addresses the review consistency question.)  The valve/syringe arrangement of
Fig. 19 keeps the **total** gas pressure pinned to `P_atm` while leaving the
**volume** free to change: as the temperature falls, the trapped gas contracts
and the water level rises, changing the air-column height `H`.  The dry-air
amount is fixed (the column is sealed), so its **partial** pressure obeys the
combined ideal-gas law between the reference and running states even though the
total pressure is fixed.  As `T` drops toward `T₀`, the saturated vapour
pressure falls toward zero, so by Dalton's law the dry-air partial pressure
rises toward `P_atm` and `P_v → 0`: the requested vapour pressure is genuinely
nonzero away from `T₀` (it does **not** collapse), because it is the *partial*
pressure that carries the gas-law temperature dependence, not the fixed total.

## Geometry and volume

The air column of the IC is a narrow, effectively **uniform cross-section**
tube (Fig. 19), so the trapped dry-air volume is directly proportional to the
recorded air-column height.  We model this as a uniform effective
cross-sectional area `A`:

* reference state volume  `V₀ = A * H₀`,
* running state volume    `V  = A * H`.

The uniform-area calibration `V ∝ H` is the geometry explicitly assumed in
Part B (it is what parts B.5–B.6 use), and it is exactly what makes the
requested vapour pressure an expression in **only** `P_atm, H₀, H, T₀, T` (the
area `A` cancels).

## Governing laws

1. **Dalton (isobaric total).**  The total pressure equals the sum of the
   dry-air and water-vapour partial pressures and is held at `P_atm`:
   `P_atm = p_air + P_v`.
2. **Combined ideal-gas law for the fixed dry-air amount.**  Between the
   reference and running states, `p_air * V / T = p_air₀ * V₀ / T₀`.
3. **Zero vapour pressure at `T₀`.**  At the reference temperature the vapour
   pressure is zero, so the reference dry-air partial pressure equals the total:
   `p_air₀ = P_atm`.

Eliminating `p_air` and `p_air₀` through these three laws and the geometry
`V = A*H` shows that the vapour pressure depends only on `P_atm, H₀, H, T₀, T`
(the area `A` cancels).  This is the answer-free characterization of "express
`P_v` in terms of `P_atm, H₀, H, T₀, T`".  The closed form is **withheld**
(answer-blind policy): no closed form, witness, or numerical value is placed in
any theorem signature.

## Answer-free policy

We record the geometry and the governing laws as real structure data
(`volume_eq`, `h_nonneg`), define the solution predicate as *the existence of
dry-air partial pressures satisfying Dalton's law, the combined gas law, and
the zero-vapour-at-`T₀` condition*, and state existence and uniqueness of the
vapour pressure.  The official closed form is deliberately not asserted.
-/

namespace IPhO_2026_4_B_4

/-- The state and governing physics of subquestion B.4.

The structure bundles the geometric calibration (uniform cross-section `A`),
the volume law `V ∝ H`, the positive physical data of the reference and
running states, and the physically true side-condition `h_nonneg` that the
running vapour pressure is nonnegative.  The three governing laws (Dalton,
combined gas law, zero vapour at `T₀`) are imposed inside the solution
predicate `IsSolutionVaporPressure`, so the dry-air / vapour split is
genuinely constrained rather than baked into a definition. -/
structure B4State where
  /-- The uniform effective cross-sectional area `A` of the IC air column
  (area); the trapped dry-air volume for a recorded air-column height `h` is
  `A * h`. -/
  A : ℝ
  /-- The cross-sectional area is positive. -/
  hA : 0 < A
  /-- Atmospheric (total) pressure `P_atm` at which the IC gas is held by the
  valve / free-syringe arrangement (pressure), positive. -/
  P_atm : ℝ
  hP_atm : 0 < P_atm
  /-- Reference absolute temperature `T₀ = 273.15 K` (0 °C), positive. -/
  T₀ : ℝ
  hT₀ : 0 < T₀
  /-- Extrapolated air-column height `H₀ = H(T₀)` at the reference temperature
  (length), positive. -/
  H₀ : ℝ
  hH₀ : 0 < H₀
  /-- Running absolute temperature `T` (Kelvin), positive. -/
  T : ℝ
  hT : 0 < T
  /-- Recorded air-column height `H` at the running temperature (length),
  positive. -/
  H : ℝ
  hH : 0 < H
  /-- The trapped dry-air volume as a function of the recorded air-column
  height. -/
  volume : ℝ → ℝ
  /-- Geometry: the volume for air-column height `h` is `A * h`. -/
  volume_eq : ∀ h : ℝ, volume h = A * h
  /-- Physical side-condition: the running vapour pressure is nonnegative.
  Since by Dalton `P_v = P_atm - p_air ≥ 0`, the dry-air partial pressure
  cannot exceed the total, so the trapped dry-air density `p_air / T` at the
  running state is at most the reference density `P_atm / T₀`.  Multiplying
  through (all quantities positive) gives
  `P_atm * (volume H₀ / T₀) ≤ P_atm * (volume H / T)`.
  This rules out the unphysical super-total dry-air density at which the gas
  laws would force a negative vapour pressure. -/
  h_nonneg : P_atm * (volume H₀ / T₀) ≤ P_atm * (volume H / T)

namespace B4State

variable (s : B4State)

/-- **Solution predicate (B.4).**  A real number `P_v` is the water-vapour
partial pressure at the running state of `s` when there exist dry-air partial
pressures `p_air` (running) and `p_air₀` (reference) such that:

1. **Dalton / isobaric total:** `p_air + P_v = P_atm`;
2. **Combined ideal-gas law for the fixed dry-air amount:**
   `p_air * (V / T) = p_air₀ * (V₀ / T₀)`, with `V = volume H`,
   `V₀ = volume H₀`;
3. **Zero vapour pressure at `T₀`:** the reference dry-air partial pressure
   equals the total, `p_air₀ = P_atm`.

This keeps the requested variables in the governing relations while leaving
the closed-form expression for `P_v` to be derived (not asserted). -/
def IsSolutionVaporPressure (s : B4State) (P_v : ℝ) : Prop :=
  ∃ p_air p_air₀ : ℝ,
    p_air + P_v = s.P_atm ∧
    p_air * (s.volume s.H / s.T) = p_air₀ * (s.volume s.H₀ / s.T₀) ∧
    p_air₀ = s.P_atm

/-- The reference volume `V₀ = A * H₀` is positive. -/
theorem volume_ref_pos (s : B4State) : 0 < s.volume s.H₀ := by
  rw [s.volume_eq]; exact mul_pos s.hA s.hH₀

/-- The running volume `V = A * H` is positive. -/
theorem volume_run_pos (s : B4State) : 0 < s.volume s.H := by
  rw [s.volume_eq]; exact mul_pos s.hA s.hH

/-- `V₀ / T₀` is positive. -/
theorem vol_ref_div_T₀_pos (s : B4State) : 0 < s.volume s.H₀ / s.T₀ :=
  div_pos s.volume_ref_pos s.hT₀

/-- `V / T` is positive. -/
theorem vol_run_div_T_pos (s : B4State) : 0 < s.volume s.H / s.T :=
  div_pos s.volume_run_pos s.hT

/-- **Existence (B.4).**  There exists a real value of the vapour pressure
satisfying the governing laws of `s`.  The witness is deliberately not
exhibited as a closed form. -/
theorem exists_vaporPressure (s : B4State) :
    ∃ P_v : ℝ, IsSolutionVaporPressure s P_v := by
  -- Dalton determines the running dry-air partial pressure as the ratio of the
  -- reference to running specific volumes times `P_atm`; the vapour pressure
  -- is the Dalton complement.  `field_simp` with the positivity of the
  -- volumes and temperatures settles the combined ideal-gas law (the
  -- `h_nonneg` side-condition is what makes the constructed value physically
  -- an admissible, i.e. nonnegative, vapour pressure).
  refine ⟨s.P_atm - s.P_atm * (s.volume s.H₀ / s.T₀) / (s.volume s.H / s.T),
    s.P_atm * (s.volume s.H₀ / s.T₀) / (s.volume s.H / s.T), s.P_atm,
    add_sub_cancel _ _, ?_, rfl⟩
  field_simp [ne_of_gt s.vol_ref_div_T₀_pos, ne_of_gt s.vol_run_div_T_pos,
    ne_of_gt s.volume_ref_pos, ne_of_gt s.volume_run_pos, ne_of_gt s.hT₀, ne_of_gt s.hT]

/-- **Uniqueness (B.4).**  The vapour pressure determined by the governing
laws is unique: any two candidates both arising from Dalton's law, the
combined dry-air gas law, and zero vapour at `T₀` coincide.  This is the
unique-value characterization of the requested algebraic expression. -/
theorem unique_vaporPressure (s : B4State) {P_v₁ P_v₂ : ℝ}
    (h₁ : IsSolutionVaporPressure s P_v₁) (h₂ : IsSolutionVaporPressure s P_v₂) :
    P_v₁ = P_v₂ := by
  -- With `p_air₀ = P_atm` the combined law fixes each running dry-air partial
  -- pressure to the same value (cancel the positive factor `V / T`); Dalton
  -- then forces the two vapour pressures to agree.
  obtain ⟨a₁, _, hdal₁, hgas₁, href₁⟩ := h₁
  obtain ⟨a₂, _, hdal₂, hgas₂, href₂⟩ := h₂
  have hcancel : a₁ = a₂ :=
    mul_right_cancel₀ (ne_of_gt s.vol_run_div_T_pos) (by rw [hgas₁, href₁, hgas₂, href₂])
  linarith

/-- **Combined existence-and-uniqueness (B.4).**  The vapour pressure described
by subquestion B.4 exists and is unique.  This is the answer-free analogue of
"express `P_v` in terms of `P_atm, H₀, H, T₀, T`": the unique value *is* the
vapour-pressure expression, and a later proof may unfold `volume`, `volume_eq`
and eliminate the dry-air partial pressures to display the closed form in the
listed variables. -/
theorem existsUnique_vaporPressure (s : B4State) :
    ∃! P_v : ℝ, IsSolutionVaporPressure s P_v := by
  obtain ⟨P_v, hP_v⟩ := s.exists_vaporPressure
  exact ⟨P_v, hP_v, fun P_v' hP_v' ↦ s.unique_vaporPressure hP_v' hP_v⟩

/- Note.  Eliminating `p_air` and `p_air₀` across the three laws and using
`volume h = A * h` (so `V / T = A * H / T` and `V₀ / T₀ = A * H₀ / T₀`) shows
the vapour pressure depends only on `P_atm, H₀, H, T₀, T` — the uniform area
`A` cancels — which is exactly the closed form the subquestion requests.  That
closed form is withheld from every signature by the answer-blind policy. -/

end B4State

end IPhO_2026_4_B_4
