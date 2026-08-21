import Mathlib

/-!
# IPhO 2026, Experimental Exam (E1), Part B.1 — answer-blind formalization

## Physical setup (Part B: moist air column, E1 pages 11–12)

The inner cylinder (IC) of the apparatus contains **dry air plus saturated
water vapor** at total pressure approximately equal to the atmospheric
pressure `P_atm`: the water level is continually adjusted so that the trapped
gas column stays at ambient pressure (hydrostatic corrections neglected).
The **liquid-free air-column height `H`** is recorded as the absolute
temperature `T` of the trapped gas falls.  At `T₀ = 273.15 K` (`0 °C`) the
extrapolated height is `H₀` and the water vapor pressure may be taken as
zero; the saturated vapor pressure follows the integrated
Clausius–Clapeyron law

    ln (P_v / P_{v0}) = − (Q_v / R) · (1/T − 1/T₀)          (3)

with `Q_v` the molar latent heat of vaporization and `R` the universal gas
constant.  This is **context** for B.1: subquestions B.2–B.6 exploit it, but
subquestion B.1 does not invoke any governing law (see below).

## Procedure (E1 p. 11)

The OC water is heated to `65 °C`; once the temperature **starts to
decrease**, recording of `H` as a function of `T` begins.  Cold water may be
substituted into the OC to lower the temperature further.  Hence the recorded
run is a **cooldown**: the sampled temperatures decrease through the
experiment's window from the (hot) start towards — not below — the ice point
`T₀` that anchors `H₀` (B.3's extrapolation endpoint).

## Subquestion B.1 (1.0 pt)

> **Record the height `H` as a function of temperature `T` in a table.**

B.1 is a **data-table deliverable**: the requested object is the measured
`(T, H)` record itself.  The source states **no governing law** for the
individual rows of B.1; the isobaric-mixture relation `P_v` vs. `H` is the
deliverable of the *later* B.4, and `H₀` is the deliverable of the later
B.3.  Faithful formalization therefore imposes only what B.1 itself asserts:
a finite recorded table of physically admissible `(T, H)` pairs sampled
along the procedure's monotone cooldown.

**Answer-blind statement design.**  The measured values of `H` (and the
sampling grid of `T`) are withheld.  Following the answer-free policy, the
theorem asserts the *existence* of a cooldown record satisfying the faithful
`Solution` predicate — a physically admissible sampled `(T, H)` table — with
no measured value, no closed form, and no sampling grid in the signature.
Uniqueness is *not* asserted: a data record is an experimental time series,
not a derived scalar.  Parts B.2–B.6 (plot the data, extrapolate `H₀`,
deduce `P_v`, determine `Q_v`, `L_v`) are not part of this file.
-/

namespace IPhO_2026_4
namespace PartB1

/-- **Experiment context (IPhO 2026 E1, Part B).**  The physical data framing
the vapor-pressure experiment: the (approximately constant) total pressure
`P_atm` of the trapped gas column, the ice-point reference temperature
`T₀ = 273.15 K`, the molar latent-heat parameter `Q_v` (J/mol) and the
vapor-pressure scale `P_v0` (Pa) of the stated Clausius–Clapeyron law (3),
and the universal gas constant `R`.  All are positive reals.

This structure is carried as *context only*: subquestion B.1 records raw
data and states no governing law, so no field of `Context` gates any
recorded row.  The vapor law is used from B.4 onward. -/
structure Context where
  /-- Total pressure of the trapped gas column, `P_atm ≈ 1.0 × 10⁵ Pa`
  (atmospheric pressure); constant throughout the measurement. -/
  P_atm : ℝ
  /-- Reference temperature `T₀ = 273.15 K` (the ice point, 0 °C); anchors
  the vapor law (3) and the extrapolated height `H₀` of B.3. -/
  T₀ : ℝ
  /-- Molar latent-heat parameter `Q_v` (J/mol) entering the stated
  Clausius–Clapeyron law (3) of the water vapor. -/
  Q_v : ℝ
  /-- Vapor-pressure scale `P_v0` (Pa) of the stated Clausius–Clapeyron law. -/
  P_v0 : ℝ
  /-- Universal gas constant `R` (J/(mol·K)); the exam prescribes the
  reference value `R = 8.31 J/(mol·K)` from B.5 onward. -/
  R : ℝ
  P_atm_pos : 0 < P_atm
  T₀_pos : 0 < T₀
  Q_v_pos : 0 < Q_v
  P_v0_pos : 0 < P_v0
  R_pos : 0 < R

/-- The ice-point reference temperature, exactly `T₀ = 273.15 K` as printed
in the statement ("At T₀ = 273.15 K, extrapolated height is H₀"). -/
noncomputable def referenceTemperature : ℝ := 273.15

/-- **Stated vapor law (context, eq. (3)):** the said Clausius–Clapeyron
relation in exponentiated form
`P_v = P_v0 · exp(−(Q_v/R)·(1/T − 1/T₀))`, equivalent for positive `P_v` to
the printed `ln(P_v/P_v0) = −(Q_v/R)·(1/T − 1/T₀)`.  `T` is the absolute
temperature (K).  Recorded here because it is stated data of Part B; B.1's
data table does not depend on it. -/
noncomputable def Context.vaporPressure (C : Context) (T : ℝ) : ℝ :=
  C.P_v0 * Real.exp (-(C.Q_v / C.R) * (T⁻¹ - C.T₀⁻¹))

/-- **The B.1 measurement table.**  The liquid-free air-column height `H`
recorded as a function of the absolute temperature `T`: a finite family of
`k` measured pairs `(T i, H i)`, `i : Fin k`, sampled in the chronological
order of the cooldown run, where

* `T i` is the measured absolute temperature of the gas column (K, positive);
* `H i` is the recorded liquid-free air-column height (positive);
* `k ≥ 2`, since recording `H` *as a function of* `T` — a table on which the
  later B.2 plot and B.3 extrapolation operate — needs at least two rows.

Strict positivity of the measured temperatures and heights is bundled here,
since nonpositive readings are physically meaningless; all admissibility
conditions that follow from the experimental procedure are imposed separately
by `WithinCooldown` and `IsCooldownDecreasing`. -/
structure CooldownRecord where
  /-- Number of recorded (temperature, height) pairs. -/
  k : ℕ
  /-- Measured absolute temperatures `T i` of the gas column (K). -/
  T : Fin k → ℝ
  /-- Recorded liquid-free air-column heights `H i` at the corresponding
  sampled temperatures (same length unit throughout). -/
  H : Fin k → ℝ
  /-- The table records a two-variable function: at least two rows. -/
  two_le : 2 ≤ k
  /-- Every measured temperature is a positive absolute temperature (K). -/
  T_pos : ∀ i, 0 < T i
  /-- Every recorded height is positive (it is an air-column length). -/
  H_pos : ∀ i, 0 < H i

/-- **Cooldown window (procedure, E1 p. 11).**  Recording begins once the
heated OC water (`65 °C`) starts cooling, and proceeds down towards — but
not below — the ice point `T₀` (the `0 °C` anchor of the vapor law and of
`H₀`).  Hence every sampled temperature lies in the physical window
`Icc T₀ T_start`, where `T_start` is the (hot) temperature at which
recording begins and `T₀ ≤ T_start`. -/
def WithinCooldown (C : Context) (D : CooldownRecord) (T_start : ℝ) : Prop :=
  ∀ i, D.T i ∈ Set.Icc C.T₀ T_start

/-- **Monotone cooldown direction (procedure, E1 p. 11).**  The sampled
temperatures decrease along the record: the OC water is left to cool from
its heated state and recording starts once the temperature *starts to
decrease*, continuing to lower temperatures (cold water may be substituted
to lower it further).  The rows are indexed in chronological order, so
nonincreasing means `i ≤ j → T j ≤ T i`, i.e. the sampled temperature
function is antitone. -/
def IsCooldownDecreasing (D : CooldownRecord) : Prop :=
  Antitone D.T

/-- **Solution predicate for B.1 (answer-free).**  A cooldown record `D`
realizes the deliverable of subquestion B.1 — "record the height `H` as a
function of temperature `T` in a table" — when its sampled rows all lie in
the physical cooldown window `Icc T₀ T_start` and follow the procedure's
monotone-decreasing direction.  No measured height, no closed form, and no
choice of sampling grid is fixed here; no vapor-law or isobaric relation is
imposed on the rows (those belong to B.4).

`T_start` is the recording-start temperature (the hot end of the run,
`T₀ ≤ T_start`, e.g. near the `65 °C` pre-heat), a parameter of the run
supplied with the setup. -/
def Solution (C : Context) (T_start : ℝ) (D : CooldownRecord) : Prop :=
  WithinCooldown C D T_start ∧ IsCooldownDecreasing D

/-- **Target theorem (answer-free, B.1).**  For the stated experimental
context — dry air plus saturated water vapor held isobarically near `P_atm`
while the temperature falls from a recording start at or above the ice point
— a B.1 height–temperature record **exists**: there is a finite sampled
cooldown table `D`, of physically admissible `(T, H)` pairs, exactly as
specified by `Solution`.

The assertion merely claims that the physical setup admits a consistent
measurement record; no measured data are exhibited.  Uniqueness is not
asserted — the record is an experimental time series, not a derived scalar. -/
theorem problem_IPhO_2026_4_B_1 (C : Context) (T_start : ℝ)
    (hT : C.T₀ ≤ T_start) :
    ∃ D : CooldownRecord, Solution C T_start D := by
  -- Witness: the minimal two-row record with both temperatures at the hot
  -- start `T_start` (a degenerate constant sampler at the start of the
  -- cooldown). With `T i = T_start` for all `i : Fin 2`, the window
  -- condition collapses to `C.T₀ ≤ T_start` (hypothesis `hT` plus
  -- `le_refl`) and the antitonicity of a constant function is
  -- `antitone_const`. The heights are sampled at `H ≡ 1 > 0`.
  refine ⟨⟨2, fun _ => T_start, fun _ => 1, le_refl 2, fun _ => hT.trans_lt' C.T₀_pos,
    fun _ => one_pos⟩, ?_, ?_⟩
  · -- Every sampled temperature equals `T_start ∈ Icc C.T₀ T_start`.
    intro i
    exact ⟨hT, le_refl T_start⟩
  · -- The constant sampler is antitone.
    exact antitone_const

end PartB1
end IPhO_2026_4
