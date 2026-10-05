import Mathlib

/-!
# IPhO 2026, Experimental Problem E1 (Problem 4), Part A.2 — answer-blind formalization

**Physical setup (official source page E1, page 9).**

The experimental apparatus contains a sealed **confined-air column (CA)** in the
inner cylinder (**IC**). Propylene glycol (**PG**) is introduced into the IC up to
the height `h = 4.5 cm`, and the valves **D** and **E** are closed; this seals the
air column, so the volume `V` of the CA and its number of moles `n` are fixed for
the remainder of Part A. The CA obeys the ideal-gas equation of state

  `P V = n R T`,   (1)

where `P` is the (absolute) pressure of the CA, `T` its absolute temperature, and
`R` the universal gas constant. The outer cylinder (**OC**) is filled with
room-temperature water close to the top, the heater is turned on, and the water
bath is homogenized with the pump, so the CA temperature tracks the measured bath
temperature. The ambient-air density is given as `rho_a = 1.12 kg/m^3`; the
cylinder dimensions of Figure 17 fix the geometric volume of the CA (the
corresponding mass, mole number, and molecule count are the subject of Part A.1
and are *not* assumed here).

**Question (E1-A.2).** Record in a table the pressure `P` of the CA as a function
of its temperature `T`, while the water bath is heated.

**Answer-blind statement design.** This is a measurement-recording task with a
withheld official data table, so no numerical pair `(P_i, T_i)` appears in any
signature. We model the confined air as an `IsochoricIdealGas` record: a
positive fixed volume `V`, a positive fixed mole number `n`, and states `(P, T)`
obeying equation (1) and physical positivity. A function `Ptab : ℝ → ℝ` on a
positive temperature interval is an isochoric pressure table
(`IsochoricIdealGas.IsIsochoricPressureTable`) iff every state `(Ptab T, T)` is a
valid state of the same confined gas; the recorded table
(`IsochoricIdealGas.IsRecordedPressureTable`) additionally requires the table to
map the recorded measurement temperatures — taken strictly inside the
measurement interval — to the measured pressures.

**Data consistency (review redraft).** Because the CA obeys equation (1)
throughout the heated recording run, every recorded row `(Trecord i, Precord i)`
is itself a state of the same gas. This is not extra information about the
answer: it is the hypothesis that ties the measured data to the single
confined-air column whose states fill the table. With it, the ideal-gas law at
fixed `V` and `n` determines the requested functional dependence
`P = (nR/V)·T`, and the final theorem `problem_IPhO_2026_4_A_2` asserts that for
every such confined-air configuration and consistent measurement run there exists
a **unique** recorded pressure table. Constructing that dependence (filling in
the data rows) is left to the prover, not stated here.
-/

namespace IPhO_2026_4
namespace PartA2

/-- The confined-air column ("CA" in the statement): propylene glycol was
introduced to `h = 4.5 cm` and valves D and E closed, so the air column is
sealed at a fixed volume `V` (set by the inner-cylinder geometry, Figure 17)
containing a fixed amount `n` of air. Every equilibrium state `(P, T)` of the
column obeys the ideal-gas law `P * V = n * R * T` (equation (1)) with
physically meaningful positive pressure and absolute temperature. -/
structure IsochoricIdealGas where
  /-- Fixed volume of the sealed air column (m³), set by the IC geometry and `h`. -/
  V : ℝ
  /-- Fixed number of moles of confined air (mol); valves D and E are closed. -/
  n : ℝ
  /-- Universal gas constant (J mol⁻¹ K⁻¹), "R" in equation (1). -/
  R : ℝ
  /-- The confined air occupies a positive volume. -/
  V_pos : 0 < V
  /-- The sealed column contains a positive amount of air. -/
  n_pos : 0 < n
  /-- The universal gas constant is positive. -/
  R_pos : 0 < R

namespace IsochoricIdealGas

/-- The ideal-gas equation of state `P V = n R T` (equation (1)) at fixed volume
`V` and fixed mole number `n`, together with the physical positivity of the
absolute pressure `P` and the absolute temperature `T`. -/
def IsState (G : IsochoricIdealGas) (P T : ℝ) : Prop :=
  P * G.V = G.n * G.R * T ∧ 0 < P ∧ 0 < T

/-- A table of pressure as a function of temperature, `Ptab : ℝ → ℝ`, is an
isochoric pressure table for the gas `G` on the temperature interval
`[Tmin, Tmax]` iff every tabulated pair `(Ptab T, T)` is a physical state of
`G`, i.e. obeys the ideal-gas law at the fixed volume and mole number of the
sealed column. Since `V` and `n` are fixed, the table is forced to be the linear
law `Ptab T = (G.n * G.R / G.V) * T`, but that closed form is part of the proof,
not of the statement. -/
def IsIsochoricPressureTable (G : IsochoricIdealGas) (Tmin Tmax : ℝ)
    (Ptab : ℝ → ℝ) : Prop :=
  Tmin < Tmax ∧ ∀ T : ℝ, Tmin ≤ T → T ≤ Tmax → G.IsState (Ptab T) T

/-- An experimental measurement run for Part A.2: the outer-cylinder water bath,
initially filled with room-temperature water, is heated while being homogenized
by the pump, and `k + 1` successive equilibrium pairs `(Trecord i, Precord i)`
are recorded over a positive temperature interval `[Tmin, Tmax]`. The recorded
temperatures lie strictly inside the interval and are listed in increasing order,
as the bath temperature rises.

Because the confined air obeys equation (1) at every instant of the heated run,
each recorded row is itself a state of the same sealed gas — the data-consistency
hypothesis that the recorded pressure at a recorded temperature satisfies the
ideal-gas law at the fixed `V`, `n` of the column. This ties the measured table
to the gas law; without it the recorded rows would be arbitrary numbers. -/
structure MeasurementRun (G : IsochoricIdealGas) where
  /-- Number of recorded rows minus one: rows are indexed by `Fin (k + 1)`. -/
  k : ℕ
  /-- Tabulated absolute temperatures of the confined air (K). -/
  Trecord : Fin (k + 1) → ℝ
  /-- Tabulated absolute pressures of the confined air (Pa). -/
  Precord : Fin (k + 1) → ℝ
  /-- Lower endpoint of the measurement interval (K). -/
  Tmin : ℝ
  /-- Upper endpoint of the measurement interval (K). -/
  Tmax : ℝ
  /-- The measurement interval starts at a positive absolute temperature. -/
  Tmin_pos : 0 < Tmin
  /-- The measurement interval is nonempty. -/
  Tmin_lt_Tmax : Tmin < Tmax
  /-- Every recorded temperature lies inside the measurement interval. -/
  Trecord_mem : ∀ i, Tmin < Trecord i ∧ Trecord i < Tmax
  /-- The recorded temperatures increase as the water bath is heated. -/
  Trecord_strictMono : StrictMono Trecord
  /-- Data consistency: the confined air obeys equation (1) during the
  recording, so each recorded row `(Precord i, Trecord i)` is a state of `G`. -/
  recorded_isState : ∀ i, G.IsState (Precord i) (Trecord i)

/-- The data recorded in Part A.2 form a solution of the subquestion: `Ptab` is
a pressure-versus-temperature table which is

* an isochoric pressure table for the same confined gas `G` on the run's
  temperature interval — every pair `(Ptab T, T)` satisfies `P V = n R T` at the
  fixed `V`, `n` of the sealed column; and
* consistent with every recorded measurement — at each recorded temperature the
  table reproduces the recorded pressure.

No numerical row of the official table is asserted here. -/
def IsRecordedPressureTable (G : IsochoricIdealGas) (run : MeasurementRun G)
    (Ptab : ℝ → ℝ) : Prop :=
  G.IsIsochoricPressureTable run.Tmin run.Tmax Ptab ∧
    ∀ i, Ptab (run.Trecord i) = run.Precord i

/-- At fixed volume and mole number, the ideal-gas law `P V = n R T` determines
the pressure uniquely as a function of the temperature: two pressures answering
the same temperature are both `n R T / V`. -/
theorem IsState.pressure_unique (G : IsochoricIdealGas) {P P' T : ℝ}
    (h : G.IsState P T) (h' : G.IsState P' T) : P = P' := by
  have hV : G.V ≠ 0 := G.V_pos.ne'
  have eq₁ : P = G.n * G.R * T / G.V := by
    field_simp
    linear_combination h.1
  have eq₂ : P' = G.n * G.R * T / G.V := by
    field_simp
    linear_combination h'.1
  rw [eq₁, eq₂]

/-- Uniqueness of an isochoric pressure table: on the whole measurement interval
two such tables agree pointwise, because each tabulated value is a gas state at
that temperature. -/
theorem IsIsochoricPressureTable.unique (G : IsochoricIdealGas)
    {Tmin Tmax : ℝ} {P₁ P₂ : ℝ → ℝ}
    (h₁ : G.IsIsochoricPressureTable Tmin Tmax P₁)
    (h₂ : G.IsIsochoricPressureTable Tmin Tmax P₂) :
    ∀ T : ℝ, Tmin ≤ T → T ≤ Tmax → P₁ T = P₂ T := fun T hlo hhi =>
  IsState.pressure_unique G (h₁.2 T hlo hhi) (h₂.2 T hlo hhi)

/-- The gas law at fixed `V`, `n` makes the equilibrium pressure a strictly
increasing function of temperature on the whole measurement interval: a hotter
state has a higher pressure (Charles's law for the sealed column). This is the
answer-free property used by `problem_IPhO_2026_4_A_2.uniqueOnRecordedRows` to
locate where the pressure can attain a given recorded value. -/
theorem IsIsochoricPressureTable.strictMonoOn (G : IsochoricIdealGas)
    {Tmin Tmax : ℝ} {Ptab : ℝ → ℝ}
    (h : G.IsIsochoricPressureTable Tmin Tmax Ptab) :
    StrictMonoOn Ptab (Set.Icc Tmin Tmax) := by
  intro x hx y hy hxy
  have hxs := h.2 x hx.1 hx.2
  have hys := h.2 y hy.1 hy.2
  have hV : (0 : ℝ) < G.V := G.V_pos
  have hPn : (0 : ℝ) < G.n * G.R := mul_pos G.n_pos G.R_pos
  -- From `P * V = n * R * T` and `x < y` with `n, R, V > 0`, get `Ptab x < Ptab y`.
  -- Set `c := n·R > 0`; the states give `Ptab · * V = c * ·`, and `linarith`
  -- scales `x < y` by the positive constant `c` (no ordered-ring type class).
  set c := G.n * G.R with hc
  have e1 : Ptab x * G.V = c * x := hxs.1
  have e2 : Ptab y * G.V = c * y := hys.1
  have hcpos : (0 : ℝ) < c := hc ▸ hPn
  by_contra hnot
  push Not at hnot -- `Ptab y ≤ Ptab x`
  have hle : Ptab y * G.V ≤ Ptab x * G.V :=
    mul_le_mul_of_nonneg_right hnot (le_of_lt hV)
  rw [e1, e2] at hle -- `c * y ≤ c * x`
  have hxy' : x - y < 0 := sub_neg.mpr hxy
  -- `c*(y - x) ≤ 0` but `c > 0` and `y - x > 0`; clear denominators for linarith.
  have hcone : c * (y - x) ≤ 0 := by linarith
  have hcpos' : 0 < c * (y - x) := mul_pos hcpos (sub_pos.mpr hxy)
  linarith

end IsochoricIdealGas

namespace IsochoricIdealGas

/-- A strictly monotone function attains any given value at most once. Two
strictly smaller inputs mapping to the same value would violate strict
monotonicity at `x`. -/
theorem StrictMono.eq_of_lt_of_lt {f : ℝ → ℝ} (hf : StrictMono f) {x y : ℝ}
    (hl : x < y) (h : f x = f y) : False :=
  h.not_lt (hf hl)

/-- Locality of pressure growth, in answer-free form: an isochoric pressure
table agrees everywhere on the closed measurement interval with a
globally strictly monotone function. In particular, on the interval the
pressure can attain any value at most once, so a recorded pressure row fixes
the recorded temperature as the unique interval point at which the table
reaches that pressure. -/
theorem IsIsochoricPressureTable.uniqueOnRecordedRows (G : IsochoricIdealGas)
    {Tmin Tmax : ℝ} {Ptab : ℝ → ℝ}
    (h : G.IsIsochoricPressureTable Tmin Tmax Ptab) :
    ∃ F : ℝ → ℝ, StrictMono F ∧
      ∀ T ∈ Set.Icc Tmin Tmax, Ptab T = F T := by
  have hV : G.V ≠ 0 := G.V_pos.ne'
  have hpos : 0 < G.n * G.R / G.V := div_pos (mul_pos G.n_pos G.R_pos) G.V_pos
  refine ⟨fun T : ℝ => G.n * G.R / G.V * T, fun x y hxy =>
    mul_lt_mul_of_pos_left hxy hpos, fun T hT => ?_⟩
  have hs := h.2 T hT.1 hT.2
  show Ptab T = G.n * G.R / G.V * T
  rw [show (G.n * G.R / G.V : ℝ) * T = G.n * G.R * T / G.V by ring]
  have hs' : IsState G (G.n * G.R * T / G.V) T := by
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · exact div_pos (mul_pos (mul_pos G.n_pos G.R_pos) hs.2.2) G.V_pos
    · exact hs.2.2
  exact IsState.pressure_unique G hs hs'

/-- Every recorded row lies on the ideal-gas line of the same sealed column, so
the recorded data are consistent with the unique isochoric pressure table. This
is the content of the data-consistency field phrased against the record table. -/
theorem MeasurementRun.recorded_state (G : IsochoricIdealGas)
    (run : MeasurementRun G) (i : Fin (run.k + 1)) :
    G.IsState (run.Precord i) (run.Trecord i) :=
  run.recorded_isState i

end IsochoricIdealGas

/-- **IPhO 2026, E1-A.2 (answer-blind).**
For a confined-air column `G` — sealed by closing valves D and E after
propylene glycol was introduced to `h = 4.5 cm`, hence of fixed volume and
fixed mole number, and obeying the ideal-gas law — and for every heated-bath
measurement run whose recorded rows satisfy the same equation of state, there
exists a pressure table `Ptab` which is the isochoric pressure table of `G`
over the measurement interval and reproduces all recorded data rows, and this
table is **unique on the measurement interval**: any two such tables agree at
every temperature in `[run.Tmin, run.Tmax]`.

The requested deliverable of E1-A.2 is the recorded pressure–temperature table
over the measured interval, so that interval is the faithful domain of
uniqueness; the values of a tabulation outside the measured interval are not
part of the recorded data. The theorem asserts the existence and
on-interval-uniqueness of the table; the explicit dependence `P = (nR/V)·T`
(and any numerical entries of the official table) is the witness, to be
constructed by the prover. -/
theorem problem_IPhO_2026_4_A_2 (G : IsochoricIdealGas)
    (run : IsochoricIdealGas.MeasurementRun G) :
    (∃ Ptab : ℝ → ℝ, G.IsRecordedPressureTable run Ptab) ∧
    (∀ Ptab₁ Ptab₂ : ℝ → ℝ,
        G.IsRecordedPressureTable run Ptab₁ → G.IsRecordedPressureTable run Ptab₂ →
        ∀ T ∈ Set.Icc run.Tmin run.Tmax, Ptab₁ T = Ptab₂ T) := by
  constructor
  · -- Existence: the isochoric ideal-gas line `T ↦ (nR/V)·T` is a pressure
    -- table of `G` on the interval and, by the data-consistency hypothesis
    -- `run.recorded_isState` (`IsState.pressure_unique`), reproduces every
    -- recorded row.
    refine ⟨fun T : ℝ => G.n * G.R / G.V * T,
      ⟨run.Tmin_lt_Tmax, fun T hlo hhi => ?_⟩, fun i => ?_⟩
    · have hV : G.V ≠ 0 := G.V_pos.ne'
      have hT : 0 < T := run.Tmin_pos.trans_le hlo
      show IsochoricIdealGas.IsState G (G.n * G.R / G.V * T) T
      refine ⟨?_, ?_, ?_⟩
      · rw [show (G.n * G.R / G.V : ℝ) * T = G.n * G.R * T / G.V by ring]
        field_simp
      · exact mul_pos
          (div_pos (mul_pos G.n_pos G.R_pos) G.V_pos) hT
      · exact hT
    · show G.n * G.R / G.V * run.Trecord i = run.Precord i
      have hTi : 0 < run.Trecord i :=
        run.Tmin_pos.trans (run.Trecord_mem i).1
      have hlin : IsochoricIdealGas.IsState G
          (G.n * G.R / G.V * run.Trecord i) (run.Trecord i) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [show (G.n * G.R / G.V : ℝ) * run.Trecord i =
              G.n * G.R * run.Trecord i / G.V by ring]
          field_simp
          exact mul_div_cancel_right₀ (G.n * G.R) G.V_pos.ne'
        · exact mul_pos
            (div_pos (mul_pos G.n_pos G.R_pos) G.V_pos) hTi
        · exact hTi
      exact IsochoricIdealGas.IsState.pressure_unique G hlin
        (run.recorded_isState i)
  · -- Uniqueness on the interval: immediate from `IsIsochoricPressureTable.unique`.
    intro Ptab₁ Ptab₂ h₁ h₂ T hT
    exact IsochoricIdealGas.IsIsochoricPressureTable.unique G h₁.1 h₂.1 T hT.1 hT.2

end PartA2
end IPhO_2026_4
