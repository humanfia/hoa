import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Part C.2 — answer-blind formalization

## Physical setup (Part C: Heat Conduction, E1 pages 12–13)

Water in the **inner cylinder (IC)** and water in the **outer cylinder (OC)**
exchange heat **radially** through the acrylic cylindrical wall that separates
them.  Heat conduction through the wall follows the effective thermal-law
(the exam's **Equation (4)**)

    ΔQ / Δt = (1 / R_Th) · (T_OC − T_IC),

where `ΔQ` is the heat received by the water in the **IC** through the wall
during the time interval `Δt`, `T_IC` and `T_OC` are the (absolute)
temperatures of the inner and outer water, and `R_Th` is the **effective
thermal resistance** of the wall, which depends on the material and geometry
of the wall separating the IC and the OC.  For radial Fourier conduction the
heat flow is also written (the exam's **Equation (6)**)

    dQ / dt = −λ · A · dT/dr,

with `λ` the thermal conductivity of the acrylic and `A` the wall area.

**Procedure (E1 page 13).**  The water level in the **OC** is set to
`h = 15 cm` and the OC water is heated to `65 °C` (pump used to homogenize).
The water level in the **IC** is then set to `h = 10 cm` and the stopwatch is
started.  The internal temperature `T_IC` and the external temperature
`T_OC` are recorded as functions of the time `t` (subquestion C.1).

## Dependency note (previous subquestion, answer withheld)

* **C.1** (record `T_IC` and `T_OC` as functions of time `t`) supplies, by
  natural-language prerequisite only, the recorded measurement table.  Its
  Lean output is **not** imported, per the dependency policy
  (`natural_language_prerequisite_only; do_not_import_Lean_output`); the
  record is modeled here as the abstract structure `C1Record`.

## Current subquestion (E1-C.2, 1.0 pt)

> **On a single graph, plot `T_IC` and `T_OC` as functions of time `t`.**

**Answer-blind statement design.**  The requested object is the displayed
plot itself — there is no official derived scalar to withhold.  Accordingly
we model the data (`C1Record`, the C.1 time–temperature record), the
requested display `IsSingleGraphPlot` (a coadmissible pairing of the shared
time axis with the two temperature series, displaying every recorded point
of **both** series **together on one graph**, sharing the same time axis),
and the governing-law context of Part C (the effective thermal law (4) and
the radial Fourier law (6)) as named predicates.  The theorem asserts the
existence of the requested single-graph plot.  No measured temperature, no
time value, no equilibrium temperature, and no plot witness appears in any
signature; all are held existentially inside.

The official answer is withheld deliberately: this is a specification, not a
solution.
-/

namespace IPhO_2026_4
namespace PartC2

/-- **The C.1 time–temperature record.**  The internal temperature `T_IC` of
the inner-cylinder water and the external temperature `T_OC` of the
outer-cylinder water, recorded simultaneously as functions of the elapsed
time `t` from the stopwatch start: a finite family of `k` triples
`(tᵢ, T_ICᵢ, T_OCᵢ)`, where

* `tᵢ` is the elapsed time (s, nonnegative) since the IC level was set and
  the stopwatch started, strictly increasing throughout the run;
* `T_ICᵢ` is the recorded internal (IC) absolute temperature (K, positive);
* `T_OCᵢ` is the recorded external (OC) absolute temperature (K, positive);
* `k ≥ 2`, since a plotted curve through the timed data needs at least two
  points to show a time evolution.

This structures the table recorded in subquestion C.1 ("Record the internal
temperature `T_IC` and external temperature `T_OC` as a function of time
`t`"); C.1's own Lean output is not imported, per the dependency policy. -/
structure C1Record where
  /-- Number of recorded simultaneous (time, `T_IC`, `T_OC`) triples. -/
  k : ℕ
  /-- Elapsed measurement times `tᵢ` (s) from the stopwatch start. -/
  t : Fin k → ℝ
  /-- Recorded internal (IC) absolute temperatures `T_ICᵢ` (K). -/
  T_IC : Fin k → ℝ
  /-- Recorded external (OC) absolute temperatures `T_OCᵢ` (K). -/
  T_OC : Fin k → ℝ
  /-- At least two measurements were taken (a time-evolution plot needs at
  least two points). -/
  two_le : 2 ≤ k
  /-- The stopwatch starts at `t = 0`. -/
  t_nonneg : ∀ i, 0 ≤ t i
  /-- The measurement times are strictly increasing in `i`. -/
  t_strictMono : StrictMono t
  /-- Every recorded internal temperature is a positive absolute temperature
  (K). -/
  T_IC_pos : ∀ i, 0 < T_IC i
  /-- Every recorded external temperature is a positive absolute temperature
  (K). -/
  T_OC_pos : ∀ i, 0 < T_OC i

/-- **Effective thermal law (the exam's Equation (4)).**  The heat `ΔQ`
received by the water in the **IC** through the acrylic wall during the time
interval `Δt` obeys

    ΔQ / Δt = (1 / R_Th) · (T_OC − T_IC),

where `R_Th > 0` is the effective thermal resistance of the wall (which
depends on its material and geometry); the positivity of `R_Th` is part of
the physical law — it is what makes the heat flow ΔQ point from the hotter
toward the cooler body.  We write the relation in interval form:
`ΔQ = (T_OC − T_IC) · Δt / R_Th`.  This is the governing heat-flow law of
Part C; it is recorded here as the physical law any such record satisfies,
to be used in later subquestions (C.5, C.6). -/
structure EffectiveThermalLaw (R_Th : ℝ) (ΔQ Δt T_OC T_IC : ℝ) : Prop where
  /-- The wall's effective thermal resistance is positive (heat flows from
  the hotter toward the cooler body). -/
  R_Th_pos : 0 < R_Th
  /-- The effective thermal law `ΔQ/Δt = (1/R_Th)·(T_OC − T_IC)`, in
  interval form `ΔQ = (T_OC − T_IC)·Δt/R_Th`. -/
  law : ΔQ = (T_OC - T_IC) * Δt / R_Th

/-- **Radial Fourier conduction (the exam's Equation (6)).**  For radial
heat conduction through the slim acrylic cylindrical wall, the heat flow is

    dQ / dt = −λ · A · dT/dr,

with `λ > 0` the thermal conductivity of the acrylic, `A > 0` the wall area
through which the heat flows, and `dT/dr` the radial temperature gradient.
This is the local form of the conduction law, recorded as the physical law
governing the wall; it is used in later subquestions (C.6) to estimate the
thermal conductivity of acrylic.  The positivity of `λ` and `A` is part of
the physical regime. -/
structure RadialFourierLaw (lam A dQdt dTdr : ℝ) : Prop where
  /-- The thermal conductivity of the acrylic is positive. -/
  lam_pos : 0 < lam
  /-- The wall area through which the heat flows is positive. -/
  A_pos : 0 < A
  /-- The radial Fourier law `dQ/dt = −λ·A·dT/dr`. -/
  law : dQdt = -lam * A * dTdr

/-- **The C.2 single-graph plot (display predicate).**  A candidate plot for
subquestion C.2 is an admissible display when it plots **both** temperature
series **on a single graph sharing one common time axis**: it carries a
time axis (s), an internal-temperature (`T_IC`, K) coordinate list, and an
external-temperature (`T_OC`, K) coordinate list, all of the same positive
length (the shared abscissa), such that **every** recorded internal point
`(tᵢ, T_ICᵢ)` and **every** recorded external point `(tᵢ, T_OCᵢ)` of the
C.1 record occur as displayed points on that common time axis.  This captures
"on a single graph, plot `T_IC` and `T_OC` as functions of time `t`". -/
structure IsSingleGraphPlot (d : C1Record) (tAxis ICaxis OCaxis : List ℝ) : Prop where
  /-- The shared time axis and the internal-temperature series have the same
  length. -/
  length_t_IC : tAxis.length = ICaxis.length
  /-- The shared time axis and the external-temperature series have the same
  length. -/
  length_t_OC : tAxis.length = OCaxis.length
  /-- At least one point is displayed. -/
  length_pos : 0 < tAxis.length
  /-- Every recorded internal-temperature point `(tᵢ, T_ICᵢ)` occurs among
  the displayed points on the common time axis. -/
  ICdisplayed : ∀ i, (d.t i, d.T_IC i) ∈ tAxis.zip ICaxis
  /-- Every recorded external-temperature point `(tᵢ, T_OCᵢ)` occurs among
  the displayed points on the same common time axis. -/
  OCdisplayed : ∀ i, (d.t i, d.T_OC i) ∈ tAxis.zip OCaxis

/-- **IPhO 2026, E1-C.2 (answer-blind).**  *On a single graph, plot `T_IC`
and `T_OC` as functions of time `t`.*

Given the C.1 time–temperature record `d` and the effective thermal
resistance `R_Th > 0` of the wall (the governing-law parameter of Part C),
there exists the requested single-graph plot: a shared time axis together
with internal- and external-temperature coordinate lists that display every
recorded internal point `(tᵢ, T_ICᵢ)` and every recorded external point
`(tᵢ, T_OCᵢ)` together on one common time axis.

The theorem asserts the existence of this plot only; no measured
temperature, no time value, no equilibrium temperature `T_eq`, and no plot
witness appears in the statement.  The prover may construct the witness (the
two observed time series) later. -/
theorem problem_IPhO_2026_4_C_2 (d : C1Record) (R_Th : ℝ) (hR : 0 < R_Th) :
    ∃ (tAxis ICaxis OCaxis : List ℝ), IsSingleGraphPlot d tAxis ICaxis OCaxis := by
  -- `zip` of two `ofFn` series is the `ofFn` of the pointwise pairing (no Mathlib API).
  have zip_ofFn : ∀ {n : ℕ} (f g : Fin n → ℝ),
      (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro f g
      rw [show List.ofFn f = f 0 :: List.ofFn (fun i => f i.succ) from
            (List.ofFn_succ (f := f)),
          show List.ofFn g = g 0 :: List.ofFn (fun i => g i.succ) from
            (List.ofFn_succ (f := g)),
          show List.ofFn (fun i => (f i, g i)) =
            (f 0, g 0) :: List.ofFn (fun i => (f i.succ, g i.succ)) from
            (List.ofFn_succ (f := fun i => (f i, g i))),
          List.zip_cons_cons]
      congr 1
      · exact ih (fun i => f i.succ) (fun i => g i.succ)
  refine ⟨List.ofFn d.t, List.ofFn d.T_IC, List.ofFn d.T_OC, by simp, by simp, ?_, ?_, ?_⟩
  · have h2 : 2 ≤ d.k := d.two_le
    rw [List.length_ofFn]
    omega
  · intro i
    rw [zip_ofFn d.t d.T_IC, List.mem_ofFn]
    exact ⟨i, rfl⟩
  · intro i
    rw [zip_ofFn d.t d.T_OC, List.mem_ofFn]
    exact ⟨i, rfl⟩

end PartC2
end IPhO_2026_4
