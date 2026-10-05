import Mathlib

/-!
# IPhO 2026, Experimental Exam (E1), Part C.3 — answer-blind formalization

## Physical setup (E1, Part C: heat conduction)

Water in the **inner cylinder (IC)** and water in the **outer cylinder (OC)**
exchange heat *radially* through the **acrylic cylindrical wall** that
separates them (Figure 17 bathtub geometry).  The procedure for Part C
(E1 page 13) is:

1. set the OC water level to `h = 15 cm`;
2. heat the OC water to `65 °C`, homogenizing it with the pump;
3. set the IC water level to `h = 10 cm` and start the stopwatch.

The two water temperatures are then recorded as functions of time (C.1):
`T_IC` (inner, initially cooler) and `T_OC` (outer, initially hotter).  Heat
conduction through the wall follows the exam's Equation (4),

```
dQ/dt = (T_OC − T_IC) / R_Th ,
```

where `Q` is the heat received by the water in the IC through the wall and
`R_Th` is the effective thermal resistance of the acrylic wall.  For
questions C3 and C4 the exam instructs: **ignore the heat capacity of the
apparatus**.  On the same page the exam defines `T_eq` as *the equilibrium
temperature that would be reached by both IC and OC if there were no heat
transfer to the environment* — the run is therefore embedded in an
environment, and the two water bodies are in mutual thermal contact across
the wall throughout the measurement.

## Current subquestion (E1–C.3, 0.7 pt)

> *Plot `T_OC − T_IC` as functions of both `T_OC` and `T_IC` on the same
> graph, with `T_OC` and `T_IC` together on the same temperature axis and
> `T_OC − T_IC` on the other axis.*

The requested object is the displayed two-curve figure itself — the exam
withholds no derived scalar here, and none is placed in any signature.  The
data plotted are the C.1 time–temperature record; per the project dependency
policy C.1's Lean output is not imported, so the record is re-modeled here
from the natural-language statement.

## Answer-blind statement design (iter-006 redraft)

* `CoolingRecord` — the C.1 record: sampled times and the two temperature
  traces, extended by the *heat received by the IC* over each sampling
  interval (a physically well-defined experimental quantity, kept
  answer-free).
* `HeatFlowModel` — the exam's Equation (4) applied interval-wise, in the
  instructed "ignore apparatus heat capacity" regime; `R_Th > 0` makes it
  the sign-carrying law of the only IC–OC exchange channel.
* `temperatureOrdering` — the physical ordering `T_IC j ≤ T_OC j` at every
  sampled instant, stated **directly as an explicit, labeled hypothesis**
  (iter-005 review directive): the hotter OC body heats the cooler IC body
  through the wall and their temperatures can only approach the common
  equilibrium value, never cross.  The environmental heat transfer
  acknowledged by the exam's own `T_eq` definition breaks any honest
  first-principles derivation of this ordering from Equation (4) alone in
  the discrete model, so it is named explicitly instead of being smuggled
  through fabricated combined-energy axioms.
* `CommonAxesPlot`, `CurvePoint`, `DisplaysAgainstOC`, `DisplaysAgainstIC`,
  `CoversRecord`, `CoversRecord'`, `SatisfiesC3` — the answer-free plot
  structures: one shared temperature axis carrying both `T_OC` and `T_IC`
  readings, the `T_OC − T_IC` ordinate axis, and the two requested curves
  drawn on these common axes, each with its own point list reparametrizing
  and covering the record.

No temperature value, graph window, slope, or equilibrium temperature appears
in any theorem signature; the prover may construct the display later.

## Iter-012 redraft note (review repair, iter-011 `needs_redraft`)

The iter-011 proof review (`underdetermined_contract`) showed the previous
`SatisfiesC3` was mathematically false: sharing *one* displayed point list
between both curves forced `T_OC (ι_OC n) = T_IC (ι_IC n)` at every
position `n` with both index maps surjective onto `Fin d.k` (counterexample
record `k = 2`, `T_IC = (0, 0)`, `T_OC = (1, 0)`).  The review's repair —
applied here — gives **each curve its own point list** (`plottedAgainstOC`,
`plottedAgainstIC`, each with its own reparametrization of the whole
record) while the two **axes** (`temperatureAxis`, `deltaAxis`), now
functions on `ℝ`, remain the single shared axis *pair* of the figure; the
hypotheses and the answer-free theorem signature are unchanged.  With
`plottedAgainstOC n = (T_OC n, T_OC n − T_IC n)` (and the `T_IC`
version) the display equalities become definitional, so existence is
provable honestly.
-/

namespace IPhO_2026_4
namespace PartC3

/-- **The C.1 time–temperature record (answer-free re-model).**  Water
temperatures of the two cylinders recorded as functions of time during the
Part-C cooldown:

* `time j` — the `j`-th sampled time `t_j` (s), strictly increasing;
* `T_IC j`, `T_OC j` — the inner / outer water temperatures sampled at
  `t_j` (same temperature unit throughout the exam as printed);
* `ΔQ j` — the heat received by the water in the IC through the wall
  during the interval `(t_{j-1}, t_j]`, for `1 ≤ j` (J).

The procedure fixes the first reading at the moment the stopwatch starts:
the OC water has just been heated to `65 °C` and is warmer than the freshly
filled IC water (`T_IC 0 < T_OC 0`). -/
structure CoolingRecord where
  /-- Number of sampled instants `t₀, t₁, …, t_{k-1}`. -/
  k : ℕ
  /-- At least two instants are sampled (a curve needs at least two
  points). -/
  two_le : 2 ≤ k
  /-- Sampled measurement times (s). -/
  time : Fin k → ℝ
  /-- The stopwatch starts at the first reading. -/
  time_zero : time ⟨0, by omega⟩ = 0
  /-- Sampled times are strictly increasing. -/
  time_strictMono : StrictMono time
  /-- Sampled inner-cylinder water temperatures `T_IC`. -/
  T_IC : Fin k → ℝ
  /-- Sampled outer-cylinder water temperatures `T_OC`. -/
  T_OC : Fin k → ℝ
  /-- The OC water starts hotter than the IC water (procedure steps 2–3:
  the OC water has just been heated to `65 °C` while the freshly filled IC
  water is cooler). -/
  temp_ordered_zero : T_IC ⟨0, by omega⟩ < T_OC ⟨0, by omega⟩
  /-- `ΔQ j` is the heat received by the IC water through the wall during
  the interval `(t_{j-1}, t_j]`, for `j ≥ 1`; `ΔQ 0 = 0` before any
  interval has elapsed. -/
  ΔQ : Fin k → ℝ
  /-- No heat has yet flowed at the first instant. -/
  ΔQ_zero : ΔQ ⟨0, by omega⟩ = 0

/-- **Exam Equation (4), interval-wise, apparatus heat capacity ignored.**
Over each sampling interval `(t_{j-1}, t_j]` the heat-flow model
`dQ/dt = (T_OC − T_IC) / R_Th` gives the recorded IC heat intake as

`ΔQ j = (T_OC j − T_IC j) / R_Th · (time j − time (j − 1))`.

This is the discrete read of the exam's Equation (4) at the recorded
samples, with the end-of-interval temperature difference (the record's own
readings — the same finite-measurement convention the exam itself uses when
it converts Equation (4) to Equation (5)); here `R_Th > 0` is the effective
thermal resistance of the acrylic wall (K/W).  Since `ΔQ` is the heat
*received by the IC*, Equation (4) with `R_Th > 0` makes the IC heat intake
positive exactly while the outer water is the hotter body — the
sign-carrying law of the only IC–OC exchange channel. -/
def HeatFlowModel (d : CoolingRecord) (R_Th : ℝ) : Prop :=
  ∀ j : Fin d.k, 0 < (j : ℕ) →
    d.ΔQ j = (d.T_OC j - d.T_IC j) / R_Th *
      (d.time j - d.time ⟨j - 1, by have := j.isLt; omega⟩)

/-- **A point of a C.3 curve.**  One plotted `(temperature, difference)`
pair: `temperature` lies on the shared temperature axis of the figure and
`difference` on the shared `T_OC − T_IC` axis. -/
structure CurvePoint where
  /-- Abscissa on the shared temperature axis (°C, as printed). -/
  temperature : ℝ
  /-- Ordinate on the shared `T_OC − T_IC` axis. -/
  difference : ℝ

/-- **The C.3 common-axes plot.**  The figure requested by C.3: a **single
pair of shared axes** — one *temperature axis* carrying both `T_OC` and
`T_IC` readings ("`T_OC` and `T_IC` together on the same temperature
axis") and one ordinate axis carrying the temperature difference
`T_OC − T_IC` — on which **two curves** are drawn, each with its own point
list reparametrizing the whole record:

* `temperatureAxis`, `deltaAxis` — the scales of the two shared axes
  (mapping axis mark values to their page positions); one axis carries the
  `T_OC` *and* `T_IC` readings alike, the other the differences;
* `plottedAgainstOC` — the `T_OC − T_IC` *against `T_OC`* curve;
* `plottedAgainstIC` — the `T_OC − T_IC` *against `T_IC`* curve, drawn on
  the same graph ("on common axes").

The two point lists are independent (the review repair of iter-011): both
curves live on the same axis pair, but no single list of positions is
shared between them, so the two abscissa series never have to coincide. -/
structure CommonAxesPlot where
  /-- The shared temperature-axis scale. -/
  temperatureAxis : ℝ → ℝ
  /-- The shared `T_OC − T_IC`-axis scale. -/
  deltaAxis : ℝ → ℝ
  /-- Number of plotted points of the difference-against-`T_OC` curve. -/
  w : ℕ
  /-- At least one point is plotted. -/
  w_pos : 0 < w
  /-- The `T_OC − T_IC` against `T_OC` curve. -/
  plottedAgainstOC : Fin w → CurvePoint
  /-- Number of plotted points of the difference-against-`T_IC` curve. -/
  w' : ℕ
  /-- At least one point is plotted. -/
  w'_pos : 0 < w'
  /-- The `T_OC − T_IC` against `T_IC` curve, on the same axes. -/
  plottedAgainstIC : Fin w' → CurvePoint

/-- **Display of the `T_OC − T_IC` against `T_OC` curve.**  With the
section index `n` labelling the recorded instant `t_n`, the points of this
curve are the pairs `(T_OC (ι n), T_OC (ι n) − T_IC (ι n))` taken from the
record — placed on the shared axes `p.temperatureAxis` (carrying the
recorded `T_OC` readings) and `p.deltaAxis` (carrying the recorded
differences), and re-indexed by `ι`. -/
def DisplaysAgainstOC (d : CoolingRecord) (p : CommonAxesPlot)
    (ι : Fin p.w → Fin d.k) : Prop :=
  ∀ n, p.plottedAgainstOC n =
    { temperature := p.temperatureAxis (d.T_OC (ι n)),
      difference := p.deltaAxis (d.T_OC (ι n) - d.T_IC (ι n)) }

/-- **Display of the `T_OC − T_IC` against `T_IC` curve.**  As
`DisplaysAgainstOC`, but with the shared temperature axis carrying the
recorded `T_IC` readings: the points are
`(T_IC (ι' n), T_OC (ι' n) − T_IC (ι' n))` on the same two axes. -/
def DisplaysAgainstIC (d : CoolingRecord) (p : CommonAxesPlot)
    (ι' : Fin p.w' → Fin d.k) : Prop :=
  ∀ n, p.plottedAgainstIC n =
    { temperature := p.temperatureAxis (d.T_IC (ι' n)),
      difference := p.deltaAxis (d.T_OC (ι' n) - d.T_IC (ι' n)) }

/-- **Reparametrization of the recorded curve (against-`T_OC`).**  The
displayed points of this C.3 curve are the recorded
`(temperature, difference)` pairs taken in some order along the record:
`ι` selects, for each displayed point, the recorded instant it came from,
and every recorded instant is displayed (surjectivity — the plot shows the
whole record). -/
def CoversRecord (d : CoolingRecord) (p : CommonAxesPlot)
    (ι : Fin p.w → Fin d.k) : Prop :=
  Function.Surjective ι

/-- **Coverage of the second curve's record.**  As `CoversRecord`, for the
difference-against-`T_IC` curve's own reparametrization `ι'`. -/
def CoversRecord' (d : CoolingRecord) (p : CommonAxesPlot)
    (ι' : Fin p.w' → Fin d.k) : Prop :=
  Function.Surjective ι'

/-- **The C.3 deliverable (answer-free).**  A candidate figure satisfies
subquestion C.3 for the record `d` when it is drawn on a single pair of
common axes (`temperatureAxis` shared by both readings, `deltaAxis`
carrying `T_OC − T_IC`) and both requested curves appear on it: the
difference-against-`T_OC` curve and the difference-against-`T_IC` curve,
each with its own point list (`ι_OC`, `ι_IC`) reparametrizing and covering
the whole record.  Moreover the displayed figure respects the physical
ordering of the run: at every recorded instant the OC reading is at or
above the matching IC reading, so both curves are drawn on the nonnegative
half of the `T_OC − T_IC` axis — the initial OC-heats-IC imbalance is
never reversed in the mutual-exchange regime. -/
def SatisfiesC3 (d : CoolingRecord) (p : CommonAxesPlot) : Prop :=
  ∃ (ι_OC : Fin p.w → Fin d.k) (ι_IC : Fin p.w' → Fin d.k),
    CoversRecord d p ι_OC ∧ CoversRecord' d p ι_IC ∧
      DisplaysAgainstOC d p ι_OC ∧ DisplaysAgainstIC d p ι_IC ∧
        ∀ j, d.T_IC j ≤ d.T_OC j

/-- **IPhO 2026, E1–C.3 (answer-blind).**  *On common axes, plot
`T_OC − T_IC` as functions of both `T_OC` and `T_IC`, with `T_OC` and
`T_IC` together on the same temperature axis and `T_OC − T_IC` on the other
axis.*

Given a C.1 time–temperature record `d` of the run for which

* the wall's thermal resistance is positive (`hR`),
* the interval-wise heat-flow model of the exam's Equation (4) holds with
  the apparatus heat capacity ignored (`heatFlow`), and
* the physical ordering of the run holds at every sampled instant
  (`temperatureOrdering`: the outer water stays at or above the inner
  water temperature — the explicit, labeled premise of the C.3/C.4 regime,
  stated directly per the iter-005 review directive rather than encoded
  through combined-energy axioms),

there exists a common-axes figure satisfying `SatisfiesC3`: both requested
`T_OC − T_IC` curves displayed against the shared temperature axis.

The theorem asserts the existence of the figure only; no recorded value,
axis window, reparametrization, or equilibrium temperature appears in the
statement. -/
theorem problem_IPhO_2026_4_C_3 (d : CoolingRecord) (R_Th : ℝ) (hR : 0 < R_Th)
    (heatFlow : HeatFlowModel d R_Th)
    (temperatureOrdering : ∀ j : Fin d.k, d.T_IC j ≤ d.T_OC j) :
    ∃ p : CommonAxesPlot, SatisfiesC3 d p := by
  -- The canonical witness: identity axis scales (`temperatureAxis = deltaAxis
  -- = id`, i.e. each axis mark placed at its own value), both curves running
  -- over all `k` recorded points in the recorded order (`ι_OC = ι_IC = id`).
  -- Each display equality then holds definitionally (`rfl`), coverage is
  -- surjectivity of the identity, and the ordering conjunct is exactly the
  -- labeled premise `temperatureOrdering`.
  exact ⟨{ temperatureAxis := id, deltaAxis := id,
           w := d.k, w_pos := Nat.lt_of_lt_of_le (by decide) d.two_le,
           plottedAgainstOC :=
             fun n => { temperature := id (d.T_OC n),
                        difference := id (d.T_OC n - d.T_IC n) },
           w' := d.k, w'_pos := Nat.lt_of_lt_of_le (by decide) d.two_le,
           plottedAgainstIC :=
             fun n => { temperature := id (d.T_IC n),
                        difference := id (d.T_OC n - d.T_IC n) } },
         id, id, Function.surjective_id, Function.surjective_id,
         fun _ => rfl, fun _ => rfl, temperatureOrdering⟩

end PartC3
end IPhO_2026_4
