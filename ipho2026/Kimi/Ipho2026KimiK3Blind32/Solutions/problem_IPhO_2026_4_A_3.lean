import Mathlib

/-!
# IPhO 2026 — Experimental Problem 4 (E1), Part A, Subquestion A.3

## Physical setting (official statement, page 9 of E1)

Part A studies the **isochoric (isovolumetric) process** of the confined air
column **CA** sealed in the inner cylinder **IC**.  Propylene glycol **PG**
is introduced into IC to the height `h = 4.5 cm` and the valves **D** and
**E** are closed, so the volume `V`, the amount of substance `n`, and the
mass of **CA** are fixed.  The confined air obeys the ideal-gas equation of
state

    P * V = n * R * T                                   (equation (1) of E1)

with `R` the universal gas constant.  The outer cylinder **OC** is filled
with water that is progressively heated (the temperature being homogenized
by the pump), and the sensor console records the pressure and temperature
of CA.

* **A.1** — determine the mass `m`, the number of moles `n` and the total
  number `N` of air molecules of CA (its Lean statement is a separate file).
* **A.2** — record in a table the pressure `P` of CA as a function of its
  temperature `T` (natural-language prerequisite only; its Lean output is
  neither imported nor assumed here).
* **A.3 (this file)** — *from the data obtained in question A.2, plot the
  behavior of pressure as a function of temperature.*

At the fixed volume of Part A the ideal-gas law says that `P` is a linear
(proportional) function of `T` with positive slope `n · R / V`, which is
precisely the behavior the requested plot exhibits.

## Answer-blind modeling

The A.2 measurement data are deliberately withheld, so no numerical values
or explicit plot parameters appear in the theorem signatures below.  A
*plot* is modeled as a graph `ℝ → ℝ` drawn on Cartesian axes together with
the physical quantities and units of its axes (the general instructions
require every graph to clearly show the quantities involved and their
units).  Subquestion A.3 is characterized answer-free by

1. **existence** — from the A.2 data one can draw a Cartesian plot, clearly
   showing the plotted quantities and units, that passes through every
   recorded pressure–temperature pair;
2. **classification / uniqueness of the behavior** — the graphs that
   simultaneously represent the recorded data and obey the isochoric
   ideal-gas law agree with each other and with the isochoric relation
   `T ↦ (n · R / V) · T` on every recorded temperature, with positive
   slope `n · R / V`.

The concrete slope `(n · R / V)` stays out of the statement's conclusion as
a number: it is expressed through the confined-gas parameters only, and its
*experimental* determination from the A.3 plot is the subject of
subquestion A.4.

## Data regularity recorded from A.2 (redraft repair)

Because A.2 records pressure *as a function of* temperature, the table is
single-valued: entries taken at the same temperature record a common
pressure.  This is captured by the `ObservationTable.single_valued`
field (a genuine *measurement*-function condition — the physical readings
themselves are equal — not by any target relation and not by the answer);
without it no functional graph could pass through every pair, so the
existence part of the formalization would be false.
-/

namespace Ipho2026.Problem4.A3

/-- Parameters of the Part A experiment: the geometry and confined-gas state
of the apparatus once the propylene glycol (PG) has been introduced into the
inner cylinder (IC) to the height `h = 4.5 cm` and the valves D and E have
been closed, sealing the confined air column (CA) at fixed volume, together
with the universal gas constant `R` of the ideal-gas law `P * V = n * R * T`
(equation (1) of the statement; its experimental determination from the A.3
plot is the subject of subquestion A.4). -/
structure ConfinedAirColumn where
  /-- the universal gas constant `R`, in J·K⁻¹·mol⁻¹. -/
  gasConstant : ℝ
  /-- height `h` of the PG column introduced into IC, in cm (`4.5` in Part A). -/
  pgHeightCm : ℝ
  /-- fixed volume `V` of the confined air column CA, in m³. -/
  volume : ℝ
  /-- amount of substance `n` of the confined air, in mol (determined in A.1). -/
  moles : ℝ
  /-- fixed mass `m` of the confined air, in kg (determined in A.1). -/
  mass : ℝ
  /-- total number `N` of air molecules in CA (determined in A.1). -/
  molecules : ℝ
  /-- the universal gas constant is positive. -/
  gasConstant_pos : 0 < gasConstant
  /-- the PG height is positive. -/
  pgHeightCm_pos : 0 < pgHeightCm
  /-- the confined volume is positive. -/
  volume_pos : 0 < volume
  /-- the confined amount of substance is positive. -/
  moles_pos : 0 < moles

/-- The time-averaged ambient air density in Bucaramanga, `ρ = 1.12 kg/m³`,
kept as part of the Part A parameter set: it fixes the confined-gas
inventory in A.1 and hence the physical state whose behavior is plotted
here.  Central value only; no uncertainty is quoted in the statement. -/
structure AmbientConditions where
  /-- ambient air density `ρ`, in kg·m⁻³ (time-averaged value `1.12`). -/
  airDensity : ℝ
  /-- the ambient density is positive. -/
  airDensity_pos : 0 < airDensity

/-- The ideal-gas law as a state relation (equation (1) of the statement):
the state `(P, T, V, n)` of the confined air obeys `P * V = n * R * T`, with
`R` the universal gas constant, `P` the (absolute) pressure in Pa, `T` the
absolute temperature in K, `V` the volume in m³ and `n` the amount of
substance in mol. -/
def IdealGasLaw (R P T V n : ℝ) : Prop :=
  P * V = n * R * T

/-- The isochoric (isovolumetric) regime of Part A: the volume `V` and the
amount `n` of the confined air column are held constant while the outer
water bath is heated (PG at `h = 4.5 cm`, valves D and E closed). -/
structure IsochoricRegime (ca : ConfinedAirColumn) where
  /-- the unchanging volume of CA, equal to `ca.volume`. -/
  fixedVolume : ℝ
  /-- the unchanging amount of substance of CA, equal to `ca.moles`. -/
  fixedMoles : ℝ
  fixedVolume_eq : fixedVolume = ca.volume
  fixedMoles_eq : fixedMoles = ca.moles

/-- One observation of subquestion A.2: a pair consisting of the recorded
pressure `P` of the confined air column (Pa) and its temperature `T` (K),
read simultaneously while the outer water bath is heated. -/
structure Observation where
  /-- recorded pressure of CA, in Pa. -/
  pressure : ℝ
  /-- recorded temperature of CA, in K. -/
  temperature : ℝ

/-- The observation table produced in subquestion A.2 ("record in a table
the pressure `P` of the CA as a function of its temperature `T`"): a finite
list of simultaneously measured `(P, T)` pairs, nonempty, and single-valued
in the sense that pressure is recorded *as a function of* temperature.
Modeled from scratch in this file; the A.2 Lean output is not imported per
the dependency policy. -/
structure ObservationTable where
  /-- the recorded observations. -/
  entries : List Observation
  /-- the table contains at least one observation. -/
  entries_nonempty : entries ≠ []
  /-- pressure is recorded as a function of temperature: any two entries
  read at the same temperature record the same pressure.  This is a
  regularity condition on the A.2 measurements themselves (the requested
  functional plot would otherwise not exist), not a conditioned answer. -/
  single_valued : ∀ obs₁ ∈ entries, ∀ obs₂ ∈ entries,
    obs₁.temperature = obs₂.temperature → obs₁.pressure = obs₂.pressure

/-- An observation series is *consistent* with the isochoric ideal gas of
Part A when every observation satisfies `P * V = n * R * T` at the fixed
volume, the fixed amount and the universal gas constant of the confined air
column — i.e. when every measured point lies on the isochoric P–T line that
the ideal-gas law prescribes. -/
def ObservationTable.ConsistentWithIsochoricIdealGas {ca : ConfinedAirColumn}
    (table : ObservationTable) (reg : IsochoricRegime ca) : Prop :=
  ∀ obs ∈ table.entries,
    IdealGasLaw ca.gasConstant obs.pressure obs.temperature reg.fixedVolume
      reg.fixedMoles

/-- A physical (dimensional) quantity represented on a graph axis: the
general instructions require that all graphs clearly show the quantities
involved and that the units of all values used are indicated. -/
structure AxisQuantity where
  /-- name of the plotted quantity (e.g. the pressure `P` of CA). -/
  name : String
  /-- unit of the values on the axis (e.g. Pa or K). -/
  unit : String

/-- The quantities involved in the plot requested by subquestion A.3:
the pressure of the confined air column (ordinate) and its temperature
(abscissa), as named in the A.2/A.3 boxes ("the pressure `P` … as a
function of its temperature `T`").  The concrete units chosen for the axes
are part of the student's plot and are left abstract. -/
structure PlotQuantities where
  /-- ordinate quantity: pressure `P` of CA. -/
  pressure : AxisQuantity
  /-- abscissa quantity: temperature `T` of CA. -/
  temperature : AxisQuantity

/-- A Cartesian plot of the kind requested in subquestion A.3: an ordinate
value (pressure, in the unit of `quantities.pressure`) for every abscissa
argument (temperature, in the unit of `quantities.temperature`), drawn on
axes clearly showing the plotted quantities and their units. -/
structure CartesianPlot (quantities : PlotQuantities) where
  /-- the plotted relation: the represented pressure at each temperature
  argument. -/
  graph : ℝ → ℝ

/-- A graph represents a pressure–temperature observation when it passes
through the recorded point: its value at the recorded temperature is the
recorded pressure. -/
def PressureAsFunctionOfTemperature (f : ℝ → ℝ) (obs : Observation) : Prop :=
  f obs.temperature = obs.pressure

/-- A *plot of the A.2 data*: every recorded pressure–temperature pair of
the A.2 table appears on the graph, i.e. the graph passes through every
recorded point. -/
def CartesianPlot.PlotsData {quantities : PlotQuantities}
    (plot : CartesianPlot quantities) (table : ObservationTable) : Prop :=
  ∀ obs ∈ table.entries, PressureAsFunctionOfTemperature plot.graph obs

/-- Answer-free specification of subquestion A.3 — a *solution plot* is a
Cartesian plot, clearly showing the plotted quantities and their units,
that represents every pressure–temperature pair recorded in the A.2
table. -/
structure SolutionPlot (quantities : PlotQuantities)
    (table : ObservationTable) where
  /-- the underlying Cartesian plot. -/
  plot : CartesianPlot quantities
  /-- the plot passes through every recorded data point. -/
  plots_data : plot.PlotsData table

/-- **Existence (A.3):** from the data obtained in question A.2 one can draw
the requested plot — there exists a Cartesian plot, clearly showing the
pressure and temperature quantities with their units, that passes through
every recorded pressure–temperature pair. -/
theorem plot_exists (quantities : PlotQuantities) (table : ObservationTable) :
    Nonempty (SolutionPlot quantities table) := by
  have key : ∀ T : ℝ, ∃ P : ℝ, ∀ ob ∈ table.entries,
      ob.temperature = T → P = ob.pressure := by
    intro T
    by_cases h : ∃ ob ∈ table.entries, ob.temperature = T
    · obtain ⟨ob₀, hmem, hT⟩ := h
      exact ⟨ob₀.pressure, fun ob hob ht =>
        table.single_valued ob₀ hmem ob hob (hT.trans ht.symm)⟩
    · exact ⟨0, fun ob hob ht => absurd ⟨ob, hob, ht⟩ h⟩
  choose g hg using key
  exact ⟨{ graph := g }, fun ob hmem => hg ob.temperature ob hmem rfl⟩

/-- **Isochoric ideal-gas behavior (A.3):** if every observation recorded in
the A.2 table is consistent with the ideal-gas law at the fixed volume, the
fixed amount and the universal gas constant of the confined air column (the
isochoric regime of Part A), then every plot of the data exhibits pressure
as a linear function of temperature through the origin with positive slope
`n * R / V` — on every recorded temperature the plotted pressure equals
`(n * R / V) * T`.  This is precisely the behavior of pressure as a
function of temperature that subquestion A.3 asks to display. -/
theorem plot_behavior_isochoric_linear {ca : ConfinedAirColumn}
    (reg : IsochoricRegime ca) {table : ObservationTable}
    (hconsistent : table.ConsistentWithIsochoricIdealGas reg)
    {quantities : PlotQuantities} (plot : CartesianPlot quantities)
    (hplots : plot.PlotsData table) :
    (0 < reg.fixedMoles * ca.gasConstant / reg.fixedVolume) ∧
      ∀ obs ∈ table.entries,
        plot.graph obs.temperature =
          (reg.fixedMoles * ca.gasConstant / reg.fixedVolume) *
            obs.temperature := by
  have hV : 0 < reg.fixedVolume := by
    rw [reg.fixedVolume_eq]; exact ca.volume_pos
  have hmn : 0 < reg.fixedMoles := by
    rw [reg.fixedMoles_eq]; exact ca.moles_pos
  constructor
  · exact div_pos (mul_pos hmn ca.gasConstant_pos) hV
  · intro obs _
    have hpe : plot.graph obs.temperature = obs.pressure := hplots obs ‹_›
    have hlaw := hconsistent obs ‹_›
    have h2 : reg.fixedMoles * ca.gasConstant / reg.fixedVolume *
        obs.temperature =
        reg.fixedMoles * ca.gasConstant * obs.temperature /
          reg.fixedVolume := div_mul_eq_mul_div _ _ _
    rw [hpe, h2, eq_div_iff (ne_of_gt hV)]
    exact hlaw

/-- **Uniqueness of the plot relation on the data (A.3):** among all graphs
`f : T ↦ P`, the ones that simultaneously (i) represent every observation
recorded in the A.2 table and (ii) obey the isochoric ideal-gas law
`f(T) * V = n * R * T` at the fixed volume and the fixed amount of the
confined air column are exactly the graphs whose value on every recorded
temperature is `(n * R / V) * T`; any two such graphs agree on every
temperature recorded in the A.2 table.  The concrete slope `(n * R / V)`
stays out of the conclusion as an experimental value: it is expressed only
through the confined-gas parameters, and its experimental determination
from the plot is the subject of subquestion A.4. -/
theorem plot_relation_unique_on_data {ca : ConfinedAirColumn}
    (reg : IsochoricRegime ca) (table : ObservationTable)
    {f g : ℝ → ℝ}
    (hf_data : ∀ obs ∈ table.entries,
      PressureAsFunctionOfTemperature f obs)
    (hf_law : ∀ T, IdealGasLaw ca.gasConstant (f T) T reg.fixedVolume
      reg.fixedMoles)
    (hg_data : ∀ obs ∈ table.entries,
      PressureAsFunctionOfTemperature g obs)
    (hg_law : ∀ T, IdealGasLaw ca.gasConstant (g T) T reg.fixedVolume
      reg.fixedMoles) :
    (∀ obs ∈ table.entries,
      f obs.temperature =
        (reg.fixedMoles * ca.gasConstant / reg.fixedVolume) *
          obs.temperature) ∧
    (∀ obs ∈ table.entries, f obs.temperature = g obs.temperature) := by
  have hV : 0 < reg.fixedVolume := by
    rw [reg.fixedVolume_eq]; exact ca.volume_pos
  have key : ∀ {h : ℝ → ℝ},
      (∀ T, IdealGasLaw ca.gasConstant (h T) T reg.fixedVolume
        reg.fixedMoles) →
      ∀ obs ∈ table.entries,
        h obs.temperature =
          (reg.fixedMoles * ca.gasConstant / reg.fixedVolume) *
            obs.temperature := by
    intro h hlaw obs _
    have h2 : reg.fixedMoles * ca.gasConstant / reg.fixedVolume *
        obs.temperature =
        reg.fixedMoles * ca.gasConstant * obs.temperature /
          reg.fixedVolume := div_mul_eq_mul_div _ _ _
    rw [h2, eq_div_iff (ne_of_gt hV)]
    exact hlaw obs.temperature
  exact ⟨key hf_law,
    fun obs hmem => (key hf_law obs hmem).trans (key hg_law obs hmem).symm⟩

/-- **IPhO 2026, E1, Part A.3 (final statement).** The behavior of the
pressure `P` of the confined air column as a function of its temperature
`T`, plotted from the data obtained in question A.2, admits an answer-free
characterization: for every observation table recorded in the isochoric
regime of Part A there exists a plot of the data (a Cartesian plot clearly
showing the pressure and temperature quantities with their units that
passes through every recorded pair), and any two graphs that both represent
the recorded data and obey the ideal-gas law at the fixed volume, fixed
amount and universal gas constant of the confined air column agree, on
every recorded temperature, with each other and with the isochoric
ideal-gas relation `T ↦ (n * R / V) * T`. -/
theorem problem_IPhO_2026_4_A_3 {ca : ConfinedAirColumn}
    (reg : IsochoricRegime ca) (table : ObservationTable)
    (quantities : PlotQuantities) :
    Nonempty (SolutionPlot quantities table) ∧
    (∀ {f g : ℝ → ℝ},
      (∀ obs ∈ table.entries, PressureAsFunctionOfTemperature f obs) →
      (∀ T, IdealGasLaw ca.gasConstant (f T) T reg.fixedVolume
        reg.fixedMoles) →
      (∀ obs ∈ table.entries, PressureAsFunctionOfTemperature g obs) →
      (∀ T, IdealGasLaw ca.gasConstant (g T) T reg.fixedVolume
        reg.fixedMoles) →
        (∀ obs ∈ table.entries,
          f obs.temperature =
            (reg.fixedMoles * ca.gasConstant / reg.fixedVolume) *
              obs.temperature) ∧
        (∀ obs ∈ table.entries, f obs.temperature = g obs.temperature)) := by
  exact ⟨plot_exists quantities table, fun hfd hfl hgd hgl =>
    plot_relation_unique_on_data reg table hfd hfl hgd hgl⟩

end Ipho2026.Problem4.A3
