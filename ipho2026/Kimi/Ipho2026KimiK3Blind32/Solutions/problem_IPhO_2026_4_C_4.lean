import Mathlib

/-!
# IPhO 2026, Experimental Exam (E1), Part C.4 — answer-blind formalization

## Physical setup (E1, Part C: heat conduction)

Water in the **inner cylinder (IC)** and water in the **outer cylinder (OC)**
exchange heat *radially* through the **acrylic cylindrical wall** that
separates them (Figure 17 bathtub geometry).  The procedure for Part C
(official page 13) is:

1. set the OC water level to `h = 15 cm`;
2. heat the OC water to `65 °C`, homogenizing it with the pump;
3. set the IC water level to `h = 10 cm` and start the stopwatch.

The two water temperatures are then recorded as functions of time: `T_IC`
(inner, initially cooler) and `T_OC` (outer, initially hotter).  Heat
conduction through the wall follows the exam's Equation (4),

```
dQ/dt = (T_OC − T_IC) / R_Th ,
```

where `Q` is the heat received by the water in the IC through the wall and
`R_Th` is the effective thermal resistance of the acrylic wall.  For
questions C3 and C4 the exam instructs: **ignore the heat capacity of the
apparatus**.

Immediately beneath C2 the statement fixes the key notion used in C4:

> *`T_eq` refers to the equilibrium temperature that would be reached by both
> IC and OC if there were no heat transfer to the environment.*

## Current subquestion (E1–C.4, 1.1 pt)

> *From the graphs constructed in C3, determine `T_eq`.  It is not necessary
> to calculate uncertainty for this question.*

Part C.3 (a natural-language prerequisite; its Lean output is **not**
imported per the project dependency policy) plots `T_OC − T_IC` against both
`T_OC` and `T_IC` on the same pair of common axes.  This question reads the
equilibrium temperature off that figure.  The physics is the conservation of
the combined thermal energy of the two water bodies in the no-environmental-
loss regime imagined in the `T_eq` definition.

### Why the two extracted quantities coincide

* With the apparatus heat capacity ignored and with no heat transferred to
  the environment, the combined thermal energy of the two water bodies,
  `E = m_IC c_w T_IC + m_OC c_w T_OC`, is conserved by the internal heat
  exchange through the wall.  Hence the *heat-capacity-weighted mean
  temperature*

  ```
  (m_IC T_IC + m_OC T_OC) / (m_IC + m_OC)
  ```

  is constant along the whole run; at equilibrium, where
  `T_IC = T_OC = T_eq`, that constant is exactly `T_eq`.  So `T_eq` is the
  persistent value of the combined-energy-per-total-heat-capacity ratio.

* On the C3 figure each recorded instant gives the two points
  `(T_OC, T_OC − T_IC)` and `(T_IC, T_OC − T_IC)`.  As the run relaxes the
  difference `T_OC − T_IC` shrinks towards `0`, and both curves tend to the
  common temperature `T_eq` — the single temperature at which the two
  plotted relations meet at zero difference.  This is the value read off the
  C3 graph.

Both characterizations single out the same `T_eq`; the proof that the
graphical zero-difference crossing equals the conserved weighted mean is the
content of the main theorem.

## Answer-blind statement design

The official value of `T_eq` is withheld.  Following the blind policy, the
theorem signature introduces a result variable `T_eq` of temperature role and
an answer-free solution predicate `IsEquilibriumTemperature` capturing the
*physical* content above:

* `ConservedWeightedMean` — the combined thermal energy, converted to a
  temperature by the total heat capacity, takes one and the same value at
  every sampled instant (internal exchange conserves it);
* `IsGraphicalEquilibrium` — that constant is the zero-difference crossing
  of the two C3 curves (the value both `T_OC` and `T_IC` approach as
  `T_OC − T_IC → 0`).

The main theorem then asserts existence and uniqueness of `T_eq`.  No
recorded temperature, closed form, numerical interval, or explicit weighted
mean appears in the signature; the prover may construct the witness later.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4C4

variable {ι : Type*}

/-- **Part-C heat-conduction data for C.4 (answer-free re-model).**

The C.1 time-temperature record together with the calorimetric content of the
two water bodies, in the instructed *ignore-apparatus-heat-capacity* regime:

* `m_IC`, `m_OC` — the masses of water in the inner and outer cylinders
  (from the IC level `h = 10 cm` and OC level `h = 15 cm` with the Figure 17
  geometry);
* `c_w` — the specific heat capacity of water (common to both bodies);
* `t` — the sampled measurement times `t_j` (s);
* `T_IC`, `T_OC` — the recorded inner / outer water temperatures `T_IC`,
  `T_OC` (same temperature unit throughout as printed);
* `start_ordered` — the procedure's initial imbalance: the OC water, freshly
  heated to `65 °C`, starts hotter than the freshly filled IC water
  (there is an instant with `T_IC < T_OC`);
* `energy_conserved` — the **governing law** behind the statement's `T_eq`
  definition: in the imagined no-environmental-loss regime, the two water
  bodies exchange heat only with each other through the wall (`dQ/dt = (T_OC −
  T_IC)/R_Th` is the *internal* exchange), so the combined thermal energy
  `m_IC c_w T_IC + m_OC c_w T_OC` takes one and the same value at every pair
  of sampled instants.  This is a constancy-of-energy law only; no
  temperature value, weighted-mean value, equilibrium temperature, or any
  other quantity requested by C.4 appears in it. -/
structure HeatConductionData (ι : Type*) where
  /-- Mass `m_IC` of the water in the inner cylinder (kg). -/
  m_IC : ℝ
  /-- Mass `m_OC` of the water in the outer cylinder (kg). -/
  m_OC : ℝ
  /-- Specific heat capacity `c_w` of water (J/(kg·K)). -/
  c_w : ℝ
  /-- Sampled measurement times `t` (s). -/
  t : ι → ℝ
  /-- Recorded internal (IC) water temperatures `T_IC`. -/
  T_IC : ι → ℝ
  /-- Recorded external (OC) water temperatures `T_OC`. -/
  T_OC : ι → ℝ
  /-- IC water mass is positive. -/
  m_IC_pos : 0 < m_IC
  /-- OC water mass is positive. -/
  m_OC_pos : 0 < m_OC
  /-- Specific heat capacity of water is positive. -/
  c_w_pos : 0 < c_w
  /-- The run has an initial imbalance: at some sampled instant the OC water
  is hotter than the IC water (procedure steps 2–3). -/
  start_ordered : ∃ j, T_IC j < T_OC j
  /-- **Governing law — conservation of the combined thermal energy.**
  With the apparatus heat capacity ignored (as instructed for C.4) and heat
  transferred only internally between the two water bodies through the wall,
  the combined thermal energy `m_IC c_w T_IC j + m_OC c_w T_OC j` is the same
  at every pair of sampled instants `j k`.  This encodes the
  no-heat-transfer-to-the-environment regime that the exam's `T_eq`
  definition imagines; it asserts the constancy of an *energy*, never the
  value of any temperature, weighted mean, or equilibrium temperature. -/
  energy_conserved :
    ∀ j k : ι, m_IC * c_w * T_IC j + m_OC * c_w * T_OC j =
      m_IC * c_w * T_IC k + m_OC * c_w * T_OC k

namespace HeatConductionData

variable (D : HeatConductionData ι)

/-- **Total heat capacity** of the two water bodies, `C = (m_IC + m_OC) c_w`
(J/K), with the apparatus heat capacity ignored as instructed for C.4. -/
noncomputable def totalHeatCapacity : ℝ := (D.m_IC + D.m_OC) * D.c_w

/-- The total heat capacity of the two water bodies is positive. -/
theorem totalHeatCapacity_pos : 0 < D.totalHeatCapacity :=
  mul_pos (add_pos D.m_IC_pos D.m_OC_pos) D.c_w_pos

/-- **Combined thermal energy** of the two water bodies at sampled instant
`j`, `E j = m_IC c_w T_IC j + m_OC c_w T_OC j` (J), measured from the
reference of the printed temperature scale and ignoring the apparatus heat
capacity.  Only its *conservation* matters for `T_eq`, so the choice of
temperature zero is inessential. -/
noncomputable def combinedEnergy (j : ι) : ℝ :=
  D.m_IC * D.c_w * D.T_IC j + D.m_OC * D.c_w * D.T_OC j

/-- **Combined-energy-per-total-heat-capacity**, the
heat-capacity-weighted mean temperature of the two water bodies at sampled
instant `j`,

```
weightedMean j = (m_IC T_IC j + m_OC T_OC j) / (m_IC + m_OC).
```

The common specific heat capacity `c_w` cancels between numerator and
denominator, so this is a pure temperature.  At thermal equilibrium
(`T_IC = T_OC = T_eq`) it reduces to `T_eq`. -/
noncomputable def weightedMean (j : ι) : ℝ :=
  D.combinedEnergy j / D.totalHeatCapacity

/-- The weighted-mean form of `weightedMean`: the heat-capacity-weighted
average of the two recorded temperatures, with `c_w` cancelled. -/
theorem weightedMean_eq (j : ι) :
    D.weightedMean j =
      (D.m_IC * D.T_IC j + D.m_OC * D.T_OC j) / (D.m_IC + D.m_OC) := by
  have hm : D.m_IC + D.m_OC ≠ 0 := ne_of_gt (add_pos D.m_IC_pos D.m_OC_pos)
  have hc : D.c_w ≠ 0 := ne_of_gt D.c_w_pos
  unfold weightedMean combinedEnergy totalHeatCapacity
  rw [div_eq_div_iff (mul_ne_zero hm hc) hm]
  ring

/-- At thermal equilibrium — both water bodies at the common temperature
`T_eq` — the heat-capacity-weighted mean temperature is `T_eq` itself. -/
theorem weightedMean_of_eq (j : ι) {T_eq : ℝ}
    (hIC : D.T_IC j = T_eq) (hOC : D.T_OC j = T_eq) :
    D.weightedMean j = T_eq := by
  rw [weightedMean_eq, hIC, hOC]
  have hm : D.m_IC + D.m_OC ≠ 0 := ne_of_gt (add_pos D.m_IC_pos D.m_OC_pos)
  field_simp

/-- **Conservation of the combined thermal energy (internal exchange, no
environmental loss).**  In the `T_eq` regime imagined by the statement —
the two water bodies exchanging heat only with each other through the wall,
with no heat transferred to the environment and the apparatus heat capacity
ignored — the combined thermal energy is conserved, so the
heat-capacity-weighted mean temperature `T_eq` takes one and the same value
at every sampled instant.  This is the physical content that `T_eq` "would be
reached by both IC and OC": it is the constant about which the run relaxes. -/
def ConservedWeightedMean (T_eq : ℝ) : Prop :=
  ∀ j : ι, D.weightedMean j = T_eq

/-- **Constancy bridge.**  Combined-energy conservation (the governing law
`energy_conserved`) forces the heat-capacity-weighted mean temperature —
the combined energy divided by the total heat capacity — to take one and
the same value at every sampled instant: with `j₀` any reference instant,
`weightedMean j = weightedMean j₀` for all `j`.  This is the only step in
the file that uses the conservation law. -/
theorem weightedMean_const (j₀ : ι) :
    D.ConservedWeightedMean (D.weightedMean j₀) := by
  intro j
  unfold weightedMean
  rw [div_eq_div_iff (ne_of_gt D.totalHeatCapacity_pos)
    (ne_of_gt D.totalHeatCapacity_pos)]
  unfold combinedEnergy
  rw [D.energy_conserved j j₀]

/-- **Graphical equilibrium from the C.3 figure (answer-free).**  On the C.3
common-axes figure both curves `(T_OC, T_OC − T_IC)` and `(T_IC, T_OC −
T_IC)` tend, as the temperature difference `T_OC − T_IC` falls to `0`, to the
single common temperature `T_eq` — the point where the two plotted relations
meet at zero difference.  Combined with energy conservation this crossing is
exactly the conserved weighted-mean temperature, so the value read off the
C.3 graph is `T_eq`.  Phrased as: whenever the recorded difference at some
instant is driven to `0`, both recorded temperatures there equal `T_eq`. -/
def IsGraphicalEquilibrium (T_eq : ℝ) : Prop :=
  ∀ j : ι, D.T_OC j - D.T_IC j = 0 → D.T_IC j = T_eq ∧ D.T_OC j = T_eq

/-- **Answer-free solution predicate for C.4.**  A real number `T_eq` of
temperature role is *the equilibrium temperature determined from the C.3
graphs* iff it is both

* the conserved heat-capacity-weighted mean temperature of the two water
  bodies (the temperature they "would reach with no heat transfer to the
  environment", by internal-exchange energy conservation), and
* the zero-difference crossing of the two C.3 curves (the common value both
  `T_OC` and `T_IC` take as `T_OC − T_IC → 0`).

No recorded value or closed form appears here; the predicate only expresses
the two faithful characterizations of `T_eq`. -/
def IsEquilibriumTemperature (T_eq : ℝ) : Prop :=
  D.ConservedWeightedMean T_eq ∧ D.IsGraphicalEquilibrium T_eq

/-- The graphical-equilibrium value agrees with the conserved weighted mean:
the temperature at which the two C.3 curves meet at zero difference is the
constant weighted-mean temperature.  This is the fact that the value read
off the C.3 graph is physically the equilibrium temperature of the
statement's definition. -/
theorem graphical_eq_of_conserved {T_eq : ℝ} (h : D.ConservedWeightedMean T_eq) :
    D.IsGraphicalEquilibrium T_eq := by
  intro j hdiff
  have hTIC : D.T_OC j = D.T_IC j := sub_eq_zero.mp hdiff
  -- At zero difference, both temperatures equal the common value, and the
  -- conserved weighted mean at instant `j` collapses to that same value.
  have hmean := h j
  have hfold : D.weightedMean j = D.T_IC j := by
    rw [weightedMean_of_eq D j rfl hTIC]
  refine ⟨?_, ?_⟩
  · -- `T_IC j = T_eq`
    calc D.T_IC j = D.weightedMean j := hfold.symm
    _ = T_eq := hmean
  · -- `T_OC j = T_eq`
    calc D.T_OC j = D.T_IC j := hTIC
    _ = T_eq := by
      calc D.T_IC j = D.weightedMean j := hfold.symm
      _ = T_eq := hmean

/-- The equilibrium temperature, if it exists, is unique: any two real
numbers both conserved as the combined weighted mean and both giving the
graphical zero-difference crossing coincide.  (Uses the existence of some
sampled instant and the initial imbalance `start_ordered`.) -/
theorem equilibrium_temperature_unique {T₁ T₂ : ℝ}
    (h₁ : D.IsEquilibriumTemperature T₁) (h₂ : D.IsEquilibriumTemperature T₂) :
    T₁ = T₂ := by
  -- `start_ordered` supplies a sampled instant, so `ι` is inhabited.
  obtain ⟨j, _⟩ := D.start_ordered
  haveI : Nonempty ι := ⟨j⟩
  letI := Classical.decEq ι
  -- Both candidates equal the weighted mean at the inhabited index.
  have hj₁ := h₁.1 j
  have hj₂ := h₂.1 j
  exact hj₁.symm.trans hj₂

/-- **E1-C.4, answer-free characterization.**  *From the graphs constructed
in C3, determine `T_eq` — the equilibrium temperature that would be reached
by both IC and OC if there were no heat transfer to the environment.*

Given the Part-C heat-conduction record — the C.1 sampled times and `T_IC`,
`T_OC` traces, with the masses of the two water bodies and the specific heat
capacity of water, the apparatus heat capacity ignored and the procedure's
initial OC-hotter imbalance — there exists a unique real number `T_eq` that
is simultaneously the conserved combined heat-capacity-weighted mean
temperature (internal-exchange energy conservation, no environmental loss)
and the zero-difference crossing of the two C.3 curves.  The explicit value
of `T_eq` — the heat-capacity-weighted mean of the recorded temperatures —
is deliberately kept out of this statement; the later proof constructs the
witness. -/
theorem equilibrium_temperature_exists_unique [Nonempty ι] :
    ∃! T_eq : ℝ, D.IsEquilibriumTemperature T_eq := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  -- Constancy of the weighted mean follows from the governing conservation
  -- law `energy_conserved` via the bridge `weightedMean_const`; the witness
  -- `weightedMean j₀` is the equilibrium temperature (its graphical half
  -- follows by `graphical_eq_of_conserved`), and uniqueness is immediate
  -- because any candidate's conservation law, evaluated at `j₀`, forces it
  -- to equal `weightedMean j₀`.
  have hcons : D.ConservedWeightedMean (D.weightedMean j₀) :=
    D.weightedMean_const j₀
  exact ⟨D.weightedMean j₀,
    ⟨hcons, D.graphical_eq_of_conserved hcons⟩,
    fun T₂ hT₂ => (hT₂.1 j₀).symm⟩

end HeatConductionData

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4C4
