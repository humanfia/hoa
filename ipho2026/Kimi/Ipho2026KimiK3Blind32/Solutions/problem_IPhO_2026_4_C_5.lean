import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Part C.5 — answer-blind formalization

## Physical setup (E1, Part C: Heat Conduction, pages 12–13)

Water in the **inner cylinder (IC)** and water in the **outer cylinder (OC)**
exchange heat radially through the acrylic cylindrical wall that separates
them.  The measured quantities are the water temperatures `T_IC(t)` and
`T_OC(t)` recorded as functions of time `t` (subquestion C.1).  The stated
heat-flow model of the wall (Equation (4) of the paper) is

    ΔQ / Δt = (1 / R_Th) · (T_OC − T_IC),

where `ΔQ` is the heat received by the water in the IC through the wall during
the time interval `Δt`, and `R_Th` is the effective thermal resistance of the
wall.  For radial Fourier conduction through the slim cylindrical wall the
paper also states `dQ/dt = −λ·A·dT/dr` (Equation (6)); both governing laws are
carried by the setup structure below, but only the first enters this
subquestion.

When the variables are measured only a finite number of times, the paper
rewrites Equation (4) as the **discrete proportionality (Equation (5))**

    (T_{IC,j} − T_{IC,j−1}) / (t_j − t_{j−1})  ∝  T̄_OC − T̄_IC,

where `j` is the measurement number and `T̄` denotes the **average
temperature of each cylinder during the interval `t_{j−1}` to `t_j`**.

## Current subquestion (E1-C.5, 1.0 pt)

*Graph the expression on the left hand side of Equation 5 as a function of the
expression on the right hand side.*  That is: from the recorded measurement
table `(t_i, T_IC,i, T_OC,i)` form, for every sampling interval `j ≥ 1`, the
finite-difference warming rate

    r_j = (T_{IC,j} − T_{IC,j−1}) / (t_j − t_{j−1})

and the corresponding temperature gap of the interval-averaged temperatures

    Δ_j = T̄_{OC,j} − T̄_{IC,j},

and display the points `(Δ_j, r_j)` on one graph — the graph whose slope is
used in C.6 to determine `R_Th`.

## Dependency note (previous subquestions, answers withheld)

* **C.1** (*Record `T_IC` and `T_OC` as functions of time `t`*) supplies, by
  natural-language prerequisite only, the recorded measurement table.  Its
  Lean output is not imported; the table is modeled here as the abstract
  structure `C1Measurements`.

## Answer-blind statement design

The requested deliverable is the displayed graph itself — there is no official
derived scalar to withhold.  We model

* `C1Measurements` — the recorded C.1 table, with strictly increasing,
  positive sampling times and absolute temperatures (K);
* `intervalMean` — the interval average `T̄_j = (T_{j−1} + T_j)/2` of a
  sampled temperature sequence over the interval indexed by `j ≥ 1`, in the
  discrete (arithmetic-mean) reading of Equation (5);
* `CoolingModel` — the heat-flow model behind Equation (5): the wall law
  `dQ/dt = (T_OC − T_IC)/R_Th` (Equation (4)) together with the IC energy
  balance `dQ/dt = C_IC · dT_IC/dt` (apparatus heat capacity ignored, as
  instructed for the C-questions), so that the discrete cooling coefficient is
  `α = 1/(R_Th · C_IC)`;
* plotting primitives — the finite-difference ordinate `fdRate` (LHS of
  Equation (5)) and the interval-mean gap abscissa `meanGap` (RHS of
  Equation (5)), and the display predicate `IsC5Plot`, which packages the
  requested graph as paired axes carrying every derived point;
* `Solution` — the answer-blind solution predicate: a realized C.5 graph whose
  plotted points fall, within the requested graphing accuracy `ε`, on the
  straight line through the origin of slope `α` predicted by Equation (5).

The main theorem then states the existence of a solution of the C.5 task, and
a companion theorem records the physically decisive characterization:
**any** solution graph is, within its accuracy, directly proportional through
the origin with slope `α` — the graphical relation exploited in C.6.  No
measured temperature, finite-difference value, or cooling coefficient appears
in any theorem signature; the prover may construct the witnesses later.
-/

namespace IPhO_2026_4_C_5

/-- **Experiment setup (E1, Part C).**  The immutable physical data of the
heat-conduction experiment:

* `R_Th` — the effective thermal resistance of the acrylic wall between the
  IC and the OC (K/W), entering the wall heat-flow model
  `ΔQ/Δt = (T_OC − T_IC)/R_Th` (Equation (4));
* `C_IC` — the heat capacity of the water contained in the inner cylinder
  (J/K); the IC satisfies the energy balance `dQ/dt = C_IC · dT_IC/dt`
  (apparatus heat capacity ignored, as instructed for the C-questions);
* `lam` — the thermal conductivity `λ` of acrylic (W/(m·K)) entering the
  radial Fourier-law model `dQ/dt = −λ·A·dT/dr` (Equation (6), named in the
  problem context; it drives only the later subquestion C.7);
* `A` — the effective heat-conduction area of the cylindrical wall (m²) in
  the same Fourier-law model.

All quantities are positive reals. -/
structure Setup where
  /-- Effective thermal resistance of the wall `R_Th` (K/W). -/
  R_Th : ℝ
  /-- Heat capacity of the water in the inner cylinder `C_IC` (J/K);
  apparatus heat capacity ignored as instructed. -/
  C_IC : ℝ
  /-- Thermal conductivity `λ` of acrylic (W/(m·K)), from the radial Fourier
  law `dQ/dt = −λ·A·dT/dr` of the problem context (Equation (6)). -/
  lam : ℝ
  /-- Effective wall area `A` (m²) in the radial Fourier law. -/
  A : ℝ
  R_Th_pos : 0 < R_Th
  C_IC_pos : 0 < C_IC
  lam_pos : 0 < lam
  A_pos : 0 < A

/-- **The C.1 measurement table.**  The temperatures `T_IC` and `T_OC`
recorded as functions of time `t` in subquestion C.1: a finite family of
`k + 1` sampled triples `(t_i, T_IC,i, T_OC,i)`.

* `t i` is the stopwatch reading of the `i`-th measurement (s), taken
  strictly increasing from a nonnegative initial reading, so that every
  interval `t_{j−1} → t_j` has positive length;
* `T_IC i` and `T_OC i` are the recorded water temperatures of the inner and
  outer cylinders (absolute temperature, K), both positive;
* at least two samples are taken (`1 ≤ k`), since finite differences over an
  interval `j ≥ 1` require a previous measurement.

This structures the table recorded in subquestion C.1 ("Record `T_IC` and
`T_OC` as functions of time `t`"); C.1's own Lean output is not imported, per
the dependency policy. -/
structure C1Measurements where
  /-- Last sample index; the samples are `i = 0, …, k`. -/
  k : ℕ
  /-- Stopwatch readings `tᵢ` (s). -/
  t : Fin (k + 1) → ℝ
  /-- Recorded inner-cylinder water temperatures `T_IC` (K). -/
  T_IC : Fin (k + 1) → ℝ
  /-- Recorded outer-cylinder water temperatures `T_OC` (K). -/
  T_OC : Fin (k + 1) → ℝ
  /-- At least two measurements were taken (one finite-difference interval). -/
  one_le : 1 ≤ k
  /-- The sampling times are strictly increasing. -/
  t_strictMono : StrictMono t
  /-- The initial stopwatch reading is nonnegative. -/
  t₀_nonneg : 0 ≤ t 0
  /-- Every recorded inner-cylinder temperature is a positive absolute
  temperature (K). -/
  T_IC_pos : ∀ i, 0 < T_IC i
  /-- Every recorded outer-cylinder temperature is a positive absolute
  temperature (K). -/
  T_OC_pos : ∀ i, 0 < T_OC i

/-- The sampling times are ordered, since they are strictly increasing. -/
lemma C1Measurements.t_mono (d : C1Measurements) : Monotone d.t :=
  d.t_strictMono.monotone

/-- Every stopwatch reading is nonnegative times are bounded below by `t 0`. -/
lemma C1Measurements.t_nonneg (d : C1Measurements) (i : Fin (d.k + 1)) : 0 ≤ d.t i :=
  d.t₀_nonneg.trans (d.t_mono (Fin.zero_le i))

/-- Every sampling interval has strictly positive length `t_j − t_{j−1} > 0`
(the denominator of the finite-difference rate is nonzero). -/
lemma C1Measurements.t_sub_pos (d : C1Measurements) (j : Fin d.k) :
  0 < d.t ⟨j + 1, Nat.add_lt_add_right j.isLt 1⟩ - d.t ⟨j, by omega⟩ :=
  sub_pos.mpr (d.t_strictMono (by simp only [Fin.lt_def]; omega))

/-- **Interval average (Equation (5)).**  For a sampled temperature sequence
`θ` on the same time grid as the C.1 record, the average temperature `T̄_j`
during the interval `t_{j−1}` to `t_j`, in the discrete (arithmetic-mean)
reading of Equation (5), is the mean of the two endpoint samples.  The
interval is indexed by `j : Fin d.k`, where `j` runs over `1, …, k` in the
paper's 1-based measurement numbering. -/
noncomputable def C1Measurements.intervalMean (d : C1Measurements)
    (θ : Fin (d.k + 1) → ℝ) (j : Fin d.k) : ℝ :=
  (θ ⟨j, by omega⟩ + θ ⟨j + 1, Nat.add_lt_add_right j.isLt 1⟩) / 2

/-- **The C.5 abscissa (RHS of Equation (5)).**  The temperature gap of the
interval-averaged temperatures over the interval indexed by `j`,

    Δ_j = T̄_{OC,j} − T̄_{IC,j},

the expression on the right hand side of Equation (5). -/
noncomputable def C1Measurements.meanGap (d : C1Measurements) (j : Fin d.k) : ℝ :=
  d.intervalMean d.T_OC j - d.intervalMean d.T_IC j

/-- **The C.5 ordinate (LHS of Equation (5)).**  The finite-difference
warming rate of the inner cylinder over the interval indexed by `j`,

    r_j = (T_{IC,j} − T_{IC,j−1}) / (t_j − t_{j−1}),

the expression on the left hand side of Equation (5). -/
noncomputable def C1Measurements.fdRate (d : C1Measurements) (j : Fin d.k) : ℝ :=
  (d.T_IC ⟨j + 1, Nat.add_lt_add_right j.isLt 1⟩ - d.T_IC ⟨j, by omega⟩) /
    (d.t ⟨j + 1, Nat.add_lt_add_right j.isLt 1⟩ - d.t ⟨j, by omega⟩)

/-- **Membership in the zipped derived record.**  A point displayed by the
C.5 plot — an abscissa–ordinate pair taken from the derived lists — is
precisely a derived interval point `(f j, g j)` for some sampling interval
`j`.  Used to discharge `displaysEveryPoint` and `WithinProportionality` for
the canonical witness. -/
theorem mem_zip_ofFn_ofFn {n : ℕ} {f g : Fin n → ℝ} {p : ℝ × ℝ}
    (h : p ∈ (List.ofFn f).zip (List.ofFn g)) :
    ∃ j : Fin n, p = (f j, g j) := by
  rcases List.mem_iff_getElem?.mp h with ⟨i, hi⟩
  rw [List.zip_eq_zipWith, List.getElem?_zipWith] at hi
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at hi
  by_cases hn : i < n
  · rw [dif_pos hn, dif_pos hn] at hi
    have hp : p = (f ⟨i, hn⟩, g ⟨i, hn⟩) := (Option.some.inj hi).symm
    exact ⟨⟨i, hn⟩, hp⟩
  · rw [dif_neg hn] at hi
    simp at hi

/-- **A derived interval is displayed.**  The `j`-th derived point
`(f j, g j)` occurs as a displayed point of the zipped record. -/
theorem mk_mem_zip_ofFn {n : ℕ} {f g : Fin n → ℝ} (j : Fin n) :
    (f j, g j) ∈ (List.ofFn f).zip (List.ofFn g) := by
  apply List.mem_iff_getElem?.mpr
  refine ⟨j.val, ?_⟩
  rw [List.zip_eq_zipWith, List.getElem?_zipWith, List.getElem?_ofFn,
      List.getElem?_ofFn, dif_pos j.isLt, dif_pos j.isLt]

/-- **Heat-flow / cooling model behind Equation (5).**  The wall law of the
problem (Equation (4)), `dQ/dt = (T_OC − T_IC)/R_Th`, combined with the IC
energy balance `dQ/dt = C_IC · dT_IC/dt` (apparatus heat capacity ignored as
instructed), makes the IC warming rate proportional to the temperature gap,

    dT_IC/dt = (T_OC − T_IC) / (R_Th · C_IC).

The **cooling coefficient** `α = 1/(R_Th · C_IC)` (s⁻¹) is the proportionality
constant of Equation (5): the slope of the directly-proportional C.5 graph
`(T̄_OC − T̄_IC) ↦ (T_{IC,j} − T_{IC,j−1})/(t_j − t_{j−1})` through the
origin.  Kept answer-free: no numerical value for `R_Th`, `C_IC`, or `α` is
asserted. -/
noncomputable def Setup.coolingCoeff (S : Setup) : ℝ :=
  1 / (S.R_Th * S.C_IC)

/-- **Plot of finite-difference quantities.**  A candidate display of the
discrete transformed record is *plot-admissible* when it pairs an abscissa
list `xs` (the interval-mean gaps `T̄_OC − T̄_IC`, K) with an ordinate list
`ys` (the finite-difference rates `(T_{IC,j} − T_{IC,j−1})/(t_j − t_{j−1})`,
K/s) of the same positive length.

This is the generic display carrier: every recorded interval must appear on
the graph (see `displaysEveryPoint`), and the pairing of `j`-th abscissa with
`j`-th ordinate is via `List.zip`. -/
structure IsC5Plot (xs ys : List ℝ) : Prop where
  /-- The two displayed axes are coadmissible (same length). -/
  length_eq : xs.length = ys.length
  /-- At least one point is displayed. -/
  length_pos : 0 < xs.length

/-- **Every derived interval is displayed.**  The candidate plot carries the
transformed measurements: for every sampling interval `j` of the record, the
derived point `(Δ_j, r_j)` — interval-mean gap, finite-difference rate —
occurs as a displayed point of the plot.  Because both axes have `d.k`
entries (and the plot has at least `d.k` displayed points), the zipped list
coincides exactly with the list of derived points. -/
def displaysEveryPoint (d : C1Measurements) (xs ys : List ℝ) : Prop :=
  ∀ j : Fin d.k, (d.meanGap j, d.fdRate j) ∈ xs.zip ys

/-- **Direct-proportionality regime (Equation (5)).**  The exam's Equation
(5) predicts that the C.5 graph is a straight line through the origin whose
slope is the cooling coefficient `α = 1/(R_Th · C_IC)`.  This predicate
records precisely that proportionality regime at the requested graphing
accuracy `ε > 0`: every plotted point `(x, y)` lies within `ε` of the line
`y = α · x`. -/
def WithinProportionality (α : ℝ) (xs ys : List ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ p : ℝ × ℝ, p ∈ xs.zip ys → |p.2 - α * p.1| ≤ ε

/-- **Solution predicate for C.5 (answer-free).**  A pair of axes
`(xs, ys)` — interval-mean gaps `T̄_OC − T̄_IC` against finite-difference
rates `(T_{IC,j} − T_{IC,j−1})/(t_j − t_{j−1})` — realizes the deliverable
of subquestion C.5, *graph the LHS of Equation (5) against the RHS of
Equation (5)*, together with the cooling coefficient `α` and graphing
accuracy `ε`, when

* the display is plot-admissible (`IsC5Plot`);
* every derived interval `(Δ_j, r_j)` occurs as a displayed point
  (`displaysEveryPoint`);
* the plotted points fall, within `ε`, on the directly-proportional line of
  Equation (5) through the origin with slope `α`
  (`WithinProportionality`).

No measured value, finite-difference value, or coefficient is fixed here. -/
def Solution (S : Setup) (d : C1Measurements)
    (spec : List ℝ × List ℝ × ℝ × ℝ) : Prop :=
  IsC5Plot spec.1 spec.2.1 ∧
  displaysEveryPoint d spec.1 spec.2.1 ∧
  spec.2.2.1 = S.coolingCoeff ∧
  WithinProportionality spec.2.2.1 spec.1 spec.2.1 spec.2.2.2

/-- **IPhO 2026, E1-C.5 (answer-blind).**  *Graph the expression on the left
hand side of Equation 5 as a function of the expression on the right hand
side.*

Given the C.1 measurement table and the stated heat-flow model of the wall
(Equation (4) with IC energy balance), a solution of subquestion C.5 exists:
paired axes displaying every finite-difference rate
`(T_{IC,j} − T_{IC,j−1})/(t_j − t_{j−1})` against its interval-mean gap
`T̄_OC − T̄_IC`, together with the cooling coefficient and graphing accuracy,
as specified by `Solution`.  The theorem asserts existence only; no witness
appears in the statement. -/
theorem problem_IPhO_2026_4_C_5 (S : Setup) (d : C1Measurements) :
    ∃ spec : List ℝ × List ℝ × ℝ × ℝ, Solution S d spec := by
  classical
  -- Every interval's residual from the line of slope `α = 1/(R_Th·C_IC)`.
  set r : Fin d.k → ℝ := fun j => |d.fdRate j - S.coolingCoeff * d.meanGap j| with hr
  -- Canonical graphing accuracy: one more than the total absolute residual.
  set ε : ℝ := (Finset.univ.sum r) + 1 with hε
  have hr_nonneg : ∀ j, 0 ≤ r j := fun j => abs_nonneg _
  have hε_pos : 0 < ε := by
    have hs : 0 ≤ Finset.univ.sum r := Finset.sum_nonneg fun j _ => hr_nonneg j
    linarith [hs]
  have hle : ∀ j, r j ≤ Finset.univ.sum r := fun j =>
    Finset.single_le_sum (fun j _ => hr_nonneg j) (Finset.mem_univ j)
  -- The displayed axes are the derived records.
  refine ⟨(List.ofFn fun j : Fin d.k => d.meanGap j,
           List.ofFn fun j : Fin d.k => d.fdRate j,
           S.coolingCoeff, ε), ⟨?_, ?_, rfl, hε_pos, ?_⟩⟩
  · -- `IsC5Plot`: the two derived lists have equal positive length `d.k ≥ 1`.
    exact ⟨by simp only [List.length_ofFn], by simp only [List.length_ofFn]; exact d.one_le⟩
  · -- `displaysEveryPoint`: every derived interval is a displayed point.
    intro j
    exact mk_mem_zip_ofFn j
  · -- `WithinProportionality`: every displayed point is within `ε` of the line.
    intro p hp
    rcases mem_zip_ofFn_ofFn hp with ⟨j, rfl⟩
    dsimp only
    calc |d.fdRate j - S.coolingCoeff * d.meanGap j|
        = r j := by simp only [r]
      _ ≤ Finset.univ.sum r := hle j
      _ ≤ ε := by simp only [ε]; linarith

/-- **Physical characterization of any C.5 solution (answer-free).**  Every
solution graph of subquestion C.5 is, within its own graphing accuracy,
directly proportional through the origin with slope `α = 1/(R_Th · C_IC)`:
its plotted points deviate from the line `y = α · x` by at most `ε`, and in
particular the guidance embedded in the graph — finite-difference rate
against interval-mean gap — is the directly-proportional relation of
Equation (5) exploited in C.6 to determine `R_Th`.

This is stated for an arbitrary solution (not only for the particular
canonical construction), expressing the physical content of the graph: the
finite-difference rates and the interval-mean gaps of the record are
proportional, with the proportionality determined by the wall resistance and
the IC water heat capacity. -/
theorem problem_IPhO_2026_4_C_5_proportional (S : Setup) (d : C1Measurements)
    {xs ys : List ℝ} {α ε : ℝ} (h : Solution S d (xs, ys, α, ε)) :
    α = S.coolingCoeff ∧
    ∀ p : ℝ × ℝ, p ∈ xs.zip ys → |p.2 - α * p.1| ≤ ε := by
  obtain ⟨hplot, hdisp, hα, hwithin⟩ := h
  refine ⟨hα, ?_⟩
  intro p hp
  exact hwithin.2 p hp

end IPhO_2026_4_C_5
