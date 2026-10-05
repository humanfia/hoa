import Mathlib

/-!
# IPhO 2026, Problem 3, Part C.5 — answer-blind formalization

Context (problem T3, part C, as printed on the official page `T3_page-4.png`):
a paramagnetic torus executes the Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1`
shown in Figure 3b in the `H`-versus-`T` plane.  `T_h` and `T_c` are the hot-
and cold-reservoir temperatures; `Q_h` is the magnitude of heat delivered to
the hot reservoir and `Q_c` the magnitude absorbed from the cold reservoir.
The equation of state of the paramagnet is `T · M · V = n · K · H` and the
isothermal heat relation from part B may be reused.

Subquestion T3-C5 (statement verified against the page image): *"The
efficiency of a refrigerator is quantified by its coefficient of performance
`COP = Q_c/W`.  Determine the overall `COP` of the refrigerator of question
T3-C4 with all the cycles performed until time `t`.  Write your answer in
terms of `T₀` and `T_h` and `T`."*

Subquestion T3-C4 (natural-language prerequisite, statement on the same page):
a body of *constant heat capacity* `C_c` is cooled by continuously performed
Carnot cycles such that the power `P` transferred to the refrigerator remains
constant; the hot-reservoir temperature `T_h` remains constant; in each
operating cycle the temperature `T_c` of the cooled body decreases by `dT_c`,
the heats satisfying `dQ_c / dQ_h = T_c / T_h`; at `t = 0` the body is at
`T_c = T₀`; determine the operating time needed to reach `T < T₀`.

The official answer is withheld deliberately.  The theorem below asserts that
the governing laws determine a unique overall coefficient of performance —
the ratio of the total heat `Q_c` extracted from the body to the total work
`W = P · t` supplied over all cycles until time `t` — without placing any
closed-form value in the signature.
-/

namespace IPhO_2026_3_C_5

/-- The constant physical parameters of the T3-C4/T3-C5 refrigeration
process: the constant heat capacity `C_c` of the cooled body (joule per
kelvin), the constant input power `P` transferred to the refrigerator
(watt), and the constant hot-reservoir (absolute) temperature `T_h`
(kelvin).  All are physically positive. -/
structure RefrigerationParameters where
  /-- Constant heat capacity `C_c` of the cooled body (joule/kelvin). -/
  Cc : ℝ
  /-- Constant refrigerator input power `P` (watt). -/
  P : ℝ
  /-- Constant hot-reservoir absolute temperature `T_h` (kelvin). -/
  Th : ℝ
  Cc_pos : 0 < Cc
  P_pos : 0 < P
  Th_pos : 0 < Th

/-- An infinitesimal operating cycle of the Carnot refrigerator at time `τ`:
`dTc` is the temperature decrease of the cooled body in the cycle, `dQc` the
magnitude of heat absorbed from the cold body and `dQh` the magnitude of heat
delivered to the hot reservoir in that cycle, while the refrigerator receives
work `P · dt` during the duration `dt` of the cycle.

The fields encode, *verbatim*, the relations of the T3-C4 statement:

* `carnot_relation`: the per-cycle relation `dQ_c / dQ_h = T_c / T_h`;
* `first_law`: energy conservation for the cyclic working substance at
  constant input power, `dQ_h = dQ_c + P · dt`;
* `temperature_drop`: each operating cycle lowers the body temperature,
  `dT_c = T_c(τ + dt) − T_c(τ) ≤ 0`;
* `heat_capacity`: the constant-heat-capacity budget of the cooled body,
  `dQ_c = −C_c · dT_c`. -/
structure InfinitesimalCycle (p : RefrigerationParameters)
    (Tc : ℝ → ℝ) (τ dt dQc dQh dTc : ℝ) : Prop where
  /-- T3-C4 verbatim: in each operating cycle the heats satisfy
  `dQ_c / dQ_h = T_c / T_h`, evaluated at the instantaneous body temperature. -/
  carnot_relation : dQh ≠ 0 → dQc / dQh = Tc τ / p.Th
  /-- Energy conservation for the refrigerator during one cycle at constant
  input power `P`: the heat rejected to the hot reservoir equals the heat
  extracted from the cold body plus the work `P · dt` supplied. -/
  first_law : dQh = dQc + p.P * dt
  /-- The temperature of the cooled body decreases by `dT_c` in the cycle. -/
  temperature_drop : dTc = Tc (τ + dt) - Tc τ ∧ dTc ≤ 0
  /-- Constant heat capacity of the cooled body: the heat extracted in the
  cycle equals `C_c` times the temperature decrease, `dQ_c = −C_c · dT_c`. -/
  heat_capacity : dQc = -(p.Cc * dTc)

/-- A realization of the T3-C4 refrigeration process as used in T3-C5: a
cold-body absolute-temperature trajectory `Tc`, the initial temperature `T₀`,
the operating time `t` by which the body has been cooled to the target
temperature `T < T₀`, and the accumulated heats `Q_c` / `Q_h` extracted from
the cold body / delivered to the hot reservoir over all cycles until `t`.
The physical ordering and scale hypotheses of the question (absolute
temperatures, a genuinely colder target, a cold side strictly below the hot
reservoir, a positive operating time, and the physical one-sided range of the
cold-body temperature along the whole trajectory) are recorded as proof
fields.  The range and continuity fields close the iter-008
`underdetermined_contract` gap: they pin `T_c` into the physical interval
`[T, T₀]` throughout the operating window and keep the trajectory continuous
on `[0, t]`, so `t` is determined by the governing laws rather than free. -/
structure CoolingProcess (p : RefrigerationParameters) where
  /-- Cold-body absolute temperature `T_c` as a function of time (kelvin). -/
  Tc : ℝ → ℝ
  /-- Initial cold-body absolute temperature `T₀` (kelvin). -/
  T0 : ℝ
  /-- Operating time by which the body reaches the target temperature (s). -/
  t : ℝ
  /-- Target cold-body absolute temperature `T` at time `t` (kelvin). -/
  Ttarget : ℝ
  /-- Total magnitude of heat extracted from the cold body over all cycles
  until time `t` (joule). -/
  Qc : ℝ
  /-- Total magnitude of heat delivered to the hot reservoir over all cycles
  until time `t` (joule). -/
  Qh : ℝ
  T0_pos : 0 < T0
  /-- The target lies strictly below the initial temperature, `T < T₀`. -/
  Ttarget_lt_T0 : Ttarget < T0
  /-- The cold side is initially colder than the hot reservoir, `T₀ < T_h`. -/
  T0_lt_Th : T0 < p.Th
  t_pos : 0 < t
  /-- The target temperature is a physical absolute temperature, `0 < T`
  (kelvin scale).  Strict positivity keeps the cold side away from absolute
  zero, where the temperature primitive `log` would be singular. -/
  Ttarget_pos : 0 < Ttarget
  /-- The body starts at the initial temperature, `T_c(0) = T₀`. -/
  Tc_at_zero : Tc 0 = T0
  /-- The body reaches the target temperature at time `t`, `T_c(t) = T`. -/
  Tc_at_t : Tc t = Ttarget
  /-- The cold side is a genuine cold reservoir along the whole operating
  window: the body temperature stays at or below its initial value `T₀` and
  at or above the final target `T`, `T ≤ T_c(τ) ≤ T₀` for `τ ∈ [0, t]`. -/
  Tc_range : ∀ τ ∈ Set.Icc 0 t, Ttarget ≤ Tc τ ∧ Tc τ ≤ T0
  /-- The temperature trajectory is continuous on the closed operating
  interval (in particular one-sided continuous at the endpoints), so a
  change-of-variables over `[0, t]` is legitimate. -/
  Tc_continuous : ContinuousOn Tc (Set.Icc 0 t)

/-- **Governing laws** of the T3-C4/T3-C5 refrigeration process — the full
physical content distinguishing this refrigerator from an arbitrary cooling
process:

1.  *Per-cycle laws:* at every operating instant `τ ∈ (0, t)` there exist
    infinitesimal-cycle data obeying verbatim the T3-C4 relations
    `dQ_c/dQ_h = T_c/T_h` (Carnot), `dQ_h = dQ_c + P·dt` (first law),
    `dT_c = T_c(τ+dt) − T_c(τ) ≤ 0` (cooling), `dQ_c = −C_c·dT_c` (constant
    heat capacity) — see `InfinitesimalCycle`.
2.  *Continuous cooling:* `T_c` is differentiable on the operating interval
    and its instantaneous rate of change is nonpositive.
3.  *Extraction-rate law:* combining `dQ_c/dQ_h = T_c/T_h` with
    `dQ_h = dQ_c + P·dt` gives `dQ_c = P·T_c/(T_h − T_c)·dt`, and the
    heat-capacity budget `dQ_c = −C_c·dT_c` then yields the governing
    evolution `C_c·T_c'(τ) = P·T_c(τ)/(T_c(τ) − T_h)` (encoded with the
    derivative written from the statement).
4.  *Heat-capacity budget (integrated):* the total heat extracted from the
    constant-heat-capacity body cooled from `T₀` to `T` is
    `Q_c = C_c·(T₀ − T)`.
5.  *Global first law:* the total heat rejected to the hot reservoir equals
    the extracted heat plus the total work `W = P·t`:
    `Q_h = Q_c + P·t`. -/
structure GoverningLaws (p : RefrigerationParameters)
    (proc : CoolingProcess p) : Prop where
  /-- At each instant of the operating interval there is an infinitesimal
  cycle governed verbatim by the relations of T3-C4 (Carnot heat relation,
  per-cycle first law at constant power, temperature drop, constant heat
  capacity).  The cycle duration is required positive (`dt > 0`): a
  zero-duration zero-heat tuple would satisfy the relations vacuously and
 says nothing about the process, so a genuine non-vanishing cycle is
  demanded. -/
  per_cycle_laws : ∀ τ ∈ Set.Ioo 0 proc.t,
      ∃ dt dQc dQh dTc : ℝ, 0 < dt ∧
        InfinitesimalCycle p proc.Tc τ dt dQc dQh dTc
  /-- The temperature trajectory is differentiable on the operating
  interval, so the cooling rate below is defined. -/
  Tc_differentiable : ∀ τ ∈ Set.Ioo 0 proc.t, DifferentiableAt ℝ proc.Tc τ
  /-- The body is being cooled: the instantaneous rate is nonpositive. -/
  cooling_rate_nonpos : ∀ τ ∈ Set.Ioo 0 proc.t, deriv proc.Tc τ ≤ 0
  /-- The extraction-rate law: the heat removed from the body per unit time,
  `−C_c·T_c'(τ)`, equals the Carnot refrigeration power
  `P·T_c(τ)/(T_h − T_c(τ))` at the constant input power `P`.  Written
  `C_c·T_c'(τ) = P·T_c(τ)/(T_c(τ) − T_h)` to match the stated derivative. -/
  extraction_rate : ∀ τ ∈ Set.Ioo 0 proc.t,
      p.Cc * deriv proc.Tc τ = p.P * proc.Tc τ / (proc.Tc τ - p.Th)
  /-- Constant heat capacity of the cooled body, integrated over the whole
  process: the total extracted heat is `Q_c = C_c·(T₀ − T)`. -/
  heat_budget : proc.Qc = p.Cc * (proc.T0 - proc.Ttarget)
  /-- Global first law over `[0, t]`: the total heat delivered to the hot
  reservoir equals the extracted heat plus the total work `P · t` supplied
  at the constant input power. -/
  first_law : proc.Qh = proc.Qc + p.P * proc.t

/-- **Solution predicate (answer-free).**  `cop` is the overall coefficient
of performance of the refrigerator of T3-C4 over all cycles until time `t`:
the ratio `COP = Q_c/W` of the total heat extracted from the cold body to the
total work `W = P·t` supplied at the constant input power, where `Q_c` is the
heat accumulated according to the governing laws (constant heat capacity of
the body, per-cycle Carnot relation, constant input power).  The ratio is
physically nonnegative and sub-Carnot: the per-cycle Carnot COP
`T_c/(T_h − T_c) ≤ T₀/(T_h − T_c)` while the cold side warms toward `T_h`
over the process, so the overall ratio obeys the Carnot bound
`COP ≤ T₀/(T_h − T₀)`; the bound is recorded as part of the solution
concept.  No closed-form value is placed in the predicate; the later proof
constructs the ratio determined by the governing laws and discharges the
bound. -/
def OverallCOP (p : RefrigerationParameters) (proc : CoolingProcess p)
    (cop : ℝ) : Prop :=
  cop = proc.Qc / (p.P * proc.t) ∧
  0 ≤ cop ∧
  cop ≤ proc.T0 / (p.Th - proc.T0)

/-- **Target theorem (answer-free, unique).**  For the stated
configuration — a body of constant heat capacity `C_c` cooled from `T₀` to
`T < T₀` by continuously performed Carnot cycles with constant input power
`P` and constant hot-reservoir temperature `T_h`, governed by the per-cycle
relations `dQ_c/dQ_h = T_c/T_h` and `dQ_c = −C_c·dT_c`, the continuous
cooling law, and the global first law — the overall coefficient of
performance, uniquely characterized as the ratio of the total heat extracted
from the cold body to the total work supplied over all cycles until time `t`,
exists.

The actual value of the COP (in terms of `T₀`, `T_h` and `T`, as the question
requests) is withheld from the signature; the proof constructs the witness
ratio `Q_c/(P·t)` and discharges nonnegativity (constant heat capacity plus
positive `P·t`), the Carnot upper bound (via the exact C4 operating-time
quadrature `P·t = C_c·(T − T₀) + C_c·T_h·ln(T₀/T)` obtained by the FTC from
the extraction-rate law, then the tangent-line bound
`ln(T₀/T) ≥ (T₀ − T)/T₀`), and uniqueness (the predicate fixes `cop` to the
ratio). -/
theorem problem_IPhO_2026_3_C_5
    (p : RefrigerationParameters) (proc : CoolingProcess p)
    (hlaws : GoverningLaws p proc) :
    ∃! cop : ℝ, OverallCOP p proc cop := by
  refine ⟨proc.Qc / (p.P * proc.t), ⟨rfl, ?_, ?_⟩, ?_⟩
  · -- `Q_c = C_c·(T₀ − T) > 0` and `P·t > 0`, so the ratio is nonnegative.
    rw [hlaws.heat_budget]
    have hPt : 0 < p.P * proc.t := mul_pos p.P_pos proc.t_pos
    exact div_nonneg (mul_nonneg (le_of_lt p.Cc_pos)
      (le_of_lt (sub_pos.mpr proc.Ttarget_lt_T0))) (le_of_lt hPt)
  · -- Carnot upper bound: `Q_c/(P·t) ≤ T₀/(T_h − T₀)`.
    rw [hlaws.heat_budget, div_le_div_iff₀ (mul_pos p.P_pos proc.t_pos)
      (sub_pos.mpr proc.T0_lt_Th)]
    -- The remaining inequality `C_c·(T₀−T)·(T_h−T₀) ≤ T₀·P·t` is the
    -- integrated Carnot bound over the whole process `0 ≤ T ≤ T_c ≤ T₀`,
    -- closed here via the C4 quadrature.  Set up short names and the range
    -- facts of the body temperature supplied by `CoolingProcess.Tc_range`.
    set f : ℝ → ℝ := fun x => p.P * x / (p.Cc * (x - p.Th)) with hf
    have hTt : 0 < proc.Ttarget := proc.Ttarget_pos
    have hTtT0 : proc.Ttarget < proc.T0 := proc.Ttarget_lt_T0
    have hT0h : proc.T0 < p.Th := proc.T0_lt_Th
    -- On the closed window, `T_c` sits in `[T, T₀] ⊂ (0, T_h)`.
    have hrange : ∀ τ ∈ Set.Icc 0 proc.t,
        proc.Ttarget ≤ proc.Tc τ ∧ proc.Tc τ ≤ proc.T0 := proc.Tc_range
    have hpos : ∀ τ ∈ Set.Icc 0 proc.t, 0 < proc.Tc τ := fun τ hτ =>
      lt_of_lt_of_le hTt (hrange τ hτ).1
    have hneTh : ∀ τ ∈ Set.Icc 0 proc.t, proc.Tc τ ≠ p.Th := fun τ hτ =>
      ne_of_lt (lt_of_le_of_lt (hrange τ hτ).2 hT0h)
    -- **Quadrature (C4, natural-language prerequisite).**  The primitive
    -- `F x = (C_c·x − C_c·T_h·log x)/P` of `1/f` over the body temperature,
    -- where `f x = P·x/(C_c·(x − T_h))` is the extraction rate from
    -- `GoverningLaws.extraction_rate`, composes with `T_c` to give
    -- `(F ∘ T_c)' = 1` on the open operating interval; the fundamental
    -- theorem of calculus then yields the exact operating-time identity
    --   `P·t = C_c·(T − T₀) + C_c·T_h·ln(T₀/T)`,
    -- from which the Carnot bound follows by `log y ≤ y − 1` (tangent line)
    -- applied at `y = T/T₀` and sign-flipped to `ln(T₀/T) ≥ (T₀ − T)/T₀`.
    -- The primitive of `1/f` on the positive cold side.
    set F : ℝ → ℝ := fun x => (p.Cc * x - p.Cc * p.Th * Real.log x) / p.P with hFdef
    have hP : (0:ℝ) < p.P := p.P_pos
    have hCc : (0:ℝ) < p.Cc := p.Cc_pos
    -- The derivative of the primitive at every positive cold-side
    -- temperature: `F'(x) = (C_c − C_c·T_h/x)/P`, the reciprocal of `f`.
    have hFderiv : ∀ x : ℝ, 0 < x →
        HasDerivAt F ((p.Cc - p.Cc * p.Th / x) / p.P) x := by
      intro x hx
      have hlog : HasDerivAt (fun x : ℝ => Real.log x) x⁻¹ x :=
        Real.hasDerivAt_log (ne_of_gt hx)
      have h1 : HasDerivAt (fun x : ℝ => p.Cc * x) p.Cc x := by
        simpa using (hasDerivAt_id x).const_mul p.Cc
      have h2 : HasDerivAt (fun x : ℝ => p.Cc * p.Th * Real.log x)
          (p.Cc * p.Th * x⁻¹) x := hlog.const_mul _
      have h3 : HasDerivAt (fun x : ℝ => p.Cc * x - p.Cc * p.Th * Real.log x)
          (p.Cc - p.Cc * p.Th * x⁻¹) x := h1.sub h2
      have h4 : HasDerivAt (fun x : ℝ => (p.Cc * x - p.Cc * p.Th * Real.log x) / p.P)
          ((p.Cc - p.Cc * p.Th * x⁻¹) / p.P) x := h3.div_const p.P
      have hdrv : (p.Cc - p.Cc * p.Th / x) / p.P = (p.Cc - p.Cc * p.Th * x⁻¹) / p.P := by
        rw [div_eq_mul_inv (p.Cc * p.Th) x]
      rwa [hFdef, hdrv]
    -- `F` is continuous on the positive cold side (it is differentiable
    -- there), so `F ∘ T_c` is continuous on the closed operating window.
    have hFcont : ContinuousOn F (Set.Ioi 0) := fun x hx =>
      (hFderiv x hx).continuousAt.continuousWithinAt
    have hcont : ContinuousOn (fun τ => F (proc.Tc τ)) (Set.Icc 0 proc.t) :=
      hFcont.comp proc.Tc_continuous fun τ hτ => hpos τ hτ
    -- The extraction-rate law: `C_c·T_c'(τ) = P·T_c(τ)/(T_c(τ) − T_h)`,
    -- rewritten into the derivative of `T_c` via `deriv` on the interior.
    have hderiv_law : ∀ τ ∈ Set.Ioo 0 proc.t,
        deriv proc.Tc τ = f (proc.Tc τ) := by
      intro τ hτ
      have h := hlaws.extraction_rate τ hτ
      have hτr := Set.mem_Icc_of_Ioo hτ
      have hne : proc.Tc τ - p.Th ≠ 0 := sub_ne_zero.mpr (hneTh τ hτr)
      have hCc' : p.Cc ≠ 0 := p.Cc_pos.ne'
      have hgoal : f (proc.Tc τ) = p.P * proc.Tc τ / (p.Cc * (proc.Tc τ - p.Th)) := rfl
      rw [hgoal]
      field_simp [hne, hCc'] at h ⊢
      linarith
    -- `(F ∘ T_c)' τ = 1` pointwise on the open operating interval: the
    -- chain rule for the explicit primitive against the cooling law.
    have hGF_ : ∀ τ ∈ Set.Ioo 0 proc.t,
        HasDerivAt (fun τ => F (proc.Tc τ)) 1 τ := by
      intro τ hτ
      have hτr := Set.mem_Icc_of_Ioo hτ
      have hTc_pos : 0 < proc.Tc τ := hpos τ hτr
      have hTc_ne : proc.Tc τ ≠ p.Th := hneTh τ hτr
      -- Chain rule against the cooling law `T_c' = f(T_c)`.
      have hTcderiv : HasDerivAt proc.Tc (f (proc.Tc τ)) τ :=
        (hlaws.Tc_differentiable τ hτ).hasDerivAt.congr_deriv (hderiv_law τ hτ)
      have hcomp := (hFderiv (proc.Tc τ) hTc_pos).comp τ hTcderiv
      -- The composite derivative `F'(T_c)·f(T_c) = 1`: the primitive was
      -- chosen as `1/f`, and `T_c < T_h` makes the denominator nonzero.
      have hderiv_eq : (p.Cc - p.Cc * p.Th / proc.Tc τ) / p.P * f (proc.Tc τ) = 1 := by
        have hne2 : proc.Tc τ - p.Th ≠ 0 := sub_ne_zero.mpr hTc_ne
        have hTcne : proc.Tc τ ≠ 0 := ne_of_gt hTc_pos
        rw [hf]
        field_simp [hne2, hTcne, p.Cc_pos.ne', p.P_pos.ne']
      rw [hderiv_eq] at hcomp
      exact hcomp
    -- Fundamental theorem of calculus on `[0, t]`: the accumulated
    -- derivative `1` integrates to `F(T_c(t)) − F(T_c(0))`.
    have hint : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 0 proc.t :=
      intervalIntegrable_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (le_of_lt proc.t_pos) hcont (fun τ hτ => hGF_ τ hτ) hint
    rw [intervalIntegral.integral_const] at hFTC
    -- Substitute the boundary values `T_c(t) = T`, `T_c(0) = T₀` and
    -- evaluate the primitive: the C4 operating-time identity.
    rw [proc.Tc_at_t, proc.Tc_at_zero] at hFTC
    have hquad : p.P * proc.t =
        p.Cc * (proc.Ttarget - proc.T0) +
          p.Cc * p.Th * Real.log (proc.T0 / proc.Ttarget) := by
      rw [hFdef] at hFTC
      field_simp [p.P_pos.ne', ne_of_gt hTt, ne_of_gt proc.T0_pos,
        sub_ne_zero.mpr (ne_of_gt (lt_trans hTtT0 hT0h)),
        sub_ne_zero.mpr (ne_of_gt hT0h)] at hFTC ⊢
      simp only [smul_eq_mul, sub_zero, mul_one] at hFTC
      have hlogsplit : Real.log (proc.T0 / proc.Ttarget) =
          Real.log proc.T0 - Real.log proc.Ttarget :=
        Real.log_div (ne_of_gt proc.T0_pos) (ne_of_gt hTt)
      rw [hlogsplit]
      linarith [hFTC]
    -- The Carnot bound: `P·t ≥ C_c·(T₀−T)·(T_h−T₀)/T₀`, i.e.
    -- `C_c·(T₀−T)·(T_h−T₀) ≤ T₀·P·t`, since
    -- `log(T₀/T) ≥ (T₀−T)/T₀` (the tangent-line inequality
    -- `log y ≤ y − 1` applied at `T/T₀` and sign-flipped).
    have hy : (0:ℝ) < proc.T0 / proc.Ttarget := div_pos proc.T0_pos hTt
    have hden : (0:ℝ) < p.Th - proc.T0 := sub_pos.mpr hT0h
    have hgoal : p.Cc * (proc.T0 - proc.Ttarget) * (p.Th - proc.T0)
        ≤ proc.T0 * (p.P * proc.t) := by
      rw [hquad]
      have haux : (proc.T0 - proc.Ttarget) / proc.T0 ≤ Real.log (proc.T0 / proc.Ttarget) := by
        have hle := Real.log_le_sub_one_of_pos (div_pos hTt proc.T0_pos)
        have hlogsplit : Real.log (proc.T0 / proc.Ttarget) =
            - Real.log (proc.Ttarget / proc.T0) := by
          rw [← Real.log_inv]; congr 1; field_simp [ne_of_gt hTt, ne_of_gt proc.T0_pos]
        rw [hlogsplit]
        have hz : (proc.T0 - proc.Ttarget) / proc.T0 = 1 - proc.Ttarget / proc.T0 := by
          field_simp [ne_of_gt proc.T0_pos]
        rw [hz]; linarith [hle]
      have haux2 : proc.T0 - proc.Ttarget ≤ proc.T0 * Real.log (proc.T0 / proc.Ttarget) := by
        have h := mul_le_mul_of_nonneg_left haux (le_of_lt proc.T0_pos)
        rwa [mul_div_cancel₀ _ (ne_of_gt proc.T0_pos)] at h
      have hprod : p.Cc * p.Th * (proc.T0 - proc.Ttarget) ≤
          p.Cc * p.Th * (proc.T0 * Real.log (proc.T0 / proc.Ttarget)) :=
        mul_le_mul_of_nonneg_left haux2 (le_of_lt (mul_pos hCc p.Th_pos))
      -- `C_c·(T₀−T)·(T_h−T₀) ≤ T₀·[C_c·(T₀−T) + C_c·T_h·log(…)]`.
      field_simp [hden.ne']
      nlinarith [hprod, mul_pos hCc (mul_pos (sub_pos.mpr hTtT0) hden), hden, proc.T0_pos, hy]
    -- Rewrite into the goal orientation expected after `div_le_div_iff₀`.
    nlinarith [hgoal]
  · -- Uniqueness: the predicate fixes `cop` to the ratio.
    rintro cop' ⟨rfl, -, -⟩
    rfl

end IPhO_2026_3_C_5
