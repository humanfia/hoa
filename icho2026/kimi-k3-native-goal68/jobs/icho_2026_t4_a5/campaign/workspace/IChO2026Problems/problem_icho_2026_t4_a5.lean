import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T4, part A5 — neutron thermalization in water

## Source statement (theory_problem.pdf, source page 38, printed page Q4-2)

> 4.5 **Determine** the average number of collisions required, n_c, to slow a
> neutron from 2 MeV to 0.012 eV, using water as the moderator. ξ(water) = 0.948

The shared problem text defines the logarithmic energy decrement through

    ξ = ln (E_initial / E_final),

where E_initial and E_final are the initial and final neutron energies *per
collision*, and states that ξ is a constant for each type of material and does
not depend on the initial neutron energy.  Fission neutrons are produced with
an average energy of 2 MeV (shared context).

## Model (every premise is taken from the problem text)

Since ξ is the *average* decrease of `log E` per collision and is independent
of the energy, the average log-energy after `n` collisions obeys the
recurrence `L(n+1) = L(n) - ξ`, `L(0) = log E₀`, whose closed form

    L(n) = log E₀ - n · ξ

is proved below (`logEnergyAfter_eq`).  Reaching a target average log-energy
`log E_target` therefore requires

    ξ · n_c = log (E₀ / E_target)   ⟹   n_c = log (E₀ / E_target) / ξ.

## Numerical evaluation (no intermediate rounding)

    n_c = log (2·10⁶ eV / 0.012 eV) / 0.948
        = log ( (5/3)·10⁸ ) / 0.948
        = (log (5/3) + 8·log 10) / 0.948
        ≈ 18.9315063677 / 0.948
        ≈ 19.96994   collisions   (raw value),
        = 20.0       collisions   at the 3-significant-figure reporting default.

The certified bounds `19.96 ≤ n_c < 19.98` proved below place the raw value
strictly inside the 3-s.f. reporting cell of `20.0`, namely `[19.95, 20.05)`.
Physically, an average of ≈ 20 collisions per neutron is required.
-/

namespace IChO2026.T4_A5

open Real Finset

/-! ## Problem inputs (exactly as printed; energies converted to the common
unit eV using 1 MeV = 10⁶ eV) -/

/-- Initial (fission) neutron energy in eV: 2 MeV = 2·10⁶ eV. -/
noncomputable def Einitial : ℝ := 2 * 10 ^ 6

/-- Target (thermalised) neutron energy in eV: 0.012 eV. -/
noncomputable def Etarget : ℝ := 0.012

/-- Logarithmic energy decrement of water: ξ(water) = 0.948. -/
noncomputable def ξWater : ℝ := 0.948

/-- ξ(water) is nonzero (it is a printed positive constant). -/
theorem ξWater_ne : ξWater ≠ 0 := by
  unfold ξWater; norm_num

/-- ξ(water) is positive. -/
theorem ξWater_pos : 0 < ξWater := by
  unfold ξWater; norm_num

/-! ## The slowing-down model -/

/-- `logEnergyAfter n logE₀ ξ` is the average log-neutron-energy after `n`
collisions, starting from average log-energy `logE₀`, where each collision
lowers the logarithm of the energy by the material constant ξ on average
(this is exactly the per-collision statement of the problem's definition of
ξ, iterated using the printed fact that ξ does not depend on the initial
energy). -/
def logEnergyAfter : ℕ → ℝ → ℝ → ℝ
  | 0, logE₀, _ => logE₀
  | n + 1, logE₀, ξ => logEnergyAfter n logE₀ ξ - ξ

/-- Closed form of the slowing-down recurrence: after `n` collisions the
average log-energy is `logE₀ - n·ξ`. -/
theorem logEnergyAfter_eq (n : ℕ) (logE₀ ξ : ℝ) :
    logEnergyAfter n logE₀ ξ = logE₀ - n * ξ := by
  induction n with
  | zero => simp [logEnergyAfter]
  | succ k ih =>
      rw [logEnergyAfter, ih]
      push_cast
      ring

/-- The average collision count for a total log-energy decrement `L` with
per-collision decrement `ξ`: the unique `n` with `ξ · n = L`. -/
noncomputable def averageCollisions (ξ L : ℝ) : ℝ := L / ξ

/-- The average collision count achieves its defining log-energy balance:
after `averageCollisions ξ L` collisions the accumulated average
log-decrement is exactly `L`. -/
theorem averageCollisions_spec {ξ L : ℝ} (hξ : ξ ≠ 0) :
    ξ * averageCollisions ξ L = L := by
  unfold averageCollisions
  field_simp

/-- Uniqueness: any collision count achieving the required log-energy
decrement equals the average collision count. -/
theorem averageCollisions_unique {ξ L n : ℝ} (hξ : ξ ≠ 0) (h : ξ * n = L) :
    n = averageCollisions ξ L := by
  unfold averageCollisions
  field_simp
  linear_combination h

/-- **The requested quantity**: the exact raw value of the average number of
collisions needed to slow a neutron from `Einitial` to `Etarget` in water.
By `logEnergyAfter_eq`, after `n` collisions the average log-energy is
`log Einitial - n·ξ`; setting this equal to `log Etarget` gives the equation
`ξWater · n = log (Einitial / Etarget)` solved by this value
(see `ncRaw_spec`). -/
noncomputable def ncRaw : ℝ := averageCollisions ξWater (log (Einitial / Etarget))

/-- Characterization of the raw answer:
`n_c = log (Einitial / Etarget) / ξ(water)`. -/
theorem ncRaw_eq : ncRaw = log (Einitial / Etarget) / ξWater := rfl

/-- The raw answer achieves the required average slowing: `ncRaw` collisions
lower the average log-energy by exactly `log (Einitial / Etarget)`. -/
theorem ncRaw_spec : ξWater * ncRaw = log (Einitial / Etarget) :=
  averageCollisions_spec ξWater_ne

/-! ## Certified bounds on the total log-decrement `log (Einitial / Etarget)`

The energy ratio is the exact rational

    Einitial / Etarget = 2·10⁶ / 0.012 = (5/3)·10⁸,

so `log (Einitial / Etarget) = log (5/3) + 8·log 10`.  We decompose further:

    log 10 = log 2 + log 5 = log 2 + log 2 + log (5/2),

and bound each ingredient rationally through the power series

    ½·log((1+x)/(1−x)) = x + x³/3 + x⁵/5 + …      (|x| < 1),

which is the artanh series.  The substitutions

    log 2     = 2 · s(1/3)      since (1 + 1/3)/(1 − 1/3) = 2,
    log (5/2) = 2 · s(3/7)      since (1 + 3/7)/(1 − 3/7) = 5/2,
    log (5/3) = 2 · s(1/4)      since (1 + 1/4)/(1 − 1/4) = 5/3

give

* lower bounds via `Real.sum_range_le_log_div` (partial sums of the series
  are lower bounds for ½·log), and
* upper bounds via `Real.log_div_le_sum_range_add` (partial sum plus a
  geometric-series remainder dominates ½·log).

Every evaluation is an exact rational identity discharged by `norm_num`, so
no floating-point or intermediate rounding ever enters the development. -/

/-- The energy ratio, as an exact rational: `Einitial / Etarget = (5/3)·10⁸`. -/
theorem E_ratio : Einitial / Etarget = (5 / 3 : ℝ) * 10 ^ 8 := by
  unfold Einitial Etarget; norm_num

section ArtanhBounds

/-- Generic lower bound: the `m`-term partial sum of the artanh series lower
bounds `½·log r` whenever `(1 + x)/(1 − x) = r`. -/
theorem artanh_lower {x r : ℝ} (h0 : 0 ≤ x) (h1 : x < 1)
    (hr : (1 + x) / (1 - x) = r) (m : ℕ) :
    2 * ∑ i ∈ range m, x ^ (2 * i + 1) / (2 * i + 1) ≤ log r := by
  have h := Real.sum_range_le_log_div h0 h1 m
  rw [hr] at h
  linarith

/-- Generic upper bound: the `m`-term partial sum plus the geometric
remainder dominates `½·log r`. -/
theorem artanh_upper {x r : ℝ} (h0 : 0 ≤ x) (h1 : x < 1)
    (hr : (1 + x) / (1 - x) = r) (m : ℕ) :
    log r ≤ 2 * (∑ i ∈ range m, x ^ (2 * i + 1) / (2 * i + 1)
      + x ^ (2 * m + 1) / (1 - x ^ 2)) := by
  have h := Real.log_div_le_sum_range_add h0 h1 m
  rw [hr] at h
  linarith

/-- Lower bound for `log 2` from the 8-term artanh series at `x = 1/3`:
`log 2 ≥ 149337754816/215448838605 ≈ 0.69314718`. -/
theorem log_two_lower :
    (149337754816 / 215448838605 : ℝ) ≤ log 2 := by
  have h := artanh_lower (x := (1/3 : ℝ)) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine le_trans ?_ h
  norm_num [sum_range_succ]

/-- Upper bound for `log 2` from the 8-term artanh series at `x = 1/3`:
`log 2 ≤ 597351034279/861795354420 ≈ 0.69314720`. -/
theorem log_two_upper :
    log 2 ≤ (597351034279 / 861795354420 : ℝ) := by
  have h := artanh_upper (x := (1/3 : ℝ)) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine h.trans ?_
  norm_num [sum_range_succ]

/-- Lower bound for `log (5/2)` from the 8-term artanh series at `x = 3/7`:
`log (5/2) ≥ 3110354561150016/3394506479609245 ≈ 0.91629065`. -/
theorem log_five_halves_lower :
    (3110354561150016 / 3394506479609245 : ℝ) ≤ log (5 / 2) := by
  have h := artanh_lower (x := (3/7 : ℝ)) (r := 5/2) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine le_trans ?_ h
  norm_num [sum_range_succ]

/-- Upper bound for `log (5/2)` from the 8-term artanh series at `x = 3/7`:
`log (5/2) ≤ 1777348101663339/1939717988348140 ≈ 0.91629201`. -/
theorem log_five_halves_upper :
    log (5 / 2) ≤ (1777348101663339 / 1939717988348140 : ℝ) := by
  have h := artanh_upper (x := (3/7 : ℝ)) (r := 5/2) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine h.trans ?_
  norm_num [sum_range_succ]

/-- Lower bound for `log (5/3)` from the 8-term artanh series at `x = 1/4`. -/
theorem log_five_thirds_lower :
    (12353474966347 / 24183350231040 : ℝ) ≤ log (5 / 3) := by
  have h := artanh_lower (x := (1/4 : ℝ)) (r := 5/3) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine le_trans ?_ h
  norm_num [sum_range_succ]

/-- Upper bound for `log (5/3)` from the 8-term artanh series at `x = 1/4`. -/
theorem log_five_thirds_upper :
    log (5 / 3 : ℝ) ≤ (1235347496935 / 2418335023104 : ℝ) := by
  have h := artanh_upper (x := (1/4 : ℝ)) (r := 5/3) (by norm_num) (by norm_num)
    (by norm_num) 8
  refine h.trans ?_
  norm_num [sum_range_succ]

/-- `log 10 = 2·log 2 + log (5/2)`: since `10 = 2 · 2 · (5/2)`. -/
theorem log_ten_eq : log 10 = 2 * log 2 + log (5 / 2 : ℝ) := by
  have h10 : (10 : ℝ) = 2 * 2 * (5 / 2) := by norm_num
  rw [h10, log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num)]
  ring

/-- Certified lower bound on `log 10`. -/
theorem log_ten_lower :
    (2 * (149337754816 / 215448838605)
      + 3110354561150016 / 3394506479609245 : ℝ) ≤ log 10 := by
  rw [log_ten_eq]
  linarith [log_two_lower, log_five_halves_lower]

/-- Certified upper bound on `log 10`. -/
theorem log_ten_upper :
    log 10 ≤ (2 * (597351034279 / 861795354420)
      + 1777348101663339 / 1939717988348140 : ℝ) := by
  rw [log_ten_eq]
  linarith [log_two_upper, log_five_halves_upper]

end ArtanhBounds

theorem log_total_eq :
    log (Einitial / Etarget) = log (5 / 3 : ℝ) + 8 * log 10 := by
  rw [E_ratio]
  rw [log_mul (by norm_num) (by norm_num), Real.log_pow]
  ring

/-- Total log-decrement, lower bound:
`log (Einitial / Etarget) ≥ 18.93150572…`. -/
theorem log_total_lower :
    ((12353474966347 / 24183350231040
      + 8 * (2 * (149337754816 / 215448838605)
        + 3110354561150016 / 3394506479609245)) : ℝ)
      ≤ log (Einitial / Etarget) := by
  rw [log_total_eq]
  rw [log_ten_eq]
  linarith [log_five_thirds_lower, log_two_lower, log_five_halves_lower]

/-- Total log-decrement, upper bound:
`log (Einitial / Etarget) ≤ 18.93151689…`. -/
theorem log_total_upper :
    log (Einitial / Etarget)
      ≤ ((1235347496935 / 2418335023104
        + 8 * (2 * (597351034279 / 861795354420)
          + 1777348101663339 / 1939717988348140)) : ℝ) := by
  rw [log_total_eq]
  rw [log_ten_eq]
  linarith [log_five_thirds_upper, log_two_upper, log_five_halves_upper]

/-- **Certified lower bound on the requested average collision count**:
`n_c ≥ 19.96`.  Since `ξWater > 0`,
`n_c = log(Einitial/Etarget)/ξWater ≥ [lower bound]/0.948`, and the rational
inequality `lowerbound ≥ 0.948·19.96 = 18.92208` is decided by `norm_num`. -/
theorem ncRaw_lower : (1996 / 100 : ℝ) ≤ ncRaw := by
  have hξ : (0 : ℝ) < ξWater := ξWater_pos
  have hlb := log_total_lower
  have hr : (1996 / 100 : ℝ) * ξWater
      ≤ 12353474966347 / 24183350231040
        + 8 * (2 * (149337754816 / 215448838605)
          + 3110354561150016 / 3394506479609245) := by
    unfold ξWater
    norm_num
  rw [ncRaw_eq]
  rw [le_div_iff₀ hξ]
  exact hr.trans hlb

/-- **Certified upper bound on the requested average collision count**:
`n_c < 19.98`.  Similar to `ncRaw_lower`, using `log_total_upper` and the
strict rational inequality `upperbound < 0.948·19.98 = 18.94104`. -/
theorem ncRaw_upper : ncRaw < (1998 / 100 : ℝ) := by
  have hξ : (0 : ℝ) < ξWater := ξWater_pos
  have hub := log_total_upper
  have hr : (1235347496935 / 2418335023104
      + 8 * (2 * (597351034279 / 861795354420)
        + 1777348101663339 / 1939717988348140) : ℝ) < (1998 / 100) * ξWater := by
    unfold ξWater
    norm_num
  rw [ncRaw_eq]
  rw [div_lt_iff₀ hξ]
  exact hub.trans_lt hr



/-- **Main result (raw value)**: the average number of collisions required to
slow a neutron from 2 MeV to 0.012 eV in water satisfies

    19.96 ≤ n_c < 19.98,

i.e. `n_c ≈ 19.97` collisions, and the three-significant-figure default
report is `20.0` collisions: `n_c ∈ [19.95, 20.05)`, the half-quantum cell
of `20.0` at quantum `0.1`. -/
theorem ncRaw_bounds : (1996 / 100 : ℝ) ≤ ncRaw ∧ ncRaw < 1998 / 100 :=
  ⟨ncRaw_lower, ncRaw_upper⟩

/-- The raw value lies in the three-significant-figure reporting cell of
`20.0` (half-quantum interval `[19.95, 20.05)` at quantum `0.1`). -/
theorem ncRaw_in_reporting_cell :
    (1995 / 100 : ℝ) ≤ ncRaw ∧ ncRaw < 2005 / 100 := by
  constructor
  · linarith [ncRaw_lower]
  · linarith [ncRaw_upper]

/-! ## Interfacing with the answer-blind reporting contract -/

open IChO2026Chem.Reporting

/-- The chosen submission: raw value `ncRaw`, reported value `20.0`
collisions at the three-significant-figure default quantum `0.1`. -/
noncomputable def submission : NumericSubmission where
  rawValue := ncRaw
  reportedValue := 20
  reportingQuantum := 1 / 10

/-- The submission satisfies the fixed answer-blind reporting contract: the
reported value `20.0 = 200 · 0.1` is a multiple of the quantum, and the raw
value `19.96 ≤ n_c < 19.98` lies strictly inside the half-quantum cell
`[19.95, 20.05)` of the reported value (with strict inequalities to spare,
so no tie-breaking question arises). -/
theorem submission_valid :
    ValidNumericSubmission ncRaw submission := by
  refine ⟨rfl, ?_⟩
  have hq : (0 : ℝ) < submission.reportingQuantum := by
    change (0 : ℝ) < 1 / 10
    norm_num
  have hmult : ∃ k : ℤ, submission.reportedValue = submission.reportingQuantum * k := by
    refine ⟨200, ?_⟩
    change (20 : ℝ) = 1 / 10 * (200 : ℤ)
    norm_num
  refine ⟨hq, hmult, ?_⟩
  have hlo := ncRaw_lower
  have hhi := ncRaw_upper
  have hrawpos : (0 : ℝ) ≤ submission.rawValue := by
    change (0 : ℝ) ≤ ncRaw
    linarith
  rw [if_pos hrawpos]
  change submission.reportedValue - submission.reportingQuantum / 2 ≤ submission.rawValue ∧
    submission.rawValue < submission.reportedValue + submission.reportingQuantum / 2
  refine ⟨?_, ?_⟩ <;> simp only [submission] <;> linarith

end IChO2026.T4_A5
