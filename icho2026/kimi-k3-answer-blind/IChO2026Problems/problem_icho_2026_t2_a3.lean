import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T2, part A3 (printed item 2.3): critical bromide
concentration of the Belousov–Zhabotinsky reaction

## Source contract (answer-blind; problem-only inputs)

* Source images: `icho_2026_source/image/T2_page-2.png` (mechanism table with
  the elementary steps and rate constants, and the maintained-concentration
  assumptions) and `icho_2026_source/image/T2_page-3.png` (phase portrait of
  `[HBrO₂]` vs `[Br⁻]`, the switch-over rule, and printed item 2.3:
  "Calculate [Br⁻]critical").
* Step (1): `HBrO₂ + BrO₃⁻ + H⁺ → 2BrO₂• + H₂O`, `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`.
* Step (4): `HBrO₂ + Br⁻ + H⁺ → 2HBrO`, `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`.
* `[BrO₃⁻]₀ = 0.06 M` and `[H⁺]₀ = 0.8 M`, maintained constant throughout
  the BZ reaction.
* Switch-over rule (problem text, T2_page-3.png): "To switch Process A to
  Process B, the reaction rate of the elementary step (4) must exceed that of
  the elementary step (1) and vice versa."  Hence `[Br⁻]critical` is the
  balance point `r₄ = r₁`.

## Assumption / target split

Assumptions (all problem-stipulated): the two elementary-step mass-action
rate laws, the rate constants `k₁`, `k₄`, and the maintained concentrations
`[BrO₃⁻]`, `[H⁺]`.  Target: the unique positive bromide concentration at
which `r₄ = r₁`.

Because steps (1) and (4) are both first order in HBrO₂, the balance point
`k₄·[Br⁻] = k₁·[BrO₃⁻]` is independent of the stationary `[HBrO₂]`.  The
T2-A2 prerequisite (`[HBrO₂]A`, `[HBrO₂]B`) therefore cancels out of this
part: no T2-A2 value (derived or printed fallback) is consumed, and the
printed `[Br⁻]critical` fallback `1 × 10⁻⁷ M` on T2_page-3.png is authorised
only for *later* parts and is not used here.

## Raw and reported results

Raw (unrounded, exact): `[Br⁻]critical = k₁·[BrO₃⁻]/k₄ = 3/10000000 mol dm⁻³`.
Reporting rule: three significant figures, ties away from zero (the project
`final_precision` of the source reporting policy), giving `3.00e-7 mol dm⁻³`
at the last-place quantum `1e-9 mol dm⁻³`.
-/

namespace IChO2026Problems.ProblemIcho2026T2A3

/-! ## Problem-stipulated constants (exact as printed) -/

/-- Rate constant of elementary step (1), `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`
(problem-stipulated, T2_page-2.png). -/
def k1 : ℝ := 1.0e4

/-- Rate constant of elementary step (4), `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`
(problem-stipulated, T2_page-2.png). -/
def k4 : ℝ := 2.0e9

/-- Bromate concentration, maintained constant throughout the BZ reaction:
`[BrO₃⁻] = 0.06 mol dm⁻³` (problem-stipulated, T2_page-2.png). -/
def bromateConc : ℝ := 0.06

/-- Hydrogen-ion concentration, maintained constant throughout the BZ
reaction: `[H⁺] = 0.8 mol dm⁻³` (problem-stipulated, T2_page-2.png). -/
def hydrogenConc : ℝ := 0.8

/-! ## Mass-action rate laws of the two competing elementary steps -/

/-- Rate of elementary step (1): `r₁ = k₁·[HBrO₂]·[BrO₃⁻]·[H⁺]`. -/
def rateStep1 (hbrO2 brO3 h : ℝ) : ℝ :=
  k1 * hbrO2 * brO3 * h

/-- Rate of elementary step (4): `r₄ = k₄·[HBrO₂]·[Br⁻]·[H⁺]`. -/
def rateStep4 (hbrO2 br h : ℝ) : ℝ :=
  k4 * hbrO2 * br * h

/-! ## Criticality -/

/-- The critical-bromide predicate at the maintained bromate and hydrogen-ion
concentrations: the rate of step (4) equals the rate of step (1).  Both steps
are first order in HBrO₂, so the balance is quantified over every positive
stationary HBrO₂ level; the common factor cancels. -/
def IsCriticalBromide (br : ℝ) : Prop :=
  ∀ hbrO2 : ℝ, 0 < hbrO2 →
    rateStep4 hbrO2 br hydrogenConc = rateStep1 hbrO2 bromateConc hydrogenConc

/-- Raw, unrounded critical bromide concentration, derived end to end from the
problem-stipulated constants by `r₄ = r₁ ⟺ k₄·[Br⁻] = k₁·[BrO₃⁻]`. -/
noncomputable def bromideCriticalRaw : ℝ :=
  k1 * bromateConc / k4

/-- Derivation specification: `bromideCriticalRaw` is the unique positive
bromide concentration at which the rates of steps (1) and (4) coincide; above
it step (4) is faster (switch towards Process B) and below it step (1) is
faster (switch towards Process A). -/
def bromideCriticalRawSpec : Prop :=
  0 < bromideCriticalRaw ∧
    IsCriticalBromide bromideCriticalRaw ∧
      (∀ y : ℝ, 0 < y → IsCriticalBromide y → y = bromideCriticalRaw) ∧
        (∀ hbrO2 br : ℝ, 0 < hbrO2 → bromideCriticalRaw < br →
          rateStep1 hbrO2 bromateConc hydrogenConc <
            rateStep4 hbrO2 br hydrogenConc) ∧
          ∀ hbrO2 br : ℝ, 0 < hbrO2 → 0 ≤ br → br < bromideCriticalRaw →
            rateStep4 hbrO2 br hydrogenConc <
              rateStep1 hbrO2 bromateConc hydrogenConc

/-- Exact rational value of the raw expression:
`k₁·[BrO₃⁻]/k₄ = 3/10000000 mol dm⁻³`. -/
theorem bromideCriticalRaw_value :
    bromideCriticalRaw = (3 : ℝ) / 10000000 := by
  norm_num [bromideCriticalRaw, k1, k4, bromateConc]

/-- **Raw result contract** (answer-blind certificate): the end-to-end derived
critical bromide concentration satisfies the derivation specification and lies
in the certified interval `[2.995e-7, 3.005e-7]`, the reporting half-cell of
the three-significant-figure quantum `1e-9 mol dm⁻³`. -/
theorem bromideCriticalRawResult :
    bromideCriticalRawSpec ∧
      ((599 : ℝ) / 2000000000) ≤ bromideCriticalRaw ∧
        bromideCriticalRaw ≤ ((601 : ℝ) / 2000000000) := by
  have hval : bromideCriticalRaw = (3 : ℝ) / 10000000 := bromideCriticalRaw_value
  -- The rate-balance condition `r₄ = r₁` at the maintained concentrations:
  -- `k₄·[Br⁻]critical = k₁·[BrO₃⁻]`, i.e. `2.0e9 · (1.0e4 · 0.06 / 2.0e9) = 600`.
  have hk : k4 * bromideCriticalRaw = k1 * bromateConc := by
    norm_num [bromideCriticalRaw, k1, k4, bromateConc]
  have hk4pos : (0 : ℝ) < k4 := by norm_num [k4]
  have hk4ne : k4 ≠ 0 := ne_of_gt hk4pos
  have hhpos : (0 : ℝ) < hydrogenConc := by norm_num [hydrogenConc]
  have hhne : hydrogenConc ≠ 0 := ne_of_gt hhpos
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `[Br⁻]critical > 0`: it equals `3/10000000`.
    rw [hval]
    norm_num
  · -- At `[Br⁻]critical` the two step rates coincide for every `[HBrO₂] > 0`.
    intro x _
    change k4 * x * bromideCriticalRaw * hydrogenConc
        = k1 * x * bromateConc * hydrogenConc
    linear_combination x * hydrogenConc * hk
  · -- Uniqueness: any positive critical bromide level equals `k₁·[BrO₃⁻]/k₄`.
    intro y _ hy
    have h1 : k4 * (1 : ℝ) * y * hydrogenConc
        = k1 * (1 : ℝ) * bromateConc * hydrogenConc := hy 1 one_pos
    have h1' : (k4 * y) * hydrogenConc = (k1 * bromateConc) * hydrogenConc := by
      calc (k4 * y) * hydrogenConc = k4 * 1 * y * hydrogenConc := by ring
        _ = k1 * 1 * bromateConc * hydrogenConc := h1
        _ = (k1 * bromateConc) * hydrogenConc := by ring
    have h2 : k4 * y = k1 * bromateConc := mul_right_cancel₀ hhne h1'
    have h3 : y = k1 * bromateConc / k4 := by
      rw [eq_div_iff hk4ne]
      linear_combination h2
    exact h3
  · -- Above criticality step (4) is faster: switch from Process A to Process B.
    intro x br hx hbr
    have hfactor : (0 : ℝ) < k4 * x * hydrogenConc := by positivity
    calc rateStep1 x bromateConc hydrogenConc
        = (k4 * x * hydrogenConc) * bromideCriticalRaw := by
          change k1 * x * bromateConc * hydrogenConc
              = (k4 * x * hydrogenConc) * bromideCriticalRaw
          linear_combination -x * hydrogenConc * hk
      _ < (k4 * x * hydrogenConc) * br := mul_lt_mul_of_pos_left hbr hfactor
      _ = rateStep4 x br hydrogenConc := by
          change (k4 * x * hydrogenConc) * br = k4 * x * br * hydrogenConc
          ring
  · -- Below criticality step (1) is faster: switch from Process B to Process A.
    intro x br hx _ hbr
    have hfactor : (0 : ℝ) < k4 * x * hydrogenConc := by positivity
    calc rateStep4 x br hydrogenConc
        = (k4 * x * hydrogenConc) * br := by
          change k4 * x * br * hydrogenConc = (k4 * x * hydrogenConc) * br
          ring
      _ < (k4 * x * hydrogenConc) * bromideCriticalRaw :=
          mul_lt_mul_of_pos_left hbr hfactor
      _ = rateStep1 x bromateConc hydrogenConc := by
          change (k4 * x * hydrogenConc) * bromideCriticalRaw
              = k1 * x * bromateConc * hydrogenConc
          linear_combination x * hydrogenConc * hk
  · -- Lower half-cell bound: `2.995e-7 ≤ 3e-7`.
    rw [hval]
    norm_num
  · -- Upper half-cell bound: `3e-7 ≤ 3.005e-7`.
    rw [hval]
    norm_num

/-- **Reported result contract**: the raw critical bromide concentration,
reported at three significant figures (quantum `1e-9 mol dm⁻³`, ties away
from zero), is `3.00e-7 mol dm⁻³`. -/
theorem bromideCriticalReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum bromideCriticalRaw
      ((300 : ℝ) / 1000000000) ((1 : ℝ) / 1000000000) := by
  rw [bromideCriticalRaw_value]
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(300 : ℤ), by norm_num⟩, ?_⟩
  -- `raw = 3e-7 ≥ 0`, so the `0 ≤ raw` branch applies; the raw value sits in
  -- the half-quantum cell `[3e-7 - 5e-10, 3e-7 + 5e-10)` around `3.00e-7`.
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 3 / 10000000)]
  constructor <;> norm_num

end IChO2026Problems.ProblemIcho2026T2A3
