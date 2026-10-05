/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), Subquestion 7.3

Blueprint chapter: `blueprint/src/chapters/IChO2026Problems_problem_icho_2026_t7_a3.tex`.
Source report: `reports/icho_2026/problem_icho_2026_t7_a3.source.json`
(`blind_record_sha256 = 9a249c84aa1ece0fe1c4ddc64196f5455985bc2a539a43bf6f7b4e4b9dc32662`).

## Problem data (problem text and problem image `T7_page-2.png`, Fig. 2)

A model of a real reaction system with recirculation of reagents.  An open
system operates in a cyclic mode; each cycle has four steps:

1. a stoichiometric `N2 : H2 = 1 : 3` mixture with total amount `n0` mol is fed
   into the reactor after each cycle (hence `n0/4` mol of `N2` per cycle);
2. the reaction proceeds with a fixed yield `η = 0.150` (fraction of the
   nitrogen present that is converted, per cycle);
3. ammonia is separated by liquification;
4. unreacted gases are returned into the reactor.

The cycle is repeated until the required overall yield is reached.  Feed and
consumption are both in the ratio `1 : 3`, so the gas inventory in the reactor
stays stoichiometric and tracking the `N2` amount suffices.

**Subquestion 7.3.** a) Calculate the amount of nitrogen present in the system
after the 58th cycle (before the addition of the 59th portion of mixture), if
`n0 = 4` mol; provide 4 decimal places.  Hint: a formula for the sum of the
terms of a geometric progression is needed.  b) Calculate the number of cycles
needed to increase the overall yield from `15.0%` to `97.0%`.

## Assumption / target split

* **Assumptions** (all from the problem text/image): the four printed cycle
  steps; `η = 0.150` and `n0 = 4` mol stipulated exactly as printed; the `1:3`
  feed stoichiometry; full liquefaction removal of `NH3`; full recycle of the
  unreacted gas.  The previous part T7-A1 concerns the Fig. 1 steady-state
  flowsheet and is not consumed by this Fig. 2 cyclic model.
* **Targets.** a) raw `n(N2)` after 58 cycles with a certified enclosure,
  reported at the problem-requested 4-decimal quantum `1e-4` mol; b) the least
  number of cycles at which the overall yield reaches `97.0%` (exact integer).

## Derivation carried by this file

Let `r(k)` be the nitrogen present right after cycle `k`.  Then `r(0) = 0` and
`r(k+1) = (1-η)(r(k) + n0/4)`, with closed form (finite geometric series, the
printed hint)
`r(k) = (n0/4)(1-η)(1-(1-η)^k)/η`, carried by `nitrogenAfterCycles` with
`nitrogenAfterCycles_zero` and `nitrogenAfterCycles_recurrence`.
With `n0 = 4`, `η = 0.150`: `r(58) = (17/3)(1-(17/20)^58) = 5.6662099726...`
mol, enclosed in `[5.66620, 5.66622]` and reported as `5.6662` mol.

The overall yield after `k` cycles is
`Y(k) = 1 - r(k)/(k·n0/4) = 1 - (1-η)(1-(1-η)^k)/(η·k)`; `Y(1) = 0.15` (the
printed `15.0%` starting point).  `Y` is strictly increasing: with `q = 1-η`,
`q^k (1 + k(1-q)) ≤ ((1-q)(1+(1-q)))^k = (1-(1-q)^2)^k ≤ 1` by Bernoulli's
inequality, which rearranges to `Y(k) ≤ Y(k+1)`.  Finally
`Y(188) < 0.970 ≤ Y(189)` (using `(17/20)^58 < 10^{-4}` for the lower side and
`1-(17/20)^189 ≤ 1` for the upper side), so the least cycle count is `189`,
formalized as `IsLeast cyclesReachingTarget 189`.
-/

namespace IChO2026Problems.Icho2026T7A3

/-! ## Problem-stipulated data (steps 1–2 of the cyclic model) -/

/-- Per-cycle yield `η = 0.150`: the fraction of the nitrogen present that is
converted to ammonia in each cycle (step 2, stipulated exactly as printed). -/
def cycleYield : ℝ := 0.150

/-- Total fresh mixture fed per cycle: `n0 = 4` mol of stoichiometric
`N2 : H2 = 1 : 3` mixture (step 1 with the part-(a) value), so the nitrogen
feed per cycle is `feedTotalAmount / 4 = 1` mol. -/
def feedTotalAmount : ℝ := 4

/-- The required overall yield of part (b): `97.0%`, stipulated exactly as
printed. -/
def targetYield : ℝ := 0.970

/-! ## The cyclic nitrogen inventory -/

/-- Nitrogen `r(k)` (mol of `N2`) present in the system right after cycle `k`
(before the next feed).  Closed form of the recurrence `r(0) = 0`,
`r(k+1) = (1-η)(r(k) + n0/4)`, obtained from the finite geometric series as
the printed hint requires: `r(k) = (n0/4)(1-η)(1-(1-η)^k)/η`. -/
noncomputable def nitrogenAfterCycles (n0 η : ℝ) (k : ℕ) : ℝ :=
  n0 / 4 * (1 - η) * (1 - (1 - η)^k) / η

/-- The closed form starts at zero: nothing is in the reactor before the first
cycle. -/
theorem nitrogenAfterCycles_zero (n0 η : ℝ) : nitrogenAfterCycles n0 η 0 = 0 := by
  simp [nitrogenAfterCycles]

/-- The closed form satisfies the cycle-to-cycle recurrence: the surviving
fraction `1-η` acts on the sum of the recycled inventory and the fresh
`n0/4` mol nitrogen portion. -/
theorem nitrogenAfterCycles_recurrence (n0 η : ℝ) (hη : η ≠ 0) (k : ℕ) :
    nitrogenAfterCycles n0 η (k + 1) = (1 - η) * (nitrogenAfterCycles n0 η k + n0 / 4) := by
  simp only [nitrogenAfterCycles, pow_succ]
  field_simp
  ring

/-- Overall yield after `k` cycles: total nitrogen fed is `k · n0/4`, the
amount converted to ammonia is `k · n0/4 - r(k)`, so the overall yield is
`1 - r(k)/(k · n0/4)`. -/
noncomputable def overallYieldAfterCycles (n0 η : ℝ) (k : ℕ) : ℝ :=
  1 - nitrogenAfterCycles n0 η k / (k * (n0 / 4))

/-- The overall yield in the `q`-form: the feed factor `n0/4` cancels. -/
theorem overallYield_general (n0 η : ℝ) (hη : η ≠ 0) (hn0 : n0 ≠ 0) (k : ℕ)
    (hk : ((k : ℕ) : ℝ) ≠ 0) :
    overallYieldAfterCycles n0 η k = 1 - (1 - η) * (1 - (1 - η)^k) / (η * ((k : ℕ) : ℝ)) := by
  unfold overallYieldAfterCycles nitrogenAfterCycles
  field_simp

/-- The overall yield with the problem data, in the explicit rational form
`Y(k) = 1 - (17/3)(1-(17/20)^k)/k`. -/
theorem overallYield_eq (k : ℕ) (hk : 1 ≤ k) :
    overallYieldAfterCycles feedTotalAmount cycleYield k
      = 1 - (17 / 3 : ℝ) * (1 - (17 / 20)^k) / ((k : ℕ) : ℝ) := by
  have hk0 : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [overallYield_general feedTotalAmount cycleYield (by norm_num [cycleYield])
    (by norm_num [feedTotalAmount]) k hk0]
  have hc : cycleYield = (3 / 20 : ℝ) := by norm_num [cycleYield]
  rw [hc]
  have h320 : (3 / 20 : ℝ) ≠ 0 := by norm_num
  field_simp
  ring

/-- After one cycle the overall yield is exactly `η = 0.150`: the printed
`15.0%` starting point of part (b). -/
theorem overallYield_one :
    overallYieldAfterCycles feedTotalAmount cycleYield 1 = 0.150 := by
  rw [overallYield_eq 1 (le_refl 1)]
  norm_num

/-! ## Part (a): nitrogen after the 58th cycle -/

/-- Raw (unrounded) amount of nitrogen after the 58th cycle, in mol. -/
noncomputable def nitrogenAfter58Raw : ℝ := nitrogenAfterCycles feedTotalAmount cycleYield 58

/-- Numerical evaluation: `r(58) = (17/3)(1-(17/20)^58)`. -/
theorem nitrogenAfter58Raw_eq :
    nitrogenAfter58Raw = (17 / 3 : ℝ) * (1 - (17 / 20)^58) := by
  norm_num [nitrogenAfter58Raw, nitrogenAfterCycles, feedTotalAmount, cycleYield]

/-- Strict rational enclosure of the raw value, fixed from the closed form
before any rounding: `5.66620 ≤ r(58) ≤ 5.66622`, wholly inside the committed
4-decimal rounding cell `(5.66615, 5.66625)`. -/
theorem nitrogenAfter58Raw_bounds :
    (5.66620 : ℝ) ≤ nitrogenAfter58Raw ∧ nitrogenAfter58Raw ≤ 5.66622 := by
  rw [nitrogenAfter58Raw_eq]
  constructor <;> norm_num

/-- Reporting at the problem-requested 4-decimal quantum: the raw value is
reported as `5.6662` mol (ties half away from zero; the raw value is not a
half-quantum tie). -/
theorem nitrogenAfter58Raw_reports :
    IChO2026Chem.Reporting.ReportsAtQuantum nitrogenAfter58Raw 5.6662 0.0001 := by
  obtain ⟨hlo, hhi⟩ := nitrogenAfter58Raw_bounds
  have hraw_nonneg : (0 : ℝ) ≤ nitrogenAfter58Raw := by linarith
  refine ⟨by norm_num, ⟨56662, by norm_num⟩, ?_⟩
  rw [if_pos hraw_nonneg]
  constructor <;> linarith

/-! ## Part (b): the least number of cycles reaching 97.0% overall yield -/

/-- The set of cycle counts (at least one cycle) whose overall yield reaches
the required `97.0%`. -/
def cyclesReachingTarget : Set ℕ :=
  {k | 1 ≤ k ∧ overallYieldAfterCycles feedTotalAmount cycleYield k ≥ targetYield}

/-- One monotonicity step for the per-cycle loss ratio.  With `q = 17/20`:
`q^k (1 + k(1-q)) ≤ 1` by Bernoulli (`1 + k(1-q) ≤ (1+(1-q))^k`) and
`q(1+(1-q)) = 391/400 ≤ 1`; cross-multiplication turns this into the claimed
inequality of ratios. -/
theorem yield_ratio_step (k : ℕ) (hk : 1 ≤ k) :
    (17 / 3 : ℝ) * (1 - (17 / 20)^(k + 1)) / (((k + 1 : ℕ)) : ℝ)
      ≤ (17 / 3 : ℝ) * (1 - (17 / 20)^k) / ((k : ℕ) : ℝ) := by
  have q0 : (0 : ℝ) ≤ 17 / 20 := by norm_num
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hk1pos : (0 : ℝ) < (((k + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hkey : (17 / 20 : ℝ)^k * (1 + ((k : ℕ) : ℝ) * (1 - 17 / 20)) ≤ 1 := by
    have hbern : (1 : ℝ) + ((k : ℕ) : ℝ) * (1 - 17 / 20) ≤ (1 + (1 - 17 / 20))^k :=
      one_add_mul_le_pow (a := (1 - 17 / 20 : ℝ)) (by norm_num) k
    have h2 := mul_le_mul_of_nonneg_left hbern (pow_nonneg q0 k)
    have h3 : (17 / 20 : ℝ)^k * (1 + (1 - 17 / 20))^k
        = ((17 / 20) * (1 + (1 - 17 / 20)))^k := (mul_pow _ _ _).symm
    have hb1 : (17 / 20 : ℝ) * (1 + (1 - 17 / 20)) ≤ 1 := by norm_num
    have hb0 : (0 : ℝ) ≤ (17 / 20 : ℝ) * (1 + (1 - 17 / 20)) := by norm_num
    have h4 : ((17 / 20 : ℝ) * (1 + (1 - 17 / 20)))^k ≤ 1 :=
      le_trans (pow_le_pow_left₀ hb0 hb1 k) (one_pow k).le
    calc (17 / 20 : ℝ)^k * (1 + ((k : ℕ) : ℝ) * (1 - 17 / 20))
        ≤ (17 / 20)^k * (1 + (1 - 17 / 20))^k := h2
      _ = ((17 / 20) * (1 + (1 - 17 / 20)))^k := h3
      _ ≤ 1 := h4
  rw [div_le_iff₀ hk1pos,
    div_mul_eq_mul_div ((17 / 3 : ℝ) * (1 - (17 / 20)^k)) (((k : ℕ)) : ℝ) (((k + 1 : ℕ)) : ℝ),
    le_div_iff₀ hkpos]
  push_cast
  rw [pow_succ]
  nlinarith [hkey]

/-- The overall yield is monotone increasing cycle by cycle. -/
theorem overallYield_mono (k : ℕ) (hk : 1 ≤ k) :
    overallYieldAfterCycles feedTotalAmount cycleYield k
      ≤ overallYieldAfterCycles feedTotalAmount cycleYield (k + 1) := by
  rw [overallYield_eq k hk, overallYield_eq (k + 1) (by omega)]
  have hstep := yield_ratio_step k hk
  linarith [hstep]

/-- Monotonicity over a whole range of cycles. -/
theorem overallYield_mono_upto (k m : ℕ) (hk : 1 ≤ k) :
    overallYieldAfterCycles feedTotalAmount cycleYield k
      ≤ overallYieldAfterCycles feedTotalAmount cycleYield (k + m) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h := overallYield_mono (k + n) (by omega)
    exact le_trans ih h

/-- After 189 cycles the required overall yield is reached:
`Y(189) = 1 - (17/3)(1-(17/20)^189)/189 ≥ 1 - 17/567 = 550/567 ≥ 0.970`. -/
theorem yield189 :
    overallYieldAfterCycles feedTotalAmount cycleYield 189 ≥ targetYield := by
  rw [overallYield_eq 189 (by norm_num), targetYield]
  have h1 : (1 : ℝ) - (17 / 20)^189 ≤ 1 := by
    have h := pow_nonneg (show (0 : ℝ) ≤ 17 / 20 by norm_num) 189
    linarith
  have h189 : (0 : ℝ) < ((189 : ℕ) : ℝ) := by norm_num
  have h2 : (17 / 3 : ℝ) * (1 - (17 / 20)^189) / ((189 : ℕ) : ℝ)
      ≤ (17 / 3 : ℝ) * 1 / ((189 : ℕ) : ℝ) := by
    rw [div_le_iff₀ h189, div_mul_cancel₀ _ h189.ne']
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h3 : (1 : ℝ) - (17 / 3) * 1 / ((189 : ℕ) : ℝ) ≥ 0.970 := by norm_num
  linarith [h2, h3]

/-- After 188 cycles the required overall yield is not yet reached:
`(17/20)^188 ≤ (17/20)^58 < 10^{-4}` gives
`Y(188) < 1 - (17/3)(9999/10000)/188 < 0.970`. -/
theorem yield188 :
    overallYieldAfterCycles feedTotalAmount cycleYield 188 < targetYield := by
  rw [overallYield_eq 188 (by norm_num), targetYield]
  have q58 : (17 / 20 : ℝ)^58 < 1 / 10000 := by norm_num
  have q188 : (17 / 20 : ℝ)^188 ≤ (17 / 20 : ℝ)^58 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 58 ≤ 188)
  have h1 : (9999 / 10000 : ℝ) < 1 - (17 / 20)^188 := by linarith [q188, q58]
  have h188 : (0 : ℝ) < ((188 : ℕ) : ℝ) := by norm_num
  have h2 : (17 / 3 : ℝ) * (9999 / 10000) / ((188 : ℕ) : ℝ)
      ≤ (17 / 3 : ℝ) * (1 - (17 / 20)^188) / ((188 : ℕ) : ℝ) := by
    rw [div_le_iff₀ h188, div_mul_cancel₀ _ h188.ne']
    exact mul_le_mul_of_nonneg_left (le_of_lt h1) (by norm_num)
  have h3 : (3 / 100 : ℝ) < (17 / 3) * (9999 / 10000) / ((188 : ℕ) : ℝ) := by norm_num
  linarith [h2, h3]

/-- 189 is the least cycle count at which the overall yield reaches `97.0%`:
membership is `yield189`, and every count in the set is at least 189 because
the yield is monotone and `Y(188) < 0.970`. -/
theorem cycles_189_isLeast : IsLeast cyclesReachingTarget 189 := by
  constructor
  · exact ⟨by norm_num, yield189⟩
  · intro k hk
    obtain ⟨hk1, hkY⟩ := hk
    by_contra hlt
    have hle : k ≤ 188 := by omega
    have hmono := overallYield_mono_upto k (188 - k) hk1
    rw [Nat.add_sub_of_le hle] at hmono
    linarith [hkY, hmono, yield188]

/-! ## Raw and reported result specifications and answer-blind certificates -/

/-- Raw derivation spec covering both requested outputs, before any reporting
rounding: the closed form obeys the cyclic recurrence and starts at zero; the
raw nitrogen amount after 58 cycles is exactly `(17/3)(1-(17/20)^58)` and lies
in the certified enclosure `[5.66620, 5.66622]` mol; the overall yield after
one cycle is the printed `15.0%`; and 189 is the least cycle count reaching
`97.0%` overall yield. -/
def RawResultSpec : Prop :=
  (∀ n0 η : ℝ, η ≠ 0 → ∀ k : ℕ,
      nitrogenAfterCycles n0 η (k + 1) = (1 - η) * (nitrogenAfterCycles n0 η k + n0 / 4))
  ∧ (∀ n0 η : ℝ, nitrogenAfterCycles n0 η 0 = 0)
  ∧ nitrogenAfter58Raw = (17 / 3 : ℝ) * (1 - (17 / 20)^58)
  ∧ ((5.66620 : ℝ) ≤ nitrogenAfter58Raw ∧ nitrogenAfter58Raw ≤ 5.66622)
  ∧ overallYieldAfterCycles feedTotalAmount cycleYield 1 = 0.150
  ∧ IsLeast cyclesReachingTarget 189

/-- Reported (final) spec: the raw nitrogen amount reported at the
problem-requested 4-decimal quantum is `5.6662` mol, and the number of cycles
reported as an exact integer is 189, the least count reaching `97.0%`. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum nitrogenAfter58Raw 5.6662 0.0001
  ∧ IsLeast cyclesReachingTarget 189

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("e48414562cbe204be5e6527edc621aea9d0778448b8baf834a86575c969de9df" : String)
      = "e48414562cbe204be5e6527edc621aea9d0778448b8baf834a86575c969de9df"
      ∧ RawResultSpec :=
  ⟨rfl, nitrogenAfterCycles_recurrence, nitrogenAfterCycles_zero, nitrogenAfter58Raw_eq,
    nitrogenAfter58Raw_bounds, overallYield_one, cycles_189_isLeast⟩

/-- Reported result certificate: binds the answer-blind reported-role payload
digest to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("b083d72a1740cef8354050ca9c205d461bd6eb3f40e6c0f41a36d88a96858610" : String)
      = "b083d72a1740cef8354050ca9c205d461bd6eb3f40e6c0f41a36d88a96858610"
      ∧ ReportedResultSpec :=
  ⟨rfl, nitrogenAfter58Raw_reports, cycles_189_isLeast⟩

end IChO2026Problems.Icho2026T7A3
