import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, T7 (Nitrogen Fixation), subquestion 7.3 — target `icho_2026_t7_a3`

## Problem statement (official English, `T7_page-2.png`, box 7.3 and its preamble)

A model of a real reaction system includes recirculation of reagents. An open
system operates in a cyclic mode; each cycle consists of four steps:
1. A stoichiometric N₂ : H₂ = 1 : 3 mixture with a total amount of `n₀` mol is
   fed into the reactor after each cycle.
2. The reaction proceeds with a constant yield of `η = 0.150`.
3. Ammonia is separated by liquification.
4. Unreacted gases are returned into the reactor.

The cycle is repeated until the required overall yield is reached.

* (a) Calculate the amount of nitrogen present in the system after the 58th
  cycle (before the addition of the 59th portion of mixture), if `n₀ = 4` mol.
  Provide **4 decimal places**. (Hint: a formula for the sum of the terms of a
  geometric progression is needed.)
* (b) Calculate the number of cycles needed to increase the **overall** yield
  from 15.0 % to 97.0 %.

## Model proved here

Write `q = 1 − η = 0.85` (the recycled fraction). Each fresh portion brings
`n₀/4` mol of N₂. In every cycle, any N₂ present is multiplied by `q` twice:
once when the previous cycle's residue re-enters the reactor with the next
portion (steps 4 and 1), and once when the unreacted fraction of the cycle
survives reaction and NH₃ removal (steps 2 and 3). The portion fed before
cycle `j` has therefore been recycled `k − j` times at the moment "after cycle
k" and contributes `(n₀/4)·q·q^{2(k−j)}` mol of N₂. Summing over the `k`
portions fed so far,

    Aₖ = (n₀/4)·Σᵢ₌₀…ᵏ⁻¹ q^{2i}          (inventory in the reactor during cycle k)
    Nₖ = q·Aₖ = (n₀·q/4)·Σᵢ₌₀…ᵏ⁻¹ q^{2i} (inventory after cycle k)

and the geometric-series formula (the official hint) closes the sum:

    Nₖ = (n₀·q/4)·(1 − q^{2k})/(1 − q²)  =  0.85·(1 − 0.7225ᵏ)/0.2775   mol

for `n₀ = 4`, `q = 0.85`. Part (a): `N₅₈ = 3.06306304… mol`, which reports as
**3.0631 mol** at the requested 4-decimal-place quantum.

The overall yield after `n` cycles is `Y(n) = 1 − qⁿ` (after one cycle it equals
`0.150` — exactly the "from 15.0 %" baseline of part b). Part (b): `Y(n) ≥ 0.970`
first holds at **n = 22**, because `0.85²¹ = 0.032417… > 0.030` while
`0.85²² = 0.027554… < 0.030`.

No `sorry`/`admit` and no custom axioms are used anywhere below; `#print axioms`
at the end of the file lists only Lean's standard logical axioms.
-/

namespace IChO2026T7A3

open BigOperators

/-! ## Problem data (exact, as printed) -/

/-- Stoichiometric total feed per portion, `n₀ = 4` mol (problem datum). -/
noncomputable def n0 : ℝ := 4

/-- Constant per-cycle yield, `η = 0.150` (problem datum). -/
noncomputable def eta : ℝ := 0.150

/-- Recycled fraction of unreacted reagents, `q = 1 − η = 0.85`. -/
noncomputable def q : ℝ := 1 - eta

/-- Amount of N₂ in one fresh portion of the 1 : 3 stoichiometric mixture,
`n₀/4 = 1` mol. -/
noncomputable def nitrogenFeed : ℝ := n0 / 4

theorem q_val : q = (0.85 : ℝ) := by norm_num [q, eta]

theorem q_sq_val : q ^ 2 = (0.7225 : ℝ) := by norm_num [q, eta]

theorem q_pos : (0 : ℝ) < q := by rw [q_val]; norm_num

theorem q_lt_one : q < (1 : ℝ) := by rw [q_val]; norm_num

theorem nitrogenFeed_val : nitrogenFeed = 1 := by norm_num [nitrogenFeed, n0]

/-! ## Cyclic nitrogen inventory -/

/-- Nitrogen present **after cycle k** (after reaction and NH₃ removal, before
portion k + 1 is added): the sum of the surviving contributions of the `k`
portions fed so far, `(n₀/4)·q^{2i+1}` for a portion that has been recycled `i`
times.  This is the quantity part (a) asks about. -/
noncomputable def nitrogenAfter (k : ℕ) : ℝ :=
  q * nitrogenFeed * ∑ i ∈ Finset.range k, q ^ (2 * i)

/-- The system starts empty: before the first portion is fed there is no
nitrogen in the system, `N₀ = 0`. -/
theorem nitrogenAfter_zero : nitrogenAfter 0 = 0 := by
  simp [nitrogenAfter]

/-- Nitrogen inventory in the reactor **during cycle k** (after the k-th portion
has been added to the recycled unreacted gas, before reaction):
`Aₖ = Nₖ/q = (n₀/4)·Σᵢ₌₀…ᵏ⁻¹ q^{2i}`. -/
noncomputable def reactorNitrogen (k : ℕ) : ℝ :=
  nitrogenFeed * ∑ i ∈ Finset.range k, q ^ (2 * i)

/-- Steps 2–3 of the printed cycle: only the fraction `q` of the reactor
inventory survives reaction and ammonia separation. -/
theorem nitrogenAfter_eq_q_mul_reactor (k : ℕ) :
    nitrogenAfter k = q * reactorNitrogen k := by
  rw [nitrogenAfter, reactorNitrogen, mul_assoc]

/-- **Inventory recurrence** derived from the four printed cycle steps:
`Nₖ₊₁ = q²·Nₖ + q·(n₀/4)`. -/
theorem nitrogen_recurrence (k : ℕ) :
    nitrogenAfter (k + 1) = q ^ 2 * nitrogenAfter k + q * nitrogenFeed := by
  show q * nitrogenFeed * ∑ i ∈ Finset.range (k + 1), q ^ (2 * i)
      = q ^ 2 * (q * nitrogenFeed * ∑ i ∈ Finset.range k, q ^ (2 * i))
        + q * nitrogenFeed
  rw [Finset.sum_range_succ']
  simp only [mul_zero, pow_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 2 * (i + 1) = 2 * i + 2 from by ring, pow_add]
  ring
  · ring

/-- Specialised recurrence with the printed constants:
`Nₖ₊₁ = 0.7225·Nₖ + 0.85`. -/
theorem nitrogen_recurrence_0_85 (k : ℕ) :
    nitrogenAfter (k + 1) = 0.7225 * nitrogenAfter k + 0.85 := by
  rw [nitrogen_recurrence k, q_sq_val, q_val, nitrogenFeed_val]
  ring

/-! ## Geometric-series closed form (the official hint) -/

/-- The inventory as a geometric progression with ratio `q²`:
`Nₖ = (n₀·q/4)·Σᵢ₌₀…ᵏ⁻¹ (q²)ⁱ`. -/
theorem nitrogen_inventory_geo_sum (k : ℕ) :
    nitrogenAfter k = nitrogenFeed * q * ∑ i ∈ Finset.range k, (q ^ 2) ^ i := by
  show q * nitrogenFeed * ∑ i ∈ Finset.range k, q ^ (2 * i)
      = nitrogenFeed * q * ∑ i ∈ Finset.range k, (q ^ 2) ^ i
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← pow_mul]
  ring

/-- **Closed form of the geometric sum** (the hint of part a):
`Nₖ = (n₀·q/4)·(1 − q^{2k})/(1 − q²)` for every `k`. -/
theorem nitrogen_inventory_closedForm (k : ℕ) :
    nitrogenAfter k = nitrogenFeed * q * (1 - q ^ (2 * k)) / (1 - q ^ 2) := by
  have hne : q ^ 2 ≠ (1 : ℝ) := by
    intro h
    rw [q_sq_val] at h
    norm_num at h
  rw [nitrogen_inventory_geo_sum k, geom_sum_eq hne, pow_mul]
  have e : ((q ^ 2) ^ k - 1) / (q ^ 2 - 1) = (1 - (q ^ 2) ^ k) / (1 - q ^ 2) := by
    rw [show (q ^ 2) ^ k - 1 = - (1 - (q ^ 2) ^ k) from by ring,
        show q ^ 2 - 1 = - (1 - q ^ 2) from by ring, neg_div_neg_eq]
  rw [e, ← pow_mul, mul_div_assoc]

/-- With the problem's concrete constants:
`Nₖ = 0.85·(1 − 0.7225ᵏ)/0.2775` mol for every `k`. -/
theorem nitrogen_inventory_0_85 (k : ℕ) :
    nitrogenAfter k = 0.85 * (1 - (0.7225 : ℝ) ^ k) / 0.2775 := by
  have h : nitrogenAfter k
      = 1 * (0.85 : ℝ) * (1 - 0.85 ^ (2 * k)) / (1 - 0.85 ^ 2) := by
    rw [nitrogen_inventory_closedForm k, nitrogenFeed_val, q_val]
  rw [h]
  have e : (0.85 : ℝ) ^ (2 * k) = (0.7225 : ℝ) ^ k := by
    rw [show (0.7225 : ℝ) = (0.85 : ℝ) ^ 2 by norm_num, ← pow_mul]
  conv_lhs => rw [e]
  have hd : (1 - 0.85 ^ 2 : ℝ) = 0.2775 := by norm_num
  rw [hd]
  ring

/-- `0.85⁵⁸ = (17/20)⁵⁸` is tiny: it is exactly the rational number
`17⁵⁸/20⁵⁸ = 0.000080593…`.  The bound `(17/20)⁵⁸ < 806/10⁷` is discharged by
exact integer arithmetic: kernel-checked `decide` proves the raw integer
inequality `17⁵⁸·10⁷ < 806·20⁵⁸` (no floating point, no extra axioms), and
exact rational casts transfer it to ℝ. -/
theorem pow58_small : (0.85 : ℝ) ^ 58 < 0.0000806 := by
  have hint : (17 : ℤ)^58 * 10000000 < 806 * 20^58 := by decide
  have hq : (17/20 : ℚ)^58 < (806/10000000 : ℚ) := by
    have hpos : (0 : ℚ) < 10000000 := by norm_num
    have hbase : (0 : ℚ) < 20^58 := by positivity
    rw [div_pow, div_lt_div_iff₀ hbase hpos]
    exact_mod_cast hint
  have h0 : (0.85 : ℝ) = ↑((17/20 : ℚ)) := by norm_num
  have hd : (↑((806/10000000 : ℚ)) : ℝ) = 0.0000806 := by
    set_option maxRecDepth 4096 in norm_num
  rw [h0, ← Rat.cast_pow, ← hd]
  exact Rat.cast_lt.mpr hq

/-- The correction term `0.85¹¹⁶ = (17/20)¹¹⁶ = 0.000000006496…` is below
`10⁻⁸`, by the same route: kernel-checked `decide` proves the raw integer
inequality `17¹¹⁶·10⁸ < 20¹¹⁶`. -/
theorem pow116_small : (0.85 : ℝ) ^ 116 < 0.00000001 := by
  have hint : (17 : ℤ)^116 * 100000000 < 1 * (20 : ℤ)^116 := by decide
  have hq : (17/20 : ℚ)^116 < (1/100000000 : ℚ) := by
    have hpos : (0 : ℚ) < 100000000 := by norm_num
    have hbase : (0 : ℚ) < 20^116 := by positivity
    rw [div_pow, div_lt_div_iff₀ hbase hpos]
    exact_mod_cast hint
  have h0 : (0.85 : ℝ) = ↑((17/20 : ℚ)) := by norm_num
  have hd : (↑((1/100000000 : ℚ)) : ℝ) = 0.00000001 := by
    set_option maxRecDepth 4096 in norm_num
  rw [h0, ← Rat.cast_pow, ← hd]
  exact Rat.cast_lt.mpr hq

/-! ## Part (a): nitrogen after the 58th cycle -/

/-- The raw (exact, unrounded) amount of nitrogen after the 58th cycle:
`0.85·(1 − 0.7225⁵⁸)/0.2775 = 0.85·(1 − 0.85¹¹⁶)/0.2775 = 3.06306304…` mol. -/
noncomputable def nitrogen58Raw : ℝ := 0.85 * (1 - (0.7225 : ℝ) ^ 58) / 0.2775

theorem nitrogenAfter_58_eq_raw : nitrogenAfter 58 = nitrogen58Raw :=
  nitrogen_inventory_0_85 58

/-- `0.7225⁵⁸ = (289/400)⁵⁸ = 0.000006496…` is strictly below `0.0000806`:
`decide` proves the kernel-checked raw integer certificate
`289⁵⁸·10⁷ < 806·400⁵⁸` and exact rational casts transfer it to ℝ. -/
theorem pow58_7225_small : (0.7225 : ℝ) ^ 58 < 0.0000806 := by
  have hint : (289 : ℤ)^58 * 10000000 < 806 * 400^58 := by decide
  have hq : (289/400 : ℚ)^58 < (806/10000000 : ℚ) := by
    have hpos : (0 : ℚ) < 10000000 := by norm_num
    have hbase : (0 : ℚ) < 400^58 := by positivity
    rw [div_pow, div_lt_div_iff₀ hbase hpos]
    exact_mod_cast hint
  have h0 : (0.7225 : ℝ) = ↑((289/400 : ℚ)) := by norm_num
  have hd : (↑((806/10000000 : ℚ)) : ℝ) = 0.0000806 := by
    set_option maxRecDepth 4096 in norm_num
  rw [h0, ← Rat.cast_pow, ← hd]
  exact Rat.cast_lt.mpr hq

/-- The raw value lies strictly inside the half-quantum interval around `3.0631`
at the requested quantum `0.0001` (four decimal places):
`3.06305 ≤ N₅₈ < 3.06315`.  Both sides follow from the kernel-checked exact
bound `0 < 0.7225⁵⁸ < 0.0000806` on the tiny correction term by exact real
arithmetic (`nlinarith`); no floating point and no axioms beyond Lean's
standard logical ones. -/
theorem nitrogen58_in_report_interval :
    (3.0631 : ℝ) - 0.0001 / 2 ≤ nitrogen58Raw ∧ nitrogen58Raw < 3.0631 + 0.0001 / 2 := by
  have hlow : 0 < (0.7225 : ℝ) ^ 58 := by positivity
  have hup := pow58_7225_small
  rw [nitrogen58Raw]
  constructor
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 0.2775)]
    nlinarith
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 0.2775)]
    nlinarith

/-- **Part (a), answer-blind final reporting.** The exact nitrogen inventory
after the 58th cycle reports as **3.0631 mol** at the 4-decimal-place quantum
`0.0001` requested by the problem, under the project reporting contract
`IChO2026Chem.Reporting.ValidNumericSubmission` (raw = exact value,
reported = 3.0631, quantum = 0.0001, tie rule irrelevant since the raw value is
strictly inside the interval). -/
theorem nitrogen_after_58_cycles_reports_3_0631_mol :
    IChO2026Chem.Reporting.ValidNumericSubmission
      nitrogen58Raw
      { rawValue := nitrogen58Raw
        reportedValue := 3.0631
        reportingQuantum := 0.0001 } := by
  obtain ⟨hge, hlt⟩ := nitrogen58_in_report_interval
  have hnonneg : (0 : ℝ) ≤ nitrogen58Raw := by linarith
  refine ⟨rfl, by norm_num, ⟨30631, by norm_num⟩, ?_⟩
  rw [if_pos hnonneg]
  constructor
  · show (3.0631 : ℝ) - 0.0001 / 2 ≤ nitrogen58Raw
    exact hge
  · show nitrogen58Raw < (3.0631 : ℝ) + 0.0001 / 2
    exact hlt

/-! ## Part (b): cycles needed for a 97.0 % overall yield -/

/-- Overall yield after `n` cycles: the unconverted fraction of all reagent fed
is `qⁿ`, so `Y(n) = 1 − qⁿ`. In particular `Y(1) = 0.150` — exactly the
"from 15.0 %" baseline named in the question. -/
noncomputable def overallYield (n : ℕ) : ℝ := 1 - q ^ n

theorem overallYield_eq_one_sub_pow (n : ℕ) :
    overallYield n = 1 - (1 - eta) ^ n := rfl

/-- With the printed constants, `Y(n) = 1 − 0.85ⁿ`. -/
theorem overallYield_0_85 (n : ℕ) : overallYield n = 1 - (0.85 : ℝ) ^ n := by
  show 1 - q ^ n = 1 - (0.85 : ℝ) ^ n
  congr 2
  exact q_val

/-- 21 cycles are **not** enough: `Y(21) = 0.96758… < 0.970`. -/
theorem twenty_one_cycles_yield_below : overallYield 21 < 0.970 := by
  rw [overallYield_0_85]
  norm_num

/-- 22 cycles are enough: `Y(22) = 0.971996… ≥ 0.970`. -/
theorem twenty_two_cycles_yield_at_least : overallYield 22 ≥ (0.970 : ℝ) := by
  rw [overallYield_0_85]
  norm_num

/-- Since `0 < q < 1`, the unconverted fraction `qⁿ` is antitone in `n`, so
every cycle count of at most 21 remains below the 97.0 % threshold. -/
theorem yield_below_of_le_21 (n : ℕ) (hn : n ≤ 21) : overallYield n < 0.970 := by
  have h21 : (0.030 : ℝ) < q ^ 21 := by rw [q_val]; norm_num
  have hle : q ^ 21 ≤ q ^ n :=
    pow_le_pow_of_le_one q_pos.le q_lt_one.le hn
  rw [overallYield]
  linarith

/-- **Part (b) final.** 22 is the least number of cycles for which the overall
yield reaches 97.0 %: `Y(22) ≥ 0.970`, while every `n ≤ 21` gives `Y(n) < 0.970`. -/
theorem cycles_for_97_percent :
    IsLeast {n : ℕ | (0.970 : ℝ) ≤ overallYield n} 22 := by
  constructor
  · exact twenty_two_cycles_yield_at_least
  · rintro n hn
    by_contra hlt
    push Not at hlt
    have hn21 : n ≤ 21 := by omega
    have hb : overallYield n < 0.970 := yield_below_of_le_21 n hn21
    have hn2 : (0.970 : ℝ) ≤ overallYield n := hn
    linarith

/-- Since `0 < q < 1`, the overall yield is monotone in the number of cycles. -/
theorem overallYield_monotone : Monotone overallYield := by
  intro a b hab
  rw [overallYield, overallYield]
  have hle : q ^ b ≤ q ^ a :=
    pow_le_pow_of_le_one q_pos.le q_lt_one.le hab
  linarith

/-- The integer answer of part (b), characterized exactly: the overall yield
reaches at least 97.0 % **iff** at least 22 cycles have been run. -/
theorem cycles_needed_iff (n : ℕ) :
    (0.970 : ℝ) ≤ overallYield n ↔ 22 ≤ n := by
  constructor
  · intro hn
    by_contra hlt
    push Not at hlt
    have hn21 : n ≤ 21 := by omega
    have hb : overallYield n < 0.970 := yield_below_of_le_21 n hn21
    linarith
  · intro hn
    exact le_trans twenty_two_cycles_yield_at_least (overallYield_monotone hn)

end IChO2026T7A3

#print axioms IChO2026T7A3.nitrogen_recurrence
#print axioms IChO2026T7A3.nitrogen_recurrence_0_85
#print axioms IChO2026T7A3.nitrogen_inventory_geo_sum
#print axioms IChO2026T7A3.nitrogen_inventory_closedForm
#print axioms IChO2026T7A3.nitrogenAfter_58_eq_raw
#print axioms IChO2026T7A3.nitrogen58_in_report_interval
#print axioms IChO2026T7A3.nitrogen_after_58_cycles_reports_3_0631_mol
#print axioms IChO2026T7A3.twenty_one_cycles_yield_below
#print axioms IChO2026T7A3.twenty_two_cycles_yield_at_least
#print axioms IChO2026T7A3.cycles_for_97_percent
#print axioms IChO2026T7A3.cycles_needed_iff
