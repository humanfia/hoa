import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A3: cyclic ammonia synthesis with reagent recirculation

The problem states that every fresh portion has total amount `4 mol` and the
stoichiometric ratio `N₂ : H₂ = 1 : 3`.  Thus every portion contains `1 mol`
of `N₂`.  A single-cycle yield of `0.150 = 3/20` leaves the fraction `17/20`.

`nitrogenAfter k` is the amount of molecular nitrogen, in moles, after cycle
`k` and before the next fresh portion is added.  It is written as a geometric
sum so that each summand records one fresh portion and all of its subsequent
passes through the reactor.
-/

namespace IChO2026Problems.T7A3

open Finset
open IChO2026Chem.Reporting

noncomputable section

/-! ## Problem data -/

/-- Total amount, in moles, in each fresh stoichiometric gas portion. -/
def freshMixtureAmount : ℝ := 4

/-- The nitrogen fraction in a `N₂ : H₂ = 1 : 3` stoichiometric mixture. -/
def nitrogenMoleFraction : ℝ := 1 / 4

/-- Nitrogen introduced by each fresh portion, in moles. -/
def freshNitrogen : ℝ := freshMixtureAmount * nitrogenMoleFraction

/-- The stipulated per-cycle reaction yield `0.150`. -/
def singleCycleYield : ℝ := 3 / 20

/-- The fraction of the reactor's nitrogen left after one cycle. -/
def retainedFraction : ℝ := 1 - singleCycleYield

theorem fresh_nitrogen_eq_one : freshNitrogen = 1 := by
  norm_num [freshNitrogen, freshMixtureAmount, nitrogenMoleFraction]

theorem retained_fraction_eq : retainedFraction = 17 / 20 := by
  norm_num [retainedFraction, singleCycleYield]

/-! ## Nitrogen inventory -/

/-- Molecular nitrogen remaining after `cycles` completed cycles, before the
next portion is added.  The portion added in cycle `j` has passed through the
reactor `cycles - j + 1` times, which produces the displayed geometric sum. -/
def nitrogenAfter (cycles : ℕ) : ℝ :=
  ∑ i ∈ range cycles, (17 / 20 : ℝ) ^ (i + 1)

theorem nitrogenAfter_zero : nitrogenAfter 0 = 0 := by
  simp [nitrogenAfter]

/-- A useful alternate form of the geometric sum. -/
theorem nitrogenAfter_eq_mul_geom (cycles : ℕ) :
    nitrogenAfter cycles =
      (17 / 20 : ℝ) * ∑ i ∈ range cycles, (17 / 20 : ℝ) ^ i := by
  simp_rw [nitrogenAfter, pow_succ']
  rw [← mul_sum]

/-- The geometric-sum model obeys the cycle balance dictated by the source:
add the fresh `1 mol` of nitrogen and retain `17/20` after reaction. -/
theorem nitrogenAfter_recurrence (cycles : ℕ) :
    nitrogenAfter (cycles + 1) =
      (17 / 20 : ℝ) * (nitrogenAfter cycles + 1) := by
  rw [nitrogenAfter_eq_mul_geom, nitrogenAfter_eq_mul_geom, geom_sum_succ]

/-- The same balance stated entirely in terms of the named problem data. -/
theorem nitrogenAfter_source_balance (cycles : ℕ) :
    nitrogenAfter (cycles + 1) =
      retainedFraction * (nitrogenAfter cycles + freshNitrogen) := by
  rw [retained_fraction_eq, fresh_nitrogen_eq_one]
  exact nitrogenAfter_recurrence cycles

/-- Closed form of the nitrogen inventory, derived from the geometric sum. -/
theorem nitrogenAfter_closedForm (cycles : ℕ) :
    nitrogenAfter cycles =
      (17 / 3 : ℝ) * (1 - (17 / 20 : ℝ) ^ cycles) := by
  rw [nitrogenAfter_eq_mul_geom, geom_sum_eq]
  · ring
  · norm_num

/-! ## Part (a): exact value and four-decimal reporting -/

/-- The answer submission keeps the exact raw result separate from its
four-decimal-place display. -/
def nitrogen58Submission : NumericSubmission where
  rawValue := nitrogenAfter 58
  reportedValue := 56662 / 10000
  reportingQuantum := 1 / 10000

/-- Exact half-quantum bounds proving that `5.6662` is the required rounding
of the unrounded geometric-series result. -/
theorem nitrogen_after_58_rounding_bounds :
    (56662 / 10000 : ℝ) - (1 / 10000 : ℝ) / 2 ≤ nitrogenAfter 58 ∧
      nitrogenAfter 58 < (56662 / 10000 : ℝ) + (1 / 10000 : ℝ) / 2 := by
  rw [nitrogenAfter_closedForm]
  norm_num

/-- Requested output (a): `5.6662 mol` is a valid four-decimal report of the
exact amount of nitrogen after cycle 58. -/
theorem nitrogen_after_58_cycles :
    ValidNumericSubmission (nitrogenAfter 58) nitrogen58Submission := by
  refine ⟨rfl, ?_⟩
  refine ⟨by norm_num [nitrogen58Submission], ?_, ?_⟩
  · refine ⟨56662, ?_⟩
    norm_num [nitrogen58Submission]
  · have bounds := nitrogen_after_58_rounding_bounds
    have hnonneg : 0 ≤ nitrogenAfter 58 := by
      norm_num at bounds ⊢
      linarith [bounds.1]
    simp only [nitrogen58Submission]
    rw [if_pos hnonneg]
    exact bounds

/-! ## Part (b): cumulative overall yield and its first 97% cycle -/

/-- Total molecular nitrogen supplied by all fresh portions through the given
number of cycles. -/
def cumulativeFreshNitrogen (cycles : ℕ) : ℝ :=
  (cycles : ℝ) * freshNitrogen

/-- Total molecular nitrogen converted to ammonia through the given number of
cycles, by material balance. -/
def convertedNitrogen (cycles : ℕ) : ℝ :=
  cumulativeFreshNitrogen cycles - nitrogenAfter cycles

theorem cumulativeFreshNitrogen_eq (cycles : ℕ) :
    cumulativeFreshNitrogen cycles = (cycles : ℝ) := by
  rw [cumulativeFreshNitrogen, fresh_nitrogen_eq_one, mul_one]

/-- Overall nitrogen conversion after `cycles` cycles.  For a positive number
of cycles, the cumulative fresh nitrogen feed is `cycles` moles, the remaining
inventory is `nitrogenAfter cycles`, and their ratio gives the unconverted
fraction.  The zero-cycle value merely makes the function total. -/
def overallYield (cycles : ℕ) : ℝ :=
  if cycles = 0 then 0
  else 1 - nitrogenAfter cycles / (cycles : ℝ)

theorem overallYield_of_pos {cycles : ℕ} (hcycles : 0 < cycles) :
    overallYield cycles = 1 - nitrogenAfter cycles / (cycles : ℝ) := by
  simp [overallYield, Nat.ne_of_gt hcycles]

/-- For every positive cycle count, the simplified expression used in
`overallYield` is exactly converted nitrogen divided by cumulative feed. -/
theorem overallYield_eq_conversion_ratio {cycles : ℕ} (hcycles : 0 < cycles) :
    overallYield cycles =
      convertedNitrogen cycles / cumulativeFreshNitrogen cycles := by
  rw [overallYield_of_pos hcycles, convertedNitrogen,
    cumulativeFreshNitrogen_eq]
  have hne : (cycles : ℝ) ≠ 0 := by positivity
  field_simp

/-- The source's stated 15.0% is recovered at the first cycle. -/
theorem overallYield_one : overallYield 1 = 15 / 100 := by
  norm_num [overallYield, nitrogenAfter]

/-- The residual nitrogen per mole of cumulative fresh nitrogen decreases
from one positive cycle to the next. -/
theorem residual_average_succ_le (cycles : ℕ) (hcycles : 0 < cycles) :
    nitrogenAfter (cycles + 1) / ((cycles + 1 : ℕ) : ℝ) ≤
      nitrogenAfter cycles / (cycles : ℝ) := by
  have hterm :
      (cycles : ℝ) * (17 / 20 : ℝ) ^ (cycles + 1) ≤ nitrogenAfter cycles := by
    calc
      (cycles : ℝ) * (17 / 20 : ℝ) ^ (cycles + 1) =
          ∑ _i ∈ range cycles, (17 / 20 : ℝ) ^ (cycles + 1) := by simp
      _ ≤ ∑ i ∈ range cycles, (17 / 20 : ℝ) ^ (i + 1) := by
        refine sum_le_sum fun i hi ↦ ?_
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.succ_le_succ (Nat.le_of_lt (mem_range.mp hi)))
      _ = nitrogenAfter cycles := rfl
  rw [nitrogenAfter] at hterm
  simp only [nitrogenAfter, sum_range_succ]
  have hcyclesR : (0 : ℝ) < cycles := by exact_mod_cast hcycles
  have hsuccR : (0 : ℝ) < (cycles + 1 : ℕ) := by positivity
  apply (div_le_div_iff₀ hsuccR hcyclesR).2
  push_cast
  nlinarith

/-- Consequently the overall cumulative yield is monotone over positive cycle
counts. -/
theorem overallYield_mono_of_pos {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n) :
    overallYield m ≤ overallYield n := by
  have havg :
      nitrogenAfter n / (n : ℝ) ≤ nitrogenAfter m / (m : ℝ) := by
    cases m with
    | zero => omega
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            have hantitone : Antitone (fun k : ℕ ↦
                nitrogenAfter (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
              apply antitone_nat_of_succ_le
              intro k
              simpa [Nat.add_assoc] using
                residual_average_succ_le (k + 1) (by omega)
            exact hantitone (Nat.succ_le_succ_iff.mp hmn)
  rw [overallYield_of_pos hm, overallYield_of_pos hn]
  linarith

/-- Cycle 188 is still below the stipulated 97.0% target. -/
theorem overallYield_188_lt : overallYield 188 < 97 / 100 := by
  rw [overallYield_of_pos (by norm_num), nitrogenAfter_closedForm]
  norm_num

/-- Cycle 189 reaches the stipulated 97.0% target. -/
theorem overallYield_189_ge : 97 / 100 ≤ overallYield 189 := by
  rw [overallYield_of_pos (by norm_num), nitrogenAfter_closedForm]
  norm_num

/-- A cycle count is the requested answer exactly when it reaches 97.0% and
no earlier positive cycle does. -/
def IsFirstCycleAt97 (cycles : ℕ) : Prop :=
  97 / 100 ≤ overallYield cycles ∧
    ∀ earlier, 0 < earlier → earlier < cycles → ¬ 97 / 100 ≤ overallYield earlier

/-- Requested output (b): 189 is the least positive cycle count at which the
overall cumulative yield reaches 97.0%. -/
theorem cycles_for_97_percent : IsFirstCycleAt97 189 := by
  refine ⟨overallYield_189_ge, ?_⟩
  intro earlier hearlier hlt hreach
  have hle : earlier ≤ 188 := by omega
  have hmono := overallYield_mono_of_pos hearlier (by norm_num : 0 < 188) hle
  linarith [overallYield_188_lt]

#print axioms nitrogen_after_58_cycles
#print axioms cycles_for_97_percent

end
end IChO2026Problems.T7A3
