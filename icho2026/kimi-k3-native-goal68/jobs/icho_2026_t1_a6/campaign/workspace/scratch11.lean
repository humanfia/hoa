import Mathlib

/-- Bridge: a/b < c/d for naturals is a pure Nat comparison. -/
theorem rat_div_lt_div {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d) :
    (a : ℚ) / b < (c : ℚ) / d ↔ a * d < c * b := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)]
  norm_cast

/-- Bridge, non-strict. -/
theorem rat_div_le_div {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d) :
    (a : ℚ) / b ≤ (c : ℚ) / d ↔ a * d ≤ c * b := by
  rw [div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)]
  norm_cast

-- the parser builds 39165/100000 as HDiv.hDiv on ℚ-numerals; the bridge wants casts:
example : (32845 : ℚ)/100000 < 3 * (22990:ℚ)/1000 / (3*(22990:ℚ)/1000 + 26982/1000 + 6*(18998:ℚ)/1000) := by
  have e : 3 * (22990:ℚ)/1000 / (3*(22990:ℚ)/1000 + 26982/1000 + 6*(18998:ℚ)/1000)
         = (2299:ℚ)/6998 := by native_decide
  sorry

-- Simplest robust route: state final theorems as equalities to reduced fractions
-- proved by native_decide? NO — native_decide adds trust axioms. Must use decide (kernel).
-- Kernel decide failed on Rat.blt (Bool match). BUT Rat equality + comparisons:
example : (2299:ℚ)/6998 = 2299/6998 := by decide  -- trivial check
example : ((32845:ℕ):ℚ)/((100000:ℕ)) < 3 * (22990:ℚ)/1000 / (3*(22990:ℚ)/1000 + 26982/1000 + 6*(18998:ℚ)/1000) := by
  have h2 : 3 * (22990:ℚ)/1000 / (3*(22990:ℚ)/1000 + 26982/1000 + 6*(18998:ℚ)/1000)
          = ((2299:ℕ):ℚ)/((6998:ℕ)) := by
    rw [div_eq_iff (by norm_num), div_eq_iff (by norm_num)]
    norm_num
  rw [h2, rat_div_lt_div (by norm_num) (by norm_num)]
  norm_num1
