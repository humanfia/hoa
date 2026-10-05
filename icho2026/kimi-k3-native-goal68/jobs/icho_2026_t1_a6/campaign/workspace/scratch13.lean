import Mathlib

theorem bridge {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b := div_lt_div_iff₀ hb hd

-- true instance: 0.39155 < 54045/138022
example : (39155:ℚ)/100000 < (54045:ℚ)/138022 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (39155*138022 : ℕ) < 54045*100000)

-- upper: 54045/138022 < 0.39165
example : (54045:ℚ)/138022 < (39165:ℚ)/100000 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (54045*100000 : ℕ) < 39165*138022)

-- plateau x=22 fails: 294090/690420 < 5745/10000? per-gram residue 0.42596 < 0.5745 TRUE
example : (294090:ℚ)/690420 < (5745:ℚ)/1000 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (294090*1000 : ℕ) < 5745*690420)

-- plateau x=12 fails: 5755/1000 < 294090/510270 : i.e. 0.5755 < 0.576335 TRUE
example : (5755:ℚ)/1000 < (294090:ℚ)/510270 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (5755*510270 : ℕ) < 294090*1000)

-- plateau2 x=21 fails: 1505/1000 < 101961/672405 : 0.1505 < 0.151636 TRUE
example : (1505:ℚ)/1000 < (101961:ℚ)/672405 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (1505*672405 : ℕ) < 101961*1000)

-- cryolite Na window: 32845/100000 < 68970/209941 TRUE
example : (32845:ℚ)/100000 < (3*22990:ℚ)/209941 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (32845*209941 : ℕ) < 68970*100000)
example : (3*22990:ℚ)/209941 < (32855:ℚ)/100000 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (68970*100000 : ℕ) < 32855*209941)

-- cryolite Al window
example : (12845:ℚ)/100000 < (26982:ℚ)/209941 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (12845*209941 : ℕ) < 26982*100000)
example : (26982:ℚ)/209941 < (12855:ℚ)/100000 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (26982*100000 : ℕ) < 12855*209941)

-- AlF3.4H2O excluded: 46.18% well above window: 39165/100000 < 72060/156036 TRUE
example : (39165:ℚ)/100000 < (72060:ℚ)/156036 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (39165*156036 : ℕ) < 72060*100000)
-- AlF3.2H2O excluded: 30.02% below window: 36030/120007 < 39155/100000 TRUE
example : (36030:ℚ)/120007 < (39155:ℚ)/100000 := by
  rw [bridge (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (36030*100000 : ℕ) < 39155*120007)

-- G=C12O9 window: 49975/100000 ≤ 143991/288123 AND ≤ 49985/100000
theorem bridgeLe {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := div_le_div_iff₀ hb hd

example : (49975:ℚ)/100000 ≤ (143991:ℚ)/288123 := by
  rw [bridgeLe (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (49975*288123 : ℕ) ≤ 143991*100000)
example : (143991:ℚ)/288123 ≤ (49985:ℚ)/100000 := by
  rw [bridgeLe (by norm_num) (by norm_num)]
  exact_mod_cast (by norm_num1 : (143991*100000 : ℕ) ≤ 49985*288123)
