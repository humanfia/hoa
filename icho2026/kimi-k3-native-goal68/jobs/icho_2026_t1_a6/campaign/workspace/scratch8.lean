import Mathlib
def mNa : ℚ := 22990/1000
def mAl : ℚ := 26982/1000
def mF : ℚ := 18998/1000
def mCr : ℚ := 3*mNa + mAl + 6*mF
#eval 3*mNa/mCr
#eval (32845:ℚ)/100000
#eval ((32845:ℚ)/100000) < 3*mNa/mCr
#eval (3*mNa/mCr) < (32855:ℚ)/100000
#eval 3*mNa/mCr = (68970:ℚ)/209941
