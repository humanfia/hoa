import Mathlib
def mH : ℚ := 1008/1000
def mO : ℚ := 15999/1000
def mAl : ℚ := 26982/1000
def mF : ℚ := 18998/1000
def mCr : ℚ := 3*(22990/1000) + mAl + 6*mF
def mH2O : ℚ := 2*mH + mO
#eval mAl/mCr
#eval 3*mH2O/(mAl+3*mF+3*mH2O)
