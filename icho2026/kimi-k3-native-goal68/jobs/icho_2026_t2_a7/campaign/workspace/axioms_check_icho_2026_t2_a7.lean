-- Scratch axiom-inspection driver for target icho_2026_t2_a7.
-- Run with:  lake env lean axioms_check_icho_2026_t2_a7.lean
import Mathlib
import IChO2026Problems.problem_icho_2026_t2_a7

open IChO2026T2A7

#print axioms optionSixShape_fRepr
#print axioms answer_is_bottom_right
#print axioms P1_fRepr
#print axioms P2_fRepr
#print axioms P3_fRepr
#print axioms P4_fRepr
#print axioms P5_fRepr
#print axioms P6_fRepr
#print axioms positive_violates_P1
#print axioms sine_fails_P1
#print axioms growing_sine_fails_P1
#print axioms constant_rate_fails_P3
#print axioms negative_slope_fails_P3
#print axioms monotone_fails_P5
#print axioms optionThree_shape_fails_P5
