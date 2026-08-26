import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The normalized pseudo-Helmholtz functional

For a positive reference concentration `xStar`, this module defines the
reference-normalized pseudo-Helmholtz functional.  The summand includes
`+ xStar s`, so its minimum value is zero rather than an unspecified additive
constant.

Source reference: YU-CRACIUN-2018, Section 2.1, Theorem 2.3 and equation (8),
<https://arxiv.org/pdf/1805.10371v1>.
-/

namespace ChemistryLib.ReactionNetwork

noncomputable section

/-- The normalized pseudo-Helmholtz functional relative to `xStar`. -/
def pseudoHelmholtz {Species : Type} [Fintype Species]
    (xStar x : Species → ℝ) : ℝ :=
  ∑ s, (x s * (Real.log (x s) - Real.log (xStar s) - 1) + xStar s)

private theorem pseudoHelmholtz_term_nonneg {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    0 ≤ x * (Real.log x - Real.log a - 1) + a := by
  have hratio : 0 < a / x := div_pos ha hx
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hx)] at hmul
  have hcancel : x * (a / x - 1) = a - x := by
    rw [mul_sub, mul_one, mul_div_cancel₀ a (ne_of_gt hx)]
  rw [hcancel] at hmul
  nlinarith

private theorem pseudoHelmholtz_term_pos {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    0 < x * (Real.log x - Real.log a - 1) + a := by
  have hratio : 0 < a / x := div_pos ha hx
  have hratio_ne : a / x ≠ 1 := fun h =>
    hxa ((div_eq_one_iff_eq (ne_of_gt hx)).mp h).symm
  have hlog := Real.log_lt_sub_one_of_pos hratio hratio_ne
  have hmul := mul_lt_mul_of_pos_left hlog hx
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hx)] at hmul
  have hcancel : x * (a / x - 1) = a - x := by
    rw [mul_sub, mul_one, mul_div_cancel₀ a (ne_of_gt hx)]
  rw [hcancel] at hmul
  nlinarith

/-- On positive concentration vectors, the normalized functional vanishes
exactly at its reference vector. -/
theorem pseudoHelmholtz_eq_zero_iff {Species : Type} [Fintype Species]
    (xStar x : Species → ℝ) (hxStar : ∀ s, 0 < xStar s)
    (hx : ∀ s, 0 < x s) :
    (pseudoHelmholtz xStar x = 0 ↔ x = xStar) := by
  constructor
  · intro hsum
    apply funext
    intro s
    unfold pseudoHelmholtz at hsum
    have hs0 :
        x s * (Real.log (x s) - Real.log (xStar s) - 1) + xStar s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun t _ => pseudoHelmholtz_term_nonneg (hxStar t) (hx t))).mp hsum s
          (Finset.mem_univ s)
    by_contra hne
    have hspos := pseudoHelmholtz_term_pos (hxStar s) (hx s) hne
    linarith
  · intro h
    subst x
    unfold pseudoHelmholtz
    apply Finset.sum_eq_zero
    intro s _
    ring

/-- The pseudo-Helmholtz functional is the normalized finite sum from its
definition. -/
theorem pseudoHelmholtz_formula {Species : Type} [Fintype Species]
    (xStar x : Species → ℝ) :
    pseudoHelmholtz xStar x =
      ∑ s, (x s * (Real.log (x s) - Real.log (xStar s) - 1) + xStar s) := by
  rfl

/-- The normalized pseudo-Helmholtz functional is nonnegative on positive
concentration vectors. -/
theorem pseudoHelmholtz_nonneg {Species : Type} [Fintype Species]
    (xStar x : Species → ℝ) (hxStar : ∀ s, 0 < xStar s)
    (hx : ∀ s, 0 < x s) :
    0 ≤ pseudoHelmholtz xStar x := by
  unfold pseudoHelmholtz
  exact Finset.sum_nonneg
    (fun s _ => pseudoHelmholtz_term_nonneg (hxStar s) (hx s))

end

end ChemistryLib.ReactionNetwork
