import ChemistryLib.Foundations.Concentration
import ChemistryLib.ReactionNetwork.PseudoHelmholtz

/-!
# Generalized relative entropy for open reaction networks

The generalized relative entropy used for ideal-dilute reaction networks is
the normalized pseudo-Helmholtz functional, with the reference state supplied
as its first argument.  At the theorem boundary, the concentration state may
have zero coordinates; the reference state remains strictly positive.

Source reference: RAO-ESPOSITO-2016, Sections III.E.2–III.E.3, equations
(70)–(79), <https://arxiv.org/pdf/1602.07257v3> (artifact SHA-256
`ed86193f16e3df2561a52fda55bfc63ba6086969494520122485193d9fce77d1`).
Sanitized contract: `research:rao_esposito_2016:nonequilibrium_free_energy`.
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

noncomputable section

/-- The generalized relative entropy of `z` from the reference state `zEq`. -/
abbrev generalizedRelativeEntropy {Species : Type} [Fintype Species]
    (z zEq : Species → ℝ) : ℝ :=
  ChemistryLib.ReactionNetwork.pseudoHelmholtz zEq z

/-- Generalized relative entropy is the pseudo-Helmholtz functional with its
reference-state argument first. -/
theorem generalizedRelativeEntropy_eq_pseudoHelmholtz
    {Species : Type} [Fintype Species] (z zEq : Species → ℝ) :
    generalizedRelativeEntropy z zEq =
      ChemistryLib.ReactionNetwork.pseudoHelmholtz zEq z :=
  rfl

private theorem generalizedRelativeEntropy_term_nonneg {a x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ x * (Real.log x - Real.log a - 1) + a := by
  rcases eq_or_lt_of_le hx with hzero | hx
  · subst x
    simpa using le_of_lt ha
  · have hratio : 0 < a / x := div_pos ha hx
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hx)] at hmul
    have hcancel : x * (a / x - 1) = a - x := by
      rw [mul_sub, mul_one, mul_div_cancel₀ a (ne_of_gt hx)]
    rw [hcancel] at hmul
    nlinarith

private theorem generalizedRelativeEntropy_term_pos {a x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≠ a) :
    0 < x * (Real.log x - Real.log a - 1) + a := by
  rcases eq_or_lt_of_le hx with hzero | hx
  · subst x
    simpa using ha
  · have hratio : 0 < a / x := div_pos ha hx
    have hratio_ne : a / x ≠ 1 := fun h ↦
      hxa ((div_eq_one_iff_eq (ne_of_gt hx)).mp h).symm
    have hlog := Real.log_lt_sub_one_of_pos hratio hratio_ne
    have hmul := mul_lt_mul_of_pos_left hlog hx
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hx)] at hmul
    have hcancel : x * (a / x - 1) = a - x := by
      rw [mul_sub, mul_one, mul_div_cancel₀ a (ne_of_gt hx)]
    rw [hcancel] at hmul
    nlinarith

/-- For a nonnegative concentration state and a strictly positive reference
state, generalized relative entropy vanishes exactly at the reference state. -/
theorem generalizedRelativeEntropy_eq_zero_iff
    {Species : Type} [Fintype Species] (z zEq : Species → ℝ)
    (hz : ∀ s, 0 ≤ z s) (hzEq : ∀ s, 0 < zEq s) :
    (generalizedRelativeEntropy z zEq = 0 ↔ z = zEq) := by
  constructor
  · intro hsum
    apply funext
    intro s
    unfold generalizedRelativeEntropy ChemistryLib.ReactionNetwork.pseudoHelmholtz at hsum
    have hs0 :
        z s * (Real.log (z s) - Real.log (zEq s) - 1) + zEq s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun t _ ↦ generalizedRelativeEntropy_term_nonneg (hzEq t) (hz t))).mp
          hsum s (Finset.mem_univ s)
    by_contra hne
    have hspos := generalizedRelativeEntropy_term_pos (hzEq s) (hz s) hne
    linarith
  · intro h
    subst z
    unfold generalizedRelativeEntropy ChemistryLib.ReactionNetwork.pseudoHelmholtz
    apply Finset.sum_eq_zero
    intro s _
    ring

/-- Generalized relative entropy is nonnegative for nonnegative concentration
states relative to a strictly positive reference state. -/
theorem generalizedRelativeEntropy_nonneg
    {Species : Type} [Fintype Species] (z zEq : Species → ℝ)
    (hz : ∀ s, 0 ≤ z s) (hzEq : ∀ s, 0 < zEq s) :
    0 ≤ generalizedRelativeEntropy z zEq := by
  unfold generalizedRelativeEntropy ChemistryLib.ReactionNetwork.pseudoHelmholtz
  exact Finset.sum_nonneg
    (fun s _ ↦ generalizedRelativeEntropy_term_nonneg (hzEq s) (hz s))

end

end ChemistryLib.Thermodynamics.OpenNetworks
