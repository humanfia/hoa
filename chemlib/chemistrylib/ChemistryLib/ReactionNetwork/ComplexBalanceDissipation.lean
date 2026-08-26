import ChemistryLib.ReactionNetwork.Balance
import ChemistryLib.ReactionNetwork.Basic
import ChemistryLib.ReactionNetwork.MassAction
import ChemistryLib.ReactionNetwork.PseudoHelmholtz

/-!
# Complex-balance dissipation

This module records the edgewise entropy-production expression for a
complex-balanced mass-action system and the corresponding orbital derivative
of the normalized pseudo-Helmholtz functional.

Source reference: YU-CRACIUN-2018, Section 2.1, Theorem 2.3 and equation (8),
<https://arxiv.org/pdf/1805.10371v1>.  The source artifact has SHA-256
`087c3303f891486c8056bd60bd540dc85bf1b862999249906199e8b57a6dc671`.
Only the algebraic dissipation and nonpositivity statements are represented
here; no global-attraction conclusion is asserted.
-/

namespace ChemistryLib.ReactionNetwork

noncomputable section

/-! ## Project-local Mathlib supplement — Positive entropy production -/

private theorem complex_monomial_pos
    {Species : Type} (y : ChemistryLib.Complex Species)
    (x : Species → ℝ) (hx : ∀ s, 0 < x s) :
    0 < ChemistryLib.Complex.monomial y x := by
  unfold ChemistryLib.Complex.monomial
  apply Finset.prod_pos
  intro s hs
  exact pow_pos (hx s) _

private theorem entropyProduction_nonneg {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a * Real.log (a / b) - a + b := by
  have hratio : 0 < b / a := div_pos hb ha
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hmul
  have hcancel : a * (b / a - 1) = b - a := by
    rw [mul_sub, mul_one, mul_div_cancel₀ b (ne_of_gt ha)]
  rw [hcancel] at hmul
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  nlinarith

private theorem entropyProduction_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < a * Real.log (a / b) - a + b := by
  have hratio : 0 < b / a := div_pos hb ha
  have hratio_ne : b / a ≠ 1 := fun h =>
    hab ((div_eq_one_iff_eq (ne_of_gt ha)).mp h).symm
  have hlog := Real.log_lt_sub_one_of_pos hratio hratio_ne
  have hmul := mul_lt_mul_of_pos_left hlog ha
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hmul
  have hcancel : a * (b / a - 1) = b - a := by
    rw [mul_sub, mul_one, mul_div_cancel₀ b (ne_of_gt ha)]
  rw [hcancel] at hmul
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  nlinarith

/-- The monomial activity of a complex relative to a reference state. -/
def complexActivityRatio
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId) : ℝ :=
  N.complexMonomialVector x c / N.complexMonomialVector xStar c

/-- The complex activity ratio is the quotient of the two complex monomials. -/
theorem complexActivityRatio_apply
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId) :
    N.complexActivityRatio xStar x c =
      N.complexMonomialVector x c / N.complexMonomialVector xStar c := by
  rfl

private theorem complexActivityRatio_pos
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    0 < N.complexActivityRatio xStar x c := by
  unfold complexActivityRatio complexMonomialVector
  exact div_pos
    (complex_monomial_pos (N.complex c) x hx)
    (complex_monomial_pos (N.complex c) xStar hxStar)

private theorem log_complex_monomial
    {Species : Type} [Fintype Species]
    (y : ChemistryLib.Complex Species)
    (x : Species → ℝ) (hx : ∀ s, 0 < x s) :
    Real.log (ChemistryLib.Complex.monomial y x) =
      ∑ s, (y s : ℝ) * Real.log (x s) := by
  classical
  unfold ChemistryLib.Complex.monomial
  change Real.log (y.support.prod fun s => x s ^ y s) =
    ∑ s, (y s : ℝ) * Real.log (x s)
  rw [Real.log_prod]
  · simp_rw [Real.log_pow]
    apply Finset.sum_subset (Finset.subset_univ y.support)
    intro s hs hnot
    have hy : y s = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hy]
  · intro s hs
    exact pow_ne_zero _ (ne_of_gt (hx s))

private theorem log_complexActivityRatio
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (c : ComplexId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    Real.log (N.complexActivityRatio xStar x c) =
      ∑ s, (N.complex c s : ℝ) *
        (Real.log (x s) - Real.log (xStar s)) := by
  unfold complexActivityRatio complexMonomialVector
  rw [
    Real.log_div
      (ne_of_gt (complex_monomial_pos (N.complex c) x hx))
      (ne_of_gt (complex_monomial_pos (N.complex c) xStar hxStar)),
    log_complex_monomial (N.complex c) x hx,
    log_complex_monomial (N.complex c) xStar hxStar]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem log_pairing_reactionVector
    {Species ComplexId ReactionId : Type} [Fintype Species]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (xStar x : Species → ℝ) (r : ReactionId)
    (hxStar : ∀ s, 0 < xStar s) (hx : ∀ s, 0 < x s) :
    ∑ s, (Real.log (x s) - Real.log (xStar s)) *
        N.reactionVector r s =
      Real.log
        (N.complexActivityRatio xStar x (N.target r) /
          N.complexActivityRatio xStar x (N.source r)) := by
  rw [Real.log_div
    (ne_of_gt (N.complexActivityRatio_pos xStar x (N.target r) hxStar hx))
    (ne_of_gt (N.complexActivityRatio_pos xStar x (N.source r) hxStar hx)),
    N.log_complexActivityRatio xStar x (N.target r) hxStar hx,
    N.log_complexActivityRatio xStar x (N.source r) hxStar hx]
  unfold reactionVector product reactant
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro s hs <;>
    ring

private theorem massActionFlux_eq_reference_mul_activityRatio
    {Species ComplexId ReactionId : Type}
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) (r : ReactionId)
    (hxStar : ∀ s, 0 < xStar s) :
    N.massActionFlux k x r =
      N.massActionFlux k xStar r *
        N.complexActivityRatio xStar x (N.source r) := by
  unfold massActionFlux complexActivityRatio complexMonomialVector reactant
  field_simp [ne_of_gt (complex_monomial_pos (N.complex (N.source r))
    xStar hxStar)]

private theorem complexBalanced_sum_target_eq_sum_source
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [Fintype ReactionId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (A : ComplexId → ℝ) :
    ∑ r, N.massActionFlux k xStar r * A (N.target r) =
      ∑ r, N.massActionFlux k xStar r * A (N.source r) := by
  calc
    ∑ r, N.massActionFlux k xStar r * A (N.target r) =
        ∑ c, A c * ∑ r,
          if N.target r = c then N.massActionFlux k xStar r else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      simp [mul_comm]
    _ = ∑ c, A c * ∑ r,
          if N.source r = c then N.massActionFlux k xStar r else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hbal.2.2 c]
    _ = ∑ r, N.massActionFlux k xStar r * A (N.source r) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      simp [mul_comm]

/-- The edgewise relative-entropy dissipation at a reference state. -/
def complexBalanceDissipation
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) : ℝ :=
  ∑ r, N.massActionFlux k xStar r *
    (N.complexActivityRatio xStar x (N.source r) *
        Real.log
          (N.complexActivityRatio xStar x (N.source r) /
            N.complexActivityRatio xStar x (N.target r)) -
      N.complexActivityRatio xStar x (N.source r) +
      N.complexActivityRatio xStar x (N.target r))

/-- Under complex balance, dissipation vanishes exactly when each reaction
has equal source and target complex activities. -/
theorem complexBalanceDissipation_eq_zero_iff_activityRatio_source_eq_target
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    (N.complexBalanceDissipation k xStar x = 0 ↔
      ∀ r, N.complexActivityRatio xStar x (N.source r) =
        N.complexActivityRatio xStar x (N.target r)) := by
  have hxStar := hbal.2.1
  have hflux : ∀ r, 0 < N.massActionFlux k xStar r := by
    intro r
    unfold massActionFlux
    exact mul_pos (hbal.1 r)
      (complex_monomial_pos (N.reactant r) xStar hxStar)
  have hsource : ∀ r,
      0 < N.complexActivityRatio xStar x (N.source r) := by
    intro r
    exact N.complexActivityRatio_pos xStar x (N.source r) hxStar hx
  have htarget : ∀ r,
      0 < N.complexActivityRatio xStar x (N.target r) := by
    intro r
    exact N.complexActivityRatio_pos xStar x (N.target r) hxStar hx
  unfold complexBalanceDissipation
  constructor
  · intro hsum r
    have hnonneg : ∀ q ∈ (Finset.univ : Finset ReactionId),
        0 ≤ N.massActionFlux k xStar q *
          (N.complexActivityRatio xStar x (N.source q) *
              Real.log
                (N.complexActivityRatio xStar x (N.source q) /
                  N.complexActivityRatio xStar x (N.target q)) -
            N.complexActivityRatio xStar x (N.source q) +
            N.complexActivityRatio xStar x (N.target q)) := by
      intro q hq
      exact mul_nonneg (le_of_lt (hflux q))
        (entropyProduction_nonneg (hsource q) (htarget q))
    have hrzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum r
      (Finset.mem_univ r)
    by_contra hne
    have hrpos := mul_pos (hflux r)
      (entropyProduction_pos (hsource r) (htarget r) hne)
    linarith
  · intro h
    apply Finset.sum_eq_zero
    intro r hr
    rw [h r, div_self (ne_of_gt (htarget r)), Real.log_one]
    ring

/-- Expansion of complex-balance dissipation as a sum over reactions. -/
theorem complexBalanceDissipation_formula
    {Species ComplexId ReactionId : Type} [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) :
    N.complexBalanceDissipation k xStar x =
      ∑ r, (N.massActionFlux k xStar r *
        (N.complexActivityRatio xStar x (N.source r) *
            Real.log
              (N.complexActivityRatio xStar x (N.source r) /
                N.complexActivityRatio xStar x (N.target r)) -
          N.complexActivityRatio xStar x (N.source r) +
          N.complexActivityRatio xStar x (N.target r))) := by
  rfl

/-- Complex-balance dissipation is nonnegative on positive states. -/
theorem complexBalanceDissipation_nonneg
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    0 ≤ N.complexBalanceDissipation k xStar x := by
  have hxStar := hbal.2.1
  have hflux : ∀ r, 0 < N.massActionFlux k xStar r := by
    intro r
    unfold massActionFlux
    exact mul_pos (hbal.1 r)
      (complex_monomial_pos (N.reactant r) xStar hxStar)
  have hsource : ∀ r,
      0 < N.complexActivityRatio xStar x (N.source r) :=
    fun r => N.complexActivityRatio_pos xStar x (N.source r) hxStar hx
  have htarget : ∀ r,
      0 < N.complexActivityRatio xStar x (N.target r) :=
    fun r => N.complexActivityRatio_pos xStar x (N.target r) hxStar hx
  unfold complexBalanceDissipation
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (le_of_lt (hflux r))
    (entropyProduction_nonneg (hsource r) (htarget r))

/-- The directional derivative of the pseudo-Helmholtz functional along the
mass-action vector field. -/
def pseudoHelmholtzOrbitalDerivative
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) : ℝ :=
  ∑ s, (Real.log (x s) - Real.log (xStar s)) *
    N.massActionVectorField k x s

/-- Expansion of the pseudo-Helmholtz orbital derivative by species. -/
theorem pseudoHelmholtzOrbitalDerivative_formula
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ReactionId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ) :
    N.pseudoHelmholtzOrbitalDerivative k xStar x =
      ∑ s, ((Real.log (x s) - Real.log (xStar s)) *
        N.massActionVectorField k x s) := by
  rfl

/-- At a complex-balanced reference state, the pseudo-Helmholtz orbital
derivative is the negative complex-balance dissipation. -/
theorem pseudoHelmholtz_derivative_eq_neg_dissipation
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    N.pseudoHelmholtzOrbitalDerivative k xStar x =
      -N.complexBalanceDissipation k xStar x := by
  have hxStar := hbal.2.1
  have hsource : ∀ r,
      0 < N.complexActivityRatio xStar x (N.source r) :=
    fun r => N.complexActivityRatio_pos xStar x (N.source r) hxStar hx
  have htarget : ∀ r,
      0 < N.complexActivityRatio xStar x (N.target r) :=
    fun r => N.complexActivityRatio_pos xStar x (N.target r) hxStar hx
  have horbit :
      N.pseudoHelmholtzOrbitalDerivative k xStar x =
        ∑ r, N.massActionFlux k x r *
          Real.log
            (N.complexActivityRatio xStar x (N.target r) /
              N.complexActivityRatio xStar x (N.source r)) := by
    unfold pseudoHelmholtzOrbitalDerivative massActionVectorField
    simp_rw [stoichiometricMatrix_mulVec_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [N.log_pairing_reactionVector xStar x r hxStar hx]
    ring
  have hbalance :
      ∑ r, N.massActionFlux k xStar r *
          N.complexActivityRatio xStar x (N.target r) =
        ∑ r, N.massActionFlux k xStar r *
          N.complexActivityRatio xStar x (N.source r) :=
    complexBalanced_sum_target_eq_sum_source N k xStar hbal
      (N.complexActivityRatio xStar x)
  have hdiss :
      N.complexBalanceDissipation k xStar x =
        ∑ r, N.massActionFlux k xStar r *
          N.complexActivityRatio xStar x (N.source r) *
          Real.log
            (N.complexActivityRatio xStar x (N.source r) /
              N.complexActivityRatio xStar x (N.target r)) := by
    unfold complexBalanceDissipation
    calc
      ∑ r, N.massActionFlux k xStar r *
          (N.complexActivityRatio xStar x (N.source r) *
              Real.log
                (N.complexActivityRatio xStar x (N.source r) /
                  N.complexActivityRatio xStar x (N.target r)) -
            N.complexActivityRatio xStar x (N.source r) +
            N.complexActivityRatio xStar x (N.target r)) =
          (∑ r, N.massActionFlux k xStar r *
            N.complexActivityRatio xStar x (N.source r) *
            Real.log
              (N.complexActivityRatio xStar x (N.source r) /
                N.complexActivityRatio xStar x (N.target r))) -
          (∑ r, N.massActionFlux k xStar r *
            N.complexActivityRatio xStar x (N.source r)) +
          ∑ r, N.massActionFlux k xStar r *
            N.complexActivityRatio xStar x (N.target r) := by
        simp_rw [mul_add, mul_sub]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring_nf
      _ = _ := by rw [hbalance]; ring
  rw [horbit, hdiss]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [N.massActionFlux_eq_reference_mul_activityRatio k xStar x r hxStar,
    Real.log_div (ne_of_gt (htarget r)) (ne_of_gt (hsource r)),
    Real.log_div (ne_of_gt (hsource r)) (ne_of_gt (htarget r))]
  ring

/-- The pseudo-Helmholtz orbital derivative is nonpositive at a
complex-balanced reference state. -/
theorem pseudoHelmholtz_derivative_nonpos
    {Species ComplexId ReactionId : Type}
    [Fintype Species] [Fintype ComplexId] [Fintype ReactionId]
    [DecidableEq Species] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (k : ReactionId → ℝ) (xStar x : Species → ℝ)
    (hbal : N.IsComplexBalanced k xStar) (hx : ∀ s, 0 < x s) :
    N.pseudoHelmholtzOrbitalDerivative k xStar x ≤ 0 := by
  rw [N.pseudoHelmholtz_derivative_eq_neg_dissipation k xStar x hbal hx]
  exact neg_nonpos.mpr
    (N.complexBalanceDissipation_nonneg k xStar x hbal hx)

end

end ChemistryLib.ReactionNetwork
