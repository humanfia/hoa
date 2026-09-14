import Mathlib

/-!
# IChO 2026, theory problem 8.10

The problem gives dynamic bimolecular quenching reactions for both the singlet
and triplet excited states.  If `tau0` is the lifetime without quencher, `kq`
is the (positive) bimolecular quenching constant, and `c` is the reductant
concentration, addition of the pseudo-first-order channel `kq * c` gives the
Stern--Volmer lifetime

`tau c = tau0 / (1 + kq * tau0 * c)`.

The proof below first establishes the strict concentration dependence for any
positive `tau0` and `kq`, and then instantiates it with both pairs of numerical
data printed in the question.  Thus the selected classification is derived
from the kinetic law rather than postulated as an answer.
-/

namespace IChO2026Problems.ProblemIChO2026T8A10

noncomputable section

/-! ## Answer vocabulary from the printed checkbox -/

/-- The three classifications printed in question 8.10. -/
inductive LifetimeTrend where
  | increases
  | decreases
  | unchanged
  deriving DecidableEq, Repr

/-- The mathematical meaning of each printed lifetime classification, on the
physical domain of nonnegative reductant concentrations. -/
def DescribesTrend (trend : LifetimeTrend) (lifetime : ℝ → ℝ) : Prop :=
  match trend with
  | .increases => StrictMonoOn lifetime (Set.Ici 0)
  | .decreases => StrictAntiOn lifetime (Set.Ici 0)
  | .unchanged => ∀ ⦃c₁⦄, c₁ ∈ Set.Ici (0 : ℝ) →
      ∀ ⦃c₂⦄, c₂ ∈ Set.Ici (0 : ℝ) → lifetime c₁ = lifetime c₂

/-! ## Problem inputs -/

/-- The printed unquenched S1 lifetime, `2.9 ns`, expressed in seconds. -/
def singletUnquenchedLifetime : ℝ := 29 / (10 : ℝ) ^ 10

/-- The printed unquenched T1 lifetime, `84 microseconds`, in seconds. -/
def tripletUnquenchedLifetime : ℝ := 84 / (10 : ℝ) ^ 6

/-- The printed S1 quenching constant, `2.7 * 10^9 M^-1 s^-1`. -/
def singletQuenchingRate : ℝ := 27 * (10 : ℝ) ^ 8

/-- The printed T1 quenching constant, `1.5 * 10^8 M^-1 s^-1`. -/
def tripletQuenchingRate : ℝ := 15 * (10 : ℝ) ^ 7

/-! ## Trusted kinetic law and derived algebra -/

/-- Dynamic-quenching lifetime law.  Concentration is represented by its
numerical value in mol/L and all rate/lifetime data use compatible SI units. -/
def quenchedLifetime (tau0 kq concentration : ℝ) : ℝ :=
  tau0 / (1 + kq * tau0 * concentration)

/-- In the absence of reductant, the dynamic-quenching law returns the given
unquenched lifetime. -/
theorem quenchedLifetime_zero (tau0 kq : ℝ) :
    quenchedLifetime tau0 kq 0 = tau0 := by
  simp [quenchedLifetime]

/-- Adding more quencher strictly shortens the lifetime whenever the
unquenched lifetime and quenching constant are positive. -/
theorem quenchedLifetime_strictAntiOn
    {tau0 kq : ℝ} (htau0 : 0 < tau0) (hkq : 0 < kq) :
    StrictAntiOn (quenchedLifetime tau0 kq) (Set.Ici 0) := by
  intro c₁ hc₁ c₂ hc₂ hc
  have hfactor : 0 < kq * tau0 := mul_pos hkq htau0
  have hden₁ : 0 < 1 + kq * tau0 * c₁ := by
    have hnonneg : 0 ≤ kq * tau0 * c₁ :=
      mul_nonneg (le_of_lt hfactor) hc₁
    linarith
  have hden_lt : 1 + kq * tau0 * c₁ < 1 + kq * tau0 * c₂ := by
    nlinarith [mul_lt_mul_of_pos_left hc hfactor]
  exact div_lt_div_of_pos_left htau0 hden₁ hden_lt

/-! ## Requested outputs -/

/-- Requested output `lifetime_s1`: the S1 emission lifetime decreases as
`[Red]` increases. -/
theorem lifetime_s1 :
    DescribesTrend .decreases
      (quenchedLifetime singletUnquenchedLifetime singletQuenchingRate) := by
  change StrictAntiOn
    (quenchedLifetime singletUnquenchedLifetime singletQuenchingRate)
    (Set.Ici 0)
  apply quenchedLifetime_strictAntiOn
  · norm_num [singletUnquenchedLifetime]
  · norm_num [singletQuenchingRate]

/-- Requested output `lifetime_t1`: the T1 emission lifetime decreases as
`[Red]` increases. -/
theorem lifetime_t1 :
    DescribesTrend .decreases
      (quenchedLifetime tripletUnquenchedLifetime tripletQuenchingRate) := by
  change StrictAntiOn
    (quenchedLifetime tripletUnquenchedLifetime tripletQuenchingRate)
    (Set.Ici 0)
  apply quenchedLifetime_strictAntiOn
  · norm_num [tripletUnquenchedLifetime]
  · norm_num [tripletQuenchingRate]

/-- The single checkbox on the blank answer sheet applies to both states, so
option (b), `decreases`, is correct for S1 and T1 together. -/
theorem icho_2026_t8_a10 :
    DescribesTrend .decreases
        (quenchedLifetime singletUnquenchedLifetime singletQuenchingRate) ∧
      DescribesTrend .decreases
        (quenchedLifetime tripletUnquenchedLifetime tripletQuenchingRate) := by
  exact ⟨lifetime_s1, lifetime_t1⟩

#print axioms quenchedLifetime_strictAntiOn
#print axioms lifetime_s1
#print axioms lifetime_t1
#print axioms icho_2026_t8_a10

end
end IChO2026Problems.ProblemIChO2026T8A10
