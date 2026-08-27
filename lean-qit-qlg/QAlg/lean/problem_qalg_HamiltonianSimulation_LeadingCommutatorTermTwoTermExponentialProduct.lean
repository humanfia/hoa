import QAlgBench.Base
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Leading commutator term for a two-term exponential product

This file formalizes the local error obtained by replacing the exponential of
a sum of two complex matrices with the product of their exponentials.
-/

open scoped Matrix.Norms.L2Operator
open Finset

namespace QAlgFormalized

/-- The error
`exp H₁ * exp H₂ - exp (H₁ + H₂)` in the two-term exponential product. -/
noncomputable def twoTermExponentialProductError {n : ℕ}
    (H₁ H₂ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp H₁ * NormedSpace.exp H₂ - NormedSpace.exp (H₁ + H₂)

set_option maxHeartbeats 800000 in
-- The local Taylor-tail proof and noncommutative norm estimates exceed the default elaboration budget.
/-- For uniformly small complex square matrices, the part of the two-term
exponential-product error beyond half the commutator is third order in the
common operator-norm bound, with a constant independent of the dimension,
matrices, and bound. -/
theorem leadingCommutatorTerm_twoTermExponentialProduct :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (H₁ H₂ : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ),
        ‖H₁‖ ≤ γ →
        ‖H₂‖ ≤ γ →
        γ < 1 →
        ‖twoTermExponentialProductError H₁ H₂ - (1 / 2 : ℂ) • ⁅H₁, H₂⁆‖ ≤
          C * γ ^ 3 := by
  let K : ℝ := NormedSpace.exp (2 : ℝ)
  have hK : 1 ≤ K := by
    change (1 : ℝ) ≤ NormedSpace.exp (2 : ℝ)
    rw [show (1 : ℝ) = NormedSpace.exp (0 : ℝ) by simp,
      NormedSpace.exp_eq_tsum ℝ]
    exact
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (0 : ℝ)).tsum_le_tsum
        (fun k => by
          simp only [smul_eq_mul]
          gcongr
          positivity)
        (NormedSpace.expSeries_summable' (𝕂 := ℝ) (2 : ℝ))
  refine ⟨32 * K ^ 2, by positivity, ?_⟩
  intro n A B γ hA hB hγ
  have hγ0 : 0 ≤ γ := (norm_nonneg A).trans hA
  have hγ1 : γ ≤ 1 := hγ.le
  let q : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun X => 1 + X + (1 / 2 : ℂ) • X ^ 2
  let r : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun X => NormedSpace.exp X - q X
  have exp_tail_bound (X : Matrix (Fin n) (Fin n) ℂ) (hX : ‖X‖ ≤ 2) :
      ‖NormedSpace.exp X - q X‖ ≤ K * ‖X‖ ^ 3 := by
    change
      ‖NormedSpace.exp X -
          (1 + X + (1 / 2 : ℂ) • X ^ 2)‖ ≤
        NormedSpace.exp (2 : ℝ) * ‖X‖ ^ 3
    let f : ℕ → Matrix (Fin n) (Fin n) ℂ :=
      fun k => ((k.factorial : ℂ)⁻¹) • X ^ k
    have hf : Summable f := by
      simpa [f] using (NormedSpace.expSeries_summable' (𝕂 := ℂ) X)
    have hsplit := hf.sum_add_tsum_nat_add 3
    have hpoly :
        (∑ k ∈ range 3, f k) =
          1 + X + (1 / 2 : ℂ) • X ^ 2 := by
      simp [f, sum_range_succ, Nat.factorial]
    have hg :
        HasSum (fun k : ℕ =>
            ‖X‖ ^ 3 * ((k.factorial : ℝ)⁻¹ * ‖X‖ ^ k))
          (‖X‖ ^ 3 * NormedSpace.exp ‖X‖) := by
      simpa [smul_eq_mul, div_eq_mul_inv] using
        ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖).mul_left
          (‖X‖ ^ 3))
    rw [show NormedSpace.exp X = ∑' k, f k by
          simpa [f] using congrFun (NormedSpace.exp_eq_tsum ℂ) X,
        ← hsplit, hpoly]
    simp only [add_sub_cancel_left]
    calc
      ‖∑' k : ℕ, f (k + 3)‖ ≤ ‖X‖ ^ 3 * NormedSpace.exp ‖X‖ := by
        apply tsum_of_norm_bounded hg
        intro k
        calc
          ‖f (k + 3)‖ ≤
              ((k + 3).factorial : ℝ)⁻¹ * ‖X‖ ^ (k + 3) := by
            calc
              ‖f (k + 3)‖ ≤
                  ‖(((k + 3).factorial : ℂ)⁻¹)‖ * ‖X ^ (k + 3)‖ :=
                norm_smul_le _ _
              _ = ((k + 3).factorial : ℝ)⁻¹ * ‖X ^ (k + 3)‖ := by
                rw [norm_inv, Complex.norm_natCast]
              _ ≤ ((k + 3).factorial : ℝ)⁻¹ * ‖X‖ ^ (k + 3) := by
                gcongr
                exact norm_pow_le' X (by omega)
          _ ≤ (k.factorial : ℝ)⁻¹ * ‖X‖ ^ (k + 3) := by
            have hfac :
                (k.factorial : ℝ) ≤ ((k + 3).factorial : ℝ) := by
              exact_mod_cast Nat.factorial_le (by omega : k ≤ k + 3)
            exact mul_le_mul_of_nonneg_right
              (inv_anti₀ (by positivity) hfac) (by positivity)
          _ = ‖X‖ ^ 3 * ((k.factorial : ℝ)⁻¹ * ‖X‖ ^ k) := by
            rw [pow_add]
            ring
      _ ≤ NormedSpace.exp (2 : ℝ) * ‖X‖ ^ 3 := by
        rw [mul_comm (‖X‖ ^ 3)]
        gcongr
        rw [NormedSpace.exp_eq_tsum ℝ]
        exact
          (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖X‖).tsum_le_tsum
            (fun k => by
              simp only [smul_eq_mul]
              gcongr)
            (NormedSpace.expSeries_summable' (𝕂 := ℝ) (2 : ℝ))
  have hone : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def]
    rw [show (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (1 : Matrix (Fin n) (Fin n) ℂ) =
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) by
      ext x
      simp]
    exact ContinuousLinearMap.norm_id_le
  have hA2 : ‖A‖ ≤ 2 := hA.trans (by linarith)
  have hB2 : ‖B‖ ≤ 2 := hB.trans (by linarith)
  have hABnorm : ‖A + B‖ ≤ 2 * γ :=
    (norm_add_le A B).trans (by linarith)
  have hAB2 : ‖A + B‖ ≤ 2 := hABnorm.trans (by nlinarith)
  have hrA0 : ‖r A‖ ≤ K * ‖A‖ ^ 3 := by
    simpa [r] using exp_tail_bound A hA2
  have hrB0 : ‖r B‖ ≤ K * ‖B‖ ^ 3 := by
    simpa [r] using exp_tail_bound B hB2
  have hrAB0 : ‖r (A + B)‖ ≤ K * ‖A + B‖ ^ 3 := by
    simpa [r] using exp_tail_bound (A + B) hAB2
  have hrA : ‖r A‖ ≤ K * γ ^ 3 := hrA0.trans <| by
    gcongr
  have hrB : ‖r B‖ ≤ K * γ ^ 3 := hrB0.trans <| by
    gcongr
  have hrAB : ‖r (A + B)‖ ≤ 8 * K * γ ^ 3 := hrAB0.trans <| by
    have hpow : ‖A + B‖ ^ 3 ≤ (2 * γ) ^ 3 := by gcongr
    calc
      K * ‖A + B‖ ^ 3 ≤ K * (2 * γ) ^ 3 := by gcongr
      _ = 8 * K * γ ^ 3 := by ring
  have hq (X : Matrix (Fin n) (Fin n) ℂ) (hX : ‖X‖ ≤ γ) :
      ‖q X‖ ≤ 3 := by
    calc
      ‖q X‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ) + X‖ +
          ‖(1 / 2 : ℂ) • X ^ 2‖ := by
        exact norm_add_le _ _
      _ ≤ (‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X‖) +
          ‖(1 / 2 : ℂ)‖ * ‖X ^ 2‖ := by
        gcongr
        · exact norm_add_le _ _
        · exact norm_smul_le _ _
      _ ≤ (1 + γ) + (1 / 2 : ℝ) * γ ^ 2 := by
        have hXpow : ‖X ^ 2‖ ≤ γ ^ 2 :=
          (norm_pow_le' X (by norm_num)).trans <| by
            exact pow_le_pow_left₀ (norm_nonneg X) hX 2
        exact add_le_add
          (add_le_add hone hX)
          (mul_le_mul (by norm_num) hXpow (norm_nonneg _) (by norm_num))
      _ ≤ 3 := by nlinarith [sq_nonneg (γ - 1)]
  have hqA : ‖q A‖ ≤ 3 := hq A hA
  have hqB : ‖q B‖ ≤ 3 := hq B hB
  have hexpB : ‖NormedSpace.exp B‖ ≤ 4 * K := by
    calc
      ‖NormedSpace.exp B‖ = ‖r B + q B‖ := by
        congr 1
        simp [r]
      _ ≤ ‖r B‖ + ‖q B‖ := norm_add_le _ _
      _ ≤ K * γ ^ 3 + 3 := by gcongr
      _ ≤ 4 * K := by
        have hγpow : γ ^ 3 ≤ 1 := by nlinarith [sq_nonneg γ]
        nlinarith [mul_le_mul_of_nonneg_left hγpow (by linarith : 0 ≤ K)]
  have hAB2mono : ‖A * B ^ 2‖ ≤ γ ^ 3 := by
    have hBpow : ‖B ^ 2‖ ≤ γ ^ 2 :=
      (norm_pow_le' B (by norm_num)).trans <| by
        exact pow_le_pow_left₀ (norm_nonneg B) hB 2
    calc
      ‖A * B ^ 2‖ ≤ ‖A‖ * ‖B ^ 2‖ := norm_mul_le _ _
      _ ≤ γ * γ ^ 2 :=
        mul_le_mul hA hBpow (norm_nonneg _) hγ0
      _ = γ ^ 3 := by ring
  have hA2Bmono : ‖A ^ 2 * B‖ ≤ γ ^ 3 := by
    have hApow : ‖A ^ 2‖ ≤ γ ^ 2 :=
      (norm_pow_le' A (by norm_num)).trans <| by
        exact pow_le_pow_left₀ (norm_nonneg A) hA 2
    calc
      ‖A ^ 2 * B‖ ≤ ‖A ^ 2‖ * ‖B‖ := norm_mul_le _ _
      _ ≤ γ ^ 2 * γ :=
        mul_le_mul hApow hB (norm_nonneg _) (sq_nonneg γ)
      _ = γ ^ 3 := by ring
  have hA2B2mono : ‖A ^ 2 * B ^ 2‖ ≤ γ ^ 3 := by
    have hApow : ‖A ^ 2‖ ≤ γ ^ 2 :=
      (norm_pow_le' A (by norm_num)).trans <| by
        exact pow_le_pow_left₀ (norm_nonneg A) hA 2
    have hBpow : ‖B ^ 2‖ ≤ γ ^ 2 :=
      (norm_pow_le' B (by norm_num)).trans <| by
        exact pow_le_pow_left₀ (norm_nonneg B) hB 2
    calc
      ‖A ^ 2 * B ^ 2‖ ≤ ‖A ^ 2‖ * ‖B ^ 2‖ := norm_mul_le _ _
      _ ≤ γ ^ 2 * γ ^ 2 :=
        mul_le_mul hApow hBpow (norm_nonneg _) (sq_nonneg γ)
      _ = γ ^ 3 * γ := by ring
      _ ≤ γ ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hγ1 (pow_nonneg hγ0 3)
      _ = γ ^ 3 := by ring
  have quadratic_product_identity :
      q A * q B - q (A + B) - (1 / 2 : ℂ) • ⁅A, B⁆ =
        (1 / 2 : ℂ) • (A * B ^ 2) +
          (1 / 2 : ℂ) • (A ^ 2 * B) +
          (1 / 4 : ℂ) • (A ^ 2 * B ^ 2) := by
    simp only [q, Ring.lie_def]
    noncomm_ring
    module
  have hpoly :
      ‖q A * q B - q (A + B) - (1 / 2 : ℂ) • ⁅A, B⁆‖ ≤
        3 * γ ^ 3 := by
    rw [quadratic_product_identity]
    calc
      ‖(1 / 2 : ℂ) • (A * B ^ 2) +
          (1 / 2 : ℂ) • (A ^ 2 * B) +
          (1 / 4 : ℂ) • (A ^ 2 * B ^ 2)‖ ≤
        ‖(1 / 2 : ℂ) • (A * B ^ 2)‖ +
          ‖(1 / 2 : ℂ) • (A ^ 2 * B)‖ +
          ‖(1 / 4 : ℂ) • (A ^ 2 * B ^ 2)‖ := by
            exact (norm_add_le _ _).trans <| add_le_add (norm_add_le _ _) le_rfl
      _ ≤ γ ^ 3 + γ ^ 3 + γ ^ 3 := by
        gcongr
        · exact (norm_smul_le _ _).trans <| by
            calc
              ‖(1 / 2 : ℂ)‖ * ‖A * B ^ 2‖ ≤ 1 * γ ^ 3 :=
                mul_le_mul (by norm_num) hAB2mono (norm_nonneg _) (by norm_num)
              _ = γ ^ 3 := one_mul _
        · exact (norm_smul_le _ _).trans <| by
            calc
              ‖(1 / 2 : ℂ)‖ * ‖A ^ 2 * B‖ ≤ 1 * γ ^ 3 :=
                mul_le_mul (by norm_num) hA2Bmono (norm_nonneg _) (by norm_num)
              _ = γ ^ 3 := one_mul _
        · exact (norm_smul_le _ _).trans <| by
            calc
              ‖(1 / 4 : ℂ)‖ * ‖A ^ 2 * B ^ 2‖ ≤ 1 * γ ^ 3 :=
                mul_le_mul (by norm_num) hA2B2mono (norm_nonneg _) (by norm_num)
              _ = γ ^ 3 := one_mul _
      _ = 3 * γ ^ 3 := by ring
  have hdecomp :
      twoTermExponentialProductError A B - (1 / 2 : ℂ) • ⁅A, B⁆ =
        r A * NormedSpace.exp B + q A * r B +
          (q A * q B - q (A + B) - (1 / 2 : ℂ) • ⁅A, B⁆) -
          r (A + B) := by
    simp only [twoTermExponentialProductError, r]
    noncomm_ring
  rw [hdecomp]
  calc
    ‖r A * NormedSpace.exp B + q A * r B +
        (q A * q B - q (A + B) - (1 / 2 : ℂ) • ⁅A, B⁆) -
        r (A + B)‖ ≤
      ‖r A * NormedSpace.exp B‖ + ‖q A * r B‖ +
        ‖q A * q B - q (A + B) - (1 / 2 : ℂ) • ⁅A, B⁆‖ +
        ‖r (A + B)‖ := by
          exact (norm_sub_le _ _).trans <| add_le_add
            ((norm_add_le _ _).trans <| add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ 8 * K ^ 2 * γ ^ 3 + 8 * K ^ 2 * γ ^ 3 +
        8 * K ^ 2 * γ ^ 3 + 8 * K ^ 2 * γ ^ 3 := by
      gcongr
      · calc
          ‖r A * NormedSpace.exp B‖ ≤ ‖r A‖ * ‖NormedSpace.exp B‖ := norm_mul_le _ _
          _ ≤ (K * γ ^ 3) * (4 * K) := by gcongr
          _ = 4 * (K ^ 2 * γ ^ 3) := by ring
          _ ≤ 8 * (K ^ 2 * γ ^ 3) := by
            nlinarith [mul_nonneg (sq_nonneg K) (pow_nonneg hγ0 3)]
          _ = 8 * K ^ 2 * γ ^ 3 := by ring
      · calc
          ‖q A * r B‖ ≤ ‖q A‖ * ‖r B‖ := norm_mul_le _ _
          _ ≤ 3 * (K * γ ^ 3) := by gcongr
          _ ≤ 3 * (K ^ 2 * γ ^ 3) := by
            have hKK : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
            nlinarith [mul_le_mul_of_nonneg_right hKK (pow_nonneg hγ0 3)]
          _ ≤ 8 * K ^ 2 * γ ^ 3 := by
            nlinarith [mul_nonneg (sq_nonneg K) (pow_nonneg hγ0 3)]
      · exact hpoly.trans <| by
          have hKsq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
          exact mul_le_mul_of_nonneg_right (by nlinarith)
            (pow_nonneg hγ0 3)
      · exact hrAB.trans <| by
          have hKK : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
          exact mul_le_mul_of_nonneg_right (by nlinarith)
            (pow_nonneg hγ0 3)
    _ = (32 * K ^ 2) * γ ^ 3 := by ring

end QAlgFormalized
