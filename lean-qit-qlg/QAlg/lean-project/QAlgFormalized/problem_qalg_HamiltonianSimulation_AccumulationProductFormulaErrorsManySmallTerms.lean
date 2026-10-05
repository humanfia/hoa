import QAlgBench.Base
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Accumulation of product-formula errors for many small terms

This file formalizes the data and conclusions in the quantum-algorithms
benchmark problem
`HamiltonianSimulation/AccumulationProductFormulaErrorsManySmallTerms`.
-/

open scoped Matrix.Norms.L2Operator
open NormedSpace

noncomputable section

namespace QAlgFormalized.AccumulationProductFormulaErrorsManySmallTerms

/-- The prefix sum `S_k = H_1 + ⋯ + H_k`, using `Fin M` index `j` for the
source term `H_{j+1}`. In particular, `partialSum H 0 = 0`. -/
def partialSum {n : Type*} [Fintype n] {M : ℕ}
    (H : Fin M → Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  ∑ j : Fin M, if (j : ℕ) < k then H j else 0

/-- The ordered, generally noncommutative product
`exp(H_1) * exp(H_2) * ⋯ * exp(H_M)`. -/
def orderedExpProduct {n : Type*} [Fintype n] [DecidableEq n] {M : ℕ}
    (H : Fin M → Matrix n n ℂ) : Matrix n n ℂ :=
  (List.ofFn fun j : Fin M => exp (H j)).prod

/-- Data and governing assumptions for accumulation of product-formula errors.
The source indices `1, …, M` are represented by `Fin M`, so a Lean index `k`
corresponds to the source index `k + 1`.

The local-error constant `C` is required to be nonnegative, as is standard for
a multiplicative error-bound constant and as is necessary for the requested
upper bound to be valid. -/
structure ProductFormulaData (n : Type*) [Fintype n] [DecidableEq n]
    (M : ℕ) (γ R C : ℝ) where
  H : Fin M → Matrix n n ℂ
  F : Fin M → Matrix n n ℂ
  E : Matrix n n ℂ
  hermitian : ∀ j, (H j).IsHermitian
  gamma_pos : 0 < γ
  gamma_lt_one : γ < 1
  radius_pos : 0 < R
  constant_nonneg : 0 ≤ C
  term_norm_le : ∀ j, ‖H j‖ ≤ γ
  total_scale_le : (M : ℝ) * γ ≤ R
  remainder_eq : ∀ k : Fin M,
    exp (partialSum H (k : ℕ)) * exp (H k) =
      exp (partialSum H ((k : ℕ) + 1)) + F k
  remainder_norm_le : ∀ k : Fin M,
    ‖F k‖ ≤ C * ‖partialSum H (k : ℕ)‖ * ‖H k‖ *
      Real.exp (‖partialSum H (k : ℕ)‖ + ‖H k‖)
  error_eq : orderedExpProduct H = exp (partialSum H M) + E

private lemma matrix_norm_one_le_one {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [show (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => 1) by
        ext
        simp,
    Matrix.l2_opNorm_diagonal]
  simpa using (pi_norm_const_le (ι := n) (1 : ℂ))

private lemma norm_exp_le_exp_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ‖exp A‖ ≤ Real.exp ‖A‖ := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  refine tsum_of_norm_bounded
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖A‖) ?_
  intro k
  rw [norm_smul]
  change |((k.factorial : ℝ)⁻¹)| * ‖A ^ k‖ ≤
    ((k.factorial : ℝ)⁻¹) * ‖A‖ ^ k
  rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  by_cases hk : k = 0
  · subst k
    simpa using (matrix_norm_one_le_one (n := n))
  · exact mul_le_mul_of_nonneg_left (norm_pow_le' A (Nat.pos_of_ne_zero hk))
      (inv_nonneg.mpr (Nat.cast_nonneg _))

private lemma partialSum_succ {n : Type*} [Fintype n] [DecidableEq n]
    {M k : ℕ} (H : Fin M → Matrix n n ℂ) (hk : k < M) :
    partialSum H (k + 1) = partialSum H k + H ⟨k, hk⟩ := by
  classical
  let i : Fin M := ⟨k, hk⟩
  have hfilter :
      Finset.univ.filter (fun j : Fin M => (j : ℕ) < k + 1) =
        insert i (Finset.univ.filter (fun j : Fin M => (j : ℕ) < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hjk : (j : ℕ) = k
      · exact Or.inl (Fin.ext hjk)
      · exact Or.inr (by omega)
    · rintro (rfl | hj)
      · simp [i]
      · omega
  unfold partialSum
  rw [← Finset.sum_filter, ← Finset.sum_filter, hfilter, Finset.sum_insert]
  · simp [i, add_comm]
  · simp [i]

private lemma orderedPrefixProduct_succ {n : Type*} [Fintype n] [DecidableEq n]
    {M k : ℕ} (H : Fin M → Matrix n n ℂ) (hk : k < M) :
    ((List.ofFn fun j : Fin M => exp (H j)).take (k + 1)).prod =
      ((List.ofFn fun j : Fin M => exp (H j)).take k).prod * exp (H ⟨k, hk⟩) := by
  rw [List.prod_take_succ _ _ (by simpa using hk)]
  simp

/-- The explicit accumulated error bound for many small Hermitian terms. -/
theorem error_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℕ) (γ R C : ℝ) (data : ProductFormulaData n M γ R C) :
    ‖data.E‖ ≤
      (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := by
  let P : ℕ → Matrix n n ℂ :=
    fun k => ((List.ofFn fun j : Fin M => exp (data.H j)).take k).prod
  have hpair_nonneg (k : ℕ) : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    cases k with
    | zero => norm_num
    | succ k =>
        rw [Nat.cast_succ]
        nlinarith [mul_nonneg (Nat.cast_nonneg k)
          (show 0 ≤ (k : ℝ) + 1 by positivity)]
  have hgamma : 0 ≤ γ := data.gamma_pos.le
  have hpartial : ∀ k : ℕ, k ≤ M →
      ‖partialSum data.H k‖ ≤ (k : ℝ) * γ := by
    intro k hk
    induction k with
    | zero =>
        simp [partialSum]
    | succ k ih =>
        have hklt : k < M := by omega
        rw [partialSum_succ data.H hklt]
        calc
          ‖partialSum data.H k + data.H ⟨k, hklt⟩‖
              ≤ ‖partialSum data.H k‖ + ‖data.H ⟨k, hklt⟩‖ :=
            norm_add_le _ _
          _ ≤ (k : ℝ) * γ + γ :=
            add_le_add (ih (by omega)) (data.term_norm_le ⟨k, hklt⟩)
          _ = ((k + 1 : ℕ) : ℝ) * γ := by
            push_cast
            ring
  have hprefix : ∀ k : ℕ, k ≤ M →
      ‖P k - exp (partialSum data.H k)‖ ≤
        (C / 2) * ((k : ℝ) * ((k : ℝ) - 1)) * γ ^ 2 *
          Real.exp ((k : ℝ) * γ) := by
    intro k hk
    induction k with
    | zero =>
        simp [P, partialSum]
    | succ k ih =>
        have hklt : k < M := by omega
        let i : Fin M := ⟨k, hklt⟩
        have hrec :
            P (k + 1) - exp (partialSum data.H (k + 1)) =
              (P k - exp (partialSum data.H k)) * exp (data.H i) + data.F i := by
          rw [show P (k + 1) = P k * exp (data.H i) by
            simpa [P, i] using orderedPrefixProduct_succ data.H hklt]
          have hrem := data.remainder_eq i
          change exp (partialSum data.H k) * exp (data.H i) =
            exp (partialSum data.H (k + 1)) + data.F i at hrem
          calc
            P k * exp (data.H i) - exp (partialSum data.H (k + 1))
                = (P k - exp (partialSum data.H k)) * exp (data.H i) +
                    (exp (partialSum data.H k) * exp (data.H i) -
                      exp (partialSum data.H (k + 1))) := by noncomm_ring
            _ = (P k - exp (partialSum data.H k)) * exp (data.H i) +
                    data.F i := by
                  rw [hrem]
                  noncomm_ring
        have hsum :
            ‖partialSum data.H k‖ + ‖data.H i‖ ≤ ((k : ℝ) + 1) * γ := by
          calc
            ‖partialSum data.H k‖ + ‖data.H i‖
                ≤ (k : ℝ) * γ + γ :=
              add_le_add (hpartial k (by omega)) (data.term_norm_le i)
            _ = ((k : ℝ) + 1) * γ := by ring
        have hlocal :
            ‖data.F i‖ ≤
              C * (k : ℝ) * γ ^ 2 * Real.exp (((k : ℝ) + 1) * γ) := by
          calc
            ‖data.F i‖
                ≤ C * ‖partialSum data.H k‖ * ‖data.H i‖ *
                    Real.exp (‖partialSum data.H k‖ + ‖data.H i‖) := by
                  simpa [i] using data.remainder_norm_le i
            _ ≤ C * ((k : ℝ) * γ) * γ *
                    Real.exp (((k : ℝ) + 1) * γ) := by
                  have hA : 0 ≤ (k : ℝ) * γ :=
                    mul_nonneg (Nat.cast_nonneg k) hgamma
                  have hab :
                      C * ‖partialSum data.H k‖ * ‖data.H i‖ ≤
                        C * ((k : ℝ) * γ) * γ := by
                    calc
                      C * ‖partialSum data.H k‖ * ‖data.H i‖
                          ≤ C * ((k : ℝ) * γ) * ‖data.H i‖ := by
                            exact mul_le_mul_of_nonneg_right
                              (mul_le_mul_of_nonneg_left
                                (hpartial k (by omega)) data.constant_nonneg)
                              (norm_nonneg _)
                      _ ≤ C * ((k : ℝ) * γ) * γ := by
                            exact mul_le_mul_of_nonneg_left
                              (data.term_norm_le i)
                              (mul_nonneg data.constant_nonneg hA)
                  exact mul_le_mul hab (Real.exp_le_exp.mpr hsum)
                    (Real.exp_pos _).le
                    (mul_nonneg (mul_nonneg data.constant_nonneg hA) hgamma)
            _ = C * (k : ℝ) * γ ^ 2 *
                    Real.exp (((k : ℝ) + 1) * γ) := by ring
        have hexp :
            ‖exp (data.H i)‖ ≤ Real.exp γ :=
          (norm_exp_le_exp_norm (data.H i)).trans
            (Real.exp_le_exp.mpr (data.term_norm_le i))
        have hcoef :
            0 ≤ (C / 2) * ((k : ℝ) * ((k : ℝ) - 1)) * γ ^ 2 := by
          exact mul_nonneg
            (mul_nonneg (div_nonneg data.constant_nonneg (by norm_num))
              (hpair_nonneg k))
            (sq_nonneg γ)
        have hexp_add :
            Real.exp ((k : ℝ) * γ) * Real.exp γ =
              Real.exp (((k : ℝ) + 1) * γ) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hrec]
        calc
          ‖(P k - exp (partialSum data.H k)) * exp (data.H i) + data.F i‖
              ≤ ‖(P k - exp (partialSum data.H k)) * exp (data.H i)‖ +
                  ‖data.F i‖ := norm_add_le _ _
          _ ≤ ‖P k - exp (partialSum data.H k)‖ * ‖exp (data.H i)‖ +
                  ‖data.F i‖ :=
                add_le_add (norm_mul_le _ _) le_rfl
          _ ≤ ((C / 2) * ((k : ℝ) * ((k : ℝ) - 1)) * γ ^ 2 *
                  Real.exp ((k : ℝ) * γ)) * Real.exp γ +
                C * (k : ℝ) * γ ^ 2 * Real.exp (((k : ℝ) + 1) * γ) := by
                exact add_le_add
                  (mul_le_mul (ih (by omega)) hexp (norm_nonneg _)
                    (mul_nonneg hcoef (Real.exp_pos _).le))
                  hlocal
          _ = (C / 2) *
                (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1)) * γ ^ 2 *
                  Real.exp (((k + 1 : ℕ) : ℝ) * γ) := by
                calc
                  _ = ((C / 2) * ((k : ℝ) * ((k : ℝ) - 1)) * γ ^ 2) *
                        (Real.exp ((k : ℝ) * γ) * Real.exp γ) +
                      C * (k : ℝ) * γ ^ 2 *
                        Real.exp (((k : ℝ) + 1) * γ) := by ring
                  _ = _ := by
                    rw [hexp_add]
                    push_cast
                    ring
  have hfull : P M = orderedExpProduct data.H := by
    simp only [P, orderedExpProduct]
    rw [List.take_of_length_le (by simp)]
  have hglobal : P M = exp (partialSum data.H M) + data.E := by
    rw [hfull]
    exact data.error_eq
  have herror :
      P M - exp (partialSum data.H M) = data.E := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm] using hglobal
  have hexp_total :
      Real.exp ((M : ℝ) * γ) ≤ Real.exp R :=
    Real.exp_le_exp.mpr data.total_scale_le
  have hcoef_total :
      0 ≤ (C / 2) * ((M : ℝ) * ((M : ℝ) - 1)) * γ ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg data.constant_nonneg (by norm_num))
        (hpair_nonneg M))
      (sq_nonneg γ)
  calc
    ‖data.E‖ = ‖P M - exp (partialSum data.H M)‖ := by rw [herror]
    _ ≤ (C / 2) * ((M : ℝ) * ((M : ℝ) - 1)) * γ ^ 2 *
          Real.exp ((M : ℝ) * γ) := hprefix M le_rfl
    _ ≤ (C / 2) * ((M : ℝ) * ((M : ℝ) - 1)) * γ ^ 2 *
          Real.exp R := mul_le_mul_of_nonneg_left hexp_total hcoef_total
    _ = (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 := by
      ring

/-- With `R` (and the universal local-remainder constant `C`) fixed, the error
is uniformly `O(M^2 γ^2)` along any family of admissible instances. The filter
`l` records the intended asymptotic direction without imposing an additional
relation between `M` and `γ` beyond the source condition `M * γ ≤ R`. -/
theorem error_norm_isBigO {ι n : Type*} [Fintype n] [DecidableEq n]
    (l : Filter ι) (M : ι → ℕ) (γ : ι → ℝ) (R C : ℝ)
    (data : ∀ i, ProductFormulaData n (M i) (γ i) R C) :
    Asymptotics.IsBigO l
      (fun i => ‖(data i).E‖)
      (fun i => (M i : ℝ) ^ 2 * (γ i) ^ 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨C * Real.exp R / 2, Filter.Eventually.of_forall fun i => ?_⟩
  have hscale : 0 ≤ (M i : ℝ) ^ 2 * (γ i) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hscale]
  have hmain := error_norm_le (M i) (γ i) R C (data i)
  have hconstant : 0 ≤ C * Real.exp R / 2 :=
    div_nonneg (mul_nonneg (data i).constant_nonneg (Real.exp_pos _).le)
      (by norm_num)
  have hquad : (M i : ℝ) * ((M i : ℝ) - 1) ≤ (M i : ℝ) ^ 2 := by
    have hm : 0 ≤ (M i : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hquad_scaled :
      (C * Real.exp R / 2) * (M i : ℝ) * ((M i : ℝ) - 1) ≤
        (C * Real.exp R / 2) * (M i : ℝ) ^ 2 := by
    calc
      (C * Real.exp R / 2) * (M i : ℝ) * ((M i : ℝ) - 1) =
          (C * Real.exp R / 2) * ((M i : ℝ) * ((M i : ℝ) - 1)) := by
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hquad hconstant
  calc
    ‖(data i).E‖ ≤
        (C * Real.exp R / 2) * (M i : ℝ) * ((M i : ℝ) - 1) *
          (γ i) ^ 2 := hmain
    _ ≤ ((C * Real.exp R / 2) * (M i : ℝ) ^ 2) * (γ i) ^ 2 :=
      mul_le_mul_of_nonneg_right hquad_scaled (sq_nonneg _)
    _ = _ := by ring

end QAlgFormalized.AccumulationProductFormulaErrorsManySmallTerms
