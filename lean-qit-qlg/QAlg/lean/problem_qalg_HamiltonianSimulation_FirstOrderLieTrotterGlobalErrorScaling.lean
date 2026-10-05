import QAlgBench.Base
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped BigOperators Matrix.Norms.L2Operator
open Filter

namespace QAlgFormalized
namespace FirstOrderLieTrotterGlobalErrorScaling

open QAlgBench

noncomputable section

/-!
This file formalizes the assumptions and requested conclusions of the
first-order Lie--Trotter global-error scaling problem.  In particular, the
scoped matrix norm is the `ℓ²` operator norm, not the entrywise sup norm.
-/

/-- The spectral/operator-norm scale `ν = max {‖A‖, ‖B‖}`. -/
def hamiltonianScale {R : Register} (A B : HilbertOperator R) : ℝ :=
  max ‖A‖ ‖B‖

/-- The matrix commutator `[A,B] = AB - BA`. -/
def matrixCommutator {R : Register} (A B : HilbertOperator R) :
    HilbertOperator R :=
  A * B - B * A

/-- One first-order Lie--Trotter step at real time `τ`. -/
def lieTrotterStep {R : Register} (A B : HilbertOperator R) (τ : ℝ) :
    HilbertOperator R :=
  NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A) *
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • B)

/-- Exact evolution under the summed Hamiltonian for real time `t`. -/
def exactEvolution {R : Register} (A B : HilbertOperator R) (t : ℝ) :
    HilbertOperator R :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • (A + B))

/-- The local cubic-remainder hypothesis, with `c,C` universal over the
register and both Hermitian Hamiltonians. -/
def LocalExpansionBound (c C : ℝ) : Prop :=
  ∀ (R : Register) (A B : HilbertOperator R),
    Matrix.IsHermitian A → Matrix.IsHermitian B →
      ∀ τ : ℝ, hamiltonianScale A B * |τ| ≤ c →
        ‖lieTrotterStep A B τ - exactEvolution A B τ +
            (((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖
          ≤ C * hamiltonianScale A B ^ 3 * |τ| ^ 3

/-- Ordered product `U_m ⋯ U_1` when `U 0` represents `U_1`. -/
def reverseOrderedProduct {R : Register} {m : ℕ}
    (U : Fin m → HilbertOperator R) : HilbertOperator R :=
  (List.ofFn U).reverse.foldl (fun product factor => product * factor) 1

/-- The assumed telescoping estimate, universally quantified over dimension,
product length, and matching unitary factors. -/
def ProductTelescopingEstimate : Prop :=
  ∀ (R : Register) (m : ℕ)
      (U V : Fin m → HilbertOperator R),
    (∀ j, U j ∈ Matrix.unitaryGroup R.Index ℂ) →
    (∀ j, V j ∈ Matrix.unitaryGroup R.Index ℂ) →
      ‖reverseOrderedProduct U - reverseOrderedProduct V‖
        ≤ ∑ j, ‖U j - V j‖

/-- Global simulation error after `m` equal Lie--Trotter steps. -/
def globalError {R : Register} (A B : HilbertOperator R) (t : ℝ)
    (m : ℕ) : ℝ :=
  ‖lieTrotterStep A B (t / (m : ℝ)) ^ m - exactEvolution A B t‖

/-- The requested first-order global-error scale `ν²t²/m`. -/
def globalErrorScale {R : Register} (A B : HilbertOperator R) (t : ℝ)
    (m : ℕ) : ℝ :=
  hamiltonianScale A B ^ 2 * t ^ 2 / (m : ℝ)

/-- Literal `m = O(ν²t²/ε)` scaling for an integer-valued step-count choice,
with the asymptotic taken as positive `ε` tends to zero. -/
def StepCountIsBigO {R : Register} (A B : HilbertOperator R) (t : ℝ)
    (steps : ℝ → ℕ) : Prop :=
  Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
    (fun ε : ℝ => (steps ε : ℝ))
    (fun ε : ℝ => hamiltonianScale A B ^ 2 * t ^ 2 / ε)

private theorem exponential_smul_hermitian_mem_unitary
    {R : Register} (A : HilbertOperator R) (hA : Matrix.IsHermitian A)
    (τ : ℝ) :
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A) ∈
      Matrix.unitaryGroup R.Index ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose]
  have hs : Matrix.conjTranspose ((-Complex.I * (τ : ℂ)) • A) =
      -((-Complex.I * (τ : ℂ)) • A) := by
    rw [Matrix.conjTranspose_smul, hA.eq]
    ext i j
    simp
  rw [hs, Matrix.exp_neg]
  apply Matrix.mul_nonsing_inv
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)

private theorem reverseOrderedProduct_const
    {R : Register} {m : ℕ} (X : HilbertOperator R) :
    reverseOrderedProduct (fun _ : Fin m => X) = X ^ m := by
  rw [reverseOrderedProduct, List.foldl_eq_foldr_reverse]
  simp only [List.reverse_reverse, List.ofFn_const]
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih, pow_succ]

private theorem exactEvolution_pow
    {R : Register} (A B : HilbertOperator R) (t : ℝ)
    (m : ℕ) (hm : 0 < m) :
    exactEvolution A B (t / (m : ℝ)) ^ m = exactEvolution A B t := by
  rw [exactEvolution, ← Matrix.exp_nsmul]
  congr 1
  ext i j
  simp
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)]
  ring

private theorem oneStep_error_bound
    (c C : ℝ) (hC : 0 < C) (hLocal : LocalExpansionBound c C)
    (R : Register) (A B : HilbertOperator R)
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsmall : hamiltonianScale A B * τ ≤ c) :
    ‖lieTrotterStep A B τ - exactEvolution A B τ‖ ≤
      (C * c + 1) * hamiltonianScale A B ^ 2 * τ ^ 2 := by
  let ν := hamiltonianScale A B
  have hν : 0 ≤ ν := by
    dsimp [ν, hamiltonianScale]
    exact le_max_of_le_left (norm_nonneg A)
  have hAν : ‖A‖ ≤ ν := by simp [ν, hamiltonianScale]
  have hBν : ‖B‖ ≤ ν := by simp [ν, hamiltonianScale]
  have hcomm : ‖matrixCommutator A B‖ ≤ 2 * ν ^ 2 := by
    calc
      ‖matrixCommutator A B‖ = ‖A * B - B * A‖ := rfl
      _ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ :=
        add_le_add (norm_mul_le A B) (norm_mul_le B A)
      _ ≤ 2 * ν ^ 2 := by
        nlinarith [norm_nonneg A, norm_nonneg B]
  have hrem := hLocal R A B hA hB τ
    (by simpa [ν, abs_of_nonneg hτ] using hsmall)
  have hrem' :
      ‖lieTrotterStep A B τ - exactEvolution A B τ +
          (((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ ≤
        C * ν ^ 3 * τ ^ 3 := by
    simpa [ν, abs_of_nonneg hτ] using hrem
  have hcorr :
      ‖(((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ ≤
        τ ^ 2 * ν ^ 2 := by
    calc
      ‖(((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ =
          (τ ^ 2 / 2) * ‖matrixCommutator A B‖ := by
            rw [norm_smul]
            simp
      _ ≤ (τ ^ 2 / 2) * (2 * ν ^ 2) :=
        mul_le_mul_of_nonneg_left hcomm (by positivity)
      _ = τ ^ 2 * ν ^ 2 := by ring
  have hcubic :
      C * ν ^ 3 * τ ^ 3 ≤ C * c * (ν ^ 2 * τ ^ 2) := by
    calc
      C * ν ^ 3 * τ ^ 3 =
          (ν * τ) * (C * (ν ^ 2 * τ ^ 2)) := by ring
      _ ≤ c * (C * (ν ^ 2 * τ ^ 2)) :=
        mul_le_mul_of_nonneg_right (by simpa [ν] using hsmall) (by positivity)
      _ = C * c * (ν ^ 2 * τ ^ 2) := by ring
  calc
    ‖lieTrotterStep A B τ - exactEvolution A B τ‖ =
        ‖(lieTrotterStep A B τ - exactEvolution A B τ +
            (((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)) -
            (((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ := by
      congr 1
      abel
    _ ≤ ‖lieTrotterStep A B τ - exactEvolution A B τ +
            (((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ +
          ‖(((τ ^ 2 / 2 : ℝ) : ℂ) • matrixCommutator A B)‖ :=
      norm_sub_le _ _
    _ ≤ C * ν ^ 3 * τ ^ 3 + τ ^ 2 * ν ^ 2 :=
      add_le_add hrem' hcorr
    _ ≤ C * c * (ν ^ 2 * τ ^ 2) + τ ^ 2 * ν ^ 2 :=
      add_le_add hcubic le_rfl
    _ = (C * c + 1) * hamiltonianScale A B ^ 2 * τ ^ 2 := by
      dsimp [ν]
      ring

/-- The local expansion and product telescoping hypotheses imply a universal
pointwise bound whenever `ν t / m ≤ c`, and hence the stated `O(ν²t²/m)`
global scaling as `m → ∞`. -/
theorem firstOrderLieTrotter_globalErrorScaling
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hLocal : LocalExpansionBound c C)
    (hTelescoping : ProductTelescopingEstimate) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (R : Register) (A B : HilbertOperator R),
        Matrix.IsHermitian A → Matrix.IsHermitian B →
          ∀ t : ℝ, 0 < t →
            Asymptotics.IsBigO atTop
              (globalError A B t) (globalErrorScale A B t)) ∧
      (∀ (R : Register) (A B : HilbertOperator R),
        Matrix.IsHermitian A → Matrix.IsHermitian B →
          ∀ (t : ℝ) (m : ℕ), 0 < t → 0 < m →
            hamiltonianScale A B * t / (m : ℝ) ≤ c →
              globalError A B t m ≤ K * globalErrorScale A B t m) := by
  let K := C * c + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hpoint :
      ∀ (R : Register) (A B : HilbertOperator R),
        Matrix.IsHermitian A → Matrix.IsHermitian B →
          ∀ (t : ℝ) (m : ℕ), 0 < t → 0 < m →
            hamiltonianScale A B * t / (m : ℝ) ≤ c →
              globalError A B t m ≤ K * globalErrorScale A B t m := by
    intro R A B hA hB t m ht hm hsmall
    have hτ : 0 ≤ t / (m : ℝ) := by positivity
    have hsmall' :
        hamiltonianScale A B * (t / (m : ℝ)) ≤ c := by
      simpa [div_eq_mul_inv, mul_assoc] using hsmall
    have hstep := oneStep_error_bound c C hC hLocal R A B hA hB
      (t / (m : ℝ)) hτ hsmall'
    have hU :
        ∀ j : Fin m,
          lieTrotterStep A B (t / (m : ℝ)) ∈
            Matrix.unitaryGroup R.Index ℂ := by
      intro j
      exact (Matrix.unitaryGroup R.Index ℂ).mul_mem
        (exponential_smul_hermitian_mem_unitary A hA _)
        (exponential_smul_hermitian_mem_unitary B hB _)
    have hV :
        ∀ j : Fin m,
          exactEvolution A B (t / (m : ℝ)) ∈
            Matrix.unitaryGroup R.Index ℂ := by
      intro j
      exact exponential_smul_hermitian_mem_unitary (A + B) (hA.add hB) _
    have htel := hTelescoping R m
      (fun _ : Fin m => lieTrotterStep A B (t / (m : ℝ)))
      (fun _ : Fin m => exactEvolution A B (t / (m : ℝ))) hU hV
    rw [reverseOrderedProduct_const, reverseOrderedProduct_const,
      exactEvolution_pow A B t m hm] at htel
    calc
      globalError A B t m =
          ‖lieTrotterStep A B (t / (m : ℝ)) ^ m -
            exactEvolution A B t‖ := rfl
      _ ≤ ∑ _ : Fin m,
          ‖lieTrotterStep A B (t / (m : ℝ)) -
            exactEvolution A B (t / (m : ℝ))‖ := htel
      _ = (m : ℝ) *
          ‖lieTrotterStep A B (t / (m : ℝ)) -
            exactEvolution A B (t / (m : ℝ))‖ := by simp
      _ ≤ (m : ℝ) *
          (K * hamiltonianScale A B ^ 2 * (t / (m : ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [K] using hstep
        · positivity
      _ = K * globalErrorScale A B t m := by
        rw [globalErrorScale]
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)]
  refine ⟨K, hK, ?_, hpoint⟩
  intro R A B hA hB t ht
  apply Asymptotics.IsBigO.of_bound K
  have hsmall :
      ∀ᶠ m : ℕ in atTop,
        hamiltonianScale A B * t / (m : ℝ) ≤ c := by
    have hlim :
        Tendsto (fun m : ℕ => hamiltonianScale A B * t / (m : ℝ))
          atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (hamiltonianScale A B * t)
    exact hlim.eventually (Iic_mem_nhds hc)
  filter_upwards [Nat.eventually_pos, hsmall] with m hm hsmallm
  have hbound := hpoint R A B hA hB t m ht hm hsmallm
  have hscale : 0 ≤ globalErrorScale A B t m := by
    rw [globalErrorScale]
    positivity
  have herror : 0 ≤ globalError A B t m := norm_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg herror,
    abs_of_nonneg hscale] using hbound

/-- A positive integer number of steps can be chosen with error at most every
`ε ∈ (0,1)` and with ceiling-robust size `1 + O(ν²t²/ε)`.  The additive one
only records that a step count is a positive integer (including when `ν=0`). -/
theorem firstOrderLieTrotter_sufficientStepCount
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hLocal : LocalExpansionBound c C)
    (hTelescoping : ProductTelescopingEstimate) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (R : Register) (A B : HilbertOperator R),
        Matrix.IsHermitian A → Matrix.IsHermitian B →
          ∀ (t ε : ℝ), 0 < t → ε ∈ Set.Ioo (0 : ℝ) 1 →
            ∃ m : ℕ,
              0 < m ∧
              hamiltonianScale A B * t / (m : ℝ) ≤ c ∧
              globalError A B t m ≤ ε ∧
              (m : ℝ) ≤ 1 + K *
                (hamiltonianScale A B ^ 2 * t ^ 2 / ε) := by
  obtain ⟨K₀, hK₀, _, hpoint⟩ :=
    firstOrderLieTrotter_globalErrorScaling c C hc hC hLocal hTelescoping
  let K := max K₀ (1 / c ^ 2)
  have hK : 0 < K := hK₀.trans_le (by simp [K])
  refine ⟨K, hK, ?_⟩
  intro R A B hA hB t ε ht hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hν : 0 ≤ hamiltonianScale A B := by
    rw [hamiltonianScale]
    exact le_max_of_le_left (norm_nonneg A)
  let q := K * (hamiltonianScale A B ^ 2 * t ^ 2 / ε)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  let m : ℕ := max 1 ⌈q⌉₊
  have hm : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_max_left 1 ⌈q⌉₊)
  have hqm : q ≤ (m : ℝ) := by
    calc
      q ≤ (⌈q⌉₊ : ℝ) := Nat.le_ceil q
      _ ≤ (m : ℕ) := by
        exact_mod_cast (le_max_right 1 ⌈q⌉₊)
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlocal :
      hamiltonianScale A B * t / (m : ℝ) ≤ c := by
    let x := hamiltonianScale A B * t
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    by_cases hxc : x ≤ c
    · apply (div_le_iff₀ hmreal).2
      calc
        x ≤ c := hxc
        _ ≤ c * (m : ℝ) := by nlinarith
    · have hcx : c < x := lt_of_not_ge hxc
      have hKc : 1 / c ^ 2 ≤ K := by simp [K]
      have hlinear_quadratic : x / c ≤ x ^ 2 / c ^ 2 := by
        rw [div_le_div_iff₀ hc (sq_pos_of_pos hc)]
        have hmul := mul_le_mul_of_nonneg_left hcx.le
          (mul_nonneg hx0 hc.le)
        nlinarith
      have hquadratic_K : x ^ 2 / c ^ 2 ≤ K * x ^ 2 := by
        calc
          x ^ 2 / c ^ 2 = (1 / c ^ 2) * x ^ 2 := by ring
          _ ≤ K * x ^ 2 :=
            mul_le_mul_of_nonneg_right hKc (sq_nonneg x)
      have hKx_div : K * x ^ 2 ≤ K * x ^ 2 / ε := by
        apply (le_div_iff₀ hε0).2
        exact mul_le_of_le_one_right (by positivity) hε1.le
      have hxq : x / c ≤ q := by
        calc
          x / c ≤ x ^ 2 / c ^ 2 := hlinear_quadratic
          _ ≤ K * x ^ 2 := hquadratic_K
          _ ≤ K * x ^ 2 / ε := hKx_div
          _ = q := by
            dsimp [x, q]
            ring
      apply (div_le_iff₀ hmreal).2
      have hxm : x / c ≤ (m : ℝ) := hxq.trans hqm
      have := (div_le_iff₀ hc).1 hxm
      nlinarith
  have hthreshold :
      K₀ * (hamiltonianScale A B ^ 2 * t ^ 2) / ε ≤ (m : ℝ) := by
    calc
      K₀ * (hamiltonianScale A B ^ 2 * t ^ 2) / ε ≤
          K * (hamiltonianScale A B ^ 2 * t ^ 2) / ε := by
        gcongr
        exact le_max_left _ _
      _ = q := by
        dsimp [q]
        ring
      _ ≤ (m : ℝ) := hqm
  have herr := hpoint R A B hA hB t m ht hm hlocal
  have herrε : globalError A B t m ≤ ε := by
    apply herr.trans
    rw [globalErrorScale]
    calc
      K₀ * (hamiltonianScale A B ^ 2 * t ^ 2 / (m : ℝ)) =
          (K₀ * (hamiltonianScale A B ^ 2 * t ^ 2)) / (m : ℝ) := by
        ring
      _ ≤ ε := by
        apply (div_le_iff₀ hmreal).2
        have := (div_le_iff₀ hε0).1 hthreshold
        nlinarith
  refine ⟨m, hm, hlocal, herrε, ?_⟩
  change (m : ℝ) ≤ 1 + q
  dsimp [m]
  push_cast
  exact max_le (by linarith) (by
    simpa [add_comm] using (Nat.ceil_lt_add_one hq).le)

/-- For nonzero Hamiltonian scale, the positive integer step choices can be
packaged as a function with the literal requested asymptotic
`m = O(ν²t²/ε)` as `ε → 0⁺`, while satisfying the local-step condition and
the error guarantee for every `ε ∈ (0,1)`. -/
theorem firstOrderLieTrotter_sufficientStepCount_isBigO
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hLocal : LocalExpansionBound c C)
    (hTelescoping : ProductTelescopingEstimate)
    (R : Register) (A B : HilbertOperator R)
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (t : ℝ) (ht : 0 < t) (hν : 0 < hamiltonianScale A B) :
    ∃ steps : ℝ → ℕ,
      StepCountIsBigO A B t steps ∧
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
        0 < steps ε ∧
        hamiltonianScale A B * t / (steps ε : ℝ) ≤ c ∧
        globalError A B t (steps ε) ≤ ε := by
  obtain ⟨K, hK, hchoose⟩ :=
    firstOrderLieTrotter_sufficientStepCount c C hc hC hLocal hTelescoping
  classical
  let steps : ℝ → ℕ := fun ε =>
    if hε : ε ∈ Set.Ioo (0 : ℝ) 1 then
      Classical.choose (hchoose R A B hA hB t ε ht hε)
    else 1
  have hsteps (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
      0 < steps ε ∧
      hamiltonianScale A B * t / (steps ε : ℝ) ≤ c ∧
      globalError A B t (steps ε) ≤ ε ∧
      (steps ε : ℝ) ≤ 1 + K *
        (hamiltonianScale A B ^ 2 * t ^ 2 / ε) := by
    simp only [steps, dif_pos hε]
    exact Classical.choose_spec (hchoose R A B hA hB t ε ht hε)
  refine ⟨steps, ?_, ?_⟩
  · rw [StepCountIsBigO]
    apply Asymptotics.IsBigO.of_bound (1 + K)
    have hscaleSq : 0 < hamiltonianScale A B ^ 2 * t ^ 2 := by
      positivity
    have heps_pos :
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hε
    have heps_lt_one :
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1 := by
      exact (show ∀ᶠ ε : ℝ in nhds 0, ε < 1 from
        Iio_mem_nhds zero_lt_one).filter_mono inf_le_left
    have heps_le_scale :
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ε ≤ hamiltonianScale A B ^ 2 * t ^ 2 := by
      exact (show
        ∀ᶠ ε : ℝ in nhds 0,
          ε ≤ hamiltonianScale A B ^ 2 * t ^ 2 from
        Iic_mem_nhds hscaleSq).filter_mono inf_le_left
    filter_upwards [heps_pos, heps_lt_one, heps_le_scale] with
      ε hε0 hε1 hεscale
    have hbound := (hsteps ε ⟨hε0, hε1⟩).2.2.2
    have hratio0 :
        0 ≤ hamiltonianScale A B ^ 2 * t ^ 2 / ε := by positivity
    have hratio1 :
        1 ≤ hamiltonianScale A B ^ 2 * t ^ 2 / ε := by
      exact (le_div_iff₀ hε0).2 (by simpa using hεscale)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (steps ε : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg hratio0]
    calc
      (steps ε : ℝ) ≤
          1 + K * (hamiltonianScale A B ^ 2 * t ^ 2 / ε) := hbound
      _ ≤ (1 + K) *
          (hamiltonianScale A B ^ 2 * t ^ 2 / ε) := by
        nlinarith
  · intro ε hε
    exact ⟨(hsteps ε hε).1, (hsteps ε hε).2.1, (hsteps ε hε).2.2.1⟩

end

end FirstOrderLieTrotterGlobalErrorScaling
end QAlgFormalized
