/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

import QAlgBench.Base

/-!
# Exact phase estimation on a superposition of two eigenvectors

This file models the state immediately before measurement in quantum phase
estimation by its inverse-Fourier sum.  The target register consists of `m`
qubits and the counting register consists of `n` qubits.
-/

@[expose] public section

namespace QAlgFormalized.QPESuperpositionExactEigenvectors

open QAlgBench

noncomputable section

/-- The unit-modulus eigenvalue associated with the real phase `φ`. -/
def phaseEigenvalue (φ : ℝ) : ℂ :=
  Complex.exp ((((2 : ℝ) * Real.pi * φ : ℝ) : ℂ) * Complex.I)

/--
The coefficient of `|y⟩` in the inverse quantum Fourier transform of `|x⟩`,
including one factor of `1 / sqrt (2^n)` from the initial uniform
superposition and one from the inverse Fourier transform.
-/
def inverseQFTCoefficient (n : ℕ) (x y : Fin (2 ^ n)) : ℂ :=
  (((2 ^ n : ℕ) : ℂ)⁻¹) *
    Complex.exp
      (((((-2 : ℝ) * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
          ((2 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)

/--
The joint counting-target state produced by phase estimation immediately
before measurement.  The inner sum is the target state controlled by the
counting value `x`; the outer sum applies the inverse quantum Fourier
transform to the counting register.
-/
def preMeasurementState (n m : ℕ) (U : Gate (Qubits m))
    (ψ : StateVector (Qubits m)) : StateVector (Qubits (n + m)) :=
  ∑ y : Fin (2 ^ n),
    StateVector.tensor
      ((PureState.ket y : PureState (Qubits n)) : StateVector (Qubits n))
      (∑ x : Fin (2 ^ n),
        inverseQFTCoefficient n x y • (U ^ x.val).applyVec ψ)

/--
If the target is a normalized superposition of two orthonormal eigenvectors
whose phases have exact `n`-bit labels, quantum phase estimation correlates
each eigenvector with its corresponding computational-basis phase label.
-/
theorem qpe_superposition_exact_eigenvectors
    {n m : ℕ}
    (U : Gate (Qubits m))
    (u₁ u₂ : PureState (Qubits m))
    (φ₁ φ₂ : ℝ)
    (k₁ k₂ : Fin (2 ^ n))
    (α β : ℂ)
    (ψ : PureState (Qubits m))
    (h_orthogonal :
      inner ℂ (u₁ : StateVector (Qubits m)) (u₂ : StateVector (Qubits m)) = 0)
    (h_eigen₁ :
      U.applyVec (u₁ : StateVector (Qubits m)) =
        phaseEigenvalue φ₁ • (u₁ : StateVector (Qubits m)))
    (h_eigen₂ :
      U.applyVec (u₂ : StateVector (Qubits m)) =
        phaseEigenvalue φ₂ • (u₂ : StateVector (Qubits m)))
    (h_exact₁ :
      ((2 ^ n : ℕ) : ℝ) * φ₁ = (k₁.val : ℝ))
    (h_exact₂ :
      ((2 ^ n : ℕ) : ℝ) * φ₂ = (k₂.val : ℝ))
    (h_coefficients_normalized :
      Complex.normSq α + Complex.normSq β = 1)
    (h_target :
      (ψ : StateVector (Qubits m)) =
        α • (u₁ : StateVector (Qubits m)) +
          β • (u₂ : StateVector (Qubits m))) :
    preMeasurementState n m U (ψ : StateVector (Qubits m)) =
      α • StateVector.tensor
          ((PureState.ket k₁ : PureState (Qubits n)) : StateVector (Qubits n))
          (u₁ : StateVector (Qubits m)) +
        β • StateVector.tensor
          ((PureState.ket k₂ : PureState (Qubits n)) : StateVector (Qubits n))
          (u₂ : StateVector (Qubits m)) := by
  classical
  have h_power₁ (x : ℕ) :
      (U ^ x).applyVec (u₁ : StateVector (Qubits m)) =
        phaseEigenvalue φ₁ ^ x • (u₁ : StateVector (Qubits m)) := by
    induction x with
    | zero => simp
    | succ x ih =>
        rw [pow_succ, Gate.mul_applyVec, h_eigen₁, Gate.applyVec_smul,
          ih, smul_smul]
        congr 1
        ring
  have h_power₂ (x : ℕ) :
      (U ^ x).applyVec (u₂ : StateVector (Qubits m)) =
        phaseEigenvalue φ₂ ^ x • (u₂ : StateVector (Qubits m)) := by
    induction x with
    | zero => simp
    | succ x ih =>
        rw [pow_succ, Gate.mul_applyVec, h_eigen₂, Gate.applyVec_smul,
          ih, smul_smul]
        congr 1
        ring
  have h_fourier (φ : ℝ) (k : Fin (2 ^ n))
      (h_exact : ((2 ^ n : ℕ) : ℝ) * φ = (k.val : ℝ))
      (y : Fin (2 ^ n)) :
      (∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y * phaseEigenvalue φ ^ x.val) =
        if y = k then 1 else 0 := by
    have h_term (x : Fin (2 ^ n)) :
        inverseQFTCoefficient n x y * phaseEigenvalue φ ^ x.val =
          (((2 ^ n : ℕ) : ℂ)⁻¹) *
            Complex.exp
                (((2 * Real.pi * ((k.val : ℝ) - (y.val : ℝ)) /
                  ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) ^ x.val := by
      unfold inverseQFTCoefficient phaseEigenvalue
      have h_real :
          (-2 : ℝ) * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
                ((2 ^ n : ℕ) : ℝ) +
              (x.val : ℝ) * (2 * Real.pi * φ) =
            (x.val : ℝ) *
              (2 * Real.pi * ((k.val : ℝ) - (y.val : ℝ)) /
                ((2 ^ n : ℕ) : ℝ)) := by
        have h_nonzero : (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
        ring_nf at h_exact ⊢
        nlinarith
      calc
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) *
            (Complex.exp
                (((((-2 : ℝ) * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
                  ((2 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) *
              Complex.exp
                ((x.val : ℂ) *
                  ((((2 : ℝ) * Real.pi * φ : ℝ) : ℂ) * Complex.I))) := by
              rw [Complex.exp_nat_mul]
              ring
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) *
            Complex.exp
              (((((-2 : ℝ) * Real.pi * (x.val : ℝ) * (y.val : ℝ) /
                  ((2 ^ n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I +
                (x.val : ℂ) *
                  ((((2 : ℝ) * Real.pi * φ : ℝ) : ℂ) * Complex.I)) := by
              rw [Complex.exp_add]
        _ = (((2 ^ n : ℕ) : ℂ)⁻¹) *
            Complex.exp
              ((x.val : ℂ) *
                (((2 * Real.pi * ((k.val : ℝ) - (y.val : ℝ)) /
                  ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) := by
              congr 2
              push_cast
              convert congrArg
                (fun r : ℝ => (r : ℂ) * Complex.I) h_real using 1 <;>
                  push_cast <;> ring
        _ = _ := by rw [Complex.exp_nat_mul]
    simp_rw [h_term]
    by_cases hyk : y = k
    · subst y
      simp
    · simp only [hyk, ↓reduceIte]
      let q : ℂ :=
        Complex.exp
          (((2 * Real.pi * ((k.val : ℝ) - (y.val : ℝ)) /
            ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
      change
        ∑ x : Fin (2 ^ n), (((2 ^ n : ℕ) : ℂ)⁻¹) * q ^ x.val = 0
      rw [← Finset.mul_sum]
      suffices (∑ x : Fin (2 ^ n), q ^ x.val) = 0 by
        rw [this, mul_zero]
      rw [Fin.sum_univ_eq_sum_range]
      have h_q_nat :
          q =
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I *
                ((k.val + 2 ^ n - y.val : ℕ) : ℂ) /
                  ((2 ^ n : ℕ) : ℂ)) := by
        dsimp [q]
        have hy : y.val ≤ k.val + 2 ^ n := by omega
        have h_cast :
            ((k.val + 2 ^ n - y.val : ℕ) : ℂ) =
              (k.val : ℂ) + ((2 ^ n : ℕ) : ℂ) - (y.val : ℂ) := by
          rw [Nat.cast_sub hy]
          push_cast
          ring
        rw [h_cast]
        have h_argument :
            2 * (Real.pi : ℂ) * Complex.I *
                  ((k.val : ℂ) + ((2 ^ n : ℕ) : ℂ) - (y.val : ℂ)) /
                    ((2 ^ n : ℕ) : ℂ) =
                (((2 * Real.pi * ((k.val : ℝ) - (y.val : ℝ)) /
                  ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
                  2 * (Real.pi : ℂ) * Complex.I := by
          push_cast
          field_simp
          ring
        rw [h_argument, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      have h_q_pow : q ^ (2 ^ n) = 1 := by
        rw [h_q_nat, ← Complex.exp_nat_mul]
        rw [show
          ((2 ^ n : ℕ) : ℂ) *
                (2 * (Real.pi : ℂ) * Complex.I *
                  ((k.val + 2 ^ n - y.val : ℕ) : ℂ) /
                    ((2 ^ n : ℕ) : ℂ)) =
              ((k.val + 2 ^ n - y.val : ℕ) : ℂ) *
                (2 * (Real.pi : ℂ) * Complex.I) by
                  field_simp]
        exact
          Complex.exp_nat_mul_two_pi_mul_I
            (k.val + 2 ^ n - y.val)
      have h_q_ne : q ≠ 1 := by
        rw [h_q_nat]
        have h_pos : 0 < 2 ^ n := by positivity
        have h_nonzero : 2 ^ n ≠ 0 := h_pos.ne'
        have h_dvd :
            2 ^ n ∣ k.val + 2 ^ n - y.val ↔ k = y := by
          constructor
          · rintro ⟨c, hc⟩
            have hk := k.isLt
            have hy := y.isLt
            have h_diff_pos : 0 < k.val + 2 ^ n - y.val := by omega
            have h_diff_lt :
                k.val + 2 ^ n - y.val < 2 * (2 ^ n) := by
              omega
            have hc_pos : 0 < c := by
              by_contra hc_zero
              have : c = 0 := Nat.eq_zero_of_not_pos hc_zero
              simp [this] at hc
              omega
            have hc_lt : c < 2 := by nlinarith
            have hc_one : c = 1 := by omega
            subst c
            simp at hc
            apply Fin.ext
            omega
          · intro h
            subst y
            simp
        rw [ne_eq,
          Complex.exp_two_pi_mul_I_mul_div_eq_one_iff h_nonzero, h_dvd]
        exact Ne.symm hyk
      have h_geometric := geom_sum_mul q (2 ^ n)
      rw [h_q_pow, sub_self] at h_geometric
      exact
        (mul_eq_zero.mp h_geometric).resolve_right
          (sub_ne_zero.mpr h_q_ne)
  have h_inner (y : Fin (2 ^ n)) :
      (∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y •
            (U ^ x.val).applyVec (ψ : StateVector (Qubits m))) =
        (if y = k₁ then α • (u₁ : StateVector (Qubits m)) else 0) +
          (if y = k₂ then β • (u₂ : StateVector (Qubits m)) else 0) := by
    simp_rw [h_target, Gate.applyVec_add, Gate.applyVec_smul,
      h_power₁, h_power₂, smul_add, smul_smul]
    rw [Finset.sum_add_distrib]
    rw [← Finset.sum_smul, ← Finset.sum_smul]
    rw [show
      (∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y *
            (α * phaseEigenvalue φ₁ ^ x.val)) =
        α * ∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y *
            phaseEigenvalue φ₁ ^ x.val by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring]
    rw [show
      (∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y *
            (β * phaseEigenvalue φ₂ ^ x.val)) =
        β * ∑ x : Fin (2 ^ n),
          inverseQFTCoefficient n x y *
            phaseEigenvalue φ₂ ^ x.val by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              ring]
    rw [h_fourier φ₁ k₁ h_exact₁, h_fourier φ₂ k₂ h_exact₂]
    split_ifs <;> simp
  unfold preMeasurementState
  simp_rw [h_inner, StateVector.tensor_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · calc
      (∑ y : Fin (2 ^ n),
          StateVector.tensor
            ((PureState.ket y : PureState (Qubits n)) :
              StateVector (Qubits n))
            (if y = k₁ then
              α • (u₁ : StateVector (Qubits m)) else 0)) =
        ∑ y : Fin (2 ^ n), if y = k₁ then
          α • StateVector.tensor
            ((PureState.ket y : PureState (Qubits n)) :
              StateVector (Qubits n))
            (u₁ : StateVector (Qubits m)) else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              split_ifs with h
              · rw [StateVector.tensor_smul]
              · rw [StateVector.tensor_zero]
      _ = _ := Fintype.sum_ite_eq' k₁ _
  · calc
      (∑ y : Fin (2 ^ n),
          StateVector.tensor
            ((PureState.ket y : PureState (Qubits n)) :
              StateVector (Qubits n))
            (if y = k₂ then
              β • (u₂ : StateVector (Qubits m)) else 0)) =
        ∑ y : Fin (2 ^ n), if y = k₂ then
          β • StateVector.tensor
            ((PureState.ket y : PureState (Qubits n)) :
              StateVector (Qubits n))
            (u₂ : StateVector (Qubits m)) else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              split_ifs with h
              · rw [StateVector.tensor_smul]
              · rw [StateVector.tensor_zero]
      _ = _ := Fintype.sum_ite_eq' k₂ _

end

end QAlgFormalized.QPESuperpositionExactEigenvectors
