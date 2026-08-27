import QAlgBench.Base
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Unitarity of the finite quantum Fourier transform

This file formalizes the normalized quantum Fourier transform on the
`M`-dimensional computational register and states its unitarity for `M > 0`.
-/

namespace QAlgBench

noncomputable section

namespace FiniteQFTUnitarity

/-- The `M`-dimensional computational register, with basis labels `0, ..., M - 1`. -/
abbrev qftRegister (M : ℕ) : QAlgBench.Register where
  Index := Fin M
  fintype := inferInstance
  decEq := inferInstance

/-- The primitive phase `ω_M = exp (2πi / M)` used by the finite QFT. -/
def rootOfUnity (M : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / M)

/--
The normalized finite quantum Fourier transform.  Its row index is the output
basis label `y`, and its column index is the input basis label `x`.
-/
def qftMatrix (M : ℕ) : HilbertOperator (qftRegister M) :=
  fun y x => (Real.sqrt M : ℂ)⁻¹ * rootOfUnity M ^ (x.val * y.val)

private theorem rootOfUnity_isPrimitive {M : ℕ} (hM : 0 < M) :
    IsPrimitiveRoot (rootOfUnity M) M := by
  simpa [rootOfUnity, mul_assoc] using
    (Complex.isPrimitiveRoot_exp M (Nat.ne_of_gt hM))

private theorem star_rootOfUnity (M : ℕ) :
    starRingEnd ℂ (rootOfUnity M) = (rootOfUnity M)⁻¹ := by
  rw [rootOfUnity, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  norm_num [map_ofNat]
  ring

private theorem qft_orthogonality {M : ℕ} (hM : 0 < M) (i j : Fin M) :
    ∑ k : Fin M,
        starRingEnd ℂ (rootOfUnity M ^ (i.val * k.val)) *
          rootOfUnity M ^ (j.val * k.val) =
      if i = j then (M : ℂ) else 0 := by
  let ω := rootOfUnity M
  have hω : IsPrimitiveRoot ω M := rootOfUnity_isPrimitive hM
  have hstar : starRingEnd ℂ ω = ω⁻¹ := star_rootOfUnity M
  have hterm (k : Fin M) :
      starRingEnd ℂ (ω ^ (i.val * k.val)) * ω ^ (j.val * k.val) =
        (starRingEnd ℂ (ω ^ i.val) * ω ^ j.val) ^ k.val := by
    rw [mul_pow, ← map_pow, pow_mul, pow_mul]
  change (∑ k : Fin M,
    starRingEnd ℂ (ω ^ (i.val * k.val)) * ω ^ (j.val * k.val)) =
      if i = j then (M : ℂ) else 0
  simp_rw [hterm]
  split_ifs with hij
  · subst j
    have hω0 : ω ≠ 0 := hω.ne_zero (Nat.ne_of_gt hM)
    have hi0 : ω ^ i.val ≠ 0 := pow_ne_zero _ hω0
    have hbase : starRingEnd ℂ (ω ^ i.val) * ω ^ i.val = 1 := by
      rw [map_pow, hstar, inv_pow, inv_mul_cancel₀ hi0]
    rw [hbase]
    simp
  · have hz_ne : starRingEnd ℂ (ω ^ i.val) * ω ^ j.val ≠ 1 := by
      rw [map_pow, hstar, inv_pow]
      intro hz
      have hω0 : ω ≠ 0 := hω.ne_zero (Nat.ne_of_gt hM)
      have hpows : ω ^ i.val = ω ^ j.val :=
        (inv_mul_eq_one₀ (pow_ne_zero _ hω0)).mp hz
      exact hij (Fin.ext (hω.pow_inj i.isLt j.isLt hpows))
    have hz_pow : (starRingEnd ℂ (ω ^ i.val) * ω ^ j.val) ^ M = 1 := by
      rw [mul_pow, ← map_pow]
      rw [← pow_mul, ← pow_mul]
      rw [Nat.mul_comm i.val M, Nat.mul_comm j.val M]
      rw [pow_mul, pow_mul, hω.pow_eq_one]
      simp
    rw [Fin.sum_univ_eq_sum_range]
    rw [geom_sum_eq hz_ne M, hz_pow]
    simp

/-- The matrix definition has the advertised action on a computational-basis ket. -/
theorem qftMatrix_apply_ket (M : ℕ) (x : Fin M) :
    HilbertOperator.applyVec (qftMatrix M)
        (PureState.ket (R := qftRegister M) x : StateVector (qftRegister M)) =
      (Real.sqrt M : ℂ)⁻¹ •
        ∑ y : Fin M, rootOfUnity M ^ (x.val * y.val) •
          (PureState.ket (R := qftRegister M) y : StateVector (qftRegister M)) := by
  ext i
  rw [HilbertOperator.applyVec_ket]
  simp [qftMatrix, PureState.ket_apply]

/-- For every positive dimension, the finite quantum Fourier transform is unitary. -/
theorem qftMatrix_mem_unitaryGroup {M : ℕ} (hM : 0 < M) :
    qftMatrix M ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, qftMatrix]
  change (∑ x : Fin M,
      starRingEnd ℂ ((Real.sqrt M : ℂ)⁻¹ *
        rootOfUnity M ^ (i.val * x.val)) *
        ((Real.sqrt M : ℂ)⁻¹ * rootOfUnity M ^ (j.val * x.val))) =
    if i = j then 1 else 0
  have hterm (x : Fin M) :
      starRingEnd ℂ ((Real.sqrt M : ℂ)⁻¹ *
          rootOfUnity M ^ (i.val * x.val)) *
          ((Real.sqrt M : ℂ)⁻¹ * rootOfUnity M ^ (j.val * x.val)) =
        ((Real.sqrt M : ℂ)⁻¹ * (Real.sqrt M : ℂ)⁻¹) *
          (starRingEnd ℂ (rootOfUnity M ^ (i.val * x.val)) *
            rootOfUnity M ^ (j.val * x.val)) := by
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, qft_orthogonality hM i j]
  have hnorm :
      (Real.sqrt M : ℂ)⁻¹ * (Real.sqrt M : ℂ)⁻¹ * (M : ℂ) = 1 := by
    have hsqrt : (Real.sqrt M : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.2 hM)).ne'
    have hsqrt_sq :
        (Real.sqrt M : ℂ) * (Real.sqrt M : ℂ) = (M : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (Nat.cast_nonneg M)
    rw [← hsqrt_sq]
    field_simp
  by_cases hij : i = j
  · simpa [hij] using hnorm
  · simp [hij]

end FiniteQFTUnitarity

end

end QAlgBench
