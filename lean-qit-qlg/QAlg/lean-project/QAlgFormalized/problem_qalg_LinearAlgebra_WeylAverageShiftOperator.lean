import QAlgBench.Base

/-!
# Weyl average of the finite cyclic shift

This file formalizes the clock and shift matrices on `ℂ^d` and the averaging
map from the benchmark statement.  In particular, the order

`Z^j X^k U (Z^j)⁻¹ (X^k)⁻¹`

is intentional: it is the order stated in the source, rather than ordinary
conjugation by `Z^j X^k`.
-/

namespace QAlgFormalized

noncomputable section

/-- The primitive `d`-th root of unity `ω = exp (2πi / d)`. -/
def weylRoot (d : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The clock matrix `Z = ∑ j, ω^j |j⟩⟨j|` in the computational basis. -/
def weylClock (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j => weylRoot d ^ j.val

/-- The cyclic shift matrix `X = ∑ j, |j+1 mod d⟩⟨j|`. -/
def weylShift (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun row col => if row.val = (col.val + 1) % d then 1 else 0

/-- The average from the source, preserving its multiplication order:
`d⁻¹ ∑ j k, Z^j X^k U Z⁻j X⁻k`.

Since matrices carry Mathlib's nonsingular inverse rather than integer powers,
the negative powers are written explicitly as inverses of natural powers.
-/
def weylAverage (d : ℕ) (Z X U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ)⁻¹) •
    ∑ j : Fin d, ∑ k : Fin d,
      Z ^ j.val * X ^ k.val * U * (Z ^ j.val)⁻¹ * (X ^ k.val)⁻¹

private lemma weylRoot_pow_d (d : ℕ) (hd : d ≠ 0) :
    weylRoot d ^ d = 1 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [weylRoot, ← Complex.exp_nat_mul]
  rw [show (d : ℂ) *
      (((2 * Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I by
    push_cast
    field_simp [hdC]]
  exact Complex.exp_two_pi_mul_I

private lemma weylRoot_pow_ne_one (d m : ℕ) (hd : d ≠ 0)
    (hm0 : 0 < m) (hmd : m < d) :
    weylRoot d ^ m ≠ 1 := by
  intro h
  rw [weylRoot, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
  rcases h with ⟨n, hn⟩
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    add_zero, zero_mul, sub_zero] at him
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmdR : (m : ℝ) < d := by exact_mod_cast hmd
  have hnreal : (n : ℝ) = (m : ℝ) / d := by
    apply
      (mul_left_cancel₀
        (ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)))
    field_simp at him ⊢
    nlinarith [Real.pi_pos]
  have hnposR : (0 : ℝ) < n := by
    rw [hnreal]
    exact div_pos hmR hdR
  have hnltR : (n : ℝ) < 1 := by
    rw [hnreal]
    exact (div_lt_one hdR).2 hmdR
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hnposR
  have hnlt : n < (1 : ℤ) := by exact_mod_cast hnltR
  omega

private lemma weylRoot_succ_mod (d n : ℕ) (hd : d ≠ 0) (hn : n < d) :
    weylRoot d ^ ((n + 1) % d) = weylRoot d * weylRoot d ^ n := by
  by_cases h : n + 1 < d
  · rw [Nat.mod_eq_of_lt h, pow_succ']
  · have heq : n + 1 = d := by omega
    rw [heq, Nat.mod_self, pow_zero, ← pow_succ', heq,
      weylRoot_pow_d d hd]

private lemma sum_weylRoot_pow_mul_eq_zero (d m : ℕ) (hd : d ≠ 0)
    (hm0 : 0 < m) (hmd : m < d) :
    (∑ j : Fin d, weylRoot d ^ (j.val * m)) = 0 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => weylRoot d ^ (j * m)) d]
  simp_rw [mul_comm _ m, pow_mul]
  have hqpow : (weylRoot d ^ m) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, weylRoot_pow_d d hd, one_pow]
  have hgeom := geom_sum_mul (weylRoot d ^ m) d
  rw [hqpow, sub_self] at hgeom
  rcases mul_eq_zero.mp hgeom with hsum | hq
  · exact hsum
  · exact False.elim
      ((sub_ne_zero.mpr (weylRoot_pow_ne_one d m hd hm0 hmd)) hq)

private lemma sum_weylRoot_pow_mul_eq_d (d : ℕ) (hd : d ≠ 0) :
    (∑ j : Fin d, weylRoot d ^ (j.val * d)) = (d : ℂ) := by
  simp_rw [mul_comm _ d, pow_mul, weylRoot_pow_d d hd, one_pow]
  simp [nsmul_eq_mul]

private def weylPredPerm (d : ℕ) [NeZero d] : Equiv.Perm (Fin d) :=
  Equiv.addRight (-1 : Fin d)

private lemma weylShift_eq_permMatrix (d : ℕ) (hd : 2 ≤ d) [NeZero d] :
    weylShift d = (weylPredPerm d).permMatrix ℂ := by
  ext row col
  have hone : (1 : Fin d).val = 1 := by
    change 1 % d = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc : row.val = (col.val + 1) % d ↔ row = col + 1 := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [Fin.val_add, hone] using h
    · intro h
      rw [h, Fin.val_add, hone]
  have hpred : row = col + 1 ↔ row + (-1 : Fin d) = col := by
    constructor
    · rintro rfl
      simp
    · intro h
      calc
        row = (row + (-1 : Fin d)) + 1 := by simp
        _ = col + 1 := by rw [h]
  simp only [weylShift, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, weylPredPerm, Option.mem_def,
    Option.some.injEq]
  simp only [hsucc, hpred]
  rfl

private lemma matrix_commute_pow (Z X : Matrix (Fin d) (Fin d) ℂ) (c : ℂ)
    (hZX : Z * X = c • (X * Z)) (j n : ℕ) :
    Z ^ j * X ^ n = c ^ (j * n) • (X ^ n * Z ^ j) := by
  have hone : Z ^ j * X = c ^ j • (X * Z ^ j) := by
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          Z ^ (j + 1) * X = Z ^ j * (Z * X) := by
            rw [pow_succ, Matrix.mul_assoc]
          _ = Z ^ j * (c • (X * Z)) := by rw [hZX]
          _ = c • ((Z ^ j * X) * Z) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
          _ = c • ((c ^ j • (X * Z ^ j)) * Z) := by rw [ih]
          _ = c ^ (j + 1) • (X * Z ^ (j + 1)) := by
            rw [Matrix.smul_mul, smul_smul, pow_succ, pow_succ,
              mul_comm c, Matrix.mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Z ^ j * X ^ (n + 1) = (Z ^ j * X ^ n) * X := by
          rw [pow_succ, Matrix.mul_assoc]
        _ = (c ^ (j * n) • (X ^ n * Z ^ j)) * X := by rw [ih]
        _ = c ^ (j * n) • (X ^ n * (Z ^ j * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = c ^ (j * n) • (X ^ n * (c ^ j • (X * Z ^ j))) := by
          rw [hone]
        _ = c ^ (j * (n + 1)) • (X ^ (n + 1) * Z ^ j) := by
          rw [Matrix.mul_smul, smul_smul, pow_succ, ← Matrix.mul_assoc]
          congr 1
          rw [← pow_add]
          ring

private lemma addRight_pow {G : Type*} [AddCommGroup G] (a : G) (n : ℕ) :
    (Equiv.addRight a) ^ n = Equiv.addRight (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Equiv.addRight_add]
      apply congrArg Equiv.addRight
      simpa [add_comm] using (succ_nsmul a n).symm

private lemma weylPredPerm_pow_d (d : ℕ) [NeZero d] :
    (weylPredPerm d) ^ d = 1 := by
  rw [weylPredPerm, addRight_pow]
  rw [show d • (-1 : Fin d) = 0 by
    simpa using (@card_nsmul_eq_zero (Fin d) _ _ (-1 : Fin d))]
  exact Equiv.addRight_zero

private lemma permMatrix_nonsing_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (σ.permMatrix ℂ)⁻¹ = (σ⁻¹).permMatrix ℂ := by
  have hdet : IsUnit ((σ.permMatrix ℂ).det) := by
    rw [Matrix.det_permutation, isUnit_iff_ne_zero]
    exact_mod_cast (Units.ne_zero (Equiv.Perm.sign σ))
  have hleft : (σ⁻¹).permMatrix ℂ * σ.permMatrix ℂ = 1 := by
    simpa using (Matrix.permMatrix_mul σ (σ⁻¹) (R := ℂ)).symm
  calc
    (σ.permMatrix ℂ)⁻¹ = 1 * (σ.permMatrix ℂ)⁻¹ := by
      rw [Matrix.one_mul]
    _ = ((σ⁻¹).permMatrix ℂ * σ.permMatrix ℂ) *
        (σ.permMatrix ℂ)⁻¹ := by rw [hleft]
    _ = (σ⁻¹).permMatrix ℂ *
        (σ.permMatrix ℂ * (σ.permMatrix ℂ)⁻¹) :=
      Matrix.mul_assoc _ _ _
    _ = (σ⁻¹).permMatrix ℂ := by
      rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

private lemma permMatrix_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (n : ℕ) :
    (σ.permMatrix ℂ) ^ n = (σ ^ n).permMatrix ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Matrix.permMatrix_mul, ← pow_succ']

/-- The finite clock and cyclic shift obey `ZX = ω XZ`. -/
theorem weylClock_mul_weylShift (d : ℕ) (hd : 2 ≤ d) :
    weylClock d * weylShift d =
      weylRoot d • (weylShift d * weylClock d) := by
  ext row col
  simp only [weylClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply]
  simp only [weylShift, smul_eq_mul]
  by_cases h : row.val = (col.val + 1) % d
  · simp only [h, if_true, mul_one, one_mul]
    exact weylRoot_succ_mod d col.val (by omega) col.isLt
  · simp only [h, if_false, mul_zero, zero_mul]

/-- The individual summands in the source-ordered average at `U = X`. -/
theorem weylAverage_shift_summand (d : ℕ) (hd : 2 ≤ d) (j k : Fin d) :
    weylClock d ^ j.val * weylShift d ^ k.val * weylShift d *
          (weylClock d ^ j.val)⁻¹ * (weylShift d ^ k.val)⁻¹ =
      weylRoot d ^ (j.val * (k.val + 1)) • weylShift d := by
  have hZbase : IsUnit (weylClock d).det := by
    rw [weylClock, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (Complex.exp_ne_zero _)
  have hZ : IsUnit (weylClock d ^ j.val).det := by
    rw [Matrix.det_pow]
    exact hZbase.pow _
  letI : NeZero d := ⟨by omega⟩
  have hshift := weylShift_eq_permMatrix d hd
  have hXbase : IsUnit (weylShift d).det := by
    rw [hshift, Matrix.det_permutation, isUnit_iff_ne_zero]
    exact_mod_cast
      (Units.ne_zero (Equiv.Perm.sign (weylPredPerm d)))
  have hX : IsUnit (weylShift d ^ k.val).det := by
    rw [Matrix.det_pow]
    exact hXbase.pow _
  calc
    weylClock d ^ j.val * weylShift d ^ k.val * weylShift d *
          (weylClock d ^ j.val)⁻¹ * (weylShift d ^ k.val)⁻¹ =
        (weylClock d ^ j.val * weylShift d ^ (k.val + 1)) *
          (weylClock d ^ j.val)⁻¹ *
          (weylShift d ^ k.val)⁻¹ := by
      simp only [Matrix.mul_assoc, pow_succ]
    _ = (weylRoot d ^ (j.val * (k.val + 1)) •
          (weylShift d ^ (k.val + 1) * weylClock d ^ j.val)) *
          (weylClock d ^ j.val)⁻¹ *
          (weylShift d ^ k.val)⁻¹ := by
      rw [matrix_commute_pow _ _ _ (weylClock_mul_weylShift d hd)]
    _ = weylRoot d ^ (j.val * (k.val + 1)) •
          (weylShift d ^ (k.val + 1) *
            (weylClock d ^ j.val * (weylClock d ^ j.val)⁻¹) *
            (weylShift d ^ k.val)⁻¹) := by
      simp only [Matrix.smul_mul, Matrix.mul_assoc]
    _ = weylRoot d ^ (j.val * (k.val + 1)) •
          (weylShift d ^ (k.val + 1) *
            (weylShift d ^ k.val)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hZ, Matrix.mul_one]
    _ = weylRoot d ^ (j.val * (k.val + 1)) • weylShift d := by
      rw [pow_succ', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX,
        Matrix.mul_one]

/-- Explicit unnormalized evaluation of the double sum at `U = X`. -/
theorem weylAverage_shift_double_sum (d : ℕ) (hd : 2 ≤ d) :
    (∑ j : Fin d, ∑ k : Fin d,
        weylClock d ^ j.val * weylShift d ^ k.val * weylShift d *
          (weylClock d ^ j.val)⁻¹ * (weylShift d ^ k.val)⁻¹) =
      (d : ℂ) • weylShift d := by
  have hscalar :
      (∑ j : Fin d, ∑ k : Fin d,
        weylRoot d ^ (j.val * (k.val + 1))) = (d : ℂ) := by
    rw [Finset.sum_comm]
    let last : Fin d := ⟨d - 1, by omega⟩
    rw [Finset.sum_eq_single_of_mem last (Finset.mem_univ _)]
    · have hlast : last.val + 1 = d := by
        dsimp [last]
        omega
      rw [hlast]
      exact sum_weylRoot_pow_mul_eq_d d (by omega)
    · intro k _ hk
      have hkval : k.val ≠ d - 1 := by
        intro hval
        apply hk
        apply Fin.ext
        simpa [last] using hval
      have hklt : k.val + 1 < d := by omega
      exact sum_weylRoot_pow_mul_eq_zero d (k.val + 1) (by omega)
        (by omega) hklt
  calc
    (∑ j : Fin d, ∑ k : Fin d,
        weylClock d ^ j.val * weylShift d ^ k.val * weylShift d *
          (weylClock d ^ j.val)⁻¹ * (weylShift d ^ k.val)⁻¹) =
        ∑ j : Fin d, ∑ k : Fin d,
          weylRoot d ^ (j.val * (k.val + 1)) • weylShift d := by
      simp_rw [weylAverage_shift_summand d hd]
    _ = (∑ j : Fin d, ∑ k : Fin d,
          weylRoot d ^ (j.val * (k.val + 1))) • weylShift d := by
      simp only [Finset.sum_smul]
    _ = (d : ℂ) • weylShift d := by rw [hscalar]

/-- The source-ordered Weyl average fixes the cyclic shift: `𝒯(X) = X`. -/
theorem weylAverage_shift (d : ℕ) (hd : 2 ≤ d) :
    weylAverage d (weylClock d) (weylShift d) (weylShift d) =
      weylShift d := by
  rw [weylAverage, weylAverage_shift_double_sum d hd, smul_smul]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [inv_mul_cancel₀ hdC, one_smul]

/-- For the cyclic shift, `Xᵀ = X⁻¹ = X^(d-1)`. -/
theorem weylShift_transpose_inverse_power (d : ℕ) (hd : 2 ≤ d) :
    (weylShift d).transpose = (weylShift d)⁻¹ ∧
      (weylShift d)⁻¹ = weylShift d ^ (d - 1) := by
  letI : NeZero d := ⟨by omega⟩
  let σ := weylPredPerm d
  have hshift : weylShift d = σ.permMatrix ℂ :=
    weylShift_eq_permMatrix d hd
  have hσinv : σ⁻¹ = σ ^ (d - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [pow_sub_one_mul (by omega), weylPredPerm_pow_d d]
  constructor
  · rw [hshift, Matrix.transpose_permMatrix, permMatrix_nonsing_inv]
  · rw [hshift, permMatrix_nonsing_inv, permMatrix_pow, hσinv]

/-- When `d > 2`, the identity `𝒯(U) = Uᵀ` cannot hold for every matrix `U`. -/
theorem weylAverage_not_transpose_for_all (d : ℕ) (hd : 2 < d) :
    ¬ ∀ U : Matrix (Fin d) (Fin d) ℂ,
      weylAverage d (weylClock d) (weylShift d) U = U.transpose := by
  intro h
  have hshift := h (weylShift d)
  rw [weylAverage_shift d (by omega)] at hshift
  let row : Fin d := ⟨1, by omega⟩
  let col : Fin d := ⟨0, by omega⟩
  have he := congr_fun (congr_fun hshift row) col
  have h1mod : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  have h2mod : 2 % d = 2 := Nat.mod_eq_of_lt hd
  simp only [weylShift, Matrix.transpose_apply, row, col, h1mod, h2mod,
    Nat.reduceAdd, if_true] at he
  norm_num at he

end

end QAlgFormalized
