import QITBench.Base.OneShot
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Entropy increase under a non-selective projective measurement

This file models a finite-dimensional orthogonal projector `P`, its
complement `Q = 1 - P`, and the non-selective measurement channel
`X ↦ P * X * P + Q * X * Q`.  The target states that applying this channel to
a density state cannot decrease its von Neumann entropy.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement

open QITBench

noncomputable section

universe u

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A square complex matrix is an orthogonal projector when it is Hermitian
and idempotent. -/
def IsOrthogonalProjector (P : CMatrix a) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- The complementary projector `Q = I - P`. -/
def complementaryProjector (P : CMatrix a) : CMatrix a :=
  1 - P

/-- The matrix action of the non-selective two-outcome projective
measurement associated with `P` and `Q = I - P`. -/
def nonSelectiveProjectiveMeasurementMatrix
    (P X : CMatrix a) : CMatrix a :=
  P * X * P +
    complementaryProjector P * X * complementaryProjector P

/-- The complex-linear matrix map underlying the non-selective projective
measurement. -/
def nonSelectiveProjectiveMeasurementMap
    (P : CMatrix a) : MatrixMap a a where
  toFun := nonSelectiveProjectiveMeasurementMatrix P
  map_add' := by
    intro X Y
    simp only [nonSelectiveProjectiveMeasurementMatrix, Matrix.mul_add,
      Matrix.add_mul]
    abel
  map_smul' := by
    intro c X
    simp [nonSelectiveProjectiveMeasurementMatrix, smul_add]

/-- The non-selective projective measurement as a finite-dimensional CPTP
channel.  Its projector hypothesis supplies complete positivity and trace
preservation of the displayed matrix map. -/
def nonSelectiveProjectiveMeasurementChannel
    (P : CMatrix a) (hP : IsOrthogonalProjector P) : Channel a a where
  map := nonSelectiveProjectiveMeasurementMap P
  completelyPositive := by
    let K : Bool → CMatrix a :=
      fun b => if b then P else complementaryProjector P
    have hmap :
        nonSelectiveProjectiveMeasurementMap P = MatrixMap.ofKraus K := by
      apply LinearMap.ext
      intro X
      simp [nonSelectiveProjectiveMeasurementMap,
        nonSelectiveProjectiveMeasurementMatrix, K, complementaryProjector,
        MatrixMap.ofKraus, hP.1.eq]
    rw [hmap]
    exact MatrixMap.ofKraus_completelyPositive K
  tracePreserving := by
    let K : Bool → CMatrix a :=
      fun b => if b then P else complementaryProjector P
    have hp : IsStarProjection P := by
      constructor
      · exact hP.2
      · simpa [Matrix.star_eq_conjTranspose] using hP.1
    have hmap :
        nonSelectiveProjectiveMeasurementMap P = MatrixMap.ofKraus K := by
      apply LinearMap.ext
      intro X
      simp [nonSelectiveProjectiveMeasurementMap,
        nonSelectiveProjectiveMeasurementMatrix, K, complementaryProjector,
        MatrixMap.ofKraus, hP.1.eq]
    rw [hmap]
    apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
    simp [MatrixMap.krausAdjoint, K, complementaryProjector, hP.1.eq,
      hp.isIdempotentElem.eq, hp.one_sub.isIdempotentElem.eq]
  mapsPositive := by
    let K : Bool → CMatrix a :=
      fun b => if b then P else complementaryProjector P
    have hmap :
        nonSelectiveProjectiveMeasurementMap P = MatrixMap.ofKraus K := by
      apply LinearMap.ext
      intro X
      simp [nonSelectiveProjectiveMeasurementMap,
        nonSelectiveProjectiveMeasurementMatrix, K, complementaryProjector,
        MatrixMap.ofKraus, hP.1.eq]
    rw [hmap]
    exact MatrixMap.ofKraus_mapsPositive K

/-- The channel acts by the source formula `P X P + Q X Q`. -/
theorem nonSelectiveProjectiveMeasurementChannel_apply
    (P : CMatrix a) (hP : IsOrthogonalProjector P) (X : CMatrix a) :
    (nonSelectiveProjectiveMeasurementChannel P hP).map X =
      P * X * P +
        complementaryProjector P * X * complementaryProjector P := by
  rfl

/-- The density matrix of the measured state is the non-selective
projective-measurement expression from the source. -/
theorem nonSelectiveProjectiveMeasurementState_matrix
    (P : CMatrix a) (hP : IsOrthogonalProjector P) (rho : State a) :
    ((nonSelectiveProjectiveMeasurementChannel P hP).applyState rho).matrix =
      P * rho.matrix * P +
        complementaryProjector P * rho.matrix * complementaryProjector P := by
  rfl

/-- The Hermitian reflection `U = P - Q = 2P - I` associated with the
orthogonal projector `P`. -/
def projectorReflection (P : CMatrix a) : CMatrix a :=
  (2 : ℂ) • P - 1

/-- The reflection associated with an orthogonal projector is unitary. -/
theorem projectorReflection_isUnitary
    (P : CMatrix a) (hP : IsOrthogonalProjector P) :
    Matrix.conjTranspose (projectorReflection P) * projectorReflection P = 1 ∧
      projectorReflection P * Matrix.conjTranspose (projectorReflection P) = 1 := by
  have hp : IsStarProjection P := by
    constructor
    · exact hP.2
    · simpa [Matrix.star_eq_conjTranspose] using hP.1
  have hu := hp.two_mul_sub_one_mem_unitary
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose] at hu
  have htwo : (2 : ℂ) • P = (2 : CMatrix a) * P := by
    rw [two_smul ℂ P]
    rw [show (2 : CMatrix a) = 1 + 1 by norm_num]
    rw [Matrix.add_mul, Matrix.one_mul]
  rw [projectorReflection, htwo]
  exact hu

/-- Random-unitary representation of the non-selective projective
measurement: it is the equal mixture of the identity and conjugation by the
reflection `2P - I`. -/
theorem nonSelectiveProjectiveMeasurement_eq_randomUnitary
    (P : CMatrix a) (hP : IsOrthogonalProjector P) (X : CMatrix a) :
    nonSelectiveProjectiveMeasurementMatrix P X =
      (1 / 2 : ℂ) •
        (X + projectorReflection P * X *
          Matrix.conjTranspose (projectorReflection P)) := by
  have hct :
      Matrix.conjTranspose (projectorReflection P) =
        projectorReflection P := by
    simp [projectorReflection, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, hP.1.eq]
  rw [hct]
  unfold nonSelectiveProjectiveMeasurementMatrix complementaryProjector
    projectorReflection
  rw [show (2 : ℂ) • P = P + P by exact two_smul ℂ P]
  noncomm_ring
  module

/-- Von Neumann entropy in bits, defined as the Shannon entropy of the real
eigenvalues of a finite-dimensional density matrix.  Lean's convention
`Real.log 0 = 0` supplies the standard value `0 * log₂ 0 = 0`. -/
def vonNeumannEntropy (rho : State a) : ℝ :=
  QITBench.OneShot.schmidtEntropy rho.pos.isHermitian.eigenvalues

/-- The entropy of a positive matrix cannot decrease when it is averaged with
a unitary conjugate.  The proof diagonalizes the input and output matrices.
The squared moduli of the two change-of-eigenbasis matrices form a doubly
stochastic matrix, so scalar concavity of `-x log x` applies. -/
private theorem schmidtEntropy_le_equal_unitary_mixture
    (A B W : CMatrix a) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hW : Matrix.conjTranspose W * W = 1 ∧
      W * Matrix.conjTranspose W = 1)
    (hmix : B = (1 / 2 : ℂ) •
      (A + W * A * Matrix.conjTranspose W)) :
    QITBench.OneShot.schmidtEntropy hA.isHermitian.eigenvalues ≤
      QITBench.OneShot.schmidtEntropy hB.isHermitian.eigenvalues := by
  let U : CMatrix a := hA.isHermitian.eigenvectorUnitary
  let V : CMatrix a := hB.isHermitian.eigenvectorUnitary
  let C₁ : CMatrix a := Matrix.conjTranspose V * U
  let C₂ : CMatrix a := Matrix.conjTranspose V * W * U
  let L : CMatrix a :=
    Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  let D : a → a → ℝ := fun j i =>
    (Complex.normSq (C₁ j i) + Complex.normSq (C₂ j i)) / 2
  have hU :
      Matrix.conjTranspose U * U = 1 ∧
        U * Matrix.conjTranspose U = 1 := by
    constructor
    · simpa [U, Matrix.star_eq_conjTranspose] using
        Matrix.UnitaryGroup.star_mul_self
          hA.isHermitian.eigenvectorUnitary
    · simpa [U, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have hV :
      Matrix.conjTranspose V * V = 1 ∧
        V * Matrix.conjTranspose V = 1 := by
    constructor
    · simpa [V, Matrix.star_eq_conjTranspose] using
        Matrix.UnitaryGroup.star_mul_self
          hB.isHermitian.eigenvectorUnitary
    · simpa [V, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hB.isHermitian.eigenvectorUnitary
  have hC₁ :
      Matrix.conjTranspose C₁ * C₁ = 1 ∧
        C₁ * Matrix.conjTranspose C₁ = 1 := by
    constructor
    · simp only [C₁, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        Matrix.conjTranspose U * V * (Matrix.conjTranspose V * U) =
            Matrix.conjTranspose U * (V * Matrix.conjTranspose V) * U := by
          noncomm_ring
        _ = 1 := by rw [hV.2, Matrix.mul_one, hU.1]
    · simp only [C₁, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        Matrix.conjTranspose V * U * (Matrix.conjTranspose U * V) =
            Matrix.conjTranspose V * (U * Matrix.conjTranspose U) * V := by
          noncomm_ring
        _ = 1 := by rw [hU.2, Matrix.mul_one, hV.1]
  have hC₂ :
      Matrix.conjTranspose C₂ * C₂ = 1 ∧
        C₂ * Matrix.conjTranspose C₂ = 1 := by
    constructor
    · simp only [C₂, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        Matrix.conjTranspose U * (Matrix.conjTranspose W * V) *
            (Matrix.conjTranspose V * W * U) =
          Matrix.conjTranspose U * Matrix.conjTranspose W *
            (V * Matrix.conjTranspose V) * W * U := by
              noncomm_ring
        _ = Matrix.conjTranspose U * (Matrix.conjTranspose W * W) * U := by
          rw [hV.2]
          noncomm_ring
        _ = 1 := by rw [hW.1, Matrix.mul_one, hU.1]
    · simp only [C₂, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        Matrix.conjTranspose V * W * U *
            (Matrix.conjTranspose U * (Matrix.conjTranspose W * V)) =
          Matrix.conjTranspose V * W * (U * Matrix.conjTranspose U) *
            Matrix.conjTranspose W * V := by
              noncomm_ring
        _ = Matrix.conjTranspose V * (W * Matrix.conjTranspose W) * V := by
          rw [hU.2]
          noncomm_ring
        _ = 1 := by rw [hW.2, Matrix.mul_one, hV.1]
  have hsums (C : CMatrix a)
      (hC : Matrix.conjTranspose C * C = 1 ∧
        C * Matrix.conjTranspose C = 1) :
      (∀ j, ∑ i, Complex.normSq (C j i) = 1) ∧
        (∀ i, ∑ j, Complex.normSq (C j i) = 1) := by
    constructor
    · intro j
      have h := congrFun (congrFun hC.2 j) j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, if_pos] at h
      apply Complex.ofReal_injective
      rw [Complex.ofReal_sum, Complex.ofReal_one]
      simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using h
    · intro i
      have h := congrFun (congrFun hC.1 i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, if_pos] at h
      apply Complex.ofReal_injective
      rw [Complex.ofReal_sum, Complex.ofReal_one]
      simpa [Complex.normSq_eq_conj_mul_self] using h
  have hD : ∀ j i, 0 ≤ D j i := by
    intro j i
    exact div_nonneg
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (by norm_num)
  have hrow : ∀ j, ∑ i, D j i = 1 := by
    intro j
    dsimp [D]
    simp_rw [add_div]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      (hsums C₁ hC₁).1 j, (hsums C₂ hC₂).1 j]
    norm_num
  have hcol : ∀ i, ∑ j, D j i = 1 := by
    intro i
    dsimp [D]
    simp_rw [add_div]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      (hsums C₁ hC₁).2 i, (hsums C₂ hC₂).2 i]
    norm_num
  have hAs : A = U * L * Matrix.conjTranspose U := by
    simpa [U, L, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose] using
        hA.isHermitian.spectral_theorem
  have hBd :
      Matrix.conjTranspose V * B * V =
        Matrix.diagonal (fun i => (hB.isHermitian.eigenvalues i : ℂ)) := by
    simpa [V, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose] using
        hB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag :
      Matrix.diagonal (fun i => (hB.isHermitian.eigenvalues i : ℂ)) =
        (1 / 2 : ℂ) •
          (C₁ * L * Matrix.conjTranspose C₁ +
            C₂ * L * Matrix.conjTranspose C₂) := by
    rw [← hBd, hmix, hAs]
    simp only [C₁, C₂, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hmul (C : CMatrix a) :
      C * L * Matrix.conjTranspose C =
        fun j k => ∑ i,
          C j i * (hA.isHermitian.eigenvalues i : ℂ) * star (C k i) := by
    ext j k
    change
      (∑ i,
        (C * Matrix.diagonal
          (fun x => (hA.isHermitian.eigenvalues x : ℂ))) j i *
            Matrix.conjTranspose C i k) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_diagonal]
    rfl
  rw [hmul C₁, hmul C₂] at hdiag
  have hmu : ∀ j,
      hB.isHermitian.eigenvalues j =
        ∑ i, D j i * hA.isHermitian.eigenvalues i := by
    intro j
    have h := congrFun (congrFun hdiag j) j
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.add_apply] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, h]
    simp only [D, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_ofNat]
    simp_rw [Complex.normSq_eq_conj_mul_self, add_div, add_mul]
    rw [Finset.sum_add_distrib]
    change (1 / 2 : ℂ) * (_ + _) = _ + _
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
      simp only [starRingEnd_apply] <;> ring
  have hj : ∀ j,
      (∑ i, D j i * Real.negMulLog (hA.isHermitian.eigenvalues i)) ≤
        Real.negMulLog (hB.isHermitian.eigenvalues j) := by
    intro j
    rw [hmu j]
    simpa [smul_eq_mul] using
      (Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := D j)
        (p := hA.isHermitian.eigenvalues)
        (fun i _ => hD j i) (by simpa using hrow j)
        (fun i _ => hA.eigenvalues_nonneg i))
  have hsum :
      (∑ i, Real.negMulLog (hA.isHermitian.eigenvalues i)) ≤
        ∑ j, Real.negMulLog (hB.isHermitian.eigenvalues j) := by
    calc
      (∑ i, Real.negMulLog (hA.isHermitian.eigenvalues i)) =
          ∑ j, ∑ i,
            D j i * Real.negMulLog (hA.isHermitian.eigenvalues i) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_mul, hcol i, one_mul]
      _ ≤ ∑ j, Real.negMulLog (hB.isHermitian.eigenvalues j) :=
        Finset.sum_le_sum fun j _ => hj j
  have entropy_eq (p : a → ℝ) :
      QITBench.OneShot.schmidtEntropy p =
        (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
    simp only [QITBench.OneShot.schmidtEntropy, QITBench.OneShot.log2,
      Real.negMulLog, div_eq_mul_inv]
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [entropy_eq, entropy_eq]
  exact (div_le_div_iff_of_pos_right
    (Real.log_pos (by norm_num))).mpr hsum

/-- A non-selective projective measurement cannot decrease the von Neumann
entropy of a finite-dimensional quantum state. -/
theorem entropy_le_nonSelectiveProjectiveMeasurement
    (P : CMatrix a) (hP : IsOrthogonalProjector P) (rho : State a) :
    vonNeumannEntropy rho ≤
      vonNeumannEntropy
        ((nonSelectiveProjectiveMeasurementChannel P hP).applyState rho) := by
  let sigma :=
    (nonSelectiveProjectiveMeasurementChannel P hP).applyState rho
  apply schmidtEntropy_le_equal_unitary_mixture
    rho.matrix sigma.matrix (projectorReflection P) rho.pos sigma.pos
  · exact projectorReflection_isUnitary P hP
  · calc
      sigma.matrix = nonSelectiveProjectiveMeasurementMatrix P rho.matrix := by
        simpa [sigma, nonSelectiveProjectiveMeasurementMatrix] using
          nonSelectiveProjectiveMeasurementState_matrix P hP rho
      _ = (1 / 2 : ℂ) •
          (rho.matrix + projectorReflection P * rho.matrix *
            Matrix.conjTranspose (projectorReflection P)) :=
        nonSelectiveProjectiveMeasurement_eq_randomUnitary P hP rho.matrix

end

end QITFormalized.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement
