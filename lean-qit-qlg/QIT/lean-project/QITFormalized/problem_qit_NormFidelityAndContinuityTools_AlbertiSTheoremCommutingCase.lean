import QITBench.Base.OneShot
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Alberti's theorem for commuting density operators

This file records Alberti's variational characterization of quantum fidelity,
its reduction to a scalar optimization in a common orthonormal eigenbasis, and
the resulting Bhattacharyya-coefficient formula.
-/

open scoped BigOperators ComplexOrder MatrixOrder Topology
  Matrix.Norms.L2Operator

namespace QITFormalized.AlbertiCommutingCase

open QITBench

noncomputable section

set_option maxHeartbeats 1000000

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The product of trace pairings appearing in Alberti's theorem. -/
def albertiObjective (rho sigma P : CMatrix ι) : ℝ :=
  Complex.re ((rho * P).trace) * Complex.re ((sigma * P⁻¹).trace)

/--
The values of Alberti's objective over invertible positive-definite operators.
The `IsUnit` field makes the source's invertibility restriction explicit,
although positive definiteness already implies it in this finite-dimensional
setting.
-/
def albertiVariationalValues (rho sigma : CMatrix ι) : Set ℝ :=
  {x | ∃ P : CMatrix ι,
    P.PosDef ∧ IsUnit P ∧ x = albertiObjective rho sigma P}

/-- The diagonal operator with real diagonal entries `p i`. -/
def diagonalPositiveOperator (p : ι → ℝ) : CMatrix ι :=
  Matrix.diagonal fun i => (p i : ℂ)

/-- Alberti's objective after all three matrices are diagonalized. -/
def diagonalAlbertiObjective (lambda mu p : ι → ℝ) : ℝ :=
  (∑ i, lambda i * p i) * (∑ i, mu i * (p i)⁻¹)

/-- Values of the diagonal objective as the diagonal entries range over positive reals. -/
def diagonalAlbertiValues (lambda mu : ι → ℝ) : Set ℝ :=
  {x | ∃ p : ι → ℝ,
    (∀ i, 0 < p i) ∧ x = diagonalAlbertiObjective lambda mu p}

/-- Classical fidelity, also called the Bhattacharyya coefficient. -/
def bhattacharyyaCoefficient (lambda mu : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (lambda i * mu i)

private def matrixEuclidean (A : CMatrix ι) :
    EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun ij => A ij.1 ij.2

private lemma matrixEuclidean_inner (A B : CMatrix ι) :
    inner ℂ (matrixEuclidean A) (matrixEuclidean B) =
      (A.conjTranspose * B).trace := by
  simp only [matrixEuclidean, PiLp.inner_apply, RCLike.inner_apply]
  rw [Fintype.sum_prod_type, Matrix.trace, Finset.sum_comm]
  simp [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    mul_comm]

private lemma norm_trace_mul_le (A B : CMatrix ι) :
    ‖(A * B).trace‖ ≤
      Real.sqrt
          (Complex.re ((A * A.conjTranspose).trace)) *
        Real.sqrt
          (Complex.re ((B.conjTranspose * B).trace)) := by
  have hinner := norm_inner_le_norm (𝕜 := ℂ)
    (matrixEuclidean A.conjTranspose) (matrixEuclidean B)
  rw [matrixEuclidean_inner,
    Matrix.conjTranspose_conjTranspose] at hinner
  calc
    ‖(A * B).trace‖ ≤
        ‖matrixEuclidean A.conjTranspose‖ *
          ‖matrixEuclidean B‖ := hinner
    _ =
        Real.sqrt
            (Complex.re ((A * A.conjTranspose).trace)) *
          Real.sqrt
            (Complex.re ((B.conjTranspose * B).trace)) := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)
          (matrixEuclidean A.conjTranspose),
        norm_eq_sqrt_re_inner (𝕜 := ℂ)
          (matrixEuclidean B),
        matrixEuclidean_inner, matrixEuclidean_inner,
        Matrix.conjTranspose_conjTranspose]
      rfl

private lemma matrixSqrt_posDef (A : CMatrix ι) (hA : A.PosDef) :
    (QITBench.OneShot.matrixSqrt A).PosDef := by
  unfold QITBench.OneShot.matrixSqrt
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.sqrt A)

private lemma matrixSqrt_posSemidef (A : CMatrix ι) :
    (QITBench.OneShot.matrixSqrt A).PosSemidef := by
  unfold QITBench.OneShot.matrixSqrt
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)

private lemma trace_mul_nonneg_of_posSemidef
    {A B : CMatrix ι}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have hsqrtPos :
      (QITBench.OneShot.matrixSqrt B).PosSemidef :=
    matrixSqrt_posSemidef B
  have hsqrt_sq :
      QITBench.OneShot.matrixSqrt B *
          QITBench.OneShot.matrixSqrt B =
        B := by
    simpa [QITBench.OneShot.matrixSqrt, pow_two] using
      (CFC.sq_sqrt B hB.nonneg)
  have hsandwich :
      (QITBench.OneShot.matrixSqrt B * A *
          QITBench.OneShot.matrixSqrt B).PosSemidef := by
    simpa [hsqrtPos.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same
        (QITBench.OneShot.matrixSqrt B)
  have htrace :
      (QITBench.OneShot.matrixSqrt B * A *
            QITBench.OneShot.matrixSqrt B).trace =
        (A * B).trace := by
    calc
      (QITBench.OneShot.matrixSqrt B * A *
            QITBench.OneShot.matrixSqrt B).trace =
          (QITBench.OneShot.matrixSqrt B *
              QITBench.OneShot.matrixSqrt B * A).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ =
          (A * (QITBench.OneShot.matrixSqrt B *
            QITBench.OneShot.matrixSqrt B)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (A * B).trace := by rw [hsqrt_sq]
  rw [← htrace]
  exact hsandwich.trace_nonneg

private lemma re_trace_mul_nonneg_of_posSemidef
    {A B : CMatrix ι}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Complex.re ((A * B).trace) :=
  (Complex.nonneg_iff.mp
    (trace_mul_nonneg_of_posSemidef hA hB)).1

private lemma re_trace_mul_mono_left
    {A A' B : CMatrix ι}
    (hdiff : (A' - A).PosSemidef) (hB : B.PosSemidef) :
    Complex.re ((A * B).trace) ≤
      Complex.re ((A' * B).trace) := by
  have hnonneg :=
    re_trace_mul_nonneg_of_posSemidef hdiff hB
  have hdecomp :
      (A' * B).trace =
        (A * B).trace + ((A' - A) * B).trace := by
    rw [sub_mul, Matrix.trace_sub]
    abel
  rw [hdecomp, Complex.add_re]
  linarith

private def regularizedMatrix (A : CMatrix ι) (t : ℝ) :
    CMatrix ι :=
  A + t • 1

private lemma regularizedMatrix_posSemidef
    (A : CMatrix ι) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    (regularizedMatrix A t).PosSemidef := by
  exact hA.add (Matrix.PosSemidef.one.smul ht)

private lemma regularizedMatrix_posDef
    (A : CMatrix ι) (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (regularizedMatrix A t).PosDef := by
  simpa [regularizedMatrix, add_comm] using
    (Matrix.PosDef.one.smul ht).add_posSemidef hA

private theorem geometric_mean_data
    (A B : CMatrix ι) (hA : A.PosDef) (hB : B.PosDef) :
    ∃ G : CMatrix ι,
      G.PosDef ∧
      G * A * G = B ∧
      QITBench.OneShot.quantumFidelity A B =
        Complex.re ((A * G).trace) := by
  let R : CMatrix ι := QITBench.OneShot.matrixSqrt A
  let X : CMatrix ι :=
    QITBench.OneShot.matrixSqrt (R * B * R)
  let G : CMatrix ι := R⁻¹ * X * R⁻¹
  have hRpd : R.PosDef := matrixSqrt_posDef A hA
  have hRunit : IsUnit R := hRpd.isUnit
  have hRinvpd : R⁻¹.PosDef := hRpd.inv
  have hRstar : R.conjTranspose = R :=
    hRpd.isHermitian.eq
  have hcorepd : (R * B * R).PosDef := by
    have h := hB.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr hRunit)
    simpa [hRstar] using h
  have hXpd : X.PosDef :=
    matrixSqrt_posDef _ hcorepd
  have hRinvstar : (R⁻¹).conjTranspose = R⁻¹ :=
    hRinvpd.isHermitian.eq
  have hGpd : G.PosDef := by
    have h := hXpd.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr
        hRinvpd.isUnit)
    simpa [G, hRinvstar] using h
  have hRR : R * R = A := by
    dsimp [R]
    unfold QITBench.OneShot.matrixSqrt
    exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hXX : X * X = R * B * R := by
    dsimp [X]
    unfold QITBench.OneShot.matrixSqrt
    exact CFC.sqrt_mul_sqrt_self _
      hcorepd.posSemidef.nonneg
  have hdet : IsUnit R.det :=
    (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hRiR : R⁻¹ * R = 1 :=
    Matrix.nonsing_inv_mul R hdet
  have hRRi : R * R⁻¹ = 1 :=
    Matrix.mul_nonsing_inv R hdet
  have hGAG : G * A * G = B := by
    dsimp [G]
    rw [← hRR]
    calc
      (R⁻¹ * X * R⁻¹) * (R * R) *
            (R⁻¹ * X * R⁻¹) =
          R⁻¹ * X * (R⁻¹ * R) * (R * R⁻¹) *
            X * R⁻¹ := by
              noncomm_ring
      _ = R⁻¹ * X * X * R⁻¹ := by
        rw [hRiR, hRRi]
        simp
      _ = R⁻¹ * (R * B * R) * R⁻¹ := by
        rw [← hXX]
        noncomm_ring
      _ = B := by
        calc
          R⁻¹ * (R * B * R) * R⁻¹ =
              (R⁻¹ * R) * B * (R * R⁻¹) := by
                noncomm_ring
          _ = B := by
            rw [hRiR, hRRi]
            simp
  have hfid :
      QITBench.OneShot.quantumFidelity A B =
        Complex.re X.trace := by
    rfl
  have hAG : A * G = R * X * R⁻¹ := by
    dsimp [G]
    rw [← hRR]
    calc
      R * R * (R⁻¹ * X * R⁻¹) =
          R * (R * R⁻¹) * X * R⁻¹ := by
            noncomm_ring
      _ = R * X * R⁻¹ := by
        rw [hRRi]
        simp
  have htrace : (A * G).trace = X.trace := by
    rw [hAG, Matrix.trace_mul_cycle, hRiR]
    simp
  exact
    ⟨G, hGpd, hGAG,
      hfid.trans (congrArg Complex.re htrace.symm)⟩

private theorem full_rank_alberti_bound
    (A B G Q : CMatrix ι)
    (hA : A.PosDef) (hG : G.PosDef)
    (hGAG : G * A * G = B) (hQ : Q.PosDef) :
    Complex.re ((A * G).trace) ^ 2 ≤
      Complex.re ((A * Q).trace) *
        Complex.re ((B * Q⁻¹).trace) := by
  let R : CMatrix ι := QITBench.OneShot.matrixSqrt A
  let S : CMatrix ι := QITBench.OneShot.matrixSqrt Q
  let X : CMatrix ι := S * R
  let Y : CMatrix ι := R * G * S⁻¹
  have hRpd := matrixSqrt_posDef A hA
  have hSpd := matrixSqrt_posDef Q hQ
  have hRstar : R.conjTranspose = R :=
    hRpd.isHermitian.eq
  have hSstar : S.conjTranspose = S :=
    hSpd.isHermitian.eq
  have hSistarpd : S⁻¹.PosDef := hSpd.inv
  have hSistar : (S⁻¹).conjTranspose = S⁻¹ :=
    hSistarpd.isHermitian.eq
  have hRR : R * R = A := by
    dsimp [R]
    unfold QITBench.OneShot.matrixSqrt
    exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSS : S * S = Q := by
    dsimp [S]
    unfold QITBench.OneShot.matrixSqrt
    exact CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg
  have hXY : (X * Y).trace = (A * G).trace := by
    dsimp [X, Y]
    calc
      (S * R * (R * G * S⁻¹)).trace =
          (S * (R * R * G) * S⁻¹).trace := by
            congr 1
            noncomm_ring
      _ = (S⁻¹ * S * (R * R * G)).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = (S⁻¹ * S * (R * R) * G).trace := by
        congr 1
        noncomm_ring
      _ = (A * G).trace := by
        have hSdet : IsUnit S.det :=
          (Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit
        rw [Matrix.nonsing_inv_mul S hSdet, hRR]
        simp
  have hXX :
      (X * X.conjTranspose).trace = (A * Q).trace := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, hRstar, hSstar]
    calc
      (S * R * (R * S)).trace =
          (S * (R * R) * S).trace := by
            congr 1
            noncomm_ring
      _ = (S * S * (R * R)).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = ((R * R) * (S * S)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (A * Q).trace := by rw [hRR, hSS]
  have hYY :
      (Y.conjTranspose * Y).trace =
        (B * Q⁻¹).trace := by
    dsimp [Y]
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hRstar,
      hG.isHermitian.eq, hSistar]
    calc
      (S⁻¹ * (G * R) * (R * G * S⁻¹)).trace =
          (S⁻¹ * (G * (R * R) * G) * S⁻¹).trace := by
            congr 1
            noncomm_ring
      _ =
          (S⁻¹ * S⁻¹ * (G * (R * R) * G)).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ =
          ((G * (R * R) * G) * (S⁻¹ * S⁻¹)).trace :=
        Matrix.trace_mul_comm _ _
      _ =
          (G * (R * R) * G * (S⁻¹ * S⁻¹)).trace := by
        congr 1
      _ = (B * (S * S)⁻¹).trace := by
        rw [hRR, hGAG, Matrix.mul_inv_rev]
      _ = (B * Q⁻¹).trace := by rw [hSS]
  have hAQ_nonneg :
      0 ≤ Complex.re ((A * Q).trace) := by
    exact re_trace_mul_nonneg_of_posSemidef
      hA.posSemidef hQ.posSemidef
  have hBpsd : B.PosSemidef := by
    rw [← hGAG]
    simpa [hG.isHermitian.eq] using
      hA.posSemidef.mul_mul_conjTranspose_same G
  have hBQi_nonneg :
      0 ≤ Complex.re ((B * Q⁻¹).trace) :=
    re_trace_mul_nonneg_of_posSemidef
      hBpsd hQ.posSemidef.inv
  have hcs := norm_trace_mul_le X Y
  rw [hXY, hXX, hYY] at hcs
  calc
    Complex.re ((A * G).trace) ^ 2 ≤
        ‖(A * G).trace‖ ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (norm_nonneg _)] using
        Complex.abs_re_le_norm ((A * G).trace)
    _ ≤
        (Real.sqrt (Complex.re ((A * Q).trace)) *
            Real.sqrt
              (Complex.re ((B * Q⁻¹).trace))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _))).mpr hcs
    _ =
        Complex.re ((A * Q).trace) *
          Complex.re ((B * Q⁻¹).trace) := by
      rw [mul_pow, Real.sq_sqrt hAQ_nonneg,
        Real.sq_sqrt hBQi_nonneg]

private theorem optimizer_objective
    (A B G : CMatrix ι)
    (hG : G.PosDef) (hGAG : G * A * G = B)
    (hfid :
      QITBench.OneShot.quantumFidelity A B =
        Complex.re ((A * G).trace)) :
    albertiObjective A B G =
      QITBench.OneShot.quantumFidelity A B ^ 2 := by
  have hdet : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hGGi : G * G⁻¹ = 1 :=
    Matrix.mul_nonsing_inv G hdet
  have hsecond : (B * G⁻¹).trace = (A * G).trace := by
    rw [← hGAG]
    calc
      (G * A * G * G⁻¹).trace =
          ((G * A) * (G * G⁻¹)).trace := by
            congr 1
            noncomm_ring
      _ = (G * A).trace := by
        rw [hGGi, Matrix.mul_one]
      _ = (A * G).trace := Matrix.trace_mul_comm _ _
  unfold albertiObjective
  rw [hsecond, ← hfid]
  ring

private theorem matrixSqrt_tendsto
    [Nonempty ι]
    {α : Type*} {l : Filter α}
    {A : α → CMatrix ι} {A0 : CMatrix ι}
    (hA : Filter.Tendsto A l (𝓝 A0))
    (hpos : ∀ᶠ x in l, (A x).PosSemidef)
    (hA0 : A0.PosSemidef) :
    Filter.Tendsto
      (fun x => QITBench.OneShot.matrixSqrt (A x)) l
      (𝓝 (QITBench.OneShot.matrixSqrt A0)) := by
  letI : CStarAlgebra (CMatrix ι) := {}
  letI :
      IsometricContinuousFunctionalCalculus
        ℝ (CMatrix ι) IsSelfAdjoint :=
    inferInstance
  let f : ℝ → ℝ :=
    fun x => (NNReal.sqrt x.toNNReal : ℝ)
  let r : ℝ := ‖A0‖ + 1
  have hball :
      ∀ᶠ x in l, A x ∈ Metric.ball A0 1 :=
    hA (Metric.ball_mem_nhds A0 zero_lt_one)
  have hnorm : ∀ᶠ x in l, ‖A x‖ ≤ r := by
    filter_upwards [hball] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hbase :=
      norm_le_norm_add_norm_sub' (A x) A0
    dsimp [r]
    linarith
  have hspec :
      ∀ᶠ x in l,
        spectrum ℝ (A x) ⊆ Metric.closedBall 0 r := by
    filter_upwards [hnorm] with x hx y hy
    rw [Metric.mem_closedBall, Real.dist_eq]
    simpa [abs_sub_comm] using
      (spectrum.norm_le_norm_of_mem hy).trans hx
  have hspec0 :
      spectrum ℝ A0 ⊆ Metric.closedBall 0 r := by
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq]
    have hle := spectrum.norm_le_norm_of_mem hy
    dsimp [r]
    simpa [abs_sub_comm] using
      hle.trans (by linarith : ‖A0‖ ≤ ‖A0‖ + 1)
  have hself : ∀ᶠ x in l, IsSelfAdjoint (A x) :=
    hpos.mono fun x hx => hx.isHermitian
  have hcfc :
      Filter.Tendsto (fun x => cfc f (A x)) l
        (𝓝 (cfc f A0)) :=
    hA.cfc (isCompact_closedBall (0 : ℝ) r) f
      hspec hself hspec0 hA0.isHermitian (by
        exact
          NNReal.continuous_coe.comp
            (NNReal.continuous_sqrt.comp
              continuous_real_toNNReal) |>.continuousOn)
  have hsqrt (M : CMatrix ι) (hM : M.PosSemidef) :
      QITBench.OneShot.matrixSqrt M = cfc f M := by
    unfold QITBench.OneShot.matrixSqrt
    rw [CFC.sqrt_eq_cfc,
      cfc_nnreal_eq_real NNReal.sqrt M hM.nonneg]
  rw [hsqrt A0 hA0]
  apply hcfc.congr'
  filter_upwards [hpos] with x hx
  exact (hsqrt (A x) hx).symm

private theorem fidelity_regularized_tendsto
    [Nonempty ι]
    (A B : CMatrix ι)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Filter.Tendsto
      (fun t : ℝ =>
        QITBench.OneShot.quantumFidelity
          (regularizedMatrix A t)
          (regularizedMatrix B t))
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (QITBench.OneShot.quantumFidelity A B)) := by
  let l : Filter ℝ := 𝓝[Set.Ioi 0] 0
  have hregA :
      Filter.Tendsto
        (fun t : ℝ => regularizedMatrix A t) l (𝓝 A) := by
    have hc :
        ContinuousAt
          (fun t : ℝ => A + t • (1 : CMatrix ι)) 0 := by
      fun_prop
    simpa [l, regularizedMatrix] using
      hc.tendsto.mono_left inf_le_left
  have hregB :
      Filter.Tendsto
        (fun t : ℝ => regularizedMatrix B t) l (𝓝 B) := by
    have hc :
        ContinuousAt
          (fun t : ℝ => B + t • (1 : CMatrix ι)) 0 := by
      fun_prop
    simpa [l, regularizedMatrix] using
      hc.tendsto.mono_left inf_le_left
  have hposA :
      ∀ᶠ t in l, (regularizedMatrix A t).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact regularizedMatrix_posSemidef A hA ht.le
  have hposB :
      ∀ᶠ t in l, (regularizedMatrix B t).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact regularizedMatrix_posSemidef B hB ht.le
  have hsqrtA := matrixSqrt_tendsto hregA hposA hA
  have hinside :
      Filter.Tendsto
        (fun t : ℝ =>
          QITBench.OneShot.matrixSqrt
                (regularizedMatrix A t) *
              regularizedMatrix B t *
            QITBench.OneShot.matrixSqrt
                (regularizedMatrix A t))
        l
        (𝓝
          (QITBench.OneShot.matrixSqrt A * B *
            QITBench.OneShot.matrixSqrt A)) :=
    (hsqrtA.mul hregB).mul hsqrtA
  have hposInside :
      ∀ᶠ t in l,
        (QITBench.OneShot.matrixSqrt
                (regularizedMatrix A t) *
              regularizedMatrix B t *
            QITBench.OneShot.matrixSqrt
                (regularizedMatrix A t)).PosSemidef := by
    filter_upwards [hposB] with t ht
    let S :=
      QITBench.OneShot.matrixSqrt (regularizedMatrix A t)
    have hSstar : S.conjTranspose = S :=
      (matrixSqrt_posSemidef _).isHermitian.eq
    simpa [S, hSstar] using
      ht.mul_mul_conjTranspose_same S
  have hinside0 :
      (QITBench.OneShot.matrixSqrt A * B *
          QITBench.OneShot.matrixSqrt A).PosSemidef := by
    let S := QITBench.OneShot.matrixSqrt A
    have hSstar : S.conjTranspose = S :=
      (matrixSqrt_posSemidef _).isHermitian.eq
    simpa [S, hSstar] using
      hB.mul_mul_conjTranspose_same S
  have hsqrtInside :=
    matrixSqrt_tendsto hinside hposInside hinside0
  have htrace :
      Continuous
        (fun M : CMatrix ι => Complex.re M.trace) := by
    fun_prop
  unfold QITBench.OneShot.quantumFidelity
  exact htrace.continuousAt.tendsto.comp hsqrtInside

private theorem albertiObjective_regularized_tendsto
    (A B P : CMatrix ι) :
    Filter.Tendsto
      (fun t : ℝ =>
        albertiObjective
          (regularizedMatrix A t)
          (regularizedMatrix B t) P)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (albertiObjective A B P)) := by
  have hc :
      ContinuousAt
        (fun t : ℝ =>
          Complex.re
              (((A + t • (1 : CMatrix ι)) * P).trace) *
            Complex.re
              (((B + t • (1 : CMatrix ι)) * P⁻¹).trace))
        0 := by
    fun_prop
  simpa [albertiObjective, regularizedMatrix] using
    hc.tendsto.mono_left inf_le_left

private theorem quantumFidelity_sq_le_albertiObjective
    [Nonempty ι]
    (A B P : CMatrix ι)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hP : P.PosDef) :
    QITBench.OneShot.quantumFidelity A B ^ 2 ≤
      albertiObjective A B P := by
  let l : Filter ℝ := 𝓝[Set.Ioi 0] 0
  have hfid :=
    fidelity_regularized_tendsto A B hA hB
  have hfid_sq :
      Filter.Tendsto
        (fun t : ℝ =>
          QITBench.OneShot.quantumFidelity
              (regularizedMatrix A t)
              (regularizedMatrix B t) ^ 2)
        l
        (𝓝 (QITBench.OneShot.quantumFidelity A B ^ 2)) :=
    hfid.pow 2
  have hobj :
      Filter.Tendsto
        (fun t : ℝ =>
          albertiObjective
            (regularizedMatrix A t)
            (regularizedMatrix B t) P)
        l
        (𝓝 (albertiObjective A B P)) :=
    albertiObjective_regularized_tendsto A B P
  apply le_of_tendsto_of_tendsto hfid_sq hobj
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hAt :=
    regularizedMatrix_posDef A hA ht
  have hBt :=
    regularizedMatrix_posDef B hB ht
  obtain ⟨G, hG, hGAG, hfidG⟩ :=
    geometric_mean_data
      (regularizedMatrix A t)
      (regularizedMatrix B t) hAt hBt
  calc
    QITBench.OneShot.quantumFidelity
          (regularizedMatrix A t)
          (regularizedMatrix B t) ^ 2 =
        Complex.re
          (((regularizedMatrix A t) * G).trace) ^ 2 := by
            rw [hfidG]
    _ ≤
        Complex.re
            (((regularizedMatrix A t) * P).trace) *
          Complex.re
            (((regularizedMatrix B t) * P⁻¹).trace) :=
      full_rank_alberti_bound
        (regularizedMatrix A t)
        (regularizedMatrix B t) G P
        hAt hG hGAG hP
    _ =
        albertiObjective
          (regularizedMatrix A t)
          (regularizedMatrix B t) P := by
      rfl

/-- Alberti's variational characterization for finite-dimensional density operators. -/
theorem alberti_variational_characterization
    (rho sigma : State ι) :
    QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix ^ 2 =
      sInf (albertiVariationalValues rho.matrix sigma.matrix) := by
  letI : Nonempty ι := rho.nonempty
  have hvalues_nonempty :
      (albertiVariationalValues rho.matrix sigma.matrix).Nonempty := by
    refine ⟨albertiObjective rho.matrix sigma.matrix 1, ?_⟩
    exact ⟨1, Matrix.PosDef.one, isUnit_one, rfl⟩
  have hvalues_bddBelow :
      BddBelow
        (albertiVariationalValues
          rho.matrix sigma.matrix) := by
    refine
      ⟨QITBench.OneShot.quantumFidelity
          rho.matrix sigma.matrix ^ 2, ?_⟩
    rintro x ⟨P, hPpos, hPunit, rfl⟩
    exact
      quantumFidelity_sq_le_albertiObjective
        rho.matrix sigma.matrix P
        rho.pos sigma.pos hPpos
  apply le_antisymm
  · refine le_csInf hvalues_nonempty ?_
    rintro x ⟨P, hPpos, hPunit, rfl⟩
    exact
      quantumFidelity_sq_le_albertiObjective
        rho.matrix sigma.matrix P
        rho.pos sigma.pos hPpos
  · let l : Filter ℝ := 𝓝[Set.Ioi 0] 0
    have hfid :=
      fidelity_regularized_tendsto
        rho.matrix sigma.matrix rho.pos sigma.pos
    have hfid_sq :
        Filter.Tendsto
          (fun t : ℝ =>
            QITBench.OneShot.quantumFidelity
                (regularizedMatrix rho.matrix t)
                (regularizedMatrix sigma.matrix t) ^ 2)
          l
          (𝓝
            (QITBench.OneShot.quantumFidelity
              rho.matrix sigma.matrix ^ 2)) :=
      hfid.pow 2
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hfid_sq
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hrt :=
      regularizedMatrix_posDef rho.matrix rho.pos ht
    have hst :=
      regularizedMatrix_posDef sigma.matrix sigma.pos ht
    obtain ⟨G, hG, hGAG, hfidG⟩ :=
      geometric_mean_data
        (regularizedMatrix rho.matrix t)
        (regularizedMatrix sigma.matrix t)
        hrt hst
    have hdiffR :
        (regularizedMatrix rho.matrix t -
          rho.matrix).PosSemidef := by
      simpa [regularizedMatrix] using
        (Matrix.PosSemidef.one.smul ht.le :
          (t • (1 : CMatrix ι)).PosSemidef)
    have hdiffS :
        (regularizedMatrix sigma.matrix t -
          sigma.matrix).PosSemidef := by
      simpa [regularizedMatrix] using
        (Matrix.PosSemidef.one.smul ht.le :
          (t • (1 : CMatrix ι)).PosSemidef)
    have hleft :
        Complex.re ((rho.matrix * G).trace) ≤
          Complex.re
            (((regularizedMatrix rho.matrix t) * G).trace) :=
      re_trace_mul_mono_left hdiffR hG.posSemidef
    have hright :
        Complex.re ((sigma.matrix * G⁻¹).trace) ≤
          Complex.re
            (((regularizedMatrix sigma.matrix t) *
              G⁻¹).trace) :=
      re_trace_mul_mono_left hdiffS hG.posSemidef.inv
    have hright_nonneg :
        0 ≤ Complex.re ((sigma.matrix * G⁻¹).trace) :=
      re_trace_mul_nonneg_of_posSemidef
        sigma.pos hG.posSemidef.inv
    have hleft_reg_nonneg :
        0 ≤
          Complex.re
            (((regularizedMatrix rho.matrix t) * G).trace) :=
      re_trace_mul_nonneg_of_posSemidef
        hrt.posSemidef hG.posSemidef
    have hobjective_mono :
        albertiObjective rho.matrix sigma.matrix G ≤
          albertiObjective
            (regularizedMatrix rho.matrix t)
            (regularizedMatrix sigma.matrix t) G := by
      unfold albertiObjective
      exact mul_le_mul hleft hright
        hright_nonneg hleft_reg_nonneg
    calc
      sInf
          (albertiVariationalValues
            rho.matrix sigma.matrix) ≤
        albertiObjective rho.matrix sigma.matrix G :=
          csInf_le hvalues_bddBelow
            ⟨G, hG, hG.isUnit, rfl⟩
      _ ≤
          albertiObjective
            (regularizedMatrix rho.matrix t)
            (regularizedMatrix sigma.matrix t) G :=
        hobjective_mono
      _ =
          QITBench.OneShot.quantumFidelity
              (regularizedMatrix rho.matrix t)
              (regularizedMatrix sigma.matrix t) ^ 2 :=
        optimizer_objective
          (regularizedMatrix rho.matrix t)
          (regularizedMatrix sigma.matrix t)
          G hG hGAG hfidG

/--
Strictly positive diagonal entries give a positive-definite, invertible
operator, matching the admissible diagonal restriction in Alberti's theorem.
-/
theorem diagonalPositiveOperator_posDef_isUnit
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    (diagonalPositiveOperator p).PosDef ∧
      IsUnit (diagonalPositiveOperator p) := by
  have hpd : (diagonalPositiveOperator p).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hp i
  exact ⟨hpd, hpd.isUnit⟩

/-- The matrix trace objective reduces to the stated scalar objective on diagonal data. -/
theorem albertiObjective_diagonal
    (lambda mu p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    albertiObjective
        (Matrix.diagonal fun i => (lambda i : ℂ))
        (Matrix.diagonal fun i => (mu i : ℂ))
        (diagonalPositiveOperator p) =
      diagonalAlbertiObjective lambda mu p := by
  have hunit : IsUnit (fun i => (p i : ℂ)) :=
    Pi.isUnit_iff.mpr fun i =>
      isUnit_iff_ne_zero.mpr
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (hp i)))
  have hinv :
      Ring.inverse (fun i => (p i : ℂ)) =
        fun i => ((p i : ℂ)⁻¹) := by
    rw [Ring.inverse_of_isUnit hunit]
    funext i
    rw [hunit.val_inv_apply]
    rw [← Ring.inverse_of_isUnit (hunit.apply i), Ring.inverse_eq_inv]
  simp [albertiObjective, diagonalPositiveOperator,
    diagonalAlbertiObjective, Matrix.inv_diagonal, hinv,
    ← Complex.ofReal_inv]

/-- The Cauchy--Schwarz lower bound for every positive diagonal choice. -/
theorem bhattacharyya_sq_le_diagonalAlbertiObjective
    (lambda mu p : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hmu : ∀ i, 0 ≤ mu i)
    (hp : ∀ i, 0 < p i) :
    bhattacharyyaCoefficient lambda mu ^ 2 ≤
      diagonalAlbertiObjective lambda mu p := by
  unfold bhattacharyyaCoefficient diagonalAlbertiObjective
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i hi
    exact mul_nonneg (hlambda i) (le_of_lt (hp i))
  · intro i hi
    exact mul_nonneg (hmu i) (le_of_lt (inv_pos.mpr (hp i)))
  · intro i hi
    rw [Real.sq_sqrt (mul_nonneg (hlambda i) (hmu i))]
    apply le_of_eq
    field_simp [ne_of_gt (hp i)]

/--
The exact scalar optimization arising from restriction to positive diagonal
operators in the common eigenbasis.
-/
theorem diagonal_alberti_infimum
    (lambda mu : ι → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hmu : ∀ i, 0 ≤ mu i)
    (hlambda_sum : ∑ i, lambda i = 1)
    (hmu_sum : ∑ i, mu i = 1) :
    sInf (diagonalAlbertiValues lambda mu) =
      bhattacharyyaCoefficient lambda mu ^ 2 := by
  have hset_nonempty : (diagonalAlbertiValues lambda mu).Nonempty := by
    refine ⟨diagonalAlbertiObjective lambda mu (fun _ => 1), ?_⟩
    exact ⟨fun _ => 1, fun _ => zero_lt_one, rfl⟩
  have hbelow : BddBelow (diagonalAlbertiValues lambda mu) := by
    refine ⟨bhattacharyyaCoefficient lambda mu ^ 2, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    exact bhattacharyya_sq_le_diagonalAlbertiObjective
      lambda mu p hlambda hmu hp
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro eps heps
    let d : ℝ := min 1 (eps / 3)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min zero_lt_one (div_pos heps (by norm_num))
    have hd_one : d ≤ 1 := min_le_left _ _
    have hthree_d : 3 * d ≤ eps := by
      have := min_le_right (1 : ℝ) (eps / 3)
      dsimp [d] at hd ⊢
      nlinarith
    let p : ι → ℝ := fun i =>
      if lambda i = 0 then
        if mu i = 0 then 1 else d⁻¹
      else
        if mu i = 0 then d
        else Real.sqrt (mu i) / Real.sqrt (lambda i)
    have hp : ∀ i, 0 < p i := by
      intro i
      dsimp [p]
      by_cases hl0 : lambda i = 0
      · by_cases hm0 : mu i = 0
        · simp [hl0, hm0]
        · simp [hl0, hm0, inv_pos.mpr hd]
      · by_cases hm0 : mu i = 0
        · simp [hl0, hm0, hd]
        · simp only [hl0, hm0, if_false]
          exact div_pos
            (Real.sqrt_pos.mpr
              (lt_of_le_of_ne (hmu i) (Ne.symm hm0)))
            (Real.sqrt_pos.mpr
              (lt_of_le_of_ne (hlambda i) (Ne.symm hl0)))
    let C : ℝ := bhattacharyyaCoefficient lambda mu
    let L : ℝ := ∑ i, if mu i = 0 then lambda i else 0
    let M : ℝ := ∑ i, if lambda i = 0 then mu i else 0
    have hfirst_point (i : ι) :
        lambda i * p i =
          Real.sqrt (lambda i * mu i) +
            d * (if mu i = 0 then lambda i else 0) := by
      dsimp [p]
      by_cases hl0 : lambda i = 0
      · simp [hl0]
      by_cases hm0 : mu i = 0
      · simp [hl0, hm0, mul_comm]
      simp only [hl0, hm0, if_false, mul_zero, add_zero]
      rw [Real.sqrt_mul (hlambda i)]
      have hsl : Real.sqrt (lambda i) ≠ 0 :=
        (Real.sqrt_ne_zero (hlambda i)).mpr hl0
      rw [div_eq_mul_inv]
      calc
        lambda i *
              (Real.sqrt (mu i) * (Real.sqrt (lambda i))⁻¹) =
            (Real.sqrt (lambda i)) ^ 2 *
              (Real.sqrt (mu i) *
                (Real.sqrt (lambda i))⁻¹) := by
                  rw [Real.sq_sqrt (hlambda i)]
        _ = Real.sqrt (lambda i) * Real.sqrt (mu i) := by
          field_simp
    have hsecond_point (i : ι) :
        mu i * (p i)⁻¹ =
          Real.sqrt (lambda i * mu i) +
            d * (if lambda i = 0 then mu i else 0) := by
      dsimp [p]
      by_cases hl0 : lambda i = 0
      · by_cases hm0 : mu i = 0
        · simp [hl0, hm0]
        · simp only [hl0, hm0, if_true, if_false, zero_mul,
            Real.sqrt_zero, zero_add]
          field_simp [ne_of_gt hd]
      by_cases hm0 : mu i = 0
      · simp [hm0]
      simp only [hl0, hm0, if_false, mul_zero, add_zero]
      rw [Real.sqrt_mul (hlambda i), inv_div]
      have hsm : Real.sqrt (mu i) ≠ 0 :=
        (Real.sqrt_ne_zero (hmu i)).mpr hm0
      calc
        mu i * (Real.sqrt (lambda i) / Real.sqrt (mu i)) =
            (Real.sqrt (mu i)) ^ 2 *
              (Real.sqrt (lambda i) / Real.sqrt (mu i)) := by
                rw [Real.sq_sqrt (hmu i)]
        _ = Real.sqrt (lambda i) * Real.sqrt (mu i) := by
          field_simp
    have hfirst :
        (∑ i, lambda i * p i) = C + d * L := by
      calc
        (∑ i, lambda i * p i) =
            ∑ i, (Real.sqrt (lambda i * mu i) +
              d * (if mu i = 0 then lambda i else 0)) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hfirst_point i
        _ = C + d * L := by
          dsimp [C, L, bhattacharyyaCoefficient]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hsecond :
        (∑ i, mu i * (p i)⁻¹) = C + d * M := by
      calc
        (∑ i, mu i * (p i)⁻¹) =
            ∑ i, (Real.sqrt (lambda i * mu i) +
              d * (if lambda i = 0 then mu i else 0)) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hsecond_point i
        _ = C + d * M := by
          dsimp [C, M, bhattacharyyaCoefficient]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hC_nonneg : 0 ≤ C := by
      dsimp [C, bhattacharyyaCoefficient]
      exact Finset.sum_nonneg fun i hi => Real.sqrt_nonneg _
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      apply Finset.sum_nonneg
      intro i hi
      by_cases hm0 : mu i = 0 <;>
        simp [hm0, hlambda i]
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      apply Finset.sum_nonneg
      intro i hi
      by_cases hl0 : lambda i = 0 <;>
        simp [hl0, hmu i]
    have hL_one : L ≤ 1 := by
      rw [← hlambda_sum]
      dsimp [L]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hm0 : mu i = 0 <;>
        simp [hm0, hlambda i]
    have hM_one : M ≤ 1 := by
      rw [← hmu_sum]
      dsimp [M]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hl0 : lambda i = 0 <;>
        simp [hl0, hmu i]
    have hC_sq : C ^ 2 ≤ 1 := by
      have h := bhattacharyya_sq_le_diagonalAlbertiObjective
        lambda mu (fun _ => 1) hlambda hmu
          (fun _ => zero_lt_one)
      simpa [C, diagonalAlbertiObjective,
        hlambda_sum, hmu_sum] using h
    have hC_one : C ≤ 1 := by
      nlinarith
    have hA_bound : C + d * L ≤ C + d := by
      exact add_le_add_right
        (mul_le_of_le_one_right hd.le hL_one) C
    have hB_bound : C + d * M ≤ C + d := by
      exact add_le_add_right
        (mul_le_of_le_one_right hd.le hM_one) C
    have hprod :
        diagonalAlbertiObjective lambda mu p ≤ (C + d) ^ 2 := by
      rw [diagonalAlbertiObjective, hfirst, hsecond]
      calc
        (C + d * L) * (C + d * M) ≤
            (C + d) * (C + d * M) :=
          mul_le_mul_of_nonneg_right hA_bound
            (add_nonneg hC_nonneg (mul_nonneg hd.le hM_nonneg))
        _ ≤ (C + d) * (C + d) :=
          mul_le_mul_of_nonneg_left hB_bound
            (add_nonneg hC_nonneg hd.le)
        _ = (C + d) ^ 2 := by ring
    have hCd : (C + d) ^ 2 ≤ C ^ 2 + 3 * d := by
      nlinarith [
        mul_nonneg (sub_nonneg.mpr hC_one) hd.le,
        mul_nonneg hd.le (sub_nonneg.mpr hd_one)]
    calc
      sInf (diagonalAlbertiValues lambda mu) ≤
          diagonalAlbertiObjective lambda mu p :=
        csInf_le hbelow ⟨p, hp, rfl⟩
      _ ≤ C ^ 2 + 3 * d := hprod.trans hCd
      _ ≤ C ^ 2 + eps := add_le_add_right hthree_d _
      _ = bhattacharyyaCoefficient lambda mu ^ 2 + eps := by
        rfl
  · exact le_csInf hset_nonempty fun b hb => by
      rcases hb with ⟨p, hp, rfl⟩
      exact bhattacharyya_sq_le_diagonalAlbertiObjective
        lambda mu p hlambda hmu hp

/-- Positivity and trace normalization transported through a unitary diagonalization. -/
private theorem diagonal_spectrum_nonneg_sum_one
    (rho : State ι)
    (U : CMatrix ι) (lambda : ι → ℝ)
    (hUstarU : Matrix.conjTranspose U * U = 1)
    (hUUstar : U * Matrix.conjTranspose U = 1)
    (hrho :
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U) :
    (∀ i, 0 ≤ lambda i) ∧ (∑ i, lambda i) = 1 := by
  let D : CMatrix ι :=
    Matrix.diagonal fun i => (lambda i : ℂ)
  have hD_eq :
      D = Matrix.conjTranspose U * rho.matrix * U := by
    rw [hrho]
    change
      D =
        Matrix.conjTranspose U *
          (U * D * Matrix.conjTranspose U) * U
    symm
    calc
      Matrix.conjTranspose U *
            (U * D * Matrix.conjTranspose U) * U =
          (Matrix.conjTranspose U * U) * D *
            (Matrix.conjTranspose U * U) := by
              noncomm_ring
      _ = D := by
        rw [hUstarU]
        simp
  have hDpsd : D.PosSemidef := by
    rw [hD_eq]
    exact rho.pos.conjTranspose_mul_mul_same U
  constructor
  · intro i
    have hi := Matrix.posSemidef_diagonal_iff.mp hDpsd i
    exact_mod_cast hi
  · have htrace : D.trace = 1 := by
      rw [hD_eq, Matrix.trace_mul_cycle, hUUstar,
        Matrix.one_mul, rho.trace_eq_one]
    dsimp [D] at htrace
    rw [Matrix.trace_diagonal] at htrace
    have hre := congrArg Complex.re htrace
    simpa using hre

/--
The matrix-CFC definition of fidelity evaluates to the Bhattacharyya
coefficient on a common unitary diagonalization.
-/
private theorem quantumFidelity_eq_bhattacharyya_of_common_diagonalization
    (rho sigma : State ι)
    (U : CMatrix ι) (lambda mu : ι → ℝ)
    (hUstarU : Matrix.conjTranspose U * U = 1)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hmu : ∀ i, 0 ≤ mu i)
    (hrho :
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U)
    (hsigma :
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U) :
    QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix =
      bhattacharyyaCoefficient lambda mu := by
  let Dl : CMatrix ι :=
    Matrix.diagonal fun i => (lambda i : ℂ)
  let Dm : CMatrix ι :=
    Matrix.diagonal fun i => (mu i : ℂ)
  let Sl : CMatrix ι :=
    Matrix.diagonal fun i => (Real.sqrt (lambda i) : ℂ)
  let Dlm : CMatrix ι :=
    Matrix.diagonal fun i => ((lambda i * mu i) : ℂ)
  let Slm : CMatrix ι :=
    Matrix.diagonal fun i =>
      (Real.sqrt (lambda i * mu i) : ℂ)
  have hDl : Dl.PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => by
      exact_mod_cast hlambda i
  have hDlm : Dlm.PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => by
      exact_mod_cast mul_nonneg (hlambda i) (hmu i)
  have sqrt_diagonal
      (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
      QITBench.OneShot.matrixSqrt
          (Matrix.diagonal fun i => (l i : ℂ)) =
        Matrix.diagonal fun i => (Real.sqrt (l i) : ℂ) := by
    unfold QITBench.OneShot.matrixSqrt
    have hD :
        0 ≤ (Matrix.diagonal fun i => (l i : ℂ)) :=
      Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.posSemidef_diagonal_iff.mpr fun i => by
          exact_mod_cast hl i)
    have hS :
        0 ≤
          (Matrix.diagonal fun i =>
            (Real.sqrt (l i) : ℂ)) :=
      Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.posSemidef_diagonal_iff.mpr fun i => by
          exact_mod_cast Real.sqrt_nonneg (l i))
    apply (CFC.sqrt_eq_iff _ _ hD hS).mpr
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    simpa [pow_two] using Real.sq_sqrt (hl i)
  have sqrt_conjugate
      (D : CMatrix ι) (hD : D.PosSemidef) :
      QITBench.OneShot.matrixSqrt
          (U * D * Matrix.conjTranspose U) =
        U * QITBench.OneShot.matrixSqrt D *
          Matrix.conjTranspose U := by
    unfold QITBench.OneShot.matrixSqrt
    have hA :
        0 ≤ U * D * Matrix.conjTranspose U :=
      Matrix.nonneg_iff_posSemidef.mpr
        (hD.mul_mul_conjTranspose_same U)
    have hS :
        0 ≤ U * CFC.sqrt D * Matrix.conjTranspose U :=
      Matrix.nonneg_iff_posSemidef.mpr
        ((Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg D)).mul_mul_conjTranspose_same U)
    apply (CFC.sqrt_eq_iff _ _ hA hS).mpr
    calc
      (U * CFC.sqrt D * Matrix.conjTranspose U) *
            (U * CFC.sqrt D * Matrix.conjTranspose U) =
          U * CFC.sqrt D *
            (Matrix.conjTranspose U * U) *
              CFC.sqrt D * Matrix.conjTranspose U := by
                noncomm_ring
      _ =
          U * (CFC.sqrt D * CFC.sqrt D) *
            Matrix.conjTranspose U := by
              rw [hUstarU]
              simp only [Matrix.mul_one]
              noncomm_ring
      _ = U * D * Matrix.conjTranspose U := by
        rw [← pow_two, CFC.sq_sqrt D hD.nonneg]
  have hsqrt_rho :
      QITBench.OneShot.matrixSqrt rho.matrix =
        U * Sl * Matrix.conjTranspose U := by
    rw [hrho]
    rw [sqrt_conjugate Dl hDl]
    rw [sqrt_diagonal lambda hlambda]
  have hcore_diag : Sl * Dm * Sl = Dlm := by
    dsimp [Sl, Dm, Dlm]
    rw [Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    calc
      Real.sqrt (lambda i) * mu i *
            Real.sqrt (lambda i) =
          (Real.sqrt (lambda i)) ^ 2 * mu i := by
            ring
      _ = lambda i * mu i := by
        rw [Real.sq_sqrt (hlambda i)]
  have hinside :
      QITBench.OneShot.matrixSqrt rho.matrix *
            sigma.matrix *
          QITBench.OneShot.matrixSqrt rho.matrix =
        U * Dlm * Matrix.conjTranspose U := by
    rw [hsqrt_rho, hsigma]
    change
      (U * Sl * Matrix.conjTranspose U) *
            (U * Dm * Matrix.conjTranspose U) *
          (U * Sl * Matrix.conjTranspose U) =
        _
    calc
      (U * Sl * Matrix.conjTranspose U) *
              (U * Dm * Matrix.conjTranspose U) *
            (U * Sl * Matrix.conjTranspose U) =
          U * Sl * (Matrix.conjTranspose U * U) *
            Dm * (Matrix.conjTranspose U * U) *
              Sl * Matrix.conjTranspose U := by
                noncomm_ring
      _ = U * (Sl * Dm * Sl) * Matrix.conjTranspose U := by
        rw [hUstarU]
        simp only [Matrix.mul_one]
        noncomm_ring
      _ = U * Dlm * Matrix.conjTranspose U := by
        rw [hcore_diag]
  unfold QITBench.OneShot.quantumFidelity
  rw [hinside, sqrt_conjugate Dlm hDlm]
  have hsqrt_Dlm :
      QITBench.OneShot.matrixSqrt Dlm = Slm := by
    dsimp [Dlm, Slm]
    convert sqrt_diagonal
      (fun i => lambda i * mu i)
      (fun i => mul_nonneg (hlambda i) (hmu i)) using 1 <;>
        ext i j <;> simp
  rw [hsqrt_Dlm, Matrix.trace_mul_cycle, hUstarU,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp [bhattacharyyaCoefficient]

/--
Two commuting density matrices admit a common orthonormal eigenbasis.  The
columns of `U` are that basis; the two displayed unitary equations express
orthonormality and completeness.
-/
theorem exists_common_orthonormal_eigenbasis_of_commute
    (rho sigma : State ι)
    (hcomm : rho.matrix * sigma.matrix = sigma.matrix * rho.matrix) :
    ∃ (U : CMatrix ι) (lambda mu : ι → ℝ),
      Matrix.conjTranspose U * U = 1 ∧
      U * Matrix.conjTranspose U = 1 ∧
      (∀ i, 0 ≤ lambda i) ∧
      (∀ i, 0 ≤ mu i) ∧
      (∑ i, lambda i) = 1 ∧
      (∑ i, mu i) = 1 ∧
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U ∧
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U := by
  let A := Matrix.toEuclideanLin rho.matrix
  let B := Matrix.toEuclideanLin sigma.matrix
  have hA : A.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      rho.pos.isHermitian
  have hB : B.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      sigma.pos.isHermitian
  have hAB : Commute A B := by
    rw [Commute]
    ext x i
    simp only [A, B, Module.End.mul_apply,
      Matrix.toEuclideanLin_apply]
    change
      Matrix.mulVec rho.matrix
          (Matrix.mulVec sigma.matrix x.ofLp) i =
        Matrix.mulVec sigma.matrix
          (Matrix.mulVec rho.matrix x.ofLp) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
  let V :
      Module.End.Eigenvalues A × Module.End.Eigenvalues B →
        Submodule ℂ (EuclideanSpace ℂ ι) :=
    fun ab =>
      Module.End.eigenspace A (ab.1 : ℂ) ⊓
        Module.End.eigenspace B (ab.2 : ℂ)
  have hOrth :
      OrthogonalFamily ℂ (fun ab => V ab)
        fun ab => (V ab).subtypeₗᵢ := by
    let f :
        Module.End.Eigenvalues A × Module.End.Eigenvalues B →
          ℂ × ℂ :=
      fun ab => ((ab.2 : ℂ), (ab.1 : ℂ))
    have hf : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [f, Prod.mk.injEq] at h
      apply Prod.ext
      · exact Subtype.ext h.2
      · exact Subtype.ext h.1
    simpa only [V, f] using
      (hA.orthogonalFamily_eigenspace_inf_eigenspace hB).comp hf
  have htop : ⨆ ab, V ab = ⊤ := by
    apply top_unique
    rw [←
      hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
        hB hAB]
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    by_cases hjoint :
        Module.End.eigenspace A a ⊓
            Module.End.eigenspace B b =
          ⊥
    · simp [hjoint]
    · have ha : Module.End.eigenspace A a ≠ ⊥ := by
        intro ha0
        apply hjoint
        simp [ha0]
      have hb : Module.End.eigenspace B b ≠ ⊥ := by
        intro hb0
        apply hjoint
        simp [hb0]
      let ae : Module.End.Eigenvalues A :=
        ⟨a, Module.End.hasEigenvalue_iff.mpr ha⟩
      let be : Module.End.Eigenvalues B :=
        ⟨b, Module.End.hasEigenvalue_iff.mpr hb⟩
      exact le_iSup_of_le (ae, be) (by rfl)
  have hInt : DirectSum.IsInternal V := by
    apply hOrth.isInternal_iff.mpr
    rw [htop, Submodule.top_orthogonal_eq_bot]
  let b0 :
      OrthonormalBasis (Fin (Fintype.card ι)) ℂ
        (EuclideanSpace ℂ ι) :=
    hInt.subordinateOrthonormalBasis
      finrank_euclideanSpace hOrth
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (by simp)
  let b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) :=
    b0.reindex e
  let idx :
      ι → Module.End.Eigenvalues A × Module.End.Eigenvalues B :=
    fun i =>
      hInt.subordinateOrthonormalBasisIndex
        finrank_euclideanSpace (e.symm i) hOrth
  let lambda : ι → ℝ :=
    fun i => Complex.re ((idx i).1 : ℂ)
  let mu : ι → ℝ :=
    fun i => Complex.re ((idx i).2 : ℂ)
  let U : CMatrix ι :=
    (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis
  have hmem (i : ι) : b i ∈ V (idx i) := by
    dsimp [b, idx]
    rw [OrthonormalBasis.reindex_apply]
    exact hInt.subordinateOrthonormalBasis_subordinate
      finrank_euclideanSpace (e.symm i) hOrth
  have heigA (i : ι) :
      A (b i) = (lambda i : ℂ) • b i := by
    have hraw :=
      Module.End.mem_eigenspace_iff.mp (hmem i).1
    have hre : (lambda i : ℂ) = ((idx i).1 : ℂ) := by
      exact RCLike.conj_eq_iff_re.mp
        (hA.conj_eigenvalue_eq_self (idx i).1.property)
    rw [hre]
    exact hraw
  have heigB (i : ι) :
      B (b i) = (mu i : ℂ) • b i := by
    have hraw :=
      Module.End.mem_eigenspace_iff.mp (hmem i).2
    have hre : (mu i : ℂ) = ((idx i).2 : ℂ) := by
      exact RCLike.conj_eq_iff_re.mp
        (hB.conj_eigenvalue_eq_self (idx i).2.property)
    rw [hre]
    exact hraw
  have hvecA (j : ι) :
      Matrix.mulVec rho.matrix (b j).ofLp =
        (lambda j : ℂ) • (b j).ofLp := by
    have h := congrArg WithLp.ofLp (heigA j)
    simpa only [A, Matrix.toEuclideanLin_apply,
      WithLp.ofLp_toLp, WithLp.ofLp_smul] using h
  have hvecB (j : ι) :
      Matrix.mulVec sigma.matrix (b j).ofLp =
        (mu j : ℂ) • (b j).ofLp := by
    have h := congrArg WithLp.ofLp (heigB j)
    simpa only [B, Matrix.toEuclideanLin_apply,
      WithLp.ofLp_toLp, WithLp.ofLp_smul] using h
  have hrhoU :
      rho.matrix * U =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) := by
    ext i j
    have h := congrFun (hvecA j) i
    simpa [Matrix.mul_apply, U, Module.Basis.toMatrix_apply,
      EuclideanSpace.basisFun_repr, Matrix.diagonal, mul_comm]
      using h
  have hsigmaU :
      sigma.matrix * U =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) := by
    ext i j
    have h := congrFun (hvecB j) i
    simpa [Matrix.mul_apply, U, Module.Basis.toMatrix_apply,
      EuclideanSpace.basisFun_repr, Matrix.diagonal, mul_comm]
      using h
  have hUstarU : Matrix.conjTranspose U * U = 1 := by
    exact
      (EuclideanSpace.basisFun ι ℂ
        ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hUUstar : U * Matrix.conjTranspose U = 1 := by
    exact
      (EuclideanSpace.basisFun ι ℂ
        ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
  have hrho_diag :
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U := by
    calc
      rho.matrix = rho.matrix * 1 := by simp
      _ = rho.matrix * (U * Matrix.conjTranspose U) := by
        rw [hUUstar]
      _ = (rho.matrix * U) * Matrix.conjTranspose U := by
        noncomm_ring
      _ =
          U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
            Matrix.conjTranspose U := by
              rw [hrhoU]
  have hsigma_diag :
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U := by
    calc
      sigma.matrix = sigma.matrix * 1 := by simp
      _ = sigma.matrix * (U * Matrix.conjTranspose U) := by
        rw [hUUstar]
      _ = (sigma.matrix * U) * Matrix.conjTranspose U := by
        noncomm_ring
      _ =
          U * Matrix.diagonal (fun i => (mu i : ℂ)) *
            Matrix.conjTranspose U := by
              rw [hsigmaU]
  have hlambda_data :=
    diagonal_spectrum_nonneg_sum_one
      rho U lambda hUstarU hUUstar hrho_diag
  have hmu_data :=
    diagonal_spectrum_nonneg_sum_one
      sigma U mu hUstarU hUUstar hsigma_diag
  exact
    ⟨U, lambda, mu, hUstarU, hUUstar,
      hlambda_data.1, hmu_data.1,
      hlambda_data.2, hmu_data.2,
      hrho_diag, hsigma_diag⟩

/--
Restricting Alberti's optimization to positive operators diagonal in a common
orthonormal eigenbasis loses no value.  The right-hand side is written in the
coordinates of that basis, while the left-hand side uses the original state
matrices.
-/
theorem alberti_infimum_eq_diagonal_infimum_of_common_eigenbasis
    (rho sigma : State ι)
    (U : CMatrix ι) (lambda mu : ι → ℝ)
    (hUstarU : Matrix.conjTranspose U * U = 1)
    (hUUstar : U * Matrix.conjTranspose U = 1)
    (hrho :
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U)
    (hsigma :
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U) :
    sInf (albertiVariationalValues rho.matrix sigma.matrix) =
      sInf (diagonalAlbertiValues lambda mu) := by
  have hlambda_data :=
    diagonal_spectrum_nonneg_sum_one
      rho U lambda hUstarU hUUstar hrho
  have hmu_data :=
    diagonal_spectrum_nonneg_sum_one
      sigma U mu hUstarU hUUstar hsigma
  have hfid :=
    quantumFidelity_eq_bhattacharyya_of_common_diagonalization
      rho sigma U lambda mu hUstarU
      hlambda_data.1 hmu_data.1 hrho hsigma
  calc
    sInf (albertiVariationalValues rho.matrix sigma.matrix) =
        QITBench.OneShot.quantumFidelity
          rho.matrix sigma.matrix ^ 2 :=
      (alberti_variational_characterization rho sigma).symm
    _ = bhattacharyyaCoefficient lambda mu ^ 2 := by
      rw [hfid]
    _ = sInf (diagonalAlbertiValues lambda mu) :=
      (diagonal_alberti_infimum
        lambda mu hlambda_data.1 hmu_data.1
          hlambda_data.2 hmu_data.2).symm

/--
The common-eigenbasis formula transported back through the unitary change of
basis to the original density matrices.
-/
theorem quantumFidelity_eq_bhattacharyya_in_common_eigenbasis
    (rho sigma : State ι)
    (U : CMatrix ι) (lambda mu : ι → ℝ)
    (hUstarU : Matrix.conjTranspose U * U = 1)
    (hUUstar : U * Matrix.conjTranspose U = 1)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hmu : ∀ i, 0 ≤ mu i)
    (hlambda_sum : ∑ i, lambda i = 1)
    (hmu_sum : ∑ i, mu i = 1)
    (hrho :
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U)
    (hsigma :
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U) :
    QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix =
      bhattacharyyaCoefficient lambda mu := by
  exact
    quantumFidelity_eq_bhattacharyya_of_common_diagonalization
      rho sigma U lambda mu hUstarU
        hlambda hmu hrho hsigma

/--
Arbitrary commuting density operators have a common orthonormal eigenbasis in
which their quantum fidelity is the classical Bhattacharyya coefficient.
-/
theorem quantumFidelity_eq_bhattacharyya_of_commuting
    (rho sigma : State ι)
    (hcomm : rho.matrix * sigma.matrix = sigma.matrix * rho.matrix) :
    ∃ (U : CMatrix ι) (lambda mu : ι → ℝ),
      Matrix.conjTranspose U * U = 1 ∧
      U * Matrix.conjTranspose U = 1 ∧
      (∀ i, 0 ≤ lambda i) ∧
      (∀ i, 0 ≤ mu i) ∧
      (∑ i, lambda i) = 1 ∧
      (∑ i, mu i) = 1 ∧
      rho.matrix =
        U * Matrix.diagonal (fun i => (lambda i : ℂ)) *
          Matrix.conjTranspose U ∧
      sigma.matrix =
        U * Matrix.diagonal (fun i => (mu i : ℂ)) *
          Matrix.conjTranspose U ∧
      QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix =
        bhattacharyyaCoefficient lambda mu := by
  obtain
    ⟨U, lambda, mu, hUstarU, hUUstar,
      hlambda, hmu, hlambda_sum, hmu_sum,
      hrho, hsigma⟩ :=
    exists_common_orthonormal_eigenbasis_of_commute
      rho sigma hcomm
  refine
    ⟨U, lambda, mu, hUstarU, hUUstar,
      hlambda, hmu, hlambda_sum, hmu_sum,
      hrho, hsigma, ?_⟩
  exact
    quantumFidelity_eq_bhattacharyya_in_common_eigenbasis
      rho sigma U lambda mu hUstarU hUUstar
        hlambda hmu hlambda_sum hmu_sum hrho hsigma

end

end QITFormalized.AlbertiCommutingCase
