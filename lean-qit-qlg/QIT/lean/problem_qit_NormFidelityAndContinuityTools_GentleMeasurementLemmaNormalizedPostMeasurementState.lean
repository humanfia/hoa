import QITBench.Base.OneShot

/-!
# Gentle measurement with a normalized post-measurement state

This file formalizes the finite-dimensional gentle measurement statement for
the canonical square-root instrument.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.NormFidelityAndContinuityTools

open QITBench
open QITBench.OneShot

universe u

noncomputable section

set_option maxHeartbeats 1000000

private def matrixEuclidean
    {d : Type u} [Fintype d]
    (A : CMatrix d) : EuclideanSpace ℂ (d × d) :=
  WithLp.toLp 2 fun ij => A ij.1 ij.2

private lemma matrixEuclidean_inner
    {d : Type u} [Fintype d] [DecidableEq d]
    (A B : CMatrix d) :
    inner ℂ (matrixEuclidean A) (matrixEuclidean B) =
      (A.conjTranspose * B).trace := by
  simp only [matrixEuclidean, PiLp.inner_apply, RCLike.inner_apply]
  rw [Fintype.sum_prod_type, Matrix.trace, Finset.sum_comm]
  simp [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]

private lemma norm_trace_mul_le
    {d : Type u} [Fintype d] [DecidableEq d]
    (A B : CMatrix d) :
    ‖(A * B).trace‖ ≤
      Real.sqrt (Complex.re ((A * A.conjTranspose).trace)) *
        Real.sqrt (Complex.re ((B.conjTranspose * B).trace)) := by
  have hinner := norm_inner_le_norm (𝕜 := ℂ)
    (matrixEuclidean A.conjTranspose) (matrixEuclidean B)
  rw [matrixEuclidean_inner, Matrix.conjTranspose_conjTranspose] at hinner
  calc
    ‖(A * B).trace‖ ≤
        ‖matrixEuclidean A.conjTranspose‖ * ‖matrixEuclidean B‖ := hinner
    _ = Real.sqrt (Complex.re ((A * A.conjTranspose).trace)) *
        Real.sqrt (Complex.re ((B.conjTranspose * B).trace)) := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (matrixEuclidean A.conjTranspose),
        norm_eq_sqrt_re_inner (𝕜 := ℂ) (matrixEuclidean B),
        matrixEuclidean_inner, matrixEuclidean_inner,
        Matrix.conjTranspose_conjTranspose]
      rfl

private lemma trace_adjoint_mul_unitary_hilbertSchmidt
    {d : Type u} [Fintype d] [DecidableEq d]
    (A U : CMatrix d) (hUright : U * U.conjTranspose = 1) :
    (((A.conjTranspose * U).conjTranspose *
        (A.conjTranspose * U)).trace) =
      (A * A.conjTranspose).trace := by
  calc
    ((A.conjTranspose * U).conjTranspose *
        (A.conjTranspose * U)).trace =
        (U.conjTranspose * (A * A.conjTranspose) * U).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      congr 1
      noncomm_ring
    _ = (U * U.conjTranspose * (A * A.conjTranspose)).trace :=
      Matrix.trace_mul_cycle _ _ _
    _ = (A * A.conjTranspose).trace := by rw [hUright, one_mul]

private lemma trace_mul_nonneg_of_posSemidef
    {d : Type u} [Fintype d] [DecidableEq d]
    {A B : CMatrix d}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have hsqrtPos : (matrixSqrt B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hsqrt_sq : matrixSqrt B * matrixSqrt B = B := by
    simpa [matrixSqrt, pow_two] using (CFC.sq_sqrt B hB.nonneg)
  have hsandwich :
      (matrixSqrt B * A * matrixSqrt B).PosSemidef := by
    simpa [hsqrtPos.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (matrixSqrt B)
  have htrace :
      (matrixSqrt B * A * matrixSqrt B).trace = (A * B).trace := by
    calc
      (matrixSqrt B * A * matrixSqrt B).trace =
          (matrixSqrt B * matrixSqrt B * A).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = (A * (matrixSqrt B * matrixSqrt B)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (A * B).trace := by rw [hsqrt_sq]
  rw [← htrace]
  exact hsandwich.trace_nonneg

private lemma matrixSqrt_le_one
    {d : Type u} [Fintype d] [DecidableEq d]
    (M : CMatrix d) (hMpos : M.PosSemidef) (hMle : M ≤ 1) :
    matrixSqrt M ≤ 1 := by
  let S : CMatrix d := matrixSqrt M
  have hSpos : S.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hSsq : S * S = M := by
    simpa [S, matrixSqrt, pow_two] using (CFC.sq_sqrt M hMpos.nonneg)
  let hSH := hSpos.isHermitian
  let U := hSH.eigenvectorUnitary
  let V : CMatrix d := U
  let D : CMatrix d :=
    Matrix.diagonal (Complex.ofReal ∘ hSH.eigenvalues)
  have hVunit : IsUnit V := by
    exact Unitary.isUnit_coe
  have hVstar : V * star V = 1 := by
    exact Unitary.coe_mul_star_self U
  have hstarV : star V * V = 1 := by
    exact Unitary.coe_star_mul_self U
  have hspec : S = V * D * star V := by
    simpa [U, V, D, Unitary.conjStarAlgAut_apply] using hSH.spectral_theorem
  have hcompEq : 1 - M = V * (1 - D * D) * star V := by
    rw [← hSsq, hspec]
    calc
      1 - (V * D * star V) * (V * D * star V) =
          1 - V * D * (star V * V) * D * star V := by
        noncomm_ring
      _ = 1 - V * D * D * star V := by
        rw [hstarV]
        noncomm_ring
      _ = V * star V - V * D * D * star V := by rw [hVstar]
      _ = V * (1 - D * D) * star V := by noncomm_ring
  have hdiagSq : (1 - D * D).PosSemidef := by
    apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hVunit).mp
    rw [← hcompEq]
    exact hMle
  have hlambda : ∀ i, hSH.eigenvalues i ≤ 1 := by
    intro i
    have hiC := Matrix.PosSemidef.diag_nonneg (i := i) hdiagSq
    have hi : 0 ≤ 1 - (hSH.eigenvalues i) ^ 2 := by
      have hire := (Complex.nonneg_iff.mp hiC).1
      simpa [D, Matrix.mul_apply, pow_two] using hire
    nlinarith [hSpos.eigenvalues_nonneg i]
  have hdiagOne : (1 - D).PosSemidef := by
    have hdiag :
        (Matrix.diagonal
          (fun i => ((1 - hSH.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      change (0 : ℂ) ≤ ((1 - hSH.eigenvalues i : ℝ) : ℂ)
      rw [Complex.nonneg_iff]
      simp [hlambda i]
    convert hdiag using 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hconj : (V * (1 - D) * star V).PosSemidef :=
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hVunit).mpr hdiagOne
  have heq : V * (1 - D) * star V = 1 - S := by
    calc
      V * (1 - D) * star V = V * star V - V * D * star V := by
        noncomm_ring
      _ = 1 - S := by rw [hVstar, hspec]
  rw [heq] at hconj
  exact hconj

private noncomputable def hermitianSign
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) : CMatrix d :=
  hX.cfc (fun x => if x < 0 then -1 else 1)

private lemma hermitianSign_unitary
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    hermitianSign hX ∈ unitary (CMatrix d) := by
  let f : d → ℝ := fun i => if hX.eigenvalues i < 0 then -1 else 1
  let D : CMatrix d := Matrix.diagonal fun i => (f i : ℂ)
  have hf : ∀ i, f i = -1 ∨ f i = 1 := by
    intro i
    simp only [f]
    split_ifs <;> simp
  have hD : D ∈ unitary (CMatrix d) := by
    rw [Unitary.mem_iff]
    constructor <;>
      simp only [D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Pi.star_apply, RCLike.star_def, Matrix.diagonal_mul_diagonal]
    · ext i j
      simp only [Matrix.diagonal_apply]
      split_ifs with hij
      · subst j
        rcases hf i with hi | hi <;> simp [hi]
      · simp [hij]
    · ext i j
      simp only [Matrix.diagonal_apply]
      split_ifs with hij
      · subst j
        rcases hf i with hi | hi <;> simp [hi]
      · simp [hij]
  let e := Unitary.conjStarAlgAut ℝ (CMatrix d) hX.eigenvectorUnitary
  have heD : e D ∈ unitary (CMatrix d) := by
    rw [Unitary.mem_iff] at hD ⊢
    constructor
    · calc
        star (e D) * e D = e (star D) * e D := by rw [map_star]
        _ = e (star D * D) := (map_mul e _ _).symm
        _ = 1 := by rw [hD.1, map_one]
    · calc
        e D * star (e D) = e D * e (star D) := by rw [map_star]
        _ = e (D * star D) := (map_mul e _ _).symm
        _ = 1 := by rw [hD.2, map_one]
  simpa [hermitianSign, Matrix.IsHermitian.cfc, e, D, f] using heD

private lemma mul_hermitianSign_eq_abs
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    X * hermitianSign hX = CFC.abs X := by
  rw [CFC.abs_eq_cfc_norm X hX]
  rw [hX.cfc_eq]
  change X * hX.cfc (fun x => if x < 0 then -1 else 1) =
    hX.cfc fun x => ‖x‖
  calc
    X * hX.cfc (fun x => if x < 0 then -1 else 1) =
        ((Unitary.conjStarAlgAut ℂ (CMatrix d)) hX.eigenvectorUnitary)
            (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) *
          hX.cfc (fun x => if x < 0 then -1 else 1) :=
      congrArg (fun Z => Z * hX.cfc (fun x => if x < 0 then -1 else 1))
        hX.spectral_theorem
    _ = hX.cfc (fun x => ‖x‖) := by
      unfold Matrix.IsHermitian.cfc
      rw [← map_mul]
      congr 1
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Function.comp_apply]
      by_cases hi : hX.eigenvalues i < 0
      · simp [hi, abs_of_neg hi]
      · simp [hi, abs_of_nonneg (le_of_not_gt hi)]

private lemma traceNorm_eq_re_trace_mul_hermitianSign
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    traceNorm X = Complex.re ((X * hermitianSign hX).trace) := by
  rw [traceNorm, matrixSqrt]
  have habs :
      CFC.sqrt (X.conjTranspose * X) = CFC.abs X := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose]
  rw [habs, ← mul_hermitianSign_eq_abs hX]

/-- The normalized state obtained after accepting the effect `M` using the
canonical square-root measurement instrument.

The nonzero trace assumption is the normalization side condition.  It is
necessary because the source permits `ε = 1`, in which case its remaining
assumptions alone do not rule out an outcome of probability zero. -/
noncomputable def normalizedSqrtPostMeasurementState
    {d : Type u} [Fintype d] [DecidableEq d]
    (ρ : State d) (M : CMatrix d)
    (hMpos : M.PosSemidef)
    (htrace : (M * ρ.matrix).trace ≠ 0) :
    State d where
  matrix :=
    ((M * ρ.matrix).trace)⁻¹ •
      (matrixSqrt M * ρ.matrix * matrixSqrt M)
  pos := by
    have hsqrtPos : (matrixSqrt M).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
    have hnum :
        (matrixSqrt M * ρ.matrix * matrixSqrt M).PosSemidef := by
      simpa [hsqrtPos.isHermitian.eq] using
        ρ.pos.conjTranspose_mul_mul_same (matrixSqrt M)
    have hsqrt_sq : matrixSqrt M * matrixSqrt M = M := by
      simpa [matrixSqrt, pow_two] using
        (CFC.sq_sqrt M hMpos.nonneg)
    have hnum_trace :
        (matrixSqrt M * ρ.matrix * matrixSqrt M).trace =
          (M * ρ.matrix).trace := by
      rw [Matrix.trace_mul_cycle, hsqrt_sq]
    apply hnum.smul
    apply inv_nonneg.mpr
    rw [← hnum_trace]
    exact hnum.trace_nonneg
  trace_eq_one := by
    have hsqrt_sq : matrixSqrt M * matrixSqrt M = M := by
      simpa [matrixSqrt, pow_two] using
        (CFC.sq_sqrt M hMpos.nonneg)
    have hnum_trace :
        (matrixSqrt M * ρ.matrix * matrixSqrt M).trace =
          (M * ρ.matrix).trace := by
      rw [Matrix.trace_mul_cycle, hsqrt_sq]
    rw [Matrix.trace_smul, hnum_trace]
    exact inv_mul_cancel₀ htrace

/-- The matrix of the normalized square-root post-measurement state is the
displayed normalized update from the source statement. -/
@[simp]
theorem normalizedSqrtPostMeasurementState_matrix
    {d : Type u} [Fintype d] [DecidableEq d]
    (ρ : State d) (M : CMatrix d)
    (hMpos : M.PosSemidef)
    (htrace : (M * ρ.matrix).trace ≠ 0) :
    (normalizedSqrtPostMeasurementState ρ M hMpos htrace).matrix =
      ((M * ρ.matrix).trace)⁻¹ •
        (matrixSqrt M * ρ.matrix * matrixSqrt M) :=
  rfl

/-- Gentle measurement lemma for the normalized state produced by the
canonical square-root instrument. -/
theorem gentleMeasurement_normalizedPostMeasurementState
    {d : Type u} [Fintype d] [DecidableEq d]
    (ρ : State d) (M : CMatrix d) (ε : ℝ)
    (hMpos : M.PosSemidef)
    (hMle : M ≤ 1)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsuccess :
      1 - ε ≤ Complex.re ((M * ρ.matrix).trace))
    (htrace : (M * ρ.matrix).trace ≠ 0) :
    traceNorm
        ((normalizedSqrtPostMeasurementState ρ M hMpos htrace).matrix -
          ρ.matrix) ≤
      2 * Real.sqrt ε + ε := by
  let S : CMatrix d := matrixSqrt M
  let R : CMatrix d := matrixSqrt ρ.matrix
  let τ : CMatrix d := S * ρ.matrix * S
  let p : ℝ := Complex.re ((M * ρ.matrix).trace)
  let Δ : CMatrix d := (1 - S) * (1 - S)
  have hSpos : S.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hRpos : R.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ.matrix)
  have hSsq : S * S = M := by
    simpa [S, matrixSqrt, pow_two] using (CFC.sq_sqrt M hMpos.nonneg)
  have hRsq : R * R = ρ.matrix := by
    simpa [R, matrixSqrt, pow_two] using
      (CFC.sq_sqrt ρ.matrix ρ.pos.nonneg)
  have hqnonneg : 0 ≤ (M * ρ.matrix).trace :=
    trace_mul_nonneg_of_posSemidef hMpos ρ.pos
  have hqreal : (M * ρ.matrix).trace = (p : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [p] using (Complex.nonneg_iff.mp hqnonneg).2.symm
  have hp0 : 0 ≤ p := by
    exact (Complex.nonneg_iff.mp hqnonneg).1
  have hcompPos : (1 - M).PosSemidef := by
    exact hMle
  have hcompTrace :
      0 ≤ Complex.re (((1 - M) * ρ.matrix).trace) :=
    (Complex.nonneg_iff.mp
      (trace_mul_nonneg_of_posSemidef hcompPos ρ.pos)).1
  have hp1 : p ≤ 1 := by
    simp only [sub_mul, one_mul, Matrix.trace_sub, ρ.trace_eq_one,
      Complex.sub_re, Complex.one_re] at hcompTrace
    linarith
  have hp : 0 < p := lt_of_le_of_ne hp0 fun hpzero => by
    apply htrace
    rw [hqreal, ← hpzero]
    simp
  have hSle : S ≤ 1 := by
    exact matrixSqrt_le_one M hMpos hMle
  have hOneSubSPos : (1 - S).PosSemidef := by
    exact hSle
  have hcomm : Commute S (1 - S) := by
    change S * (1 - S) = (1 - S) * S
    noncomm_ring
  have hSOneSubS : 0 ≤ S * (1 - S) :=
    hcomm.mul_nonneg hSpos.nonneg hOneSubSPos.nonneg
  have hSminusM : (S - M).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    rw [← hSsq]
    convert hSOneSubS using 1
    noncomm_ring
  have hDeltaPos : Δ.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      ((Commute.refl (1 - S)).mul_nonneg
        hOneSubSPos.nonneg hOneSubSPos.nonneg)
  have hDeltaLe : Δ ≤ 1 - M := by
    rw [Matrix.le_iff]
    have hadd := hSminusM.add hSminusM
    convert hadd using 1
    dsimp only [Δ]
    calc
      1 - M - (1 - S) * (1 - S) =
          S - M + (S - S * S) := by noncomm_ring
      _ = S - M + (S - M) := by rw [hSsq]
  have hΔtrace0 :
      0 ≤ Complex.re ((Δ * ρ.matrix).trace) :=
    (Complex.nonneg_iff.mp
      (trace_mul_nonneg_of_posSemidef hDeltaPos ρ.pos)).1
  have hΔtraceLe :
      Complex.re ((Δ * ρ.matrix).trace) ≤ 1 - p := by
    have hdiffPos : ((1 - M) - Δ).PosSemidef := hDeltaLe
    have hdiffTrace :
        0 ≤ Complex.re ((((1 - M) - Δ) * ρ.matrix).trace) :=
      (Complex.nonneg_iff.mp
        (trace_mul_nonneg_of_posSemidef hdiffPos ρ.pos)).1
    simp only [sub_mul, one_mul, Matrix.trace_sub, ρ.trace_eq_one,
      Complex.sub_re, Complex.one_re] at hdiffTrace
    linarith
  have hτpos : τ.PosSemidef := by
    simpa [τ, hSpos.isHermitian.eq] using
      ρ.pos.conjTranspose_mul_mul_same S
  have hτtrace : τ.trace = (p : ℂ) := by
    dsimp only [τ]
    rw [Matrix.trace_mul_cycle, hSsq, hqreal]
  let X : CMatrix d :=
    (normalizedSqrtPostMeasurementState ρ M hMpos htrace).matrix -
      ρ.matrix
  have hX : X.IsHermitian := by
    exact
      (normalizedSqrtPostMeasurementState ρ M hMpos htrace).pos.isHermitian.sub
        ρ.pos.isHermitian
  let U : CMatrix d := hermitianSign hX
  have hU : U ∈ unitary (CMatrix d) := by
    exact hermitianSign_unitary hX
  have hUleft : U.conjTranspose * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).1
  have hUright : U * U.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).2
  have hterm1 :
      ‖(((1 - S) * ρ.matrix * U).trace)‖ ≤
        Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by
    have hcs := norm_trace_mul_le ((1 - S) * R) (R * U)
    have hprod :
        ((1 - S) * R) * (R * U) = (1 - S) * ρ.matrix * U := by
      rw [← hRsq]
      noncomm_ring
    have hleft :
        ((((1 - S) * R) * ((1 - S) * R).conjTranspose).trace) =
          (Δ * ρ.matrix).trace := by
      calc
        (((1 - S) * R) * ((1 - S) * R).conjTranspose).trace =
            ((1 - S) * (R * R) * (1 - S)).trace := by
          rw [Matrix.conjTranspose_mul, hRpos.isHermitian.eq,
            hOneSubSPos.isHermitian.eq]
          congr 1
          noncomm_ring
        _ = ((1 - S) * (1 - S) * (R * R)).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = (Δ * ρ.matrix).trace := by rw [hRsq]
    have hright :
        (((R * U).conjTranspose * (R * U)).trace) = 1 := by
      calc
        ((R * U).conjTranspose * (R * U)).trace =
            (U.conjTranspose * ρ.matrix * U).trace := by
          rw [Matrix.conjTranspose_mul, hRpos.isHermitian.eq, ← hRsq]
          congr 1
          noncomm_ring
        _ = (U * U.conjTranspose * ρ.matrix).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = 1 := by rw [hUright, one_mul, ρ.trace_eq_one]
    rw [hprod, hleft, hright] at hcs
    simpa using hcs
  have hterm2 :
      ‖((S * ρ.matrix * (1 - S) * U).trace)‖ ≤
        Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by
    have hcs := norm_trace_mul_le (S * R) (R * (1 - S) * U)
    have hprod :
        (S * R) * (R * (1 - S) * U) =
          S * ρ.matrix * (1 - S) * U := by
      rw [← hRsq]
      noncomm_ring
    have hleft :
        (((S * R) * (S * R).conjTranspose).trace) = (p : ℂ) := by
      calc
        ((S * R) * (S * R).conjTranspose).trace =
            (S * ρ.matrix * S).trace := by
          rw [Matrix.conjTranspose_mul, hRpos.isHermitian.eq,
            hSpos.isHermitian.eq, ← hRsq]
          congr 1
          noncomm_ring
        _ = (p : ℂ) := by simpa [τ] using hτtrace
    have hright :
        (((R * (1 - S) * U).conjTranspose *
          (R * (1 - S) * U)).trace) =
            (Δ * ρ.matrix).trace := by
      calc
        ((R * (1 - S) * U).conjTranspose *
            (R * (1 - S) * U)).trace =
            (U.conjTranspose * ((1 - S) * ρ.matrix * (1 - S)) * U).trace := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            hRpos.isHermitian.eq, hOneSubSPos.isHermitian.eq, ← hRsq]
          congr 1
          noncomm_ring
        _ = (U * U.conjTranspose *
            ((1 - S) * ρ.matrix * (1 - S))).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = ((1 - S) * ρ.matrix * (1 - S)).trace := by
          rw [hUright, one_mul]
        _ = ((1 - S) * (1 - S) * ρ.matrix).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = (Δ * ρ.matrix).trace := rfl
    rw [hprod, hleft, hright] at hcs
    calc
      ‖(S * ρ.matrix * (1 - S) * U).trace‖ ≤
          Real.sqrt p *
            Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by
        simpa using hcs
      _ ≤ Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) :=
        mul_le_of_le_one_left (Real.sqrt_nonneg _)
          (Real.sqrt_le_one.mpr hp1)
  have hdiffU :
      ‖(((τ - ρ.matrix) * U).trace)‖ ≤
        2 * Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by
    have hmat :
        (τ - ρ.matrix) * U =
          -((1 - S) * ρ.matrix * U) -
            (S * ρ.matrix * (1 - S) * U) := by
      dsimp only [τ]
      noncomm_ring
    rw [hmat, Matrix.trace_sub, Matrix.trace_neg]
    calc
      ‖-((1 - S) * ρ.matrix * U).trace -
          (S * ρ.matrix * (1 - S) * U).trace‖ ≤
          ‖-((1 - S) * ρ.matrix * U).trace‖ +
            ‖(S * ρ.matrix * (1 - S) * U).trace‖ :=
        norm_sub_le _ _
      _ ≤ Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) +
          Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by
        gcongr
        simpa using hterm1
      _ = 2 * Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) := by ring
  have hτU : ‖((τ * U).trace)‖ ≤ p := by
    have hcs := norm_trace_mul_le (S * R) (R * S * U)
    have hprod : (S * R) * (R * S * U) = τ * U := by
      dsimp only [τ]
      rw [← hRsq]
      noncomm_ring
    have hleft :
        (((S * R) * (S * R).conjTranspose).trace) = (p : ℂ) := by
      calc
        ((S * R) * (S * R).conjTranspose).trace =
            (S * ρ.matrix * S).trace := by
          rw [Matrix.conjTranspose_mul, hRpos.isHermitian.eq,
            hSpos.isHermitian.eq, ← hRsq]
          congr 1
          noncomm_ring
        _ = (p : ℂ) := by simpa [τ] using hτtrace
    have hright :
        (((R * S * U).conjTranspose * (R * S * U)).trace) =
          (p : ℂ) := by
      have heq : R * S * U = (S * R).conjTranspose * U := by
        rw [Matrix.conjTranspose_mul, hSpos.isHermitian.eq,
          hRpos.isHermitian.eq]
      rw [heq, trace_adjoint_mul_unitary_hilbertSchmidt _ _ hUright,
        hleft]
    rw [hprod, hleft, hright] at hcs
    simpa [Real.mul_self_sqrt hp0] using hcs
  have hcoeff0 : 0 ≤ p⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ hp]
    exact hp1
  have hcorrection :
      ‖(((((p : ℂ)⁻¹ - 1) • τ) * U).trace)‖ ≤ 1 - p := by
    have hcoeffCast :
        (p : ℂ)⁻¹ - 1 = ((p⁻¹ - 1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one]
    calc
      ‖(((((p : ℂ)⁻¹ - 1) • τ) * U).trace)‖ =
          ‖((p : ℂ)⁻¹ - 1) * (τ * U).trace‖ := by
        rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
      _ = (p⁻¹ - 1) * ‖(τ * U).trace‖ := by
        rw [norm_mul, hcoeffCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hcoeff0]
      _ ≤ (p⁻¹ - 1) * p :=
        mul_le_mul_of_nonneg_left hτU hcoeff0
      _ = 1 - p := by
        field_simp
  have hXdecomp :
      X = (τ - ρ.matrix) + (((p : ℂ)⁻¹ - 1) • τ) := by
    dsimp only [X]
    rw [normalizedSqrtPostMeasurementState_matrix, hqreal]
    change
      (p : ℂ)⁻¹ • τ - ρ.matrix =
        τ - ρ.matrix + ((p : ℂ)⁻¹ - 1) • τ
    module
  change traceNorm X ≤ 2 * Real.sqrt ε + ε
  rw [traceNorm_eq_re_trace_mul_hermitianSign hX]
  change Complex.re ((X * U).trace) ≤ 2 * Real.sqrt ε + ε
  rw [hXdecomp, add_mul, Matrix.trace_add, Complex.add_re]
  have hfailureLe : 1 - p ≤ ε := by
    dsimp only [p]
    linarith
  have hΔtraceEps :
      Complex.re ((Δ * ρ.matrix).trace) ≤ ε :=
    hΔtraceLe.trans hfailureLe
  have hsqrtLe :
      Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hΔtraceEps
  calc
    Complex.re (((τ - ρ.matrix) * U).trace) +
        Complex.re (((((p : ℂ)⁻¹ - 1) • τ) * U).trace) ≤
        ‖(((τ - ρ.matrix) * U).trace)‖ +
          ‖(((((p : ℂ)⁻¹ - 1) • τ) * U).trace)‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
    _ ≤ 2 * Real.sqrt (Complex.re ((Δ * ρ.matrix).trace)) +
        (1 - p) :=
      add_le_add hdiffU hcorrection
    _ ≤ 2 * Real.sqrt ε + ε := by linarith [hε.1]

end

end QITFormalized.NormFidelityAndContinuityTools
