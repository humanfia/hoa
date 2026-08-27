import QITBench.Base.OneShot

/-!
# Universal upper bound in Alberti's theorem

For arbitrary finite-dimensional density operators `ρ` and `σ`, every
positive-definite operator `P` gives the upper bound

`F(ρ, σ)² ≤ Tr(ρP) Tr(σP⁻¹)`.

There is deliberately no commutativity hypothesis on the density operators.
The complex matrix traces are coerced to their mathematically real values by
taking real parts.  `Matrix.PosDef P` expresses `P > 0` and, in particular,
implies that `P` is invertible.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.NormFidelityAndContinuityTools

open QITBench

universe u

noncomputable section

variable {d : Type u} [Fintype d] [DecidableEq d]

private theorem inner_mulVec_eigenvectorBasis
    (A : CMatrix d)
    (i j : d) :
    let C := A.conjTranspose * A
    let hC : C.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
    let e := hC.isHermitian.eigenvectorBasis
    inner ℂ (Matrix.toEuclideanLin A (e i)) (Matrix.toEuclideanLin A (e j)) =
      (hC.isHermitian.eigenvalues j : ℂ) * inner ℂ (e i) (e j) := by
  dsimp only
  let C : CMatrix d := A.conjTranspose * A
  let hC : C.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  let e := hC.isHermitian.eigenvectorBasis
  calc
    inner ℂ (Matrix.toEuclideanLin A (e i)) (Matrix.toEuclideanLin A (e j)) =
        inner ℂ (e i)
          ((LinearMap.adjoint (Matrix.toEuclideanLin A)) (Matrix.toEuclideanLin A (e j))) := by
            symm
            exact LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A) (e i)
              (Matrix.toEuclideanLin A (e j))
    _ = inner ℂ (e i) (Matrix.toEuclideanLin C (e j)) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
      change inner ℂ (e i)
          (((Matrix.toLpLin 2 2) A.conjTranspose) (((Matrix.toLpLin 2 2) A) (e j))) =
        inner ℂ (e i) (((Matrix.toLpLin 2 2) C) (e j))
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    _ = inner ℂ (e i) ((hC.isHermitian.eigenvalues j : ℂ) • e j) := by
      congr 1
      rw [Matrix.toLpLin_apply]
      simpa [C, e] using
        congrArg (WithLp.toLp 2) (hC.isHermitian.mulVec_eigenvectorBasis j)
    _ = (hC.isHermitian.eigenvalues j : ℂ) * inner ℂ (e i) (e j) := by
      rw [inner_smul_right]

private theorem exists_unitary_trace_sqrt_eq
    (A : CMatrix d) :
    ∃ U : Matrix.unitaryGroup d ℂ,
      (CFC.sqrt (A.conjTranspose * A)).trace =
        ((U : CMatrix d).conjTranspose * A).trace := by
  let C : CMatrix d := A.conjTranspose * A
  let hC : C.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  let e := hC.isHermitian.eigenvectorBasis
  let lam : d → ℝ := hC.isHermitian.eigenvalues
  let f : d → EuclideanSpace ℂ d := fun i => Matrix.toEuclideanLin A (e i)
  let s : Set d := {i | lam i ≠ 0}
  let v : d → EuclideanSpace ℂ d := fun i =>
    ((Real.sqrt (lam i) : ℂ)⁻¹) • f i
  have hlam (i : d) : 0 ≤ lam i := by
    exact hC.eigenvalues_nonneg i
  have hfinner (i j : d) :
      inner ℂ (f i) (f j) =
        (lam j : ℂ) * (if i = j then 1 else 0) := by
    rw [show f i = Matrix.toEuclideanLin A (e i) from rfl,
      show f j = Matrix.toEuclideanLin A (e j) from rfl,
      inner_mulVec_eigenvectorBasis]
    rw [e.inner_eq_ite]
  have hfnorm_sq (i : d) : ‖f i‖ ^ 2 = lam i := by
    rw [@norm_sq_eq_re_inner ℂ, hfinner i i]
    simp
  have hfnorm (i : d) : ‖f i‖ = Real.sqrt (lam i) := by
    calc
      ‖f i‖ = Real.sqrt (‖f i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (lam i) := by rw [hfnorm_sq]
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.restrict_apply]
    rw [show v i = ((Real.sqrt (lam i) : ℂ)⁻¹) • f i from rfl,
      show v j = ((Real.sqrt (lam j) : ℂ)⁻¹) • f j from rfl,
      inner_smul_left, inner_smul_right, hfinner]
    by_cases hij : i = j
    · subst j
      simp only [if_pos]
      have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hi)
      rw [map_inv₀]
      rw [starRingEnd_apply]
      rw [RCLike.star_def, Complex.conj_ofReal]
      change ((Real.sqrt (lam i) : ℂ)⁻¹) *
          ((Real.sqrt (lam i) : ℂ)⁻¹ * ((lam i : ℂ) * 1)) = 1
      field_simp [Real.sqrt_ne_zero'.mpr hpos]
      exact_mod_cast (Real.sq_sqrt hpos.le).symm
    · simp [hij, Subtype.ext_iff]
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (finrank_euclideanSpace (𝕜 := ℂ) (ι := d))
  have hdiag (i : d) :
      inner ℂ (b i) (f i) = (Real.sqrt (lam i) : ℂ) := by
    by_cases hi : lam i = 0
    · have hfzero : f i = 0 := by
        apply norm_eq_zero.mp
        rw [hfnorm, hi, Real.sqrt_zero]
      simp [hfzero, hi]
    · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hi)
      rw [hb i hi]
      rw [show v i = ((Real.sqrt (lam i) : ℂ)⁻¹) • f i from rfl,
        inner_smul_left, hfinner, if_pos rfl]
      rw [map_inv₀, starRingEnd_apply]
      rw [RCLike.star_def, Complex.conj_ofReal]
      change ((Real.sqrt (lam i) : ℂ)⁻¹) * ((lam i : ℂ) * 1) =
        (Real.sqrt (lam i) : ℂ)
      field_simp [Real.sqrt_ne_zero'.mpr hpos]
      exact_mod_cast (Real.sq_sqrt hpos.le).symm
  let W : Matrix.unitaryGroup d ℂ :=
    ⟨(EuclideanSpace.basisFun d ℂ).toBasis.toMatrix b,
      (EuclideanSpace.basisFun d ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  let V : Matrix.unitaryGroup d ℂ := hC.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup d ℂ := W * star V
  refine ⟨U, ?_⟩
  have hsqrttrace :
      (CFC.sqrt C).trace = ∑ i, (Real.sqrt (lam i) : ℂ) := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt C hC.nonneg,
      hC.isHermitian.cfc_eq]
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Matrix.trace_diagonal, lam, hlam]
  have hUtrace :
      (((U : Matrix.unitaryGroup d ℂ) : CMatrix d).conjTranspose * A).trace =
        ∑ i, (Real.sqrt (lam i) : ℂ) := by
    calc
      (((U : Matrix.unitaryGroup d ℂ) : CMatrix d).conjTranspose * A).trace =
          (((V : Matrix.unitaryGroup d ℂ) : CMatrix d) *
            ((W : Matrix.unitaryGroup d ℂ) : CMatrix d).conjTranspose * A).trace := by
              simp [U, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
      _ = (((W : Matrix.unitaryGroup d ℂ) : CMatrix d).conjTranspose * A *
          ((V : Matrix.unitaryGroup d ℂ) : CMatrix d)).trace := by
            exact (Matrix.trace_mul_cycle
              (((W : Matrix.unitaryGroup d ℂ) : CMatrix d).conjTranspose) A
              ((V : Matrix.unitaryGroup d ℂ) : CMatrix d)).symm
      _ = ∑ i, inner ℂ (b i) (f i) := by
        rw [Matrix.trace]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, W, V,
          Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
          Matrix.IsHermitian.eigenvectorUnitary_apply, f, Matrix.toLpLin_apply,
          PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, Matrix.mulVec, dotProduct]
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext x
        simp [e, mul_assoc]
      _ = ∑ i, (Real.sqrt (lam i) : ℂ) := by
        exact Finset.sum_congr rfl fun i _ => hdiag i
  simpa [C] using hsqrttrace.trans hUtrace.symm

private theorem trace_mul_conjTranspose_norm_sq_le
    (X Y : CMatrix d) :
    ‖(X * Y.conjTranspose).trace‖ ^ 2 ≤
      Complex.re (X * X.conjTranspose).trace *
        Complex.re (Y * Y.conjTranspose).trace := by
  letI : SeminormedAddCommGroup (CMatrix d) :=
    Matrix.toMatrixSeminormedAddCommGroup (1 : CMatrix d) Matrix.PosSemidef.one
  letI : InnerProductSpace ℂ (CMatrix d) :=
    Matrix.toMatrixInnerProductSpace (1 : CMatrix d) Matrix.PosSemidef.one
  have hcs := norm_inner_le_norm (𝕜 := ℂ) Y X
  change ‖(X * (1 : CMatrix d) * Y.conjTranspose).trace‖ ≤ ‖Y‖ * ‖X‖ at hcs
  simp only [Matrix.mul_one] at hcs
  have hX : ‖X‖ ^ 2 = Complex.re (X * X.conjTranspose).trace := by
    rw [@norm_sq_eq_re_inner ℂ]
    change Complex.re (X * (1 : CMatrix d) * X.conjTranspose).trace =
      Complex.re (X * X.conjTranspose).trace
    simp
  have hY : ‖Y‖ ^ 2 = Complex.re (Y * Y.conjTranspose).trace := by
    rw [@norm_sq_eq_re_inner ℂ]
    change Complex.re (Y * (1 : CMatrix d) * Y.conjTranspose).trace =
      Complex.re (Y * Y.conjTranspose).trace
    simp
  have hsquare :
      ‖(X * Y.conjTranspose).trace‖ ^ 2 ≤ (‖Y‖ * ‖X‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [mul_pow, hX, hY] at hsquare
  simpa [mul_comm] using hsquare

/-- The pointwise squared-fidelity upper bound furnished by Alberti's
variational characterization. -/
theorem quantumFidelity_sq_le_albertiTraceProduct
    (ρ σ : State d) (P : CMatrix d) (hP : P.PosDef) :
    OneShot.quantumFidelity ρ.matrix σ.matrix ^ 2 ≤
      Complex.re (ρ.matrix * P).trace *
        Complex.re (σ.matrix * P⁻¹).trace := by
  let rS : CMatrix d := CFC.sqrt ρ.matrix
  let sS : CMatrix d := CFC.sqrt σ.matrix
  let pS : CMatrix d := CFC.sqrt P
  let qS : CMatrix d := CFC.sqrt P⁻¹
  have hrSpos : rS.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ.matrix)
  have hsSpos : sS.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.matrix)
  have hpSpos : pS.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hqSpos : qS.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P⁻¹)
  have hrSsq : rS * rS = ρ.matrix := by
    simpa [rS, pow_two] using CFC.sq_sqrt ρ.matrix ρ.pos.nonneg
  have hsSsq : sS * sS = σ.matrix := by
    simpa [sS, pow_two] using CFC.sq_sqrt σ.matrix σ.pos.nonneg
  have hpSsq : pS * pS = P := by
    simpa [pS, pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hqSsq : qS * qS = P⁻¹ := by
    simpa [qS, pow_two] using CFC.sq_sqrt P⁻¹ hP.inv.posSemidef.nonneg
  have hqSpS : qS * pS = 1 := by
    rw [show qS = (CFC.sqrt P)⁻¹ by
      simpa [qS] using hP.posSemidef.inv_sqrt.symm]
    apply Matrix.nonsing_inv_mul
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact (CFC.isUnit_sqrt_iff P hP.posSemidef.nonneg).mpr hP.isUnit
  let A : CMatrix d := sS * rS
  obtain ⟨U, hU⟩ := exists_unitary_trace_sqrt_eq A
  have hgram :
      A.conjTranspose * A = rS * σ.matrix * rS := by
    calc
      A.conjTranspose * A = rS * (sS * sS) * rS := by
        simp [A, Matrix.conjTranspose_mul, hrSpos.isHermitian.eq,
          hsSpos.isHermitian.eq, Matrix.mul_assoc]
      _ = rS * σ.matrix * rS := by rw [hsSsq]
  have hfid :
      OneShot.quantumFidelity ρ.matrix σ.matrix =
        Complex.re (((U : CMatrix d).conjTranspose * A).trace) := by
    rw [OneShot.quantumFidelity, OneShot.matrixSqrt]
    change Complex.re (CFC.sqrt (rS * σ.matrix * rS)).trace = _
    rw [← hgram, hU]
  let X : CMatrix d := (U : CMatrix d).conjTranspose * sS * qS
  let Y : CMatrix d := rS * pS
  have hpair :
      X * Y.conjTranspose = (U : CMatrix d).conjTranspose * A := by
    calc
      X * Y.conjTranspose =
          (U : CMatrix d).conjTranspose * sS * (qS * pS) * rS := by
        simp [X, Y, Matrix.conjTranspose_mul, hrSpos.isHermitian.eq,
          hpSpos.isHermitian.eq, Matrix.mul_assoc]
      _ = (U : CMatrix d).conjTranspose * A := by
        rw [hqSpS]
        simp [A, Matrix.mul_assoc]
  have hYtrace :
      (Y * Y.conjTranspose).trace = (ρ.matrix * P).trace := by
    calc
      (Y * Y.conjTranspose).trace = (rS * (pS * pS) * rS).trace := by
        simp [Y, Matrix.conjTranspose_mul, hrSpos.isHermitian.eq,
          hpSpos.isHermitian.eq, Matrix.mul_assoc]
      _ = (rS * P * rS).trace := by rw [hpSsq]
      _ = (rS * rS * P).trace := Matrix.trace_mul_cycle rS P rS
      _ = (ρ.matrix * P).trace := by rw [hrSsq]
  have hXtrace :
      (X * X.conjTranspose).trace = (σ.matrix * P⁻¹).trace := by
    let B : CMatrix d := sS * P⁻¹ * sS
    calc
      (X * X.conjTranspose).trace = ((U : CMatrix d).conjTranspose *
          (sS * (qS * qS) * sS) * (U : CMatrix d)).trace := by
        simp [X, Matrix.conjTranspose_mul, hsSpos.isHermitian.eq,
          hqSpos.isHermitian.eq, Matrix.mul_assoc]
      _ = ((U : CMatrix d).conjTranspose * B * (U : CMatrix d)).trace := by
        rw [hqSsq]
      _ = ((U : CMatrix d) * (U : CMatrix d).conjTranspose * B).trace :=
        Matrix.trace_mul_cycle (U : CMatrix d).conjTranspose B (U : CMatrix d)
      _ = B.trace := by
        rw [show (U : CMatrix d) * (U : CMatrix d).conjTranspose = 1 by
          simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U]
        simp
      _ = (sS * sS * P⁻¹).trace := Matrix.trace_mul_cycle sS P⁻¹ sS
      _ = (σ.matrix * P⁻¹).trace := by rw [hsSsq]
  have hcs := trace_mul_conjTranspose_norm_sq_le X Y
  rw [hpair, hXtrace, hYtrace] at hcs
  have hFle :
      OneShot.quantumFidelity ρ.matrix σ.matrix ≤
        ‖(((U : CMatrix d).conjTranspose * A).trace)‖ := by
    rw [hfid]
    exact Complex.re_le_norm _
  have hFnonneg : 0 ≤ OneShot.quantumFidelity ρ.matrix σ.matrix := by
    rw [OneShot.quantumFidelity, OneShot.matrixSqrt]
    change 0 ≤ Complex.re (CFC.sqrt (rS * σ.matrix * rS)).trace
    exact (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (rS * σ.matrix * rS))).trace_nonneg).1
  exact ((sq_le_sq₀ hFnonneg (norm_nonneg _)).mpr hFle).trans
    (by simpa [mul_comm] using hcs)

/-- The equivalent square-root form of the universal Alberti upper bound. -/
theorem quantumFidelity_le_sqrt_albertiTraceProduct
    (ρ σ : State d) (P : CMatrix d) (hP : P.PosDef) :
    OneShot.quantumFidelity ρ.matrix σ.matrix ≤
      Real.sqrt
        (Complex.re (ρ.matrix * P).trace *
          Complex.re (σ.matrix * P⁻¹).trace) := by
  have hsq := quantumFidelity_sq_le_albertiTraceProduct ρ σ P hP
  have hFnonneg : 0 ≤ OneShot.quantumFidelity ρ.matrix σ.matrix := by
    rw [OneShot.quantumFidelity, OneShot.matrixSqrt]
    exact (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg
          (CFC.sqrt ρ.matrix * σ.matrix * CFC.sqrt ρ.matrix))).trace_nonneg).1
  have hproduct_nonneg :
      0 ≤ Complex.re (ρ.matrix * P).trace *
        Complex.re (σ.matrix * P⁻¹).trace :=
    (sq_nonneg (OneShot.quantumFidelity ρ.matrix σ.matrix)).trans hsq
  exact (Real.le_sqrt hFnonneg hproduct_nonneg).mpr hsq

end

end QITFormalized.NormFidelityAndContinuityTools
