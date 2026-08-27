import QITBench.Base.OneShot

/-!
# Trace-norm bound for a unitary trace pairing

Finite-dimensional Hilbert spaces are represented in the benchmark's chosen-basis
model by a finite index type `d`. Thus operators are complex square matrices
`QITBench.CMatrix d`, and the unitary quantifier is represented by
`Matrix.unitaryGroup d ℂ`.
-/

open QITBench
open scoped ComplexOrder MatrixOrder

namespace QITFormalized

universe u

/-- For every unitary `U`, the modulus of `Tr (A U)` is at most
`Tr √(A† A)`, i.e. the trace norm of `A`. -/
theorem traceNorm_unitary_optimization
    {d : Type u} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (U : Matrix.unitaryGroup d ℂ) :
    ‖(A * (U : CMatrix d)).trace‖ ≤ OneShot.traceNorm A := by
  classical
  let H : CMatrix d := A.conjTranspose * A
  have hH : H.IsHermitian := by
    simp [H, Matrix.IsHermitian]
  have hHpos : H.PosSemidef := by
    simpa [H] using Matrix.posSemidef_conjTranspose_mul_self A
  let V : Matrix.unitaryGroup d ℂ := hH.eigenvectorUnitary
  let B : CMatrix d := A * (V : CMatrix d)
  let W : Matrix.unitaryGroup d ℂ := star V * U
  have htrace :
      (A * (U : CMatrix d)).trace =
        (B * (W : CMatrix d)).trace := by
    change (A * (U : CMatrix d)).trace =
      ((A * (V : CMatrix d)) *
        (star (V : CMatrix d) * (U : CMatrix d))).trace
    rw [← Matrix.mul_assoc (A * (V : CMatrix d)),
      Matrix.mul_assoc A, Unitary.mul_star_self_of_mem V.prop, Matrix.mul_one]
  rw [htrace]
  have hBGram :
      B.conjTranspose * B =
        Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    simpa [B, H, V, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      Unitary.conjStarAlgAut_apply]
      using hH.conjStarAlgAut_star_eigenvectorUnitary
  have htraceNorm :
      OneShot.traceNorm A = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    change Complex.re (Matrix.trace (CFC.sqrt H)) = _
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ H hHpos.nonneg, hH.cfc_eq]
    simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle]
    apply Finset.sum_congr rfl
    intro i _
    rw [max_eq_left (hHpos.eigenvalues_nonneg i)]
  have htrace_expand :
      (B * (W : CMatrix d)).trace =
        ∑ j, ∑ i, B i j * (W : CMatrix d) j i := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
  have hcol_sq (j : d) :
      ∑ i, ‖B i j‖ ^ 2 = hH.eigenvalues j := by
    have hj := congrArg (fun M : CMatrix d => M j j) hBGram
    simp [Matrix.mul_apply] at hj
    have hre := congrArg Complex.re hj
    simpa [← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self] using hre
  have hrow_sq (j : d) :
      ∑ i, ‖(W : CMatrix d) j i‖ ^ 2 = 1 := by
    have hj := congrArg (fun M : CMatrix d => M j j)
      (Unitary.mul_star_self_of_mem W.prop)
    simp [Matrix.mul_apply] at hj
    have hre := congrArg Complex.re hj
    simpa [← Complex.normSq_eq_norm_sq, Complex.mul_conj] using hre
  have hterm (j : d) :
      ‖∑ i, B i j * (W : CMatrix d) j i‖ ≤
        Real.sqrt (hH.eigenvalues j) := by
    let x : EuclideanSpace ℂ d :=
      WithLp.toLp 2 (fun i => star (B i j))
    let y : EuclideanSpace ℂ d :=
      WithLp.toLp 2 (fun i => (W : CMatrix d) j i)
    have hx : ‖x‖ = Real.sqrt (hH.eigenvalues j) := by
      simpa [x, hcol_sq j] using EuclideanSpace.norm_eq x
    have hy : ‖y‖ = 1 := by
      simpa [y, hrow_sq j] using EuclideanSpace.norm_eq y
    have hinner :
        inner ℂ x y = ∑ i, B i j * (W : CMatrix d) j i := by
      simp [x, y, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
    rw [← hinner]
    simpa [hx, hy] using norm_inner_le_norm x y
  rw [htrace_expand, htraceNorm]
  calc
    ‖∑ j, ∑ i, B i j * (W : CMatrix d) j i‖
        ≤ ∑ j, ‖∑ i, B i j * (W : CMatrix d) j i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, Real.sqrt (hH.eigenvalues j) :=
      Finset.sum_le_sum fun j _ => hterm j

end QITFormalized
