import QITBench.Base.OneShot
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Fuchs--van de Graaf inequalities

This file states the two-sided comparison between trace distance and
unsquared quantum fidelity for finite-dimensional density states.
-/

namespace QITFormalized.FuchsVanDeGraafInequalities

open QITBench
open BigOperators
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

universe u

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- The trace distance `D(ρ, σ) = (1 / 2) ‖ρ - σ‖₁` between density states. -/
noncomputable def traceDistance (rho sigma : State d) : ℝ :=
  (1 / 2 : ℝ) * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix)

/- The SVD and trace-norm variational infrastructure below is adapted to the
QITBench definitions from PhysLib's Apache-2.0-licensed
`QuantumInfo.ForMathlib.MatrixNorm.TraceNorm` (Alex Meiburg, 2025). -/

omit [DecidableEq d] in
private lemma inner_mulVec_eq
    (A : Matrix d d ℂ) (v w : d → ℂ) :
    inner ℂ (WithLp.toLp 2 (A.mulVec v)) (WithLp.toLp 2 (A.mulVec w)) =
      star v ⬝ᵥ ((Aᴴ * A).mulVec w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- A square complex matrix admits an SVD whose diagonal entries are the
square roots of the eigenvalues of `Aᴴ * A`. -/
private theorem exists_svd_sqrt_eigenvalues (A : Matrix d d ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    ∃ V W : Matrix.unitaryGroup d ℂ,
      A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  let s : d → ℂ := fun i => Real.sqrt (hH.eigenvalues i)
  have hs_ne {i : d} (hi : hH.eigenvalues i ≠ 0) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast Real.sqrt_ne_zero'.2
      (lt_of_le_of_ne (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) (Ne.symm hi))
  let v : d → EuclideanSpace ℂ d := fun i =>
    if hi : hH.eigenvalues i ≠ 0 then
      ((s i)⁻¹ • WithLp.toLp 2 (A.mulVec (hH.eigenvectorBasis i).ofLp))
    else 0
  have hv : Orthonormal ℂ ({i | hH.eigenvalues i ≠ 0}.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [v, s]
    have hi' : hH.eigenvalues i.1 ≠ 0 := i.2
    have hj' : hH.eigenvalues j.1 ≠ 0 := j.2
    simp only [hi', hj', not_false_eq_true, if_true]
    rw [inner_smul_left, inner_smul_right, inner_mulVec_eq,
      hH.mulVec_eigenvectorBasis j.1]
    by_cases hij : i.1 = j.1
    · cases Subtype.ext hij
      simp [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      field_simp [show (Real.sqrt (hH.eigenvalues i.1) : ℂ) ≠ 0 by
        simpa [s] using hs_ne i.2]
      exact_mod_cast
        (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i.1)).symm
    · simpa [hij, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal, mul_comm]
        using (show i ≠ j from fun h => hij (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ d) (ι := d)
      (by simp [finrank_euclideanSpace]) (v := v)
      (s := {i | hH.eigenvalues i ≠ 0}) hv
  let V : Matrix.unitaryGroup d ℂ := ⟨Matrix.of (fun i j ↦ b j i), by
    simp only [Matrix.mem_unitaryGroup_iff]
    ext i j
    have h1 := b.sum_inner_mul_inner
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp_all [inner]
    exact h1⟩
  let W : Matrix.unitaryGroup d ℂ := hH.eigenvectorUnitary
  have hAW : A * W.val = V.val * Matrix.diagonal s := by
    ext i j
    have hleft :
        (A * W.val) i j = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W,
        Matrix.IsHermitian.eigenvectorUnitary_apply]
    by_cases hj : hH.eigenvalues j = 0
    · have hzero : A.mulVec (hH.eigenvectorBasis j).ofLp = 0 := by
        apply (WithLp.toLp_injective (p := 2))
        exact inner_self_eq_zero.mp (by
          rw [inner_mulVec_eq]
          rw [hH.mulVec_eigenvectorBasis j, hj]
          simp)
      rw [hleft, congrFun hzero i]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, hj]
    · have hbji :
          b j i = (s j)⁻¹ * A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        simpa [v, hj] using
          congrArg (fun x : EuclideanSpace ℂ d => x.ofLp i) (hb j hj)
      have hs_mul :
          s j * b j i = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        rw [hbji]
        field_simp [hs_ne hj]
      rw [hleft, ← hs_mul]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, mul_comm]
  refine ⟨V, W, ?_⟩
  simpa [W, Matrix.IsHermitian.eigenvectorUnitary, Matrix.mul_assoc] using
    congrArg (fun X => X * W.valᴴ) hAW

private lemma traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix d d ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    QITBench.OneShot.traceNorm A = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  intro hH
  unfold QITBench.OneShot.traceNorm QITBench.OneShot.matrixSqrt
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

private lemma traceNorm_nonneg (A : Matrix d d ℂ) :
    0 ≤ QITBench.OneShot.traceNorm A := by
  unfold QITBench.OneShot.traceNorm QITBench.OneShot.matrixSqrt
  have hsqrt :
      (CFC.sqrt (A.conjTranspose * A)).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  exact (Complex.nonneg_iff.mp hsqrt.trace_nonneg).1

private theorem re_trace_mul_nonneg_of_posSemidef
    {A B : Matrix d d ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hXB : (X * B * X.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same X
  have htr : 0 ≤ (X * B * X.conjTranspose).trace := hXB.trace_nonneg
  have hre : 0 ≤ (X * B * star X).trace.re := by
    simpa only [Matrix.star_eq_conjTranspose] using (Complex.nonneg_iff.mp htr).1
  rw [hX]
  calc
    (star X * X * B).trace.re = (X * B * star X).trace.re := by
      rw [Matrix.trace_mul_cycle X B (star X)]
    _ ≥ 0 := hre

private theorem re_trace_mul_le_posPart
    (A E : Matrix d d ℂ) (hA : A.IsHermitian)
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    (A * E).trace.re ≤ (A⁺).trace.re := by
  have hPpos : (A⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hQpos : (A⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have hQE : 0 ≤ (A⁻ * E).trace.re :=
    re_trace_mul_nonneg_of_posSemidef hQpos hEpos
  have hcomp : (1 - E).PosSemidef := Matrix.le_iff.mp hEle
  have hcompP : 0 ≤ ((1 - E) * A⁺).trace.re :=
    re_trace_mul_nonneg_of_posSemidef hcomp hPpos
  have hPEle : (A⁺ * E).trace.re ≤ (A⁺).trace.re := by
    have hrewrite : ((1 - E) * A⁺).trace.re =
        (A⁺).trace.re - (A⁺ * E).trace.re := by
      rw [sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_mul_comm E A⁺]
      rfl
    rw [hrewrite] at hcompP
    linarith
  calc
    (A * E).trace.re = ((A⁺ - A⁻) * E).trace.re := by
      rw [CFC.posPart_sub_negPart A hA]
    _ = (A⁺ * E).trace.re - (A⁻ * E).trace.re := by
      rw [sub_mul, Matrix.trace_sub]
      rfl
    _ ≤ (A⁺).trace.re := by linarith

/-- The spectral projection onto the strictly positive eigenspaces of a
Hermitian matrix. -/
private noncomputable def positiveSupport
    (A : Matrix d d ℂ) (hA : A.IsHermitian) : Matrix d d ℂ :=
  hA.cfc (fun x : ℝ => if 0 < x then 1 else 0)

private theorem positiveSupport_pos
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    (positiveSupport A hA).PosSemidef := by
  rw [positiveSupport, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (U := (hA.eigenvectorUnitary : Matrix d d ℂ)) Unitary.isUnit_coe).2
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Function.comp_apply]
  split <;> simp

private theorem positiveSupport_idem
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    positiveSupport A hA * positiveSupport A hA = positiveSupport A hA := by
  simp only [positiveSupport, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  let U : Matrix d d ℂ := ↑hA.eigenvectorUnitary
  let D : Matrix d d ℂ :=
    Matrix.diagonal
      (RCLike.ofReal ∘ (fun x : ℝ => if 0 < x then 1 else 0) ∘ hA.eigenvalues)
  change (U * D * star U) * (U * D * star U) = U * D * star U
  rw [show (U * D * star U) * (U * D * star U) =
      U * D * (star U * U) * D * star U by noncomm_ring]
  have hU : star U * U = 1 := by
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hU, Matrix.mul_one]
  have hDD : D * D = D := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    split <;> simp
  rw [show U * D * D * star U = U * (D * D) * star U by noncomm_ring, hDD]

private theorem positiveSupport_le_one
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    positiveSupport A hA ≤ 1 := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (positiveSupport A hA) (positiveSupport_pos A hA) (positiveSupport_idem A hA)

private theorem mul_positiveSupport
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    A * positiveSupport A hA = A⁺ := by
  rw [positiveSupport, CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
  conv_lhs =>
    lhs
    rw [hA.spectral_theorem]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  let U : Matrix d d ℂ := ↑hA.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let E : Matrix d d ℂ :=
    Matrix.diagonal
      (RCLike.ofReal ∘ (fun x : ℝ => if 0 < x then 1 else 0) ∘ hA.eigenvalues)
  let P : Matrix d d ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ (fun x : ℝ => x⁺) ∘ hA.eigenvalues)
  change (U * D * star U) * (U * E * star U) = U * P * star U
  rw [show (U * D * star U) * (U * E * star U) =
      U * D * (star U * U) * E * star U by noncomm_ring]
  have hU : star U * U = 1 := by
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hU, Matrix.mul_one]
  have hDE : D * E = P := by
    dsimp [D, E, P]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    by_cases hi : 0 < hA.eigenvalues i
    · simp [hi, le_of_lt hi]
    · have hi' : hA.eigenvalues i ≤ 0 := le_of_not_gt hi
      simp [hi, hi']
  rw [show U * D * E * star U = U * (D * E) * star U by noncomm_ring, hDE]

private theorem traceNorm_eq_two_re_trace_posPart_of_trace_zero
    (A : Matrix d d ℂ) (hA : A.IsHermitian) (htr : A.trace = 0) :
    QITBench.OneShot.traceNorm A = 2 * (A⁺).trace.re := by
  have hparts : (A⁺).trace = (A⁻).trace := by
    have h := congrArg Matrix.trace (CFC.posPart_sub_negPart A hA)
    rw [Matrix.trace_sub, htr] at h
    exact sub_eq_zero.mp h
  rw [QITBench.OneShot.traceNorm, QITBench.OneShot.matrixSqrt]
  change (CFC.abs A).trace.re = _
  rw [← CFC.posPart_add_negPart A hA, Matrix.trace_add, hparts]
  simp only [Complex.add_re]
  ring

/-- The trace norm is the maximum real trace pairing with a unitary matrix. -/
private theorem traceNorm_eq_max_re_trace_unitary (A : Matrix d d ℂ) :
    IsGreatest
      {x : ℝ | ∃ U : Matrix.unitaryGroup d ℂ,
        Complex.re ((U.val * A).trace) = x}
      (QITBench.OneShot.traceNorm A) := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ :
      ∃ V W : Matrix.unitaryGroup d ℂ,
        A = V.val *
          Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) *
            W.valᴴ := by
    simpa [hH] using exists_svd_sqrt_eigenvalues A
  have htraceNorm :
      QITBench.OneShot.traceNorm A =
        ∑ i, Real.sqrt (hH.eigenvalues i) := by
    simpa [hH] using traceNorm_eq_sum_sqrt_eigenvalues A
  set D : Matrix d d ℂ :=
    Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hVu : V.valᴴ * V.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hWu : W.valᴴ * W.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
  refine ⟨⟨W * star V, ?_⟩, ?_⟩
  · calc
      Complex.re (((W * star V).val * A).trace)
          = Complex.re D.trace := by
              rw [hA]
              congr 1
              change
                (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace =
                  D.trace
              simp [Matrix.mul_assoc, hVu, Matrix.trace_mul_comm, hWu]
      _ = QITBench.OneShot.traceNorm A := by
            simp [D, Matrix.trace, htraceNorm]
  · rintro _ ⟨U, rfl⟩
    set C : Matrix.unitaryGroup d ℂ := star W * U * V
    rw [show Complex.re ((U.val * A).trace) =
        ∑ i, Real.sqrt (hH.eigenvalues i) * Complex.re (C.val i i) by
      conv_lhs => rw [hA]
      have h1 :
          (U.val * (V.val * D * W.valᴴ)).trace =
            (C.val * D).trace := by
        change _ = (W.valᴴ * U.val * V.val * D).trace
        rw [show
            (U.val * (V.val * D * W.valᴴ)).trace =
              (((U.val * V.val) * D) * W.valᴴ).trace by
                simp [Matrix.mul_assoc],
          Matrix.trace_mul_comm _ W.valᴴ]
        simp [Matrix.mul_assoc]
      rw [h1]
      simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
        Complex.mul_re, mul_comm],
      htraceNorm]
    have hdiag_le : ∀ i, Complex.re (C.val i i) ≤ 1 := fun i =>
      (Complex.re_le_norm _).trans
        (entry_norm_bound_of_unitary C.property i i)
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hdiag_le i, Real.sqrt_nonneg (hH.eigenvalues i)]

private lemma traceNorm_add_le (A B : Matrix d d ℂ) :
    QITBench.OneShot.traceNorm (A + B) ≤
      QITBench.OneShot.traceNorm A + QITBench.OneShot.traceNorm B := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_re_trace_unitary (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h₁
  obtain h₂ := (traceNorm_eq_max_re_trace_unitary A).right
  obtain h₃ := (traceNorm_eq_max_re_trace_unitary B).right
  simp only [upperBounds, Set.mem_setOf_eq] at h₂ h₃
  calc
    QITBench.OneShot.traceNorm (A + B)
        = Complex.re ((Uab.1 * A).trace) +
            Complex.re ((Uab.1 * B).trace) := h₁.symm
    _ ≤ QITBench.OneShot.traceNorm A +
          Complex.re ((Uab.1 * B).trace) := by
        simpa [add_comm] using
          add_le_add_right
            (h₂ (a := Complex.re ((Uab.1 * A).trace)) ⟨Uab, rfl⟩)
            (Complex.re ((Uab.1 * B).trace))
    _ ≤ QITBench.OneShot.traceNorm A +
          QITBench.OneShot.traceNorm B := by
        simpa [add_comm] using
          add_le_add_left
            (h₃ (a := Complex.re ((Uab.1 * B).trace)) ⟨Uab, rfl⟩)
            (QITBench.OneShot.traceNorm A)

private def frobeniusVec (A : Matrix d d ℂ) :
    EuclideanSpace ℂ (d × d) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

private def frobeniusSq (A : Matrix d d ℂ) : ℝ :=
  Complex.re (Matrix.trace (Aᴴ * A))

omit [DecidableEq d] in
private lemma frobeniusVec_inner (A B : Matrix d d ℂ) :
    inner ℂ (frobeniusVec A) (frobeniusVec B) =
      Matrix.trace (Aᴴ * B) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [frobeniusVec, WithLp.ofLp_toLp, dotProduct, Matrix.trace]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

omit [DecidableEq d] in
private lemma frobeniusSq_nonneg (A : Matrix d d ℂ) :
    0 ≤ frobeniusSq A := by
  unfold frobeniusSq
  exact
    (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

omit [DecidableEq d] in
private lemma frobeniusVec_norm (A : Matrix d d ℂ) :
    ‖frobeniusVec A‖ = Real.sqrt (frobeniusSq A) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), frobeniusVec_inner,
    Real.sq_sqrt (frobeniusSq_nonneg A)]
  rfl

private lemma frobeniusSq_mul_unitary
    (B : Matrix d d ℂ) (U : Matrix.unitaryGroup d ℂ) :
    frobeniusSq (B * U.val) = frobeniusSq B := by
  unfold frobeniusSq
  congr 1
  calc
    ((B * U.val)ᴴ * (B * U.val)).trace =
        (U.valᴴ * (Bᴴ * B) * U.val).trace := by
      congr 1
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (U.val * U.valᴴ * (Bᴴ * B)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = ((Bᴴ * B) * (U.val * U.valᴴ)).trace := by
      simpa [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (U.val * U.valᴴ) (Bᴴ * B)
    _ = (Bᴴ * B).trace := by
      rw [show U.val * U.valᴴ = 1 by
        simpa [Matrix.star_eq_conjTranspose] using
          Unitary.coe_mul_star_self U]
      simp

private lemma traceNorm_conjTranspose_mul_le
    (A B : Matrix d d ℂ) :
    QITBench.OneShot.traceNorm (Aᴴ * B) ≤
      Real.sqrt (frobeniusSq A) * Real.sqrt (frobeniusSq B) := by
  obtain ⟨U, hU⟩ :=
    (traceNorm_eq_max_re_trace_unitary (Aᴴ * B)).left
  calc
    QITBench.OneShot.traceNorm (Aᴴ * B) =
        Complex.re ((U.val * (Aᴴ * B)).trace) := hU.symm
    _ ≤ ‖(U.val * (Aᴴ * B)).trace‖ := Complex.re_le_norm _
    _ = ‖inner ℂ (frobeniusVec A) (frobeniusVec (B * U.val))‖ := by
      congr 1
      rw [frobeniusVec_inner, Matrix.trace_mul_comm U.val (Aᴴ * B),
        Matrix.mul_assoc]
    _ ≤ ‖frobeniusVec A‖ * ‖frobeniusVec (B * U.val)‖ :=
      norm_inner_le_norm _ _
    _ = Real.sqrt (frobeniusSq A) * Real.sqrt (frobeniusSq B) := by
      rw [frobeniusVec_norm, frobeniusVec_norm,
        frobeniusSq_mul_unitary]

private lemma quantumFidelity_eq_traceNorm_sqrt_mul_sqrt
    (rho sigma : State d) :
    QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix =
      QITBench.OneShot.traceNorm
        (QITBench.OneShot.matrixSqrt sigma.matrix *
          QITBench.OneShot.matrixSqrt rho.matrix) := by
  let R := QITBench.OneShot.matrixSqrt rho.matrix
  let S := QITBench.OneShot.matrixSqrt sigma.matrix
  have hR : Rᴴ = R := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hS : Sᴴ = S := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hSsq : S * S = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix (ha := sigma.pos.nonneg)
  unfold QITBench.OneShot.quantumFidelity QITBench.OneShot.traceNorm
  change
    Complex.re
        (Matrix.trace
          (QITBench.OneShot.matrixSqrt (R * sigma.matrix * R))) =
      Complex.re
        (Matrix.trace
          (QITBench.OneShot.matrixSqrt ((S * R)ᴴ * (S * R))))
  congr 3
  rw [Matrix.conjTranspose_mul, hR, hS]
  rw [← Matrix.mul_assoc (R * S) S R, Matrix.mul_assoc R S S, hSsq]

private theorem fuchsVanDeGraaf_lower (rho sigma : State d) :
    1 - QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix ≤
      traceDistance rho sigma := by
  let R := QITBench.OneShot.matrixSqrt rho.matrix
  let S := QITBench.OneShot.matrixSqrt sigma.matrix
  let N := R - S
  let Δ := rho.matrix - sigma.matrix
  have hR : Rᴴ = R := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hS : Sᴴ = S := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRpos : R.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hSpos : S.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRsq : R * R = rho.matrix :=
    CFC.sqrt_mul_sqrt_self rho.matrix (ha := rho.pos.nonneg)
  have hSsq : S * S = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix (ha := sigma.pos.nonneg)
  have hNherm : N.IsHermitian := by
    dsimp [N]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hR, hS]
  have hΔherm : Δ.IsHermitian := by
    dsimp [Δ]
    exact rho.pos.isHermitian.sub sigma.pos.isHermitian
  have hΔtr : Δ.trace = 0 := by
    simp [Δ, Matrix.trace_sub, rho.trace_eq_one, sigma.trace_eq_one]
  let P := positiveSupport N hNherm
  have hPpos : P.PosSemidef := by
    simpa [P] using positiveSupport_pos N hNherm
  have hPh : Pᴴ = P := hPpos.isHermitian
  have hPid : P * P = P := by
    simpa [P] using positiveSupport_idem N hNherm
  have hPle : P ≤ 1 := by
    simpa [P] using positiveSupport_le_one N hNherm
  have hNplusPos : (N⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg N)
  have hNminusPos : (N⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg N)
  have hNP : N * P = N⁺ := by
    simpa [P] using mul_positiveSupport N hNherm
  have hPN : P * N = N⁺ := by
    calc
      P * N = (N * P)ᴴ := by
        rw [Matrix.conjTranspose_mul, hNherm.eq, hPh]
      _ = (N⁺)ᴴ := by rw [hNP]
      _ = N⁺ := hNplusPos.isHermitian
  have hExpr : rho.matrix - S * R = N * R := by
    rw [← hRsq]
    dsimp [N]
    noncomm_ring
  have htotal_le_projected :
      Complex.re ((rho.matrix - S * R).trace) ≤
        Complex.re ((P * (rho.matrix - S * R)).trace) := by
    have hnegative :
        0 ≤ Complex.re ((N⁻ * R).trace) :=
      re_trace_mul_nonneg_of_posSemidef hNminusPos hRpos
    rw [hExpr, show P * (N * R) = N⁺ * R by
      rw [← Matrix.mul_assoc, hPN]]
    calc
      Complex.re ((N * R).trace) =
          Complex.re (((N⁺ - N⁻) * R).trace) := by
        rw [CFC.posPart_sub_negPart N hNherm]
      _ = Complex.re ((N⁺ * R).trace) -
          Complex.re ((N⁻ * R).trace) := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
      _ ≤ Complex.re ((N⁺ * R).trace) := by linarith
  have hDeltaSplit :
      Δ = (rho.matrix - S * R) + S * N := by
    dsimp [Δ, N]
    rw [← hRsq, ← hSsq]
    noncomm_ring
  have hprojected_le_delta :
      Complex.re ((P * (rho.matrix - S * R)).trace) ≤
        Complex.re ((P * Δ).trace) := by
    have hpositive :
        0 ≤ Complex.re ((N⁺ * S).trace) :=
      re_trace_mul_nonneg_of_posSemidef hNplusPos hSpos
    rw [hDeltaSplit, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hcycle :
        Complex.re ((P * (S * N)).trace) =
          Complex.re ((N⁺ * S).trace) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle P S N, hNP]
    rw [hcycle]
    linarith
  have hdelta_le_posPart :
      Complex.re ((P * Δ).trace) ≤ Complex.re ((Δ⁺).trace) := by
    have hbound := re_trace_mul_le_posPart Δ P hΔherm hPpos hPle
    rw [Matrix.trace_mul_comm Δ P] at hbound
    exact hbound
  have hmain :
      1 - Complex.re ((S * R).trace) ≤ Complex.re ((Δ⁺).trace) := by
    have htrace :
        Complex.re ((rho.matrix - S * R).trace) =
          1 - Complex.re ((S * R).trace) := by
      rw [Matrix.trace_sub, Complex.sub_re, rho.trace_eq_one]
      norm_num
    rw [← htrace]
    exact htotal_le_projected.trans
      (hprojected_le_delta.trans hdelta_le_posPart)
  have htrace_le_fidelity :
      Complex.re ((S * R).trace) ≤
        QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix := by
    rw [quantumFidelity_eq_traceNorm_sqrt_mul_sqrt]
    have hbound := (traceNorm_eq_max_re_trace_unitary (S * R)).right
    simp only [upperBounds, Set.mem_setOf_eq] at hbound
    have hone := hbound
      (a := Complex.re ((((1 : Matrix.unitaryGroup d ℂ).val) * (S * R)).trace))
      ⟨1, rfl⟩
    simpa using hone
  have hposPart_eq_distance :
      Complex.re ((Δ⁺).trace) = traceDistance rho sigma := by
    change Complex.re ((Δ⁺).trace) =
      (1 / 2 : ℝ) * QITBench.OneShot.traceNorm Δ
    rw [traceNorm_eq_two_re_trace_posPart_of_trace_zero Δ hΔherm hΔtr]
    ring
  rw [← hposPart_eq_distance]
  linarith

private lemma traceNorm_two_smul (A : Matrix d d ℂ) :
    QITBench.OneShot.traceNorm ((2 : ℂ) • A) =
      2 * QITBench.OneShot.traceNorm A := by
  unfold QITBench.OneShot.traceNorm QITBench.OneShot.matrixSqrt
  have hrad :
      (((2 : ℂ) • A)ᴴ * ((2 : ℂ) • A)) =
        (4 : ℂ) • (Aᴴ * A) := by
    simp [smul_smul]
    norm_num
  rw [hrad]
  have hsqrt :
      CFC.sqrt ((4 : ℂ) • (Aᴴ * A)) =
        (2 : ℂ) • CFC.sqrt (Aᴴ * A) := by
    apply CFC.sqrt_unique
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      norm_num
      exact CFC.sqrt_mul_sqrt_self _
        (ha := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg)
    · change 0 ≤ (2 : ℝ) • CFC.sqrt (Aᴴ * A)
      exact smul_nonneg (by norm_num) (CFC.sqrt_nonneg _)
  rw [hsqrt]
  simp

private theorem fuchsVanDeGraaf_upper (rho sigma : State d) :
    traceDistance rho sigma ≤
      Real.sqrt
        (1 - (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := by
  let R := QITBench.OneShot.matrixSqrt rho.matrix
  let S := QITBench.OneShot.matrixSqrt sigma.matrix
  let F := QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix
  have hR : Rᴴ = R := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hS : Sᴴ = S := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRsq : R * R = rho.matrix :=
    CFC.sqrt_mul_sqrt_self rho.matrix (ha := rho.pos.nonneg)
  have hSsq : S * S = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix (ha := sigma.pos.nonneg)
  have hF :
      F = QITBench.OneShot.traceNorm (S * R) := by
    simpa [F, R, S] using
      quantumFidelity_eq_traceNorm_sqrt_mul_sqrt rho sigma
  obtain ⟨U, hUmax⟩ :=
    (traceNorm_eq_max_re_trace_unitary (S * R)).left
  have hUtrace :
      Complex.re ((U.val * (S * R)).trace) = F :=
    hUmax.trans hF.symm
  let C := U.val * S
  have hUstarU : U.valᴴ * U.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  have hCstarC : Cᴴ * C = sigma.matrix := by
    dsimp [C]
    rw [Matrix.conjTranspose_mul, hS]
    rw [Matrix.mul_assoc S U.valᴴ (U.val * S),
      ← Matrix.mul_assoc U.valᴴ U.val S, hUstarU, one_mul,
      hSsq]
  have hRstarR : Rᴴ * R = rho.matrix := by
    rw [hR, hRsq]
  have hcross :
      Complex.re ((Rᴴ * C).trace) = F := by
    rw [hR]
    dsimp [C]
    rw [Matrix.trace_mul_comm R (U.val * S), Matrix.mul_assoc]
    exact hUtrace
  have hcrossStar :
      Complex.re ((Cᴴ * R).trace) = F := by
    calc
      Complex.re ((Cᴴ * R).trace) =
          Complex.re (((Rᴴ * C)ᴴ).trace) := by
            congr 2
            simp [Matrix.conjTranspose_mul]
      _ = Complex.re (star ((Rᴴ * C).trace)) := by
            rw [Matrix.trace_conjTranspose]
      _ = Complex.re ((Rᴴ * C).trace) := Complex.conj_re _
      _ = F := hcross
  have hfsR : frobeniusSq R = 1 := by
    unfold frobeniusSq
    rw [hRstarR, rho.trace_eq_one]
    norm_num
  have hfsC : frobeniusSq C = 1 := by
    unfold frobeniusSq
    rw [hCstarC, sigma.trace_eq_one]
    norm_num
  let X := R - C
  let Y := R + C
  have hfsX : frobeniusSq X = 2 - 2 * F := by
    have hexpand :
        Xᴴ * X =
          Rᴴ * R - Rᴴ * C - Cᴴ * R + Cᴴ * C := by
      dsimp [X]
      rw [Matrix.conjTranspose_sub]
      noncomm_ring
    unfold frobeniusSq
    rw [hexpand]
    simp only [Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
    rw [show Complex.re ((Rᴴ * R).trace) = frobeniusSq R by rfl,
      show Complex.re ((Cᴴ * C).trace) = frobeniusSq C by rfl,
      hfsR, hfsC, hcross, hcrossStar]
    ring
  have hfsY : frobeniusSq Y = 2 + 2 * F := by
    have hexpand :
        Yᴴ * Y =
          Rᴴ * R + Rᴴ * C + Cᴴ * R + Cᴴ * C := by
      dsimp [Y]
      rw [Matrix.conjTranspose_add]
      noncomm_ring
    unfold frobeniusSq
    rw [hexpand]
    simp only [Matrix.trace_add, Complex.add_re]
    rw [show Complex.re ((Rᴴ * R).trace) = frobeniusSq R by rfl,
      show Complex.re ((Cᴴ * C).trace) = frobeniusSq C by rfl,
      hfsR, hfsC, hcross, hcrossStar]
    ring
  have hdouble :
      (2 : ℂ) • (rho.matrix - sigma.matrix) =
        Xᴴ * Y + Yᴴ * X := by
    rw [← hRstarR, ← hCstarC]
    dsimp [X, Y]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add]
    noncomm_ring
    module
  have hxy := traceNorm_conjTranspose_mul_le X Y
  have hyx := traceNorm_conjTranspose_mul_le Y X
  have hnorm :
      QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) ≤
        Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) := by
    have htwo :
        2 * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) ≤
          2 * (Real.sqrt (frobeniusSq X) *
            Real.sqrt (frobeniusSq Y)) := by
      calc
        2 * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) =
            QITBench.OneShot.traceNorm
              ((2 : ℂ) • (rho.matrix - sigma.matrix)) :=
                (traceNorm_two_smul _).symm
        _ = QITBench.OneShot.traceNorm
              (Xᴴ * Y + Yᴴ * X) := by rw [hdouble]
        _ ≤ QITBench.OneShot.traceNorm (Xᴴ * Y) +
              QITBench.OneShot.traceNorm (Yᴴ * X) :=
                traceNorm_add_le _ _
        _ ≤ Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) +
              Real.sqrt (frobeniusSq Y) * Real.sqrt (frobeniusSq X) :=
                add_le_add hxy hyx
        _ = 2 * (Real.sqrt (frobeniusSq X) *
              Real.sqrt (frobeniusSq Y)) := by ring
    linarith
  have hXnonneg : 0 ≤ 2 - 2 * F := by
    rw [← hfsX]
    exact frobeniusSq_nonneg X
  have hYnonneg : 0 ≤ 2 + 2 * F := by
    rw [← hfsY]
    exact frobeniusSq_nonneg Y
  have hradicand : 0 ≤ 1 - F ^ 2 := by
    nlinarith [mul_nonneg hXnonneg hYnonneg]
  have hsqrt_product :
      (1 / 2 : ℝ) * Real.sqrt (frobeniusSq X) *
          Real.sqrt (frobeniusSq Y) =
        Real.sqrt (1 - F ^ 2) := by
    rw [hfsX, hfsY]
    calc
      (1 / 2 : ℝ) * Real.sqrt (2 - 2 * F) *
          Real.sqrt (2 + 2 * F) =
          (1 / 2 : ℝ) *
            (Real.sqrt (2 - 2 * F) * Real.sqrt (2 + 2 * F)) := by ring
      _ = (1 / 2 : ℝ) *
            Real.sqrt ((2 - 2 * F) * (2 + 2 * F)) := by
              rw [Real.sqrt_mul hXnonneg]
      _ = (1 / 2 : ℝ) * Real.sqrt (4 * (1 - F ^ 2)) := by ring
      _ = (1 / 2 : ℝ) *
            (Real.sqrt 4 * Real.sqrt (1 - F ^ 2)) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = Real.sqrt (1 - F ^ 2) := by
            rw [show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq_eq_abs]
              norm_num]
            ring
  calc
    traceDistance rho sigma =
        (1 / 2 : ℝ) *
          QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) := rfl
    _ ≤ (1 / 2 : ℝ) *
          (Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y)) := by
            exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = Real.sqrt (1 - F ^ 2) := by
          rw [← hsqrt_product]
          ring
    _ = Real.sqrt
        (1 -
          (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := rfl

/-- The Fuchs--van de Graaf inequalities for finite-dimensional density states. -/
theorem fuchsVanDeGraafInequalities (rho sigma : State d) :
    1 - QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix ≤
        traceDistance rho sigma ∧
      traceDistance rho sigma ≤
        Real.sqrt
          (1 - (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := by
  exact ⟨fuchsVanDeGraaf_lower rho sigma, fuchsVanDeGraaf_upper rho sigma⟩

end

end QITFormalized.FuchsVanDeGraafInequalities
