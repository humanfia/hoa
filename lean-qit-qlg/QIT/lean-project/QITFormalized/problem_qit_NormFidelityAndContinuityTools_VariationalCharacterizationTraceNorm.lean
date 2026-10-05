import QITBench.Base.OneShot
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Variational characterization of the trace norm

This file formalizes the finite-dimensional density-operator statement using
the matrix model from `QITBench.Base`.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized

universe u

open QITBench
open BigOperators

noncomputable section

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
  rw [CFC.abs_eq_cfc_norm X hX, hX.cfc_eq]
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
    OneShot.traceNorm X =
      Complex.re ((X * hermitianSign hX).trace) := by
  rw [OneShot.traceNorm, OneShot.matrixSqrt]
  have habs :
      CFC.sqrt (X.conjTranspose * X) = CFC.abs X := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose]
  rw [habs, ← mul_hermitianSign_eq_abs hX]

private lemma traceNorm_eq_sum_norm_eigenvalues
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    OneShot.traceNorm X = ∑ i, ‖hX.eigenvalues i‖ := by
  rw [OneShot.traceNorm, OneShot.matrixSqrt]
  have habs :
      CFC.sqrt (X.conjTranspose * X) = CFC.abs X := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose]
  rw [habs, CFC.abs_eq_cfc_norm X hX, hX.cfc_eq,
    Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

private lemma norm_trace_mul_unitary_le_traceNorm
    {d : Type u} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian)
    (U : Matrix.unitaryGroup d ℂ) :
    ‖(X * (U : CMatrix d)).trace‖ ≤ OneShot.traceNorm X := by
  let V : Matrix.unitaryGroup d ℂ := hX.eigenvectorUnitary
  let D : CMatrix d :=
    Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)
  let C : Matrix.unitaryGroup d ℂ := star V * U * V
  have hspec : X = V.val * D * star V.val := by
    simpa [V, D, Unitary.conjStarAlgAut_apply] using hX.spectral_theorem
  have htrace :
      (X * (U : CMatrix d)).trace = (D * C.val).trace := by
    rw [hspec]
    calc
      ((V.val * D * star V.val) * U.val).trace =
          (V.val * (D * (star V.val * U.val))).trace := by
            congr 1
            noncomm_ring
      _ = ((D * (star V.val * U.val)) * V.val).trace :=
        Matrix.trace_mul_comm _ _
      _ = (D * C.val).trace := by
        simp [C, Matrix.mul_assoc]
  have hdiag :
      (D * C.val).trace =
        ∑ i, (hX.eigenvalues i : ℂ) * C.val i i := by
    simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal]
  rw [htrace, hdiag, traceNorm_eq_sum_norm_eigenvalues hX]
  calc
    ‖∑ i, (hX.eigenvalues i : ℂ) * C.val i i‖ ≤
        ∑ i, ‖(hX.eigenvalues i : ℂ) * C.val i i‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖hX.eigenvalues i‖ * ‖C.val i i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ ≤ ∑ i, ‖hX.eigenvalues i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_of_le_one_right (norm_nonneg _)
        (entry_norm_bound_of_unitary C.property i i)

/-- The trace norm of the difference of two finite-dimensional density
operators is attained as the maximum absolute trace pairing over all unitary
operators.  `IsGreatest` records both attainment and the universal upper-bound
property of the stated maximum. -/
theorem variationalCharacterizationTraceNorm
    {d : Type u} [Fintype d] [DecidableEq d]
    (rho sigma : State d) :
    IsGreatest
      (Set.range fun U : Matrix.unitaryGroup d ℂ =>
        ‖Matrix.trace ((rho.matrix - sigma.matrix) * (U : CMatrix d))‖)
      (OneShot.traceNorm (rho.matrix - sigma.matrix)) := by
  let X : CMatrix d := rho.matrix - sigma.matrix
  have hX : X.IsHermitian :=
    rho.pos.isHermitian.sub sigma.pos.isHermitian
  let S : Matrix.unitaryGroup d ℂ :=
    ⟨hermitianSign hX, hermitianSign_unitary hX⟩
  refine ⟨?_, ?_⟩
  · refine ⟨S, ?_⟩
    change ‖(X * hermitianSign hX).trace‖ = OneShot.traceNorm X
    have hnonneg : 0 ≤ (CFC.abs X).trace := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg X)).trace_nonneg
    calc
      ‖(X * hermitianSign hX).trace‖ =
          Complex.re ((X * hermitianSign hX).trace) := by
            rw [mul_hermitianSign_eq_abs hX]
            exact (Complex.re_eq_norm.mpr hnonneg).symm
      _ = OneShot.traceNorm X :=
        (traceNorm_eq_re_trace_mul_hermitianSign hX).symm
  · rintro _ ⟨U, rfl⟩
    exact norm_trace_mul_unitary_le_traceNorm hX U

end
end QITFormalized
