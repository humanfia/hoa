import QITBench.Base.OneShot

/-!
# Trace-distance data processing for quantum channels

This file formalizes the finite-dimensional data-processing inequality for
trace distance. Density operators and completely positive trace-preserving maps
are represented by `QITBench.State` and `QITBench.Channel`, respectively.
-/

namespace QITFormalized.TraceDistanceDataProcessingQuantumChannels

open QITBench
open scoped ComplexOrder MatrixOrder

noncomputable section

universe u v

/-- The trace distance between two finite-dimensional density states:
`D(ω, τ) = (1 / 2) * ‖ω - τ‖₁`. -/
def traceDistance
    {d : Type u} [Fintype d] [DecidableEq d]
    (ω τ : State d) : ℝ :=
  (1 / 2 : ℝ) * OneShot.traceNorm (ω.matrix - τ.matrix)

private theorem re_trace_mul_nonneg_of_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {A B : CMatrix d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
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
    {d : Type*} [Fintype d] [DecidableEq d]
    (A E : CMatrix d) (hA : A.IsHermitian)
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
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) : CMatrix d :=
  hA.cfc (fun x : ℝ => if 0 < x then 1 else 0)

private theorem positiveSupport_pos
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) :
    (positiveSupport A hA).PosSemidef := by
  rw [positiveSupport, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (U := (hA.eigenvectorUnitary : CMatrix d)) Unitary.isUnit_coe).2
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Function.comp_apply]
  split <;> simp

private theorem positiveSupport_idem
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) :
    positiveSupport A hA * positiveSupport A hA = positiveSupport A hA := by
  simp only [positiveSupport, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  let U : CMatrix d := ↑hA.eigenvectorUnitary
  let D : CMatrix d :=
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
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) :
    positiveSupport A hA ≤ 1 := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (positiveSupport A hA) (positiveSupport_pos A hA) (positiveSupport_idem A hA)

private theorem mul_positiveSupport
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) :
    A * positiveSupport A hA = A⁺ := by
  rw [positiveSupport, CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
  conv_lhs =>
    lhs
    rw [hA.spectral_theorem]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  let U : CMatrix d := ↑hA.eigenvectorUnitary
  let D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let E : CMatrix d :=
    Matrix.diagonal
      (RCLike.ofReal ∘ (fun x : ℝ => if 0 < x then 1 else 0) ∘ hA.eigenvalues)
  let P : CMatrix d :=
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
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.IsHermitian) (htr : A.trace = 0) :
    OneShot.traceNorm A = 2 * (A⁺).trace.re := by
  have hparts : (A⁺).trace = (A⁻).trace := by
    have h := congrArg Matrix.trace (CFC.posPart_sub_negPart A hA)
    rw [Matrix.trace_sub, htr] at h
    exact sub_eq_zero.mp h
  rw [OneShot.traceNorm, OneShot.matrixSqrt]
  change (CFC.abs A).trace.re = _
  rw [← CFC.posPart_add_negPart A hA, Matrix.trace_add, hparts]
  simp only [Complex.add_re]
  ring

/-- Every finite-dimensional completely positive trace-preserving map is a
contraction for trace distance on density states. -/
theorem traceDistance_dataProcessing
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ σ : State a) (𝒩 : Channel a b) :
    traceDistance (𝒩.applyState ρ) (𝒩.applyState σ) ≤
      traceDistance ρ σ := by
  let Δ : CMatrix a := ρ.matrix - σ.matrix
  have hΔherm : Δ.IsHermitian := ρ.pos.isHermitian.sub σ.pos.isHermitian
  have hΔtr : Δ.trace = 0 := by
    simp [Δ, Matrix.trace_sub, ρ.trace_eq_one, σ.trace_eq_one]
  have hPpos : (Δ⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg Δ)
  have hQpos : (Δ⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg Δ)
  have houtP : (𝒩.map Δ⁺).PosSemidef := 𝒩.mapsPositive Δ⁺ hPpos
  have houtQ : (𝒩.map Δ⁻).PosSemidef := 𝒩.mapsPositive Δ⁻ hQpos
  have houtdecomp : 𝒩.map Δ = 𝒩.map Δ⁺ - 𝒩.map Δ⁻ := by
    rw [← map_sub, CFC.posPart_sub_negPart Δ hΔherm]
  have houtherm : (𝒩.map Δ).IsHermitian := by
    rw [houtdecomp]
    exact houtP.isHermitian.sub houtQ.isHermitian
  have houttr : (𝒩.map Δ).trace = 0 := by
    rw [𝒩.tracePreserving Δ, hΔtr]
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd 𝒩.map 𝒩.completelyPositive
  have hKTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact 𝒩.tracePreserving
  let E : CMatrix b := positiveSupport (𝒩.map Δ) houtherm
  have hEpos : E.PosSemidef := positiveSupport_pos (𝒩.map Δ) houtherm
  have hEle : E ≤ 1 := positiveSupport_le_one (𝒩.map Δ) houtherm
  have hAdj := MatrixMap.krausAdjoint_effect_of_tracePreserving K hKTP hEpos hEle
  have hinputBound :
      (Δ * MatrixMap.krausAdjoint K E).trace.re ≤ (Δ⁺).trace.re :=
    re_trace_mul_le_posPart Δ (MatrixMap.krausAdjoint K E) hΔherm hAdj.1 hAdj.2
  have hpairing : ((𝒩.map Δ)⁺).trace.re =
      (Δ * MatrixMap.krausAdjoint K E).trace.re := by
    calc
      ((𝒩.map Δ)⁺).trace.re = (𝒩.map Δ * E).trace.re := by
        rw [mul_positiveSupport (𝒩.map Δ) houtherm]
      _ = (MatrixMap.ofKraus K Δ * E).trace.re := by rw [← hK]
      _ = (Δ * MatrixMap.krausAdjoint K E).trace.re := by
        rw [MatrixMap.ofKraus_trace_duality]
  have hpospart : ((𝒩.map Δ)⁺).trace.re ≤ (Δ⁺).trace.re := by
    rw [hpairing]
    exact hinputBound
  rw [traceDistance, traceDistance]
  change (1 / 2 : ℝ) * OneShot.traceNorm (𝒩.map ρ.matrix - 𝒩.map σ.matrix) ≤
    (1 / 2 : ℝ) * OneShot.traceNorm Δ
  rw [← map_sub]
  change (1 / 2 : ℝ) * OneShot.traceNorm (𝒩.map Δ) ≤
    (1 / 2 : ℝ) * OneShot.traceNorm Δ
  rw [traceNorm_eq_two_re_trace_posPart_of_trace_zero (𝒩.map Δ) houtherm houttr,
    traceNorm_eq_two_re_trace_posPart_of_trace_zero Δ hΔherm hΔtr]
  norm_num
  exact hpospart

end

end QITFormalized.TraceDistanceDataProcessingQuantumChannels
