/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import QITBench.Base

/-!
# No maximally entangled vector in the qutrit antisymmetric subspace

The benchmark Base represents a bipartite finite-dimensional amplitude vector
by a function on a product basis.  For two qutrits, currying this function gives
its `3 × 3` coefficient matrix.
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QITFormalized.NoMaximallyEntangledVectorQutritAntisymmetricSubspace

noncomputable section

/-- The computational-basis label type of a qutrit. -/
abbrev Qutrit := Fin 3

/-- A (not necessarily normalized) vector in `ℂ³ ⊗ ℂ³`, in the product basis
used by `QITBench.Base`. -/
abbrev BipartiteQutritVector := (Qutrit × Qutrit) → ℂ

/-- Identification of a bipartite qutrit vector with its `3 × 3` coefficient
matrix. -/
def coefficientMatrix :
    BipartiteQutritVector ≃ₗ[ℂ] QITBench.CMatrix Qutrit where
  toFun ψ i j := ψ (i, j)
  invFun C ij := C ij.1 ij.2
  left_inv ψ := by rfl
  right_inv C := by rfl
  map_add' ψ φ := by rfl
  map_smul' c ψ := by rfl

/-- The tensor-factor swap on two-qutrit amplitude vectors. -/
def swapQutritFactors :
    BipartiteQutritVector →ₗ[ℂ] BipartiteQutritVector where
  toFun ψ ij := ψ (ij.2, ij.1)
  map_add' ψ φ := by rfl
  map_smul' c ψ := by rfl

/-- The exterior square `ASym²(ℂ³)`, realized as the `(-1)` eigenspace of the
tensor-factor swap. -/
def qutritAntisymmetricSubspace : Submodule ℂ BipartiteQutritVector :=
  LinearMap.ker (swapQutritFactors + LinearMap.id)

/-- A normalized two-qutrit pure vector is maximally entangled when its first
qutrit marginal is the maximally mixed state `I₃ / 3`. -/
def IsMaximallyEntangled
    (ψ : QITBench.PureVector (Qutrit × Qutrit)) : Prop :=
  ψ.state.marginalA.matrix =
    ((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit))

/-- A two-qutrit vector is antisymmetric exactly when its coefficient matrix is
skew-symmetric. -/
theorem mem_qutritAntisymmetricSubspace_iff_coefficientMatrix_transpose
    (ψ : BipartiteQutritVector) :
    ψ ∈ qutritAntisymmetricSubspace ↔
      (coefficientMatrix ψ)ᵀ = -coefficientMatrix ψ := by
  rw [qutritAntisymmetricSubspace, LinearMap.mem_ker]
  constructor
  · intro h
    ext i j
    have hij := congrFun h (i, j)
    change ψ (j, i) = -ψ (i, j)
    exact eq_neg_of_add_eq_zero_left <|
      by simpa [swapQutritFactors] using hij
  · intro h
    funext ij
    have hij := congrFun (congrFun h ij.1) ij.2
    change ψ (ij.2, ij.1) + ψ ij = 0
    exact add_eq_zero_iff_eq_neg.mpr <|
      by simpa [coefficientMatrix] using hij

/-- No normalized maximally entangled two-qutrit vector belongs to
`ASym²(ℂ³)`. -/
theorem no_maximallyEntangledVector_mem_qutritAntisymmetricSubspace :
    ¬ ∃ ψ : QITBench.PureVector (Qutrit × Qutrit),
      ψ.amp ∈ qutritAntisymmetricSubspace ∧ IsMaximallyEntangled ψ := by
  rintro ⟨ψ, hψ, hmax⟩
  let C : QITBench.CMatrix Qutrit := coefficientMatrix ψ.amp
  have hskew : Cᵀ = -C := by
    simpa [C] using
      (mem_qutritAntisymmetricSubspace_iff_coefficientMatrix_transpose ψ.amp).mp hψ
  have hdet_eq_neg : C.det = -C.det := by
    calc
      C.det = Cᵀ.det := (Matrix.det_transpose C).symm
      _ = (-C).det := congrArg Matrix.det hskew
      _ = (-1) ^ Fintype.card Qutrit * C.det := Matrix.det_neg C
      _ = -C.det := by norm_num [Qutrit]
  have hdet : C.det = 0 := by
    have htwo : (2 : ℂ) * C.det = 0 := by
      calc
        (2 : ℂ) * C.det = C.det + C.det := by ring
        _ = -C.det + C.det :=
          congrArg (fun z : ℂ => z + C.det) hdet_eq_neg
        _ = 0 := neg_add_cancel C.det
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  change QITBench.partialTraceB (QITBench.rankOneMatrix ψ.amp) =
    ((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit)) at hmax
  have hGram :
      C * Cᴴ = ((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit)) := by
    ext i i'
    have hii := congrFun (congrFun hmax i) i'
    simpa [C, coefficientMatrix, QITBench.partialTraceB,
      QITBench.rankOneMatrix_apply, Matrix.mul_apply] using hii
  have hzero :
      (0 : ℂ) =
        (((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit))).det := by
    calc
      (0 : ℂ) = (C * Cᴴ).det := by simp [Matrix.det_mul, hdet]
      _ = (((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit))).det :=
        congrArg Matrix.det hGram
  have hnonzero :
      (((3 : ℂ)⁻¹ • (1 : QITBench.CMatrix Qutrit))).det ≠ 0 := by
    rw [Matrix.det_smul]
    norm_num [Qutrit]
  exact hnonzero hzero.symm

end

end QITFormalized.NoMaximallyEntangledVectorQutritAntisymmetricSubspace
