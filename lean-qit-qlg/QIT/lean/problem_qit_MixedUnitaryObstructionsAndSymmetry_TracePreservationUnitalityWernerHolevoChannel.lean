import QITBench.Base

/-!
# Trace preservation and unitality of the qutrit Werner--Holevo map

The computational basis of `ℂ³` is represented by `Fin 3`.  Thus an operator on
`ℂ³` is a matrix in `CMatrix (Fin 3)`, and transpose is taken in this fixed
basis.
-/

open scoped ComplexOrder MatrixOrder

namespace QITBench

noncomputable section

/-- The Werner--Holevo linear map on qutrit operators,
`Φ(X) = (1 / 2) • (Tr(X) • I - Xᵀ)`. -/
def qutritWernerHolevoMap : MatrixMap (Fin 3) (Fin 3) where
  toFun X :=
    (1 / 2 : ℂ) •
      (X.trace • (1 : CMatrix (Fin 3)) - Matrix.transpose X)
  map_add' X Y := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.trace_add]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
      ring
  map_smul' c X := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.trace_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
      ring

/-- The qutrit Werner--Holevo map preserves the trace of every operator. -/
theorem qutritWernerHolevoMap_isTracePreserving :
    MatrixMap.IsTracePreserving qutritWernerHolevoMap := by
  intro X
  simp only [qutritWernerHolevoMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_transpose,
    Matrix.trace_smul, Matrix.trace_one]
  norm_num
  ring

/-- The qutrit Werner--Holevo map sends the identity operator to itself. -/
theorem qutritWernerHolevoMap_one :
    qutritWernerHolevoMap (1 : CMatrix (Fin 3)) = 1 := by
  ext i j
  simp [qutritWernerHolevoMap]
  by_cases hij : i = j
  · subst j
    simp
    norm_num
  · simp [hij]

end

end QITBench
