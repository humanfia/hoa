import QITBench.Base

open scoped BigOperators

namespace QITBench

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The partial trace over `b`, packaged as a complex-linear map.

The finite types `a` and `b` index fixed orthonormal coordinate bases of the
two finite-dimensional Hilbert spaces. -/
def partialTraceBMap : MatrixMap (a × b) a where
  toFun := partialTraceB
  map_add' := partialTraceB_add
  map_smul' := partialTraceB_smul

/-- The Kraus operator `I_a ⊗ ⟨j|` associated with the `j`th vector of the
fixed orthonormal basis of the subsystem being traced out. -/
def partialTraceBKraus (j : b) : Matrix a (a × b) ℂ :=
  fun i x => if x = (i, j) then 1 else 0

/-- The partial trace over `b` has the basis-indexed Kraus representation
`X ↦ ∑ j, (I_a ⊗ ⟨j|) X (I_a ⊗ |j⟩)`. -/
theorem partialTraceBMap_krausRepresentation :
    partialTraceBMap (a := a) (b := b) =
      MatrixMap.ofKraus (partialTraceBKraus (a := a) (b := b)) := by
  apply LinearMap.ext
  intro X
  ext i i'
  simp only [partialTraceBMap, partialTraceB, LinearMap.coe_mk, AddHom.coe_mk,
    MatrixMap.ofKraus, Matrix.sum_apply, Matrix.mul_apply, partialTraceBKraus,
    Matrix.conjTranspose_apply]
  simp

/-- The partial trace over `b` is completely positive. -/
theorem partialTraceBMap_isCompletelyPositive :
    MatrixMap.IsCompletelyPositive (partialTraceBMap (a := a) (b := b)) := by
  rw [partialTraceBMap_krausRepresentation]
  exact MatrixMap.ofKraus_completelyPositive _

/-- The partial trace over `b` is trace-preserving. -/
theorem partialTraceBMap_isTracePreserving :
    MatrixMap.IsTracePreserving (partialTraceBMap (a := a) (b := b)) := by
  intro X
  exact partialTraceB_trace X

/-- The explicit Kraus representation of the partial trace, together with its
complete positivity and trace preservation. -/
theorem partialTraceBMap_isCPTP_with_krausRepresentation :
    partialTraceBMap (a := a) (b := b) =
        MatrixMap.ofKraus (partialTraceBKraus (a := a) (b := b)) ∧
      MatrixMap.IsCompletelyPositive (partialTraceBMap (a := a) (b := b)) ∧
      MatrixMap.IsTracePreserving (partialTraceBMap (a := a) (b := b)) := by
  exact ⟨partialTraceBMap_krausRepresentation,
    partialTraceBMap_isCompletelyPositive, partialTraceBMap_isTracePreserving⟩

end

end QITBench
