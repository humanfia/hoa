import QAlgBench.Base

/-!
# The two-qubit Hadamard matrix

The computational basis of `Qubits 2` is indexed in the benchmark's big-endian
order `|00⟩, |01⟩, |10⟩, |11⟩`.
-/

namespace QAlgFormalized.HadamardTensorHadamardMatrix

open QAlgBench

noncomputable section

/-- The full matrix of `H ⊗ H` in the ordered computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/
def matrix : HilbertOperator (Qubits 2) :=
  (1 / 2 : ℂ) •
    !![(1 : ℂ),  1,  1,  1;
        1,      -1,  1, -1;
        1,       1, -1, -1;
        1,      -1, -1,  1]

/-- Computing the tensor product of the two Hadamard operators gives the
displayed `4 × 4` matrix. -/
theorem H_tensor_H_eq_matrix :
    ((Gate.H.tensor Gate.H : Gate (Qubits 2)) : HilbertOperator (Qubits 2)) = matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Gate.tensor_apply, Gate.H, Gate.HOp, QAlgBench.prodEquiv,
      finProdFinEquiv, finCongr, Fin.divNat, Fin.modNat,
      QAlgBench.PureState.invSqrt2_mul_self]

/-- The computed two-qubit Hadamard matrix is unitary. -/
theorem matrix_mem_unitaryGroup :
    matrix ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ := by
  rw [← H_tensor_H_eq_matrix]
  exact (Gate.H.tensor Gate.H).unitary

/-- The computed two-qubit Hadamard matrix is self-inverse. -/
theorem matrix_mul_self :
    matrix * matrix = (1 : HilbertOperator (Qubits 2)) := by
  rw [← H_tensor_H_eq_matrix]
  change
    ((((Gate.H.tensor Gate.H) * (Gate.H.tensor Gate.H) : Gate (Qubits 2)) :
        HilbertOperator (Qubits 2))) =
      (1 : HilbertOperator (Qubits 2))
  rw [Gate.tensor_mul_tensor, Gate.H_mul_H, Gate.one_tensor_one]
  exact Gate.coe_one

end

end QAlgFormalized.HadamardTensorHadamardMatrix
