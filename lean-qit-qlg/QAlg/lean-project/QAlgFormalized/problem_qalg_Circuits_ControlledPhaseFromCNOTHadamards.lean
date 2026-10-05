import QAlgBench.Base

/-!
# Controlled phase from CNOT and target Hadamards

The first qubit is the control and the second qubit is the target.  Thus
`Gate.controlled Gate.Z` is `CZ`, `Gate.CNOT` is `CX₁→₂`, and
`(1 : Gate (Qubits 1)).tensor Gate.H` is `I ⊗ H`.
-/

namespace QAlgFormalized.ControlledPhaseFromCNOTHadamards

open QAlgBench

/-- The exact circuit identity
`CZ = (I ⊗ H) CX₁→₂ (I ⊗ H)`. -/
theorem controlledPhase_eq_targetHadamard_cnot_targetHadamard :
    Gate.controlled Gate.Z =
      (1 : Gate (Qubits 1)).tensor Gate.H
        * Gate.CNOT
        * (1 : Gate (Qubits 1)).tensor Gate.H := by
  have hHXH : Gate.H * Gate.X * Gate.H = Gate.Z := by
    ext i j
    change ((Gate.HOp * (Gate.X : HilbertOperator (Qubits 1))) * Gate.HOp) i j =
      Gate.ZOp i j
    fin_cases i <;> fin_cases j <;>
      simp +decide [Gate.HOp, Gate.X, Gate.ofPerm, Gate.ZOp, Matrix.mul_apply,
        PureState.invSqrt2_mul_self] <;> norm_num
  have hHHop :
      (Gate.H : HilbertOperator (Qubits 1)) * Gate.H = 1 := by
    simpa using congrArg
      (fun G : Gate (Qubits 1) => (G : HilbertOperator (Qubits 1))) Gate.H_mul_H
  have hHXHop :
      ((Gate.H : HilbertOperator (Qubits 1)) * Gate.X) * Gate.H = Gate.Z := by
    simpa using congrArg
      (fun G : Gate (Qubits 1) => (G : HilbertOperator (Qubits 1))) hHXH
  have hop :
      Gate.controlledOp Gate.Z =
        (HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
            (Gate.H : HilbertOperator (Qubits 1)) *
          Gate.controlledOp Gate.X) *
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          (Gate.H : HilbertOperator (Qubits 1)) := by
    simp only [Gate.controlledOp]
    rw [Matrix.mul_add, Matrix.add_mul,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor]
    simp [hHHop, hHXHop]
  rw [← Gate.controlled_X]
  apply Gate.ext
  intro i j
  exact congrFun (congrFun hop i) j

end QAlgFormalized.ControlledPhaseFromCNOTHadamards
