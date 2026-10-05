import QAlgBench.Base

/-!
# Controlled `R_y` synthesis with two CNOT gates

This file formalizes the exact two-CNOT decomposition of a controlled
single-qubit rotation about the Pauli `Y` axis.  Gate multiplication denotes
right-to-left composition.
-/

namespace QAlgFormalized

open QAlgBench

noncomputable section

/-- For every real rotation angle `θ`, a controlled `R_y(θ)` gate is exactly
the circuit consisting, from right to left, of a CNOT, `R_y(-θ/2)` on the
target, a second CNOT, and `R_y(θ/2)` on the target. -/
theorem controlledRY_twoCNOT_synthesis (θ : ℝ) :
    Gate.controlled (rotY θ) =
      (1 : Gate (Qubits 1)).tensor (rotY (θ / 2)) *
        Gate.CNOT *
        (1 : Gate (Qubits 1)).tensor (rotY (-(θ / 2))) *
        Gate.CNOT := by
  have hrot (a b : ℝ) : rotY a * rotY b = rotY (a + b) := by
    apply Gate.ext
    intro i j
    change (rotYOp a * rotYOp b) i j = rotYOp (a + b) i j
    fin_cases i <;> fin_cases j <;> simp [rotYOp, Matrix.mul_apply]
    all_goals
      rw [show ((a : ℂ) + (b : ℂ)) / 2 = (a : ℂ) / 2 + (b : ℂ) / 2 by ring]
    all_goals simp only [Complex.cos_add, Complex.sin_add]
    all_goals ring
  have hzero : rotY 0 = 1 := by
    apply Gate.ext
    intro i j
    change rotYOp 0 i j = (1 : HilbertOperator (Qubits 1)) i j
    fin_cases i <;> fin_cases j <;> simp [rotYOp]
  have hconj (b : ℝ) : Gate.X * rotY b * Gate.X = rotY (-b) := by
    apply Gate.ext
    intro i j
    change ((Gate.X : HilbertOperator (Qubits 1)) * rotYOp b *
      (Gate.X : HilbertOperator (Qubits 1))) i j = rotYOp (-b) i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate.X, Gate.ofPerm, rotYOp, Matrix.mul_apply]
    all_goals rw [show -(b : ℂ) / 2 = -((b : ℂ) / 2) by ring]
    all_goals simp only [Complex.cos_neg, Complex.sin_neg]
    all_goals ring
  have hAB : rotY (θ / 2) * rotY (-(θ / 2)) = 1 := by
    rw [hrot, show θ / 2 + -(θ / 2) = 0 by ring, hzero]
  have hAXBX :
      rotY (θ / 2) * Gate.X * rotY (-(θ / 2)) * Gate.X = rotY θ := by
    calc
      rotY (θ / 2) * Gate.X * rotY (-(θ / 2)) * Gate.X =
          rotY (θ / 2) * (Gate.X * rotY (-(θ / 2)) * Gate.X) := by
            simp only [mul_assoc]
      _ = rotY (θ / 2) * rotY (-(-(θ / 2))) := by rw [hconj]
      _ = rotY (θ / 2 + -(-(θ / 2))) := hrot _ _
      _ = rotY θ := by congr 1; ring
  have hABop :
      (rotY (θ / 2) : HilbertOperator (Qubits 1)) *
          (rotY (-(θ / 2)) : HilbertOperator (Qubits 1)) = 1 := by
    simpa using congrArg
      (fun G : Gate (Qubits 1) => (G : HilbertOperator (Qubits 1))) hAB
  have hAXBXop :
      (rotY (θ / 2) : HilbertOperator (Qubits 1)) *
            (Gate.X : HilbertOperator (Qubits 1)) *
          (rotY (-(θ / 2)) : HilbertOperator (Qubits 1)) *
        (Gate.X : HilbertOperator (Qubits 1)) =
      (rotY θ : HilbertOperator (Qubits 1)) := by
    simpa using congrArg
      (fun G : Gate (Qubits 1) => (G : HilbertOperator (Qubits 1))) hAXBX
  have hmatrix :
      Gate.controlledOp (rotY θ) =
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
            (rotY (θ / 2) : HilbertOperator (Qubits 1)) *
          Gate.controlledOp Gate.X *
          HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
            (rotY (-(θ / 2)) : HilbertOperator (Qubits 1)) *
          Gate.controlledOp Gate.X := by
    simp only [Gate.controlledOp, Matrix.mul_add, Matrix.add_mul]
    repeat' rw [HilbertOperator.tensor_mul_tensor]
    simp only [Matrix.one_mul, Matrix.mul_one, hABop, hAXBXop]
    rw [Gate.proj0_mul_proj0, Gate.proj1_mul_proj0,
      Gate.proj0_mul_proj1, Gate.proj1_mul_proj1]
    simp only [HilbertOperator.zero_tensor, zero_add, add_zero]
  rw [← Gate.controlled_X]
  apply Gate.ext
  intro i j
  exact congrArg (fun A : HilbertOperator (Qubits 2) => A i j) hmatrix

end

end QAlgFormalized
