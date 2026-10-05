/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Components.Gates

/-!
# Controlled gates

`Gate.controlled U` is the `(1 + n)`-qubit Gate (Qubits that) applies the `n`-qubit
gate `U` on the target register exactly when the control qubit is in `|1>`,
and does nothing when it is in `|0>` [CEMM98, cemm6.tex:127]. As a matrix it
is the block decomposition `c-U = |0><0| ⊗ 1 + |1><1| ⊗ U`.

The projectors `proj0` and `proj1` are `HilbertOperator`s, not gates.
-/

@[expose] public section

namespace QAlgBench

namespace Gate

open PureState

noncomputable section

variable {n : ℕ}

/-- The one-qubit projector `|0><0| = [[1, 0], [0, 0]]`. -/
def proj0 : HilbertOperator (Qubits 1) := !![(1 : ℂ), 0; 0, 0]

/-- The one-qubit projector `|1><1| = [[0, 0], [0, 1]]`. -/
def proj1 : HilbertOperator (Qubits 1) := !![(0 : ℂ), 0; 0, 1]

@[simp]
theorem proj0_conjTranspose : proj0.conjTranspose = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]

@[simp]
theorem proj1_conjTranspose : proj1.conjTranspose = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]

theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply]

@[simp]
theorem proj0_applyVec_ket0 :
    HilbertOperator.applyVec proj0 (ket0 : StateVector (Qubits 1))
      = (ket0 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket0, PureState.ket]

@[simp]
theorem proj0_applyVec_ket1 :
    HilbertOperator.applyVec proj0 (ket1 : StateVector (Qubits 1)) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket1, PureState.ket]

@[simp]
theorem proj1_applyVec_ket0 :
    HilbertOperator.applyVec proj1 (ket0 : StateVector (Qubits 1)) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket0, PureState.ket]

@[simp]
theorem proj1_applyVec_ket1 :
    HilbertOperator.applyVec proj1 (ket1 : StateVector (Qubits 1))
      = (ket1 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket1, PureState.ket]

/-- Raw controlled-operator matrix. -/
def controlledOp (U : Gate (Qubits n)) : HilbertOperator (Qubits (1 + n)) :=
  HilbertOperator.tensor proj0 (1 : HilbertOperator (Qubits n))
    + HilbertOperator.tensor proj1 (U : HilbertOperator (Qubits n))

/-- Raw zero-branch controlled-operator matrix: applies `U` on `|0>` and
does nothing on `|1>`. -/
def controlledOnZeroOp (U : Gate (Qubits n)) : HilbertOperator (Qubits (1 + n)) :=
  HilbertOperator.tensor proj0 (U : HilbertOperator (Qubits n))
    + HilbertOperator.tensor proj1 (1 : HilbertOperator (Qubits n))

/-- The controlled gate `c-U`. -/
def controlled (U : Gate (Qubits n)) : Gate (Qubits (1 + n)) :=
  ofUnitary (controlledOp U) (by
    have hU :
        (U : HilbertOperator (Qubits n))
          * (U : HilbertOperator (Qubits n)).conjTranspose = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp U.unitary
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [controlledOp, Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
      HilbertOperator.conjTranspose_tensor, proj0_conjTranspose, proj1_conjTranspose,
      Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor, hU]
    simp only [Matrix.one_mul, Matrix.mul_one]
    have h00 :
        HilbertOperator.tensor (proj0 * proj0) (1 : HilbertOperator (Qubits n)) =
          HilbertOperator.tensor proj0 (1 : HilbertOperator (Qubits n)) := by
      rw [proj0_mul_proj0]
    have h01 :
        HilbertOperator.tensor (proj0 * proj1)
            ((U : HilbertOperator (Qubits n)).conjTranspose) = 0 := by
      rw [proj0_mul_proj1, HilbertOperator.zero_tensor]
    have h10 :
        HilbertOperator.tensor (proj1 * proj0) (U : HilbertOperator (Qubits n)) = 0 := by
      rw [proj1_mul_proj0, HilbertOperator.zero_tensor]
    have h11 :
        HilbertOperator.tensor (proj1 * proj1) (1 : HilbertOperator (Qubits n)) =
          HilbertOperator.tensor proj1 (1 : HilbertOperator (Qubits n)) := by
      rw [proj1_mul_proj1]
    rw [h00, h01, h10, h11]
    simp [zero_add, add_zero]
    rw [← HilbertOperator.add_tensor, proj0_add_proj1, HilbertOperator.one_tensor_one])

/-- The zero-branch controlled gate: `|0><0| ⊗ U + |1><1| ⊗ I`. -/
def controlledOnZero (U : Gate (Qubits n)) : Gate (Qubits (1 + n)) :=
  ofUnitary (controlledOnZeroOp U) (by
    have hU :
        (U : HilbertOperator (Qubits n))
          * (U : HilbertOperator (Qubits n)).conjTranspose = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp U.unitary
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [controlledOnZeroOp, Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
      HilbertOperator.conjTranspose_tensor, proj0_conjTranspose, proj1_conjTranspose,
      Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor, hU]
    simp only [Matrix.one_mul, Matrix.mul_one]
    have h00 :
        HilbertOperator.tensor (proj0 * proj0) (1 : HilbertOperator (Qubits n)) =
          HilbertOperator.tensor proj0 (1 : HilbertOperator (Qubits n)) := by
      rw [proj0_mul_proj0]
    have h01 :
        HilbertOperator.tensor (proj0 * proj1)
            (U : HilbertOperator (Qubits n)) = 0 := by
      rw [proj0_mul_proj1, HilbertOperator.zero_tensor]
    have h10 :
        HilbertOperator.tensor (proj1 * proj0)
            ((U : HilbertOperator (Qubits n)).conjTranspose) = 0 := by
      rw [proj1_mul_proj0, HilbertOperator.zero_tensor]
    have h11 :
        HilbertOperator.tensor (proj1 * proj1) (1 : HilbertOperator (Qubits n)) =
          HilbertOperator.tensor proj1 (1 : HilbertOperator (Qubits n)) := by
      rw [proj1_mul_proj1]
    rw [h00, h01, h10, h11]
    simp [zero_add, add_zero]
    rw [← HilbertOperator.add_tensor, proj0_add_proj1, HilbertOperator.one_tensor_one])

/-- On the `|0>` control branch `c-U` does nothing. -/
@[simp]
theorem controlled_applyVec_ket0_tensor (U : Gate (Qubits n)) (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi)
      = StateVector.tensor (ket0 : StateVector (Qubits 1)) psi := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi) i
      = StateVector.tensor (ket0 : StateVector (Qubits 1)) psi i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket0, proj1_applyVec_ket0,
    HilbertOperator.one_applyVec, StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` control branch `c-U` applies `U`. -/
@[simp]
theorem controlled_applyVec_ket1_tensor (U : Gate (Qubits n)) (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) psi)
      = StateVector.tensor (ket1 : StateVector (Qubits 1)) (U.applyVec psi) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) psi) i
      = StateVector.tensor (ket1 : StateVector (Qubits 1))
        (HilbertOperator.applyVec (U : HilbertOperator (Qubits n)) psi) i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket1, proj1_applyVec_ket1,
    StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|0>` control branch `controlledOnZero U` applies `U`. -/
@[simp]
theorem controlledOnZero_applyVec_ket0_tensor (U : Gate (Qubits n)) (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec (controlledOnZero U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi)
      = StateVector.tensor (ket0 : StateVector (Qubits 1)) (U.applyVec psi) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOnZeroOp U)
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) psi) i
      = StateVector.tensor (ket0 : StateVector (Qubits 1))
        (HilbertOperator.applyVec (U : HilbertOperator (Qubits n)) psi) i
  rw [controlledOnZeroOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket0, proj1_applyVec_ket0,
    StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` control branch `controlledOnZero U` does nothing. -/
@[simp]
theorem controlledOnZero_applyVec_ket1_tensor (U : Gate (Qubits n)) (psi : StateVector (Qubits n)) :
    HilbertOperator.applyVec (controlledOnZero U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) psi)
      = StateVector.tensor (ket1 : StateVector (Qubits 1)) psi := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOnZeroOp U)
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) psi) i
      = StateVector.tensor (ket1 : StateVector (Qubits 1)) psi i
  rw [controlledOnZeroOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket1, proj1_applyVec_ket1,
    HilbertOperator.one_applyVec, StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|0>` control branch `c-U` does nothing. -/
@[simp]
theorem controlled_apply_ket0_tensor (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    (controlled U).apply (ket0.tensor psi) = ket0.tensor psi := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) i
      = StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n)) i
  rw [controlled_applyVec_ket0_tensor]

/-- On the `|1>` control branch `c-U` applies `U`. -/
@[simp]
theorem controlled_apply_ket1_tensor (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    (controlled U).apply (ket1.tensor psi) = ket1.tensor (U.apply psi) := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) i
      = StateVector.tensor (ket1 : StateVector (Qubits 1))
        (U.applyVec (psi : StateVector (Qubits n))) i
  rw [controlled_applyVec_ket1_tensor]

/-- On the `|0>` control branch `controlledOnZero U` applies `U`. -/
@[simp]
theorem controlledOnZero_apply_ket0_tensor (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    (controlledOnZero U).apply (ket0.tensor psi) = ket0.tensor (U.apply psi) := by
  ext i
  change HilbertOperator.applyVec (controlledOnZero U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket0 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) i
      = StateVector.tensor (ket0 : StateVector (Qubits 1))
        (U.applyVec (psi : StateVector (Qubits n))) i
  rw [controlledOnZero_applyVec_ket0_tensor]

/-- On the `|1>` control branch `controlledOnZero U` does nothing. -/
@[simp]
theorem controlledOnZero_apply_ket1_tensor (U : Gate (Qubits n)) (psi : PureState (Qubits n)) :
    (controlledOnZero U).apply (ket1.tensor psi) = ket1.tensor psi := by
  ext i
  change HilbertOperator.applyVec (controlledOnZero U : HilbertOperator (Qubits (1 + n)))
        (StateVector.tensor (ket1 : StateVector (Qubits 1)) (psi : StateVector (Qubits n))) i
      = StateVector.tensor (ket1 : StateVector (Qubits 1)) (psi : StateVector (Qubits n)) i
  rw [controlledOnZero_applyVec_ket1_tensor]

/-- `c-U` is unitary. -/
theorem controlled_mem_unitaryGroup {U : Gate (Qubits n)}
    (_hU : (U : HilbertOperator (Qubits n)) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (controlled U : HilbertOperator (Qubits (1 + n)))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  (controlled U).unitary

/-- Sanity check: the controlled Pauli-X Gate (Qubits is) exactly `CNOT`. -/
theorem controlled_X : controlled X = CNOT := by
  have hX : ∀ i j : Fin (2 ^ 1), (X : HilbertOperator (Qubits 1)) i j
      = if i = Equiv.swap 0 1 j then 1 else 0 := by
    intro i j
    rw [← apply_ket X j i, X, ofPerm_apply_ket, Equiv.swap_inv, PureState.ket_apply]
  have hC : ∀ i j : Fin (2 ^ 2), CNOT i j
      = if i = Equiv.swap 2 3 j then 1 else 0 := by
    intro i j
    rw [← apply_ket CNOT j i, CNOT_apply_ket, PureState.ket_apply]
  ext i j
  change controlledOp X i j = CNOT i j
  rw [hC]
  fin_cases i <;> fin_cases j <;>
    simp +decide [controlledOp, HilbertOperator.tensor_apply, proj0, proj1,
      hX, Matrix.one_apply, prodEquiv, finProdFinEquiv, finCongr,
      Fin.divNat, Fin.modNat]

end

end Gate

end QAlgBench

