/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Components.Gates
public import QAlgBench.Base.Components.Oracle.Common

/-!
# Reflection oracle constructors

Reusable Core-level reflection constructors.  They are all exposed as `Gate`s:
the underlying diagonal phase oracle is a unitary matrix, and prepared
reflections are conjugates of that basis reflection by a preparation gate.
This module also carries projector-controlled NOT gates `C_P NOT`, which are
the projector oracles used by QSVT-style statements.  Block-encoding predicates
and their encoded targets live separately in `Oracle.BlockEncoding`.
-/

@[expose] public section

namespace QAlgBench

open PureState

noncomputable section

namespace Gate

theorem X_conjTranspose :
    (Gate.X : HilbertOperator (Qubits 1)).conjTranspose =
      (Gate.X : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gate.X, Gate.ofPerm, Matrix.conjTranspose_apply]

theorem X_mul_X :
    (Gate.X : HilbertOperator (Qubits 1)) * (Gate.X : HilbertOperator (Qubits 1)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gate.X, Gate.ofPerm, Matrix.mul_apply]

end Gate

/-- A finite-dimensional orthogonal projector.  Projectors are raw Hilbert
operators rather than gates; their associated reflections are unitary gates. -/
structure OrthogonalProjector (n : Nat) where
  /-- The projector matrix. -/
  op : HilbertOperator (Qubits n)
  selfAdjoint : op.conjTranspose = op
  idempotent : op * op = op

namespace OrthogonalProjector

/-- The identity projector. -/
def identity (n : Nat) : OrthogonalProjector n where
  op := 1
  selfAdjoint := by rw [Matrix.conjTranspose_one]
  idempotent := by simp

/-- The rank-one computational-basis projector `|j><j|`. -/
def basisOp {n : Nat} (j : Fin (2 ^ n)) : HilbertOperator (Qubits n) :=
  Matrix.of fun r c => (if r = j then (1 : ℂ) else 0) * (if c = j then (1 : ℂ) else 0)

theorem basisOp_conjTranspose {n : Nat} (j : Fin (2 ^ n)) :
    (basisOp j).conjTranspose = basisOp j := by
  ext r c
  by_cases hr : r = j <;> by_cases hc : c = j <;>
    simp [basisOp, Matrix.conjTranspose_apply, hr, hc]

theorem basisOp_idempotent {n : Nat} (j : Fin (2 ^ n)) :
    basisOp j * basisOp j = basisOp j := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hr : r = j <;> by_cases hc : c = j <;>
    simp [basisOp, hr, hc]

/-- The computational-basis projector `|j><j|`. -/
def basis {n : Nat} (j : Fin (2 ^ n)) : OrthogonalProjector n where
  op := basisOp j
  selfAdjoint := basisOp_conjTranspose j
  idempotent := basisOp_idempotent j

/-- The computational all-zero basis projector. -/
def zero (n : Nat) : OrthogonalProjector n :=
  basis (0 : Fin (2 ^ n))

/-- Tensor product of orthogonal projectors. -/
def tensor {m n : Nat} (P : OrthogonalProjector m) (Q : OrthogonalProjector n) :
    OrthogonalProjector (m + n) where
  op := HilbertOperator.tensor P.op Q.op
  selfAdjoint := by
    rw [HilbertOperator.conjTranspose_tensor, P.selfAdjoint, Q.selfAdjoint]
  idempotent := by
    rw [HilbertOperator.tensor_mul_tensor, P.idempotent, Q.idempotent]

/-- Projector onto the `|0^a>` ancilla block tensored with the full `n`-qubit
system register. -/
def zeroAncilla (a n : Nat) : OrthogonalProjector (a + n) :=
  tensor (zero a) (identity n)

/-- The reflection `2P - I` associated to an orthogonal projector. -/
def reflectionOp {n : Nat} (P : OrthogonalProjector n) : HilbertOperator (Qubits n) :=
  (2 : ℂ) • P.op - 1

theorem reflectionOp_conjTranspose {n : Nat} (P : OrthogonalProjector n) :
    (reflectionOp P).conjTranspose = reflectionOp P := by
  simp [reflectionOp, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, P.selfAdjoint]

theorem reflectionOp_sq {n : Nat} (P : OrthogonalProjector n) :
    reflectionOp P * reflectionOp P = 1 := by
  simp [reflectionOp, Matrix.mul_sub, Matrix.sub_mul, P.idempotent]
  module

theorem reflectionOp_mem_unitaryGroup {n : Nat} (P : OrthogonalProjector n) :
    reflectionOp P ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    reflectionOp_conjTranspose, reflectionOp_sq]

/-- Bundle the projector reflection as a gate. -/
def reflection {n : Nat} (P : OrthogonalProjector n) : Gate (Qubits n) :=
  Gate.ofUnitary (reflectionOp P) (reflectionOp_mem_unitaryGroup P)

/-- The complementary orthogonal projector `I - P`. -/
def complement {n : Nat} (P : OrthogonalProjector n) : HilbertOperator (Qubits n) :=
  1 - P.op

theorem mul_complement {n : Nat} (P : OrthogonalProjector n) :
    P.op * complement P = 0 := by
  simp [complement, Matrix.mul_sub, P.idempotent]

theorem complement_mul {n : Nat} (P : OrthogonalProjector n) :
    complement P * P.op = 0 := by
  simp [complement, Matrix.sub_mul, P.idempotent]

theorem complement_sq {n : Nat} (P : OrthogonalProjector n) :
    complement P * complement P = complement P := by
  simp [complement, Matrix.mul_sub, Matrix.sub_mul, P.idempotent]

theorem complement_conjTranspose {n : Nat} (P : OrthogonalProjector n) :
    (complement P).conjTranspose = complement P := by
  simp [complement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, P.selfAdjoint]

/-- A projector complement kills vectors already supported on the projector. -/
theorem complement_applyVec_eq_zero_of_projector_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {psi : StateVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op psi = psi) :
    HilbertOperator.applyVec (complement P) psi = 0 := by
  calc
    HilbertOperator.applyVec (complement P) psi =
        HilbertOperator.applyVec (complement P) (HilbertOperator.applyVec P.op psi) := by
      rw [hpsi]
    _ = HilbertOperator.applyVec (complement P * P.op) psi := by
      rw [HilbertOperator.mul_applyVec]
    _ = 0 := by
      rw [complement_mul]
      ext i
      simp [HilbertOperator.applyVec_apply]

/-- A projector kills vectors supported on its complement. -/
theorem projector_applyVec_eq_zero_of_complement_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {psi : StateVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec (complement P) psi = psi) :
    HilbertOperator.applyVec P.op psi = 0 := by
  calc
    HilbertOperator.applyVec P.op psi =
        HilbertOperator.applyVec P.op (HilbertOperator.applyVec (complement P) psi) := by
      rw [hpsi]
    _ = HilbertOperator.applyVec (P.op * complement P) psi := by
      rw [HilbertOperator.mul_applyVec]
    _ = 0 := by
      rw [mul_complement]
      ext i
      simp [HilbertOperator.applyVec_apply]

/-- The reflection through a projector fixes vectors in the projector image. -/
theorem reflectionOp_applyVec_of_projector_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {psi : StateVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op psi = psi) :
    HilbertOperator.applyVec (reflectionOp P) psi = psi := by
  have hOp :
      reflectionOp P =
        (2 : ℂ) • P.op + (-1 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
    ext i j
    simp [reflectionOp, sub_eq_add_neg]
  rw [hOp, HilbertOperator.add_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec, hpsi]
  ext i
  simp
  ring

/-- The reflection through a projector negates vectors in the complementary
image. -/
theorem reflectionOp_applyVec_of_projector_applyVec_eq_zero {n : Nat}
    (P : OrthogonalProjector n) {psi : StateVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op psi = 0) :
    HilbertOperator.applyVec (reflectionOp P) psi = -psi := by
  have hOp :
      reflectionOp P =
        (2 : ℂ) • P.op + (-1 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
    ext i j
    simp [reflectionOp, sub_eq_add_neg]
  rw [hOp, HilbertOperator.add_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec, hpsi]
  ext i
  simp

/-- Projector-controlled NOT:
`C_P NOT = X ⊗ P + I ⊗ (I-P)`, flipping the leading qubit on the image of `P`. -/
def controlledNotOp {n : Nat} (P : OrthogonalProjector n) : HilbertOperator (Qubits (1 + n)) :=
  HilbertOperator.tensor (Gate.X : HilbertOperator (Qubits 1)) P.op
    + HilbertOperator.tensor (1 : HilbertOperator (Qubits 1)) (complement P)

theorem controlledNotOp_mem_unitaryGroup {n : Nat} (P : OrthogonalProjector n) :
    controlledNotOp P ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [controlledNotOp, Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
    HilbertOperator.conjTranspose_tensor, Gate.X_conjTranspose, P.selfAdjoint,
    Matrix.conjTranspose_one, complement_conjTranspose]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
    HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
    Gate.X_mul_X, Matrix.one_mul, Matrix.mul_one,
    P.idempotent, mul_complement, complement_mul, complement_sq]
  simp [HilbertOperator.tensor_zero]
  rw [← HilbertOperator.tensor_add]
  have hsum : P.op + complement P = 1 := by
    simp [complement]
  rw [hsum, HilbertOperator.one_tensor_one]

/-- Projector-controlled NOT as a gate. -/
def controlledNot {n : Nat} (P : OrthogonalProjector n) : Gate (Qubits (1 + n)) :=
  Gate.ofUnitary (controlledNotOp P) (controlledNotOp_mem_unitaryGroup P)

end OrthogonalProjector

namespace Gate

variable {n : Nat}

/-- The computational-basis reflection that fixes `|j>` and phases every other
basis ket by `-1`.  This is the `2|j><j| - I` convention packaged as a gate. -/
def basisReflection (j : Fin (2 ^ n)) : Gate (Qubits n) :=
  phaseOracle (fun k => k != j)

@[simp]
theorem basisReflection_applyVec_ket_self (j : Fin (2 ^ n)) :
    (basisReflection j).applyVec (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) =
      (PureState.ket (R := Qubits n) j : StateVector (Qubits n)) := by
  simp [basisReflection, phaseOracle_apply_ket]

theorem basisReflection_applyVec_ket_ne (j k : Fin (2 ^ n)) (hk : k != j) :
    (basisReflection j).applyVec (PureState.ket (R := Qubits n) k : StateVector (Qubits n)) =
      (-(PureState.ket (R := Qubits n) k : StateVector (Qubits n))) := by
  simp [basisReflection, phaseOracle_apply_ket, hk]

/-- The reflection through the all-zero computational basis state. -/
def zeroReflection (n : Nat) : Gate (Qubits n) :=
  basisReflection (0 : Fin (2 ^ n))

/-- Reflection through the prepared basis state `V |j>`, written as
`V (2|j><j| - I) V†`. -/
def preparedReflection (V : Gate (Qubits n)) (j : Fin (2 ^ n)) : Gate (Qubits n) :=
  V * basisReflection j * V.conjTranspose

@[simp]
theorem preparedReflection_zero (V : Gate (Qubits n)) :
    preparedReflection V (0 : Fin (2 ^ n)) = V * zeroReflection n * V.conjTranspose := by
  rfl

end Gate

end

end QAlgBench

