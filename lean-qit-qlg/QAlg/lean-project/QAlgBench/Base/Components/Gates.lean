/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Gate
public import QAlgBench.Base.Components.Kets
public import QAlgBench.Base.Util.Complex

/-!
# Named gates

The standard named gates as `Components` (concrete instances built on the
`Core` Gate (Qubits framework) `QAlgBench.Gate`). Raw matrices are first stated as
`HilbertOperator`s, then bundled into `Gate`s with their unitarity proofs.
-/

@[expose] public section

namespace QAlgBench

open PureState

noncomputable section

namespace Gate

/-! ## Pauli, Hadamard, and CNOT -/

/-- Raw Hadamard operator `H = (1/sqrt 2) [[1, 1], [1, -1]]`. -/
def HOp : HilbertOperator (Qubits 1) :=
  invSqrt2 • !![(1 : ℂ), 1; 1, -1]

theorem HOp_mem_unitaryGroup :
    HOp ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, HOp, star_smul, smul_mul_smul_comm,
    star_invSqrt2, invSqrt2_mul_self]
  have hstar : star (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
      = !![(1 : ℂ), 1; 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  have hmul :
      (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
        * !![(1 : ℂ), 1; 1, -1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
  rw [hstar, hmul, smul_smul]
  norm_num

/-- The Hadamard gate. -/
def H : Gate (Qubits 1) := ofUnitary HOp HOp_mem_unitaryGroup

/-- The Pauli-X (NOT) gate, as the basis permutation `|0> ↔ |1>`. -/
def X : Gate (Qubits 1) := ofPerm (Equiv.swap 0 1)

/-- Raw Pauli-Y operator `[[0, -i], [i, 0]]`. -/
def YOp : HilbertOperator (Qubits 1) := !![(0 : ℂ), -Complex.I; Complex.I, 0]

theorem YOp_mem_unitaryGroup :
    YOp ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [YOp, Matrix.mul_apply, Matrix.star_apply]

/-- The Pauli-Y gate. -/
def Y : Gate (Qubits 1) := ofUnitary YOp YOp_mem_unitaryGroup

/-- Raw Pauli-Z operator `[[1, 0], [0, -1]]`. -/
def ZOp : HilbertOperator (Qubits 1) := !![(1 : ℂ), 0; 0, -1]

theorem ZOp_mem_unitaryGroup :
    ZOp ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ZOp, Matrix.mul_apply, Matrix.star_apply]

/-- The Pauli-Z gate. -/
def Z : Gate (Qubits 1) := ofUnitary ZOp ZOp_mem_unitaryGroup

/-- The controlled-NOT Gate (Qubits on) two qubits, control = qubit 0. -/
def CNOT : Gate (Qubits 2) := ofPerm (Equiv.swap 2 3)

theorem X_mem_unitaryGroup : (X : HilbertOperator (Qubits 1))
    ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  X.unitary

theorem CNOT_mem_unitaryGroup : (CNOT : HilbertOperator (Qubits 2))
    ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ :=
  CNOT.unitary

theorem Y_mem_unitaryGroup : (Y : HilbertOperator (Qubits 1))
    ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  Y.unitary

theorem Z_mem_unitaryGroup : (Z : HilbertOperator (Qubits 1))
    ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  Z.unitary

theorem H_mem_unitaryGroup : (H : HilbertOperator (Qubits 1))
    ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  H.unitary

/-- `H |0> = |+>`. -/
@[simp]
theorem H_apply_ket0 : H.apply ket0 = ketPlus := by
  ext i
  rw [ket0, apply_ket, ketPlus_apply]
  fin_cases i <;> simp [H, HOp]

/-- `H |1> = |->`. -/
@[simp]
theorem H_apply_ket1 : H.apply ket1 = ketMinus := by
  ext i
  rw [ket1, apply_ket, ketMinus_apply]
  fin_cases i <;> simp [H, HOp]

@[simp]
theorem H_applyVec_ket0 :
    H.applyVec (ket0 : StateVector (Qubits 1)) = (ketPlus : StateVector (Qubits 1)) :=
  congrArg (fun psi : PureState (Qubits 1) => (psi : StateVector (Qubits 1))) H_apply_ket0

@[simp]
theorem H_applyVec_ket1 :
    H.applyVec (ket1 : StateVector (Qubits 1)) = (ketMinus : StateVector (Qubits 1)) :=
  congrArg (fun psi : PureState (Qubits 1) => (psi : StateVector (Qubits 1))) H_apply_ket1

/-- `CNOT` permutes the basis by swapping `|10> ↔ |11>` (indices 2 ↔ 3). -/
theorem CNOT_apply_ket (x : Fin (2 ^ 2)) :
    CNOT.apply (ket x) =
      ket (Equiv.swap (2 : Fin (2 ^ 2)) (3 : Fin (2 ^ 2)) x) := by
  rw [CNOT, ofPerm_apply_ket, Equiv.swap_inv]

/-- `X |0> = |1>`. -/
@[simp]
theorem X_apply_ket0 : X.apply ket0 = ket1 := by
  rw [ket0, X, ofPerm_apply_ket, Equiv.swap_inv, ket1]
  congr 1

/-- `X |1> = |0>`. -/
@[simp]
theorem X_apply_ket1 : X.apply ket1 = ket0 := by
  rw [ket1, X, ofPerm_apply_ket, Equiv.swap_inv, ket0]
  congr 1

@[simp]
theorem X_applyVec_ket0 :
    X.applyVec (ket0 : StateVector (Qubits 1)) = (ket1 : StateVector (Qubits 1)) :=
  congrArg (fun psi : PureState (Qubits 1) => (psi : StateVector (Qubits 1))) X_apply_ket0

@[simp]
theorem X_applyVec_ket1 :
    X.applyVec (ket1 : StateVector (Qubits 1)) = (ket0 : StateVector (Qubits 1)) :=
  congrArg (fun psi : PureState (Qubits 1) => (psi : StateVector (Qubits 1))) X_apply_ket1

/-- `Z |0> = |0>`. -/
@[simp]
theorem Z_apply_ket0 : Z.apply ket0 = ket0 := by
  ext i
  rw [ket0, apply_ket, ket_apply]
  fin_cases i <;> simp [Z, ZOp]

@[simp]
theorem Z_applyVec_ket0 :
    Z.applyVec (ket0 : StateVector (Qubits 1)) = (ket0 : StateVector (Qubits 1)) :=
  congrArg (fun psi : PureState (Qubits 1) => (psi : StateVector (Qubits 1))) Z_apply_ket0

/-- Raw-vector form of `Z |1> = -|1>`. -/
@[simp]
theorem Z_applyVec_ket1 :
    Z.applyVec (ket1 : StateVector (Qubits 1)) = -(ket1 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Z, ZOp, Gate.applyVec, HilbertOperator.applyVec, ket1, PureState.ket]

/-- `H * H = 1`: the Hadamard Gate (Qubits is) an involution. -/
theorem H_mul_H : H * H = 1 := by
  ext i j
  change (HOp * HOp) i j = (1 : HilbertOperator (Qubits 1)) i j
  have h : HOp * HOp = (1 : HilbertOperator (Qubits 1)) := by
    rw [HOp, smul_mul_smul_comm, invSqrt2_mul_self]
    have hmul :
        (!![(1 : ℂ), 1; 1, -1] : HilbertOperator (Qubits 1))
          * !![(1 : ℂ), 1; 1, -1] = (2 : ℂ) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
    rw [hmul, smul_smul]
    norm_num
  rw [h]

/-- `H |+> = |0>`. -/
@[simp]
theorem H_apply_ketPlus : H.apply ketPlus = ket0 := by
  rw [← H_apply_ket0, ← mul_apply, H_mul_H, one_apply]

/-- `H |-> = |1>`. -/
@[simp]
theorem H_apply_ketMinus : H.apply ketMinus = ket1 := by
  rw [← H_apply_ket1, ← mul_apply, H_mul_H, one_apply]

/-! ## `CNOT` on the tensor basis -/

/-- `CNOT |00> = |00>`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket0 :
    CNOT.apply (ket0.tensor ket0) = ket0.tensor ket0 := by
  rw [ket0, PureState.tensor_ket]
  change CNOT.apply (PureState.ket (R := Qubits 2) 0) =
    PureState.ket (R := Qubits 2) 0
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 0 = 0 from by decide]

/-- `CNOT |01> = |01>`. -/
@[simp]
theorem CNOT_apply_ket0_tensor_ket1 :
    CNOT.apply (ket0.tensor ket1) = ket0.tensor ket1 := by
  rw [ket0, ket1, PureState.tensor_ket]
  change CNOT.apply (PureState.ket (R := Qubits 2) 1) =
    PureState.ket (R := Qubits 2) 1
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 1 = 1 from by decide]

/-- `CNOT |10> = |11>`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket0 :
    CNOT.apply (ket1.tensor ket0) = ket1.tensor ket1 := by
  rw [ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change CNOT.apply (PureState.ket (R := Qubits 2) 2) =
    PureState.ket (R := Qubits 2) 3
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 2 = 3 from by decide]

/-- `CNOT |11> = |10>`. -/
@[simp]
theorem CNOT_apply_ket1_tensor_ket1 :
    CNOT.apply (ket1.tensor ket1) = ket1.tensor ket0 := by
  rw [ket0, ket1, PureState.tensor_ket, PureState.tensor_ket]
  change CNOT.apply (PureState.ket (R := Qubits 2) 3) =
    PureState.ket (R := Qubits 2) 2
  rw [CNOT_apply_ket, show Equiv.swap (2 : Fin (2 ^ 2)) 3 3 = 2 from by decide]

@[simp]
theorem CNOT_applyVec_ket0_tensor_ket0 :
    CNOT.applyVec
        (StateVector.tensor (ket0 : StateVector (Qubits 1))
          (ket0 : StateVector (Qubits 1)))
      =
      StateVector.tensor (ket0 : StateVector (Qubits 1)) (ket0 : StateVector (Qubits 1)) :=
  congrArg
    (fun psi : PureState (Qubits 2) => (psi : StateVector (Qubits 2)))
    CNOT_apply_ket0_tensor_ket0

@[simp]
theorem CNOT_applyVec_ket0_tensor_ket1 :
    CNOT.applyVec
        (StateVector.tensor (ket0 : StateVector (Qubits 1))
          (ket1 : StateVector (Qubits 1)))
      =
      StateVector.tensor (ket0 : StateVector (Qubits 1)) (ket1 : StateVector (Qubits 1)) :=
  congrArg
    (fun psi : PureState (Qubits 2) => (psi : StateVector (Qubits 2)))
    CNOT_apply_ket0_tensor_ket1

@[simp]
theorem CNOT_applyVec_ket1_tensor_ket0 :
    CNOT.applyVec
        (StateVector.tensor (ket1 : StateVector (Qubits 1))
          (ket0 : StateVector (Qubits 1)))
      =
      StateVector.tensor (ket1 : StateVector (Qubits 1)) (ket1 : StateVector (Qubits 1)) :=
  congrArg
    (fun psi : PureState (Qubits 2) => (psi : StateVector (Qubits 2)))
    CNOT_apply_ket1_tensor_ket0

@[simp]
theorem CNOT_applyVec_ket1_tensor_ket1 :
    CNOT.applyVec
        (StateVector.tensor (ket1 : StateVector (Qubits 1))
          (ket1 : StateVector (Qubits 1)))
      =
      StateVector.tensor (ket1 : StateVector (Qubits 1)) (ket0 : StateVector (Qubits 1)) :=
  congrArg
    (fun psi : PureState (Qubits 2) => (psi : StateVector (Qubits 2)))
    CNOT_apply_ket1_tensor_ket1

end Gate

/-! ## Rotation gates (QSP / QNN conventions) -/

/-- Raw processing rotation `e^{i phi Z}`. -/
def rotZOp (phi : ℝ) : HilbertOperator (Qubits 1) :=
  !![Complex.exp (phi * Complex.I), 0; 0, Complex.exp (-(phi * Complex.I))]

theorem rotZOp_mem_unitaryGroup (phi : ℝ) :
    rotZOp phi ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZOp, Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
      conj_exp_neg_I, exp_I_mul_exp_neg_I, exp_neg_I_mul_exp_I]

/-- The processing rotation `e^{i phi Z}`. -/
def rotZ (phi : ℝ) : Gate (Qubits 1) := Gate.ofUnitary (rotZOp phi) (rotZOp_mem_unitaryGroup phi)

theorem rotZ_mul_rotZ (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  ext i j
  change (rotZOp a * rotZOp b) i j = rotZOp (a + b) i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZOp, Matrix.mul_apply, ← Complex.exp_add]
  · congr 1; ring
  · congr 1; ring

@[simp]
theorem rotZ_zero : rotZ 0 = 1 := by
  ext i j
  change rotZOp 0 i j = (1 : HilbertOperator (Qubits 1)) i j
  fin_cases i <;> fin_cases j <;> simp [rotZOp]

theorem rotZ_mem_unitaryGroup (phi : ℝ) :
    (rotZ phi : HilbertOperator (Qubits 1)) ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  (rotZ phi).unitary

theorem rotZ_comm (a b : ℝ) : rotZ a * rotZ b = rotZ b * rotZ a := by
  rw [rotZ_mul_rotZ, rotZ_mul_rotZ, add_comm]

theorem rotZ_neg_mul_rotZ (phi : ℝ) : rotZ (-phi) * rotZ phi = 1 := by
  rw [rotZ_mul_rotZ, neg_add_cancel, rotZ_zero]

theorem rotZ_mul_rotZ_neg (phi : ℝ) : rotZ phi * rotZ (-phi) = 1 := by
  rw [rotZ_mul_rotZ, add_neg_cancel, rotZ_zero]

/-- Raw standard `R_Y(theta)`. -/
def rotYOp (theta : ℝ) : HilbertOperator (Qubits 1) :=
  !![(Real.cos (theta / 2) : ℂ), -(Real.sin (theta / 2) : ℂ);
     (Real.sin (theta / 2) : ℂ), (Real.cos (theta / 2) : ℂ)]

theorem rotYOp_mem_unitaryGroup (theta : ℝ) :
    rotYOp theta ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have hcs' : (Real.sin (theta / 2) : ℂ) ^ 2
      + (Real.cos (theta / 2) : ℂ) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq (theta / 2)
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
  rw [Matrix.mem_unitaryGroup_iff]
  unfold rotYOp
  generalize Real.cos (theta / 2) = c at hcs' ⊢
  generalize Real.sin (theta / 2) = s at hcs' ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
      try ring_nf
      try linear_combination hcs'

/-- The standard `R_Y(theta)` gate. -/
def rotY (theta : ℝ) : Gate (Qubits 1) :=
  Gate.ofUnitary (rotYOp theta) (rotYOp_mem_unitaryGroup theta)

/-- The standard `R_Z(phi) = e^{-i phi Z/2}`. -/
def rotZStd (phi : ℝ) : Gate (Qubits 1) := rotZ (-(phi / 2))

@[simp]
theorem rotZStd_zero : rotZStd 0 = 1 := by
  rw [rotZStd, show -(0 / 2 : ℝ) = 0 by norm_num, rotZ_zero]

theorem rotY_mem_unitaryGroup (theta : ℝ) :
    (rotY theta : HilbertOperator (Qubits 1)) ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  (rotY theta).unitary

theorem rotZStd_mem_unitaryGroup (phi : ℝ) :
    (rotZStd phi : HilbertOperator (Qubits 1)) ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  (rotZStd phi).unitary

/-! ## Phase gates -/

/-- A one-qubit state is its `|0⟩`/`|1⟩` coordinate combination. -/
theorem single_qubit_vec_decomp (ψ : StateVector (Qubits 1)) :
    ψ =
      (ψ 0) • (ket0 : StateVector (Qubits 1)) + (ψ 1) • (ket1 : StateVector (Qubits 1)) := by
  ext i
  fin_cases i <;>
    simp [ket0, ket1, ket_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem single_qubit_decomp (ψ : PureState (Qubits 1)) :
    (ψ : StateVector (Qubits 1)) =
      (ψ 0) • (ket0 : StateVector (Qubits 1)) + (ψ 1) • (ket1 : StateVector (Qubits 1)) :=
  single_qubit_vec_decomp (ψ : StateVector (Qubits 1))

/-- The controlled-phase gate `diag(1, e^{iθ})`. -/
def phaseGateOp (θ : ℝ) : HilbertOperator (Qubits 1) :=
  !![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)]

theorem phaseGateOp_mem_unitaryGroup (θ : ℝ) :
    phaseGateOp θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGateOp, Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
      exp_I_mul_exp_neg_I]

/-- Single-qubit phase gate with phases `1` and `exp (i * theta)`. -/
def phaseGate (θ : ℝ) : Gate (Qubits 1) :=
  Gate.ofUnitary (phaseGateOp θ) (phaseGateOp_mem_unitaryGroup θ)

/-- The zero-branch controlled-phase gate `diag(e^{iθ}, 1)`. -/
def phaseGateOnZeroOp (θ : ℝ) : HilbertOperator (Qubits 1) :=
  !![Complex.exp ((θ : ℝ) * Complex.I), 0; 0, 1]

theorem phaseGateOnZeroOp_mem_unitaryGroup (θ : ℝ) :
    phaseGateOnZeroOp θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGateOnZeroOp, Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
      exp_I_mul_exp_neg_I]

/-- Single-qubit phase gate with phases `exp (i * theta)` and `1`. -/
def phaseGateOnZero (θ : ℝ) : Gate (Qubits 1) :=
  Gate.ofUnitary (phaseGateOnZeroOp θ) (phaseGateOnZeroOp_mem_unitaryGroup θ)

@[simp]
theorem phaseGate_apply_ket0 (θ : ℝ) : (phaseGate θ).apply ket0 = ket0 := by
  ext i
  rw [ket0, Gate.apply_ket]
  fin_cases i <;> simp [phaseGate, phaseGateOp, ket_apply]

@[simp]
theorem phaseGate_apply_ket1 (θ : ℝ) :
    (phaseGate θ).applyVec (ket1 : StateVector (Qubits 1)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (ket1 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Gate.applyVec, HilbertOperator.applyVec, phaseGate, phaseGateOp, ket1,
      PureState.ket, PiLp.smul_apply, smul_eq_mul]

/-- The controlled-phase gate on a general ancilla state. -/
theorem phaseGate_applyVec (θ : ℝ) (ψ : StateVector (Qubits 1)) :
    (phaseGate θ).applyVec ψ
      = (ψ 0) • (ket0 : StateVector (Qubits 1)) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Gate.applyVec, HilbertOperator.applyVec, phaseGate, phaseGateOp, ket0, ket1,
      PureState.ket, Matrix.vecHead, Matrix.vecTail, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]

theorem phaseGate_apply (θ : ℝ) (ψ : PureState (Qubits 1)) :
    (phaseGate θ).applyVec (ψ : StateVector (Qubits 1))
      = (ψ 0) • (ket0 : StateVector (Qubits 1)) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector (Qubits 1)) :=
  phaseGate_applyVec θ (ψ : StateVector (Qubits 1))

/-- The zero-branch controlled-phase gate on a general ancilla state. -/
theorem phaseGateOnZero_applyVec (θ : ℝ) (ψ : StateVector (Qubits 1)) :
    (phaseGateOnZero θ).applyVec ψ
      = (Complex.exp ((θ : ℝ) * Complex.I) * ψ 0) •
          (ket0 : StateVector (Qubits 1)) +
        (ψ 1) • (ket1 : StateVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Gate.applyVec, HilbertOperator.applyVec, phaseGateOnZero, phaseGateOnZeroOp,
      ket0, ket1, PureState.ket, Matrix.vecHead, Matrix.vecTail, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]

/-- `diag(1,e^{iθ}) = e^{iθ/2} · R_Z(θ)`. -/
theorem phaseGate_signal (θ : ℝ) :
    (phaseGate θ : HilbertOperator (Qubits 1)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) • (rotZStd θ : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, phaseGateOp, rotZStd, rotZ, rotZOp, Matrix.smul_apply,
      smul_eq_mul]
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- `diag(e^{-iθ},1) = e^{-iθ/2} · R_Z(θ)`. -/
theorem phaseGateOnZero_signal (θ : ℝ) :
    (phaseGateOnZero (-θ) : HilbertOperator (Qubits 1)) =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) • (rotZStd θ : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGateOnZero, phaseGateOnZeroOp, rotZStd, rotZ, rotZOp, Matrix.smul_apply,
      smul_eq_mul]
  · rw [← Complex.exp_add]
    congr 1
    ring
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    ring

/-- `diag(1,e^{iθ})` on a vector is `e^{iθ/2}` times the QSP signal
`R_Z(θ)` on that vector. -/
theorem phaseGate_applyVec_eq_smul_rotZStd (θ : ℝ) (ψ : StateVector (Qubits 1)) :
    (phaseGate θ).applyVec ψ
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec ψ := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits 1) => HilbertOperator.applyVec A ψ)
    (phaseGate_signal θ)
  simpa [Gate.applyVec, HilbertOperator.smul_applyVec] using h

/-- `diag(e^{-iθ},1)` on a vector is `e^{-iθ/2}` times the QSP signal
`R_Z(θ)` on that vector. -/
theorem phaseGateOnZero_applyVec_eq_smul_rotZStd (θ : ℝ) (ψ : StateVector (Qubits 1)) :
    (phaseGateOnZero (-θ)).applyVec ψ
      = Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec ψ := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits 1) => HilbertOperator.applyVec A ψ)
    (phaseGateOnZero_signal θ)
  simpa [Gate.applyVec, HilbertOperator.smul_applyVec] using h

theorem phaseGate_apply_eq_smul_rotZStd (θ : ℝ) (ψ : PureState (Qubits 1)) :
    (phaseGate θ).applyVec (ψ : StateVector (Qubits 1))
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec (ψ : StateVector (Qubits 1)) :=
  phaseGate_applyVec_eq_smul_rotZStd θ (ψ : StateVector (Qubits 1))

end

end QAlgBench
